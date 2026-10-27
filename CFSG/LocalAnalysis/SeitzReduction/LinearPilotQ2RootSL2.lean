module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

theorem eq_one_of_mem_center_specialLinearGroup_of_card_two (hK : Nat.card K = 2) {m : ℕ}
    {z : SpecialLinearGroup (Fin m) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin m) K)) : z = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have h2 := FiniteField.pow_card r
  rw [← Nat.card_eq_fintype_card, hK, sq] at h2
  apply Subtype.ext
  rw [← hrz, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  have hr1 : r = 1 := by
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Fintype.card_fin, zero_pow (by rintro rfl; exact i.elim0)] at hr
      exact zero_ne_one hr
    exact mul_left_cancel₀ hr0 (h2.trans (mul_one r).symm)
  rw [hr1, map_one]

theorem exists_map_blockSpecialLinear_pair_of_mulAut_two [Finite K] {m : ℕ} (hm : 3 ≤ m)
    (hK : Nat.card K = 2) (β : MulAut (SpecialLinearGroup (Fin m) K)) (a b : Fin m) :
    ∃ s : SpecialLinearGroup (Fin m) K,
      (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map β.toMonoidHom =
        (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map
          (MulAut.conj s).toMonoidHom := by
  obtain ⟨g, hg⟩ := map_rootSL2_of_mulAut hm (descendAut m K β) a b
  obtain ⟨s, rfl⟩ := proj_surjective m K g
  refine ⟨s, ?_⟩
  set H := blockSpecialLinear (K := K) ({a, b} : Finset (Fin m)) with hH
  have hle : H.map β.toMonoidHom ≤ H.map (MulAut.conj s).toMonoidHom := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : proj m K (β x) ∈ (rootSL2 (K := K) a b).map (descendAut m K β).toMonoidHom :=
      ⟨proj m K x, proj_mem_blockSL hx, descendAut_proj m K β x⟩
    rw [hg] at h1
    obtain ⟨w, hw, hweq⟩ := h1
    obtain ⟨y, hy, rfl⟩ := mem_blockSL.mp hw
    have hz : (s * y * s⁻¹)⁻¹ * β x ∈ Subgroup.center (SpecialLinearGroup (Fin m) K) := by
      rw [← scalars_eq_center, ← proj_eq_one_iff, map_mul, map_inv, ← hweq]
      change (proj m K (s * y * s⁻¹))⁻¹ * (proj m K s * proj m K y * (proj m K s)⁻¹) = 1
      rw [map_mul, map_mul, map_inv, inv_mul_cancel]
    have h1' := eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz
    rw [inv_mul_eq_one] at h1'
    refine ⟨y, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h1'
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj s).injective,
    Subgroup.card_map_of_injective β.injective]

theorem exists_map_blockSpecialLinear_pair_eq_conj_of_mulEquiv_two [Finite K] {m : ℕ}
    (hm : 3 ≤ m) (hK : Nat.card K = 2) {F : Type*} [Group F]
    (θ₁ θ₂ : SpecialLinearGroup (Fin m) K ≃* F) (a b : Fin m) :
    ∃ f : F, (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map θ₁.toMonoidHom =
      ((blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map θ₂.toMonoidHom).map
        (MulAut.conj f).toMonoidHom := by
  obtain ⟨s, hs⟩ :=
    exists_map_blockSpecialLinear_pair_of_mulAut_two hm hK (θ₁.trans θ₂.symm) a b
  refine ⟨θ₂ s, ?_⟩
  have h1 : (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map θ₁.toMonoidHom =
      ((blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map
        (θ₁.trans θ₂.symm).toMonoidHom).map θ₂.toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [h1, hs, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem exists_map_rootSL2_of_mulEquiv_blockSL_two [Finite K]
    (hK : Nat.card K = 2) {I I' : Finset (Fin n)} (hI : 3 ≤ I.card) (hII' : I.card = I'.card)
    (hI'n : I'.card < n)
    (ψ : blockSL (K := K) I ≃* blockSL (K := K) I') {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) :
    ∃ c ∈ I', ∃ d ∈ I', c ≠ d ∧ ∃ g ∈ blockSL (K := K) I',
      ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I)).map
          ((blockSL (K := K) I').subtype.comp ψ.toMonoidHom) =
        (rootSL2 (K := K) c d).map (MulAut.conj g).toMonoidHom := by
  have hIn : I.card < n := hII' ▸ hI'n
  set eI : I ≃ Fin I.card := I.equivFin with heI
  set eI' : I' ≃ Fin I.card := I'.equivFin.trans (finCongr hII'.symm) with heI'
  set θ := blockSLEquivOfEquiv (K := K) hIn eI with hθ
  set θ' := blockSLEquivOfEquiv (K := K) hI'n eI' with hθ'
  set a' := eI ⟨a, ha⟩ with ha'
  set b' := eI ⟨b, hb⟩ with hb'
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val (eI.injective h))
  obtain ⟨f, hf⟩ :=
    exists_map_blockSpecialLinear_pair_eq_conj_of_mulEquiv_two hI hK (θ.trans ψ) θ' a' b'
  set c : Fin n := (eI'.symm a' : Fin n) with hcdef
  set d : Fin n := (eI'.symm b' : Fin n) with hddef
  have hc : c ∈ I' := (eI'.symm a').2
  have hd : d ∈ I' := (eI'.symm b').2
  have hcd : c ≠ d := fun h => hab' (eI'.symm.injective (Subtype.ext h))
  refine ⟨c, hc, d, hd, hcd, f, f.2, ?_⟩
  have hJ : (rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I) =
      (blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map θ.toMonoidHom := by
    apply Subgroup.map_injective (blockSL (K := K) I).subtype_injective
    rw [map_blockSLEquivOfEquiv_pair hIn eI ha hb]
    exact Subgroup.map_subgroupOf_eq_of_le (H := rootSL2 (K := K) a b) (K := blockSL (K := K) I)
      (blockSL_mono (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩))
  have hJ' : ((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
      θ'.toMonoidHom).map (blockSL (K := K) I').subtype = rootSL2 (K := K) c d := by
    have h := map_blockSLEquivOfEquiv_pair (K := K) hI'n eI' hc hd
    have h1 : eI' ⟨c, hc⟩ = a' := by
      have : (⟨c, hc⟩ : I') = eI'.symm a' := Subtype.ext rfl
      rw [this, Equiv.apply_symm_apply]
    have h2 : eI' ⟨d, hd⟩ = b' := by
      have : (⟨d, hd⟩ : I') = eI'.symm b' := Subtype.ext rfl
      rw [this, Equiv.apply_symm_apply]
    rw [h1, h2] at h
    exact h
  calc ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I)).map
          ((blockSL (K := K) I').subtype.comp ψ.toMonoidHom)
      _ = ((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
            (θ.trans ψ).toMonoidHom).map (blockSL (K := K) I').subtype := by
        rw [hJ, Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = (((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
            θ'.toMonoidHom).map (MulAut.conj f).toMonoidHom).map (blockSL (K := K) I').subtype := by
        rw [hf]
      _ = (((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
            θ'.toMonoidHom).map (blockSL (K := K) I').subtype).map
            (MulAut.conj (f : projectiveSL n K)).toMonoidHom := by
        simp only [Subgroup.map_map]
        congr 1
      _ = (rootSL2 (K := K) c d).map (MulAut.conj (f : projectiveSL n K)).toMonoidHom := by
        rw [hJ']

end CFSG.SeitzReduction.LinearPilot
