module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag
  CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

namespace Ivk93M12FSp4

abbrev F3 : Type := ZMod 3

abbrev Mat4 : Type := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F3

@[expose] def q₁ : Matrix (Fin 2) (Fin 2) F3 := !![0, 1; -1, 0]

@[expose] def q₂ : Matrix (Fin 2) (Fin 2) F3 := !![1, 1; 1, -1]

@[expose] def d₁ : Matrix (Fin 2) (Fin 2) F3 := !![1, 0; 0, -1]

@[expose] def d₂ : Matrix (Fin 2) (Fin 2) F3 := !![0, 1; 1, 0]

@[expose] def genMat : Fin 4 → Mat4 := ![kron q₁ 1, kron q₂ 1, kron 1 d₁, kron 1 d₂]

theorem genMat_symp : ∀ i, (genMat i)ᵀ * formJ 2 F3 * genMat i = formJ 2 F3 := by decide

theorem genMat_comm : ∀ i j,
    genMat i * genMat j = genMat j * genMat i ∨ genMat i * genMat j = -(genMat j * genMat i) := by
  decide

theorem genMat_sq : ∀ i, genMat i * genMat i = 1 ∨ genMat i * genMat i = -1 := by decide

@[expose] def wordMat (v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Mat4 :=
  genMat 0 ^ (v.1 : ℕ) * genMat 1 ^ (v.2.1 : ℕ) * genMat 2 ^ (v.2.2.1 : ℕ) *
    genMat 3 ^ (v.2.2.2 : ℕ)

theorem wordMat_inj : ∀ v w, wordMat w = wordMat v ∨ wordMat w = -wordMat v → v = w := by decide

@[expose] noncomputable def genSp (i : Fin 4) : StatedSp 2 F3 := toSp (genMat i) (genMat_symp i)

theorem coe_genSp (i : Fin 4) :
    (((genSp i : StatedSp 2 F3) : GL (Fin 2 ⊕ Fin 2) F3) : Mat4) = genMat i := rfl

theorem proj_eq_of_mat {K : Type} [Field K] {a b : StatedSp 2 K}
    (h : ((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∨
      ((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        -((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    proj 2 K a = proj 2 K b := by
  rcases h with h | h
  · rw [sp_ext h]
  · have h1 : a⁻¹ * b ∈ spScalars 2 K := by
      rw [mem_spScalars_iff]
      right
      have hb : ((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          -((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
        rw [h]; simp
      rw [Subgroup.coe_mul, Units.val_mul, hb, Matrix.mul_neg]
      have : ((((a⁻¹ : StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      rw [this]
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1

@[expose] noncomputable def genProj (i : Fin 4) : StatedProj (StatedSp 2 F3) := proj 2 F3 (genSp i)

theorem coe_mul_sp (a b : StatedSp 2 F3) :
    (((a * b : StatedSp 2 F3) : GL (Fin 2 ⊕ Fin 2) F3) : Mat4) =
      ((a : GL (Fin 2 ⊕ Fin 2) F3) : Mat4) * ((b : GL (Fin 2 ⊕ Fin 2) F3) : Mat4) := by
  rw [Subgroup.coe_mul, Units.val_mul]

theorem coe_pow_sp (a : StatedSp 2 F3) (n : ℕ) :
    (((a ^ n : StatedSp 2 F3) : GL (Fin 2 ⊕ Fin 2) F3) : Mat4) =
      ((a : GL (Fin 2 ⊕ Fin 2) F3) : Mat4) ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem genProj_comm (i j : Fin 4) : genProj i * genProj j = genProj j * genProj i := by
  rw [genProj, genProj, ← map_mul, ← map_mul]
  apply proj_eq_of_mat
  rw [coe_mul_sp, coe_mul_sp, coe_genSp, coe_genSp]
  exact genMat_comm i j

theorem genProj_sq (i : Fin 4) : genProj i ^ 2 = 1 := by
  rw [genProj, pow_two, ← map_mul, ← map_one (proj 2 F3)]
  apply proj_eq_of_mat
  rw [coe_mul_sp, coe_genSp]
  simp only [Subgroup.coe_one, Units.val_one]
  exact genMat_sq i

@[expose] noncomputable def eAb : Subgroup (StatedProj (StatedSp 2 F3)) := Subgroup.closure (Set.range genProj)

theorem eAb_comm : ∀ a ∈ eAb, ∀ b ∈ eAb, a * b = b * a := by
  have hc : (Set.range genProj).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact genProj_comm i j
  have : IsMulCommutative ↥eAb := Subgroup.isMulCommutative_closure hc
  intro a ha b hb
  exact setLike_mul_comm ha hb

theorem eAb_sq : ∀ a ∈ eAb, a ^ 2 = 1 := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact genProj_sq i
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy := eAb_comm x hx y hy
    calc (x * y) ^ 2 = x * y * (x * y) := pow_two _
      _ = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = x ^ 2 * y ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [inv_pow, ihx, inv_one]

@[expose] noncomputable def genWord (v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : eAb :=
  ⟨genProj 0 ^ (v.1 : ℕ) * genProj 1 ^ (v.2.1 : ℕ) * genProj 2 ^ (v.2.2.1 : ℕ) *
      genProj 3 ^ (v.2.2.2 : ℕ), by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _)
      (Subgroup.pow_mem _ ?_ _)) (Subgroup.pow_mem _ ?_ _)) (Subgroup.pow_mem _ ?_ _) <;>
    exact Subgroup.subset_closure ⟨_, rfl⟩⟩

theorem genWord_inj : Function.Injective genWord := by
  intro v w hvw
  have h1 : genProj 0 ^ (v.1 : ℕ) * genProj 1 ^ (v.2.1 : ℕ) * genProj 2 ^ (v.2.2.1 : ℕ) *
        genProj 3 ^ (v.2.2.2 : ℕ) =
      genProj 0 ^ (w.1 : ℕ) * genProj 1 ^ (w.2.1 : ℕ) * genProj 2 ^ (w.2.2.1 : ℕ) *
        genProj 3 ^ (w.2.2.2 : ℕ) :=
    congrArg Subtype.val hvw
  simp only [genProj, ← map_pow, ← map_mul] at h1
  rcases eq_or_eq_neg_of_proj_eq h1 with h2 | h2
  · exact wordMat_inj v w (Or.inl (by simpa [wordMat, coe_mul_sp, coe_pow_sp, coe_genSp] using h2))
  · refine wordMat_inj v w (Or.inr ?_)
    have h3 := h2
    simp only [coe_mul_sp, coe_pow_sp, coe_genSp] at h3
    convert h3 using 2 <;> rfl

theorem card_eAb : 16 ≤ Nat.card eAb := by
  have := Nat.card_le_card_of_injective genWord genWord_inj
  simpa using this

theorem psp43_no_data {J : Type} [Group J] [Finite J] {y : J} (hD : Ivk93M12Data J y)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) (e : J ≃* StatedProj (StatedSp 2 F)) :
    False := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  let σ : F3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hc
  let ψ : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F3) :=
    Adapters.RankTwoModelTransports.statedProjCongr
      (Adapters.RankTwoModelTransports.glCongr (ι := Fin 2 ⊕ Fin 2) σ.symm)
      (ClassicalInvolution.Upgrade.glCongr_statedSp σ.symm 2)
      (Adapters.RankTwoModelTransports.glCongr_statedScalars σ.symm)
  let χ : J ≃* StatedProj (StatedSp 2 F3) := e.trans ψ
  let EJ : Subgroup J := eAb.map χ.symm.toMonoidHom
  have hcomm : ∀ a ∈ EJ, ∀ b ∈ EJ, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    show χ.symm x * χ.symm x' = χ.symm x' * χ.symm x
    rw [← map_mul, ← map_mul, eAb_comm x hx x' hx']
  have hsq : ∀ a ∈ EJ, a ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show χ.symm x ^ 2 = 1
    rw [← map_pow, eAb_sq x hx, map_one]
  have hcard : Nat.card EJ = Nat.card eAb :=
    (Nat.card_congr (eAb.equivMapOfInjective χ.symm.toMonoidHom χ.symm.injective).toEquiv).symm
  have h8 := hD.elemAbelian_le EJ hcomm hsq
  have h16 := card_eAb
  omega

theorem not_isSolvable_of_quasisimple_le {G : Type*} [Group G] {C H : Subgroup G}
    (hH : CFSG.IsQuasisimple ↥H) (hle : H ≤ C) : ¬ Group.IsSolvable ↥C := by
  intro hC
  have hs : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have : Group.IsPerfect ↥H := hH.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hH
  exact Group.IsPerfect.not_isSolvable ↥H hs

theorem isQuasisimple_Lsub_of_card {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (Lsub K) := by
  have hL : Lsub K = ((proj 2 K).comp (diagSL K)).range := by
    rw [Lsub, MonoidHom.range_comp]
  rw [hL]
  exact isQuasisimple_range_comp h4 (diagSL K) (ker_proj_comp_diagSL (K := K))

theorem psp4_not_isSolvable_centralizer {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {u : StatedProj (StatedSp 2 F)} (hu : orderOf u = 2) :
    ¬ Group.IsSolvable ↥(centralizer ({u} : Set (StatedProj (StatedSp 2 F)))) := by
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card F := by omega
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd hu
  intro hs
  let φ : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) := MulAut.conj g⁻¹
  have hφu : φ u = g⁻¹ * u * g := by simp [φ]
  have hs' : Group.IsSolvable ↥(centralizer ({φ u} : Set (StatedProj (StatedSp 2 F)))) := by
    rw [← map_centralizer_singleton φ u]
    exact Group.isSolvable_of_surjective (f := φ.toMonoidHom.subgroupMap (centralizer {u}))
      (φ.toMonoidHom.subgroupMap_surjective _)
  rw [hφu] at hs'
  rcases hg with hg | hg
  · rw [hg] at hs'
    exact not_isSolvable_of_quasisimple_le (isQuasisimple_E1 h2 h4)
      ((E1_le_X0 h2).trans X0_le_centralizer) hs'
  · rw [hg] at hs'
    exact not_isSolvable_of_quasisimple_le (isQuasisimple_Lsub_of_card h4) Lsub_le_centralizer hs'

end Ivk93M12FSp4

open Ivk93M12FSp4

theorem ivk93m12_sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93M12Empty (fun X _ => LieModel X .PSp 2 p f) := by
  intro p f hp hp2 hf J _ _ hJ y hD
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hJ
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  by_cases h3 : Nat.card F = 3
  · exact psp43_no_data hD h3 e
  · have h5 : 5 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      obtain ⟨m, hm⟩ := hodd
      omega
    have hord : orderOf (e y) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hD.central.1
    refine psp4_not_isSolvable_centralizer hodd h5 hord ?_
    have := hD.solvable
    rw [← map_centralizer_singleton e y]
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap (centralizer {y}))
      (e.toMonoidHom.subgroupMap_surjective _)

end CFSG.GH74.GLS.IVK.Proofs2
