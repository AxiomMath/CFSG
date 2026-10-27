module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Card

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)

section Perp

variable {K : Type} [Field K] {d : ℕ} {a b : Fin d}

theorem finrank_perpSub (hab : a ≠ b) : finrank K (perpSub K a b) = d - 2 := by
  classical
  set f : (Fin d → K) →ₗ[K] K × K := (LinearMap.proj a).prod (LinearMap.proj b) with hf
  have hker : LinearMap.ker f = perpSub K a b := by
    ext v
    simp [hf, mem_perpSub]
  have hrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨x, y⟩
    refine ⟨x • Pi.single a 1 + y • Pi.single b 1, ?_⟩
    simp [hf, hab, hab.symm]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, hrange, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega

theorem card_perpSub [Finite K] (hab : a ≠ b) :
    Nat.card (perpSub K a b) = Nat.card K ^ (d - 2) := by
  rw [Module.natCard_eq_pow_finrank (K := K), finrank_perpSub hab]

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}

theorem fixSpace_comap_pairTorusOf (h : IsHypCoord Q a b) (hq : 3 ≤ Nat.card K) :
    fixSpace ((pairTorusOf Q a b).comap (projHom Q)) = perpSub K a b := by
  ext v
  constructor
  · intro hv
    obtain ⟨c₀, hc₀⟩ := exists_units_ne_one (K := K) hq
    have hmem : (⟨torusLin a b c₀, h.torusLin_mem_orthDerived c₀⟩ : orthDerived Q) ∈
        (pairTorusOf Q a b).comap (projHom Q) :=
      ⟨_, mem_subgroupOf.mpr ⟨c₀, rfl⟩, rfl⟩
    have h1 := hv _ hmem
    change torusLin a b c₀ v = v at h1
    have ha := congrFun h1 a
    have hb := congrFun h1 b
    rw [torusLin_apply_left] at ha
    rw [torusLin_apply_right h.ne] at hb
    refine ⟨?_, ?_⟩
    · have : ((c₀ : K) - 1) * v a = 0 := by linear_combination ha
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (units_val_ne_one hc₀))
    · have : (((c₀⁻¹ : Kˣ) : K) - 1) * v b = 0 := by linear_combination hb
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (units_inv_val_ne_one hc₀))
  · intro hv g hg
    obtain ⟨t, ht, htg⟩ := hg
    rw [projHom_injective h.exists_ne_zero htg] at ht
    obtain ⟨c, hc⟩ := mem_subgroupOf.mp ht
    rw [← hc]
    exact torusLin_eq_self_of hv.1 hv.2 c

theorem card_fixSpace_comap_pairTorusOf (h : IsHypCoord Q a b) (hq : 3 ≤ Nat.card K) :
    Nat.card (fixSpace ((pairTorusOf Q a b).comap (projHom Q))) = Nat.card K ^ (d - 2) := by
  rw [fixSpace_comap_pairTorusOf h hq, card_perpSub h.ne]

end Perp

section RootGroup

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_le_stabPairsBar_of_coords {ι₀ : Type*} {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (π : ι₀ ⊕ ι₀ → Fin d) (hπ : Function.Injective π)
    (hπQ : ∀ m, IsHypCoord Q (π (.inl m)) (π (.inr m))) {i j c g h : ι₀} (hic : i ≠ c)
    (hig : i ≠ g) (hih : i ≠ h) (hjc : j ≠ c) (hjg : j ≠ g) (hjh : j ≠ h) (hcg : c ≠ g)
    (hch : c ≠ h) (hgh : g ≠ h) :
    Nat.card K ^ 4 ≤ Nat.card (stabPairsBar Q (π (.inl i)) (π (.inr i)) (π (.inl j))
      (π (.inr j))) := by
  classical
  have hc := hπQ c
  let w : K × K × K × K → Fin d → K := fun x =>
    x.1 • Pi.single (π (.inl g)) 1 + x.2.1 • Pi.single (π (.inr g)) 1 +
      x.2.2.1 • Pi.single (π (.inl h)) 1 + x.2.2.2 • Pi.single (π (.inr h)) 1
  have hw : ∀ x (m : ι₀), m ≠ g → m ≠ h →
      w x (π (.inl m)) = 0 ∧ w x (π (.inr m)) = 0 := by
    intro x m hmg hmh
    constructor <;> simp [w, hπ.eq_iff, hmg, hmh]
  have hEstab : ∀ x, eichler Q (Pi.single (π (.inl c)) 1) (w x) ∈
      stabSub (π (.inl i)) (π (.inr i)) ⊓ stabSub (π (.inl j)) (π (.inr j)) := by
    intro x
    have hfix : ∀ m : ι₀, m ≠ c → m ≠ g → m ≠ h →
        eichler Q (Pi.single (π (.inl c)) 1) (w x) (Pi.single (π (.inl m)) 1) =
          Pi.single (π (.inl m)) 1 ∧
        eichler Q (Pi.single (π (.inl c)) 1) (w x) (Pi.single (π (.inr m)) 1) =
          Pi.single (π (.inr m)) 1 := by
      intro m hmc hmg hmh
      have hm := hπQ m
      refine ⟨eichler_apply_of_polar_eq_zero ?_ ?_, eichler_apply_of_polar_eq_zero ?_ ?_⟩
      · rw [hm.polar_left]; simp [hπ.eq_iff]
      · rw [hm.polar_left]; exact (hw x m hmg hmh).2
      · rw [hm.polar_right]; simp [hπ.eq_iff, hmc]
      · rw [hm.polar_right]; exact (hw x m hmg hmh).1
    obtain ⟨hi1, hi2⟩ := hfix i hic hig hih
    obtain ⟨hj1, hj2⟩ := hfix j hjc hjg hjh
    exact ⟨⟨hi1, hi2⟩, hj1, hj2⟩
  have hEΩ : ∀ x, eichler Q (Pi.single (π (.inl c)) 1) (w x) ∈ orthDerived Q :=
    fun x => eichler_mem_orthDerived hQ hT _ _
  have hEf : ∀ x, eichler Q (Pi.single (π (.inl c)) 1) (w x) (Pi.single (π (.inr c)) 1) =
      Pi.single (π (.inr c)) 1 + w x - Q (w x) • Pi.single (π (.inl c)) 1 := by
    intro x
    have hwc := hw x c hcg hch
    rw [eichler_apply hc.map_left (by rw [hc.polar_left]; exact hwc.2), hc.polar_right,
      hc.polar_right, Pi.single_eq_same, hwc.1]
    module
  let φ : K × K × K × K → stabPairsBar Q (π (.inl i)) (π (.inr i)) (π (.inl j)) (π (.inr j)) :=
    fun x => ⟨projHom _ ⟨_, hEΩ x⟩, ⟨⟨_, hEΩ x⟩, mem_subgroupOf.mpr (hEstab x), rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : (⟨_, hEΩ x⟩ : orthDerived Q) = ⟨_, hEΩ y⟩ :=
      projHom_injective hc.exists_ne_zero (congrArg Subtype.val hxy)
    have h2 := congrArg (fun z : orthDerived Q =>
      (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single (π (.inr c)) 1)) h1
    simp only [hEf] at h2
    have hev : ∀ (v : Fin d), v ≠ π (.inr c) → v ≠ π (.inl c) → w x v = w y v := by
      intro v hv1 hv2
      have := congrFun h2 v
      simp [hv1, hv2] at this
      exact this
    have e1 := hev (π (.inl g)) (by simp [hπ.eq_iff]) (by simp [hπ.eq_iff, hcg.symm])
    have e2 := hev (π (.inr g)) (by simp [hπ.eq_iff, hcg.symm]) (by simp [hπ.eq_iff])
    have e3 := hev (π (.inl h)) (by simp [hπ.eq_iff]) (by simp [hπ.eq_iff, hch.symm])
    have e4 := hev (π (.inr h)) (by simp [hπ.eq_iff, hch.symm]) (by simp [hπ.eq_iff])
    simp [w, hπ.eq_iff, hgh, hgh.symm] at e1 e2 e3 e4
    exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod] at this
  calc Nat.card K ^ 4 = Nat.card K * (Nat.card K * (Nat.card K * Nat.card K)) := by ring
    _ ≤ _ := this

theorem card_le_stabTwoBar {n : ℕ} (hn : 3 ≤ n) {i j c g h : Fin n} (hic : i ≠ c) (hig : i ≠ g)
    (hih : i ≠ h) (hjc : j ≠ c) (hjg : j ≠ g) (hjh : j ≠ h) (hcg : c ≠ g) (hch : c ≠ h)
    (hgh : g ≠ h) :
    Nat.card K ^ 4 ≤ Nat.card (stabTwoBar K i j) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K hn
  exact card_le_stabPairsBar_of_coords hQ hT (plusIndexEquiv n) (plusIndexEquiv n).injective
    (fun m => isHypCoord_coordinateQuadPlus m) hic hig hih hjc hjg hjh hcg hch hgh

end RootGroup

end CFSG.SeitzReduction.OmegaPilot
