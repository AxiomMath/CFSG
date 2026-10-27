module

public import CFSG.GH74.GLS.Stage4.Q9.CharDecomp
public import CFSG.GH74.GLS.Stage4.Q9.ClassSumIdentity

public section

open scoped BigOperators Classical

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG.TwoRankLowerBound.Helpers

theorem glue_pair_count_sum {H : Type*} [Group H] [Fintype H] [DecidableEq H] (P Q : H → Prop)
    [DecidablePred P] [DecidablePred Q] (f : H → ℂ) :
    ∑ c : H, (∑ x : H, ∑ y : H, if P x ∧ Q y ∧ x * y = c then (1 : ℂ) else 0) * f c =
      ∑ x : H, ∑ y : H, if P x ∧ Q y then f (x * y) else 0 := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : P x ∧ Q y
  · simp [hxy.1, hxy.2]
  · simp only [hxy, ↓reduceIte]
    refine Finset.sum_eq_zero fun c _ => ?_
    have hc : ¬(P x ∧ Q y ∧ x * y = c) := fun h => hxy ⟨h.1, h.2.1⟩
    simp [hc]

theorem glue_ti_involution_pair {G : Type*} [Group G] {C : Subgroup G} {S : Set G}
    (hTI : IsTISubset S C) {z : G} (hz2 : orderOf z = 2)
    (hC : C = Subgroup.centralizer ({z} : Set G)) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hS2 : ∀ s ∈ S, orderOf s = 2 → s = z) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x * y ∈ S) : x ∈ C ∧ y ∈ C ∧ x ≠ z ∧ y ≠ z := by
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx, pow_two] at h
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy, pow_two] at h
  have hx1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hinv : (x * y)⁻¹ = y * x := by rw [mul_inv_rev, hy1, hx1]
  have hxC : x ∈ C := by
    refine CFSG.DihedralTIFusion.ti_mem_of_conj_mem hTI hxy ?_
    have h : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
      rw [hinv, hx1, ← mul_assoc, hxx, one_mul]
    rw [h]
    exact hSinv _ hxy
  have hyC : y ∈ C := by
    refine CFSG.DihedralTIFusion.ti_mem_of_conj_mem hTI hxy ?_
    have h : y * (x * y) * y⁻¹ = (x * y)⁻¹ := by
      rw [hinv, hy1]
      simp only [mul_assoc, hyy, mul_one]
    rw [h]
    exact hSinv _ hxy
  have hcomm : ∀ w ∈ C, z * w = w * z := by
    intro w hw
    rw [hC, Subgroup.mem_centralizer_iff] at hw
    exact hw z (Set.mem_singleton z)
  have hne1 : x * y ≠ 1 := fun h => hTI.2.1 (h ▸ hxy)
  refine ⟨hxC, hyC, ?_, ?_⟩
  · rintro rfl
    have hsq : (x * y) ^ 2 = 1 := by
      have h := hcomm y hyC
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; simp only [mul_assoc]
        _ = x * (x * y) * y := by rw [← h]
        _ = 1 := by simp only [← mul_assoc, hxx, one_mul, hyy]
    have hord : orderOf (x * y) = 2 := orderOf_eq_prime hsq hne1
    have hzs : x * y = x := hS2 _ hxy hord
    have hy' : y = 1 := by simpa using hzs
    rw [hy', orderOf_one] at hy
    omega
  · rintro rfl
    have hsq : (x * y) ^ 2 = 1 := by
      have h := hcomm x hxC
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; simp only [mul_assoc]
        _ = x * (x * y) * y := by rw [h]
        _ = 1 := by simp only [← mul_assoc, hxx, one_mul, hyy]
    have hord : orderOf (x * y) = 2 := orderOf_eq_prime hsq hne1
    have hzs : x * y = y := hS2 _ hxy hord
    have hx' : x = 1 := by simpa using hzs
    rw [hx', orderOf_one] at hx
    omega

@[expose] noncomputable def involutionPairCount {G : Type*} [Group G] [Fintype G] (g : G) : ℂ :=
  ∑ x : G, ∑ y : G, if orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = g then 1 else 0

theorem involutionPairCount_conj {G : Type*} [Group G] [Fintype G] (g h : G) :
    involutionPairCount (h * g * h⁻¹) = involutionPairCount g := by
  unfold involutionPairCount
  refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun x => ?_
  refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun y => ?_
  have hx : orderOf (h⁻¹ * x * h) = orderOf x := by
    have := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) x
    simpa using this
  have hy : orderOf (h⁻¹ * y * h) = orderOf y := by
    have := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) y
    simpa using this
  have hxy : (h⁻¹ * x * h) * (h⁻¹ * y * h) = g ↔ x * y = h * g * h⁻¹ := by
    constructor
    · intro H
      calc x * y = h * ((h⁻¹ * x * h) * (h⁻¹ * y * h)) * h⁻¹ := by group
        _ = h * g * h⁻¹ := by rw [H]
    · intro H
      calc (h⁻¹ * x * h) * (h⁻¹ * y * h) = h⁻¹ * (x * y) * h := by group
        _ = g := by rw [H]; group
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, inv_inv]
  simp only [hx, hy, hxy]

theorem involutionPairCount_eq_zero {G : Type*} [Group G] [Fintype G] {C : Subgroup G} {S : Set G}
    (hTI : IsTISubset S C) {z : G} (hz2 : orderOf z = 2)
    (hC : C = Subgroup.centralizer ({z} : Set G)) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hS2 : ∀ s ∈ S, orderOf s = 2 → s = z) {s : G} (hs : s ∈ S) (hsC : s ∉ C) :
    involutionPairCount s = 0 := by
  unfold involutionPairCount
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  rw [ite_eq_right_iff]
  rintro ⟨hx, hy, hxy⟩
  have h := glue_ti_involution_pair hTI hz2 hC hSinv hS2 hx hy (hxy ▸ hs)
  exact absurd (hxy ▸ C.mul_mem h.1 h.2.1) hsC

theorem involutionPairCount_eq_sum {G : Type*} [Group G] [Fintype G] {C : Subgroup G} [Fintype C]
    {S : Set G} (hTI : IsTISubset S C) {z : G} (hz2 : orderOf z = 2)
    (hC : C = Subgroup.centralizer ({z} : Set G)) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hS2 : ∀ s ∈ S, orderOf s = 2 → s = z) (c : C) (hc : (c : G) ∈ S) :
    involutionPairCount (c : G) =
      ∑ x : C, ∑ y : C, if (orderOf x = 2 ∧ (x : G) ≠ z) ∧ (orderOf y = 2 ∧ (y : G) ≠ z) ∧
        x * y = c then (1 : ℂ) else 0 := by
  unfold involutionPairCount
  rw [← Fintype.sum_prod_type' (fun x y : G =>
      if orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = (c : G) then (1 : ℂ) else 0),
    ← Fintype.sum_prod_type' (fun x y : C =>
      if (orderOf x = 2 ∧ (x : G) ≠ z) ∧ (orderOf y = 2 ∧ (y : G) ≠ z) ∧ x * y = c
        then (1 : ℂ) else 0)]
  symm
  refine Fintype.sum_of_injective (fun p : C × C => ((p.1 : G), (p.2 : G)))
    (Subtype.val_injective.prodMap Subtype.val_injective) _ _ ?_ ?_
  · intro p hp
    rw [ite_eq_right_iff]
    rintro ⟨hx, hy, hxy⟩
    have h := glue_ti_involution_pair hTI hz2 hC hSinv hS2 hx hy (hxy ▸ hc)
    exact absurd ⟨(⟨p.1, h.1⟩, ⟨p.2, h.2.1⟩), rfl⟩ hp
  · intro p
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨⟨hx, -⟩, ⟨hy, -⟩, hxy⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe]
        exact hx
      · rw [Subgroup.orderOf_coe]
        exact hy
      · rw [← Subgroup.coe_mul, hxy]
    · rintro ⟨hx, hy, hxy⟩
      have h := glue_ti_involution_pair hTI hz2 hC hSinv hS2 hx hy (hxy ▸ hc)
      refine ⟨⟨?_, h.2.2.1⟩, ⟨?_, h.2.2.2⟩, ?_⟩
      · rw [← Subgroup.orderOf_coe]
        exact hx
      · rw [← Subgroup.orderOf_coe]
        exact hy
      · exact Subtype.ext hxy

@[expose] noncomputable def involutionPairSum {G : Type*} [Group G] [Fintype G] (f : G → ℂ) : ℂ :=
  ∑ x : G, ∑ y : G, if orderOf x = 2 ∧ orderOf y = 2 then f (x * y) else 0

theorem involutionPairSum_add_sub {G : Type*} [Group G] [Fintype G] (f₁ f₂ f₃ : G → ℂ) :
    involutionPairSum (f₁ + f₂ - f₃) =
      involutionPairSum f₁ + involutionPairSum f₂ - involutionPairSum f₃ := by
  unfold involutionPairSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem involutionPairSum_eq_sum_count {G : Type*} [Group G] [Fintype G] (f : G → ℂ) :
    involutionPairSum f = ∑ g : G, involutionPairCount g * f g :=
  (glue_pair_count_sum (fun x : G => orderOf x = 2) (fun y : G => orderOf y = 2) f).symm

theorem involutionPairSum_induced {G : Type} [Group G] [Fintype G] (C : Subgroup G) [Fintype C]
    (S : Set G) (hTI : IsTISubset S C) {z : G} (hz2 : orderOf z = 2)
    (hC : C = Subgroup.centralizer ({z} : Set G)) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hS2 : ∀ s ∈ S, orderOf s = 2 → s = z) (θ : C → ℂ) (hclass : BlocksIsClassFunction θ)
    (hθS : ∀ c : C, (c : G) ∉ S → θ c = 0) :
    involutionPairSum (inducedFunction C θ) =
      (C.index : ℂ) * ∑ x : C, ∑ y : C, if (orderOf x = 2 ∧ (x : G) ≠ z) ∧
        (orderOf y = 2 ∧ (y : G) ≠ z) then θ (x * y) else 0 := by
  obtain ⟨hvan, hagree, -⟩ :=
    CFSG.DihedralTIFusion.ti_supported_induction_isometry hTI hclass hclass hθS hθS
  set w : G → ℂ := fun g => involutionPairCount g * inducedFunction C θ g with hw
  have hwclass : BlocksIsClassFunction w := fun g h => by
    simp only [hw]
    rw [involutionPairCount_conj, inducedFunction_conjugate]
  have hwvan : ∀ g ∉ ⋃ a : G, (fun y => a⁻¹ * y * a) '' S, w g = 0 := fun g hg => by
    simp only [hw, hvan g hg, mul_zero]
  have hb : ∑ g : G, w g = ∑ᶠ g ∈ ⋃ a : G, (fun y => a⁻¹ * y * a) '' S, w g := by
    rw [finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g ∈ ⋃ a : G, (fun y => a⁻¹ * y * a) '' S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg, hwvan g hg]
  have hc := (CFSG.DihedralTIFusion.ti_conjugacy_support_sum hTI w hwclass).1
  have hd : ∑ᶠ d ∈ S, w d = ∑ c : C, involutionPairCount (c : G) * θ c := by
    rw [finsum_mem_def, finsum_eq_sum_of_fintype]
    symm
    refine Fintype.sum_of_injective (Subtype.val : C → G) Subtype.val_injective _ _ ?_ ?_
    · intro d hd
      by_cases hdS : d ∈ S
      · have hdC : d ∉ C := fun h => hd ⟨⟨d, h⟩, rfl⟩
        rw [Set.indicator_of_mem hdS]
        simp only [hw, involutionPairCount_eq_zero hTI hz2 hC hSinv hS2 hdS hdC, zero_mul]
      · exact Set.indicator_of_notMem hdS w
    · intro c
      by_cases hcS : (c : G) ∈ S
      · rw [Set.indicator_of_mem hcS]
        simp only [hw, hagree c hcS]
      · rw [Set.indicator_of_notMem hcS, hθS c hcS, mul_zero]
  have he : ∑ c : C, involutionPairCount (c : G) * θ c =
      ∑ c : C, (∑ x : C, ∑ y : C, if (orderOf x = 2 ∧ (x : G) ≠ z) ∧ (orderOf y = 2 ∧ (y : G) ≠ z) ∧
        x * y = c then (1 : ℂ) else 0) * θ c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hcS : (c : G) ∈ S
    · rw [involutionPairCount_eq_sum hTI hz2 hC hSinv hS2 c hcS]
    · rw [hθS c hcS, mul_zero, mul_zero]
  rw [involutionPairSum_eq_sum_count]
  have hww : ∀ g : G, involutionPairCount g * inducedFunction C θ g = w g := fun g => rfl
  simp only [hww]
  rw [hb, hc, hd, he, glue_pair_count_sum]

theorem involutionPairSum_decomp {G : Type} [Group G] [Fintype G] {z : G} (hz2 : orderOf z = 2)
    (hone : ∀ u : G, orderOf u = 2 → IsConj z u) {Ψ Φ : G → ℂ} (hΨ : Ψ ∈ BlocksIrr G)
    (hΦ : Φ ∈ BlocksIrr G) {x : ℕ} {a : ℤ} (hx : 1 ≤ x) (hΨ1 : Ψ 1 = x)
    (hΦ1 : Φ 1 = (x : ℂ) + 1) (hΨz : Ψ z = a) (hΦz : Φ z = (a : ℂ) + 1) :
    (x : ℂ) * (x + 1) * involutionPairSum (1 + Ψ - Φ) =
      ((Nat.card G / Nat.card (Subgroup.centralizer ({z} : Set G)) : ℕ) : ℂ) ^ 2 *
        ((x : ℂ) - a) ^ 2 := by
  have h1 : involutionPairSum (1 : G → ℂ) =
      ((Nat.card G / Nat.card (Subgroup.centralizer ({z} : Set G)) : ℕ) : ℂ) ^ 2 := by
    have h := sum_irr_invol_products (decomp_one_mem_blocksIrr G) hz2 hone
    simpa [involutionPairSum] using h
  have h2 : involutionPairSum Ψ =
      ((Nat.card G / Nat.card (Subgroup.centralizer ({z} : Set G)) : ℕ) : ℂ) ^ 2 * (a : ℂ) ^ 2 /
        x := by
    have h := sum_irr_invol_products hΨ hz2 hone
    rw [hΨ1, hΨz] at h
    exact h
  have h3 : involutionPairSum Φ =
      ((Nat.card G / Nat.card (Subgroup.centralizer ({z} : Set G)) : ℕ) : ℂ) ^ 2 *
        ((a : ℂ) + 1) ^ 2 / ((x : ℂ) + 1) := by
    have h := sum_irr_invol_products hΦ hz2 hone
    rw [hΦ1, hΦz] at h
    exact h
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
  have hx1 : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : x + 1 ≠ 0)
  rw [involutionPairSum_add_sub, h1, h2, h3]
  field_simp
  ring

theorem q9_glue {G : Type} [Group G] [Fintype G] (C : Subgroup G) [Fintype C] (S : Set G)
    (hTI : IsTISubset S C) {z : G} (hz2 : orderOf z = 2) (hzS : z ∈ S)
    (hC : C = Subgroup.centralizer ({z} : Set G))
    (hone : ∀ u : G, orderOf u = 2 → IsConj z u)
    (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (hS2 : ∀ s ∈ S, orderOf s = 2 → s = z)
    (θ : C → ℂ) (hθ : θ ∈ BlocksVChar C) (hθS : ∀ c : C, (c : G) ∉ S → θ c = 0)
    (hθθ : BlocksInnerProduct θ θ = 3) (hθ1 : BlocksInnerProduct θ 1 = 1)
    (hθone : θ 1 = 0) (hθz : ∀ h : C, (h : G) = z → θ h = 0) (κ : ℂ)
    (hκ : ∑ x ∈ (Finset.univ.filter fun x : C => orderOf x = 2 ∧ (x : G) ≠ z),
            ∑ y ∈ (Finset.univ.filter fun y : C => orderOf y = 2 ∧ (y : G) ≠ z), θ (x * y) = κ) :
    ∃ (x : ℕ) (a : ℤ), 1 ≤ x ∧ |a| ≤ (x : ℤ) ∧ 1 + (a + 1) ^ 2 + a ^ 2 ≤ (Nat.card C : ℤ) ∧
      ((Nat.card G / Nat.card C : ℕ) : ℂ) * ((x : ℂ) - a) ^ 2 = κ * x * (x + 1) := by
  obtain ⟨Ψ, Φ, x, a, hΨ, hΦ, -, -, -, hΘ, hΨx, hΦx, hΨz, hΦz, hx, ha, hbound⟩ :=
    q9_decomp C S hTI hz2 hzS hC θ hθ hθS hθθ hθ1 hθone hθz
  refine ⟨x, a, hx, ha, hbound, ?_⟩
  have hclass : BlocksIsClassFunction θ := blocksVChar_isClassFunction hθ
  have hII := involutionPairSum_induced C S hTI hz2 hC hSinv hS2 θ hclass hθS
  have hI := involutionPairSum_decomp hz2 hone hΨ hΦ hx hΨx hΦx hΨz hΦz
  rw [← hΘ, hII] at hI
  have hκ' : ∑ x : C, ∑ y : C, (if (orderOf x = 2 ∧ (x : G) ≠ z) ∧
      (orderOf y = 2 ∧ (y : G) ≠ z) then θ (x * y) else 0) = κ := by
    rw [← hκ, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_filter]
    by_cases hx : orderOf x = 2 ∧ (x : G) ≠ z
    · simp [hx]
    · simp [hx]
  rw [hκ'] at hI
  have hidx : Nat.card G / Nat.card C = C.index := by
    rw [← C.card_mul_index, Nat.mul_div_cancel_left _ Nat.card_pos]
  have hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card C := by rw [hC]
  rw [hcard, hidx] at hI
  rw [hidx]
  have hidx0 : (C.index : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  refine mul_left_cancel₀ hidx0 ?_
  linear_combination -hI

end CFSG.GH74.GLS.Stage4.Q9
