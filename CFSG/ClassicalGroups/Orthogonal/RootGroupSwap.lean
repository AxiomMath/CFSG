module

public import CFSG.ClassicalGroups.F2Swap
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixed
public import CFSG.ClassicalGroups.Orthogonal.RootGroupPair
public import Mathlib.RingTheory.SimpleRing.Principal
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.F2Swap QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def eichlerG (Q : QuadraticForm K V) (u w : V) : Gom Q :=
  ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩

theorem eichlerG_app {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (x : V) :
    (eichlerG Q u w).app x = x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u :=
  eichler_apply hu hw x

theorem eichlerG_mul {u v w : V} (hv : polar Q u v = 0) (hw : polar Q u w = 0) :
    eichlerG Q u v * eichlerG Q u w = eichlerG Q u (v + w) :=
  Subtype.ext (eichler_mul hv hw)

theorem eichlerG_zero (Q : QuadraticForm K V) (u : V) : eichlerG Q u 0 = 1 :=
  Subtype.ext (eichler_zero_right Q u)

theorem eichlerG_mul_self [CharP K 2] {u w : V} (hw : polar Q u w = 0) :
    eichlerG Q u w * eichlerG Q u w = 1 := by
  rw [eichlerG_mul hw hw, ← two_smul K w, CharTwo.two_eq_zero, zero_smul, eichlerG_zero]

theorem eichlerG_conj (g : Gom Q) (u w : V) :
    g * eichlerG Q u w * g⁻¹ = eichlerG Q (g.app u) (g.app w) :=
  Subtype.ext (eichler_conj (elementaryGroup_le_orthogonalGroup Q g.2) u w)

theorem eichlerG_smul_left (c : K) (u w : V) :
    eichlerG Q (c • u) w = eichlerG Q u (c • w) :=
  Subtype.ext (eichler_smul_left c u w)

theorem eichlerG_add_smul_self {u : V} (hu : Q u = 0) (w : V) (c : K) :
    eichlerG Q u (w + c • u) = eichlerG Q u w :=
  Subtype.ext (eichler_add_smul_self hu w c)

theorem eichlerG_mem_Lom {u w : V} (hw : polar Q u w = 0) : eichlerG Q u w ∈ Lom Q u :=
  eichler_mem_rootGroup hw

theorem eichlerG_pair_app_left [CharP K 2] {e f w : V} {t : K} (he : Q e = 0) (hf : Q f = 0)
    (ht : polar Q e f = t) (htne : t ≠ 0) (hew : polar Q e w = 0) (hfw : polar Q f w = 0)
    (hc : Q w ≠ 0) :
    (eichlerG Q e ((Q w * t)⁻¹ • w) * eichlerG Q f w).app e = (Q w * t) • f := by
  have hct : Q w * t ≠ 0 := mul_ne_zero hc htne
  have hew₀ : polar Q e ((Q w * t)⁻¹ • w) = 0 := by rw [polar_smul_right_eq, hew, mul_zero]
  have hee : polar Q e e = 0 := polar_self_eq_zero he
  have hwe : polar Q w e = 0 := by rw [polar_comm, hew]
  have hfe : polar Q f e = t := by rw [polar_comm, ht]
  have hww : polar Q w w = 0 := by rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hff : polar Q f f = 0 := polar_self_eq_zero hf
  rw [Gom.app_mul, eichlerG_app hf hfw e, eichlerG_app he hew₀]
  simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, polar_add_right, polar_sub_right,
    polar_smul_right_eq, hee, hwe, hfe, ht, hew, hfw, hww, hff, mul_zero, zero_add, add_zero,
    zero_smul, mul_neg, map_smul_eq_sq]
  match_scalars
  · field_simp
    linear_combination (Q w * t ^ 2) * (CharTwo.two_eq_zero (R := K))
  · field_simp
    ring
  · exact CharTwo.neg_eq _

theorem eichlerG_pair_app_param [CharP K 2] {e f w : V} {t : K} (he : Q e = 0) (hf : Q f = 0)
    (ht : polar Q e f = t) (htne : t ≠ 0) (hew : polar Q e w = 0) (hfw : polar Q f w = 0)
    (hc : Q w ≠ 0) :
    (eichlerG Q e ((Q w * t)⁻¹ • w) * eichlerG Q f w).app ((Q w * t)⁻¹ • w) =
      (Q w * t)⁻¹ • w := by
  have hew₀ : polar Q e ((Q w * t)⁻¹ • w) = 0 := by rw [polar_smul_right_eq, hew, mul_zero]
  have hwe : polar Q w e = 0 := by rw [polar_comm, hew]
  have hwf : polar Q w f = 0 := by rw [polar_comm, hfw]
  have hww : polar Q w w = 0 := by rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  rw [Gom.app_mul, eichlerG_app hf hfw, eichlerG_app he hew₀]
  simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, polar_add_right, polar_sub_right,
    polar_smul_right_eq, hwe, hwf, hww, mul_zero, zero_add, add_zero, zero_smul, sub_zero]

theorem eichlerG_braid [CharP K 2] {e f w : V} {t : K} (he : Q e = 0) (hf : Q f = 0)
    (ht : polar Q e f = t) (htne : t ≠ 0) (hew : polar Q e w = 0) (hfw : polar Q f w = 0)
    (hc : Q w ≠ 0) :
    eichlerG Q e ((Q w * t)⁻¹ • w) * eichlerG Q f w * eichlerG Q e ((Q w * t)⁻¹ • w) =
      eichlerG Q f w * eichlerG Q e ((Q w * t)⁻¹ • w) * eichlerG Q f w := by
  have hct : Q w * t ≠ 0 := mul_ne_zero hc htne
  obtain ⟨y, hy⟩ : ∃ y, y = eichlerG Q e ((Q w * t)⁻¹ • w) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = eichlerG Q f w := ⟨_, rfl⟩
  have k1 : (y * a).app e = (Q w * t) • f := by
    rw [hy, ha]; exact eichlerG_pair_app_left he hf ht htne hew hfw hc
  have k2 : (y * a).app ((Q w * t)⁻¹ • w) = (Q w * t)⁻¹ • w := by
    rw [hy, ha]; exact eichlerG_pair_app_param he hf ht htne hew hfw hc
  have hconj : (y * a) * y * (y * a)⁻¹ = a := by
    have h1 := eichlerG_conj (y * a) e ((Q w * t)⁻¹ • w)
    rw [← hy, k1, k2, eichlerG_smul_left] at h1
    have e1 : (Q w * t) • (Q w * t)⁻¹ • w = w := by
      rw [smul_smul, mul_inv_cancel₀ hct, one_smul]
    rw [e1, ← ha] at h1
    exact h1
  rw [← hy, ← ha]
  exact (mul_inv_eq_iff_eq_mul.mp hconj).trans (mul_assoc _ _ _).symm

theorem mem_normalizer_Lom {e : V} {n : Gom Q} {s : K} (hs : s ≠ 0) (hn : n.app e = s • e) :
    n ∈ Subgroup.normalizer (Lom Q e : Set (Gom Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hn' : n⁻¹.app e = s⁻¹ • e := by
    have h1 := Gom.app_inv_app n e
    rw [hn, Gom.map_smul] at h1
    calc n⁻¹.app e = s⁻¹ • (s • n⁻¹.app e) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      _ = s⁻¹ • e := by rw [h1]
  constructor
  · intro hx
    have := conj_mem_Lom n hx
    rwa [hn, Lom_smul hs] at this
  · intro hx
    have := conj_mem_Lom n⁻¹ hx
    rw [hn', Lom_smul (inv_ne_zero hs)] at this
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem closure_Lom_union_eichlerG (hQ : (polarBilin Q).Nondegenerate) {u u' w : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) (hw : polar Q u' w = 0)
    (hQw : Q w ≠ 0) :
    Subgroup.closure ((Lom Q u : Set (Gom Q)) ∪ {eichlerG Q u' w}) = ⊤ :=
  closure_subgroupOf_union_singleton (rootGroup_le_elementaryGroup Q u)
    (eichler_mem_elementaryGroup Q u' w) (rootGroup_sup_zpowers_eichler hQ hu hu' huu' hw hQw)

theorem exists_perp_eichlerG_eq {e f w : V} (hf : Q f = 0) (hef : polar Q e f ≠ 0)
    (hfw : polar Q f w = 0) :
    ∃ w' : V, polar Q e w' = 0 ∧ polar Q f w' = 0 ∧ Q w' = Q w ∧
      eichlerG Q f w' = eichlerG Q f w := by
  set s : K := -(polar Q e w * (polar Q e f)⁻¹) with hs
  refine ⟨w + s • f, ?_, ?_, ?_, eichlerG_add_smul_self hf w s⟩
  · rw [polar_add_right, polar_smul_right_eq, hs]
    field_simp
    ring
  · rw [polar_add_right, hfw, polar_smul_right_eq, polar_self_eq_zero hf, mul_zero, add_zero]
  · rw [QuadraticMap.map_add Q, map_smul_eq_sq, hf, polar_smul_right_eq, polar_comm Q w f, hfw]
    ring

@[expose] def eichlerNonA2Set (Q : QuadraticForm K V) (e f : V) : Set (Gom Q) :=
  {a | ∃ w, polar Q e w = 0 ∧ polar Q f w = 0 ∧ Q w ≠ 0 ∧ a = eichlerG Q f w}

theorem exists_ne_zero_ne (hK : 2 < Nat.card K) (r : K) : ∃ s : K, s ≠ 0 ∧ s ≠ r := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_contra! h
  have hsub : (Set.univ : Set K) ⊆ {0, r} := fun s _ => by
    by_cases hs : s = 0
    · simp [hs]
    · simp [h s hs]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have h2 : ({0, r} : Set K).ncard ≤ 2 := by
    calc ({0, r} : Set K).ncard ≤ ({r} : Set K).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem map_sub_smul_of_map_eq_zero {w w₀ : V} (hw : Q w = 0) (hQ0 : Q w₀ ≠ 0) (s : K) :
    Q (w - s • w₀) = s * Q w₀ * (s - polar Q w w₀ * (Q w₀)⁻¹) := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, ← neg_smul,
    map_smul_eq_sq, polar_smul_right_eq, hw]
  field_simp
  ring

theorem eichlerG_mem_closure_eichlerNonA2Set [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    {e f : V}
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f ≠ 0) (hK : 2 < Nat.card K) {w : V}
    (hew : polar Q e w = 0) (hfw : polar Q f w = 0) :
    eichlerG Q f w ∈ Subgroup.closure (eichlerNonA2Set Q e f) := by
  by_cases hQw : Q w ≠ 0
  · exact Subgroup.subset_closure ⟨w, hew, hfw, hQw, rfl⟩
  rw [not_not] at hQw
  by_cases hex : ∃ w₀, polar Q e w₀ = 0 ∧ polar Q f w₀ = 0 ∧ Q w₀ ≠ 0
  · obtain ⟨w₀, h0e, h0f, hQ0⟩ := hex
    obtain ⟨s, hs0, hsr⟩ := exists_ne_zero_ne hK (polar Q w w₀ * (Q w₀)⁻¹)
    have h1e : polar Q e (w - s • w₀) = 0 := by
      rw [polar_sub_right, polar_smul_right_eq, hew, h0e]; simp
    have h1f : polar Q f (w - s • w₀) = 0 := by
      rw [polar_sub_right, polar_smul_right_eq, hfw, h0f]; simp
    have h2e : polar Q e (s • w₀) = 0 := by rw [polar_smul_right_eq, h0e, mul_zero]
    have h2f : polar Q f (s • w₀) = 0 := by rw [polar_smul_right_eq, h0f, mul_zero]
    have hQ1 : Q (w - s • w₀) ≠ 0 := by
      rw [map_sub_smul_of_map_eq_zero hQw hQ0]
      exact mul_ne_zero (mul_ne_zero hs0 hQ0) (sub_ne_zero.mpr hsr)
    have hQ2 : Q (s • w₀) ≠ 0 := by
      rw [map_smul_eq_sq]
      exact mul_ne_zero (pow_ne_zero 2 hs0) hQ0
    have hsplit : eichlerG Q f w = eichlerG Q f (w - s • w₀) * eichlerG Q f (s • w₀) := by
      rw [eichlerG_mul h1f h2f, sub_add_cancel]
    rw [hsplit]
    exact mul_mem (Subgroup.subset_closure ⟨_, h1e, h1f, hQ1, rfl⟩)
      (Subgroup.subset_closure ⟨_, h2e, h2f, hQ2, rfl⟩)
  · push Not at hex
    have hw0 : w = 0 := by
      refine eq_zero_of_polar_eq_zero hQ fun y => ?_
      set t := polar Q e f with ht
      set p : V := y - (polar Q y f * t⁻¹) • e - (polar Q y e * t⁻¹) • f with hp
      have hpe : polar Q e p = 0 := by
        rw [hp, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
          polar_self_eq_zero he, ← ht, polar_comm Q e y]
        field_simp
        ring
      have hpf : polar Q f p = 0 := by
        rw [hp, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
          polar_self_eq_zero hf, polar_comm Q f e, ← ht, polar_comm Q f y]
        field_simp
        ring
      have hQp : Q p = 0 := hex p hpe hpf
      have hQwp : Q (w + p) = 0 :=
        hex _ (by rw [polar_add_right, hew, hpe, add_zero])
          (by rw [polar_add_right, hfw, hpf, add_zero])
      have hwp : polar Q w p = 0 := by
        have := QuadraticMap.map_add Q w p
        rw [hQwp, hQw, hQp] at this
        linear_combination -this
      have hy : y = (polar Q y f * t⁻¹) • e + (polar Q y e * t⁻¹) • f + p := by
        rw [hp]; abel
      have hwe : polar Q w e = 0 := by rw [polar_comm, hew]
      have hwf : polar Q w f = 0 := by rw [polar_comm, hfw]
      rw [hy, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hwe, hwf,
        hwp]
      ring
    rw [hw0, eichlerG_zero]
    exact one_mem _

theorem Lom_le_closure_eichlerNonA2Set [CharP K 2] (hQ : (polarBilin Q).Nondegenerate) {e f : V}
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f ≠ 0) (hK : 2 < Nat.card K) :
    Lom Q f ≤ Subgroup.closure (eichlerNonA2Set Q e f) := by
  intro x hx
  obtain ⟨w', hw', hxe⟩ := mem_rootGroup.mp (mem_Lom.mp hx)
  obtain ⟨w'', hbe, hbf, -, hxx⟩ := exists_perp_eichlerG_eq hf hef hw'
  rw [show x = eichlerG Q f w' from Subtype.ext hxe.symm, ← hxx]
  exact eichlerG_mem_closure_eichlerNonA2Set hQ he hf hef hK hbe hbf

theorem eichlerG_nonA2_data [CharP K 2] (hQ : (polarBilin Q).Nondegenerate) {e f : V} {g : Gom Q}
    (hgf : g.app e = f) (he : Q e = 0) (hef : polar Q e f ≠ 0) {w : V} (hew : polar Q e w = 0)
    (hfw : polar Q f w = 0) (hc : Q w ≠ 0) :
    eichlerG Q f w ∈ Lom Q f ∧ eichlerG Q f w * eichlerG Q f w = 1 ∧
      Subgroup.closure ((Lom Q e : Set (Gom Q)) ∪ {eichlerG Q f w}) = ⊤ ∧
      ∃ y ∈ Lom Q e, y * y = 1 ∧ Subgroup.closure ((Lom Q f : Set (Gom Q)) ∪ {y}) = ⊤ ∧
        y * eichlerG Q f w * y = eichlerG Q f w * y * eichlerG Q f w ∧
        g⁻¹ * (y * eichlerG Q f w) ∈ Subgroup.normalizer (Lom Q e : Set (Gom Q)) := by
  have hf : Q f = 0 := by rw [← hgf, Gom.map_of_mem, he]
  have hct : Q w * polar Q e f ≠ 0 := mul_ne_zero hc hef
  have hfe : polar Q f e ≠ 0 := by rwa [polar_comm]
  have hew₀ : polar Q e ((Q w * polar Q e f)⁻¹ • w) = 0 := by
    rw [polar_smul_right_eq, hew, mul_zero]
  have hQ0 : Q ((Q w * polar Q e f)⁻¹ • w) ≠ 0 := by
    rw [map_smul_eq_sq]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hct)) hc
  refine ⟨eichlerG_mem_Lom hfw, eichlerG_mul_self hfw,
    closure_Lom_union_eichlerG hQ he hf hef hfw hc, _, eichlerG_mem_Lom hew₀,
    eichlerG_mul_self hew₀, closure_Lom_union_eichlerG hQ hf he hfe hew₀ hQ0,
    eichlerG_braid he hf rfl hef hew hfw hc, ?_⟩
  refine mem_normalizer_Lom hct ?_
  rw [Gom.app_mul, eichlerG_pair_app_left he hf rfl hef hew hfw hc, Gom.map_smul]
  have : g⁻¹.app f = e := by rw [← hgf, Gom.app_inv_app]
  rw [this]

theorem Lom_le_invSub [CharP K 2] {M : Type*} [AddCommGroup M] [Finite M]
    (h2 : ∀ m : M, m + m = 0) [DistribMulAction (Gom Q) M] (hK : 2 < Nat.card K)
    (hQ : (polarBilin Q).Nondegenerate) {e f : V} {g : Gom Q} (hgf : g.app e = f) (he : Q e = 0)
    (hef : polar Q e f ≠ 0)
    (hdec : IsCompl (fixedSub M (Lom Q e : Set (Gom Q))) (fixedSub M (Lom Q f : Set (Gom Q))))
    {U : AddSubgroup M} (hU : U ≤ fixedSub M (Lom Q e : Set (Gom Q)))
    (hUN : ∀ n ∈ Subgroup.normalizer (Lom Q e : Set (Gom Q)), ∀ x ∈ U, n • x ∈ U) :
    Lom Q f ≤ invSub (Gom Q) (U ⊔ U.map (DistribSMul.toAddMonoidHom M g)) := by
  have hf : Q f = 0 := by rw [← hgf, Gom.map_of_mem, he]
  have hconj : (fun s => g * s * g⁻¹) '' (Lom Q e : Set (Gom Q)) = (Lom Q f : Set (Gom Q)) := by
    rw [image_conj_Lom g e, hgf]
  refine le_invSub_of_generators h2 hconj hdec hU hUN
    (Lom_le_closure_eichlerNonA2Set hQ he hf hef hK) ?_
  rintro a ⟨w, hew, hfw, hc, rfl⟩
  exact eichlerG_nonA2_data hQ hgf he hef hew hfw hc

theorem stroth_2_1_iii_omega (hQ : (polarBilin Q).Nondegenerate) (hK : 2 < Nat.card K)
    [CharP K 2] {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    [DistribMulAction (Gom Q) M] {u : V} {g : Gom Q} (hu : Q u = 0)
    (hug : polar Q u (g.app u) ≠ 0)
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q)))
      (fixedSub M (Lom Q (g.app u) : Set (Gom Q))))
    {U : AddSubgroup M} (hU : U ≤ fixedSub M (Lom Q u : Set (Gom Q)))
    (hUN : ∀ n ∈ Subgroup.normalizer (Lom Q u : Set (Gom Q)), ∀ x ∈ U, n • x ∈ U) :
    ∀ h : Gom Q, ∀ x ∈ U ⊔ U.map (DistribSMul.toAddMonoidHom M g),
      h • x ∈ U ⊔ U.map (DistribSMul.toAddMonoidHom M g) := by
  have hu' : Q (g.app u) = 0 := by rw [Gom.map_of_mem, hu]
  have hgu : polar Q (g.app u) u ≠ 0 := by rwa [polar_comm]
  have hconj := image_conj_Lom g u
  have hLL : Lom Q u ⊔ Lom Q (g.app u) = ⊤ :=
    sup_subgroupOf_eq_top (rootGroup_le_elementaryGroup Q u)
      (rootGroup_le_elementaryGroup Q (g.app u))
      (rootGroup_sup_eq_elementaryGroup hQ hu hu' hug)
  exact invariant_of_two_sided hLL (Lom_le_invSub h2 hK hQ rfl hu hug hdec hU hUN)
    (Lom_le_invSub h2 hK hQ (Gom.app_inv_app g u) hu' hgu hdec.symm
      (map_smul_le_fixedSub hconj hU) (normalizer_invariant_map hconj hUN))

end CFSG.ClassicalGroups.Orthogonal
