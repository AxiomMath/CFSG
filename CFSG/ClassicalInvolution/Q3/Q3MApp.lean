module

public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.ClassicalInvolution.Q3.Q3MWiel

public section

namespace CFSG.ClassicalInvolution.Q3.M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification
open scoped MatrixGroups

theorem exists_hom_of_member {X : Type} [Group X] [Finite X] {L : Subgroup X} {z : X}
    (hz : IsClassicalMember3 L z) :
    ∃ φ : L →* SL(2, ZMod 3), Function.Surjective φ ∧ Odd (Nat.card φ.ker) := by
  obtain ⟨e⟩ := hz.nonempty_equiv
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L))).ker =
      classicalInvolutionOddCore L := by
    ext x
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore L)) x = 1 :=
        e.map_eq_one_iff.mp h
      exact (QuotientGroup.eq_one_iff x).mp h1
    · intro h
      have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore L)) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr h
      refine (MonoidHom.mem_ker).mpr ?_
      change e ((QuotientGroup.mk' (classicalInvolutionOddCore L)) x) = 1
      rw [h1]
      exact map_one e
  rw [hker]
  exact CFSG.ComponentClassification.OddCore.odd_card L

theorem kz_lemma {L : Type*} [Group L] [Finite L] (φ : L →* SL(2, ZMod 3))
    (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) {z : L} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hzc : ∀ g : L, g * z = z * g) {M : Subgroup L} [M.Normal] (hzM : z ∉ M) :
    ∀ x ∈ M, φ x = 1 := by
  have hodd : ∀ x : L, φ x = 1 → Odd (orderOf x) := fun x hx =>
    hker.of_dvd_nat (by
      have hx' : x ∈ φ.ker := hx
      have := orderOf_dvd_natCard (⟨x, hx'⟩ : φ.ker)
      rwa [Subgroup.orderOf_mk] at this)
  by_contra hex
  push Not at hex
  obtain ⟨x, hxM, hx1⟩ := hex
  have hKn : (M.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hw2 : φ z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hw1 : φ z ≠ 1 := fun h => by
    have := hodd z h
    rw [hzord] at this
    exact absurd this (by decide)
  have hwK : φ z ∈ M.map φ :=
    sl2_normal_inv (M.map φ) (Subgroup.mem_map_of_mem φ hxM) hx1 hw2 hw1
  obtain ⟨k, hkM, hk⟩ := Subgroup.mem_map.mp hwK
  have hodd' := hodd (k⁻¹ * z) (by rw [map_mul, map_inv, hk]; group)
  set m := orderOf (k⁻¹ * z) with hm
  have hzk : Commute k⁻¹ z := hzc k⁻¹
  have h1 : (k⁻¹ * z) ^ m = 1 := pow_orderOf_eq_one _
  rw [hzk.mul_pow] at h1
  obtain ⟨c, hc⟩ := hodd'
  have hzm : z ^ m = z := by rw [hc, pow_succ, pow_mul, hz2, one_pow, one_mul]
  rw [hzm] at h1
  have h3 : z = k ^ m := by
    have h2 : z = (k⁻¹ ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, ← inv_pow, inv_inv]
  exact hzM (h3 ▸ M.pow_mem hkM m)

theorem odd_index_of_Q {L : Type*} [Group L] [Finite L] (φ : L →* SL(2, ZMod 3))
    (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) {M : Subgroup L} [M.Normal]
    (hQ : sl2ThreeQ ≤ M.map φ) : Odd M.index := by
  have h1 : M.index = M.relIndex (M ⊔ φ.ker) * (M ⊔ φ.ker).index :=
    (Subgroup.relIndex_mul_index le_sup_left).symm
  have h2 : M.relIndex (M ⊔ φ.ker) = M.relIndex φ.ker :=
    Subgroup.relIndex_sup_left (H := φ.ker) (K := M)
  have h3 : Odd (M.relIndex φ.ker) := hker.of_dvd_nat (Subgroup.relIndex_dvd_card M φ.ker)
  have h4 : (M ⊔ φ.ker).index = (M.map φ).index := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ hφ]
  have h5 : (M.map φ).index ∣ 3 := by
    have := Subgroup.index_dvd_of_le hQ
    rwa [sl2ThreeQ_index] at this
  have h6 : Odd (M.map φ).index := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h5 with h | h <;> rw [h] <;> decide
  rw [h1, h2, h4]
  exact h3.mul h6


section Apply

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isSubnormal_subgroupOf_top' {C K : Subgroup X} (h : IsSubnormal K C) :
    (K.subgroupOf C).IsSubnormal := by
  have := isSubnormal_subgroupOf h C
  rw [Subgroup.subgroupOf_self] at this
  exact Components.mathlib_subnormal_of_chain this Subgroup.IsSubnormal.top

theorem wd_apply {Cg Tg Dg L : Subgroup X}
    (hCgT : ∀ c ∈ Cg, ∀ t ∈ Tg, c * t * c⁻¹ ∈ Tg)
    (hCgD : ∀ c ∈ Cg, ∀ d ∈ Dg, c * d * c⁻¹ ∈ Dg)
    (hcomm : ∀ t ∈ Tg, ∀ d ∈ Dg, t * d = d * t)
    (h2 : ∀ x ∈ Tg ⊓ Dg, ∃ j : ℕ, x ^ (2 ^ j) = 1)
    (h3 : ∀ c ∈ Cg, (∃ k : ℕ, c ^ (3 ^ k) = 1) → ∃ u ∈ Cg ⊓ Tg, ∃ v ∈ Cg ⊓ Dg, c = u * v)
    (hLC : IsSubnormal L Cg) (φ : L →* SL(2, ZMod 3)) (hφ : Function.Surjective φ)
    (hV : ∀ x : L, (x : X) ∈ Dg → φ x = 1) (hU : ∀ x : L, (x : X) ∈ Tg → φ x ^ 2 = 1) :
    False := by
  have hLle : L ≤ Cg := isSubnormal_le hLC
  have hUn : (Tg.subgroupOf Cg).Normal := ⟨fun u hu c => by
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    exact hCgT c c.2 u hu⟩
  have hVn : (Dg.subgroupOf Cg).Normal := ⟨fun u hu c => by
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    exact hCgD c c.2 u hu⟩
  have hL' : (L.subgroupOf Cg).IsSubnormal := isSubnormal_subgroupOf_top' hLC
  let ψ : L.subgroupOf Cg →* SL(2, ZMod 3) :=
    φ.comp (Subgroup.subgroupOfEquivOfLe hLle).toMonoidHom
  have hψ : Function.Surjective ψ := hφ.comp (Subgroup.subgroupOfEquivOfLe hLle).surjective
  refine wielandt_diagonal (U := Tg.subgroupOf Cg) (V := Dg.subgroupOf Cg) ?_ ?_ ?_ hL' ψ hψ
    ?_ ?_
  · intro u hu v hv
    exact Subtype.ext (hcomm u hu v hv)
  · intro x hx
    obtain ⟨j, hj⟩ := h2 x ⟨hx.1, hx.2⟩
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  · intro c ⟨k, hk⟩
    obtain ⟨u, hu, v, hv, huv⟩ := h3 c c.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact ⟨⟨u, hu.1⟩, hu.2, ⟨v, hv.1⟩, hv.2, Subtype.ext huv⟩
  · intro x hx
    exact hV (Subgroup.subgroupOfEquivOfLe hLle x) hx
  · intro x hx
    exact hU (Subgroup.subgroupOfEquivOfLe hLle x) hx

end Apply

end CFSG.ClassicalInvolution.Q3.M
