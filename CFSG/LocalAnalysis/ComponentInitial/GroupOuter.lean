module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralKernel

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer centerQuotient_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom
  centerQuotientHom_injective)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section CenterQuotient

variable (L : Type*) [Group L]

@[expose] noncomputable def outerOfCenterQuotient : MulAut L →* Outer (L ⧸ center L) :=
  (QuotientGroup.mk' (OuterAutomorphisms.inner (L ⧸ center L))).comp (centerQuotientHom L)

variable {L}

theorem exists_conj_eq_of_outerOfCenterQuotient_eq_one [Group.IsPerfect L] {a : MulAut L}
    (ha : outerOfCenterQuotient L a = 1) : ∃ x : L, MulAut.conj x = a := by
  have hinner : centerQuotientHom L a ∈ OuterAutomorphisms.inner (L ⧸ center L) :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨q, hq⟩ := hinner
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) q
  exact ⟨x, centerQuotientHom_injective L ((centerQuotient_conj x).trans hq)⟩

theorem outerOfCenterQuotient_injective [Finite L] [Group.IsPerfect L]
    {A : Subgroup (MulAut L)} (hA : IsPGroup 2 A)
    (hfix : ∀ a ∈ A, orderOf a = 2 → ∃ R : Sylow 2 (fixedSubgroup a),
      (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ center L) :
    Function.Injective ((outerOfCenterQuotient L).comp A.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro b hb
  by_contra hb1
  obtain ⟨k, hk⟩ := hA b
  obtain ⟨j, -, hbj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hb1 (orderOf_eq_one_iff.mp (by rw [hbj, pow_zero]))
  set c := b ^ 2 ^ (j - 1) with hc
  have hc2 : orderOf (c : MulAut L) = 2 := by
    rw [orderOf_coe, hc, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hbj]; exact Nat.pow_dvd_pow 2 (Nat.sub_le j 1)), hbj,
      Nat.pow_div (Nat.sub_le j 1) two_pos, show j - (j - 1) = 1 by omega, pow_one]
  have hcker : outerOfCenterQuotient L c = 1 := by
    change ((outerOfCenterQuotient L).comp A.subtype) c = 1
    rw [hc, map_pow, hb, one_pow]
  obtain ⟨x, hx⟩ := exists_conj_eq_of_outerOfCenterQuotient_eq_one hcker
  obtain ⟨m, hm, n, hn⟩ := exists_odd_pow_orderOf_eq_two_pow x
  have hconj : MulAut.conj (x ^ m) = (c : MulAut L) := by
    obtain ⟨t, rfl⟩ := hm
    rw [map_pow, hx, pow_succ, pow_mul, ← hc2, pow_orderOf_eq_one, one_pow, one_mul]
  have hfixed : x ^ m ∈ fixedSubgroup (c : MulAut L) := by
    change (c : MulAut L) (x ^ m) = x ^ m
    rw [← hconj, MulAut.conj_apply, mul_inv_cancel_right]
  obtain ⟨R, hR⟩ := hfix c c.2 hc2
  have hcentral : x ^ m ∈ center L := by
    by_contra hnot
    exact not_sylow_map_le_of_mem le_rfl hfixed ⟨n, hn⟩ hnot R hR
  have hone : (c : MulAut L) = 1 := by
    rw [← hconj]
    ext y
    rw [MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.mp hcentral y,
      mul_inv_cancel_right]
  rw [hone, orderOf_one] at hc2
  exact absurd hc2 (by norm_num)

theorem exists_elementaryAbelian_outer_centerQuotient [Finite L] [Group.IsPerfect L]
    {A : Subgroup (MulAut L)} [IsElementaryAbelian 2 A] {d : ℕ} (hd : Nat.card A = 2 ^ d)
    (hfix : ∀ a ∈ A, orderOf a = 2 → ∃ R : Sylow 2 (fixedSubgroup a),
      (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ center L) :
    ∃ E : Subgroup (Outer (L ⧸ center L)), IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ d := by
  have hinj := outerOfCenterQuotient_injective (IsElementaryAbelian.isPGroup 2 A) hfix
  let e := MonoidHom.ofInjective hinj
  refine ⟨((outerOfCenterQuotient L).comp A.subtype).range, ?_, ?_⟩
  · exact isElementaryAbelian_of_injective (f := e.symm.toMonoidHom) e.symm.injective
  · rw [← hd]
    exact (Nat.card_congr e.toEquiv).symm

theorem central_fixed_sylow_two_automorphisms_inject_into_outer_quotient [Finite L]
    [Group.IsPerfect L] {A : Subgroup (MulAut L)} (hA : IsPGroup 2 A)
    (hfix : ∀ a ∈ A, orderOf a = 2 → ∃ R : Sylow 2 (fixedSubgroup a),
      (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ center L) :
    Function.Injective ((outerOfCenterQuotient L).comp A.subtype) ∧
      ∀ d : ℕ, IsElementaryAbelian 2 A → Nat.card A = 2 ^ d →
        ∃ E : Subgroup (Outer (L ⧸ center L)), IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ d :=
  ⟨outerOfCenterQuotient_injective hA hfix, fun _ _ hd =>
    exists_elementaryAbelian_outer_centerQuotient hd hfix⟩

end CenterQuotient

section OuterDivisor

variable {G : Type*} [Group G]

@[expose] def autStabilizer (U : Subgroup G) : Subgroup (MulAut G) where
  carrier := {ψ | ∀ x, ψ x ∈ U ↔ x ∈ U}
  mul_mem' {ψ₁ ψ₂} h₁ h₂ x := by
    rw [MulAut.mul_apply]
    exact (h₁ (ψ₂ x)).trans (h₂ x)
  one_mem' _ := Iff.rfl
  inv_mem' {ψ} h x := by
    have h' := h (ψ⁻¹ x)
    rw [MulAut.apply_inv_self] at h'
    exact h'.symm

theorem mem_autStabilizer {U : Subgroup G} {ψ : MulAut G} :
    ψ ∈ autStabilizer U ↔ ∀ x, ψ x ∈ U ↔ x ∈ U :=
  Iff.rfl

@[expose] def autRestrict (U : Subgroup G) : autStabilizer U →* MulAut U where
  toFun ψ :=
    { toFun := fun u => ⟨(ψ : MulAut G) u, (mem_autStabilizer.mp ψ.2 u).mpr u.2⟩
      invFun := fun u => ⟨(ψ : MulAut G)⁻¹ u, (mem_autStabilizer.mp (inv_mem ψ.2) u).mpr u.2⟩
      left_inv := fun _ => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun _ => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun u v => Subtype.ext (map_mul (ψ : MulAut G) (u : G) v) }
  map_one' := rfl
  map_mul' _ _ := rfl

theorem card_outer_dvd_card_outer [Finite G] (U : Subgroup G)
    (hconj : ∀ φ : MulAut G, ∃ g : G, U.map φ.toMonoidHom = U.map (MulAut.conj g).toMonoidHom)
    (hinner : ∀ φ : MulAut G, (∀ u ∈ U, φ u = u) → ∃ g : G, MulAut.conj g = φ) :
    Nat.card (Outer G) ∣ Nat.card (Outer U) := by
  set A := autStabilizer U
  set I := OuterAutomorphisms.inner G
  set r := autRestrict U
  set M := I.subgroupOf A
  have hsup : A ⊔ I = ⊤ := by
    refine eq_top_iff.mpr fun φ _ => ?_
    obtain ⟨g, hg⟩ := hconj φ
    have hψ : (MulAut.conj g)⁻¹ * φ ∈ A := by
      intro x
      have h := Subgroup.ext_iff.mp hg (φ x)
      rw [mem_map_equiv, mem_map_equiv, MulEquiv.symm_apply_apply] at h
      rw [MulAut.mul_apply, MulAut.inv_def]
      exact h.symm
    have hφ : φ = MulAut.conj g * ((MulAut.conj g)⁻¹ * φ) := by group
    rw [hφ]
    exact mul_mem (mem_sup_right ⟨g, rfl⟩) (mem_sup_left hψ)
  have hOutG : Nat.card (Outer G) = M.index := by
    rw [← index_eq_card, ← relIndex_top_right, ← hsup, relIndex_sup_right]
    rfl
  have hker : r.ker ≤ M := by
    intro ψ hψ
    have hfix : ∀ u ∈ U, (ψ : MulAut G) u = u := fun u hu => by
      have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hψ) (⟨u, hu⟩ : U)
      exact congrArg Subtype.val h
    exact hinner ψ hfix
  have hmap : (M.map r).relIndex r.range = M.index := by
    have e1 := index_map M r
    rw [sup_eq_left.mpr hker] at e1
    have e2 := relIndex_mul_index (map_le_range r M)
    have hne : r.range.index ≠ 0 := index_ne_zero_of_finite
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (e2.trans e1)
  have hinnerU : OuterAutomorphisms.inner U ≤ M.map r := by
    rintro _ ⟨u, rfl⟩
    have hA : MulAut.conj (u : G) ∈ A := fun x => by
      rw [MulAut.conj_apply, mul_mem_cancel_right (inv_mem u.2), mul_mem_cancel_left u.2]
    exact ⟨⟨MulAut.conj (u : G), hA⟩, ⟨u, rfl⟩, rfl⟩
  rw [hOutG, ← hmap, ← index_eq_card]
  exact (relIndex_dvd_of_le_left r.range hinnerU).trans
    (relIndex_dvd_index_of_le (hinnerU.trans (map_le_range r M)))

end OuterDivisor

end CFSG.LocalAnalysis.ComponentInitial
