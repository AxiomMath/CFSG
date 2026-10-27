module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_ordE6_dvd_ordF4 {e : ℕ} (he : 1 ≤ e) :
    ¬ CFSG.Open.ordE6 (2 ^ e) ∣ CFSG.Open.ordF4 (2 ^ (2 * e)) := by
  intro h
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 9 * e) (by omega)
    (by omega)
  have h1 : p ∣ CFSG.Open.ordE6 (2 ^ e) :=
    ((EvenExc.profile_ordE6' he).prim p (9 * e) hp (by omega)).2
      (Or.inr (Or.inl ⟨1, by ring⟩))
  have h2 := ((EvenExc.profile_ordF4' (by omega : 1 ≤ 2 * e)).prim p (9 * e) hp (by omega)).1
    (h1.trans h)
  have hd : ∀ m : ℕ, 9 * e ∣ 2 * e * m → 9 ∣ 2 * m := fun m hm => by
    have : 9 * e ∣ (2 * m) * e := by rw [show 2 * m * e = 2 * e * m by ring]; exact hm
    exact Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < e) this
  rcases h2 with h2 | h2 | h2 | h2
  · exact absurd (hd 12 h2) (by norm_num)
  · exact absurd (hd 8 h2) (by norm_num)
  · exact absurd (hd 6 h2) (by norm_num)
  · exact absurd (hd 2 h2) (by norm_num)

theorem not_ordTwistedE6_dvd_ordF4 {e : ℕ} (he : 1 ≤ e) :
    ¬ CFSG.Open.ordTwistedE6 (2 ^ e) ∣ CFSG.Open.ordF4 (2 ^ (2 * e)) := by
  intro h
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 10 * e) (by omega)
    (by omega)
  have hnd : ¬ 10 * e ∣ e * 5 := fun h5 => by
    have := Nat.le_of_dvd (by omega) h5
    omega
  have h1 : p ∣ CFSG.Open.ordTwistedE6 (2 ^ e) :=
    ((EvenExc.profile_ordTwistedE6' he).prim p (10 * e) hp (by omega)).2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨1, by ring⟩, hnd⟩)))))
  have h2 := ((EvenExc.profile_ordF4' (by omega : 1 ≤ 2 * e)).prim p (10 * e) hp (by omega)).1
    (h1.trans h)
  have hd : ∀ m : ℕ, 10 * e ∣ 2 * e * m → 10 ∣ 2 * m := fun m hm => by
    have : 10 * e ∣ (2 * m) * e := by rw [show 2 * m * e = 2 * e * m by ring]; exact hm
    exact Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < e) this
  rcases h2 with h2 | h2 | h2 | h2
  · exact absurd (hd 12 h2) (by norm_num)
  · exact absurd (hd 8 h2) (by norm_num)
  · exact absurd (hd 6 h2) (by norm_num)
  · exact absurd (hd 2 h2) (by norm_num)

section General

variable {G : Type*} [Group G]

theorem eqLocus_perfect_card_of_canonicalGraphFixedSubgroup {Gm : Type*} [Group Gm]
    {C J : Subgroup Gm} {P : Gm} (hcan : CanonicalGraphFixedSubgroup C J P) {η : MulAut C}
    (hη : ∀ g : C, (η g : Gm) = P * g * P⁻¹) {k : Type} [Field k]
    (eJ : J ≃* adjointGroup .F4 k) (hperfk : Group.IsPerfect (adjointGroup .F4 k)) :
    ⁅η.toMonoidHom.eqLocus (MonoidHom.id C), η.toMonoidHom.eqLocus (MonoidHom.id C)⁆ =
        η.toMonoidHom.eqLocus (MonoidHom.id C) ∧
      Nat.card (η.toMonoidHom.eqLocus (MonoidHom.id C)) = Nat.card (adjointGroup .F4 k) := by
  obtain ⟨η₀, hη₀, -, hJC, hfix₀, -⟩ := hcan
  have hη₀η : η₀ = η := MulEquiv.ext fun g => Subtype.ext ((hη₀ g).trans (hη g).symm)
  subst hη₀η
  have hfix : η₀.toMonoidHom.eqLocus (MonoidHom.id C) = J.subgroupOf C := by
    ext g
    rw [mem_subgroupOf]
    exact hfix₀ g
  have hJJ : ⁅J, J⁆ = J := by
    have hrange : (J.subtype.comp eJ.symm.toMonoidHom).range = J := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (eJ.symm y).2
      · intro hx
        exact ⟨eJ ⟨x, hx⟩, by simp⟩
    rw [← hrange]
    exact commutator_monoidHom_range_eq_of_isPerfect _
  refine ⟨?_, ?_⟩
  · rw [hfix]
    apply Subgroup.map_injective C.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJC, hJJ]
  · rw [hfix, Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv, Nat.card_congr eJ.toEquiv]

theorem normalizerMulAut_sq_eq_one {M : Subgroup G} {X : Type*} [Group X] (eM : M ≃* X) {t : G}
    (ht : orderOf t = 2) (htM : t ∈ normalizer (M : Set G)) :
    normalizerMulAut eM ⟨t, htM⟩ ^ 2 = 1 := by
  have h1 : (⟨t, htM⟩ : normalizer (M : Set G)) ^ 2 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one]; rfl)
  rw [← map_pow, h1, map_one]

theorem exists_inner_of_normalizerMulAut_mem_range {M : Subgroup G} {X : Type*} [Group X]
    (eM : M ≃* X) {t : G} (htM : t ∈ normalizer (M : Set G))
    (h : normalizerMulAut eM ⟨t, htM⟩ ∈ (MulAut.conj : X →* MulAut X).range) :
    ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(eM.symm c : G), (eM.symm c).2, fun x hx => ?_⟩
  have h' := coe_symm_normalizerMulAut_apply eM ⟨t, htM⟩ (eM ⟨x, hx⟩)
  rw [← hc] at h'
  simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h'
  exact h'.symm

end General

end CFSG.SeitzReduction.F4Pilot
