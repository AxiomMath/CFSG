module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Basic

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem odd_index_of_sylow_le {S : Sylow 2 G} {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) :
    Odd H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := S.not_dvd_index
  have hdvd : H.index ∣ (S : Subgroup G).index := Subgroup.index_dvd_of_le hSH
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hS (h.trans hdvd))

theorem exists_conj_le_of_odd_index {H P : Subgroup G} (hH : Odd H.index)
    (hP : IsPGroup 2 P) : ∃ g : G, ∀ p ∈ P, g⁻¹ * p * g ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints (G ⧸ H)
  rw [← Subgroup.index_eq_card] at hmod
  have hfix : Nat.card (MulAction.fixedPoints P (G ⧸ H)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have h := Nat.odd_iff.mp hH
    have h' := hmod.symm
    unfold Nat.ModEq at h'
    omega
  have : Nonempty (MulAction.fixedPoints P (G ⧸ H)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints P (G ⧸ H)) := Nat.pos_of_ne_zero hfix
    exact (Nat.card_pos_iff.mp hpos).1
  obtain ⟨⟨q, hq⟩⟩ := this
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, fun p hp => ?_⟩
  have h := hq ⟨p, hp⟩
  change (p : G) • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g at h
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h
  simpa only [smul_eq_mul, mul_inv_rev, mul_assoc, inv_inv] using H.inv_mem h

theorem le_of_fixesOnly {H P X : Subgroup G} (hH : Odd H.index) (hP : IsPGroup 2 P)
    (hXP : X ≤ P) (hX : FixesOnly H X) : P ≤ H := by
  obtain ⟨g, hg⟩ := exists_conj_le_of_odd_index hH hP
  have hgH : g ∈ H := hX g fun x hx => hg x (hXP hx)
  intro p hp
  have h := H.mul_mem (H.mul_mem hgH (hg p hp)) (H.inv_mem hgH)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using h

theorem exists_conj_le_sylow {S : Sylow 2 G} {H P : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ h ∈ H, ∀ p ∈ P, h⁻¹ * p * h ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SH : Sylow 2 H := S.subtype hSH
  have hP' : IsPGroup 2 (P.subgroupOf H) :=
    hP.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H SH Q
  refine ⟨(c : G), c.property, fun p hp => ?_⟩
  have hpQ : (⟨p, hPH hp⟩ : H) ∈ (Q : Subgroup H) := hQ hp
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hpQ
  change ((MulAut.conj c)⁻¹ • (⟨p, hPH hp⟩ : H) : H) ∈ (S : Subgroup G).subgroupOf H at hpQ
  rw [Subgroup.mem_subgroupOf] at hpQ
  simpa only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    using hpQ

theorem exists_mem_normalizer_not_mem {S N : Subgroup G} (hS : IsPGroup 2 S) (hNS : N ≤ S)
    (hne : N ≠ S) : ∃ s ∈ S, s ∉ N ∧ s ∈ Subgroup.normalizer (N : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := S)
  have hlt : N.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hNS fun x hx => ?_)
    have : (⟨x, hx⟩ : S) ∈ N.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨s, hs, hsN⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨(s : G), s.property, hsN, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hs' := Subgroup.mem_normalizer_iff.mp hs
  constructor
  · intro hh
    have h1 := (hs' ⟨h, hNS hh⟩).mp hh
    exact h1
  · intro hh
    have hhS : h ∈ S := by
      have h2 := S.mul_mem (S.mul_mem (S.inv_mem s.property) (hNS hh)) s.property
      simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h2
    exact (hs' ⟨h, hhS⟩).mpr hh

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
