module

public import CFSG.CharacterTheory.Wreathed.ProjectiveTwoParameterUniqueness
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup

structure CBarProps (H : Type) [Group H] : Prop where
  card : Nat.card H = 12 ∨ Nat.card H = 60
  three : ∀ K : Subgroup H, K.Normal → 3 ∣ Nat.card K → K = ⊤
  five : ∀ K : Subgroup H, K.Normal → 5 ∣ Nat.card K → K = ⊤
  four : Nat.card H = 12 → ∃ V : Subgroup H, V.Normal ∧ Nat.card V = 4

abbrev A4 : Type := alternatingGroup (Fin 4)

theorem a4_conj : ∀ c : A4, c ≠ 1 → c ^ 3 = 1 → ∀ v : A4, v ≠ 1 → v ^ 2 = 1 →
    ∃ g h : A4, v = g * c * g⁻¹ * (h * c * h⁻¹)⁻¹ := by
  decide +kernel

theorem a4_card : Nat.card A4 = 12 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem a4_three (K : Subgroup A4) (hK : K.Normal) (h3 : 3 ∣ Nat.card K) : K = ⊤ := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3
  have hc1 : (x : A4) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hc3 : (x : A4) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hcK : (x : A4) ∈ K := x.2
  have h4 : Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 :=
    alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  have hexp : Monoid.exponent (alternatingGroup.kleinFour (Fin 4)) = 2 :=
    alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)
  have hV : alternatingGroup.kleinFour (Fin 4) ≤ K := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]; exact K.one_mem
    have hv2 : v ^ 2 = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : alternatingGroup.kleinFour (Fin 4))
      rw [hexp] at this
      exact congrArg Subtype.val this
    obtain ⟨g, h, hgh⟩ := a4_conj x hc1 hc3 v hv1 hv2
    rw [hgh]
    exact K.mul_mem (hK.conj_mem _ hcK g) (K.inv_mem (hK.conj_mem _ hcK h))
  have hd4 : 4 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le hV
    rwa [h4] at this
  have hd12 : 12 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) hd4 h3
  have hdK : Nat.card K ∣ 12 := a4_card ▸ Subgroup.card_subgroup_dvd_card K
  have hK12 : Nat.card K = 12 := Nat.dvd_antisymm hdK hd12
  exact (Subgroup.card_eq_iff_eq_top K).mp (by rw [hK12, a4_card])

theorem cbarProps_a4 {H : Type} [Group H] (e : H ≃* A4) : CBarProps H := by
  have hcard : Nat.card H = 12 := by rw [Nat.card_congr e.toEquiv]; exact a4_card
  refine ⟨Or.inl hcard, ?_, ?_, ?_⟩
  · intro K hK h3
    have hKn : (K.map e.toMonoidHom).Normal := hK.map e.toMonoidHom e.surjective
    have hc : Nat.card (K.map e.toMonoidHom) = Nat.card K :=
      Subgroup.card_map_of_injective e.injective
    have := a4_three (K.map e.toMonoidHom) hKn (hc ▸ h3)
    have h2 : K = (K.map e.toMonoidHom).comap e.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective e.injective K).symm
    rw [h2, this]; exact Subgroup.comap_top _
  · intro K _ h5
    have hdvd : Nat.card K ∣ 12 := hcard ▸ Subgroup.card_subgroup_dvd_card K
    have := h5.trans hdvd
    norm_num at this
  · intro _
    refine ⟨(alternatingGroup.kleinFour (Fin 4)).map e.symm.toMonoidHom, ?_, ?_⟩
    · exact (alternatingGroup.normal_kleinFour (by simp)).map e.symm.toMonoidHom e.symm.surjective
    · rw [Subgroup.card_map_of_injective e.symm.injective]
      exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)

theorem cbarProps_of_simple60 {H : Type} [Group H] (hs : IsSimpleGroup H) (hc : Nat.card H = 60) :
    CBarProps H := by
  have hne : ∀ K : Subgroup H, K.Normal → 3 ∣ Nat.card K ∨ 5 ∣ Nat.card K → K = ⊤ := by
    intro K hK h
    have : K.Normal := hK
    rcases hs.eq_bot_or_eq_top_of_normal K with hb | ht
    · rw [hb, Subgroup.card_bot] at h
      rcases h with h | h <;> norm_num at h
    · exact ht
  refine ⟨Or.inr hc, fun K hK h => hne K hK (Or.inl h), fun K hK h => hne K hK (Or.inr h), fun h => ?_⟩
  rw [hc] at h
  norm_num at h

theorem psl_data {H : Type} [Group H] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (h : CFSG.Blueprint.LieModel H .PSL 2 p 1) :
    IsSimpleGroup H ∧ Nat.card H = p * (p ^ 2 - 1) / 2 := by
  have hm := CFSG.GH74.Generic.stated_of_lieModel_PSL h
  refine ⟨?_, ?_⟩
  · obtain ⟨_, F, _, _, hcard, ⟨e⟩⟩ := hm
    have h4 : 4 ≤ Nat.card F := by rw [hcard]; simpa using hp5.trans' (by norm_num)
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).isSimpleGroup
  · have := CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_stated_psl_two_of_odd H p 1 hm
      (hp.eq_two_or_odd'.resolve_left hp2)
    simpa using this

theorem cbarProps_psl5 {H : Type} [Group H] (h : CFSG.Blueprint.LieModel H .PSL 2 5 1) : CBarProps H := by
  obtain ⟨hs, hc⟩ := psl_data (by norm_num) (by norm_num) (by norm_num) h
  exact cbarProps_of_simple60 hs (by rw [hc]; norm_num)

end CFSG.GH74.Uniqueness.SU.SU13
