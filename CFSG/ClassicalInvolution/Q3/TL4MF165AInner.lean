module

public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF165A

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem alphaOf_eq_bot_of_autOddFreeInner {L : Type} [Group L] (h : AutOddFreeInner L)
    {𝒳 : Subgroup (MulAut L)} (hinn : innSubgroup L ≤ 𝒳) {A : Subgroup ↥𝒳}
    (hAinn : ∀ a ∈ A, ((a : ↥𝒳) : MulAut L) ∈ innSubgroup L) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card ↥A = 4) : alphaOf A = ⊥ := by
  have hne : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hA : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    rw [hA, Subgroup.card_bot] at hcard
    omega
  refine alphaOf_eq_bot_of_oddCore hne fun a ha ha1 => ?_
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hA2 a ha) ha1
  exact h 𝒳 hinn a (hAinn a ha) ha2

theorem autOddFreeInner_of_lieModel_three {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) (h : CFSG.Blueprint.LieModel L t 3 3 1) :
    AutOddFreeInner L := by
  have hFT : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  have hadm : StatedLieAdmissible t 3 3 1 := by
    rcases ht with rfl | rfl
    · exact ⟨Nat.prime_three, le_rfl, by decide⟩
    · exact ⟨Nat.prime_three, le_rfl, by decide⟩
  obtain ⟨ψ, hψ, hker⟩ := Upgrade.lieModelCentralCover t 3 3 1 Nat.prime_three (by norm_num) hFT
    hadm L h
  exact autOddFreeInnerTag_of_not_D4 (t := t) (n := 3) (by rcases ht with rfl | rfl <;> simp)
    (by rcases ht with rfl | rfl <;> simp) Nat.prime_three hFT hadm L ψ hψ hker

theorem autOddFreeInner_of_m11
    {L : Type} [Group L] [Finite L]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic L .M11) : AutOddFreeInner L := by
  obtain ⟨e⟩ := h
  have e' : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* L := e.symm
  exact Q3CH.autOddFreeInner_of_mulEquiv e' (Q3CH.autOddFreeInner_m11 Q3CH.m11OddAutInner3)

theorem mem_of_odd_of_index_le_two {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : H.index ≤ 2) {g : G} (hg : Odd (orderOf g)) : g ∈ H := by
  have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top g
  · have : H.Normal := Subgroup.normal_of_index_eq_two h2
    have hd1 : orderOf (QuotientGroup.mk g : G ⧸ H) ∣ orderOf g :=
      orderOf_map_dvd (QuotientGroup.mk' H) g
    have hd2 : orderOf (QuotientGroup.mk g : G ⧸ H) ∣ 2 := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk g : G ⧸ H)
      rwa [← Subgroup.index, h2] at h
    have hone : orderOf (QuotientGroup.mk g : G ⧸ H) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
      · exact h
      · rw [h] at hd1
        exact absurd (even_iff_two_dvd.mpr hd1) (Nat.not_even_iff_odd.mpr hg)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hone
    exact hone

theorem autOddFreeInner_m12 :
    AutOddFreeInner ↥CFSG.Blueprint.NativeSporadic.M12 := by
  have hZ := CFSG.Sporadic.Schreier.m12_center_eq_bot'
  have hinj := conj_injective_of_center_eq_bot hZ
  have : Finite (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) :=
    Finite.of_injective (fun β : MulAut ↥CFSG.Blueprint.NativeSporadic.M12 =>
      (β : ↥CFSG.Blueprint.NativeSporadic.M12 → ↥CFSG.Blueprint.NativeSporadic.M12))
      fun β γ hβγ => MulEquiv.ext (congrFun hβγ)
  have hidx : (innSubgroup ↥CFSG.Blueprint.NativeSporadic.M12).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (innSubgroup ↥CFSG.Blueprint.NativeSporadic.M12)
    have h2 : Nat.card (innSubgroup ↥CFSG.Blueprint.NativeSporadic.M12) =
        Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have h3 := CFSG.Sporadic.Schreier.m12_mulAut_card
    have hpos : 0 < Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 := Nat.card_pos
    rw [h2] at h1
    nlinarith
  refine autOddFreeInner_of_centralizing_inner hZ (fun x hx => ?_)
    fun _ _ α hα _ => mem_of_odd_of_index_le_two hidx hα
  have h := CFSG.Sporadic.Schreier.m12_inner_oddCore x hx
  show (Open.componentClassificationOddCore
      ↥(Subgroup.centralizer ({x} : Set ↥CFSG.Blueprint.NativeSporadic.M12))).map _ = ⊥
  rw [show Open.componentClassificationOddCore
      ↥(Subgroup.centralizer ({x} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) = ⊥ from h,
    Subgroup.map_bot]

theorem autOddFreeInner_of_m12
    {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12) :
    AutOddFreeInner L := by
  obtain ⟨e⟩ := h
  have e' : ↥CFSG.Blueprint.NativeSporadic.M12 ≃* L ⧸ Subgroup.center L := e.symm
  exact autOddFreeInner_of_centralQuotient
    (Q3CH.autOddFreeInner_of_mulEquiv e' autOddFreeInner_m12)

end CFSG.ClassicalInvolution.Q3.TL4.MF165A
