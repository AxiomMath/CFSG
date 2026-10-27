module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsAct
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsCount

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L S A B Aa : Subgroup G} {z b : G}

theorem ThLocalIn.card_le_of_abelian_le_S (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hT : TransvCent L A B Aa) {Y : Subgroup G} (hYS : Y ≤ S)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) : Nat.card Y ≤ 2 ^ 8 := by
  have hYL : Y ≤ L := hYS.trans W.S_le
  have hYn : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ ∈ A := fun y hy a ha =>
    W.conj_mem_A_of_mem_S (hYS hy) ha
  obtain ⟨ρ, hρB, -⟩ := SylowBounds.exists_action W hYL hYn
  have hmul := SylowBounds.natCard_eq_mul_natCard_inf ρ hρB
  have hρcomm : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hcomm a a.2 a' a'.2))
  have hρp : IsPGroup 2 ρ.range :=
    (W.pgroup.to_le hYS).of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have h16 : Nat.card ρ.range ≤ 16 := SylowBounds.card_le_sixteen hρp hρcomm
  by_cases hYB : Y ≤ B
  · have hYB' : Y ⊓ B = Y := inf_of_le_left hYB
    by_cases hYAa : Y ≤ Aa
    · calc Nat.card Y ≤ Nat.card Aa := Subgroup.card_le_of_le hYAa
        _ = 2 ^ 8 := W2.Aa_card
    · obtain ⟨y, hyY, hyAa⟩ := IsConcreteLE.not_le_iff_exists.1 hYAa
      have hK : Y ⊓ Aa ≤ A := W2.inf_Aa_le_A W hcomm hyY (hYB hyY) hyAa
      have h1 : Nat.card ↥(Y ⊓ Aa) ≤ 16 := (Subgroup.card_le_of_le hK).trans W.A_card.le
      have h2 := W2.card_inf_B_le W Y
      rw [hYB'] at h2
      omega
  · obtain ⟨g, hgY, hgB⟩ := IsConcreteLE.not_le_iff_exists.1 hYB
    have hgL : g ∈ L := hYL hgY
    have hg16 := W2.card_Aa_inf_centralizer_le_sixteen W hT hgL (hYn g hgY) hgB
    have hKg : Y ⊓ Aa ≤ Aa ⊓ centralizer ({g} : Set G) :=
      SylowBounds.inf_le_inf_centralizer hcomm hgY
    have hYb16 : Nat.card ↥(Y ⊓ B) ≤ 16 := by
      by_cases hYBAa : Y ⊓ B ≤ Aa
      · have hle : Y ⊓ B ≤ Y ⊓ Aa := le_inf inf_le_left hYBAa
        exact (Subgroup.card_le_of_le hle).trans ((Subgroup.card_le_of_le hKg).trans hg16)
      · obtain ⟨y, hyYB, hyAa⟩ := IsConcreteLE.not_le_iff_exists.1 hYBAa
        have hK : Y ⊓ Aa ≤ A := W2.inf_Aa_le_A W hcomm hyYB.1 hyYB.2 hyAa
        have hAK : ¬ A ≤ Y ⊓ Aa := fun hAK => hgB <|
          (W.mem_B_iff g hgL).2 fun a ha => hcomm g hgY a (hAK ha).1
        have h8 := W.card_le_eight_of_not_le hK hAK
        have h2 := W2.card_inf_B_le W Y
        omega
    rw [hmul]
    calc Nat.card ρ.range * Nat.card ↥(Y ⊓ B) ≤ 16 * 16 := Nat.mul_le_mul h16 hYb16
      _ = 2 ^ 8 := by norm_num

theorem ThLocalIn.card_le_of_elementary_le_S (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) {Y : Subgroup G} (hYS : Y ≤ S)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hsq : ∀ y ∈ Y, y ^ 2 = 1) :
    Nat.card Y ≤ 2 ^ 7 := by
  have hYL : Y ≤ L := hYS.trans W.S_le
  have hYn : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ ∈ A := fun y hy a ha =>
    W.conj_mem_A_of_mem_S (hYS hy) ha
  obtain ⟨ρ, hρB, hρfix⟩ := SylowBounds.exists_action W hYL hYn
  have hmul := SylowBounds.natCard_eq_mul_natCard_inf ρ hρB
  have hρcomm : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hcomm a a.2 a' a'.2))
  have hρp : IsPGroup 2 ρ.range :=
    (W.pgroup.to_le hYS).of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hK : Y ⊓ Aa ≤ A := W2.inf_Aa_le_A_of_sq W hsq
  have hKcard : Nat.card ↥(Y ⊓ Aa) ≤ 16 := (Subgroup.card_le_of_le hK).trans W.A_card.le
  have h2 := W2.card_inf_B_le W Y
  by_cases hYB : Y ≤ B
  · have hYB' : Y ⊓ B = Y := inf_of_le_left hYB
    rw [hYB'] at h2
    omega
  · obtain ⟨g0, hg0Y, hg0B⟩ := IsConcreteLE.not_le_iff_exists.1 hYB
    have hcent : ∀ g ∈ Y, Y ⊓ Aa ≤ A ⊓ centralizer ({g} : Set G) := fun g hg x hx =>
      ⟨hK hx, mem_centralizer_singleton_iff.2 (hcomm x hx.1 g hg)⟩
    by_cases hex : ∃ g ∈ Y, g ∉ B ∧ Nat.card ↥(A ⊓ centralizer ({g} : Set G)) ≤ 4
    · obtain ⟨g, hgY, hgB, hg4⟩ := hex
      have h4 : Nat.card ↥(Y ⊓ Aa) ≤ 4 := (Subgroup.card_le_of_le (hcent g hgY)).trans hg4
      have h16 : Nat.card ρ.range ≤ 16 := SylowBounds.card_le_sixteen hρp hρcomm
      rw [hmul]
      calc Nat.card ρ.range * Nat.card ↥(Y ⊓ B) ≤ 16 * 8 := Nat.mul_le_mul h16 (by omega)
        _ = 2 ^ 7 := by norm_num
    · push Not at hex
      have h8 : ∀ g ∈ Y, g ∉ B → Nat.card ↥(A ⊓ centralizer ({g} : Set G)) = 8 := by
        intro g hgY hgB
        have h5 := hex g hgY hgB
        have hle := W.card_inf_centralizer_le_eight (hYL hgY) hgB
        have hdvd : Nat.card ↥(A ⊓ centralizer ({g} : Set G)) ∣ 16 := by
          rw [← W.A_card]
          exact Subgroup.card_dvd_of_le inf_le_left
        generalize Nat.card ↥(A ⊓ centralizer ({g} : Set G)) = d at hdvd h5 hle
        interval_cases d <;> omega
      have h8ρ : Nat.card ρ.range ≤ 8 := by
        refine SylowBounds.card_le_eight_of_transvections hρcomm ?_ ?_
        · rintro _ ⟨a, rfl⟩
          rw [← map_mul]
          have : a * a = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hsq a a.2)
          rw [this, map_one]
        · rintro _ ⟨a, rfl⟩ hne
          have hgB : (a : G) ∉ B := fun hb => hne ((hρB a).2 hb)
          have := hρfix a
          rw [h8 a a.2 hgB] at this
          exact this.ge
      have h8g := (Subgroup.card_le_of_le (hcent g0 hg0Y)).trans (h8 g0 hg0Y hg0B).le
      rw [hmul]
      calc Nat.card ρ.range * Nat.card ↥(Y ⊓ B) ≤ 8 * 16 := Nat.mul_le_mul h8ρ (by omega)
        _ = 2 ^ 7 := by norm_num

end CFSG.EvenSporadicStandard.ThStd
