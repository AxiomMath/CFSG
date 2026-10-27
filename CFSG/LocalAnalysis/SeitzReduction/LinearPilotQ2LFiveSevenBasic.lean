module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKOdd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListBasic
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.GH74.Filter.Small.RankThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def SevenL3Group (X : Type) [Group X] : Prop :=
  (∃ D : Subgroup X, IsComponent D ∧ LieModel (D ⧸ center D) .PSL 3 2 1) ∧
    ∀ Q : Subgroup X, IsPGroup 2 Q → Nat.card Q ≤ 32

theorem SevenL3Group.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SevenL3Group X) : SevenL3Group Y := by
  obtain ⟨⟨D, hD, hDm⟩, h2⟩ := h
  refine ⟨⟨D.map e.toMonoidHom, LocalCores.isComponent_map_mulEquiv e hD,
    RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
      (D.equivMapOfInjective e.toMonoidHom e.injective) hDm⟩, fun Q hQ => ?_⟩
  have h1 := h2 (Q.map e.symm.toMonoidHom) (hQ.map _)
  rwa [Subgroup.card_map_of_injective e.symm.injective] at h1

theorem SevenL3Group.not_dvd {X : Type} [Group X] [Finite X] (h : SevenL3Group X) :
    ¬ 64 ∣ Nat.card X := by
  intro h64
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := 6)
    (by norm_num; exact h64)
  have h1 := h.2 Q (IsPGroup.of_card hQ)
  rw [hQ] at h1
  norm_num at h1

theorem SevenL3Group.of_eq {S : Type} [Group S] {γ γ' : MulAut S} (hγ : γ = γ')
    (h : SevenL3Group (fixedSubgroup γ)) : SevenL3Group (fixedSubgroup γ') :=
  h.of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))

theorem SevenL3Group.congr {J J' : Type} [Group J] [Group J'] (e : J ≃* J') {α : MulAut J}
    (h : SevenL3Group (fixedSubgroup α)) : SevenL3Group (fixedSubgroup (MulAut.congr e α)) :=
  h.of_mulEquiv (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e α)

theorem sevenL3Group_of_hyp {S : Type} [Group S] [Finite S] {τ : MulAut S}
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (h2 : F4Pilot.FixedCentralizerTwoFree τ D ∨
      (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) :
    SevenL3Group (fixedSubgroup τ) :=
  ⟨⟨D, hD, hDm⟩, fun _ hQ => card_le_of_isPGroup_fixedSubgroup_lThree hD hDm
    (fixedCentralizerTwoSmall_of_lFive_hyp h2) hQ⟩

namespace SevenList

theorem eq_one_of_seven_pow_eq_seven {g : ℕ} (h : 7 ^ g = 7) : g = 1 := by
  have h' : 7 ^ g = 7 ^ 1 := by rw [h, pow_one]
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 7) h'

theorem seven_pow_ne_three (e : ℕ) : 7 ^ e ≠ 3 := by
  intro h
  rcases e with _ | e
  · norm_num at h
  · have : 7 ≤ 7 ^ (e + 1) := Nat.le_self_pow (by omega) 7
    omega

theorem odd_seven_pow (e : ℕ) : Odd (7 ^ e) := Odd.pow (by decide)

theorem two_pow_dvd_of_dvd_mul_of_dvd {s i a b o : ℕ} (h : 2 ^ (a + b) ∣ s * i)
    (hi : i ∣ 2 ^ b * o) (ho : Odd o) : 2 ^ a ∣ s := by
  have h1 : 2 ^ (a + b) ∣ s * (2 ^ b * o) := h.trans (Nat.mul_dvd_mul_left s hi)
  have h2 : 2 ^ a * 2 ^ b ∣ (s * o) * 2 ^ b := by
    rw [← pow_add]
    calc 2 ^ (a + b) ∣ s * (2 ^ b * o) := h1
      _ = (s * o) * 2 ^ b := by ring
  have h3 : 2 ^ a ∣ s * o := Nat.dvd_of_mul_dvd_mul_right (by positivity) h2
  exact (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ho)).dvd_of_dvd_mul_right h3

end SevenList

theorem card_le_four_of_twoRank_le_two {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.twoRank G ≤ 2) (E : Subgroup G) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ x : E, x * x = 1 := fun x => Subtype.ext (hE x x.2)
  have hinv : ∀ x : E, x⁻¹ = x := fun x => (eq_inv_of_mul_eq_one_left (hsq x)).symm
  have hcomm : IsMulCommutative E := ⟨⟨fun a b => by
    have h1 : a * b = (a * b)⁻¹ := (eq_inv_of_mul_eq_one_left (hsq (a * b)))
    rw [h1, mul_inv_rev, hinv a, hinv b]⟩⟩
  have hel : CFSG.Open.IsElemAbelian 2 E :=
    ⟨hcomm, fun x hx => by rw [pow_two]; exact hE x hx⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one, pow_two]; exact hsq x⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hle := CFSG.SectionRank.le_pRank (p := 2) Nat.one_lt_two (le_top : E ≤ ⊤) hel hk
  have hk2 : k ≤ 2 := hle.trans h
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem card_le_eight_of_sevenList {S : Type} [Group S] [Finite S]
    (h : LieModel S .PSL 2 7 2 ∨ LieModel S .PSL 3 7 1 ∨ LieModel S .PSU 3 7 1)
    (E : Subgroup S) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 8 := by
  have hp : (7 : ℕ).Prime := by norm_num
  have hp2 : (7 : ℕ) ≠ 2 := by norm_num
  have hr : CFSG.Open.twoRank S ≤ 2 := by
    rcases h with h | h | h
    · exact GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
    · exact GH74.Filter.t_PSL_three_odd S 7 1 hp2
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
    · exact GH74.Filter.t_PSU_three_odd S 7 1 hp2
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
  exact (card_le_four_of_twoRank_le_two hr E hE).trans (by norm_num)

@[expose] def LFiveSevenListFamilyInput (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n f : ℕ, StatedLieAdmissible t n 7 f → LieModel S t n 7 f →
    ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), IsComponent D → LieModel (D ⧸ center D) .PSL 3 2 1 →
      (F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) →
      LieModel S .PSL 2 7 2 ∨ LieModel S .PSL 3 7 1 ∨ LieModel S .PSU 3 7 1

theorem lFiveSevenRankFamilyInput_of_list {t : StatedLieTag} (h : LFiveSevenListFamilyInput t) :
    LFiveSevenRankFamilyInput t :=
  fun S _ _ hS hna n f hadm hL τ hτ D hD hDm h2 E hE =>
    card_le_eight_of_sevenList (h S hS hna n f hadm hL τ hτ D hD hDm h2) E hE

end CFSG.SeitzReduction.LinearPilot
