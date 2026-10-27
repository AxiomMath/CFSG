module

public import CFSG.Adapters.LinearFieldTransport
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem gcd_four_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Nat.gcd 4 (2 ^ f - 1) = 1 := by
  have hodd : (2 ^ f - 1) % 2 = 1 := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have h2 : Nat.Coprime 2 (2 ^ f - 1) := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
  simpa using Nat.Coprime.pow_left 2 h2

theorem card_hopfMultiplier_psl_four {Y : Type} [Group Y] {f : ℕ} (hf : 2 ≤ f)
    (hm : CFSG.Blueprint.LieModel Y .PSL 4 2 f) :
    Nat.card (CFSG.Open.griessHopfMultiplier Y) = 1 := by
  have hcl : StatedClassicalModel Y .PSL 4 2 f := by
    rcases hm with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by decide)
  obtain ⟨⟨hp, hf0, -, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 f (by omega)]
  have hcardF : Fintype.card F = Fintype.card (GaloisField 2 f) := by
    rw [hcard, Fintype.card_eq_nat_card, hF]
  let φ : F ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hcardF
  let e' : Y ≃* PSL(4, GaloisField 2 f) :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 4 F).symm).trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 4))
  have hq : 3 ≤ Fintype.card (GaloisField 2 f) := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (k := GaloisField 2 f) (n := 4) (by norm_num) hq (fun h => absurd h.1 (by norm_num))
  rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e').toEquiv,
    Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hcard,
    gcd_four_two_pow_sub_one (by omega)]

theorem center_eq_bot_of_psl_four {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hK2 : IsPGroup 2 (center K)) {f : ℕ} (hf : 2 ≤ f)
    (hm : CFSG.Blueprint.LieModel (K ⧸ center K) .PSL 4 2 f) : center K = ⊥ := by
  have h1 := card_hopfMultiplier_psl_four hf hm
  have hodd : Odd (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ center K))) := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv, h1]
    exact odd_one
  exact CFSG.GH74.Generic.noTwoCover_of_odd_hopfMultiplier hodd K hK hK2 ⟨MulEquiv.refl _⟩

end CFSG.EvenSporadicStandard.HSStd.PumpT
