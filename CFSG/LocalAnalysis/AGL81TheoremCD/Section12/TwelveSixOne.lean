module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixReduced
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbedInput
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem forall_isStronglyPEmbedded_of_mem_weakBlockSet {M : Subgroup G} {p : ℕ}
    {Q H L : Subgroup G} (h : TwelveCtx G M p Q H) (hL : L ∈ weakBlockSet M H) :
    ∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M := by
  intro q hq
  haveI : Fact q.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1⟩
  exact isStronglyPEmbedded_of_twelveCtx' h (not_isSolvable_of_mem_weakBlockSet hL) q hq

theorem normalizer_le_of_mem_weakBlockSet {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (h812 : Section15.O812sixGen) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hL3 : ∀ A : Subgroup G, A ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥A ⧸ pCore 2 ↥A))
    (hdvdL : ∀ A : Subgroup G, A ∈ weakBlockSet M H → d ∣ Nat.card A)
    (hcard : 3 ≤ (weakBlockSet M H).ncard)
    {L W : Subgroup G} (hL : L ∈ weakBlockSet M H) (hW : Nat.card W = 3) (hWL : W ≤ L) :
    Subgroup.normalizer (W : Set G) ≤ M := by
  have hdP : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have hWM : W ≤ M := hWL.trans hL.le
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hW
    omega
  have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [hW]; norm_num)
  have hsolv : Group.IsSolvable (MulAut ↥W) := by
    haveI : Group.IsSolvable (Equiv.Perm ↥W) :=
      Equiv.Perm.isSolvable (by rw [hW]; norm_num)
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm (M := ↥W))
      (fun _ _ hab => MulEquiv.toEquiv_injective hab)
  obtain ⟨hrank, hnsC⟩ :=
    centralizer_inputs_of_mem_weakBlockSet hdP hd2 hL3 hdvdL hcard hL hW hWL
  have hrank' : 2 ≤ CFSG.Open.pRank d (M ⊓ Subgroup.centralizer (W : Set G)) := by
    rwa [inf_comm]
  have hns' : ¬ CFSG.HallHigman.IsPSolvable d
      ↥(M ⊓ Subgroup.centralizer (W : Set G)) := by
    rwa [inf_comm]
  have hs := forall_isStronglyPEmbedded_of_mem_weakBlockSet h hL
  by_cases hd3 : d = 3
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le
      (hs 3 (hd3 ▸ hd)) hWne hW3 hWM
  · have h5 : 5 ≤ d := Nat.Prime.five_le_of_ne_two_of_ne_three hdP hd2 hd3
    have hO : Section15.O812sixAt G M :=
      h812 G h.cstar M h.maxLocal h.sigma_nonempty hs
    exact hO d hd h5 W hWM hW3 hWne hsolv hrank' hns'

theorem centralizer_le_of_mem_weakBlockSet {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (h812 : Section15.O812sixGen) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hL3 : ∀ A : Subgroup G, A ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥A ⧸ pCore 2 ↥A))
    (hdvdL : ∀ A : Subgroup G, A ∈ weakBlockSet M H → d ∣ Nat.card A)
    (hcard : 3 ≤ (weakBlockSet M H).ncard)
    {L W : Subgroup G} (hL : L ∈ weakBlockSet M H) (hW : Nat.card W = 3) (hWL : W ≤ L) :
    Subgroup.centralizer (W : Set G) ≤ M :=
  (Subgroup.centralizer_le_normalizer (W : Set G)).trans
    (normalizer_le_of_mem_weakBlockSet h h812 hd hL3 hdvdL hcard hL hW hWL)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
