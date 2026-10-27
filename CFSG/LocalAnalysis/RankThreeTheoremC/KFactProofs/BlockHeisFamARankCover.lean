module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCenter
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

noncomputable def heisARTopEquiv {L : Type} [Group L] {n : ℕ} {K : Type} [Field K]
    (eX : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL n K)) :
    ↥(⊤ : Subgroup L) ⧸ Subgroup.center ↥(⊤ : Subgroup L) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K :=
  (QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)).trans
    (eX.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        n K)))

theorem heisAR_card_center_top (L : Type) [Group L] :
    Nat.card (Subgroup.center ↥(⊤ : Subgroup L)) = Nat.card (Subgroup.center L) :=
  Nat.card_congr (Subgroup.centerCongr Subgroup.topEquiv).toEquiv

theorem heisAR_charP_two {K : Type} [Field K] [Fintype K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem heisAR_card_center_dvd (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L]
    [Finite L] (hperf : Group.IsPerfect L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (hs : IsSimpleGroup (L ⧸ Subgroup.center L)) {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (eX : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL n K)) :
    Nat.card (Subgroup.center L) ∣ Nat.gcd n (2 ^ f - 1) := by
  have hq : CFSG.Open.IsQuasisimple L := ⟨hperf.commutator_eq_top, hs⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI := heisAR_charP_two hK
  have h := oddCenterLinear_of_griess hGA L ⊤ (heis_isComponentOf_top hq)
    (by rw [heisAR_card_center_top]; exact hodd) n K ⟨heisARTopEquiv eX⟩
  rwa [heisAR_card_center_top, ← Nat.card_eq_fintype_card, hK] at h

theorem heisAR_exists_cover
    (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (hs : IsSimpleGroup (L ⧸ Subgroup.center L)) {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (eX : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL n K)) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* L,
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hq : CFSG.Open.IsQuasisimple L := ⟨hperf.commutator_eq_top, hs⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI := heisAR_charP_two hK
  obtain ⟨ρ, -, hker, -⟩ := kFactCoverLinear_of_griess hGA L ⊤ (heis_isComponentOf_top hq)
    (by rw [heisAR_card_center_top]; exact hodd) n K hn (heisARTopEquiv eX)
  refine ⟨(Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom.comp ρ, fun g hg => hker ?_⟩
  rw [MonoidHom.mem_ker] at hg ⊢
  exact (MulEquiv.map_eq_one_iff Subgroup.topEquiv).1 hg

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
