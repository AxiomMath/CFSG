module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Delta
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem evasion_three (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hL62 : GL83SmallRankLemma62At3 G) {P M x z T f} (h : Lemma630Hyp G 3 P M x z T f) :
    ∀ E, SmallRankSBSylow 3 f x z T E → E ⊓ M = ⊥ := by
  intro E hE
  obtain ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩ := h
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact f.Prime := ⟨hfp⟩
  have hf3 : f ≠ 3 := sr629_ne_prime hp hfp x hfD
  obtain ⟨-, -, -, hFe, hF4, -⟩ := h29
  have hFM : smallRankF 3 f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← h28.2.2.2]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hFne : smallRankF 3 f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF 3 f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFE : smallRankF 3 f x ≤ E :=
    k631_le_of_sylow_centralizer hfp (sr629_F_isPGroup hfp x) hFe.1 hE.1 hE.2.1 hE.2.2.1
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hE.2.2.2
  have hBM : zpowers x ⊔ zpowers z ≤ M := hf.B_le_M hS
  have hBX : zpowers x ⊔ zpowers z ≤ normalizer ((E ⊓ M : Subgroup G) : Set G) :=
    (le_inf hBE (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hR : Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2) := h28.2.1 rfl
  have hα : HasPrimeConstraint (G := M) 3 :=
    (hL62 hS hU0 P M hf.situation x z hf.point hf.central).resolve_right
      (lemma628_ii_three hS hU0 hf hR)
  by_contra hne
  have hXp : IsPGroup f ↥(E ⊓ M) := hE.2.1.to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(E ⊓ M)) 6 := by
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    have h2 : Nat.Coprime f 2 := (Nat.coprime_primes hfp Nat.prime_two).mpr hf2
    have h3 : Nat.Coprime f 3 := (Nat.coprime_primes hfp Nat.prime_three).mpr hf3
    exact (show (6 : ℕ) = 2 * 3 by norm_num) ▸ Nat.Coprime.mul_right h2 h3
  have hN : normalizer ((E ⊓ M : Subgroup G) : Set G) ≤ M :=
    prop65Alpha_of_kfacts hS hU0 hK1 hK2 P M hf.situation hα x z hf.point hf.central
      (E ⊓ M) inf_le_right hne hcop hBX
  have hEM : E ≤ M := by
    by_contra hEM
    have hlt : E ⊓ M < E :=
      lt_of_le_of_ne inf_le_left fun heq => hEM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyE, hyN, hyX⟩ := sr628_exists_mem_normalizer_not_mem hE.2.1 hlt
    exact hyX ⟨hyE, hN hyN⟩
  refine hFne (eq_bot_iff.mpr ?_)
  calc smallRankF 3 f x ≤ smallRankF 3 f x ⊓ M := le_inf le_rfl (hFE.trans hEM)
    _ = ⊥ := hFM
    _ ≤ ⊥ := le_rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
