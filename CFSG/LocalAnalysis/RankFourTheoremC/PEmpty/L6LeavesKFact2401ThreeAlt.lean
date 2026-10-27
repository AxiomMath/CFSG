module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeBridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Alt2401

open Equiv Equiv.Perm CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Bridge2401

theorem center_eq_bot_of_alt {L : Type} [Group L] {n : ℕ} (hn : 5 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) : Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hcen : e g ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨h, rfl⟩ := e.surjective k
    have hc := Subgroup.mem_center_iff.mp hg h
    rw [← map_mul, ← map_mul, hc]
  have h4 : 4 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  rw [alternatingGroup.center_eq_bot h4, Subgroup.mem_bot] at hcen
  exact Subgroup.mem_bot.mpr (e.injective (by rw [map_one]; exact hcen))

theorem le_of_alt {A : Type} [Group A] [Finite A] {L E J : Subgroup A} {n : ℕ} (hn : 7 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) {Q : Sylow 3 L}
    (hQ : (Q : Subgroup L).map L.subtype = E)
    (hJ : ∀ S₀ : Subgroup A, S₀ ≤ E → S₀ ≠ ⊥ → Subgroup.normalizer (S₀ : Set A) ⊓ L ≤ J) :
    L ≤ J := by
  have hcen := center_eq_bot_of_alt (by omega : 5 ≤ n) e
  have hC : Subgroup.centralizer ((⊤ : Subgroup L) : Set L) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  have hφ : ↥(⊤ : Subgroup L) ≃* alternatingGroup (Fin n) := Subgroup.topEquiv.trans e
  have htop : gammaCore 3 1 ⊤ (Q : Subgroup L) = ⊤ :=
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.gammaCore_eq_top_of_alt hn hφ hC Q
  have hle : gammaCore 3 1 ⊤ (Q : Subgroup L) ≤ J.subgroupOf L := by
    unfold gammaCore
    refine (Subgroup.closure_le (K := J.subgroupOf L)).2 ?_
    rintro x ⟨-, R, hRQ, hR, hxR⟩
    exact normalizer_le_subgroupOf hQ hJ hRQ hR hxR
  rw [htop] at hle
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top ⟨x, hx⟩))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Alt2401

end
