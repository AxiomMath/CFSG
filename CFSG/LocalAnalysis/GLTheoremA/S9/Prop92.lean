module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95C
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma96
public import CFSG.LocalAnalysis.GLTheoremA.S9.Closing

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Prop92Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l95 : Lemma95Inputs G p
  l96 : Lemma96Inputs G p
  cl : ClosingInputs G

theorem odd_commutator_of_h92 {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G} (hc : S9Ctx G p)
    (hin : Lemma93Inputs G p) (h : H92 p B x L) :
    Odd (Nat.card ↥(⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G)) := by
  have hp : p.Prime := hc.ctx.prime
  have hOle : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p (cx x) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp h.comp.2.1
  by_cases hGB : IsGB p B L
  · have hGstar : IsGStar p B L := by
      obtain ⟨E, hEB, hE, hcard, -, hne⟩ := hGB
      refine ⟨E, hEB, hE, hcard, ?_⟩
      rwa [closureIn_eq_self h.norm]
    have hodd := hc.stage4.2.1 B x L h.bmax h.mem h.ne_one h.comp hGstar
    rw [closureIn_eq_self h.norm] at hodd
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl hOle))
  · have hodd := odd_core_of_not_isGB hc hin h hGB
    have hle : (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.1 (le_normalizer_glaPPrimeCoreOf p L)
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le (hle.trans hOle))

theorem prop92 {p : ℕ} (hc : S9Ctx G p) (hin : Prop92Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : H92 p B x L) : CFSG.Open.IsQuasisimple ↥L := by
  by_contra hnq
  have hp : p.Prime := hc.ctx.prime
  have hne : (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) ≠ ⊥ :=
    fun h0 => hnq (isQuasisimple_of_commutator_eq_bot hp h.comp h0)
  have hodd := odd_commutator_of_h92 hc hin.l95.l93 h
  obtain ⟨q, Q₁, hs⟩ := exists_setup hp h.comp hne hodd
  have hC : Contra92 p B x L q Q₁ := ⟨h, hs, hne, hodd⟩
  have h95 := lemma95 hc hin.l95 hC
  have h96 : ∀ B' : Subgroup G, H92 p B' x L → Concl96 p B' x L Q₁ :=
    fun B' hB' => lemma96 hc hin.l96 ⟨hB', hs, hne, hodd⟩ h95
  exact closing hc hin.cl hC h96

end CFSG.LocalAnalysis.GLTheoremA.S9
