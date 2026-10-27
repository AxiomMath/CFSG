module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Label
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416RBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup LieSemisimpleCent)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

section Comp


theorem exists_label_component (hLSC : LieSemisimpleCent) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) {labK : GLALabel}
    (hlab : HasLabel S (fun l : GLALabel => l = labK)) (hn : 2 ≤ labK.n) {β : MulAut S}
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {Jb : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) Jb) (hcat : catalogIs (PSimple 3 Jb) I144Cat) :
    ∃ labJ : GLALabel, HasLabel ↥Jb (fun l : GLALabel => l = labJ) ∧
      (canonLabel labJ).n = 1 ∧ ((canonLabel labJ).tag = .twA ∨ (canonLabel labJ).tag = .B) := by
  have hq : CFSG.Open.IsQuasisimple S := Y10F.hasLabel_isQuasisimple hlab
  have hsimple : IsSimpleGroup S :=
    (MulEquiv.isSimpleGroup_congr (CanonInn.quotCenterEquivOfBot hcen)).1 hq.2
  have hna : ∃ a b : S, a * b ≠ b * a :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_exists_noncomm_of_isQuasisimple hq
  have hlam := CanonSubcomp.lambda2_of_hasLabel hlab
  have hc : CFSG.StandardType.markChar labK = 2 :=
    CanonSubcomp.markChar_eq_two_of_two_le hlam hn
  have hLM : CFSG.StandardType.MarkedModel labK (S ⧸ Subgroup.center S) :=
    CanonSubcomp.markedModel_of_hasLabel hlab
  unfold CFSG.StandardType.MarkedModel at hLM
  rw [hc] at hLM
  have hLM' := CFSG.StandardType.lieModel_of_mulEquiv'
    (CanonInn.quotCenterEquivOfBot hcen) hLM
  rcases CanonSubcomp.exists_index_or_small_of_lieModel_two hLM' with
    ⟨d, hd2, ⟨e⟩⟩ | h60 | h1
  · have hpil := hLSC S hsimple hna d ⟨e⟩ 3 Nat.prime_three (by norm_num)
      (by rw [hd2]; norm_num) β hβ3 hβ1
    have hJle := hpil Jb hJ.1
      (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
    have hJc := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
      hJ hJle).1
    have hJq : CFSG.Open.IsQuasisimple ↥Jb := hJc.2.2
    obtain ⟨eA⟩ := chev2_quot_equiv Nat.prime_three hJ hJq
    exact exists_label_of_catalog hJq ((catalogIs_congr eA).2 hcat)
  · exfalso
    have hfix : fixSubgroup β ≠ ⊤ := by
      intro h
      apply hβ1
      ext s
      have hs : s ∈ fixSubgroup β := by rw [h]; exact Subgroup.mem_top s
      exact mem_fixSubgroup.1 hs
    have hlt : Nat.card ↥Jb < 60 := by
      rw [← h60]
      calc Nat.card ↥Jb
          ≤ Nat.card ↥(fixSubgroup β) := Subgroup.card_le_of_le hJ.1
        _ < Nat.card ↥(⊤ : Subgroup S) :=
            Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hfix)
        _ = Nat.card S := Subgroup.card_top
    haveI := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
    have hQs := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
    haveI := hQs.2
    haveI : Nontrivial (PQuot 3 Jb) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 Jb))).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot 3 Jb)).ne hQs.1
  · exfalso
    have h1' : (canonLabel labK).n = 1 :=
      (CanonSubcomp.canonLabel_n_eq_markDeg hlam hc).trans h1
    have hdvd : labK.n ∣ 1 := by
      rw [← h1']
      exact CanonSubcomp.n_dvd_canonLabel_n hlam
    have : labK.n = 1 := Nat.dvd_one.1 hdvd
    omega

end Comp

end CFSG.LocalAnalysis.GLTheoremA.K144
