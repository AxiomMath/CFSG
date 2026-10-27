module

public import CFSG.LocalAnalysis.GLTheoremA.S4.L49a
public import CFSG.LocalAnalysis.GLTheoremA.S4.L49b
public import CFSG.LocalAnalysis.GLTheoremA.S4.L49c
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma47
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isGStar_of_pumpRel {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4) (hLB : LBalanceAt G p)
    (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {t t' : Triple G} (hrel : PumpRel p t t') (hG : IsGStar p t.1 t.2.2) :
    IsGStar p t'.1 t'.2.2 := by
  classical
  have hrel' := hrel
  obtain ⟨⟨hB, hx, hL⟩, ⟨hB', hx', hL'c⟩, hxB', hdec, hx'B', hx'L, -⟩ := hrel'
  obtain ⟨E, hEB, hEe, hEc, hne⟩ := hG
  set B := t.1
  set x := t.2.1
  set L := t.2.2
  set B' := t'.1
  set x' := t'.2.1
  set C := Subgroup.centralizer ({x} : Set G)
  set A := B ⊓ B'
  have hBC : B ≤ C := isElemAbelian_le_centralizer hB.1 hx.1
  have hB'C : B' ≤ C := isElemAbelian_le_centralizer hB'.1 hxB'
  have hAC : A ≤ C := inf_le_left.trans hBC
  have hCne : C ≠ ⊤ := centralizer_ne_top_of_ne_one hsimple hnonab hx.2.1
  have ha := glaPLayer_closureIn_inf_centralizer_ne_bot hp h183 hLB hKP hCne hL hB.1 hBC
    (inf_le_left : A ≤ B) hEB hne
  set Z := B' ⊓ centModSubgroup p L
  set Es := (E ⊓ A) ⊔ Z
  have hZB' : Z ≤ B' := inf_le_left
  have hEsB' : Es ≤ B' := sup_le (inf_le_right.trans inf_le_right) hZB'
  have hx'Es : x' ∈ Es := Subgroup.mem_sup_right ⟨hx'B', centMod_iff.1 hx'L⟩
  have hb := glaPLayer_inf_centralizer_sup_ne_bot (F := E ⊓ A) hp hL hAC (hZB'.trans hB'C)
    ((isPGroup_of_isElemAbelian hB'.1).to_le hZB')
    (fun a ha c hc => isElemAbelian_commute hB'.1 ha.2 (hZB' hc))
    (fun f hf c hc => isElemAbelian_commute hB'.1 hf.2.2 (hZB' hc)) inf_le_right ha
  have hd := glaPLayer_inf_centralizer_ne_bot_of_pumpRel hp h183 hLB hKP hsimple hnonab hrel
    hEsB' hx'Es hb
  have hcard : Nat.card E ≤ Nat.card Es :=
    card_le_card_inf_sup hB.1 hB'.1 (hB.2.1.trans hB'.2.1.symm) hdec hEB
  obtain ⟨F, hFEs, hFc⟩ := exists_le_card_eq_pow hp
    ((isPGroup_of_isElemAbelian hB'.1).to_le hEsB') (hEc ▸ hcard)
  refine ⟨F, hFEs.trans hEsB', isElemAbelian_mono hB'.1 (hFEs.trans hEsB'), hFc, ?_⟩
  set K' := closureIn t'.2.2 B'
  have hEsN : Es ≤ Subgroup.normalizer ((K' ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :
      Set G) := by
    intro e he
    have heF : e ∈ Subgroup.centralizer (F : Set G) := Subgroup.mem_centralizer_iff.2 fun f hf =>
      isElemAbelian_commute hB'.1 (hFEs.trans hEsB' hf) (hEsB' he)
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_closureIn t'.2.2 B' (hEsB' he)),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer heF)]
  have hK : CFSG.Open.IsKGroup ↥((K' ⊓ Subgroup.centralizer (F : Set G)) ⊔ Es) := by
    refine isKGroup_of_isKProper hKP (ne_top_of_le_ne_top
      (centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1) (sup_le ?_ ?_))
    · exact inf_le_left.trans (closureIn_le_of_le hL'c.1 fun b hb =>
        Subgroup.le_normalizer (isElemAbelian_le_centralizer hB'.1 hx'B' hb))
    · exact hEsB'.trans (isElemAbelian_le_centralizer hB'.1 hx'B')
  have h := glaPLayer_inf_centralizer_le hp hLB hK
    ((isPGroup_of_isElemAbelian hB'.1).to_le hEsB') hEsN
  rw [inf_assoc, inf_eq_right.2 (Subgroup.centralizer_le hFEs)] at h
  exact fun hbot => hd (eq_bot_iff.2 (hbot ▸ h))

theorem lemma49_legacySimple {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4)
    (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h1412 : I1412UsedAt G p)
    (h1122 : I1122IsoAt G p) (hLB : LBalanceAt G p) :
    ∀ t t' : Triple G, PumpRel p t t' →
      kLevel p (PSimple p t.2.2) ≤ kLevel p (PSimple p t'.2.2) ∧
        (IsGStar p t.1 t.2.2 → IsGStar p t'.1 t'.2.2) := fun _ _ hrel =>
  ⟨kLevel_le_of_pumpRel hp h183 hKP hsimple hnonab h1412 h1122 hrel,
    isGStar_of_pumpRel hp h183 hLB hKP hsimple hnonab hrel⟩

end CFSG.LocalAnalysis.GLTheoremA
