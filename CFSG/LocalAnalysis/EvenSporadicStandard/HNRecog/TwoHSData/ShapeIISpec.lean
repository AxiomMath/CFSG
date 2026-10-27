module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIICheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleySpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeThree
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeFiveA

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem card_target_S5 : Nat.card (Multiplicative (ZMod 2) × QuaternionGroup 2) = 16 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_target_B5 :
    Nat.card (Multiplicative (ZMod 5) × Multiplicative (ZMod 2) × DihedralGroup 5) = 100 := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := DihedralGroup 5),
    DihedralGroup.card, Nat.card_congr (Multiplicative.toAdd (α := ZMod 5)),
    Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod, Nat.card_zmod]

theorem isShapeCentralizerThree_of_shape3OK (h : shape3OK = true)
    (hX : Nat.card ↥(P1408 ⊓ centralizer ({elemW fix3.rep} : Set (Equiv.Perm (Fin 1408)))) =
      1440) :
    IsShapeCentralizerThree
      ↥(P1408 ⊓ centralizer ({elemW fix3.rep} : Set (Equiv.Perm (Fin 1408)))) := by
  simp only [shape3OK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwr, hord⟩, hY⟩, hN⟩, hV⟩, hA⟩, hcY⟩, hnY⟩, hNY⟩, hVN⟩, hAN⟩, hVNc⟩,
    htriv⟩, hsq⟩, hblk⟩, himg⟩ := h
  have hg : gensOK = true := gensOK_of_blkDataOK hblk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrr : Rep 1408 (tabW fix3.rep) (elemW fix3.rep) := rep_elemW_of_gensOK hg hwr
  have hr3 : orderOf (elemW fix3.rep) = 3 := orderOf_eq_of_primeOrderOK hrr hord
  obtain ⟨hYc, hYe⟩ := enumW_spec hY
  obtain ⟨hNc, hNe⟩ := enumW_spec hN
  obtain ⟨hVc, hVe⟩ := enumW_spec hV
  obtain ⟨hAc, hAe⟩ := enumW_spec hA
  obtain ⟨-, hYw⟩ := enumW_gens_words hY
  obtain ⟨-, hNw⟩ := enumW_gens_words hN
  obtain ⟨-, hVw⟩ := enumW_gens_words hV
  obtain ⟨-, hAw⟩ := enumW_gens_words hA
  have hLX := zpowers_le_inf_centralizer (elemW_mem fix3.rep)
  have hYX := closure_words_le_inf_centralizer hg hYw hrr hcY
  have hNY' := closure_words_le_of_wordsInOK hg hNw hYe hNY
  have hVN' := closure_words_le_of_wordsInOK hg hVw hNe hVN
  have hAN' := closure_words_le_of_wordsInOK hg hAw hNe hAN
  have hLc : Nat.card ↥(zpowers (elemW fix3.rep)) = 3 := by rw [Nat.card_zpowers, hr3]
  have hVsq : ∀ v ∈ closure (elemW '' {w | w ∈ v3Words}), v * v = 1 := (sqOneOK_iff hVe).1 hsq
  have hnotY : elemW fix3.rep ∉ closure (elemW '' {w | w ∈ y3Words}) := fun hm => by
    have := (hYe.memT_iff hrr).2 hm
    rw [this] at hnY
    exact absurd hnY (by decide)
  obtain ⟨φ, -, hrange, -⟩ := blkData_spec hblk
  have hφ60 : Nat.card ↥φ.range = 60 := by
    rw [hrange]
    exact blkImage_spec hblk (by show 5 < 2 ^ 32; norm_num) himg
  refine TwoHSData.isShapeCentralizerThree_of_data _ (zpowers (elemW fix3.rep)) _ _ _ _ hLX hYX
    hNY' hVN' hAN' (by rw [hX, hLc, hYc]) (by rw [hYc, hNc]) (by rw [hNc, hVc, hAc])
    (fun l hl x hx => mul_comm_of_mem_zpowers hx l hl)
    (eq_one_of_mem_zpowers_of_not_mem hr3 hnotY)
    (fun v hv n hn => (commPairsOK_spec hg hVw hNw hVNc v hv n hn).symm)
    ((trivInterOK_iff hVe hAe).1 htriv)
    ⟨mulEquivOfPrimeCardEq hLc (by simp [Nat.card_zmod])⟩
    (TwoHSData.nonempty_mulEquiv_elem2 (G := ↥(closure (elemW '' {w | w ∈ v3Words}))) 2
      (fun v => Subtype.ext (hVsq v.1 v.2)) (by rw [hVc]; norm_num))
    (TwoHSData.nonempty_mulEquiv_alternating_five φ hAc hφ60)

theorem isShapeCentralizerFiveA_of_shape5AOK (h : shape5AOK = true)
    (hX : Nat.card ↥(P1408 ⊓ centralizer ({elemW fix5A.rep} : Set (Equiv.Perm (Fin 1408)))) =
      2000)
    (hcl : closure (elemW '' {w | w ∈ fix5A.cent}) =
      P1408 ⊓ centralizer ({elemW fix5A.rep} : Set (Equiv.Perm (Fin 1408)))) :
    IsShapeCentralizerFiveA
      ↥(P1408 ⊓ centralizer ({elemW fix5A.rep} : Set (Equiv.Perm (Fin 1408)))) := by
  simp only [shape5AOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwr, hcw⟩, hN⟩, hcN⟩, hcS⟩, hpow⟩, hnorm⟩, hncomm⟩, hcay⟩ := h
  have hS := enumW_of_cayleyOK hcay
  obtain ⟨hg, hNw⟩ := enumW_gens_words hN
  obtain ⟨-, hSw⟩ := enumW_gens_words hS
  have hrr : Rep 1408 (tabW fix5A.rep) (elemW fix5A.rep) := rep_elemW_of_gensOK hg hwr
  obtain ⟨hNc, hNe⟩ := enumW_spec hN
  obtain ⟨hSc, -⟩ := enumW_spec hS
  have hu : n5Words.getD 0 [] ∈ n5Words := by decide
  have hv : n5Words.getD 2 [] ∈ n5Words := by decide
  have hru := rep_elemW_of_gensOK hg (List.all_eq_true.1 hNw _ hu)
  have hrv := rep_elemW_of_gensOK hg (List.all_eq_true.1 hNw _ hv)
  exact TwoHSData.isShapeCentralizerFiveA_of_data _ _ _
    (closure_words_le_inf_centralizer hg hNw hrr hcN)
    (closure_words_le_inf_centralizer hg hSw hrr hcS)
    (fun x hx n hn => normGensOK_spec hg hcw hNw hNe hnorm x (by rw [hcl]; exact hx) n hn)
    (by rw [hX, hNc, hSc]) hNc hSc ((powOneOK_iff hNe 5).1 hpow)
    (subset_closure ⟨_, hu, rfl⟩) (subset_closure ⟨_, hv, rfl⟩)
    (fun hh => by
      rw [(commTT_iff hru hrv).2 hh] at hncomm
      exact absurd hncomm (by decide))
    (nonempty_mulEquiv_of_cayleyOK hcay card_target_S5)

theorem isShapeCentralizerFiveB_of_shape5BOK (h : shape5BOK = true)
    (hX : Nat.card ↥(P1408 ⊓ centralizer ({elemW fix5B.rep} : Set (Equiv.Perm (Fin 1408)))) =
      100) :
    IsShapeCentralizerFiveB
      ↥(P1408 ⊓ centralizer ({elemW fix5B.rep} : Set (Equiv.Perm (Fin 1408)))) := by
  simp only [shape5BOK, Bool.and_eq_true] at h
  obtain ⟨⟨hwr, hcB⟩, hcay⟩ := h
  have henum := enumW_of_cayleyOK hcay
  obtain ⟨hg, hbw⟩ := enumW_gens_words henum
  obtain ⟨hBc, -⟩ := enumW_spec henum
  have hrr : Rep 1408 (tabW fix5B.rep) (elemW fix5B.rep) := rep_elemW_of_gensOK hg hwr
  have hBeq : closure (elemW '' {w | w ∈ b5Words}) =
      P1408 ⊓ centralizer ({elemW fix5B.rep} : Set (Equiv.Perm (Fin 1408))) :=
    Subgroup.eq_of_le_of_card_ge (closure_words_le_inf_centralizer hg hbw hrr hcB)
      (by rw [hX, hBc])
  obtain ⟨e⟩ := nonempty_mulEquiv_of_cayleyOK hcay card_target_B5
  exact ⟨(MulEquiv.subgroupCongr hBeq.symm).trans e⟩

end CFSG.EvenSporadicStandard.HNRecog
