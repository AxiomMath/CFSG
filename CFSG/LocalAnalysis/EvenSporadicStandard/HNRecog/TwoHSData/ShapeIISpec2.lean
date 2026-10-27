module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIICheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeFiveC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeSeven

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem isShapeCentralizerFiveC_of_shape5COK (h : shape5COK = true) (ha2 : elemA * elemA = 1)
    (ha1 : elemA ≠ 1) (hacen : ∀ g ∈ P1408, elemA * g = g * elemA)
    (hX : Nat.card ↥(P1408 ⊓ centralizer ({elemW fix5C.rep} : Set (Equiv.Perm (Fin 1408)))) =
      1200) :
    IsShapeCentralizerFiveC
      ↥(P1408 ⊓ centralizer ({elemW fix5C.rep} : Set (Equiv.Perm (Fin 1408)))) := by
  simp only [shape5COK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwr, hord⟩, hwu⟩, hwv⟩, hY⟩, hcY⟩, hnY⟩, haY⟩, huY⟩, hvY⟩, hblk⟩, himg⟩,
    haTriv⟩, hcomm⟩ := h
  have hg : gensOK = true := gensOK_of_blkDataOK hblk
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrr : Rep 1408 (tabW fix5C.rep) (elemW fix5C.rep) := rep_elemW_of_gensOK hg hwr
  have hr5 : orderOf (elemW fix5C.rep) = 5 := orderOf_eq_of_primeOrderOK hrr hord
  have hrA : Rep 1408 (tabW wordA) elemA := rep_elemW_of_gensOK hg (by decide)
  have hru : Rep 1408 (tabW u5Word) (elemW u5Word) := rep_elemW_of_gensOK hg hwu
  have hrv : Rep 1408 (tabW v5Word) (elemW v5Word) := rep_elemW_of_gensOK hg hwv
  obtain ⟨hYc, hYe⟩ := enumW_spec hY
  obtain ⟨-, hYw⟩ := enumW_gens_words hY
  have hLc : Nat.card ↥(zpowers (elemW fix5C.rep)) = 5 := by rw [Nat.card_zpowers, hr5]
  have hnotY : elemW fix5C.rep ∉ closure (elemW '' {w | w ∈ y5Words}) := fun hm => by
    have := (hYe.memT_iff hrr).2 hm
    rw [this] at hnY
    exact absurd hnY (by decide)
  have haYm : elemA ∈ closure (elemW '' {w | w ∈ y5Words}) := (hYe.memT_iff hrA).1 haY
  obtain ⟨φ, -, hrange, hker⟩ := blkData_spec hblk
  have hφ120 : Nat.card ↥φ.range = 120 := by
    rw [hrange]
    exact blkImage_spec hblk (by show 5 < 2 ^ 32; norm_num) himg
  have hφa : φ ⟨elemA, haYm⟩ = 1 :=
    (hker ⟨elemA, haYm⟩).2 fun p => blkTrivOK_spec hrA haTriv p
  exact TwoHSData.isShapeCentralizerFiveC_of_data _ (zpowers (elemW fix5C.rep))
    (closure (elemW '' {w | w ∈ y5Words})) φ
    (zpowers_le_inf_centralizer (elemW_mem fix5C.rep))
    (closure_words_le_inf_centralizer hg hYw hrr hcY) (by rw [hX, hLc, hYc]) hLc
    (fun l hl x hx => mul_comm_of_mem_zpowers hx l hl)
    (eq_one_of_mem_zpowers_of_not_mem hr5 hnotY) hYc hφ120 haYm ha2 ha1
    (fun y hy => (hacen y (closure_elemW_le _ hy)).symm) hφa
    ((hYe.memT_iff hru).1 huY) ((hYe.memT_iff hrv).1 hvY)
    (commutatorEqOK_spec hru hrv hrA hcomm)

theorem isShapeCentralizerSeven_of_shape7OK (h : shape7OK = true) (ha2 : elemA * elemA = 1)
    (ha1 : elemA ≠ 1) (hacen : ∀ g ∈ P1408, elemA * g = g * elemA)
    (hX : Nat.card ↥(P1408 ⊓ centralizer ({elemW fix7.rep} : Set (Equiv.Perm (Fin 1408)))) = 28)
    (hcl : closure (elemW '' {w | w ∈ fix7.cent}) =
      P1408 ⊓ centralizer ({elemW fix7.rep} : Set (Equiv.Perm (Fin 1408)))) :
    IsShapeCentralizerSeven
      ↥(P1408 ⊓ centralizer ({elemW fix7.rep} : Set (Equiv.Perm (Fin 1408)))) := by
  simp only [shape7OK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, hwr⟩, hord⟩, hww⟩, hcw⟩, hord2⟩, hcr⟩, hcc⟩, hne⟩ := h
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrr : Rep 1408 (tabW fix7.rep) (elemW fix7.rep) := rep_elemW_of_gensOK hg hwr
  have hrA : Rep 1408 (tabW wordA) elemA := rep_elemW_of_gensOK hg (by decide)
  have hrw : Rep 1408 (tabW w7Word) (elemW w7Word) := rep_elemW_of_gensOK hg hww
  have hr7 : orderOf (elemW fix7.rep) = 7 := orderOf_eq_of_primeOrderOK hrr hord
  have hw2' : orderOf (elemW w7Word) = 2 := orderOf_eq_of_primeOrderOK hrw hord2
  have hw2 := mul_self_eq_one_of_orderOf_eq_two hw2'
  have hw1 := ne_one_of_orderOf_eq_two hw2'
  have hwa : elemA ≠ elemW w7Word := fun hh => by
    have := (tblEq_iff_eq hrw hrA).2 hh.symm
    rw [this] at hne
    exact absurd hne (by decide)
  have haw : elemA * elemW w7Word = elemW w7Word * elemA := hacen _ (elemW_mem _)
  have hwr' : elemW w7Word * elemW fix7.rep = elemW fix7.rep * elemW w7Word :=
    (commTT_iff hrw hrr).1 (List.all_eq_true.1 hcr w7Word (by simp))
  have hLX := zpowers_le_inf_centralizer (elemW_mem fix7.rep)
  have hVX : closure ({elemA, elemW w7Word} : Set (Equiv.Perm (Fin 1408))) ≤
      P1408 ⊓ centralizer ({elemW fix7.rep} : Set (Equiv.Perm (Fin 1408))) := by
    rw [closure_le]
    rintro v (rfl | hv)
    · exact Subgroup.mem_inf.2 ⟨elemA_mem, mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hacen _ (elemW_mem fix7.rep)).symm⟩
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Subgroup.mem_inf.2 ⟨elemW_mem _, mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hwr'.symm⟩
  have hV4 := TwoHSData.card_closure_pair ha2 hw2 haw ha1 hw1 hwa
  have hS7 : Nat.card ↥(zpowers (elemW fix7.rep)) = 7 := by rw [Nat.card_zpowers, hr7]
  refine TwoHSData.isShapeCentralizerSeven_of_data _ _ _ hVX hLX hX hV4 hS7 ?_ ?_ ?_
  · intro v hv x hx
    have hx' : x ∈ closure (elemW '' {w | w ∈ fix7.cent}) := by rw [hcl]; exact hx
    have := commute_of_closure (S := ({elemA, elemW w7Word} : Set (Equiv.Perm (Fin 1408))))
      (T := elemW '' {w | w ∈ fix7.cent}) ?_ v hv x hx'
    · exact this.symm
    · intro s hs t ht
      obtain ⟨c, hc, rfl⟩ := ht
      rcases hs with rfl | hs
      · exact hacen _ (elemW_mem c)
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ((commTT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hcw c hc)) hrw).1
          (List.all_eq_true.1 hcc c hc)).symm
  · intro v hv
    rcases (TwoHSData.mem_closure_pair_iff ha2 hw2 haw).1 hv with h1 | h1 | h1 | h1
    · rw [h1, one_mul]
    · rw [h1]
      exact ha2
    · rw [h1]
      exact hw2
    · have hba : Commute (elemW w7Word) elemA := haw.symm
      rw [h1, hba.mul_mul_mul_comm elemA (elemW w7Word), ha2, hw2, one_mul]
  · intro v hv hvS
    have hdisj : Disjoint (closure ({elemA, elemW w7Word} : Set (Equiv.Perm (Fin 1408))))
        (zpowers (elemW fix7.rep)) :=
      Subgroup.disjoint_of_coprime_natCard (by rw [hV4, hS7]; norm_num)
    exact Subgroup.disjoint_def.1 hdisj hv hvS

end CFSG.EvenSporadicStandard.HNRecog
