module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0PlanesAux
public import Certificates.Certificate450285
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Elements

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

abbrev planeGenTabAt (tabs : Array Table) (dws : Array (List ℤ)) (u v : List ℤ) (s : ℕ) : Table :=
  planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) (planeGenWord dws u v s)

structure PlanesFacts (tabs : Array Table) (X T : Array (Array ℕ)) (par lab sep : Array ℕ)
    (dws : Array (List ℤ)) (u v : List ℤ) : Prop where
  lettersSize : (planeLetters tabs).size = 16
  lettersInv : ∀ l < 16, invOK degree (planeLetters tabs)[l]!
    (invT degree (planeLetters tabs)[l]!) = true
  rowsSize : X.size = 891
  rowSize : ∀ i < 891, X[i]!.size = 24
  rowLt : ∀ i < 891, ∀ j < 24, (X[i]!)[j]! < 920808
  rowMono : ∀ i < 891, ∀ j < 23, (X[i]!)[j]! < (X[i]!)[j + 1]!
  base : ∀ j < 24, ∃ i < 24, planeArr[i]! = (X[0]!)[j]!
  distinct : ∀ i < 891, ∀ j < i, ∃ a < 24, ∀ b < 24, (X[j]!)[b]! ≠ (X[i]!)[a]!
  sepSize : sep.size = 21
  sepLt : ∀ t < 21, sep[t]! < 891
  sepMem : ∀ t < 21, ∀ i < 24,
    ((∃ b < 24, (X[sep[t]!]!)[b]! = planeArr[i]!) ↔ (i < 3 ∨ i = t + 3))
  dwsSize : dws.size = 2
  dwsLetters : ∀ s < 2, ∀ l ∈ dws[s]!, 1 ≤ l.natAbs ∧ l.natAbs ≤ 13
  fixGen : ∀ s < 14, ap (planeGenTabAt tabs dws u v s) 0 = 0 ∧
    ap (planeGenTabAt tabs dws u v s) 1479 = 1479 ∧ ap (planeGenTabAt tabs dws u v s) 99705 = 99705
  fixU : ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) u) 0 = 0 ∧
    ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) u) 1479 = 1479 ∧
    ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) u) 99705 = 99705
  fixV : ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) v) 0 = 0 ∧
    ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) v) 1479 = 1479 ∧
    ap (planeGenTab (planeLetters tabs) ((planeLetters tabs).map (invT degree)) v) 99705 = 99705
  tabsSize : T.size = 14
  tabSize : ∀ s < 14, T[s]!.size = 891
  tabLt : ∀ s < 14, ∀ i < 891, (T[s]!)[i]! < 891
  act : ∀ s < 14, ∀ i < 891, ∀ a < 24, ∃ b < 24,
    (X[(T[s]!)[i]!]!)[b]! = ap (planeGenTabAt tabs dws u v s) ((X[i]!)[a]!)
  parSize : par.size = 891
  labSize : lab.size = 891
  tree : ∀ k, 0 < k → k < 891 → par[k]! < k ∧ lab[k]! < 14 ∧ (T[lab[k]!]!)[par[k]!]! = k
  masks : fixMasks T = fixMasksExpected

theorem lettersInvOK_spec {gs : Array Table} (h : lettersInvOK gs = true) :
    gs.size = 16 ∧ ∀ l < 16, invOK degree gs[l]! (invT degree gs[l]!) = true := by
  unfold lettersInvOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun l hl => allIn_zero_iff.1 h.2 l hl⟩

theorem rowOK_spec {r : Array ℕ} (h : rowOK r = true) :
    r.size = 24 ∧ (∀ j < 24, r[j]! < 920808) ∧ ∀ j < 23, r[j]! < r[j + 1]! := by
  unfold rowOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun j hj => ?_, fun j hj => ?_⟩
  · simpa using allIn_zero_iff.1 h2 j hj
  · simpa using allIn_zero_iff.1 h3 j hj

theorem rowsOK_spec {X : Array (Array ℕ)} (h : rowsOK X = true) :
    X.size = 891 ∧ ∀ i < 891, rowOK X[i]! = true := by
  unfold rowsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun i hi => allIn_zero_iff.1 h.2 i hi⟩

theorem baseOK_spec {X : Array (Array ℕ)} (h : baseOK X = true) :
    ∀ j < 24, ∃ i < 24, planeArr[i]! = (X[0]!)[j]! := by
  unfold baseOK at h
  intro j hj
  obtain ⟨i, -, hi, h2⟩ := anyIn_eq_true.1 (allIn_zero_iff.1 h j hj)
  exact ⟨i, hi, by simpa using h2⟩

theorem distinctOK_spec {X : Array (Array ℕ)} (h : distinctOK X = true) :
    ∀ i < 891, ∀ j < i, ∃ a < 24, ∀ b < 24, (X[j]!)[b]! ≠ (X[i]!)[a]! := by
  unfold distinctOK at h
  intro i hi j hj
  obtain ⟨a, -, ha, h2⟩ := anyIn_eq_true.1 (allIn_zero_iff.1 (allIn_zero_iff.1 h i hi) j hj)
  refine ⟨a, ha, fun b hb hbe => ?_⟩
  have := memRow_eq_true.2 ⟨b, hb, hbe⟩
  simp [this] at h2

theorem sepOK_spec {X : Array (Array ℕ)} {sep : Array ℕ} (h : sepOK X sep = true) :
    sep.size = 21 ∧ ∀ t < 21, sep[t]! < 891 ∧ ∀ i < 24,
      ((∃ b < 24, (X[sep[t]!]!)[b]! = planeArr[i]!) ↔ (i < 3 ∨ i = t + 3)) := by
  unfold sepOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun t ht => ?_⟩
  have h1 := allIn_zero_iff.1 h.2 t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1.1, fun i hi => ?_⟩
  have h2 := allIn_zero_iff.1 h1.2 i hi
  rw [beq_iff_eq] at h2
  constructor
  · rintro ⟨b, hb, hbe⟩
    have h3 : memRow X[sep[t]!]! planeArr[i]! = true := memRow_eq_true.2 ⟨b, hb, hbe⟩
    rw [h2] at h3
    simpa using h3
  · intro hi3
    have h3 : memRow X[sep[t]!]! planeArr[i]! = true := by
      rw [h2]
      simpa using hi3
    exact memRow_eq_true.1 h3

theorem dwordsOK_spec {dws : Array (List ℤ)} (h : dwordsOK dws = true) :
    dws.size = 2 ∧ ∀ s < 2, ∀ l ∈ dws[s]!, 1 ≤ l.natAbs ∧ l.natAbs ≤ 13 := by
  unfold dwordsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun s hs l hl => ?_⟩
  have := allIn_zero_iff.1 h.2 s hs
  simpa using List.all_eq_true.1 this l hl

theorem fix3_spec {t : Table} (h : fix3 t = true) :
    ap t 0 = 0 ∧ ap t 1479 = 1479 ∧ ap t 99705 = 99705 := by
  unfold fix3 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem fixTripleOK_spec {G : Array Table} (h : fixTripleOK G = true) :
    G.size = 14 ∧ ∀ s < 14, ap G[s]! 0 = 0 ∧ ap G[s]! 1479 = 1479 ∧ ap G[s]! 99705 = 99705 := by
  unfold fixTripleOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun s hs => fix3_spec (allIn_zero_iff.1 h.2 s hs)⟩

theorem actOK_spec {G : Array Table} {X T : Array (Array ℕ)} (h : actOK G X T = true) :
    T.size = 14 ∧ ∀ s < 14, T[s]!.size = 891 ∧ ∀ i < 891, (T[s]!)[i]! < 891 ∧
      ∀ a < 24, ∃ b < 24, (X[(T[s]!)[i]!]!)[b]! = ap G[s]! ((X[i]!)[a]!) := by
  unfold actOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun s hs => ?_⟩
  have h1 := allIn_zero_iff.1 h.2 s hs
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  refine ⟨h1.1, fun i hi => ?_⟩
  have h2 := allIn_zero_iff.1 h1.2 i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact ⟨h2.1, fun a ha => memRow_eq_true.1 (allIn_zero_iff.1 h2.2 a ha)⟩

theorem planeTreeOK_spec {T : Array (Array ℕ)} {par lab : Array ℕ}
    (h : planeTreeOK T par lab = true) :
    par.size = 891 ∧ lab.size = 891 ∧ ∀ k, 0 < k → k < 891 →
      par[k]! < k ∧ lab[k]! < 14 ∧ (T[lab[k]!]!)[par[k]!]! = k := by
  unfold planeTreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun k hk0 hk => ?_⟩
  have := allIn_one_iff.1 h3 k hk0 hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem PlanesFacts.of_planesOKAt {tabs : Array Table} {X T : Array (Array ℕ)}
    {par lab sep : Array ℕ} {dws : Array (List ℤ)} {u v : List ℤ}
    (h : planesOKAt tabs X T par lab sep dws u v = true) :
    PlanesFacts tabs X T par lab sep dws u v := by
  unfold planesOKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hL, hR, hB, hD, hS, hW, hF, hU, hV, hA, hT, hM⟩ := h
  obtain ⟨hLs, hLi⟩ := lettersInvOK_spec hL
  obtain ⟨hRs, hRr⟩ := rowsOK_spec hR
  obtain ⟨hSs, hSm⟩ := sepOK_spec hS
  obtain ⟨hWs, hWl⟩ := dwordsOK_spec hW
  obtain ⟨hFs, hFf⟩ := fixTripleOK_spec hF
  obtain ⟨hAs, hAa⟩ := actOK_spec hA
  obtain ⟨hTp, hTl, hTt⟩ := planeTreeOK_spec hT
  refine ⟨hLs, hLi, hRs, fun i hi => (rowOK_spec (hRr i hi)).1,
    fun i hi => (rowOK_spec (hRr i hi)).2.1, fun i hi => (rowOK_spec (hRr i hi)).2.2,
    baseOK_spec hB, distinctOK_spec hD, hSs, fun t ht => (hSm t ht).1,
    fun t ht i hi => (hSm t ht).2 i hi, hWs, hWl, fun s hs => ?_, fix3_spec hU, fix3_spec hV,
    hAs, fun s hs => (hAa s hs).1, fun s hs i hi => ((hAa s hs).2 i hi).1,
    fun s hs i hi a ha => ?_, hTp, hTl, hTt, hM⟩
  · have := hFf s hs
    rwa [getElem!_map_range _ hs] at this
  · have := ((hAa s hs).2 i hi).2 a ha
    rwa [getElem!_map_range _ hs] at this

theorem q0PlanesOK_eq_true : q0PlanesOK () = true :=
  Certificates.certificate450285

theorem planesFacts :
    PlanesFacts objTabs (planeXData ()) (planeTabs ()) (planePar ()) (planeLab ()) (planeSep ())
      (planeDWords ()) (planeUWord ()) (planeVWord ()) :=
  PlanesFacts.of_planesOKAt q0PlanesOK_eq_true

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
