module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Level
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models

public section



namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

private theorem hOrd : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
  CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

private theorem card_alt_eq (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [nat_card_alternatingGroup, Nat.card_fin]

private theorem card_alt_mono (k m : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m) :
    k.factorial / 2 ≤ Nat.card (alternatingGroup (Fin m)) := by
  rw [card_alt_eq m (hk.trans hkm)]
  exact Nat.div_le_div_right (Nat.factorial_le hkm)

private theorem fv5 : (5 : ℕ).factorial / 2 = 60 := by norm_num [Nat.factorial]
private theorem fv6 : (6 : ℕ).factorial / 2 = 360 := by norm_num [Nat.factorial]
private theorem fv7 : (7 : ℕ).factorial / 2 = 2520 := by norm_num [Nat.factorial]
private theorem fv8 : (8 : ℕ).factorial / 2 = 20160 := by norm_num [Nat.factorial]
private theorem fv9 : (9 : ℕ).factorial / 2 = 181440 := by norm_num [Nat.factorial]
private theorem fv10 : (10 : ℕ).factorial / 2 = 1814400 := by norm_num [Nat.factorial]
private theorem fv11 : (11 : ℕ).factorial / 2 = 19958400 := by norm_num [Nat.factorial]

private theorem card_spor (s : TauCeti.SporadicName) :
    Nat.card (TauCeti.CFSGIndex.sporadic s).Group =
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
  CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s

private theorem lie_hasLieModel (d : TauCeti.ValidLieTypeIndex) :
    ∃ (t : CFSG.Open.StatedLieTag) (n p f : ℕ),
      CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie d).Group t n p f := by
  by_cases h2 : d.1.characteristic = 2
  · obtain ⟨t, n, f, h⟩ :=
      CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d h2 (MulEquiv.refl _)
    exact ⟨t, n, 2, f, h⟩
  · obtain ⟨t, n, f, h⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.exists_blueprint_lieModel_of_odd d h2 (MulEquiv.refl _)
    exact ⟨t, n, _, f, h⟩

private theorem catalogIs_split {S : Type} [Group S] {P : TauCeti.CFSGIndex → Prop}
    (h : catalogIs S P) :
    (∃ (n : ℕ) (hn : 5 ≤ n), P (TauCeti.CFSGIndex.alternating n hn) ∧
      Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, P (TauCeti.CFSGIndex.lie d) ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ s : TauCeti.SporadicName, P (TauCeti.CFSGIndex.sporadic s) ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group)) ∨
    (∃ (p : ℕ) (hp : p.Prime), P (TauCeti.CFSGIndex.cyclic p hp) ∧
      Nonempty (S ≃* Multiplicative (ZMod p))) := by
  obtain ⟨i, hi, e⟩ := h
  cases i with
  | cyclic p hp => exact Or.inr (Or.inr (Or.inr ⟨p, hp, hi, e⟩))
  | alternating n hn => exact Or.inl ⟨n, hn, hi, e⟩
  | lie d => exact Or.inr (Or.inl ⟨d, hi, e⟩)
  | sporadic s => exact Or.inr (Or.inr (Or.inl ⟨s, hi, e⟩))

private theorem alt_of_isAltN {S : Type} [Group S] {n : ℕ} (h : catalogIs S (isAltN n)) :
    Nonempty (S ≃* alternatingGroup (Fin n)) := by
  rcases catalogIs_split h with ⟨m, hm, hP, e⟩ | ⟨d, hP, -⟩ | ⟨s, hP, -⟩ | ⟨p, hp, hP, -⟩
  · simp only [isAltN] at hP
    subst hP
    exact e
  · simp [isAltN] at hP
  · simp [isAltN] at hP
  · simp [isAltN] at hP

private theorem spor_of_isSporIdx {S : Type} [Group S] {s : TauCeti.SporadicName}
    (h : catalogIs S (isSporIdx s)) :
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) := by
  rcases catalogIs_split h with ⟨m, hm, hP, -⟩ | ⟨d, hP, -⟩ | ⟨s', hP, e⟩ | ⟨p, hp, hP, -⟩
  · simp [isSporIdx] at hP
  · simp [isSporIdx] at hP
  · simp only [isSporIdx] at hP
    subst hP
    exact e
  · simp [isSporIdx] at hP

private theorem alt_not_iso_lie {m : ℕ} (hm : 9 ≤ m) (d : TauCeti.ValidLieTypeIndex)
    (e : alternatingGroup (Fin m) ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  obtain ⟨t, n, p, f, h⟩ := lie_hasLieModel d
  have h' := CFSG.Blueprint.LieModel.of_mulEquiv e.symm h
  exact CFSG.OddStandard.AltStdSec.altNotLieType hOrd hm
    ⟨t, n, p, f, CFSG.Blueprint.LieModel.admissible h', h'⟩

private theorem alt7_not_iso_lie (d : TauCeti.ValidLieTypeIndex)
    (e : alternatingGroup (Fin 7) ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  obtain ⟨t, n, p, f, h⟩ := lie_hasLieModel d
  exact CFSG.ComponentClassification.CatFC.not_lieModel_of_alt7 hOrd
    (CFSG.Blueprint.LieModel.admissible h) h ⟨e.symm⟩

private theorem held_not_iso_lie (d : TauCeti.ValidLieTypeIndex)
    (hc : Nat.card (TauCeti.CFSGIndex.lie d).Group = 4030387200) : False := by
  obtain ⟨t, n, p, f, h⟩ := lie_hasLieModel d
  exact CFSG.ComponentClassification.CatLeaf.lieModel_card_ne_held hOrd
    (CFSG.Blueprint.LieModel.admissible h) h hc

private theorem k2Spor_mem {s : TauCeti.SporadicName} (hs : k2Spor 3 s) :
    CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s ∈
      ({7920, 50232960, 42305421312000, 495766656000, 448345497600, 64561751654400,
        4089470473293004800, 898128000, 51765179004000000,
        4154781481226426191177580544000000, 90745943887872000, 460815505920,
        1255205709190661721292800,
        808017424794512875886459904961710757005754368000000000} : Finset ℕ) := by
  cases s <;> simp_all [k2Spor, CFSG.HardMathSupport.Solomon.Coordinator.sporOrd,
    CFSG.Open.orderJ3, CFSG.Open.orderFi23, CFSG.Open.orderLy, CFSG.Open.orderBabyMonster,
    CFSG.Open.orderTh, CFSG.Open.orderON, CFSG.Open.orderFi24Prime, CFSG.Open.orderMonster]

private theorem k2Spor_ne_fact {m : ℕ} (hm : 7 ≤ m) {s : TauCeti.SporadicName}
    (hs : k2Spor 3 s) : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s ≠ m.factorial / 2 := by
  intro heq
  have hmem := k2Spor_mem hs
  rw [heq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases le_or_gt 45 m with h45 | h45
  · have h1 : (45 : ℕ).factorial / 2 ≤ m.factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le h45)
    have h2 : (45 : ℕ).factorial / 2 =
        59811110432740097280981580747828857532191866880000000000 := by
      norm_num [Nat.factorial]
    omega
  · interval_cases m <;> norm_num [Nat.factorial] at hmem

private theorem chev3_alt7 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 7)) :
    ¬ IsChevSimple 3 S := by
  intro hC
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ | ⟨p, hp, hP, -⟩
    · simp [onLie] at hP
    · exact alt7_not_iso_lie d (e.symm.trans e')
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · have hn6 : n = 6 := by simpa [ambiguousChev] using hP
      subst hn6
      have h1 := Nat.card_congr (e.symm.trans e').toEquiv
      have h2 := card_alt_eq 7 (by norm_num)
      have h3 := card_alt_eq 6 (by norm_num)
      have := fv7
      have := fv6
      omega
    · exact alt7_not_iso_lie d (e.symm.trans e')
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

private theorem chev3_alt_ge9 {m : ℕ} (hm : 9 ≤ m) {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin m)) : ¬ IsChevSimple 3 S := by
  intro hC
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ | ⟨p, hp, hP, -⟩
    · simp [onLie] at hP
    · exact alt_not_iso_lie hm d (e.symm.trans e')
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · have hn6 : n = 6 := by simpa [ambiguousChev] using hP
      subst hn6
      have h1 := card_alt_mono 9 m (by norm_num) hm
      have h2 := Nat.card_congr (e.symm.trans e').toEquiv
      have h3 := card_alt_eq 6 (by norm_num)
      have := fv9
      have := fv6
      omega
    · exact alt_not_iso_lie hm d (e.symm.trans e')
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

private theorem chev3_held {S : Type} [Group S] (hS : Nat.card S = 4030387200) :
    ¬ IsChevSimple 3 S := by
  intro hC
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ | ⟨p, hp, hP, -⟩
    · simp [onLie] at hP
    · exact held_not_iso_lie d (by rw [← Nat.card_congr e'.toEquiv, hS])
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · have hn6 : n = 6 := by simpa [ambiguousChev] using hP
      subst hn6
      have h2 := Nat.card_congr e'.toEquiv
      have h3 := card_alt_eq 6 (by norm_num)
      have := fv6
      omega
    · exact held_not_iso_lie d (by rw [← Nat.card_congr e'.toEquiv, hS])
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

private theorem k2_alt7 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 7)) :
    ¬ catalogIs S (k2 3) := by
  intro h
  rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, ⟨e'⟩⟩ |
    ⟨p, hp, hP, -⟩
  · have hn' : n = 5 ∨ n = 9 := by simpa [k2] using hP
    have h1 := Nat.card_congr (e.symm.trans e').toEquiv
    have h2 := card_alt_eq 7 (by norm_num)
    have h3 := card_alt_eq n (by omega)
    have := fv5
    have := fv7
    have := fv9
    rcases hn' with rfl | rfl <;> omega
  · exact alt7_not_iso_lie d (e.symm.trans e')
  · have hs : k2Spor 3 s := by simpa [k2] using hP
    have h1 := Nat.card_congr (e.symm.trans e').toEquiv
    rw [card_spor] at h1
    exact k2Spor_ne_fact (m := 7) (by norm_num) hs (h1.symm.trans (card_alt_eq 7 (by norm_num)))
  · simp [k2] at hP

private theorem k2_alt_ge10 {m : ℕ} (hm : 10 ≤ m) {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin m)) : ¬ catalogIs S (k2 3) := by
  intro h
  rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, ⟨e'⟩⟩ |
    ⟨p, hp, hP, -⟩
  · have hn' : n = 5 ∨ n = 9 := by simpa [k2] using hP
    have h1 := Nat.card_congr (e.symm.trans e').toEquiv
    have h2 := card_alt_mono 10 m (by norm_num) hm
    have h3 := card_alt_eq n (by omega)
    have := fv5
    have := fv9
    have := fv10
    rcases hn' with rfl | rfl <;> omega
  · exact alt_not_iso_lie (by omega) d (e.symm.trans e')
  · have hs : k2Spor 3 s := by simpa [k2] using hP
    have h1 := Nat.card_congr (e.symm.trans e').toEquiv
    rw [card_spor] at h1
    exact k2Spor_ne_fact (m := m) (by omega) hs (h1.symm.trans (card_alt_eq m (by omega)))
  · simp [k2] at hP

private theorem k3_alt_ge11 {m : ℕ} (hm : 11 ≤ m) {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin m)) : ¬ catalogIs S (k3 3) := by
  intro h
  have h2 := card_alt_mono 11 m (by norm_num) hm
  rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, ⟨e'⟩⟩ |
    ⟨p, hp, hP, -⟩
  · have hn' : n = 7 ∨ n = 10 := by simpa [k3] using hP
    have h1 := Nat.card_congr (e.symm.trans e').toEquiv
    have h3 := card_alt_eq n (by omega)
    have := fv7
    have := fv10
    have := fv11
    rcases hn' with rfl | rfl <;> omega
  · exact alt_not_iso_lie (by omega) d (e.symm.trans e')
  · have hs : s = .M12 ∨ s = .M22 := by simpa [k3] using hP
    have h1 := Nat.card_congr (e.symm.trans e').toEquiv
    rw [card_spor] at h1
    have := fv11
    have e1 : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .M12 = 95040 := rfl
    have e2 : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .M22 = 443520 := rfl
    rcases hs with rfl | rfl <;> omega
  · simp [k3] at hP

private theorem k2_held {S : Type} [Group S] (hS : Nat.card S = 4030387200) :
    ¬ catalogIs S (k2 3) := by
  intro h
  rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, ⟨e'⟩⟩ |
    ⟨p, hp, hP, -⟩
  · have hn' : n = 5 ∨ n = 9 := by simpa [k2] using hP
    have h1 := Nat.card_congr e'.toEquiv
    have h3 := card_alt_eq n (by omega)
    have := fv5
    have := fv9
    rcases hn' with rfl | rfl <;> omega
  · exact held_not_iso_lie d (by rw [← Nat.card_congr e'.toEquiv, hS])
  · have hs : k2Spor 3 s := by simpa [k2] using hP
    have h1 := Nat.card_congr e'.toEquiv
    rw [card_spor, hS] at h1
    have hmem := k2Spor_mem hs
    rw [← h1] at hmem
    norm_num at hmem
  · simp [k2] at hP

private theorem k3_held {S : Type} [Group S] (hS : Nat.card S = 4030387200) :
    ¬ catalogIs S (k3 3) := by
  intro h
  rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, ⟨e'⟩⟩ |
    ⟨p, hp, hP, -⟩
  · have hn' : n = 7 ∨ n = 10 := by simpa [k3] using hP
    have h1 := Nat.card_congr e'.toEquiv
    have h3 := card_alt_eq n (by omega)
    have := fv7
    have := fv10
    rcases hn' with rfl | rfl <;> omega
  · exact held_not_iso_lie d (by rw [← Nat.card_congr e'.toEquiv, hS])
  · have hs : s = .M12 ∨ s = .M22 := by simpa [k3] using hP
    have h1 := Nat.card_congr e'.toEquiv
    rw [card_spor, hS] at h1
    rcases hs with rfl | rfl <;>
      norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd] at h1
  · simp [k3] at hP

private theorem kLevel_three_of (S : Type) [Group S] (h1 : ¬ IsChevSimple 3 S)
    (h2 : ¬ catalogIs S (k2 3)) (h3 : catalogIs S (k3 3)) : kLevel 3 S = 3 := by
  rw [kLevel, if_neg h1, if_neg h2, if_pos h3]

private theorem kLevel_three_four_of (S : Type) [Group S] (h1 : ¬ IsChevSimple 3 S)
    (h2 : ¬ catalogIs S (k2 3)) (h3 : ¬ catalogIs S (k3 3)) : kLevel 3 S = 4 := by
  rw [kLevel, if_neg h1, if_neg h2, if_neg h3]

theorem kLevelAltAt_holds : KLevelAltAt := by
  intro Q _ _ hQ hO
  have hZ : IsPGroup 3 (Subgroup.center Q) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_of_pPrimeCore_eq_bot' Nat.prime_three hO
  rw [fullCoverLevel_eq_kLevel
    (listedMultiplierBound_of_tables
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      sporadicMultiplierTable_holds 3)
    (hatOddMultiplierBound_of_tables sporadicMultiplierTable_holds) Nat.prime_three (by decide)
    hQ hZ]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h7 | h10
    · obtain ⟨e⟩ := alt_of_isAltN h7
      have h5 : (5 : ℕ) ≤ 7 := by norm_num
      exact kLevel_three_of _ (chev3_alt7 e) (k2_alt7 e)
        ⟨TauCeti.CFSGIndex.alternating 7 h5, by simp [k3], ⟨e⟩⟩
    · obtain ⟨e⟩ := alt_of_isAltN h10
      have h5 : (5 : ℕ) ≤ 10 := by norm_num
      exact kLevel_three_of _ (chev3_alt_ge9 (by norm_num) e) (k2_alt_ge10 (by norm_num) e)
        ⟨TauCeti.CFSGIndex.alternating 10 h5, by simp [k3], ⟨e⟩⟩
  · rcases h with ⟨m, hm, h⟩ | h
    · obtain ⟨e⟩ := alt_of_isAltN h
      exact kLevel_three_four_of _ (chev3_alt_ge9 (by omega) e) (k2_alt_ge10 (by omega) e)
        (k3_alt_ge11 hm e)
    · obtain ⟨e⟩ := spor_of_isSporIdx h
      have hS : Nat.card (Q ⧸ Subgroup.center Q) = 4030387200 := by
        rw [Nat.card_congr e.toEquiv, card_spor]
        rfl
      exact kLevel_three_four_of _ (chev3_held hS) (k2_held hS) (k3_held hS)


private theorem numer_PSL2 (q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator CFSG.Open.StatedLieTag.PSL 2 q =
      q * (q ^ 2 - 1) := by
  have hI : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
  simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, hI]

private theorem numer_PSL3 (q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator CFSG.Open.StatedLieTag.PSL 3 q =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, hI, Finset.prod_pair]

private theorem numer_PSU3 (q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator CFSG.Open.StatedLieTag.PSU 3 q =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, hI, Finset.prod_pair, Nat.even_iff]

private theorem divisor_PSL2 (q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderDivisor CFSG.Open.StatedLieTag.PSL 2 q =
      Nat.gcd 2 (q - 1) := rfl

private theorem divisor_PSL3 (q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderDivisor CFSG.Open.StatedLieTag.PSL 3 q =
      Nat.gcd 3 (q - 1) := rfl

private theorem divisor_PSU3 (q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderDivisor CFSG.Open.StatedLieTag.PSU 3 q =
      Nat.gcd 3 (q + 1) := rfl

private theorem L3_size_ge {q : ℕ} (hq : 7 ≤ q) :
    5630688 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h2 : 49 ≤ q ^ 2 := by nlinarith
  have h3 : 343 ≤ q ^ 3 := by nlinarith
  have h2' : 48 ≤ q ^ 2 - 1 := by omega
  have h3' : 342 ≤ q ^ 3 - 1 := by omega
  calc 5630688 = 343 * (48 * 342) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h2' h3')

private theorem L3_size_ge8 {q : ℕ} (hq : 8 ≤ q) :
    16482816 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h2 : 64 ≤ q ^ 2 := by nlinarith
  have h3 : 512 ≤ q ^ 3 := by nlinarith
  have h2' : 63 ≤ q ^ 2 - 1 := by omega
  have h3' : 511 ≤ q ^ 3 - 1 := by omega
  calc 16482816 = 512 * (63 * 511) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h2' h3')

private theorem U3_size_ge {q : ℕ} (hq : 5 ≤ q) :
    378000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h2 : 25 ≤ q ^ 2 := by nlinarith
  have h3 : 125 ≤ q ^ 3 := by nlinarith
  have h2' : 24 ≤ q ^ 2 - 1 := by omega
  have h3' : 126 ≤ q ^ 3 + 1 := by omega
  calc 378000 = 125 * (24 * 126) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h2' h3')

private theorem alt8_order_six : ∃ x : alternatingGroup (Fin 8), orderOf x = 6 := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2 * (Equiv.swap 3 4 * Equiv.swap 5 6), ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide
  · rw [Subgroup.orderOf_mk, orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hm0
    interval_cases m <;> decide

private theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [card_alt_eq 8 (by norm_num)]
  exact fv8

private theorem alt8_not_A2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (hq : q.card % 9 = 4 ∨ q.card % 9 = 7)
    (e : ↥(alternatingGroup (Fin 8)) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩).Group) : False := by
  have hX : CFSG.Blueprint.LieModel ↥(alternatingGroup (Fin 8)) CFSG.Open.StatedLieTag.PSL 3
      q.p q.exponent :=
    CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_A 2 q hv e)
  have hadm := CFSG.Blueprint.LieModel.admissible hX
  by_cases hp2 : q.p = 2
  · have hcq : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
    have hord := (hOrd _ _ 3 q.p q.exponent hadm hX).2.1
    rw [card_alt8, ← TauCeti.PrimePower.card_def q, divisor_PSL3, numer_PSL3] at hord
    have hfpos := q.exponent_pos
    rcases (show q.exponent = 1 ∨ q.exponent = 2 ∨ 3 ≤ q.exponent by omega) with hf | hf | hf
    · rw [hcq, hf] at hq
      norm_num at hq
    · have hX2 : CFSG.Blueprint.LieModel ↥(alternatingGroup (Fin 8))
          CFSG.Open.StatedLieTag.PSL 3 2 2 := by
        rw [hp2, hf] at hX
        exact hX
      obtain ⟨x, hx⟩ := alt8_order_six
      exact CFSG.SeitzReduction.SporadicRefine.not_lieModel_psl_three_two_of_orderOf_six hx hX2
    · have h8 : 8 ≤ q.card := by
        rw [hcq]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
      have hsz := L3_size_ge8 h8
      have hg : Nat.gcd 3 (q.card - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      have := Nat.mul_le_mul_left 20160 hg
      linarith
  · exact CFSG.ComponentClassification.CatLeaf.lieModel_odd_card_ne_L34 hOrd hp2 hadm hX
      card_alt8

private theorem lieModel_twistedA2 {X : Type} [Group X] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group) :
    CFSG.Blueprint.LieModel X CFSG.Open.StatedLieTag.PSU 3 q.p q.exponent := by
  have h := CFSG.Models.lieModel_twistedA 2 q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ =
      q.p := TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ =
      q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  rw [hc, hf] at h
  exact CFSG.Models.LieModel.toBlueprint (by decide) h

private theorem rank_of_weakExc {r : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A r q).Valid}
    (hP : weakExcIndex (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩)) :
    r = 1 ∨ r = 2 := by
  rcases r with _ | _ | _ | r
  · simp [weakExcIndex, excIndex] at hP
  · exact Or.inl rfl
  · exact Or.inr rfl
  · simp [weakExcIndex, excIndex] at hP

private theorem rank_of_weakExc_tA {r : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA r q).Valid}
    (hP : weakExcIndex (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩)) :
    r = 2 := by
  rcases r with _ | _ | _ | r
  · simp [weakExcIndex, excIndex] at hP
  · simp [weakExcIndex, excIndex] at hP
  · rfl
  · simp [weakExcIndex, excIndex] at hP

private theorem rank_of_ambig2_A {r : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A r q).Valid}
    (hP : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩)) :
    r = 1 := by
  rcases r with _ | _ | r
  · simp [ambiguousChev] at hP
  · rfl
  · simp [ambiguousChev] at hP

private theorem rank_of_ambig2_tA {r : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA r q).Valid}
    (hP : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩)) :
    r = 2 := by
  rcases r with _ | _ | _ | _ | r
  · simp [ambiguousChev] at hP
  · simp [ambiguousChev] at hP
  · rfl
  · simp [ambiguousChev] at hP
  · simp [ambiguousChev] at hP

private theorem alt8_not_tA2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (hq : q.card % 9 = 2 ∨ q.card % 9 = 5)
    (e : ↥(alternatingGroup (Fin 8)) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group) : False := by
  have hX : CFSG.Blueprint.LieModel ↥(alternatingGroup (Fin 8)) CFSG.Open.StatedLieTag.PSU 3
      q.p q.exponent := lieModel_twistedA2 q hv e
  have hadm := CFSG.Blueprint.LieModel.admissible hX
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have h3 : 3 ≤ q.card := hr.2 rfl
  have hq5 : 5 ≤ q.card := by omega
  have hord := (hOrd _ _ 3 q.p q.exponent hadm hX).2.1
  rw [card_alt8, ← TauCeti.PrimePower.card_def q, divisor_PSU3, numer_PSU3] at hord
  have hg : Nat.gcd 3 (q.card + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hsz := U3_size_ge hq5
  have := Nat.mul_le_mul_left 20160 hg
  linarith

private theorem alt8_not_A1 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (hp : q.p = 2) (hodd : Odd q.exponent) (hf : 1 < q.exponent)
    (e : ↥(alternatingGroup (Fin 8)) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group) : False := by
  have hX : CFSG.Blueprint.LieModel ↥(alternatingGroup (Fin 8)) CFSG.Open.StatedLieTag.PSL 2
      q.p q.exponent :=
    CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_A 1 q hv e)
  have hadm := CFSG.Blueprint.LieModel.admissible hX
  have hcq : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp]
  have hord := (hOrd _ _ 2 q.p q.exponent hadm hX).2.1
  rw [card_alt8, ← TauCeti.PrimePower.card_def q, divisor_PSL2, numer_PSL2] at hord
  obtain ⟨j, hj⟩ := hodd
  have hodd' : Odd (q.card - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, q.exponent = k + 1 := ⟨q.exponent - 1, by omega⟩
    have hpow : q.card = 2 * 2 ^ k := by
      rw [hcq, hk, pow_succ]
      ring
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    generalize 2 ^ k = t at hpow hk1 ⊢
    exact ⟨t - 1, by omega⟩
  rw [show Nat.gcd 2 (q.card - 1) = 1 from Nat.coprime_two_left.mpr hodd'] at hord
  rcases (show q.exponent = 3 ∨ 5 ≤ q.exponent by omega) with hf3 | hf5
  · rw [hcq, hf3] at hord
    norm_num at hord
  · have h32 : 32 ≤ q.card := by
      rw [hcq]
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf5
    have hsq : 1024 ≤ q.card ^ 2 := by nlinarith
    have h1023 : 1023 ≤ q.card ^ 2 - 1 := Nat.le_sub_of_add_le hsq
    have hmul : 32 * 1023 ≤ q.card * (q.card ^ 2 - 1) := Nat.mul_le_mul h32 h1023
    linarith

private theorem altNotWeak_lie8 (d : TauCeti.ValidLieTypeIndex)
    (e : ↥(alternatingGroup (Fin 8)) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hP : weakExcIndex (TauCeti.CFSGIndex.lie d)) : False := by
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | A r q =>
    rcases rank_of_weakExc hP with rfl | rfl
    · have hq : q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent := by
        simpa [weakExcIndex, excIndex] using hP
      exact alt8_not_A1 q hv hq.1 hq.2.1 hq.2.2 e
    · have hq : q.card % 9 = 4 ∨ q.card % 9 = 7 := by simpa [weakExcIndex, excIndex] using hP
      exact alt8_not_A2 q hv hq e
  | twistedA r q =>
    rcases rank_of_weakExc_tA hP with rfl
    have hq : q.card % 9 = 2 ∨ q.card % 9 = 5 := by simpa [weakExcIndex, excIndex] using hP
    exact alt8_not_tA2 q hv hq e
  | _ => simp [weakExcIndex, excIndex] at hP

theorem altNotWeakExcAt_holds : AltNotWeakExcAt := by
  intro m hm h
  rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, ⟨e'⟩⟩ |
    ⟨p, hp, hP, -⟩
  · have hn' : n = 6 ∨ n = 7 := by simpa [weakExcIndex, excIndex] using hP
    have h1 := Nat.card_congr e'.toEquiv
    have h2 := card_alt_mono 8 m (by norm_num) hm
    have h3 := card_alt_eq n (by omega)
    have := fv6
    have := fv7
    have := fv8
    rcases hn' with rfl | rfl <;> omega
  · by_cases hm9 : 9 ≤ m
    · exact alt_not_iso_lie hm9 d e'
    · have hm8 : m = 8 := by omega
      subst hm8
      exact altNotWeak_lie8 d e' hP
  · have hs : s = .M22 := by simpa [weakExcIndex, excIndex] using hP
    subst hs
    have h1 := Nat.card_congr e'.toEquiv
    rw [card_spor] at h1
    have e22 : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .M22 = 443520 := rfl
    rw [e22] at h1
    rcases (show m = 8 ∨ m = 9 ∨ 10 ≤ m by omega) with rfl | rfl | h10
    · have := card_alt_eq 8 (by norm_num)
      have := fv8
      omega
    · have := card_alt_eq 9 (by norm_num)
      have := fv9
      omega
    · have := card_alt_mono 10 m (by norm_num) h10
      have := fv10
      omega
  · simp [weakExcIndex, excIndex] at hP

private theorem card_ambig2_lie {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex)
    (hP : ambiguousChev 2 (TauCeti.CFSGIndex.lie d))
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) : Nat.card X = 168 ∨ Nat.card X = 6048 := by
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | A r q =>
    rcases rank_of_ambig2_A hP with rfl
    have hq : q.card = 7 := by simpa [ambiguousChev] using hP
    have hY : CFSG.Blueprint.LieModel X CFSG.Open.StatedLieTag.PSL 2 q.p q.exponent :=
      CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_A 1 q hv e)
    have hord := (hOrd _ _ 2 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
    rw [← TauCeti.PrimePower.card_def q, divisor_PSL2, numer_PSL2, hq] at hord
    left
    norm_num at hord
    omega
  | twistedA r q =>
    rcases rank_of_ambig2_tA hP with rfl
    have hq : q.card = 3 := by simpa [ambiguousChev] using hP
    have hY : CFSG.Blueprint.LieModel X CFSG.Open.StatedLieTag.PSU 3 q.p q.exponent :=
      lieModel_twistedA2 q hv e
    have hord := (hOrd _ _ 3 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
    rw [← TauCeti.PrimePower.card_def q, divisor_PSU3, numer_PSU3, hq] at hord
    right
    norm_num at hord
    omega
  | _ => simp [ambiguousChev] at hP

private theorem card_ambig2_alt {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (hP : ambiguousChev 2 (TauCeti.CFSGIndex.alternating n hn))
    (e : X ≃* alternatingGroup (Fin n)) :
    Nat.card X = 60 ∨ Nat.card X = 360 ∨ Nat.card X = 20160 := by
  have h := Nat.card_congr e.toEquiv
  have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by simpa [ambiguousChev] using hP
  rw [h, card_alt_eq n (by omega)]
  rcases hn' with rfl | rfl | rfl
  · left; exact fv5
  · right; left; exact fv6
  · right; right; exact fv8



private theorem contra_L3 {c g Q : ℕ} (hc : c ≤ 25920) (hg : g ≤ 3)
    (h : c * g = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) (hQ : 7 ≤ Q) : False := by
  have h1 := Nat.mul_le_mul hc hg
  have h2 := L3_size_ge hQ
  linarith

private theorem contra_U3 {c g Q : ℕ} (hc : c ≤ 25920) (hg : g ≤ 3)
    (h : c * g = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1))) (hQ : 5 ≤ Q) : False := by
  have h1 := Nat.mul_le_mul hc hg
  have h2 := U3_size_ge hQ
  linarith

private theorem chev2_alt7 : ¬ IsChevSimple 2 (alternatingGroup (Fin 7)) := by
  intro hC
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · simp [onLie] at hP
    · exact alt7_not_iso_lie d e'
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by simpa [ambiguousChev] using hP
      have h1 := Nat.card_congr e'.toEquiv
      have h2 := card_alt_eq 7 (by norm_num)
      have h3 := card_alt_eq n (by omega)
      have := fv7
      have := fv5
      have := fv6
      have := fv8
      rcases hn' with rfl | rfl | rfl <;> omega
    · exact alt7_not_iso_lie d e'
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

private theorem chev2_alt_ge9 {m : ℕ} (hm : 9 ≤ m) :
    ¬ IsChevSimple 2 (alternatingGroup (Fin m)) := by
  intro hC
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · simp [onLie] at hP
    · exact alt_not_iso_lie hm d e'
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by simpa [ambiguousChev] using hP
      have h1 := Nat.card_congr e'.toEquiv
      have h2 := card_alt_mono 9 m (by norm_num) hm
      have h3 := card_alt_eq n (by omega)
      have := fv9
      have := fv5
      have := fv6
      have := fv8
      rcases hn' with rfl | rfl | rfl <;> omega
    · exact alt_not_iso_lie hm d e'
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

private theorem rank_of_k3 {p r : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A r q).Valid}
    (hi : k3 p (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩)) :
    r = 2 ∧ q.card % 6 = 1 := by
  rcases r with _ | _ | _ | r
  · simp [k3, k3Lie] at hi
  · simp [k3, k3Lie] at hi
  · simp [k3, k3Lie] at hi
    exact ⟨rfl, by simpa [TauCeti.PrimePower.card_def] using hi.2⟩
  · simp [k3, k3Lie] at hi

private theorem rank_of_k3_tA {p r : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA r q).Valid}
    (hi : k3 p (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩)) :
    r = 2 ∧ q.card % 6 = 5 := by
  rcases r with _ | _ | _ | r
  · simp [k3, k3Lie] at hi
  · simp [k3, k3Lie] at hi
  · simp [k3, k3Lie] at hi
    exact ⟨rfl, by simpa [TauCeti.PrimePower.card_def] using hi.2⟩
  · simp [k3, k3Lie] at hi

private theorem chev2_L3 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (h6 : q.card % 6 = 1)
    (hC : IsChevSimple 2 (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩).Group) :
    False := by
  have hq2 : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' _)
  have hq7 : 7 ≤ q.card := by omega
  have hY : CFSG.Blueprint.LieModel
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩).Group
      CFSG.Open.StatedLieTag.PSL 3 q.p q.exponent :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.Models.lieModel_A 2 q hv (MulEquiv.refl _))
  have hp2 : q.p ≠ 2 := by
    intro hp
    have hdvd : 2 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hp]
      exact dvd_pow_self 2 q.exponent_pos.ne'
    omega
  have hodd : CFSG.Blueprint.OddLieType
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩).Group :=
    ⟨CFSG.Open.StatedLieTag.PSL, 3, q.p, q.exponent, q.prime_p, hp2,
      CFSG.Blueprint.LieModel.admissible hY, hY⟩
  have hordY := (hOrd _ _ 3 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
  rw [← TauCeti.PrimePower.card_def q, divisor_PSL3, numer_PSL3] at hordY
  have hg : Nat.gcd 3 (q.card - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p', hp', hP, -⟩
    · simp [onLie] at hP
    · have hc2 : d.1.characteristic = 2 := by simpa [onLie] using hP
      obtain ⟨t, n, f, hL⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hc2 e'
      by_cases hex : (t = CFSG.Open.StatedLieTag.PSL ∧ n = 2 ∧ f = 2) ∨
          (t = CFSG.Open.StatedLieTag.PSL ∧ n = 3 ∧ f = 1) ∨
          (t = CFSG.Open.StatedLieTag.PSU ∧ n = 4 ∧ f = 1)
      · have hord2 := (hOrd _ t n 2 f (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
        rcases hex with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · rw [divisor_PSL2, numer_PSL2] at hord2
          norm_num at hord2
          exact contra_L3 (by omega) hg hordY hq7
        · rw [divisor_PSL3, numer_PSL3] at hord2
          norm_num at hord2
          exact contra_L3 (by omega) hg hordY hq7
        · have e1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor
              CFSG.Open.StatedLieTag.PSU 4 (2 ^ 1) = 1 := by decide
          have e2 : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator
              CFSG.Open.StatedLieTag.PSU 4 (2 ^ 1) = 25920 := by decide
          rw [e1, e2] at hord2
          exact contra_L3 (by omega) hg hordY hq7
      · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hOrd hL
          (fun h' => hex (Or.inl h')) (fun h' => hex (Or.inr (Or.inl h')))
          (fun h' => hex (Or.inr (Or.inr h'))) hodd
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p', hp', hP, -⟩
    · have hc := card_ambig2_alt hn hP e'
      exact contra_L3 (by omega) hg hordY hq7
    · have hc := card_ambig2_lie d hP e'
      exact contra_L3 (by omega) hg hordY hq7
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

private theorem chev2_U3 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (h6 : q.card % 6 = 5)
    (hC : IsChevSimple 2 (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group) :
    False := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have h3 : 3 ≤ q.card := hr.2 rfl
  have hq5 : 5 ≤ q.card := by omega
  have hY : CFSG.Blueprint.LieModel
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group
      CFSG.Open.StatedLieTag.PSU 3 q.p q.exponent :=
    lieModel_twistedA2 q hv (MulEquiv.refl _)
  have hp2 : q.p ≠ 2 := by
    intro hp
    have hdvd : 2 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hp]
      exact dvd_pow_self 2 q.exponent_pos.ne'
    omega
  have hodd : CFSG.Blueprint.OddLieType
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group :=
    ⟨CFSG.Open.StatedLieTag.PSU, 3, q.p, q.exponent, q.prime_p, hp2,
      CFSG.Blueprint.LieModel.admissible hY, hY⟩
  have hordY := (hOrd _ _ 3 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
  rw [← TauCeti.PrimePower.card_def q, divisor_PSU3, numer_PSU3] at hordY
  have hg : Nat.gcd 3 (q.card + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p', hp', hP, -⟩
    · simp [onLie] at hP
    · have hc2 : d.1.characteristic = 2 := by simpa [onLie] using hP
      obtain ⟨t, n, f, hL⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hc2 e'
      by_cases hex : (t = CFSG.Open.StatedLieTag.PSL ∧ n = 2 ∧ f = 2) ∨
          (t = CFSG.Open.StatedLieTag.PSL ∧ n = 3 ∧ f = 1) ∨
          (t = CFSG.Open.StatedLieTag.PSU ∧ n = 4 ∧ f = 1)
      · have hord2 := (hOrd _ t n 2 f (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
        rcases hex with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · rw [divisor_PSL2, numer_PSL2] at hord2
          norm_num at hord2
          exact contra_U3 (by omega) hg hordY hq5
        · rw [divisor_PSL3, numer_PSL3] at hord2
          norm_num at hord2
          exact contra_U3 (by omega) hg hordY hq5
        · have e1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor
              CFSG.Open.StatedLieTag.PSU 4 (2 ^ 1) = 1 := by decide
          have e2 : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator
              CFSG.Open.StatedLieTag.PSU 4 (2 ^ 1) = 25920 := by decide
          rw [e1, e2] at hord2
          exact contra_U3 (by omega) hg hordY hq5
      · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hOrd hL
          (fun h' => hex (Or.inl h')) (fun h' => hex (Or.inr (Or.inl h')))
          (fun h' => hex (Or.inr (Or.inr h'))) hodd
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s, hP, -⟩ |
      ⟨p', hp', hP, -⟩
    · have hc := card_ambig2_alt hn hP e'
      exact contra_U3 (by omega) hg hordY hq5
    · have hc := card_ambig2_lie d hP e'
      exact contra_U3 (by omega) hg hordY hq5
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

private theorem not_lie2_card_95040 {X : Type} [Group X] {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n 2 f) (hX : CFSG.Blueprint.LieModel X t n 2 f)
    (hc : Nat.card X = 95040) : False := by
  have hN : ¬ 2 ^ (6 + 1) ∣ Nat.card X := by
    rw [hc]
    norm_num
  obtain ⟨hb, hord⟩ := CFSG.ComponentClassification.CatLeaf.lie_bounds hOrd hadm hX (v := 6) hN
  rw [hc] at hord
  have hf : 1 ≤ f := hadm.2.1
  rcases CFSG.ComponentClassification.CatLeaf.lie_casework hadm (by omega) with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · rcases ht with rfl | rfl <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hb <;>
      interval_cases f <;> norm_num at hb <;> revert hord <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
        CFSG.ComponentClassification.CatLeaf.lieOrderDivisor] <;> decide

private theorem not_lie2_card_443520 {X : Type} [Group X] {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n 2 f) (hX : CFSG.Blueprint.LieModel X t n 2 f)
    (hc : Nat.card X = 443520) : False := by
  have hN : ¬ 2 ^ (7 + 1) ∣ Nat.card X := by
    rw [hc]
    norm_num
  obtain ⟨hb, hord⟩ := CFSG.ComponentClassification.CatLeaf.lie_bounds hOrd hadm hX (v := 7) hN
  rw [hc] at hord
  have hf : 1 ≤ f := hadm.2.1
  rcases CFSG.ComponentClassification.CatLeaf.lie_casework hadm (by omega) with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · rcases ht with rfl | rfl <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hb <;>
      interval_cases f <;> norm_num at hb <;> revert hord <;>
      simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
        CFSG.ComponentClassification.CatLeaf.lieOrderDivisor] <;> decide

private theorem chev2_spor (s : TauCeti.SporadicName) (hs : s = .M12 ∨ s = .M22) :
    ¬ IsChevSimple 2 (TauCeti.CFSGIndex.sporadic s).Group := by
  intro hC
  have hcard : Nat.card (TauCeti.CFSGIndex.sporadic s).Group = 95040 ∨
      Nat.card (TauCeti.CFSGIndex.sporadic s).Group = 443520 := by
    rw [card_spor]
    rcases hs with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  unfold IsChevSimple at hC
  rcases hC with h | h
  · rcases catalogIs_split h with ⟨n, hn, hP, -⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s', hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · simp [onLie] at hP
    · have hc2 : d.1.characteristic = 2 := by simpa [onLie] using hP
      obtain ⟨t, n, f, hL⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hc2 e'
      have hadm := CFSG.Blueprint.LieModel.admissible hL
      rcases hcard with hc | hc
      · exact not_lie2_card_95040 hadm hL hc
      · exact not_lie2_card_443520 hadm hL hc
    · simp [onLie] at hP
    · simp [onLie] at hP
  · rcases catalogIs_split h with ⟨n, hn, hP, ⟨e'⟩⟩ | ⟨d, hP, ⟨e'⟩⟩ | ⟨s', hP, -⟩ |
      ⟨p, hp, hP, -⟩
    · have hc := card_ambig2_alt hn hP e'
      omega
    · have hc := card_ambig2_lie d hP e'
      omega
    · simp [ambiguousChev] at hP
    · simp [ambiguousChev] at hP

theorem k3NotChev2At_holds : K3NotChev2At := by
  intro p Q _ hK hC
  obtain ⟨i, hi, ⟨e⟩⟩ := k3Cover_imp_catalogIs hK
  have hC' := (CFSG.LocalAnalysis.GLTheoremA.S9.isChevSimple_congr e).1 hC
  cases i with
  | cyclic p' hp' => simp [k3] at hi
  | alternating n hn =>
    have hi' : n = 7 ∨ n = 10 := by simpa [k3] using hi.2
    rcases hi' with rfl | rfl
    · exact chev2_alt7 hC'
    · exact chev2_alt_ge9 (by norm_num) hC'
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A r q =>
      obtain ⟨rfl, h6⟩ := rank_of_k3 hi
      exact chev2_L3 q hv h6 hC'
    | twistedA r q =>
      obtain ⟨rfl, h6⟩ := rank_of_k3_tA hi
      exact chev2_U3 q hv h6 hC'
    | _ => simp [k3, k3Lie] at hi
  | sporadic s =>
    have hs : s = .M12 ∨ s = .M22 := by simpa [k3] using hi.2
    exact chev2_spor s hs hC'

end CFSG.LocalAnalysis.GLTheoremA
