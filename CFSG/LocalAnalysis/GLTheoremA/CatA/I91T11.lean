module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement


theorem catalogIs_isSp4eight_of_lieModel {R : Type} [Group R] (h : CFSG.Blueprint.LieModel R .PSp 2 2 3) :
    catalogIs R S9.isSp4eight := by
  rcases h with ⟨-, hS⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact catalogIs_isSp4eight_of_statedPSp hS
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem marked_eq_L3 {lab : LargeEvenLabel} {R : Type} [Group R] {m : ℕ} (hM : MarkedModel lab R)
    (ht : lab.tag = .A) (hr : lab.rank = 2) (hn : lab.n = m) : CFSG.Blueprint.LieModel R .PSL 3 2 m := by
  have hM2 := hM
  unfold MarkedModel at hM2
  have e1 : markTag lab = .PSL := by simp [markTag, ht]
  have e2 : markRank lab = 3 := by simp [markRank, ht, hr]
  have e3 : markChar lab = 2 := by simp [markChar, ht]
  have e4 : markDeg lab = m := by simp [markDeg, ht, hn]
  rw [e1, e2, e3, e4] at hM2
  exact hM2

theorem marked_eq_U3 {lab : LargeEvenLabel} {R : Type} [Group R] {m : ℕ} (hM : MarkedModel lab R)
    (ht : lab.tag = .twA) (hr : lab.rank = 2) (hn : lab.n = m) : CFSG.Blueprint.LieModel R .PSU 3 2 m := by
  have hM2 := hM
  unfold MarkedModel at hM2
  have e1 : markTag lab = .PSU := by simp [markTag, ht]
  have e2 : markRank lab = 3 := by simp [markRank, ht, hr]
  have e3 : markChar lab = 2 := by simp [markChar, ht]
  have e4 : markDeg lab = m := by simp [markDeg, ht, hn]
  rw [e1, e2, e3, e4] at hM2
  exact hM2

theorem marked_eq_Sp {lab : LargeEvenLabel} {R : Type} [Group R] {m : ℕ} (hM : MarkedModel lab R)
    (ht : lab.tag = .B) (hr : lab.rank = 2) (hn : lab.n = m) : CFSG.Blueprint.LieModel R .PSp 2 2 m := by
  have hM2 := hM
  unfold MarkedModel at hM2
  have e1 : markTag lab = .PSp := by simp [markTag, ht]
  have e2 : markRank lab = 2 := by simp [markRank, ht, hr]
  have e3 : markChar lab = 2 := by simp [markChar, ht]
  have e4 : markDeg lab = m := by simp [markDeg, ht, hn]
  rw [e1, e2, e3, e4] at hM2
  exact hM2

theorem twoPart_card_fixSub_eq {S : Type} [Group S] [Finite S] {β : MulAut S} {D : Subgroup S}
    (hD : FR.SubfieldGrp β D) : twoPart (Nat.card ↥(FP.fixSub β)) = twoPart (Nat.card ↥D) := by
  have hCD : Nat.card ↥(FP.fixSub β) = D.relIndex (FP.fixSub β) * Nat.card ↥D := by
    have := Subgroup.relIndex_mul_card (H := D) (K := FP.fixSub β)
    rw [inf_eq_left.2 hD.1] at this
    exact this.symm
  rw [hCD]
  exact FP.twoPart_mul_odd hD.2.2 Nat.card_pos.ne'

theorem twoPart_12096 : twoPart 12096 = 64 := by
  have h : (12096 : ℕ) = 189 * 2 ^ 6 := by norm_num
  rw [h, FP.twoPart_mul_odd (by decide) (by positivity), CFSG.LocalAnalysis.GLTheoremA.I91T.twoPart_pow_two]
  norm_num

theorem twoPart_17971200 : twoPart 17971200 = 2048 := by
  have h : (17971200 : ℕ) = 8775 * 2 ^ 11 := by norm_num
  rw [h, FP.twoPart_mul_odd (by decide) (by positivity), CFSG.LocalAnalysis.GLTheoremA.I91T.twoPart_pow_two]
  norm_num

theorem twoPart_35942400 : twoPart 35942400 = 4096 := by
  have h : (35942400 : ℕ) = 8775 * 2 ^ 12 := by norm_num
  rw [h, FP.twoPart_mul_odd (by decide) (by positivity), CFSG.LocalAnalysis.GLTheoremA.I91T.twoPart_pow_two]
  norm_num

theorem exc_fieldOn (G : Type) [Group G] [Finite G] (hcls : ExcChev2Class) (hA6 : A6NoChar2Lambda)
    (X L : Subgroup G) (b : G) (hL : GLAPComponent 3 X L) (hchev : IsChevSimple 2 (PSimple 3 L))
    (hbp : b ^ 3 = 1) (hF : FieldOn 3 b L)
    (hI : GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b)) (hIne : Ipart 3 L b ≠ ⊥)
    (hexc : catalogIs (PSimple 3 (Ipart 3 L b)) excIndex) :
    catalogIs (PSimple 3 L) (fun i => S9.isSp4eight i ∨ S9.isL3char2 i ∨ S9.isU3char2 i) := by
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hF.1
  have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  have hcompT := glaPComponent_chevTransfer hp3 hb hap hI
  have hTC : chevTransfer 3 L (Ipart 3 L b) ≤ FP.fixSub (indAut 3 L b hb) := by
    rw [FR.fixSub_indAut hb]
    exact hcompT.1
  have hcomp' : GLAPComponent 3 (FP.fixSub (indAut 3 L b hb)) (chevTransfer 3 L (Ipart 3 L b)) := by
    rw [FR.fixSub_indAut hb]
    exact hcompT
  have hTperf : ⁅chevTransfer 3 L (Ipart 3 L b), chevTransfer 3 L (Ipart 3 L b)⁆ =
      chevTransfer 3 L (Ipart 3 L b) := glaPComponent_perfect hcompT
  have hTne : chevTransfer 3 L (Ipart 3 L b) ≠ ⊥ := glaPComponent_ne_bot' hcompT
  have hchI : IsChevSimple 2 (PSimple 3 (Ipart 3 L b)) :=
    (FR.i91CompAt_holds (G := G) hp3 hp2 X L b hL hchev hbp (Or.inl hF) hIne).2
  have hcl := hcls (PSimple 3 (Ipart 3 L b)) hexc hchI
  obtain ⟨lab, hlab, h3', hM, hpn, D, hD, hdat⟩ := FR.fieldOn_subfield hp3 hp2 hF
  have hTD : chevTransfer 3 L (Ipart 3 L b) ≤ D :=
    hTperf ▸ (Subgroup.commutator_mono hTC hTC).trans hD.2.1
  have hna : ∃ x y : ↥D, x * y ≠ y * x := FR.exists_noncomm_of_perfect hTD hTperf hTne
  obtain ⟨E, hEC, hEs, hEna, hEperf, h2part, -⟩ :=
    FR.coreSub_of_fieldOn hp3 hp2 FR.Res.smallDatum_holds (FR.Res.twF4Core_holds hp3 hp2) hF
      ⟨chevTransfer 3 L (Ipart 3 L b), hTC, hTperf, hTne⟩
  have hTE : chevTransfer 3 L (Ipart 3 L b) = E := FR.eq_core_of_glaPComponent hEs hEC hEperf hcomp'
  obtain ⟨e⟩ := pSimple_component_equiv hp3 hb hbp hEs hEC hEna hEperf hI
  have hcardI : Nat.card (PSimple 3 (Ipart 3 L b)) = Nat.card E := Nat.card_congr e.toEquiv
  have hEleD : Nat.card E ≤ Nat.card D := Subgroup.card_le_of_le (hTE ▸ hTD)
  have hEleC : Nat.card E ≤ Nat.card (FP.fixSub (indAut 3 L b hb)) := Subgroup.card_le_of_le hEC
  have h2C : twoPart (Nat.card (FP.fixSub (indAut 3 L b hb))) ≤ 2 * twoPart (Nat.card E) := h2part
  have h2D : twoPart (Nat.card (FP.fixSub (indAut 3 L b hb))) = twoPart (Nat.card D) :=
    twoPart_card_fixSub_eq hD
  rcases hdat with hdatum | hexc'
  · by_cases hΛ : LargeEvenInLambda2 (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel)
    ·
      have hG' : (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel).tag ≠ .G2der := by
        intro h
        have h1 : lab.n = 1 := by
          have hl := hlab
          unfold LargeEvenInLambda2 at hl
          rw [show lab.tag = .G2der from h] at hl
          exact hl.2.2
        omega
      obtain ⟨hDs, hMD⟩ := simple_of_datum hΛ hG' hna hdatum
      have hDleE : D ≤ E := hEperf D hD.1 (perfect_of_simple_sub hDs hna)
      have hEleD' : E ≤ D := hTE ▸ hTD
      have hDE : D = E := le_antisymm hDleE hEleD'
      have e' : PSimple 3 (Ipart 3 L b) ≃* ↥D := by
        rw [hDE]
        exact e
      have hcl' : catalogIs D isA6 ∨ (∃ k, 2 ≤ k ∧ Even k ∧ catalogIs D (isA2n k)) ∨
          (∃ k, 5 ≤ k ∧ Odd k ∧ catalogIs D (isU3n k)) := by
        rcases hcl with h | h | h
        · exact Or.inl ((catalogIs_congr e').mp h)
        · obtain ⟨k, hk2, hke, hk⟩ := h
          exact Or.inr (Or.inl ⟨k, hk2, hke, (catalogIs_congr e').mp hk⟩)
        · obtain ⟨k, hk5, hko, hk⟩ := h
          exact Or.inr (Or.inr ⟨k, hk5, hko, (catalogIs_congr e').mp hk⟩)
      have hch2 : markChar (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel) = 2 :=
        markChar_two_of_lambda hlab hpn
      rcases hcl' with hA6c | ⟨k, hk2, hke, hkc⟩ | ⟨k, hk5, hko, hkc⟩
      · exact (hA6 _ D hΛ hch2 hMD hA6c).elim
      · have hX := lieModel_of_catalogIs_isA2n hkc
        obtain ⟨ht, hr, hn⟩ := label_of_markedModel_L3 hk2 hMD hX
        have ht' : lab.tag = .A := ht
        have hr' : lab.rank = 2 := hr
        have hn' : lab.n = 3 * k := by
          have : lab.n / 3 = k := hn
          omega
        have hML := marked_eq_L3 hM ht' hr' hn'
        have hke' : k % 2 = 0 := Nat.even_iff.1 hke
        exact catalogIs_imp (fun _ h => Or.inr (Or.inl h))
          (catalogIs_isL3char2_of_lieModel (by omega) (Nat.even_iff.2 (by omega)) hML)
      · have hX := lieModel_of_catalogIs_isU3n hkc
        obtain ⟨ht, hr, hn⟩ := label_of_markedModel_U3 hMD hX
        have ht' : lab.tag = .twA := ht
        have hr' : lab.rank = 2 := hr
        have hn' : lab.n = 3 * k := by
          have : lab.n / 3 = k := hn
          omega
        have hML := marked_eq_U3 hM ht' hr' hn'
        have hko' : k % 2 = 1 := Nat.odd_iff.1 hko
        exact catalogIs_imp (fun _ h => Or.inr (Or.inr h))
          (catalogIs_isU3char2_of_lieModel (by omega) (Nat.odd_iff.2 (by omega)) hML)
    ·
      rcases small_datum_cases lab D hlab hpn hΛ hdatum with
        hsol | ⟨hn1, hBC, hrk, hcard⟩ | ⟨hn1, hG2, hcard⟩ | ⟨hn1, hTF, hcard⟩
      · exact (FR.false_of_perfect_solvable hTD hTperf hTne hsol).elim
      ·
        have hn3 : lab.n = 3 := by omega
        have hML : CFSG.Blueprint.LieModel (PSimple 3 L) .PSp 2 2 3 := by
          rcases hBC with ht | ht
          · exact marked_eq_Sp hM ht hrk hn3
          · have hM2 := hM
            unfold MarkedModel at hM2
            have e1 : markTag lab = .PSp := by simp [markTag, ht]
            have e2 : markRank lab = 2 := by simp [markRank, ht, hrk]
            have e3 : markChar lab = 2 := by simp [markChar, ht]
            have e4 : markDeg lab = 3 := by simp [markDeg, ht, hn3]
            rw [e1, e2, e3, e4] at hM2
            exact hM2
        exact catalogIs_imp (fun _ h => Or.inl h) (catalogIs_isSp4eight_of_lieModel hML)
      ·
        have hD12 : twoPart (Nat.card D) = 64 := by rw [hcard]; exact twoPart_12096
        have hN : 32 ≤ twoPart (Nat.card (PSimple 3 (Ipart 3 L b))) := by
          rw [hcardI]
          have := h2C
          rw [h2D, hD12] at this
          omega
        have hM' : Nat.card (PSimple 3 (Ipart 3 L b)) ≤ 12096 := by
          rw [hcardI]
          rw [hcard] at hEleD
          exact hEleD
        exact (excClass_contra hcl hM' (by norm_num) hN (fun _ => by norm_num)
          (fun h => by norm_num at h)).elim
      ·
        have hD12 : twoPart (Nat.card D) = 2048 := by rw [hcard]; exact twoPart_17971200
        have hN : 1024 ≤ twoPart (Nat.card (PSimple 3 (Ipart 3 L b))) := by
          rw [hcardI]
          have := h2C
          rw [h2D, hD12] at this
          omega
        have hM' : Nat.card (PSimple 3 (Ipart 3 L b)) ≤ 17971200 := by
          rw [hcardI]
          rw [hcard] at hEleD
          exact hEleD
        exact (excClass_contra hcl hM' (by norm_num) hN (fun _ => by norm_num)
          (fun _ => by norm_num)).elim
  ·
    rcases hexc' with ⟨h1, h2, hsol⟩ | ⟨h1, h2⟩
    · exact (FR.false_of_perfect_solvable hTD hTperf hTne hsol).elim
    · have hC := twF4CentOrder_holds G L b hF lab h1 h2 hM
      have hD12 : twoPart (Nat.card (FP.fixSub (indAut 3 L b hb))) = 4096 := by
        rw [hC]
        exact twoPart_35942400
      have hN : 2048 ≤ twoPart (Nat.card (PSimple 3 (Ipart 3 L b))) := by
        rw [hcardI]
        have := h2C
        rw [hD12] at this
        omega
      have hM' : Nat.card (PSimple 3 (Ipart 3 L b)) ≤ 35942400 := by
        rw [hcardI]
        rw [hC] at hEleC
        exact hEleC
      exact (excClass_contra hcl hM' le_rfl hN (fun _ => by norm_num)
        (fun _ => by norm_num)).elim

end I91T


end CFSG.LocalAnalysis.GLTheoremA
