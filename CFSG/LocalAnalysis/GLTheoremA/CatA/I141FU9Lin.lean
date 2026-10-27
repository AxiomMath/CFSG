module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinU64
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamLin InnDiagKind)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

theorem u9_card_psl_ne_u38 {a m : ℕ} {E : Type} [Field E] [Finite E] (ha : 2 ≤ a)
    (hE : Nat.card E = 2 ^ m) : Nat.card (StatedProj (StatedSL a E)) ≠ 5515776 := by
  have h : Nat.card (StatedProj (StatedSL a E)) = ordA (a - 1) (Nat.card E) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega), ordA,
      Nat.sub_add_cancel (by omega : 1 ≤ a), mul_comm (a - 1) a]
  rw [h]
  exact CFSG.AGLEmbedding.ordA_ne_u38 hE

theorem u9_lin_pSimple {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamLin labK) (hin : InnDiagKind S labK α)
    (hα3 : α ^ 3 = 1) {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    ∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ m ∧
      Nonempty (PSimple 3 J ≃* StatedProj (StatedSL a E)) := by
  obtain ⟨K, hK, hKf, d, hd, hcard, A, u, e, hαu, hgraph⟩ := innDiag_linear_data hcen hFam hin
  have h2 : (2 : K) = 0 := two_eq_zero_of_natCard_pow hcard
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ 3 = 1 := by
    rw [← hMEq, ← map_pow, hα3, map_one]
  haveI : Finite (LargeEvenProj (StatedSL d K)) := Finite.of_equiv S e.toEquiv
  obtain ⟨hJ', ⟨eJ⟩⟩ := chevQ_transport Nat.prime_three e hJ
  rw [hMEq] at hJ'
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ⟩⟩ :=
    pComponent_psl_fixed CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
      LinPCompIsComp_holds h2 hd A Nat.prime_three (by norm_num) u hgraph hpow _ hJ'
  have hEcard : Nat.card E = 2 ^ ((canonLabel labK).n * Module.finrank K E) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hcard, ← pow_mul]
  refine ⟨a, _, E, hEf, hEfin, ha, hEcard, ?_⟩
  haveI hperf : Group.IsPerfect ↥(J.map e.toMonoidHom) :=
    Subgroup.isPerfect_iff.2 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ')
  haveI hperfQ : Group.IsPerfect (↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥(J.map e.toMonoidHom)))
      (QuotientGroup.mk'_surjective _)
  haveI hperfT : Group.IsPerfect (StatedProj (StatedSL a E)) :=
    Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
  have h22 : a ≠ 2 ∨ Nat.card E ≠ 2 := by
    by_contra hcon
    have ha2 : a = 2 := by
      by_contra h
      exact hcon (Or.inl h)
    have hE2 : Nat.card E = 2 := by
      by_contra h
      exact hcon (Or.inr h)
    subst ha2
    have hc6 := card_statedProj_statedSL_two_of_card_eq_two hE2
    haveI : Finite (StatedProj (StatedSL 2 E)) := Nat.finite_of_card_ne_zero (by rw [hc6]; norm_num)
    haveI : Nontrivial (StatedProj (StatedSL 2 E)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hc6]; norm_num)
    exact Group.IsPerfect.not_isSolvable (StatedProj (StatedSL 2 E))
      (CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1)
        (b := 1) Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc6]; norm_num))
  have h23 : a ≠ 2 ∨ Nat.card E ≠ 3 := by
    right
    obtain ⟨k, hk⟩ : ∃ k, (canonLabel labK).n * Module.finrank K E = k + 1 := by
      refine ⟨(canonLabel labK).n * Module.finrank K E - 1, ?_⟩
      have h1 : 2 ≤ Nat.card E := Finite.one_lt_card
      rw [hEcard] at h1
      have : (canonLabel labK).n * Module.finrank K E ≠ 0 := by
        intro h0
        rw [h0] at h1
        norm_num at h1
      omega
    rw [hEcard, hk, pow_succ]
    omega
  have hsimple : IsSimpleGroup (StatedProj (StatedSL a E)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL E ha h22 h23
  haveI := hsimple
  have hq : CFSG.Open.IsQuasisimple ↥(J.map e.toMonoidHom) :=
    ⟨Group.isPerfect_def.1 hperf, φ.isSimpleGroup⟩
  obtain ⟨eC⟩ := centerQuot_equiv_pSimple Nat.prime_three hJ' hq
  exact ⟨eJ.trans (eC.symm.trans φ)⟩

theorem u9_famLin_of_canonLabel {lab : GLALabel} {r m : ℕ} (h : canonLabel lab = ⟨.A, r, m⟩) :
    FamLin lab := by
  obtain ⟨tag, rank, n⟩ := lab
  unfold FamLin
  by_cases h3 : rank = 3 <;> by_cases h2 : rank = 2 <;>
    cases tag <;> simp_all [canonLabel]

end CFSG.LocalAnalysis.GLTheoremA.I141F
