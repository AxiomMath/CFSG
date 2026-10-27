module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ALayer
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovBasic
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911ATL
public import CFSG.LocalAnalysis.GLTheoremA.CatB.L2CentBridge
public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ClassicalModels CFSG.Assembly.LowTwoRank

local notation "fixS" => CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub

theorem l2c_mem_fixSub {Y : Type} [Group Y] {α : MulAut Y} {y : Y} :
    y ∈ fixS α ↔ α y = y := Iff.rfl

theorem l2c_pow_two_of_cube {c n : ℕ} (h : c ^ 3 = 2 ^ n) : ∃ k, c = 2 ^ k ∧ 3 * k = n := by
  have hd : c ∣ 2 ^ n := by rw [← h]; exact dvd_pow_self c (by norm_num)
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  refine ⟨k, rfl, ?_⟩
  have h2 : 2 ^ (k * 3) = 2 ^ n := by rw [pow_mul]; exact h
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

theorem l2c_two_pow_ne_nine {n : ℕ} (hn : 1 ≤ n) : 2 ^ n ≠ 9 := by
  intro h
  have h2d : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  rw [h] at h2d
  norm_num at h2d

theorem l2c_solvable_two {F₀ : Type} [Field F₀] [Finite F₀] (hF : Nat.card F₀ = 2 ^ 1) :
    Group.IsSolvable (StatedProj (StatedSL 2 F₀)) := by
  have hcard1 : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by norm_num)
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 2 ^ 1 * 3 ^ 1 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard1]
    norm_num
  have hsl := CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_card_two_three hc
  haveI := hsl
  have hpsl : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1)) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (Subgroup.center _)) (QuotientGroup.mk'_surjective _)
  haveI := hpsl
  have e := statedLinearModelEquivGaloisPSL F₀ 2 2 1 (by norm_num) hF
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem l2c_pSimple_iso {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 S)) (hs : IsSimpleGroup (PQuot 3 S)) :
    Nonempty (PSimple 3 S ≃* PQuot 3 S) := by
  have hcen : Subgroup.center (PQuot 3 S) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 S)) with h | h
    · exact h
    · exfalso
      haveI := hq.2
      have hnt : Nontrivial (PQuot 3 S ⧸ Subgroup.center (PQuot 3 S)) := inferInstance
      rw [h] at hnt
      haveI : Subsingleton (PQuot 3 S ⧸ (⊤ : Subgroup (PQuot 3 S))) :=
        QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton _ this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot⟩

theorem l2c_nontrivial_pQuot {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 X)) : Nontrivial (PQuot 3 X) :=
  CFSG.LocalCores.isQuasisimple_nontrivial (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)

theorem l2c_ne_bot_of_comp {G : Type} [Group G] [Finite G] {X S : Subgroup G}
    (hS : GLAPComponent 3 X S) : S ≠ ⊥ := by
  intro h
  subst h
  haveI := l2c_nontrivial_pQuot (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hS)
  have : Subsingleton (PQuot 3 (⊥ : Subgroup G)) := by unfold PQuot; infer_instance
  exact not_subsingleton _ this

theorem l2c_core_ne_top {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 X)) (h : GLAPPrimeCore 3 ↥X = ⊤) : False := by
  haveI := l2c_nontrivial_pQuot hq
  have hnt : Nontrivial (↥X ⧸ GLAPPrimeCore 3 ↥X) := inferInstance
  rw [h] at hnt
  haveI : Subsingleton (↥X ⧸ (⊤ : Subgroup ↥X)) := QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ this

theorem l2c_field_case (h0 : L2CentreThree) (h1 : L2Aut3Classification) (h2 : L2FieldFixed)
    {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q) (hO : GLAPPrimeCore 3 Q = ⊥)
    {n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 2 F))
    {a : MulAut Q} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {S : Subgroup Q}
    (hS : GLAPComponent 3 (fixS a) S) :
    ∃ (k : ℕ) (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), 2 ≤ k ∧ Nat.card F₀ = 2 ^ k ∧
      Nonempty (PSimple 3 S ≃* StatedProj (StatedSL 2 F₀)) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hF9 : Nat.card F ≠ 9 := by rw [hF]; exact l2c_two_pow_ne_nine hn
  have hZ : Subgroup.center Q = ⊥ := by
    by_contra hne
    exact hF9 (h0 Q hQ (isPGroup_center_of_core_eq_bot hO) hne F ⟨e⟩)
  let eZ : (Q ⧸ Subgroup.center Q) ≃* Q := (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let θ : Q ≃* StatedProj (StatedSL 2 F) := eZ.symm.trans e
  let β : MulAut (StatedProj (StatedSL 2 F)) := MulAut.congr θ a
  have hβ3 : β ^ 3 = 1 := by
    show MulAut.congr θ a ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply ha1
    apply (MulAut.congr θ).injective
    rw [map_one]
    exact h
  have hfix : fixS β = (fixS a).map θ.toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hy' : β y = y := (l2c_mem_fixSub).1 hy
      refine Subgroup.mem_map.2 ⟨θ.symm y, (l2c_mem_fixSub).2 ?_, by simp⟩
      apply θ.injective
      have hβy : β y = θ (a (θ.symm y)) := by
        show MulAut.congr θ a y = _
        simp [MulAut.congr_apply]
      rw [hβy] at hy'
      simpa using hy'
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
      rw [l2c_mem_fixSub]
      show θ (a (θ.symm (θ q))) = θ q
      rw [θ.symm_apply_apply, (l2c_mem_fixSub).1 hq]
  let ψ₀ : fixS a ≃* fixS β :=
    (θ.subgroupMap (fixS a)).trans (MulEquiv.subgroupCongr hfix.symm)
  have hcontra : Group.IsSolvable (fixS β) → False := fun hs => by
    haveI : Group.IsSolvable (fixS a) :=
      Group.isSolvable_of_surjective (f := ψ₀.symm.toMonoidHom) ψ₀.symm.surjective
    exact CFSG.HardMathSupport.Dickson.KD.false_of_glaPComponent_of_solvable hS inferInstance
  rcases h1 F β hβ3 with hb | hsol | ⟨σ, φ, γ, hφ, hβγ⟩
  · exact (hβ1 hb).elim
  · exact (hcontra hsol).elim
  obtain ⟨F₀, hF₀f, hF₀fin, hcube, ⟨ψ⟩⟩ := h2 F β hβ3 hβ1 σ φ γ hφ hβγ
  have hcube' : (Nat.card F₀) ^ 3 = 2 ^ n := by rw [← hF, hcube]
  obtain ⟨k, hk, -⟩ := l2c_pow_two_of_cube hcube'
  have hF₀nt : 1 < Nat.card F₀ := Finite.one_lt_card
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp at hk; omega
    ·
      have hT : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) := l2c_solvable_two (by rw [hk])
      haveI := hT
      exact (hcontra (Group.isSolvable_of_surjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective)).elim
  have hT4 : 4 ≤ Nat.card F₀ := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  let τ : fixS a ≃* StatedProj (StatedSL 2 F₀) := ψ₀.trans ψ
  have hTs : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) :=
    (MulEquiv.isSimpleGroup_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F₀)).1
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hT4)
  have hSimpFix : IsSimpleGroup ↥(fixS a) := (MulEquiv.isSimpleGroup_congr τ).2 hTs
  rcases eq_bot_or_eq_of_isSubnormal_of_simple hSimpFix hS.2.1 with hb | hSeq
  · exact (l2c_ne_bot_of_comp hS hb).elim
  subst hSeq
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥(fixS a)) with hO' | hO'
  · let eQ : PQuot 3 (fixS a) ≃* ↥(fixS a) :=
      (QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot
    have hsPQ : IsSimpleGroup (PQuot 3 (fixS a)) := (MulEquiv.isSimpleGroup_congr (eQ.trans τ)).2 hTs
    obtain ⟨φ⟩ := l2c_pSimple_iso hq hsPQ
    exact ⟨k, F₀, hF₀f, hF₀fin, hk2, hk, ⟨φ.trans (eQ.trans τ)⟩⟩
  · exact (l2c_core_ne_top hq hO').elim

end CFSG.LocalAnalysis.GLTheoremA
