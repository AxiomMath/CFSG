module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.NormalForm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Elements
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Struct
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Cyclic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Extraspecial
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Monomial
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.RElement
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.ThreeA6
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Small
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.PSLTwo
public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
public import CFSG.Adapters.StatedSLPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.Defs
public import CFSG.RankThree.PartOne.N1322.Mono

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.RepresentationTheory

private theorem natCast_ne_zero_of_prime {q n : ℕ} [Fact q.Prime] (hn : n.Prime) (hnq : n ≠ q) :
    (n : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => hnq ((Nat.prime_dvd_prime_iff_eq Fact.out hn).mp h).symm

private theorem five_le_of_mod_three {q : ℕ} [hq : Fact q.Prime] (hq3 : q % 3 = 1) : 5 ≤ q := by
  have hp := hq.out
  have := hp.two_le
  by_contra h
  push Not at h
  interval_cases q <;> first | omega | norm_num at hp

private theorem ne_bot_of_irr {F : Type} [Field F] {H : Subgroup (GL (Fin 3) F)}
    (hirr : IsIrreducibleMatrixRep H.subtype) : H ≠ ⊥ := by
  rintro rfl
  have hinv : ∀ (g : (⊥ : Subgroup (GL (Fin 3) F))) (w : Fin 3 → F),
      w ∈ Submodule.span F {(Pi.single (0 : Fin 3) 1 : Fin 3 → F)} →
      (((⊥ : Subgroup (GL (Fin 3) F)).subtype g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈
        Submodule.span F {(Pi.single (0 : Fin 3) 1 : Fin 3 → F)} := by
    intro g w hw
    rw [Subgroup.coe_subtype, Subgroup.mem_bot.1 g.2, Units.val_one, Matrix.one_mulVec]
    exact hw
  rcases hirr _ hinv with h | h
  · have h0 : (Pi.single (0 : Fin 3) 1 : Fin 3 → F) ∈
        Submodule.span F {(Pi.single (0 : Fin 3) 1 : Fin 3 → F)} :=
      Submodule.subset_span (Set.mem_singleton _)
    rw [h, Submodule.mem_bot] at h0
    simpa using congrFun h0 0
  · have h1 : (Pi.single (1 : Fin 3) 1 : Fin 3 → F) ∈
        Submodule.span F {(Pi.single (0 : Fin 3) 1 : Fin 3 → F)} := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    simpa using congrFun hc 1

private theorem isPerfect_gl_three_two : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl
  refine Group.IsPerfect.ofSurjective (f := SpecialLinearGroup.toGL) fun g => ?_
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = d at hu
    revert d; decide
  exact ⟨⟨g, hdet⟩, Units.ext rfl⟩

private theorem false_of_noElemSq {q : ℕ} [Fact q.Prime] {A : Subgroup (GL (Fin 3) (ZMod q))}
    (hA : IsElemModScalars 3 A) {ω μ : (ZMod q)ˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (ha : diagOmega ω ∈ A) (hb : cycMat μ ∈ A) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hn : ∀ g ∈ A, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    {T : Type*} [Group T] [Group.IsPerfect T] (e : H ≃* T) (hT : NoElemSq 3 T) : False := by
  have hH : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨E, hE, hc⟩ := exists_elemSq_mulAut hA hω hω3 ha hb hH (ne_bot_of_irr hirr) hn
  exact NoElemSq.of_mulEquiv e hT E hE (by rw [hc]; norm_num)

private theorem false_of_monomial {q : ℕ} [Fact q.Prime] (hq3 : q % 3 = 1)
    (hF2 : (2 : ZMod q) ≠ 0) (hF3 : (3 : ZMod q) ≠ 0) {A : Subgroup (GL (Fin 3) (ZMod q))}
    {ω μ : (ZMod q)ˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) (ha : diagOmega ω ∈ A)
    (hb : cycMat μ ∈ A) (hμ : μ = 1 ∨ ∀ ν : (ZMod q)ˣ, ν ^ 3 ≠ μ)
    (hmon : CFSG.RankThree.SubgroupLists.IsTransitiveMonomial
      (Subgroup.closure (fixSetThree 3 A) ⊔ A)) : False := by
  have hX : ∀ y ∈ fixSetThree 3 A, y ∈ Subgroup.closure (fixSetThree 3 A) ⊔ A :=
    fun y hy => Subgroup.mem_sup_left (Subgroup.subset_closure hy)
  rcases hμ with rfl | hμ
  · refine false_of_isTransitiveMonomial_of_fourier hF2 hF3 hω hω3 hmon
      (fun i => hX _ (diagSign_mem_fixSetThree hF2 Nat.prime_three (by norm_num) hω hω3 ha i))
      fun k => ?_
    obtain ⟨d, hd, hdk⟩ :=
      exists_fourierMat_mem_fixSetThree hF2 hF3 Nat.prime_three (by norm_num) hω hω3 hb k
    exact ⟨d, hX d hd, hdk⟩
  · obtain ⟨y, hy, r, hr, hr6, hyr, hno⟩ := exists_noEigen_mem_fixSetThree hq3 hμ hb
    exact false_of_isTransitiveMonomial_of_noEigen hmon (hX y hy) hr hr6 hyr hno

theorem closure_fixSetThree_of_normalForm (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    (hA6 : CFSG.RankThree.PartOne.N1322.KF1322ThreeA6Norm) {q : ℕ} [Fact q.Prime]
    (hq3 : q % 3 = 1) {A : Subgroup (GL (Fin 3) (ZMod q))} (hA : IsElemModScalars 3 A)
    {ω μ : (ZMod q)ˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) (ha : diagOmega ω ∈ A)
    (hb : cycMat μ ∈ A) (hμ : μ = 1 ∨ ∀ ν : (ZMod q)ˣ, ν ^ 3 ≠ μ) :
    Subgroup.closure (fixSetThree 3 A) = CFSG.Open.StatedSL 3 (ZMod q) := by
  have h5 := five_le_of_mod_three hq3
  have hF2 : (2 : ZMod q) ≠ 0 := by
    simpa using natCast_ne_zero_of_prime (q := q) Nat.prime_two (by omega)
  have hF3 : (3 : ZMod q) ≠ 0 := by
    simpa using natCast_ne_zero_of_prime (q := q) Nat.prime_three (by omega)
  refine le_antisymm (closure_fixSetThree_le A) ?_
  obtain ⟨H, hHle, hHn, hHirr, hcases⟩ := hB q (by omega)
    (isIrreducible_of_mem hω hω3 (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_right hb) :
      IsIrreducibleMatrixRep (Subgroup.closure (fixSetThree 3 A) ⊔ A).subtype)
  have hnA : ∀ g ∈ A, ∀ x ∈ H, g * x * g⁻¹ ∈ H := fun g hg => hHn g (Subgroup.mem_sup_right hg)
  have hnX : ∀ y ∈ fixSetThree 3 A, ∀ x ∈ H, y * x * y⁻¹ ∈ H :=
    fun y hy => hHn y (Subgroup.mem_sup_left (Subgroup.subset_closure hy))
  have hK : ∀ i : Fin 3, diagSign i ∈ fixSetThree 3 A :=
    diagSign_mem_fixSetThree hF2 Nat.prime_three (by norm_num) hω hω3 ha
  have hd : ∀ i : Fin 3, ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ ∈ H := fun i => hnX _ (hK i)
  rcases hcases with rfl | ⟨M, hMt, hMd, rfl⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hperf, hZ, hiso, -⟩ |
    ⟨hcyc, hdvd, hndvd⟩ | ⟨hcard, hex, -⟩ | ⟨rfl, hmon⟩
  · exact le_closure_fixSetThree_of_isPerfect hA
      (CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le le_rfl _) hHle
  · obtain ⟨e⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 h5 hMt hMd
    have := CFSG.RankThree.PartOne.KFBloom.omegaGL_isPerfect h5 M hMt hMd
    have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact (false_of_noElemSq hA hω hω3 ha hb hHirr hnA e
      (noElemSq_psl_two q (by omega) Nat.prime_three (by norm_num) (by omega))).elim
  · have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact (false_of_noElemSq hA hω hω3 ha hb hHirr hnA e
      (noElemSq_alt_five Nat.prime_three (by norm_num))).elim
  · have := isPerfect_gl_three_two
    exact (false_of_noElemSq hA hω hω3 ha hb hHirr hnA e
      (noElemSq_gl_three_two Nat.prime_three (by norm_num))).elim
  · exact (diagSign_ne_one hF2 0
      (eq_one_of_threeA6 hA6 hq3 hA hHirr hperf hZ hiso hnA hnX _ (hK 0))).elim
  · exact (false_of_isCyclic (by omega) hHirr hcyc hdvd hndvd hd).elim
  · exact (false_of_extraspecial hq3 hHirr hcard hex hd).elim
  · exact (false_of_monomial hq3 hF2 hF3 hω hω3 ha hb hμ hmon).elim

theorem closure_fixSetThree_of_not_commute (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    (hA6 : CFSG.RankThree.PartOne.N1322.KF1322ThreeA6Norm) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q) {A : Subgroup (GL (Fin 3) (ZMod q))}
    (hA : IsElemModScalars p A) (hnc : ∃ g ∈ A, ∃ h ∈ A, g * h ≠ h * g) :
    Subgroup.closure (fixSetThree p A) = CFSG.Open.StatedSL 3 (ZMod q) := by
  obtain ⟨rfl, hq3, ω, μ, P, hω, hω3, ha, hb⟩ := exists_conj_normalForm hq2 hp hp2 hpq hA hnc
  have hA' := hA.map_conj P
  refine closure_fixSetThree_eq_of_le_conj P le_rfl ?_
  by_cases hμ : ∃ ν : (ZMod q)ˣ, ν ^ 3 = μ
  · obtain ⟨ν, rfl⟩ := hμ
    obtain ⟨P', ha', hb'⟩ := exists_conj_cycMat_one hA'.center_le ha hb
    exact closure_fixSetThree_eq_of_le_conj P' le_rfl
      (closure_fixSetThree_of_normalForm hB hA6 hq3 (hA'.map_conj P') hω hω3 ha' hb' (Or.inl rfl))
  · push Not at hμ
    exact closure_fixSetThree_of_normalForm hB hA6 hq3 hA' hω hω3 ha hb (Or.inr hμ)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
