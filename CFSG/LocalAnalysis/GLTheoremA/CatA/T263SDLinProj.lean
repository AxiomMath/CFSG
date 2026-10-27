module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinBlock
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CentralQuotient
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXGlue
public import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary
  CFSG.LocalAnalysis.GLTheoremA.T263.DX

variable {K : Type} [Field K] [Finite K] {n : ℕ}

local notation "σ" => CatalogueBHigherLinearAction.slConjugation n K

theorem proj_mem_fix {A : GL (Fin n) K} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ fixSubgroup (σ A)) : proj n K g ∈ fixSubgroup (conjAut n K A) := by
  rw [mem_fixSubgroup, conjAut_proj, mem_fixSubgroup.1 hg]

theorem map_specialFactor_le_fix (A : GL (Fin n) K) (h : K[X]) :
    (specialFactor A h).map (proj n K) ≤ fixSubgroup (conjAut n K A) := by
  rintro _ ⟨g, hg, rfl⟩
  exact proj_mem_fix (specialFactor_le_fixSubgroup A h hg)

theorem map_fix_le_fix (A : GL (Fin n) K) :
    (fixSubgroup (σ A)).map (proj n K) ≤ fixSubgroup (conjAut n K A) := by
  rintro _ ⟨g, hg, rfl⟩
  exact proj_mem_fix hg

theorem conj_mem_map_fix {A : GL (Fin n) K} {x : projectiveSL n K}
    (hx : x ∈ fixSubgroup (conjAut n K A)) {c : projectiveSL n K}
    (hc : c ∈ (fixSubgroup (σ A)).map (proj n K)) :
    x * c * x⁻¹ ∈ (fixSubgroup (σ A)).map (proj n K) := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  refine ⟨g * c₀ * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [SetLike.mem_coe]
  have h1 : proj n K (σ A g) = proj n K g := by
    rw [← conjAut_proj]
    exact mem_fixSubgroup.1 hx
  have hs : g⁻¹ * σ A g ∈ scalars n K := proj_eq_proj_iff.1 h1.symm
  set s := g⁻¹ * σ A g with hsdef
  have hσg : σ A g = g * s := by rw [hsdef, mul_inv_cancel_left]
  have hc0 : σ A c₀ = c₀ := mem_fixSubgroup.1 hc₀
  rw [mem_fixSubgroup, map_mul, map_mul, map_inv, hσg, hc0]
  have hsc : s * c₀ * s⁻¹ = c₀ := mul_inv_eq_iff_eq_mul.2 (scalars_commute hs c₀).eq
  calc g * s * c₀ * (g * s)⁻¹ = g * (s * c₀ * s⁻¹) * g⁻¹ := by group
    _ = g * c₀ * g⁻¹ := by rw [hsc]

theorem normal_map_subgroupOf {G H : Type*} [Group G] [Group H] (f : G →* H) {N M : Subgroup G}
    (hn : ∀ c ∈ M, ∀ x ∈ N, c * x * c⁻¹ ∈ N) : ((N.map f).subgroupOf (M.map f)).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨x₀, hx₀, hxx⟩ := hx
  obtain ⟨c, hcM, hcy⟩ := y.2
  refine ⟨c * x₀ * c⁻¹, hn c hcM x₀ hx₀, ?_⟩
  simp only [map_mul, map_inv, hxx, hcy, Subgroup.coe_mul, Subgroup.coe_inv]

theorem isQuasisimple_map_specialFactor {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K (Fin n → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hgood : IsGoodFactor A h) :
    CFSG.IsQuasisimple ↥((specialFactor A h).map (proj n K)) := by
  have hFq := isQuasisimple_specialFactor hsq hh hgood
  refine CFSG.LocalCores.isQuasisimple_map hFq (proj n K) fun hle => ?_
  have hFc : ∀ g ∈ specialFactor A h, g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    fun g hg => scalars_le_center n K (by rw [← ker_proj]; exact hle hg)
  have hZF : Subgroup.center (specialFactor A h) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_center_iff]
    intro g'
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hFc g g.2)) g')
  obtain ⟨u, w, huw⟩ := hFq.2.2
  apply huw
  induction u using QuotientGroup.induction_on with
  | H u =>
    induction w using QuotientGroup.induction_on with
    | H w =>
      rw [(QuotientGroup.eq_one_iff u).mpr (by rw [hZF]; exact Subgroup.mem_top u),
        (QuotientGroup.eq_one_iff w).mpr (by rw [hZF]; exact Subgroup.mem_top w)]

theorem isComponentOf_map_specialFactor {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K (Fin n → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hgood : IsGoodFactor A h) :
    CFSG.Open.IsComponentOf ((specialFactor A h).map (proj n K)) (fixSubgroup (conjAut n K A)) := by
  refine ⟨map_specialFactor_le_fix A h, ?_,
    open_of_native_dx (isQuasisimple_map_specialFactor hsq hh hgood)⟩
  have hJC : (specialFactor A h).map (proj n K) ≤ (fixSubgroup (σ A)).map (proj n K) :=
    Subgroup.map_mono (specialFactor_le_fixSubgroup A h)
  have hJn : (((specialFactor A h).map (proj n K)).subgroupOf
      ((fixSubgroup (σ A)).map (proj n K))).Normal :=
    normal_map_subgroupOf (proj n K) (fun c hc g hg => conj_mem_specialFactor hc hg)
  have hCn : (((fixSubgroup (σ A)).map (proj n K)).subgroupOf (fixSubgroup (conjAut n K A))).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using conj_mem_map_fix y.2 hx
  exact CFSG.Open.IsSubnormal.step hJC hJn
    (CFSG.Open.IsSubnormal.step (map_fix_le_fix A) hCn (CFSG.Open.IsSubnormal.refl _))

theorem dvd_card_centerQuot_map_of_dvd {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K (Fin n → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hgood : IsGoodFactor A h) {p : ℕ}
    (hp : p.Prime) (hpF : p ∣ Nat.card (specialFactor A h)) :
    p ∣ Nat.card (↥((specialFactor A h).map (proj n K)) ⧸
      Subgroup.center ↥((specialFactor A h).map (proj n K))) := by
  have hFq := isQuasisimple_specialFactor hsq hh hgood
  have hperf : commutator (specialFactor A h) = ⊤ := (open_of_native_dx hFq).1
  obtain ⟨e⟩ := LieComp.nonempty_centralQuotient_mulEquiv hperf ((proj n K).subgroupMap (specialFactor A h))
    ((proj n K).subgroupMap_surjective _) (by
      intro g hg
      have h1 : proj n K (g : SpecialLinearGroup (Fin n) K) = 1 := congrArg Subtype.val hg
      have h2 : (g : SpecialLinearGroup (Fin n) K) ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
        scalars_le_center n K (proj_eq_one_iff.1 h1)
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext ((Subgroup.mem_center_iff.mp h2) g'))
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.dvd_card_quotient_center_of_quasisimple hFq hp hpF

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
