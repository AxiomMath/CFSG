module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmCases
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
public import CFSG.GroupTheory.Fitting.LayerContainment
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockProofFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 CFSG.SeitzReduction.OmegaPilot CFSG.RankThree.PartOne
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.AssemblyBPredicates
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d
open scoped Classical

private theorem isSolvable_supportedFixedDerived_of_finrank_le_two
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (h2 : Module.finrank K (fixedSpace x) ≤ 2) :
    Group.IsSolvable ↥(supportedFixedDerived Q x) := by
  classical
  set R := Q.comp (fixedSpace x).subtype with hR
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  haveI : Group.IsSolvable ↥(orthDerived R) := by
    rcases Nat.lt_or_ge (Module.finrank K (fixedSpace x)) 2 with h1 | h2'
    · refine isSolvable_of_comm fun a b => ?_
      have ha1 : (a : fixedSpace x ≃ₗ[K] fixedSpace x) = 1 :=
        eq_one_of_dicksonHom_eq_one_of_finrank_le_one hRnd (by omega)
          (dicksonHom_apply_orthDerived_eq_one hRnd a.2)
      have hb1 : (b : fixedSpace x ≃ₗ[K] fixedSpace x) = 1 :=
        eq_one_of_dicksonHom_eq_one_of_finrank_le_one hRnd (by omega)
          (dicksonHom_apply_orthDerived_eq_one hRnd b.2)
      refine Subtype.ext ?_
      show (a : fixedSpace x ≃ₗ[K] fixedSpace x) * b = b * a
      rw [ha1, hb1]
    · have hdim : Module.finrank K (fixedSpace x) = 2 := by omega
      refine isSolvable_of_comm fun a b => ?_
      have ha : dicksonHom R hRnd
          ⟨(a : fixedSpace x ≃ₗ[K] fixedSpace x), orthDerived_le_orthogonalGroup a.2⟩ = 1 :=
        dicksonHom_apply_orthDerived_eq_one hRnd a.2
      have hb : dicksonHom R hRnd
          ⟨(b : fixedSpace x ≃ₗ[K] fixedSpace x), orthDerived_le_orthogonalGroup b.2⟩ = 1 :=
        dicksonHom_apply_orthDerived_eq_one hRnd b.2
      exact Subtype.ext (commute_of_dicksonHom_eq_one hRnd hdim
        (orthDerived_le_orthogonalGroup a.2) (orthDerived_le_orthogonalGroup b.2) ha hb)
  refine Group.isSolvable_of_isSolvable_injective
    (f := (supportedFixedDerivedEquiv hx).toMonoidHom) ?_
  exact (supportedFixedDerivedEquiv hx).injective

private theorem supportedFixedDerived_le_sup_centralizer_of_quasisimple
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hlist : FixedLayerListed Q x)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    supportedFixedDerived Q x ≤ F ⊔ Subgroup.centralizer (F : Set (V ≃ₗ[K] V)) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨n, Ff, hFf, hcomm, hsup, -⟩ := exists_fixedFactors_comm hx
  have hFcomp : CFSG.Open.IsComponentOf F (supportedFixedDerived Q x) :=
    ⟨hFle, CFSG.Open.IsSubnormal.step hFle hFn (CFSG.Open.IsSubnormal.refl _),
      (isQuasisimple_iff_open ↥F).1 ((isQuasisimple_iff_native ↥F).2 hFq)⟩
  have hFfcomp : ∀ i, CFSG.Open.IsComponentOf (Ff i) (supportedFixedDerived Q x) := by
    intro i
    have hq := (isQuasisimple_iff_open ↥(Ff i)).1
      ((isQuasisimple_iff_native ↥(Ff i)).2 (hFf i).1)
    exact ⟨(hFf i).2.1, CFSG.Open.IsSubnormal.step (hFf i).2.1 (hFf i).2.2
      (CFSG.Open.IsSubnormal.refl _), hq⟩
  have hperf : ∀ P : Subgroup (V ≃ₗ[K] V), P ≤ supportedFixedDerived Q x →
      commutator ↥P = ⊤ → P ≤ ⨆ i, Ff i := by
    intro P hP _
    rw [hsup hlist]
    exact hP
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors Ff hFfcomp
      hperf hFcomp
  rw [← hsup hlist]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    rw [hi]
    exact le_sup_left
  · refine le_sup_of_le_right ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hi] at ha
    exact (hcomm j i hji b hb a ha).symm

theorem orthFixedBlock_holds {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) : OrthFixedBlock Q := by
  classical
  intro p hp hp2 x y hx hyc hyp F hFq hFle hFn J hJeq hN
  have hFq' : CFSG.IsQuasisimple ↥(F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hFle).symm hFq
  have hdim3 : 3 ≤ Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) := by
    by_contra hlt
    push Not at hlt
    have h2 : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) ≤ 2 := by omega
    haveI hsol := isSolvable_supportedFixedDerived_of_finrank_le_two hx h2
    exact (CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.not_isQuasisimple_of_isSolvable
      (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V)))) hFq'
  have hlist : FixedLayerListed Q (x : V ≃ₗ[K] V) := by
    refine ⟨hdim3, ?_⟩
    intro hS
    haveI hsol := isSolvable_supportedFixedDerived_of_smallFixedException hx hdim3 hS
    exact (CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.not_isQuasisimple_of_isSolvable
      (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V)))) hFq'
  have hX1 : (X - 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap :=
    X_sub_one_mem_of_fixed (x := (x : V ≃ₗ[K] V)) (by omega)
  set yW : V ≃ₗ[K] V :=
    (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx
      ⟨(y : V ≃ₗ[K] V), (Subgroup.mem_inf.mp hyc).2⟩ (X - 1)).1 with hyWdef
  have hypV : (y : V ≃ₗ[K] V) ^ p = 1 := by
    simpa using congrArg (fun e : ↥(orthDerived Q) => (e : V ≃ₗ[K] V)) hyp
  have hyWblock : yW ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1) :=
    hx.blockComponent_mem hyc hX1
  have hyWp : yW ^ p = 1 := blockComponent_fixed_pow hx hyc hypV
  have hyWP : yW ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V) := by
    set R := Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype with hR
    have hRnd : (QuadraticMap.polarBilin R).Nondegenerate :=
      hx.polarBilin_fixed_nondegenerate
    have hgpow : (restrictFixed Q (x : V ≃ₗ[K] V)
        ⟨yW, hyWblock⟩) ^ p = 1 := by
      rw [← map_pow]
      have h1 : (⟨yW, hyWblock⟩ : ↥(supportedBlock Q (x : V ≃ₗ[K] V) (X - 1))) ^ p = 1 :=
        Subtype.ext hyWp
      rw [h1, map_one]
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hδ : dicksonHom R hRnd
        ⟨restrictFixed Q (x : V ≃ₗ[K] V) ⟨yW, hyWblock⟩,
          restrictFixed_mem_orthogonalGroup _⟩ = 1 :=
      dicksonHom_eq_one_of_pow_eq_one hRnd hodd (Subtype.ext hgpow)
    have hω : restrictFixed Q (x : V ≃ₗ[K] V) ⟨yW, hyWblock⟩ ∈ omegaGroup R hRnd := by
      have hk : (⟨restrictFixed Q (x : V ≃ₗ[K] V) ⟨yW, hyWblock⟩,
          restrictFixed_mem_orthogonalGroup _⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ∈ (dicksonHom R hRnd).ker := by
        rw [MonoidHom.mem_ker]
        exact hδ
      rw [dicksonHom_ker] at hk
      exact Subgroup.mem_subgroupOf.mp hk
    exact mem_supportedFixedDerived.mpr ⟨hyWblock,
      omegaGroup_le_orthDerived_of_listed R hRnd hlist.1 hlist.2 hω⟩
  have hle_sup : supportedFixedDerived Q (x : V ≃ₗ[K] V) ≤
      F ⊔ Subgroup.centralizer (F : Set (V ≃ₗ[K] V)) :=
    supportedFixedDerived_le_sup_centralizer_of_quasisimple hx hlist hFq hFle hFn
  obtain ⟨f, hfF, hfconj⟩ :=
    CFSG.GroupTheory.exists_forall_conj_eq_of_mem_sup_centralizer (C := F) (k := yW)
      (hle_sup hyWP)
  have hfOr : f ∈ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived (hFle hfF)
  set f' : ↥(orthDerived Q) := ⟨f, hfOr⟩ with hf'def
  have hhJ : piOrth Q f' ∈ J := by
    rw [hJeq]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr hfF)
  refine indAut_mem_inner_of_conj_eq hN hhJ ?_
  intro z
  have hz : (z : ProjOrthDerived Q) ∈
      (F.subgroupOf (orthDerived Q)).map (piOrth Q) := by
    rw [← hJeq]
    exact z.2
  obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
  have haF : (a : V ≃ₗ[K] V) ∈ F := Subgroup.mem_subgroupOf.mp ha
  have haSB : (a : V ≃ₗ[K] V) ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1) :=
    supportedFixedDerived_le_supportedBlock (hFle haF)
  have hVEq : (y : V ≃ₗ[K] V) * (a : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)⁻¹ =
      f * (a : V ≃ₗ[K] V) * f⁻¹ :=
    (blockComponent_fixed_conj_eq hx hyc haSB).trans (hfconj (a : V ≃ₗ[K] V) haF)
  have hAEq : y * a * y⁻¹ = f' * a * f'⁻¹ := Subtype.ext hVEq
  calc
    piOrth Q y * (z : ProjOrthDerived Q) * (piOrth Q y)⁻¹
        = piOrth Q (y * a * y⁻¹) := by rw [← haz, map_mul, map_mul, map_inv]
    _ = piOrth Q (f' * a * f'⁻¹) := by rw [hAEq]
    _ = piOrth Q f' * (z : ProjOrthDerived Q) * (piOrth Q f')⁻¹ := by
      rw [← haz, map_mul, map_mul, map_inv]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
