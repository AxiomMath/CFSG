module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairModels
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthMinus

public section

namespace CFSG.Quasithin

namespace B69K

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.Quasithin.LieOver
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (statedProjectiveSubspaceStabilizer statedProjectiveFlagStabilizer)
open scoped Pointwise

theorem lf_tail_indepQ {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
    {qA : QuadraticForm K A} (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) (i : Fin r) :
    ∃ x : lkQ r qA, x ∉ lkPi r qA i ∧ ∀ j : Fin r, j ≠ i → x ∈ lkPi r qA j := by
  refine ⟨QuotientGroup.mk' (elemScalars (quadTail r qA))
    ⟨tailWeylElt r qA a₀ i, tailWeylElt_mem a₀ i⟩, ?_, fun j hj => ?_⟩
  · intro h
    have hfix := mem_stabP_iff.1 h ⟨tailWeylElt r qA a₀ i, tailWeylElt_mem a₀ i⟩ rfl
    have hsm : tailWeylElt r qA a₀ i • tailFlag K A r ((i : ℕ) + 1) =
        tailFlag K A r ((i : ℕ) + 1) :=
      MulAction.mem_stabilizer_iff.1 (Submodule.mem_stabilizer_submodule_iff_map_eq.2 hfix)
    exact (tailWeylElt_smul_tailFlag hani ha₀ i i).1 hsm rfl
  · have hfix : tailWeylElt r qA a₀ i • tailFlag K A r ((j : ℕ) + 1) =
        tailFlag K A r ((j : ℕ) + 1) :=
      (tailWeylElt_smul_tailFlag hani ha₀ j i).2 (Ne.symm hj)
    exact Subgroup.mem_map_of_mem _ (mem_stabilizer_iff_map.2
      (Submodule.mem_stabilizer_submodule_iff_map_eq.1 (MulAction.mem_stabilizer_iff.2 hfix)))

theorem lf_tail_facts {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
    {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (ψ : (quadTail r qA).IsometryEquiv Q) (hQ : ⇑Q = Q0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {F : Fin r → Submodule K (ι → K)}
    (hF : ∀ i, F i = (tailFlag K A r ((i : ℕ) + 1)).map ψ.toLinearMap)
    (hani : qA.Anisotropic) (hm : finrank K A = 1 ∨ finrank K A = 2) :
    Finite (StatedProj (StatedOmega Q0)) ∧
      ∀ i : Fin r, ∃ g : StatedProj (StatedOmega Q0),
        g ∉ statedProjectiveSubspaceStabilizer Q0 (F i) ∧
          ∀ j : Fin r, j ≠ i → g ∈ statedProjectiveSubspaceStabilizer Q0 (F j) := by
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  haveI : FiniteDimensional K A := Module.finite_of_finrank_pos hpos
  haveI : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  haveI : Finite A := Module.finite_of_finite K
  haveI : Finite (lkGL r K A) := Finite.of_injective
    (fun g : lkGL r K A => (g : ((Fin r ⊕ Fin r → K) × A) → (Fin r ⊕ Fin r → K) × A))
    DFunLike.coe_injective
  haveI : Finite (orthElementaryGroup (quadTail r qA)) := inferInstance
  haveI : Finite (lkQ r qA) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hPhiPi : ∀ i : Fin r, (statedProjectiveSubspaceStabilizer Q0 (F i)).map
      (tailProjEquiv ψ hQ hE).toMonoidHom = lkPi r qA i := by
    intro i
    rw [tailProjEquiv_subspaceStabilizer ψ hQ hE, hF i, map_symm_map_isometry]
  refine ⟨Finite.of_surjective (tailProjEquiv ψ hQ hE).symm
    (tailProjEquiv ψ hQ hE).symm.surjective, fun i => ?_⟩
  obtain ⟨x, hx1, hx2⟩ := lf_tail_indepQ hani ha₀ i
  have key : ∀ j : Fin r,
      (tailProjEquiv ψ hQ hE).symm x ∈ statedProjectiveSubspaceStabilizer Q0 (F j) ↔
        x ∈ lkPi r qA j := by
    intro j
    rw [← hPhiPi j]
    exact Subgroup.mem_map_equiv.symm
  exact ⟨(tailProjEquiv ψ hQ hE).symm x, fun h => hx1 ((key i).1 h),
    fun j hj => (key j).2 (hx2 j hj)⟩

theorem parabolicPair_lfMinus {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hBI : OrthogonalTail.BorelInterface 2 (StatedQuadMinus n K b c)
      (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2))) :
    ∃ U : Subgroup (lfMinusModel n K b c),
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  obtain ⟨hfl, ⟨S, hSB⟩, -, -, hidx⟩ := hBI
  obtain ⟨hfin, hindep⟩ := lf_tail_facts (minusTailIsometry n K b c) (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr)
    (tailModelFlag_eq_map (minusTailIsometry n K b c) fun _ => rfl)
    (anisotropic_minusTailForm hirr) (Or.inr finrank_fin_two_fun)
  haveI : Finite (lfMinusModel n K b c) := hfin
  have hBle : ∀ i : Fin (n - 1),
      statedProjectiveFlagStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)) ≤
        statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) :=
    fun i => iInf_le _ i
  have hSB' : (S : Subgroup (lfMinusModel n K b c)) ≤
      statedProjectiveFlagStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)) := by
    rw [hSB]
    exact Subgroup.le_normalizer
  have hSle : ∀ i : Fin (n - 1), (S : Subgroup (lfMinusModel n K b c)) ≤
      statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) :=
    fun i => hSB'.trans (hBle i)
  obtain ⟨i0, hi0⟩ : ∃ i : Fin (n - 1), (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin (n - 1), (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hlt := hidx _ _ (hfl i1).1 (by rw [(hfl i1).2, hi1]) (hfl i0).1
    (by rw [(hfl i0).2, hi0])
  refine ⟨(S : Subgroup (lfMinusModel n K b c)),
    CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow S, ?_⟩
  refine parabolicPair_of_coatoms (Ps := pOmegaMinusParabolics n K b c) ?_ ?_ ?_ ?_
  · rintro P ⟨i, rfl⟩
    exact ⟨covBy_top_iff.1 (pOmegaMinusCoatom_holds n K b c hn hirr i), hSle i⟩
  · intro A hA hAt
    obtain ⟨i, hi⟩ := pOmegaMinusCover_holds n K b c hn hirr S hSB A hA hAt
    exact ⟨_, lf_mem_minusPs i, hi⟩
  · rintro P ⟨i, rfl⟩
    obtain ⟨g, hg1, hg2⟩ := hindep i
    refine ⟨g, hg1, ?_⟩
    rintro P' ⟨j, rfl⟩ hne
    exact hg2 j (fun h => hne (by rw [h]))
  · exact ⟨_, lf_mem_minusPs i0, _, lf_mem_minusPs i1, hlt.ne⟩

theorem pairData_of_statedPOmegaMinus {C : Type} [Group C] {n f : ℕ} (hn : 4 ≤ n)
    (hmc : StatedClassicalModel C .POmegaMinus n 2 f) :
    ∃ U : Subgroup C, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  have hBI := OrthogonalTail.orthogonal_geometry_tail_model_Borel_overgroup_interface C .POmegaMinus
    (Or.inr rfl) n 2 f hmc
  obtain ⟨-, K, hK, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hmc
  have hB := hBI K hcard b c hirr
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact pairData_of_mulEquiv e (parabolicPair_lfMinus hn hirr hB)

end B69K

end CFSG.Quasithin
