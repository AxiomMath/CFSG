module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOBlocks
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeLinModel
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic

public section

namespace CFSG.AGLEmbedding

open Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def ThreeCentInnerKey (S : Type*) [Group S] : Prop :=
  ∀ a : S, a ^ 3 = 1 →
    (∀ P : Subgroup S, P ≤ Subgroup.centralizer ({a} : Set S) → ⁅P, P⁆ = P → P = ⊥) →
    ∀ y ∈ Subgroup.centralizer ({a} : Set S), ∀ p : ℕ, p.Prime → 5 ≤ p → y ^ p = 1 → y = 1

theorem ThreeCentInnerKey.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : ThreeCentInnerKey S') : ThreeCentInnerKey S := by
  intro a ha3 hfree y hy p hp hp5 hyp
  have hcent : ∀ z : S, z ∈ Subgroup.centralizer ({a} : Set S) ↔
      e z ∈ Subgroup.centralizer ({e a} : Set S') := fun z => by
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, e.injective.eq_iff]
  refine e.injective ((h (e a) (by rw [← map_pow, ha3, map_one]) (fun P hP hPP => ?_) (e y)
    ((hcent y).mp hy) p hp hp5 (by rw [← map_pow, hyp, map_one])).trans (map_one e).symm)
  have h1 := hfree (P.map e.symm.toMonoidHom) (by
      rintro _ ⟨z, hz, rfl⟩
      rw [hcent]
      simpa using hP hz) (by rw [← Subgroup.map_commutator, hPP])
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h1

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem statedScalars_index_eq_bot_of_card_eq_two (hK : Nat.card K = 2) :
    StatedScalars ι K = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [units_eq_one_of_card_eq_two hK c, map_one]
  exact Subgroup.one_mem _

noncomputable def statedProjOmegaEquivDerived (hK : Nat.card K = 2)
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    StatedProj (StatedOmega Q₀) ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((QuotientGroup.quotientMulEquivOfEq (by
      rw [statedScalars_index_eq_bot_of_card_eq_two hK, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot).trans
    (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans
      (MulEquiv.subgroupCongr (by
        rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ]
        exact Subgroup.map_comap_eq_self_of_surjective
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _)))

omit [DecidableEq ι] in
theorem threeCentInnerKey_orthDerived (hK : Nat.card K = 2) {Q : QuadraticForm K (ι → K)}
    (hQ : (polarBilin Q).Nondegenerate) :
    ThreeCentInnerKey ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  intro a ha3 hfree y hy p hp hp5 hyp
  by_contra hy1
  have hxO : (a : (ι → K) ≃ₗ[K] (ι → K)) ∈ O := Subgroup.commutator_le_self O a.2
  have hx3 : (a : (ι → K) ≃ₗ[K] (ι → K)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ha3, Subgroup.coe_one]
  have hyC : (y : (ι → K) ≃ₗ[K] (ι → K)) ∈ isometryCentralizer Q a := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.commutator_le_self O y.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  obtain ⟨P, hPC, hP, hP1⟩ := exists_perfect_of_isometryCentralizer_orth hK hQ hxO hx3 hyC hp
    hp5 (by rw [← Subgroup.coe_pow, hyp, Subgroup.coe_one])
    (fun h => hy1 (Subtype.ext h))
  have hPO : P ≤ O := hPC.trans inf_le_left
  have hPD : P ≤ ⁅O, O⁆ := by
    rw [← hP]
    exact Subgroup.commutator_mono hPO hPO
  set P' := P.subgroupOf ⁅O, O⁆
  have hP'map : P'.map ⁅O, O⁆.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD]
  have hcent : P' ≤ Subgroup.centralizer {a} := fun z hz => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (hPC (Subgroup.mem_subgroupOf.mp hz))).2)
  have hperf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective (Subgroup.subtype_injective ⁅O, O⁆)
    rw [Subgroup.map_commutator, hP'map, hP]
  refine hP1 ?_
  rw [← hP'map, hfree P' hcent hperf, Subgroup.map_bot]

theorem innerKey_of_model_pomega {X : Type} [Group X] (hK : Nat.card K = 2)
    {Q : QuadraticForm K (ι → K)} (hQ : (polarBilin Q).Nondegenerate) {Q₀ : (ι → K) → K}
    (hQ0 : ⇑Q = Q₀) (e : X ≃* StatedProj (StatedOmega Q₀)) : ThreeCentInnerKey X :=
  ThreeCentInnerKey.of_mulEquiv (e.trans (statedProjOmegaEquivDerived hK hQ0))
    (threeCentInnerKey_orthDerived hK hQ)

open CFSG.LieType.Universal.Spin in
theorem center_eq_bot_and_innerKey_of_model_pomegaPlus_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .POmegaPlus n 2 1) :
    Subgroup.center X = ⊥ ∧ ThreeCentInnerKey X := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
  have : Group.IsPerfect (StatedOmega (StatedQuadPlus n K)) :=
    isPerfect_statedOmega_quadPlus (by omega)
  have : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup X := e.isSimpleGroup
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  exact ⟨center_eq_bot_of_simple_of_perfect, innerKey_of_model_pomega hK2
    (nondegenerate_polarBilin_quadPlus n K) (coe_quadPlus n K) e⟩

open CFSG.LieType.Universal.Spin in
theorem threeAutFixedTwoThree_of_model_pomegaMinus_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n 2 1) : ThreeAutFixedTwoThree X := by
  have hout := card_outer_le_two_of_omegaMinus_two h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hn hirr
  have : Group.IsPerfect (StatedOmega (StatedQuadMinus n K b c)) :=
    isPerfect_statedOmega_quadMinus hn hirr
  have : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup X := e.isSimpleGroup
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  refine threeAutFixedTwoThree_of_inner_prime center_eq_bot_of_simple_of_perfect ?_
    (innerKey_of_model_pomega hK2 (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      (coe_quadMinus n K b c) e)
  intro h3
  have := Nat.le_of_dvd hout.1 h3
  omega

theorem threeAutFixedTwoThree_of_model_pomegaPlus_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .POmegaPlus n 2 1) (hn5 : 5 ≤ n) : ThreeAutFixedTwoThree X := by
  have hout := card_outer_le_two_of_omegaPlus_two_of_five_le h hn5
  obtain ⟨hZ, hkey⟩ := center_eq_bot_and_innerKey_of_model_pomegaPlus_two h
  refine threeAutFixedTwoThree_of_inner_prime hZ ?_ hkey
  intro h3
  have := Nat.le_of_dvd hout.1 h3
  omega

end CFSG.AGLEmbedding
