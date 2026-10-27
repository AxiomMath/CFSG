module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexHomologyHyperbolic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Homology

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover
  CFSG.OddSolvableUnitary CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI
  CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
  CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open scoped commutatorElement

theorem unitary_homology_subgroup_saturates_hyperbolic_rightCoset {K : Type} [Field K]
    (J : HermitianForm 3 K) {f : ℕ} (hf : 1 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (C : Subgroup J.specialSubgroup) [C.Normal] (hC : C ≤ UnitaryAutomorphism.scalarCenter J)
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (L : Subgroup G) (φ : L ≃* J.specialSubgroup ⧸ C)
    {t : G} (htL : t ∈ L) (ht : orderOf t = 2)
    (htbeta : rightCosetTranslate H (rightCosetMk H 1) t = beta)
    {I W : Subgroup G} (hIE : I ≤ pairPointStabilizer H beta)
    (hIN : pairPointStabilizer H beta ≤ normalizer (I : Set G)) (hIodd : Odd (Nat.card I))
    (hEt : ⁅pairPointStabilizer H beta, zpowers t⁆ ≤ I)
    (hWE : W ≤ pairPointStabilizer H beta) (hWL : W ≤ L)
    (hW : (W.subgroupOf L).map φ.toMonoidHom = UnitaryAutomorphism.torusL J C hJ)
    (hWt : ∀ w ∈ W, w * t = t * w) (hsolv : Group.IsSolvable ((W ⊔ I) ⊓ L : Subgroup G))
    (hWH : ⁅W, (W ⊔ I) ⊓ L⁆ ≠ ⊥)
    (hfix : ∀ ω ∈ pointFixedSet H ((W ⊔ I) ⊓ L), ω = rightCosetMk H 1 ∨ ω = beta) :
    (W ⊔ I) ⊓ L = I ⊓ L ∧ ⁅(W ⊔ I) ⊓ L, zpowers t⁆ = (W ⊔ I) ⊓ L ∧
      {y | ∃ x ∈ (W ⊔ I) ⊓ L, x * t * x⁻¹ = y}.ncard = 3 * (2 ^ f + 1) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hK : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  have hJbar : ∀ c, J.conj c = hK.bar c := fun c => by
    rw [CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard hfixed,
      UnitaryFieldData.bar_apply]
  let Θ := specialSubgroupEquiv hK hJbar
  let Z₀ : Subgroup (sesqSpecialUnitaryGroup (hermForm hK J)) := C.map Θ.toMonoidHom
  have hZ₀n : Z₀.Normal := Subgroup.Normal.map inferInstance _ Θ.surjective
  have hZ₀ : ∀ z ∈ Z₀, ∃ c : K, ((z : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
      (Fin 3 → K) →ₗ[K] Fin 3 → K) = c • 1 := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc, -, -⟩ := hC hz
    exact ⟨c, specialSubgroupEquiv_eq_smul_one hJbar hc⟩
  let Ξ : J.specialSubgroup ⧸ C ≃* sesqSpecialUnitaryGroup (hermForm hK J) ⧸ Z₀ :=
    QuotientGroup.congr C Z₀ Θ rfl
  let ι : sesqSpecialUnitaryGroup (hermForm hK J) ⧸ Z₀ →* G :=
    L.subtype.comp (φ.symm.toMonoidHom.comp Ξ.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    L.subtype_injective.comp (φ.symm.injective.comp Ξ.symm.injective)
  have hιrange : ι.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ((φ.symm.surjective.comp Ξ.symm.surjective)), ← MonoidHom.range_eq_map,
      range_subtype]
  have hιΘ : (ι.comp (QuotientGroup.mk' Z₀)).comp Θ.toMonoidHom =
      L.subtype.comp (φ.symm.toMonoidHom.comp (QuotientGroup.mk' C)) := by
    ext g
    simp only [ι, Ξ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, Subgroup.coe_subtype]
    rw [← QuotientGroup.congr_mk C Z₀ Θ rfl g, MulEquiv.symm_apply_apply]
  obtain ⟨μ, hμ⟩ := exists_add_bar_eq_one hK
  obtain ⟨e₀, he₀⟩ := exists_basis_eq_hyperbolicVec hJ hμ
  have he₀o : ∀ i j, hermForm hK J (e₀ i) (e₀ j) = if i = j then 1 else 0 := fun i j => by
    rw [he₀]
    exact hermForm_hyperbolicVec hJ hμ i j
  have hW' : W = (homologySubgroup (hermForm hK J) e₀).map (ι.comp (QuotientGroup.mk' Z₀)) := by
    rw [homologySubgroup_eq_map_torusHom hJbar hJ he₀, Subgroup.map_map, hιΘ,
      ← Subgroup.map_map, ← Subgroup.map_map, ← MonoidHom.range_comp]
    change W = ((UnitaryAutomorphism.torusL J C hJ).map φ.symm.toMonoidHom).map L.subtype
    have hcomp : (L.subtype.comp φ.symm.toMonoidHom).comp φ.toMonoidHom = L.subtype := by
      ext x
      simp
    rw [← hW, Subgroup.map_map, Subgroup.map_map, hcomp, subgroupOf_map_subtype,
      inf_of_le_left hWL]
  let eq := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htα : t • eq (rightCosetMk H 1) = eq beta := by
    rw [← htbeta, rightCosetTranslate_inversion, htinv]
  have htβ : t • eq beta = eq (rightCosetMk H 1) := by
    rw [← htα, smul_smul, ht2, one_smul]
  have hαβ : eq (rightCosetMk H 1) ≠ eq beta := fun h => hbeta (eq.injective h).symm
  have hXE : (W ⊔ I) ⊓ L ≤ pairPointStabilizer H beta := inf_le_left.trans (sup_le hWE hIE)
  have hfix' : {ω : G ⧸ H | ∀ h ∈ (W ⊔ I) ⊓ L, h • ω = ω} =
      {eq (rightCosetMk H 1), eq beta} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have hmem : eq.symm ω ∈ pointFixedSet H ((W ⊔ I) ⊓ L) := by
        rw [mem_pointFixedSet_iff]
        intro x hx
        change x • eq (eq.symm ω) = eq (eq.symm ω)
        rw [Equiv.apply_symm_apply]
        exact h x hx
      rcases hfix _ hmem with h1 | h1
      · left
        rw [← h1, Equiv.apply_symm_apply]
      · right
        rw [← h1, Equiv.apply_symm_apply]
    · rintro (rfl | rfl) x hx
      · exact (hXE hx).1
      · exact (hXE hx).2
  obtain ⟨-, -, -, -, -, hXI, hXt, hXcard⟩ :=
    unitary_homology_subgroup_saturates_from_pair_fixed_set hK (Module.finrank_fin_fun K)
      (hermForm_isSymm hJbar) hermForm_separatingLeft Z₀ hZ₀ hαβ ι hι (hιrange ▸ htL) ht htα htβ
      (D := pairPointStabilizer H beta) rfl hIE hIN hIodd
      (fun d hd => hEt (commutator_mem_commutator hd (mem_zpowers t))) e₀ he₀o hW' hWE
      (fun w hw => commutatorElement_eq_one_iff_mul_comm.2 (hWt w hw))
      (H := (W ⊔ I) ⊓ L) (by rw [hιrange]) hsolv hWH hfix'
  rw [hιrange] at hXI
  exact ⟨hXI, hXt, hXcard⟩

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Homology
