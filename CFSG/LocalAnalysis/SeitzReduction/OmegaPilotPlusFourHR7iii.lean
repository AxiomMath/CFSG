module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHsyl
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.RankThree.PartOne.K159.Klein
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)

section Neighbour

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nonempty_pairPerp_mulEquiv_SL4 (hq : 4 ≤ Nat.card K) (k : Fin 4) :
    Nonempty (pairPerp (K := K) k ≃* Matrix.SpecialLinearGroup (Fin 4) K) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (4 - 1) K (by omega)
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (coordinateQuadPlus (4 - 1) K) hQ (by rw [Module.finrank_fin_fun]) hT hq
  set O := TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus (4 - 1) K) with hO
  have h1 : (commutator ↥O).map O.subtype = orthDerived (coordinateQuadPlus (4 - 1) K) := by
    rw [Subgroup.map_subtype_commutator]
  let e₁ : orthDerived (coordinateQuadPlus (4 - 1) K) ≃* commutator ↥O :=
    ((Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)).symm
  exact ⟨(((pairPerpEquiv le_rfl k).trans e₁).trans κ).trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm⟩

theorem isSolvable_outer_pairPerp_four (hq : 4 ≤ Nat.card K) (k : Fin 4) :
    Group.IsSolvable (Outer (pairPerp (K := K) k)) := by
  obtain ⟨φ⟩ := nonempty_pairPerp_mulEquiv_SL4 hq k
  have hsol := LinearPilot.isSolvable_outer_quotient_center_of_mulEquiv (m := 4) (by norm_num) φ
  have hcen := center_pairPerp (K := K) (n := 4) le_rfl k
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)

variable {G : Type} [Group G] {L : Subgroup G}

theorem neighbour_data_pairTorus_four {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (k : Fin 4) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Nat.card X = Nat.card K - 1 ∧
      Odd (Nat.card X) ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin 4) K) ∧
      Group.IsSolvable (Outer D) := by
  subst hX hDe
  have hDk := isQuasisimple_pairPerp (K := K) (n := 4) le_rfl k
  set ψ := LinearPilot.mapSymmMulEquiv e (pairPerp (K := K) k) with hψ
  obtain ⟨φ⟩ := nonempty_pairPerp_mulEquiv_SL4 hq k
  have hOut := isSolvable_outer_pairPerp_four hq k
  refine ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.isCyclic_map_symm e (isCyclic_pairTorus k),
    (LinearPilot.card_map_symm e _).trans (card_pairTorus k),
    (LinearPilot.card_map_symm e _).symm ▸ odd_card_pairTorus hKc k,
    (F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e (centralizer_pairTorus hq k)
      (isHypCoord_coordinateQuadPlus k).pairTorusOf_le_centralizer_pairPerpOf
      (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_pairTorus k)) hDk).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e
      ((isHypCoord_coordinateQuadPlus k).pairPerpOf_le_centralizer hq))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hDk, ?_, ⟨ψ.trans φ⟩,
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv ψ.symm⟩
  rw [← map_center_eq ψ.symm, center_pairPerp (K := K) (n := 4) le_rfl k, Subgroup.map_bot]

end Neighbour

section Inputs

@[expose] def PlusFourLeviInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ i j : Fin 4, i ≠ j →
    ⁅stabTwoBar K i j, stabTwoBar K i j⁆ = stabTwoBar K i j ∧
      ∀ N : Subgroup (plusLevi K i j), N.Normal → IsPGroup 2 N → N = ⊥

@[expose] def PlusFourRefinedF6Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ i j k : Fin 4, i ≠ j →
    i ≠ k → j ≠ k →
    RefinedF6 (plusRadical K i j) (plusLevi K i j) (pairTorus k) (pairPerp (K := K) k)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem plusRootElt_decomp_four (hlevi : PlusFourLeviInput) (hq : 4 ≤ Nat.card K) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    plusRootElt K (by norm_num) hij hik hjk ∈ pairPerp k ∧
      IsLongRoot _ (plusRootElt K (by norm_num) hij hik hjk) ∧
      perfectCore (centralizer ({plusRootElt K (by norm_num) hij hik hjk} :
        Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) =
        plusRadical K i j ⊔ plusLevi K i j ∧
      IsPGroup 2 (plusRadical K i j) ∧
      plusLevi K i j ≤ normalizer (plusRadical K i j :
        Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) ∧
      Disjoint (plusRadical K i j) (plusLevi K i j) ∧
      (∀ N : Subgroup (plusLevi K i j), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      pairTorus k ≤ plusLevi K i j := by
  obtain ⟨hS, hO⟩ := hlevi K hq i j hij
  have hQ := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hi := isHypCoord_coordinateQuadPlus (K := K) i
  have hj := isHypCoord_coordinateQuadPlus (K := K) j
  have hk := isHypCoord_coordinateQuadPlus (K := K) k
  have h₁₂ := hi.orth hj (pairDisjoint_plus hij)
  have h₁₃ := hi.orth hk (pairDisjoint_plus hik)
  have h₂₃ := hj.orth hk (pairDisjoint_plus hjk)
  refine ⟨?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃, ?_, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂, hO, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
  · obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
    have hP := commutator_centralizer_rootPairElt_of hi hj (pairDisjoint_plus hij) hQ h₁₃ h₂₃ hl0
      hl1 hS
    exact (CFSG.Quasithin.perfectCore_eq_self_of_perfect hP).trans
      (centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃)
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inr rfl)⟩

end Inputs

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_longRoot_twoSided_plus_of_habel_four (hset : SeitzSetting G L)
    {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC := mem_centralizer_of_inf_eq hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hLt : L ≤ centralizer ({t} : Set G) :=
    SeitzQ2.le_centralizer_singleton_of_mem_centralizer htC
  obtain ⟨x, z, hz, hxz, hz1, ⟨U, hU⟩, ⟨U', hU'⟩, hact⟩ :=
    exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2
      (SeitzQ2.commutator_eq_top_of_standardSetting hset.standardSetting) ht hLt hCN hKt
      (not_forall_commute_sylow_conj_plus hset (by norm_num) hK hq e htC ht)
      (autU2_plus_of_mulEquiv e (by norm_num)) habel
  refine ⟨x, z, hz, hxz, ⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩, hact⟩
  · exact isLongRoot_of_commute_sylow_plus_of_mulEquiv e (by norm_num) U
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU u hu)
  · exact isLongRoot_of_commute_sylow_plus_of_mulEquiv ((conjugateMulEquiv L x).symm.trans e)
      (by norm_num) U' (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU' u hu)

theorem not_normal_neighbour_pairTorus_of_twoSided_four (hlevi : PlusFourLeviInput)
    (hF6 : PlusFourRefinedF6Input) (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹)
    (k : Fin 4) {X D : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by norm_num : 3 ≤ 4) k
  obtain ⟨hz₀D, hz₀L, hF3, hQz, hMN, hQM, hM, hJ⟩ := plusRootElt_decomp_four hlevi hq hij hik hjk
  have hF6' := hF6 K hq i j k hij hik hjk
  set z₀ := plusRootElt K (by norm_num) hij hik hjk with hz₀
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩, hact⟩ := hR5
  obtain ⟨g, hg, w', hw', hact', hgw⟩ := exists_recentred_of_twoSided e htC hzL hzx hxz hact
    (isConj_of_isLongRoot_plus (by norm_num) hzl hz₀L)
  have hconj : IsConj (e ⟨g * w' * g⁻¹, hw'⟩) z₀ := by
    have hw : (⟨g * w' * g⁻¹, hw'⟩ : L) = (conjugateMulEquiv L x).symm ⟨z, hzx⟩ := by
      apply (conjugateMulEquiv L x).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [coe_conjugateMulEquiv]
      change x⁻¹ * (g * w' * g⁻¹) * x = z
      rw [hgw]
      group
    rw [hw]
    exact isConj_of_isLongRoot_plus (by norm_num) hzl' hz₀L
  have hOut := isSolvable_outer_of_mulEquiv_plus (by norm_num)
    (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc e
  have hKt := inf_centralizer_eq_zpowers_plus hset (by norm_num) hKc e htC ht
  obtain ⟨P, hP, hPD⟩ := EPilot.exists_le_centralizer_mulEquiv_of_conj_eq_mul_single_of_isConj
    hset.standardSetting hOut e ht hKt hg ⟨w', hw', hact', hconj⟩ (plusRadical K i j)
    (plusLevi K i j) hF3 hQz hMN hQM hM hJ (odd_card_pairTorus hKc k) hF6'
  obtain ⟨-, htX, -, -, -, -, hDC, hDq, hZD, -, hOutD⟩ :=
    neighbour_data_pairTorus_four hKc hq k e htC hX hDe
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting_four hset hKc hq k e htC ht hX htX hDe
  have hyD : (e.symm z₀ : G) ∈ D := by
    rw [hDe]
    exact ⟨e.symm z₀, ⟨z₀, hz₀D, rfl⟩, rfl⟩
  have hy1 : (e.symm z₀ : G) ≠ 1 := by
    intro h1
    have h2 : e.symm z₀ = 1 := Subtype.ext h1
    rw [MulEquiv.symm_apply_eq, map_one] at h2
    exact rootPairElt_ne_one _ _ _ _ h2
  have hP' : P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm z₀ : G)} : Set G) := by
    rw [hX, ← hg]
    exact hP
  have hPD' : Nonempty (P ≃* D) := by
    obtain ⟨ePD⟩ := hPD
    subst hDe
    exact ⟨ePD.trans (LinearPilot.mapSymmMulEquiv e (pairPerp (K := K) k)).symm⟩
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht (hDC.trans inf_le_left)
    ⟨hDq.1.commutator_eq_top, hDq.2.1⟩ hZD hOutD (hDC.trans inf_le_right) hsyl hyD hy1
    (Or.inr rfl) hP' hPD'

theorem not_normal_neighbour_pairTorus_of_habel_four (hlevi : PlusFourLeviInput)
    (hF6 : PlusFourRefinedF6Input) (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L)
    (k : Fin 4) {X D : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hKt := inf_centralizer_eq_zpowers_plus hset (by norm_num) hKc e htC ht
  exact not_normal_neighbour_pairTorus_of_twoSided_four hlevi hF6 hset hKc hq e htC ht
    (exists_conj_eq_mul_longRoot_twoSided_plus_of_habel_four hset hKc hq e ht hKt habel) k hX
    hDe

end Main

end CFSG.SeitzReduction.OmegaPilot
