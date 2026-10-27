module

public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterProjective
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterTransport
public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore

public noncomputable section

namespace CFSG.Wreathed.DegreeThreeModelFullCenter

open Matrix CFSG.Semidihedral.OddLinearNormals
open CFSG.Assembly.LowTwoRank

universe u v w

theorem centralizer_map_eq_bot_of_equiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (Q : Subgroup G)
    (hC : Subgroup.centralizer (Q : Set G) = ⊥) :
    Subgroup.centralizer ((Q.map (e : G →* H) : Subgroup H) : Set H) = ⊥ := by
  apply le_bot_iff.mp
  intro h hh
  have hc : e.symm h ∈ Subgroup.centralizer (Q : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hh (e x) (Subgroup.mem_map_of_mem (e : G →* H) hx)
  rw [hC, Subgroup.mem_bot] at hc
  rw [Subgroup.mem_bot]
  simpa only [e.apply_symm_apply, map_one] using congrArg e hc

theorem generalizedFitting_eq_map_of_simple_equiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite H]
    (e : G ≃* H) [IsSimpleGroup (CFSG.generalizedFitting G)]
    (hab : ∃ x y : CFSG.generalizedFitting G, x * y ≠ y * x)
    (hC : Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥) :
    CFSG.generalizedFitting H = (CFSG.generalizedFitting G).map (e : G →* H) := by
  let Q := CFSG.generalizedFitting G
  let theta := e.subgroupMap Q
  let : IsSimpleGroup (Q.map (e : G →* H)) := theta.symm.isSimpleGroup
  have hnonab : ∃ x y : Q.map (e : G →* H), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hab
    refine ⟨theta x, theta y, fun h => hxy (theta.injective ?_)⟩
    simpa only [map_mul] using h
  exact generalizedFitting_eq_of_selfCentralizing_simple_normal _
    ((CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2.map
      (e : G →* H) e.surjective) hnonab (centralizer_map_eq_bot_of_equiv e Q hC)

@[expose] def generalizedFittingSimpleEquiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite H]
    (e : G ≃* H) [IsSimpleGroup (CFSG.generalizedFitting G)]
    (hab : ∃ x y : CFSG.generalizedFitting G, x * y ≠ y * x)
    (hC : Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥) :
    CFSG.generalizedFitting G ≃* CFSG.generalizedFitting H :=
  (e.subgroupMap (CFSG.generalizedFitting G)).trans
    (MulEquiv.subgroupCongr (generalizedFitting_eq_map_of_simple_equiv e hab hC).symm)

theorem statedPSLModel_of_equiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (n p f : ℕ) (hmodel : StatedClassicalModel G .PSL n p f) :
    StatedClassicalModel H .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hmodel

theorem full_large_conclusions_of_equiv {G H : Type} [Group G] [Group H] [Finite H]
    (e : G ≃* H) (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hq : 5 ≤ p ^ f)
    (hG : IsSimpleGroup (CFSG.generalizedFitting G) ∧
      (∃ x y : CFSG.generalizedFitting G, x * y ≠ y * x) ∧
      Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥ ∧
      (CFSG.generalizedFitting G).index = 2 ∧
      StatedClassicalModel (CFSG.generalizedFitting G) .PSL 2 p f) :
    let L := CFSG.generalizedFitting H
    IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      Subgroup.centralizer (L : Set H) = ⊥ ∧ L.index = 2 ∧
      StatedClassicalModel L .PSL 2 p f ∧ Nat.card L = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∀ (r a : ℕ), r.Prime → Odd r → 1 ≤ a → StatedClassicalModel L .PSL 2 r a →
        r ^ a = p ^ f ∧ r = p ∧ a = f := by
  dsimp only
  let : IsSimpleGroup (CFSG.generalizedFitting G) := hG.1
  let theta := generalizedFittingSimpleEquiv e hG.2.1 hG.2.2.1
  let : IsSimpleGroup (CFSG.generalizedFitting H) := theta.symm.isSimpleGroup
  have hab : ∃ x y : CFSG.generalizedFitting H, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hG.2.1
    refine ⟨theta x, theta y, fun h => hxy (theta.injective ?_)⟩
    simpa only [map_mul] using h
  have hmodel := statedPSLModel_of_equiv theta 2 p f hG.2.2.2.2
  have hparams := ProjectiveTwoParameterUniqueness.stated_psl_two_order_and_parameter_uniqueness
    (CFSG.generalizedFitting H) p f hp hpodd hf hq hmodel
  refine ⟨inferInstance, hab, ?_, ?_, hmodel, hparams.2.1, hparams.2.2⟩
  · rw [generalizedFitting_eq_map_of_simple_equiv e hG.2.1 hG.2.2.1]
    exact centralizer_map_eq_bot_of_equiv e _ hG.2.2.1
  · rw [generalizedFitting_eq_map_of_simple_equiv e hG.2.1 hG.2.2.1,
      Subgroup.index_map_equiv]
    exact hG.2.2.2.1

section OriginalLinearPlane

variable (F : Type u) [Field F] {V : Type v} [AddCommGroup V] [Module F V]

@[expose] def linearPlaneEquiv (b : Module.Basis (Fin 2) F V) :
    (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)) ≃* (V ≃ₗ[F] V) :=
  Subgroup.topEquiv.trans (OddLinearTwoAutomorphisms.matrixEquiv F V b)

theorem linearPlaneEquiv_scalar (b : Module.Basis (Fin 2) F V) (c : Fˣ) :
    linearPlaneEquiv F b (linearMatrixScalarHom F c) =
      OddLinearTwoAutomorphisms.scalarHom F V c :=
  OddLinearTwoAutomorphisms.matrixEquiv_scalar F V b c

theorem linearPlaneEquiv_comp_scalars (b : Module.Basis (Fin 2) F V) :
    (linearPlaneEquiv F b).toMonoidHom.comp (linearMatrixScalarHom F) =
      OddLinearTwoAutomorphisms.scalarHom F V := by
  apply MonoidHom.ext
  intro c
  exact linearPlaneEquiv_scalar F b c

end OriginalLinearPlane

section OriginalLinearThree

open OddLinearThreeCentralizerCore

variable (F : Type u) [Field F] [Finite F]

@[expose] def linearMatrixTargetHom (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (z : SL3 F) (hz : orderOf z = 2)
    (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (b : Module.Basis (Fin 2) F (minusSpace (matrixAction F z).toLinearMap)) :
    (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)) →*
      Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)) :=
  (targetQuotientCentralizer F hF D z hz t hzt).comp (linearPlaneEquiv F b).toMonoidHom

theorem linearMatrixTargetHom_coe (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (z : SL3 F) (hz : orderOf z = 2)
    (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (b : Module.Basis (Fin 2) F (minusSpace (matrixAction F z).toLinearMap))
    (a : (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F))) :
    (linearMatrixTargetHom F hF D z hz t hzt b a : SL3 F ⧸ D) =
      QuotientGroup.mk' D (matrixCentralizerEquiv F hF z hz (linearPlaneEquiv F b a)) :=
  targetQuotientCentralizer_coe F hF D z hz t hzt _

theorem linearMatrixTargetHom_surjective (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (b : Module.Basis (Fin 2) F (minusSpace (matrixAction F z).toLinearMap)) :
    Function.Surjective (linearMatrixTargetHom F hF D z hz t hzt b) :=
  (targetQuotientCentralizer_surjective F hF D hD z hz t hzt).comp
    (linearPlaneEquiv F b).surjective

theorem linearMatrixTargetHom_ker_le_odd_scalars (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (b : Module.Basis (Fin 2) F (minusSpace (matrixAction F z).toLinearMap)) :
    (linearMatrixTargetHom F hF D z hz t hzt b).ker ≤
      oddScalarSubgroup (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)) := by
  let phi := linearMatrixTargetHom F hF D z hz t hzt b
  have ho : Odd (Nat.card phi.ker) := by
    dsimp only [phi]
    rw [linearMatrixTargetHom, ← MonoidHom.comap_ker]
    have hk : Odd (Nat.card (targetQuotientCentralizer F hF D z hz t hzt).ker) := by
      rw [targetQuotientCentralizer_ker]
      exact matrixQuotientKernel_odd F hF D hD z hz
    exact hk.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _
      (linearPlaneEquiv F b).toMonoidHom (linearPlaneEquiv F b).injective)
  have hs : phi.ker ≤ (linearMatrixScalarHom F).range := by
    intro a ha
    have hk : linearPlaneEquiv F b a ∈
        (targetQuotientCentralizer F hF D z hz t hzt).ker := ha
    rw [targetQuotientCentralizer_ker] at hk
    obtain ⟨c, hc⟩ := matrixQuotientKernel_le_scalars F hF D hD z hz hk
    refine ⟨c, (linearPlaneEquiv F b).injective ?_⟩
    exact (linearPlaneEquiv_scalar F b c).trans hc
  rw [oddScalarSubgroup_eq_map _ _ (linearMatrixScalarHom_injective F)
    (linearMatrixScalarHom_range F)]
  exact CyclicOddScalarQuotient.ker_le_oddScalarImage (linearMatrixScalarHom F)
    (linearMatrixScalarHom_injective F) phi ho hs

theorem linearMatrixTargetHom_oddCore (hF : Odd (Nat.card F)) (hq : 3 ≤ Nat.card F)
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (b : Module.Basis (Fin 2) F (minusSpace (matrixAction F z).toLinearMap)) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) =
      (oddScalarSubgroup (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F))).map
        (linearMatrixTargetHom F hF D z hz t hzt b) := by
  rw [oddScalarSubgroup_eq_map _ _ (linearMatrixScalarHom_injective F)
    (linearMatrixScalarHom_range F), Subgroup.map_map]
  have he : (linearMatrixTargetHom F hF D z hz t hzt b).comp (linearMatrixScalarHom F) =
      (targetQuotientCentralizer F hF D z hz t hzt).comp
        (OddLinearTwoAutomorphisms.scalarHom F (minusSpace (matrixAction F z).toLinearMap)) := by
    rw [linearMatrixTargetHom, MonoidHom.comp_assoc, linearPlaneEquiv_comp_scalars]
  rw [he, ← Subgroup.map_map]
  exact (targetQuotientCentralizer_core_structure F hF hq D hD z hz t hzt).1

end OriginalLinearThree

open OddLinearThreeCentralizerCore

@[expose] def localQuotientConclusions (p f : ℕ) (Gamma : Type) [Group Gamma] : Prop :=
  (p ^ f = 3 → Group.IsSolvable Gamma ∧ Nat.card Gamma = 24) ∧
  (5 ≤ p ^ f →
    let L := CFSG.generalizedFitting Gamma
    IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      Subgroup.centralizer (L : Set Gamma) = ⊥ ∧ L.index = 2 ∧
      StatedClassicalModel L .PSL 2 p f ∧ Nat.card L = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∀ (r a : ℕ), r.Prime → Odd r → 1 ≤ a → StatedClassicalModel L .PSL 2 r a →
        r ^ a = p ^ f ∧ r = p ∧ a = f)

abbrev reducedFullCenter (C : Type) [Group C] :=
  (C ⧸ CFSG.oddCore C) ⧸ Subgroup.center (C ⧸ CFSG.oddCore C)

theorem linear_three_target_full_center_quotient_conclusions
    (F : Type) [Field F] [Finite F] (p f : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (t : SL3 F ⧸ D) (ht : orderOf t = 2) :
    localQuotientConclusions p f
      (reducedFullCenter (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)))) := by
  have hFodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hpne : p ≠ 2 := by rintro rfl; norm_num at hpodd
    omega
  have hq : 3 ≤ Nat.card F := by
    rw [hcard]
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨z, ⟨hz, hzt⟩, _⟩ := unique_involution_lift F D hD t ht
  let P := minusSpace (matrixAction F z).toLinearMap
  have hP : Module.finrank F P = 2 := (matrixAction_finrank F hFodd z hz).1
  let b := Module.finBasisOfFinrankEq F P hP
  let B : Subgroup (GeneralLinearGroup (Fin 2) F) := ⊤
  let phi := linearMatrixTargetHom F hFodd D z hz t hzt b
  have hphi := linearMatrixTargetHom_surjective F hFodd D hD z hz t hzt b
  have hk := linearMatrixTargetHom_ker_le_odd_scalars F hFodd D hD z hz t hzt b
  have hc := linearMatrixTargetHom_oddCore F hFodd hq D hD z hz t hzt b
  have hB := card_linearMatrixGroup F
  constructor
  · intro hthree
    have hF3 : Nat.card F = 3 := hcard.trans hthree
    let e := reducedTargetFullCenterEquivOfTwoPower (RingHom.id F)
      (1 : GeneralLinearGroup (Fin 2) F) B le_top 1
      (by rw [card_linearMatrixScalars, hF3]; rfl) phi hphi hk hc
    obtain ⟨hsolv, horder⟩ := matrix_overgroup_scalar_quotient_three hF3
      (RingHom.id F) (1 : GeneralLinearGroup (Fin 2) F) B le_top hB
    let : Group.IsSolvable (B ⧸ scalarSubgroup B) := hsolv
    exact ⟨Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective,
      (Nat.card_congr e.symm.toEquiv).trans horder⟩
  · intro hlarge
    have hF4 : 4 ≤ Nat.card F := by rw [hcard]; omega
    let e := reducedTargetFullCenterEquiv hF4 (RingHom.id F)
      (1 : GeneralLinearGroup (Fin 2) F) B le_top phi hphi hk hc
    have hm := matrix_overgroup_generalizedFitting_full_conclusions p f hp hpodd hf hlarge
      hcard (RingHom.id F) (1 : GeneralLinearGroup (Fin 2) F) B le_top hB
    exact full_large_conclusions_of_equiv e p f hp hpodd hf hlarge
      ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1⟩

end CFSG.Wreathed.DegreeThreeModelFullCenter
