module

public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenter
public import CFSG.CharacterTheory.Wreathed.FullCenterOddCore
public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public noncomputable section

namespace CFSG.Semidihedral.Principal.DegreeThreeReducedCentralizer

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Wreathed.DegreeThreeModelFullCenter

universe u v

section Generic

theorem oddCore_eq_N {G : Type u} [Group G] (t : G) : CFSG.oddCore (C t) = N t :=
  CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore (C t)

theorem oddCore_le_NZ {G : Type u} [Group G] (t : G) : CFSG.oddCore (C t) ≤ NZ t :=
  (oddCore_eq_N t).le.trans le_sup_left

theorem orderOf_mk_tInC {G : Type u} [Group G] [Finite G] (t : G) (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' (CFSG.oddCore (C t)) (tInC t)) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC : orderOf (tInC t) = 2 :=
    (orderOf_injective (C t).subtype Subtype.val_injective (tInC t)).symm.trans ht
  apply orderOf_eq_prime
  · rw [← map_pow, ← htC, pow_orderOf_eq_one, map_one]
  · intro h1
    have hmem : tInC t ∈ CFSG.oddCore (C t) := (QuotientGroup.eq_one_iff _).mp h1
    have hdvd : 2 ∣ Nat.card (CFSG.oddCore (C t)) := by
      rw [← htC, ← Subgroup.orderOf_mk (tInC t) hmem]
      exact orderOf_dvd_natCard _
    exact (Nat.not_even_iff_odd.mpr (CFSG.Wreathed.weakClosure_oddCore_card (C t)))
      (even_iff_two_dvd.mpr hdvd)

theorem center_eq_map_NZ {G : Type u} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    (hZ : Nat.card (Subgroup.center (C t ⧸ CFSG.oddCore (C t))) ∣ 2) :
    Subgroup.center (C t ⧸ CFSG.oddCore (C t)) =
      (NZ t).map (QuotientGroup.mk' (CFSG.oddCore (C t))) := by
  have hmap : (NZ t).map (QuotientGroup.mk' (CFSG.oddCore (C t))) =
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore (C t)) (tInC t)) := by
    change (N t ⊔ Subgroup.zpowers (tInC t)).map _ = _
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← oddCore_eq_N, QuotientGroup.map_mk'_self,
      bot_sup_eq]
  have hle : Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore (C t)) (tInC t)) ≤
      Subgroup.center (C t ⧸ CFSG.oddCore (C t)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore (C t)) y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (tInC_central t) x]
  rw [hmap]
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers, orderOf_mk_tInC t ht]
  exact Nat.le_of_dvd two_pos hZ

@[expose] def reducedFullCenterEquivGamma {G : Type} [Group G] [Finite G] (t : G)
    (ht : orderOf t = 2) (hZ : Nat.card (Subgroup.center (C t ⧸ CFSG.oddCore (C t))) ∣ 2) :
    reducedFullCenter (C t) ≃* Gamma t :=
  (QuotientGroup.quotientMulEquivOfEq (center_eq_map_NZ t ht hZ)).trans
    (QuotientGroup.quotientQuotientEquivQuotient (CFSG.oddCore (C t)) (NZ t) (oddCore_le_NZ t))

theorem card_center_dvd_two {X : Type u} [Group X] [Finite X] (m : ℕ)
    (hm : Nat.card (Subgroup.center (X ⧸ CFSG.oddCore X)) ∣ m) (h4 : ¬ 4 ∣ m) :
    Nat.card (Subgroup.center (X ⧸ CFSG.oddCore X)) ∣ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := CFSG.Wreathed.center_isTwoGroup_of_oddCore_eq_bot (X ⧸ CFSG.oddCore X)
    (CFSG.Wreathed.weakClosure_oddCore_quotient_eq_bot X)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  rw [hn] at hm ⊢
  have hn1 : n ≤ 1 := by
    by_contra hlt
    exact h4 ((pow_dvd_pow 2 (by omega : 2 ≤ n)).trans hm)
  simpa only [pow_one] using pow_dvd_pow 2 hn1

theorem card_reduced_center_of_equiv {G : Type u} {G' : Type v} [Group G] [Group G']
    [Finite G] (e : G ≃* G') (t : G) :
    Nat.card (Subgroup.center (C t ⧸ CFSG.oddCore (C t))) =
      Nat.card (Subgroup.center (C (e t) ⧸ CFSG.oddCore (C (e t)))) := by
  let : Finite G' := Finite.of_equiv G e.toEquiv
  let a := CFSG.Wreathed.DegreeThreeModelFullCenter.originalCentralizerEquiv e t
  have hker : Odd (Nat.card a.toMonoidHom.ker) := by
    rw [a.toMonoidHom.ker_eq_bot a.injective, Subgroup.card_bot]
    decide
  let theta := CFSG.Wreathed.ReducedCentralizerInclusion.reducedSurjectionEquiv
    a.toMonoidHom a.surjective hker
  rw [← Subgroup.map_center_eq theta]
  exact (Subgroup.card_map_of_injective theta.injective).symm

end Generic

section Linear

open CFSG.Wreathed.OddLinearThreeCentralizerCore

theorem linear_reduced_center_card_dvd (F : Type) [Field F] [Finite F]
    (hFodd : Odd (Nat.card F)) (hF4 : 4 ≤ Nat.card F)
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (t : SL3 F ⧸ D) (ht : orderOf t = 2) :
    Nat.card (Subgroup.center (C t ⧸ CFSG.oddCore (C t))) ∣ Nat.card F - 1 := by
  have hq : 3 ≤ Nat.card F := by omega
  obtain ⟨z, ⟨hz, hzt⟩, _⟩ := unique_involution_lift F D hD t ht
  let P := minusSpace (matrixAction F z).toLinearMap
  have hP : Module.finrank F P = 2 := (matrixAction_finrank F hFodd z hz).1
  let b := Module.finBasisOfFinrankEq F P hP
  let B : Subgroup (GeneralLinearGroup (Fin 2) F) := ⊤
  let phi := linearMatrixTargetHom F hFodd D z hz t hzt b
  have hphi := linearMatrixTargetHom_surjective F hFodd D hD z hz t hzt b
  have hcomap := reducedTargetHom_full_center_comap hF4 (RingHom.id F)
    (1 : GeneralLinearGroup (Fin 2) F) B le_top phi hphi
    (linearMatrixTargetHom_ker_le_odd_scalars F hFodd D hD z hz t hzt b)
    (linearMatrixTargetHom_oddCore F hFodd hq D hD z hz t hzt b)
  have hmap := Subgroup.map_comap_eq_self_of_surjective
    (reducedTargetHom_surjective phi hphi) (Subgroup.center _)
  rw [hcomap] at hmap
  rw [← hmap, ← card_linearMatrixScalars F]
  exact Subgroup.card_map_dvd _ _

end Linear

section Unitary

open CFSG.ComponentClassification CatalogueBUnitaryIsometry CatalogueBUnitaryTwo
open CFSG.Wreathed.OddUnitaryThreeCentralizerCore CFSG.Wreathed.OddLinearThreeCentralizerCore
open CFSG.Semidihedral.OddLinearNormals

theorem unitary_reduced_center_card_dvd {E V : Type} [Field E] [Finite E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (p f : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hq : 5 ≤ p ^ f) (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) [D.Normal] (hD : D ≤ scalarCenter h hdim)
    (t : specialIsometry h ⧸ D) (ht : orderOf t = 2) :
    Nat.card (Subgroup.center (C t ⧸ CFSG.oddCore (C t))) ∣ p ^ f + 1 := by
  let : Finite (isometryGroup h) := isometryGroup_finite h
  let sigma := unitaryFieldConjugation p f hE
  let h2 := unitaryField_two_ne_zero p f hpodd hE
  let hsigma := (unitaryFieldConjugation_data p f hE).1
  let hne := (unitaryFieldConjugation_data p f hE).2.1
  obtain ⟨z, ⟨hz, hzt⟩, _⟩ :=
    CFSG.Wreathed.OddUnitaryThreeCentralizerCore.unique_involution_lift h hdim D hD t ht
  let P := minusSpace z.val.val.toLinearMap
  let hP := h.domRestrict₁₂ P P
  have hPdim : Module.finrank E P = 2 := (involution_finrank h h2 hdim z hz).1
  have hPnd : hP.Nondegenerate := (involution_restrictions h h2 hsym hnd z hz).1
  obtain ⟨hFcard, B, d, eSU, _, _, _, _, hinverse⟩ :=
    unitary_field_two_special_linear_isomorphism p f hE hP (hsym.domRestrict P) hPnd hPdim
  let F := CatalogueBLinearTwoDescent.fixedSubfield E sigma
  let U := (unitaryPlaneMatrixHom hP B).range
  have hSU : conjugatedImageSL F.subtype (diagonalGL d) ≤ U :=
    unitaryPlaneMatrixHom_contains_special hP B d eSU hinverse
  let phi := unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B
  have hphi := unitaryMatrixTargetHom_surjective h h2 hsym hnd hsigma hne hdim D hD z hz t hzt B
  have hF4 : 4 ≤ Nat.card F := by rw [hFcard]; omega
  have hcomap := reducedTargetHom_full_center_comap hF4 F.subtype (diagonalGL d) U hSU phi hphi
    (unitaryMatrixTargetHom_ker_le_odd_scalars h h2 hsym hnd hsigma hne hdim D hD z hz t hzt B)
    (unitaryMatrixTargetHom_oddCore p f hpodd hE h hsym hnd hdim D hD z hz t hzt B)
  have hmap := Subgroup.map_comap_eq_self_of_surjective
    (reducedTargetHom_surjective phi hphi) (Subgroup.center _)
  rw [hcomap] at hmap
  rw [← hmap, ← card_unitaryMatrixScalars p f hE hP hPnd B]
  exact Subgroup.card_map_dvd _ _

end Unitary

theorem stated_reduced_center_card_dvd_two (G : Type) [Group G] (tau : StatedLieTag)
    (htau : tau = .PSL ∨ tau = .PSU) (p f : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hq : 5 ≤ p ^ f) (hmodel : StatedClassicalModel G tau 3 p f)
    (hcong : (tau = .PSL → p ^ f % 4 = 3) ∧ (tau = .PSU → p ^ f % 4 = 1))
    (t : G) (ht : orderOf t = 2) :
    Nat.card (Subgroup.center (C t ⧸ CFSG.oddCore (C t))) ∣ 2 := by
  let : Finite G := originalDegreeThreeModel_finite G p f tau htau hmodel
  rcases htau with rfl | rfl
  · have h3 := hcong.1 rfl
    obtain ⟨_, F, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
    let e := eModel.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
    have ht' : orderOf (e t) = 2 := (orderOf_injective e.toMonoidHom e.injective t).trans ht
    have hFodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
    have hF4 : 4 ≤ Nat.card F := by rw [hcard]; omega
    have hdvd := linear_reduced_center_card_dvd F hFodd hF4
      (Subgroup.center (SpecialLinearGroup (Fin 3) F)) le_rfl (e t) ht'
    rw [card_reduced_center_of_equiv e t]
    exact card_center_dvd_two _ hdvd (by rw [hcard]; omega)
  · have h1 := hcong.2 rfl
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨_, E, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
    let h := originalIdentityForm p f hcard
    let : Finite (CFSG.ComponentClassification.CatalogueBUnitaryIsometry.isometryGroup h) :=
      CFSG.Wreathed.OddUnitaryThreeCentralizerCore.isometryGroup_finite h
    let D := CFSG.Wreathed.OddUnitaryThreeCentralizerCore.scalarCenter h
      (Module.finrank_fin_fun E)
    let : D.Normal := CFSG.Wreathed.OddUnitaryThreeCentralizerCore.scalar_subgroup_normal h
      (Module.finrank_fin_fun E) D le_rfl
    let e := eModel.trans (originalIdentityProjectiveEquiv p f hcard).symm
    have ht' : orderOf (e t) = 2 := (orderOf_injective e.toMonoidHom e.injective t).trans ht
    have hdvd := unitary_reduced_center_card_dvd p f hpodd hq hcard h
      (originalIdentityForm_isSymm p f hcard) (originalIdentityForm_nondegenerate p f hcard)
      (Module.finrank_fin_fun E) D le_rfl (e t) ht'
    rw [card_reduced_center_of_equiv e t]
    exact card_center_dvd_two _ hdvd (by omega)

end CFSG.Semidihedral.Principal.DegreeThreeReducedCentralizer
