module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueL34
public import CFSG.LocalAnalysis.ComponentClassification.GS82HLargeDatum
public import CFSG.LocalAnalysis.ComponentClassification.GS82HDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatInner
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.Residue

open CFSG Subgroup CFSG.Semidihedral.Principal
open scoped commutatorElement MatrixGroups

theorem apply_mem_fusionZStar {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A}
    (ha : a ∈ Open.fusionZStar A) : e a ∈ Open.fusionZStar B := by
  rw [GSThmB.OddQuot.mem_fusionZStar_iff] at ha ⊢
  intro m
  have h1 := Subgroup.mem_map_of_mem e.toMonoidHom (ha (e.symm m))
  rw [pPrimeCore_map_iso 2 e] at h1
  have h2 : e.toMonoidHom ⁅a, e.symm m⁆ = ⁅e a, m⁆ := by
    rw [MulEquiv.coe_toMonoidHom, map_commutatorElement, MulEquiv.apply_symm_apply]
  rwa [h2] at h1

theorem oddLieType_center_quot_of_isSLTwoOver {q : ℕ} {A : Type} [Group A]
    (h : HarrisLit.IsSLTwoOver q A) (hq : Odd q) (h5 : 5 ≤ q) :
    Blueprint.OddLieType (A ⧸ center A) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨p, hchar⟩ := CharP.exists F
  obtain ⟨f, hp, hcard⟩ := FiniteField.card F p
  have hq' : q = p ^ (f : ℕ) := hF.symm.trans hcard
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hq'] at hq
    exact Nat.not_even_iff_odd.mpr hq ((Nat.even_pow' f.ne_zero).mpr even_two)
  have hF' : Nat.card F = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have e' : A ⧸ center A ≃* PSL(2, F) :=
    QuotientGroup.congr (center A) (center (Matrix.SpecialLinearGroup (Fin 2) F)) e
      (Subgroup.map_center_eq e)
  have hm := GH74.Generic.BProg.B2.L2Cover.lieModel_psl2_of_equiv hp f.pos hF' (by omega)
    (by omega) e'
  exact ⟨.PSL, 2, p, f, hp, hp2, hm.admissible, hm⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem card_center_eq_sixteen_of_twoGroup
    (hP11 : L34CentralSLTwoFact) (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y))
    (hL : GH74.GLS.IsL34Quotient (Y ⧸ pPrimeCore 2 Y)) {A : Type} [Group A] [Finite A]
    (hA : IsPGroup 2 A) (α : A →* MulAut Y) {F : Subgroup Y}
    (hF : ∀ y, y ∈ F ↔ ∀ a, α a y = y) {T : Subgroup Y} (hTF : T ≤ F)
    (hT : IsPComponent 2 (T.subgroupOf F)) {q₀ : ℕ} (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ))
    (hSL : HarrisLit.IsSLTwoOver q₀ (↥T ⧸ pPrimeCore 2 ↥T)) {w : Y} (hw : orderOf w = 2)
    (hwT : w ∈ T) (hwZ : w ∈ Open.fusionZStar Y) :
    Nat.card ↥(center (Y ⧸ pPrimeCore 2 Y)) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hYO : pPrimeCore 2 (Y ⧸ O) = ⊥ := GH74.GLS.pPrimeCore_quotient_eq_bot Y
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hαO : ∀ a : A, ∀ n ∈ O, α a n ∈ O := by
    intro a n hn
    have hOmap : O.map (α a).toMonoidHom = O :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance (α a)
    exact hOmap ▸ mem_map_of_mem _ hn
  set ρ := CoprimeFixedPoint.quotientAction α O hαO with hρ
  have hρmk : ∀ a y, ρ a (π y) = π (α a y) := fun a y => rfl
  by_cases htriv : ∀ a : A, ρ a = 1
  ·
    exfalso
    have hcov := coprime_fixed_point_lifting 2 hA α O hαO
      (fun h => Nat.not_even_iff_odd.mpr hOodd (even_iff_two_dvd.mpr h))
    have hsurj : Function.Surjective (π.comp F.subtype) := by
      intro y
      have hy : y ∈ {q : Y ⧸ O | ∀ a : A, CoprimeFixedPoint.quotientAction α O hαO a q = q} :=
        fun a => by rw [← hρ, htriv a, MulAut.one_apply]
      rw [hcov] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨⟨c, (hF c).mpr hc⟩, rfl⟩
    obtain ⟨e⟩ := nonempty_quot_equiv_of_map_eq_top (map_eq_top_of_surjective hYq hsurj hTF hT)
    have h1 : Nat.card (Y ⧸ O) = q₀ * (q₀ ^ 2 - 1) := by
      rw [← Nat.card_congr e.toEquiv]
      exact card_of_isSLTwoOver hSL
    have h2 : 20160 ∣ Nat.card (Y ⧸ O) := by
      rw [← card_of_l34 hL, Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Y ⧸ O))]
      exact dvd_mul_right _ _
    rw [h1] at h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    rcases hq₀ with rfl | rfl | rfl <;> exact absurd h2 (by decide)
  obtain ⟨a, ha⟩ := not_forall.mp htriv
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hA) a
  have hdvd : orderOf (ρ a) ∣ 2 ^ m := hm ▸ orderOf_map_dvd ρ a
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact ha hj
  have h2 : 2 ∣ orderOf (ρ a) := hj ▸ dvd_pow_self 2 hj0
  set k := orderOf (ρ a) / 2 with hk
  set σ := ρ (a ^ k) with hσdef
  have hσ2 : orderOf σ = 2 := by
    rw [hσdef, map_pow]
    exact orderOf_pow_orderOf_div (by rw [hj]; positivity) h2
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y
    have h1 := pow_orderOf_eq_one σ
    rw [hσ2] at h1
    rw [← MulAut.mul_apply, ← pow_two, h1, MulAut.one_apply]
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ2
    exact absurd hσ2 (by norm_num)
  set N := T.map π with hN
  have hNC : N ≤ FixedCommutingProduct.fixedSubgroup σ := by
    rintro _ ⟨t, ht, rfl⟩
    change σ (π t) = π t
    rw [hσdef, hρmk, (hF t).mp (hTF ht)]
  let πT : ↥T →* ↥N := (π.comp T.subtype).codRestrict N fun t => ⟨t, t.2, rfl⟩
  have hπT : Function.Surjective πT := by
    rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hπTodd : Odd (Nat.card πT.ker) := by
    have hk' : πT.ker = (π.domRestrict T).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk']
    exact OddKernel.odd_card_restriction_kernel π (by rw [QuotientGroup.ker_mk']; exact hOodd) T
  obtain ⟨eN⟩ := DPrime.nonempty_coreQuotEquiv_of_surjective πT hπT hπTodd
  have hNSL : HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) :=
    DPrime.isSLTwoOver_of_coreEquiv eN hSL
  have hwZ' : π w ∈ center (Y ⧸ O) := by
    rw [Sol78.fusionZStar_eq_comap] at hwZ
    exact hwZ
  have hw2 : orderOf (π w) = 2 := GH74.GLS.TwoThin.orderOf_barMk hw
  exact (hP11 (Y ⧸ O) hYq (Sol78.center_isPGroup_two hYO) hL σ hσσ hσ1 N hNC q₀ hq₀ hNSL (π w)
    hw2 ⟨w, hwT, rfl⟩ hwZ').2

variable {X : Type} [Group X] [Finite X]

end CFSG.ComponentClassification.GS82PumpInputs.Residue
