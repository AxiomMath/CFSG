module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporBase
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatInner
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint
open scoped MatrixGroups

structure SL2Facts (T : Type*) [Group T] (t : T) : Prop where
  ne_one : t ≠ 1
  mul_self : t * t = 1
  mem_center : t ∈ center T
  card_center : Nat.card (center T) = 2
  unique : ∀ x : T, x * x = 1 → x = 1 ∨ x = t

theorem ringChar_ne_two_of_odd {K : Type*} [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    ringChar K ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  intro h
  have h2 := (FiniteField.even_card_iff_char_two (F := K)).1 h
  rw [Nat.card_eq_fintype_card] at hK
  rw [Nat.odd_iff] at hK
  omega

theorem sl2Facts_of_equiv {T : Type*} [Group T] {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (e : T ≃* SL(2, K)) : SL2Facts T (e.symm (-1)) := by
  have hk := ringChar_ne_two_of_odd hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk
  have hne : (-1 : SL(2, K)) ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h1
    apply h2
    linear_combination -h1
  refine ⟨fun h => hne ?_, ?_, ?_, ?_, fun x hx => ?_⟩
  · have := congrArg e h
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · rw [← map_mul, neg_one_mul, neg_neg, map_one]
  · rw [mem_center_iff]
    intro x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mul_neg_one, neg_one_mul]
  · rw [← (ABGLocalTools.card_center_sl2 hK), ← Subgroup.map_center_eq e,
      Subgroup.card_map_of_injective e.injective]
  · have h1 : (e x) ^ 2 = 1 := by rw [sq, ← map_mul, hx, map_one]
    rcases (LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hk (e x)).1 h1 with h | h
    · left
      rw [← e.symm_apply_apply x, h, map_one]
    · right
      rw [← e.symm_apply_apply x, h]

theorem exists_pow_four_eq_neg_one_of_card_nine {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 9) : ∃ A : SL(2, K), A ^ 4 = -1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  set a : K := (g : K) with hadef
  have ha0 : a ≠ 0 := g.ne_zero
  have ha8 : a ^ 8 = 1 := by
    rw [hadef, ← Units.val_pow_eq_pow_val, ← hord, pow_orderOf_eq_one, Units.val_one]
  have ha4 : a ^ 4 ≠ 1 := by
    intro h
    have h1 : g ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ← hadef, h, Units.val_one])
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    exact absurd this (by norm_num)
  have ha4' : a ^ 4 = -1 := by
    have h1 : (a ^ 4 - 1) * (a ^ 4 + 1) = 0 := by
      rw [show (a ^ 4 - 1) * (a ^ 4 + 1) = a ^ 8 - 1 by ring, ha8, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) ha4
    · exact eq_neg_of_add_eq_zero_left h
  have hinv4 : a⁻¹ ^ 4 = -1 := by rw [inv_pow, ha4', inv_neg, inv_one]
  have hdet : (Matrix.diagonal ![a, a⁻¹]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    exact mul_inv_cancel₀ ha0
  refine ⟨⟨Matrix.diagonal ![a, a⁻¹], hdet⟩, ?_⟩
  apply Subtype.ext
  change Matrix.diagonal ![a, a⁻¹] ^ 4 = -1
  rw [Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha4', hinv4]

theorem exists_sl2Facts (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers) {T : Type} [Group T] [Finite T]
    (hq : IsQuasisimple T) (hZ2 : IsPGroup 2 (center T)) (hZ : center T ≠ ⊥) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : LieModel (T ⧸ center T) .PSL 2 p f) :
    ∃ t : T, SL2Facts T t ∧ (p = 3 → f = 2 → ∃ w : T, w ^ 4 = t) := by
  obtain ⟨hf, hfact, ⟨e⟩⟩ := TBLit.psl_two_double_cover hGA hGC hq hZ2 hZ hp hp2 hL
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  refine ⟨e.symm (-1), sl2Facts_of_equiv hodd e, fun h3 h2 => ?_⟩
  subst h3 h2
  obtain ⟨A, hA⟩ := exists_pow_four_eq_neg_one_of_card_nine (K := GaloisField 3 2)
    (by rw [hcard]; norm_num)
  exact ⟨e.symm A, by rw [← map_pow, hA]⟩

theorem SL2Facts.eq_of_mem_center {T : Type*} [Group T] [Finite T] {t : T} (h : SL2Facts T t)
    {x : T} (hx : x ∈ center T) : x = 1 ∨ x = t := by
  have h1 : orderOf (⟨x, hx⟩ : center T) ∣ 2 := h.card_center ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact h.unique x (by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.1 h1)

theorem mem_center_of_rho_eq_one {Y : Type} [Group Y] (hO : pPrimeCore 2 Y = ⊥)
    {T : Subgroup Y} {x : T} (hx : rho Y x = 1) : x ∈ center T := by
  have hxZ : (x : Y) ∈ center Y := by
    rw [← ker_rho hO, MonoidHom.mem_ker]
    exact hx
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.mp hxZ y)

theorem SL2Facts.rho_injective {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {T : Subgroup Y} {t : T} (h : SL2Facts T t) (ht : rho Y t ≠ 1) {x : T}
    (hx : rho Y x = 1) : x = 1 := by
  rcases h.eq_of_mem_center (mem_center_of_rho_eq_one hO hx) with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hx) ht

theorem SL2Facts.orderOf_rho {Y : Type} [Group Y] {T : Subgroup Y} {t : T} (h : SL2Facts T t)
    (ht : rho Y t ≠ 1) : orderOf (rho Y t) = 2 :=
  orderOf_eq_prime (by rw [sq, ← map_mul, ← Subgroup.coe_mul, h.mul_self, Subgroup.coe_one,
    map_one]) ht

theorem SL2Facts.rho_commute {Y : Type} [Group Y] {T : Subgroup Y} {t : T} (h : SL2Facts T t)
    (x : T) : rho Y x * rho Y t = rho Y t * rho Y x := by
  rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
    (mem_center_iff.mp h.mem_center x).symm]

theorem SL2Facts.card_map_rho {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {T : Subgroup Y} {t : T} (h : SL2Facts T t) (ht : rho Y t = 1) :
    Nat.card T = 2 * Nat.card (T.map (rho Y)) := by
  set f := (rho Y).subgroupMap T
  have hker : f.ker = center T := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      exact mem_center_of_rho_eq_one hO (congrArg Subtype.val hx)
    · intro hx
      rcases h.eq_of_mem_center hx with rfl | rfl
      · exact map_one f
      · exact Subtype.ext ht
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    ((rho Y).subgroupMap_surjective T)).toEquiv, hker, h.card_center, mul_comm] at h1
  exact h1

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
