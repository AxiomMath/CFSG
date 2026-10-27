module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7Basic
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerPsi
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.E7Model
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

theorem card_center_spinPlus {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n) (h2 : (2 : F) ≠ 0)
    (he : Even n) : Nat.card (center (spinGroup (quadPlus n F))) = 4 := by
  have hc : center (spinGroup (quadPlus n F)) = SpinPlusClosed.scalarSpin n F :=
    (spinToStatedProj_quadPlus (K := F) hn).2.2.symm.trans (spinToStatedProj_quadPlus hn).2.1
  rw [hc]
  exact (SpinPlusClosed.isKleinFour_scalarSpin hn h2 he).card_four

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "M₁₂" =>
  CFSG.ClassicalInvolution.ModelFacts.modelUniv StatedLieTag.POmegaPlus 6 p f Fact.out

theorem spin12_facts (hp2 : p ≠ 2) (hf : f ≠ 0) :
    IsQuasisimple (M₁₂).K ∧ IsPGroup 2 (center (M₁₂).K) ∧
      Blueprint.LieModel ((M₁₂).K ⧸ center (M₁₂).K) .POmegaPlus 6 p f := by
  have hn : 3 ≤ 6 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.2 hf, by norm_num⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h : M₁₂ =
      ⟨spinGroup (quadPlus 6 (GaloisField p f)), plusDatum 6 (GaloisField p f) hn⟩ := by
    simp only [CFSG.ClassicalInvolution.ModelFacts.modelUniv, lieUniversal, hn, ↓reduceDIte]
  rw [h]
  obtain ⟨-, hQ, hL⟩ := (curtisTitsConclusion_spinPlus.{0} hadm hcard hn).1
  refine ⟨hQ, IsPGroup.of_card (n := 2) ?_, hL⟩
  exact card_center_spinPlus hn (two_ne_zero_galoisField f hp2) (by decide)

theorem hj_facts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    IsQuasisimple ↥(HJ p f) ∧ IsPGroup 2 (center ↥(HJ p f)) ∧
      Blueprint.LieModel (↥(HJ p f) ⧸ center ↥(HJ p f)) .POmegaPlus 6 p f := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨Ψ, hker, hrange, -⟩ := exists_psi_E7 (p := p) (f := f) (by omega)
  obtain ⟨hK, hZ, hL⟩ := spin12_facts (p := p) (f := f) hp2 hf
  rw [← hrange]
  have hs : Function.Surjective Ψ.rangeRestrict := Ψ.rangeRestrict_surjective
  have hk : Ψ.rangeRestrict.ker ≤ center (M₁₂).K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hne : ∃ x, Ψ.rangeRestrict x ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨-, -, a, b, hab⟩ := hK
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a ∈ center (M₁₂).K := hk (MonoidHom.mem_ker.2 (hall a))
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.1 ha b).symm]
  refine ⟨isQuasisimple_of_surjective hK hs hne, ?_, ?_⟩
  · rw [center_eq_map_center_of_isQuasisimple hK hs hk]
    exact hZ.map _
  · exact lieModel_of_mulEquiv (centralQuotientEquivOfIsQuasisimple hK hs hk) hL

theorem e7c_cases : ∀ m : Fin (Tag.rank .E7),
    m = e7Idx 1 ∨ m = e7Idx 4 ∨ m = e7Idx 6 ∨ MinusculeClosed.e7c m = 0 := by
  decide

theorem center_le_HJ : center M₇ ≤ HJ p f := by
  intro z hz
  obtain ⟨u, rfl⟩ := MinusculeClosed.center_le_range_minTorus e7Data_valid (GaloisField p f)
    isFiniteType_cartan_E7 (e7Datum_isCTGroupDatum _) (e7Datum_steinbergExtras _)
    (e7Datum_bruhatExtras _) hz
  have hu := (MinusculeClosed.minTorus_mem_center_iff e7Data_valid _ u).1 hz
  have h := fun m => MinusculeClosed.eq_zpow_of_mem_centerChars MinusculeClosed.e7C_spec hu m
  have h14 : e7Idx 1 ≠ e7Idx 4 := by decide
  have h16 : e7Idx 1 ≠ e7Idx 6 := by decide
  have h46 : e7Idx 4 ≠ e7Idx 6 := by decide
  have hu' : u = Pi.mulSingle (e7Idx 1) (u (e7Idx 1)) * Pi.mulSingle (e7Idx 4) (u (e7Idx 4)) *
      Pi.mulSingle (e7Idx 6) (u (e7Idx 6)) := by
    funext m
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    rcases e7c_cases m with rfl | rfl | rfl | h0
    · rw [ite_eq_left rfl, ite_eq_right h14, ite_eq_right h16, mul_one, mul_one]
    · rw [ite_eq_right h14.symm, ite_eq_left rfl, ite_eq_right h46, one_mul, mul_one]
    · rw [ite_eq_right h16.symm, ite_eq_right h46.symm, ite_eq_left rfl, one_mul, one_mul]
    · have hne : ∀ j : Fin (Tag.rank .E7), MinusculeClosed.e7c j ≠ 0 → m ≠ j := by
        rintro j hj rfl
        exact hj h0
      rw [ite_eq_right (hne _ (by decide)), ite_eq_right (hne _ (by decide)),
        ite_eq_right (hne _ (by decide)), h m, h0, zpow_zero, mul_one, mul_one]
  have hmem : ∀ (a : Fin (Tag.rank .E7)), a.val ≠ 0 → ∀ t : (GaloisField p f)ˣ,
      MinusculeClosed.minTorus e7Data_valid (GaloisField p f) (Pi.mulSingle a t) ∈ HJ p f := by
    intro a ha t
    rw [MinusculeClosed.minTorus_mulSingle]
    exact rankOne_le_HJ_of_ne_zero (j := a) ha
      ((e7Datum_isCTGroupDatum _).H_le a (e7Data_valid.hm_mem_torus _ a t))
  rw [hu', map_mul, map_mul]
  exact mul_mem (mul_mem (hmem _ (by decide) _) (hmem _ (by decide) _)) (hmem _ (by decide) _)

end CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row
