module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossOut
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Spor
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open Subgroup CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

theorem not_dvd_lieOrderDivisor {K : Type} [Group K] {p : ℕ} (hp5 : 5 ≤ p)
    (hl : ¬ IsLinearOrUnitaryAt p K) {t : StatedLieTag} {n ℓ f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel K t n ℓ f) : ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) := by
  have hn1 : ¬ p ∣ 1 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hn2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hn3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hn4 : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  cases t
  case PSL =>
    exact CFSG.LocalAnalysis.RankFourTheoremC.not_dvd_gcd_psl_of_not_isLinearOrUnitaryAt hl
      (hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  case PSU =>
    exact CFSG.LocalAnalysis.RankFourTheoremC.not_dvd_gcd_psu_of_not_isLinearOrUnitaryAt hl
      (hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  case PSp =>
    intro h
    have h' : p ∣ Nat.gcd 2 (ℓ ^ f - 1) := h
    exact hn2 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case POmegaOdd =>
    intro h
    have h' : p ∣ 2 := h
    exact hn2 h'
  case POmegaPlus =>
    intro h
    have h' : p ∣ Nat.gcd 4 ((ℓ ^ f) ^ n - 1) := h
    exact hn4 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case POmegaMinus =>
    intro h
    have h' : p ∣ Nat.gcd 4 ((ℓ ^ f) ^ n + 1) := h
    exact hn4 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case E6 =>
    intro h
    have h' : p ∣ Nat.gcd 3 (ℓ ^ f - 1) := h
    exact hn3 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case E7 =>
    intro h
    have h' : p ∣ Nat.gcd 2 (ℓ ^ f - 1) := h
    exact hn2 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case twistedE6 =>
    intro h
    have h' : p ∣ Nat.gcd 3 (ℓ ^ f + 1) := h
    exact hn3 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  all_goals (intro h; exact hn1 h)

theorem isL2pp_of_lieModel {K : Type} [Group K] {p n ℓ f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel K .PSL n ℓ f) (hn : n = 2) (hℓ : ℓ = p) (hf : f = p) :
    P64IsL2pp p K := by
  subst hn hℓ hf
  obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  exact ⟨F, hF, hFin, hFcard, ⟨e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

theorem not_dvd_card_outer_of_tits
    {K : Type} [Group K] [Finite K] {p n ℓ f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmodel : CFSG.Blueprint.LieModel K .Tits n ℓ f) : ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨-, hree⟩ := (CFSG.Blueprint.LieModel.reeTits_iff (by decide)).1 hmodel
  obtain ⟨k, hk⟩ := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1.exists_card_eq
  intro hdvd
  rw [hk] at hdvd
  have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
  omega

@[expose] def SporadicCarrierOutOdd : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 → ∀ (T : Type) [Group T],
    Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.Carrier s) → ¬ p ∣ Nat.card (Outer T)

open CFSG.RankThree.PartOne in
theorem kd291OuterLie_of_fixedRank
    (hSpor : SporadicCarrierOutOdd) (hD : ∀ t, OuterFixedRankDefAt t)
    (hC : ∀ t, OuterFixedRankCrossAt t) : KD291OuterLie := by
  intro p hp hp5 Y _ _ L _ hs hnab hnlu hlie hcen h3 x hxL hxo hxc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup ↥L := hs
  obtain ⟨d, ⟨e⟩⟩ := hlie
  have hcat : CFSG.Open.IsCatalogGroup ↥L := ⟨TauCeti.CFSGIndex.lie d, ⟨e⟩⟩
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hQ := CFSG.LocalAnalysis.RankFourTheoremC.pRank_quotient_le_one_of_catalog hp hp5 L hs hnab
    hcat hnlu hcen
  have h2L : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
    have := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_top_le_add_of_normal hp L
    omega
  have hα : (MulAut.conjNormal x : MulAut ↥L) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hαin : (MulAut.conjNormal x : MulAut ↥L) ∉ inner ↥L :=
    CFSG.ComponentClassification.RestrictedStd.Spor.conjNormal_not_mem_inner hcen hxL
  have hno : ¬ p ∣ Nat.card (Outer ↥L) → False := fun hout =>
    hxL (CFSG.LocalAnalysis.RankFourTheoremC.mem_of_pow_eq_one_of_not_dvd_card_outer hp L hcen
      hout hxp)
  rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge ↥L hnab hcat) with
    ⟨q, hq, ⟨e'⟩⟩ | ⟨n, hn5, ⟨e'⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e'⟩⟩
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e'.injective (by rw [map_mul, map_mul, mul_comm]))
  ·
    exfalso
    refine hno ?_
    have h1 := CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp (by omega)
    rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
      at h1
  ·
    by_cases hT : t = .Tits
    · subst hT
      exact (hno (not_dvd_card_outer_of_tits hp hp5 hmodel)).elim
    · have hdiv := not_dvd_lieOrderDivisor hp5 hnlu hmodel
      by_cases hℓp : ℓ = p
      · rcases hD t ↥L n ℓ f hadm hmodel hT p hp hp5 hℓp _ hα hαin with h | ⟨rfl, hn, hf⟩
        · exact absurd (three_le_pRank_of_two_le_fixed L hxo hxL h) (by omega)
        · exact isL2pp_of_lieModel hmodel hn hℓp hf
      · have h := hC t ↥L n ℓ f hadm hmodel hT p hp hp5 hℓp hdiv _ hα hαin h2L
        exact absurd (three_le_pRank_of_two_le_fixed L hxo hxL h) (by omega)
  ·
    exfalso
    exact hno (hSpor s p hp (by omega) ↥L ⟨e'⟩)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
