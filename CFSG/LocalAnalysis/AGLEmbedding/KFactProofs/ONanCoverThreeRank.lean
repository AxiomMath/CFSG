module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
public import CFSG.RankThree.PartOne.N143.LieLeaves
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverTorusRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverSpor
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLifts
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
import CFSG.RankThree.PartOne.K159.CenterRank

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverFive

open CFSG.Open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.Sec4.Census
  (SporadicMultipliers sporadicMultiplierOrder tripleCoverAlternating tripleCoverLie_of_griess)
open CFSG.RankThree.PartOne.N143 (IsLieThreeIndex IsLieE6Index)
open CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def IsCoverThreeResidualIndex : CFSGIndex → Prop
  | .cyclic _ _ => False
  | .alternating n _ => n = 6 ∨ n = 7
  | .sporadic s => s = .M22 ∨ s = .ONan
  | .lie d => IsLieThreeIndex (.lie d) ∨ IsLieE6Index (.lie d)

theorem localRank_le_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    CFSG.Assembly.RankThreeEven.localRank p G ≤ Open.pRank p (⊤ : Subgroup G) := by
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hp.one_lt le_top

theorem sporadic_three_cases (hSpor : SporadicMultipliers) {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) {s : SporadicName}
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic s).Group)
    (h3 : 3 ∣ Nat.card (Subgroup.center K)) :
    s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi24Prime := by
  have h1 := h3.trans (CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e)
  rw [hSpor.1 s] at h1
  clear e h3 hq
  revert h1
  cases s <;> decide

theorem statedClassicalModel_psl_of_typeA {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (e : G ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group) :
    StatedClassicalModel G .PSL (r + 1) q.p q.exponent := by
  obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := CFSG.RankThree.PartTwo.Sec4.Census.lieModel_typeA r q hv
  · obtain ⟨hadm', rest⟩ := hcl
    obtain ⟨k, hkf, hkfin, hk, ⟨e'⟩⟩ := rest
    exact ⟨hadm', k, hkf, hkfin, hk, ⟨e.trans e'⟩⟩
  · omega

theorem four_le_pRank_three_or_residual (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers)
    {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hcat : IsCatalogGroup (K ⧸ Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K)) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup K) ∨
      ∃ i : CFSGIndex, IsCoverThreeResidualIndex i ∧
        Nonempty (K ⧸ Subgroup.center K ≃* i.Group) := by
  obtain ⟨i, ⟨e⟩⟩ := hcat
  have hq' : CFSG.IsQuasisimple K := isQuasisimple_of_open hq
  have h3 : 3 ∣ Nat.card (Subgroup.center K) :=
    dvd_card_center_of_isPGroup Nat.prime_three hZ hZp
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    odd_card_center_of_isPGroup Nat.prime_three (by norm_num) hZp
  by_cases hrk : 4 ≤ Open.pRank 3 (⊤ : Subgroup K)
  · exact Or.inl hrk
  have hrk' : Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by omega
  refine Or.inr ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hq'.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod r)) _ _
  | alternating n hn =>
    exact tripleCoverAlternating n K hn ⟨hq', h3, ⟨e⟩⟩
  | sporadic s =>
    rcases sporadic_three_cases hSpor hq' e h3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have := HasLiftableTriple.four_le_pRank_of_cover kFactLiftJ3 e h3
      omega
    · exact (ThreeCover.false_McL hq hZp hZ hZc hrk' e).elim
    · exact (ThreeCover.false_Suz hZp hZ hZc hrk' e).elim
    · exact Or.inr rfl
    · exact (ThreeCover.false_Fi22 hZp hZ hZc hrk' e).elim
    · exact (ThreeCover.false_Fi24 hZp hZ hZc hrk' e).elim
  | lie d =>
    have hidx := tripleCoverLie_of_griess hGA d K ⟨hq', h3, ⟨e⟩⟩
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      obtain ⟨hpn, hpq⟩ := hidx
      by_cases hr : r + 1 = 3
      · exact Or.inl ⟨by omega, hpq⟩
      · exfalso
        have hmod := statedClassicalModel_psl_of_typeA r q hv e
        obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_four_psl_of_ne_two Nat.prime_three
          (by norm_num) (by omega) h3 hodd hmod hpn (by simpa only [PrimePower.card_def] using hpq)
        have := le_pRank_of_pow_le_card Nat.prime_three le_top
          ⟨⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩, hBp⟩ hBcard
        omega
    | twistedA r q =>
      rcases hidx with ⟨hpn, hpq⟩ | ⟨rfl, hq3⟩
      · by_cases hr : r + 1 = 3
        · exact Or.inl ⟨by omega, hpq⟩
        · exfalso
          have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
          obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_four_psu_of_ne_two Nat.prime_three
            (by norm_num) (by omega) h3 hodd hmod hpn
            (by simpa only [PrimePower.card_def] using hpq)
          have := le_pRank_of_pow_le_card Nat.prime_three le_top
            ⟨⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩, hBp⟩ hBcard
          omega
      · exfalso
        have := HasLiftableTriple.four_le_pRank_of_cover (kFactLiftU43 q hv hq3) e h3
        omega
    | B r q =>
      exfalso
      obtain ⟨rfl, hq3⟩ := hidx
      obtain ⟨hp3, -⟩ := CFSG.RankThree.PartOne.N143.primePower_eq_three hq3
      have hp2 : q.p ≠ 2 := by omega
      obtain ⟨-, F, _, _, hF3, ⟨eF⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl
          (G := K ⧸ Subgroup.center K) e
      have hF : Nat.card F = 3 := by rw [hF3, ← PrimePower.card_def]; exact hq3
      let e' : K ⧸ Subgroup.center K ≃* ↥CFSG.RankThree.PartOne.N143.O7.Om :=
        eF.trans (CFSG.RankThree.PartOne.N143.O7.modelEquiv hF)
      let φ' : K →* ↥CFSG.RankThree.PartOne.N143.O7.Om :=
        e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
      have hφ' : Function.Surjective φ' := e'.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : φ'.ker = Subgroup.center K :=
        CFSG.RankThree.PartOne.K159.ker_comp_mk'_eq_center e'
      have h4 := CFSG.RankThree.PartOne.N143.O7.four_le_localRank_of_cover φ' hφ' hker.le
        (by rw [hker]; exact h3)
      have := h4.trans (localRank_le_pRank Nat.prime_three)
      omega
    | G2 q =>
      exfalso
      have := HasLiftableTriple.four_le_pRank_of_cover (kFactLiftG23 q hv hidx) e h3
      omega
    | E6 q => exact Or.inr hidx
    | twistedE6 q => exact Or.inr hidx
    | C r q => exact hidx.elim
    | D r q => exact hidx.elim
    | twistedD r q => exact hidx.elim
    | E7 q => exact hidx.elim
    | E8 q => exact hidx.elim
    | F4 q => exact hidx.elim
    | trialityD4 q => exact hidx.elim
    | suzuki m => exact hidx.elim
    | reeG2 m => exact hidx.elim
    | reeF4 m => exact hidx.elim
    | tits => exact hidx.elim

end CFSG.AGLEmbedding.KFactProofs.CoverFive
