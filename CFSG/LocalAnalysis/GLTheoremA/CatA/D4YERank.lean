module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCRed
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

theorem exists_inj_projOmegaPlus {K : Type} [Group K] [Finite K] (h4 : catalogIs K isD4any)
    (hn : ¬ catalogIs K S9.isD4two) :
    ∃ ψ : CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1) →* K, Function.Injective ψ := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h4
  have hi2 : ¬ S9.isD4two i := fun h => hn ⟨i, h, ⟨e⟩⟩
  obtain ⟨q, hv, hp2, hex, rfl⟩ := exists_D4_of_isD4any_not_two hi hi2
  have hm := CFSG.Models.lieModel_D 4 q hv e
  have hsc : StatedClassicalModel K .POmegaPlus 4 q.p q.exponent :=
    hm.statedClassicalModel (by decide)
  obtain ⟨-, K₀, _, _, hK₀, ⟨eK⟩⟩ := hsc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  have hK₀' : Nat.card K₀ = 2 ^ q.exponent := by rw [hK₀, hp2]
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := q.exponent)
    (by rw [← Nat.card_eq_fintype_card, hK₀'])
  let k : Subfield K₀ := ⊥
  have hk2 : Nat.card ↥k = 2 := Subfield.card_bot K₀ 2
  haveI : Finite ↥k := Nat.finite_of_card_ne_zero (by omega)
  let eKG : K ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K₀) :=
    eK.trans (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K₀) (coe_quadPlus 4 K₀))
  let e2 : matrixProjectiveDerived (coordinateQuadPlus 4 ↥k) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 4 ↥k)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 ↥k) (coe_quadPlus 4 ↥k)).symm
  obtain ⟨e3⟩ := CFSG.LocalAnalysis.GLTheoremA.D4XF.equiv_projOmegaPlus_of_statedProj hk2 e2
  let ι := CFSG.RankThree.PartOne.KCOrthogonalSubfield.incl k
    (CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadPlus_isExtension k 4)
  have hι : Function.Injective ι := CFSG.RankThree.PartOne.KCOrthogonalSubfield.incl_injective k _
    (by norm_num)
  refine ⟨(eKG.symm.toMonoidHom.comp ι).comp e3.symm.toMonoidHom, ?_⟩
  intro a b hab
  exact e3.symm.injective (hι (eKG.symm.injective hab))

theorem d4big_rank4 {K : Type} [Group K] [Finite K] (h4 : catalogIs K isD4any)
    (hn : ¬ catalogIs K S9.isD4two) :
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  obtain ⟨ψ, hψ⟩ := exists_inj_projOmegaPlus h4 hn
  obtain ⟨D, hD, hDc⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.exists_e81_of_three_lt_pRank
    CFSG.RankThree.PartTwo.Sec4.Census.three_lt_pRank_omegaPlus
  refine ⟨D.map ψ, CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map ψ hD, ?_⟩
  rw [Subgroup.card_map_of_injective hψ, hDc]
  norm_num

theorem d4big_rank3 {K : Type} [Group K] [Finite K] (h4 : catalogIs K isD4any)
    (hn : ¬ catalogIs K S9.isD4two) :
    ∃ E W : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (W : Set K) := by
  obtain ⟨ψ, hψ⟩ := exists_inj_projOmegaPlus h4 hn
  haveI : Finite (CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1)) :=
    Finite.of_injective ψ hψ
  obtain ⟨E, W, hE, hEc, hW2, hWne, hEW⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.D4XF.exists_E27_of_three_le_twoLocalPrimeRank
      (G := CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1))
      CFSG.RankThree.PartTwo.Sec4.Census.localRank_omega8PlusTwo
  refine ⟨E.map ψ, W.map ψ, CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map ψ hE, ?_,
    hW2.map ψ, fun h => hWne ((Subgroup.map_eq_bot_iff_of_injective W hψ).1 h), ?_⟩
  · rw [Subgroup.card_map_of_injective hψ, hEc]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem _ (hEW hy))

end CFSG.LocalAnalysis.GLTheoremA.D4Y

