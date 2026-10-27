module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.GH74.GLS.Classes
import CFSG.LocalAnalysis.OddStandard.ChildHeHeld
import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Mult
import CFSG.GH74.E2.ComponentsBasic

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Blueprint

private theorem fixedSubgroup_conj_eq_centralizer_gen' {X : Type*} [Group X] (z : X) :
    CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj z) =
      Subgroup.centralizer {z} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change MulAut.conj z x = x ↔ x * z = z * x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc x * z = (z * x * z⁻¹) * z := by rw [h]
      _ = z * x := by group
  · intro h
    calc z * x * z⁻¹ = (x * z) * z⁻¹ := by rw [h]
      _ = x := by group

theorem properFixedComponent_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L) {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    ComponentClassification.CatLeaf.ProperFixedComponent (MulAut.conj t) L := by
  haveI : IsSimpleGroup G := hS.simple
  obtain ⟨hLT, hcomp⟩ := isPComponent_two_of_standard hS.standard ht ht2
    (even_iff_two_dvd.1 (even_card_of_standard hS.standard))
  have hfix : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj t) =
      Subgroup.centralizer ({t} : Set G) := fixedSubgroup_conj_eq_centralizer_gen' t
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    simp only [MulAut.conj_apply, hti]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [htt]; group
  · rw [hfix]
    exact hLT
  · rw [hfix]
    exact hcomp
  · intro htop
    have htcenter : t ∈ center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subgroup.mem_centralizer_iff.mp ht x (by rw [htop]; exact Subgroup.mem_top x)
    have ht1 : t = 1 := by
      rw [ComponentClassification.CatLeaf.center_eq_bot_of_simple hS.nonab] at htcenter
      simpa using htcenter
    rw [ht1, orderOf_one] at ht2
    norm_num at ht2

theorem lieModel_fusionZStar_iff_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L) (τ : Assembly.LowTwoRank.StatedLieTag)
    (n p f : ℕ) :
    LieModel (L ⧸ center L) τ n p f ↔ LieModel (L ⧸ Open.fusionZStar L) τ n p f := by
  have hZ := fusionZStar_eq_center_of_standard hL
  have e : (L ⧸ Open.fusionZStar L) ≃* (L ⧸ center L) :=
    QuotientGroup.quotientMulEquivOfEq hZ
  constructor
  · intro hm
    exact LieModel.of_mulEquiv e.symm hm
  · intro hm
    exact LieModel.of_mulEquiv e hm

theorem exists_isSimpleChevalleyOver_of_oddLieType {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L)
    (hlie : OddLieType (L ⧸ center L)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      ComponentClassification.HarrisLit.IsSimpleChevalleyOver r (L ⧸ Open.fusionZStar L) := by
  obtain ⟨τ, n, p, f, hp, hp2, -, hm⟩ := hlie
  exact ⟨p, hp, hp2, τ, n, f, (lieModel_fusionZStar_iff_of_standard hL τ n p f).1 hm⟩

theorem not_inChev2_fusionZStar_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L) (h : ¬ GH74.GLS.InChev2 (L ⧸ center L)) :
    ¬ GH74.GLS.InChev2 (L ⧸ Open.fusionZStar L) := by
  intro h'
  apply h
  have hZ := fusionZStar_eq_center_of_standard hL
  exact GH74.E2.inChev2_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ) h'

end CFSG.OddStandard.HigherRank
