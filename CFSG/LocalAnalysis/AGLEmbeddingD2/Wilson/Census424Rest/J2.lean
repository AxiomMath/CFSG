module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.SolvableKit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.QuasisimpleCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS219.J2
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219
open CFSG.RankThree.PartTwo.Sec21 (IsCentral218)

theorem nonempty_centralizer_equiv_of_isCentral218
    {X : Type} [Group X] [Finite X] (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) {x : X}
    (hx1 : x ≠ 1) (hx : IsCentral218 (⊤ : Subgroup X) x) :
    Nonempty (centralizer ({x} : Set X) ≃* centralizer ({zJ} : Set GJ)) := by
  let e' : X ≃* GJ := e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  set P₀ : Subgroup X := P3.map e'.symm.toMonoidHom with hP₀def
  have hP₀ : Nat.card P₀ = 3 ^ (Nat.card X).factorization 3 := by
    rw [hP₀def, card_map_of_injective e'.symm.injective, card_P3, Nat.card_congr e'.toEquiv,
      factorization_card_GJ]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_center_of_isCentral218 hP₀ hx
  have hZ : P₀ ⊓ centralizer (P₀ : Set X) = (zpowers zJ).map e'.symm.toMonoidHom := by
    rw [hP₀def, ← CFSG.RankThree.PartTwo.Sec4.Sporadic.map_inf_centralizer e'.symm P3,
      inf_centralizer_P3, ← z_eq]
  rw [hZ] at hg
  obtain ⟨w, hw, hwx⟩ := mem_map.mp hg
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
  have hwx' : e'.symm (zJ ^ n) = g⁻¹ * x * g := hwx
  have hxw : x = g * e'.symm (zJ ^ n) * g⁻¹ := by rw [hwx']; group
  have hzn : zJ ^ n ≠ 1 := by
    intro h
    apply hx1
    rw [hxw, h, map_one, mul_one, mul_inv_cancel]
  have hmapC : (centralizer ({e'.symm (zJ ^ n)} : Set X)).map e'.toMonoidHom =
      centralizer ({zJ} : Set GJ) := by
    rw [Proving.centralizer_map_mulEquiv_wilson, MulEquiv.apply_symm_apply,
      centralizer_zpow_eq hzn]
  exact ⟨(MulEquiv.subgroupCongr (congrArg (fun y : X => centralizer ({y} : Set X)) hxw)).trans
      ((centralizerConjEquiv g _).trans
        ((e'.subgroupMap _).trans (MulEquiv.subgroupCongr hmapC)))⟩


theorem census424_of_j2
    {X : Type} [Group X] [Finite X] (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) :
    Census424 X := by
  intro D c d K h
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hDP⟩ := (Sec5.isPGroup_of_isElemAbelian h.maximal.prop).exists_le_sylow
  obtain ⟨-, -, -, h4, -⟩ := Sporadic.rank3II_4_15 X ⟨e⟩ P _ rfl _ rfl
  by_cases hcZ : c ∈ (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X)
  ·
    have hcentral : IsCentral218 (⊤ : Subgroup X) c := by
      refine ⟨(P : Subgroup X), ?_, ?_⟩
      · have hcard : Nat.card ((P : Subgroup X).subgroupOf (⊤ : Subgroup X)) =
            3 ^ (Nat.card ↥(⊤ : Subgroup X)).factorization 3 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv,
            Sylow.card_eq_multiplicity, Nat.card_congr (Subgroup.topEquiv (G := X)).toEquiv]
        refine ⟨Sylow.ofCard _ hcard, ?_⟩
        change ((P : Subgroup X).subgroupOf (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype =
          (P : Subgroup X)
        exact Subgroup.map_subgroupOf_eq_of_le le_top
      · refine ⟨⟨c, (Subgroup.mem_inf.mp hcZ).1⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_center_iff]
        intro t
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcZ).2) t t.2)
    obtain ⟨φ⟩ := nonempty_centralizer_equiv_of_isCentral218 e h.c_ne_one hcentral
    have hq : CFSG.IsQuasisimple (centralizer ({c} : Set X)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm isQuasisimple_C
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center (centralizer ({zJ} : Set GJ))))
      3 (by rw [card_center_C])
    set z : centralizer ({c} : Set X) := φ.symm (g : centralizer ({zJ} : Set GJ)) with hz
    have hzc : z ∈ center (centralizer ({c} : Set X)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply φ.injective
      rw [map_mul, map_mul, hz, MulEquiv.apply_symm_apply]
      exact (Subgroup.mem_center_iff.mp g.2) (φ y)
    have hzo : orderOf z = 3 := by
      rw [hz, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
      exact hg
    obtain ⟨hKC, hK'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsIn
    have hT' : Sec11.IsType424 (K.subgroupOf (centralizer ({c} : Set X)) ⧸
        aschbacherSolvableCore 3 (K.subgroupOf (centralizer ({c} : Set X)))) := by
      refine Sec11.isType424_of_mulEquiv ?_ h.isType424
      let e0 := Subgroup.subgroupOfEquivOfLe hKC
      exact QuotientGroup.congr _ _ e0
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e0)
    exact false_of_mem_thetaComponents_of_quasisimple hq hzc hzo hK' hT'
  · exact Item424Res2.not_isSolvable_centralizer h
      (isSolvable_centralizer_of_normalizer_equiv c
        (h4 D ⟨hDP, h.card_eq⟩ c h.c_mem hcZ).2.1.some)

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
