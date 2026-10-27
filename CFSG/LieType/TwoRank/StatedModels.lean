module

public import CFSG.Open.StatedDefs
public import CFSG.Foundations.Basic
import CFSG.Open.StatedAPI
import CFSG.LieType.TwoRank.PGLFour

public section

namespace CFSG.LieType.TwoRank

open Matrix CFSG.Open

private noncomputable def statedProjToPGL {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (H : Subgroup (GL ι K)) : StatedProj H →* ProjGenLinGroup ι K :=
  (Subgroup.subtype (H.map (ProjGenLinGroup.mk : GL ι K →* ProjGenLinGroup ι K))).comp
    (CFSG.Open.StatedAPI.mapMkEquivStatedProj H).symm.toMonoidHom

@[simp] private theorem statedProjToPGL_apply {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (H : Subgroup (GL ι K)) (A : H) :
    statedProjToPGL H (A : StatedProj H) = ProjGenLinGroup.mk (A : GL ι K) :=
  CFSG.Open.StatedAPI.coe_mapMkEquivStatedProj_symm_mk H A

private theorem statedProjToPGL_injective {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (H : Subgroup (GL ι K)) : Function.Injective (statedProjToPGL H) := by
  intro a b hab
  exact (CFSG.Open.StatedAPI.mapMkEquivStatedProj H).symm.injective
    (Subgroup.subtype_injective _ hab)

theorem card_le_sixteen_of_isElementaryAbelian_statedProj {K : Type} [Field K]
    (hK : ringChar K ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4)
    {H : Subgroup (GL ι K)} (E : Subgroup (StatedProj H)) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : Function.Injective (statedProjToPGL H) := statedProjToPGL_injective H
  haveI : IsElementaryAbelian 2 (E.map (statedProjToPGL H)) :=
    IsElementaryAbelian.map (p := 2) (A := E) (statedProjToPGL H)
  have h := card_le_sixteen_of_isElementaryAbelian_pgl_four hK hι (E.map (statedProjToPGL H))
  rwa [Subgroup.card_map_of_injective (f := statedProjToPGL H) hψ] at h

theorem trace_eq_zero_of_card_eq_sixteen_statedProj {K : Type} [Field K] (hK : ringChar K ≠ 2)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4) {H : Subgroup (GL ι K)}
    (E : Subgroup (StatedProj H)) [IsElementaryAbelian 2 E] (hE : Nat.card E = 16) {h : H}
    (hhE : (h : StatedProj H) ∈ E) (hh : (h : StatedProj H) ≠ 1) :
    trace ((h : GL ι K) : Matrix ι ι K) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : Function.Injective (statedProjToPGL H) := statedProjToPGL_injective H
  haveI : IsElementaryAbelian 2 (E.map (statedProjToPGL H)) :=
    IsElementaryAbelian.map (p := 2) (A := E) (statedProjToPGL H)
  have hcard : Nat.card (E.map (statedProjToPGL H)) = 16 := by
    rw [Subgroup.card_map_of_injective (f := statedProjToPGL H) hψ, hE]
  have hmem : ProjGenLinGroup.mk (h : GL ι K) ∈ E.map (statedProjToPGL H) := by
    simpa only [statedProjToPGL_apply] using
      Subgroup.mem_map_of_mem (statedProjToPGL H) hhE
  have hne : ProjGenLinGroup.mk (h : GL ι K) ≠ 1 := by
    intro h1
    apply hh
    apply hψ
    rw [map_one, statedProjToPGL_apply, h1]
  exact trace_eq_zero_of_card_eq_sixteen hK hι (E.map (statedProjToPGL H)) hcard hmem hne

end CFSG.LieType.TwoRank
