module

public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.RankThree.PartOne.CTP

section Bridge

variable {K : Type*} [Group K]

theorem closure_fixUnion_eq_planeClosure (E : Subgroup (MulAut K)) :
    Subgroup.closure (fixUnion E) = planeClosure E := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro k ⟨F, hFE, hFb, hk⟩
    obtain ⟨⟨φ, hφF⟩, hφ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFb
    exact mem_planeClosure_of_fixed (hFE hφF) (fun h => hφ1 (Subtype.ext h)) (hk φ hφF)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro k ⟨e, he, he1, hk⟩
    exact Subgroup.subset_closure (fixedSubgroup_subset_fixUnion he he1 hk)

theorem planeGen_iff_closure_fixUnion (E : Subgroup (MulAut K)) :
    PlaneGen E ↔ Subgroup.closure (fixUnion E) = ⊤ := by
  rw [PlaneGen, closure_fixUnion_eq_planeClosure]

end Bridge

section Transport

variable {K P : Type*} [Group K] [Group P]

theorem not_le_range_conj_map_congr (e : K ≃* P) {E : Subgroup (MulAut K)}
    (h : ¬ E ≤ (MulAut.conj : K →* MulAut K).range) :
    ¬ E.map (MulAut.congr e).toMonoidHom ≤ (MulAut.conj : P →* MulAut P).range := by
  intro hle
  apply h
  intro x hx
  have hx' : (MulAut.congr e).toMonoidHom x ∈ (MulAut.conj : P →* MulAut P).range :=
    hle ⟨x, hx, rfl⟩
  have hx'' : (MulAut.congr e).toMonoidHom x ∈
      ((MulAut.conj : K →* MulAut K).range).map (MulAut.congr e).toMonoidHom := by
    rw [map_range_conj_congr e]
    exact hx'
  obtain ⟨y, hy, hyx⟩ := hx''
  rwa [← (MulAut.congr e).injective hyx]

theorem isElemAbelian_map_congr (e : K ≃* P) {p : ℕ} {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
  CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _

theorem card_map_congr (e : K ≃* P) (E : Subgroup (MulAut K)) :
    Nat.card (E.map (MulAut.congr e).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective

theorem planeGen_of_outer_model (e : K ≃* P) {E : Subgroup (MulAut K)}
    (h : PlaneGen (E.map (MulAut.congr e).toMonoidHom)) : PlaneGen E :=
  (planeGen_map_congr e E).mp h

end Transport

end CFSG.LieType.SeitzGeneration
