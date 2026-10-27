module

public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open Subgroup CFSG.Sporadic.Schreier CFSG.LocalAnalysis.ComponentInitial

theorem conj_injective_of_center {Y : Type*} [Group Y] (hZ : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hc : y ∈ center Y := by
    rw [mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut Y => φ x) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = (y * x * y⁻¹) * y := by rw [this]
      _ = y * x := by group
  rw [hZ, mem_bot] at hc
  exact hc

theorem map_conj_fixSub {Y : Type*} [Group Y] (hZ : center Y = ⊥) (φ : MulAut Y) :
    (fixSub φ).map (MulAut.conj : Y →* MulAut Y) =
      (MulAut.conj : Y →* MulAut Y).range ⊓ centralizer ({φ} : Set (MulAut Y)) := by
  ext σ
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_inf.mpr ⟨⟨y, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have hy' : φ y = y := mem_fixSub.mp hy
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hy']
  · rintro hσ
    obtain ⟨⟨y, rfl⟩, hc⟩ := mem_inf.mp hσ
    refine ⟨y, mem_fixSub.mpr ?_, rfl⟩
    rw [mem_centralizer_singleton_iff] at hc
    apply conj_injective_of_center hZ
    ext x
    have h1 := congrArg (fun σ : MulAut Y => σ (φ⁻¹ x)) hc
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulAut.apply_inv_self] at h1
    rw [MulAut.conj_apply, MulAut.conj_apply]
    exact h1.symm

theorem exists_fix_component {Y : Type*} [Group Y] (hZ : center Y = ⊥)
    {G : Subgroup (MulAut Y)} (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ G) (φ : G)
    {Jh : Subgroup G} (hJle : Jh ≤ (MulAut.conj : Y →* MulAut Y).range.subgroupOf G)
    (hJc : Jh ≤ centralizer ({φ} : Set G))
    (hJ : CFSG.IsComponent (Jh.subgroupOf (centralizer ({φ} : Set G)))) :
    ∃ M : Subgroup Y, CFSG.Assembly.IsComponentOf M (fixSub (φ : MulAut Y)) ∧
      Nonempty (↥M ≃* ↥Jh) := by
  set ι := (MulAut.conj : Y →* MulAut Y) with hιdef
  have hι : Function.Injective ι := conj_injective_of_center hZ
  have hG : Function.Injective G.subtype := Subtype.val_injective
  have h1 : CFSG.Assembly.IsComponentOf Jh (centralizer ({φ} : Set G)) :=
    (isComponentOf_iff_isComponent_subgroupOf hJc).2 hJ
  have h2 := (isComponentOf_map_iff hG).2 h1
  rw [CFSG.Sporadic.SmallOddCore.map_centralizer_eq_inf hG, range_subtype,
    Set.image_singleton] at h2
  have hJι : Jh.map G.subtype ≤ ι.range := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mem_subgroupOf.mp (hJle hσ)
  have hR : ι.range ⊓ centralizer ({(φ : MulAut Y)} : Set (MulAut Y)) ≤
      G ⊓ centralizer ({(φ : MulAut Y)} : Set (MulAut Y)) :=
    inf_le_inf_right _ hInn
  have h3 := isComponentOf_of_le h2 (le_inf hJι (h2.1.trans inf_le_right)) hR
  rw [← map_conj_fixSub hZ] at h3
  refine ⟨(Jh.map G.subtype).comap ι, ?_, ?_⟩
  · rw [← isComponentOf_map_iff hι, map_comap_eq_self hJι]
    exact h3
  · exact ⟨(((Jh.map G.subtype).comap ι).equivMapOfInjective ι hι).trans
      ((MulEquiv.subgroupCongr (map_comap_eq_self hJι)).trans
        (Jh.equivMapOfInjective G.subtype hG).symm)⟩

theorem fixSub_map_equiv {Y N : Type*} [Group Y] [Group N] (e : Y ≃* N) (φ : MulAut Y) :
    (fixSub φ).map e.toMonoidHom = fixSub ((e.symm.trans φ).trans e) := by
  ext n
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : φ y = y := mem_fixSub.mp hy
    rw [mem_fixSub]
    simp [hy']
  · intro hn
    rw [mem_fixSub] at hn
    refine ⟨e.symm n, mem_fixSub.mpr ?_, by simp⟩
    apply e.injective
    simpa using hn

theorem isComponentOf_fixSub_map {Y N : Type*} [Group Y] [Group N] (e : Y ≃* N) (φ : MulAut Y)
    {M : Subgroup Y} (hM : CFSG.Assembly.IsComponentOf M (fixSub φ)) :
    CFSG.Assembly.IsComponentOf (M.map e.toMonoidHom) (fixSub ((e.symm.trans φ).trans e)) := by
  rw [← fixSub_map_equiv]
  exact (isComponentOf_map_iff e.injective).2 hM

end CFSG.ComponentClassification.GSThmB.Cov
