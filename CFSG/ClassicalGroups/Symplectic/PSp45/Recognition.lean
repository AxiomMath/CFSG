module

public import CFSG.ClassicalGroups.Symplectic.PSp45.Generation
public import CFSG.ClassicalGroups.Symplectic.PSp45.Pres
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.ClassicalGroups.Symplectic.PSp45

open CFSG.CosetTable CFSG.Open


theorem exists_presented_mulEquiv :
    ∃ φ : PG 8 pspRels ≃* PSp45, ∀ i, φ (PresentedGroup.of i) = psp45GenP i := by
  obtain ⟨_, hle⟩ := finite_card_presented_le
  let p : PG 8 pspRels →* PSp45 := PresentedGroup.toGroup (f := psp45GenP) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact lift_psp45GenP_rels w hw)
  have hp : ∀ i, p (PresentedGroup.of i) = psp45GenP i :=
    fun i => PresentedGroup.toGroup.of (f := psp45GenP) _
  have hsurj : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_psp45GenP, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hp i⟩
  have hbij : Function.Bijective p := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [card_psp45]
    exact hle
  exact ⟨MulEquiv.ofBijective p hbij, fun i => hp i⟩

theorem exists_closure_mulEquiv {X : Type*} [Group X] (x : Fin 8 → X)
    (hx : ∀ r ∈ pspRels, FreeGroup.lift x (FreeGroup.mk r) = 1) (hne : ∃ i, x i ≠ 1) :
    ∃ ψ : Subgroup.closure (Set.range x) ≃* PSp45,
      ∀ i, ψ ⟨x i, Subgroup.subset_closure (Set.mem_range_self i)⟩ = psp45GenP i := by
  have hx' : ∀ r ∈ {r : FreeGroup (Fin 8) | r ∈ pspRels.map FreeGroup.mk},
      FreeGroup.lift x r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact hx w hw
  let q : PG 8 pspRels →* X := PresentedGroup.toGroup (f := x) hx'
  have hq : ∀ i, q (PresentedGroup.of i) = x i :=
    fun i => PresentedGroup.toGroup.of (f := x) hx'
  have hrange : q.range = Subgroup.closure (Set.range x) := by
    rw [MonoidHom.range_eq_map,
      ← PresentedGroup.closure_range_of (rels := {r : FreeGroup (Fin 8) |
        r ∈ pspRels.map FreeGroup.mk}),
      MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hq i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨PresentedGroup.of i, ⟨i, rfl⟩, hq i⟩
  obtain ⟨e, he⟩ := exists_presented_mulEquiv
  haveI : IsSimpleGroup PSp45 :=
    isSimpleGroup_statedProj_statedSp (ZMod 5) 2 (by norm_num) (Or.inl (Or.inr (by simp)))
  haveI : IsSimpleGroup (PG 8 pspRels) := e.isSimpleGroup
  have hker : q.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top q.ker with h | h
    · exact h
    · exfalso
      obtain ⟨i, hi⟩ := hne
      have hq1 : q = 1 := MonoidHom.ker_eq_top_iff.mp h
      have h1 : q (PresentedGroup.of i) = 1 := by rw [hq1]; rfl
      exact hi ((hq i).symm.trans h1)
  have hqinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hker
  refine ⟨(MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hqinj).symm.trans e),
    fun i => ?_⟩
  have hof : (MonoidHom.ofInjective hqinj).symm ((MulEquiv.subgroupCongr hrange).symm
      ⟨x i, Subgroup.subset_closure (Set.mem_range_self i)⟩) = PresentedGroup.of i := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (hq i).symm
  simp only [MulEquiv.trans_apply, hof, he]

theorem nonempty_closure_mulEquiv {X : Type*} [Group X] (x : Fin 8 → X)
    (hx : ∀ r ∈ pspRels, FreeGroup.lift x (FreeGroup.mk r) = 1) (hne : ∃ i, x i ≠ 1) :
    Nonempty (Subgroup.closure (Set.range x) ≃* PSp45) :=
  (exists_closure_mulEquiv x hx hne).elim fun ψ _ => ⟨ψ⟩

theorem statedClassicalModel_closure {X : Type} [Group X] (x : Fin 8 → X)
    (hx : ∀ r ∈ pspRels, FreeGroup.lift x (FreeGroup.mk r) = 1) (hne : ∃ i, x i ≠ 1) :
    StatedClassicalModel (Subgroup.closure (Set.range x)) .PSp 2 5 1 := by
  obtain ⟨e⟩ := nonempty_closure_mulEquiv x hx hne
  exact ⟨⟨Nat.prime_five, le_rfl, by norm_num, by decide⟩, ZMod 5, inferInstance,
    inferInstance, by simp, ⟨e⟩⟩

end CFSG.ClassicalGroups.Symplectic.PSp45
