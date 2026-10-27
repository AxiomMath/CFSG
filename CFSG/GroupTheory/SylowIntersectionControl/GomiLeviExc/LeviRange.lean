module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
public import CFSG.LieType.RootSystem.Restrict

public section

namespace CFSG.GroupTheory.GomiLeviExc

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.ParabLevi

variable {K k : Type} [Group K] [Field k] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {x : (Fin D.rank → ℤ) → k → K} {m : ℕ}
  {e : Fin m → Fin D.rank}

private theorem roots_eq_roots_empty (D : UniversalRootDatum K) (hdiv : D.divisible = ∅) :
    D.roots = CFSG.LieType.RootSystem.roots D.isFiniteType ∅ := by
  rw [UniversalRootDatum.roots, hdiv]

private theorem ext_neg_single (he : Function.Injective e) (j : Fin m) :
    Restrict.ext e (-Pi.single j 1) = -Pi.single (e j) 1 := by
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    rw [Restrict.ext_apply he]
    simp [Pi.single_apply, he.eq_iff]
  · rw [Restrict.ext_apply_of_notMem_range _ hk, Pi.neg_apply, Pi.single_eq_of_ne]
    · simp
    · rintro rfl
      exact hk ⟨j, rfl⟩

private theorem closure_rootElements_ext_le_leviM
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅)
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    (he : Function.Injective e) :
    Subgroup.closure {g | ∃ γ ∈ CFSG.LieType.RootSystem.roots (D.isFiniteType.submatrix he) ∅,
      ∃ c, x (Restrict.ext e γ) c = g} ≤ leviM D (Set.range e) := by
  rw [Subgroup.closure_le]
  rintro g ⟨γ, hγ, c, rfl⟩
  have hroot : Restrict.ext e γ ∈ D.roots := by
    rw [roots_eq_roots_empty D hdiv]
    exact (Restrict.ext_mem_roots_iff he D.isFiniteType γ).mpr hγ
  exact rootGroup_le_leviM hct hroot (fun k hk => Restrict.ext_apply_of_notMem_range γ hk)
    (((hpar (Restrict.ext e γ) hroot).1 _).mpr ⟨c, rfl⟩)

private theorem leviM_le_closure_rootElements_ext
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    (he : Function.Injective e) :
    leviM D (Set.range e) ≤
      Subgroup.closure {g | ∃ γ ∈ CFSG.LieType.RootSystem.roots (D.isFiniteType.submatrix he) ∅,
        ∃ c, x (Restrict.ext e γ) c = g} := by
  refine iSup₂_le fun i hi => ?_
  obtain ⟨j, rfl⟩ := hi
  refine sup_le ?_ ?_
  · intro g hg
    have hroot : Pi.single (e j) 1 ∈ D.roots := Or.inl ⟨1, e j, by simp⟩
    obtain ⟨c, hc⟩ := ((hpar (Pi.single (e j) 1) hroot).1 g).mp hg
    rw [← hc]
    refine Subgroup.subset_closure ⟨Pi.single j 1, Or.inl ⟨1, j, by simp⟩, c, ?_⟩
    rw [Restrict.ext_single he j]
  · intro g hg
    have hroot : -Pi.single (e j) 1 ∈ D.roots :=
      Or.inl ⟨(coxeterMatrix D.isFiniteType).toCoxeterSystem.simple (e j), e j, by
        rw [weylAction_simple, reflection_single_self (D.isFiniteType.apply_self (e j))]⟩
    obtain ⟨c, hc⟩ := ((hpar (-Pi.single (e j) 1) hroot).1 g).mp hg
    rw [← hc]
    refine Subgroup.subset_closure ⟨-Pi.single j 1, ?_, c, ?_⟩
    · exact CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (hA := D.isFiniteType.submatrix he)
        (Or.inl ⟨1, j, by simp⟩)
    · rw [ext_neg_single he j]

theorem closure_rootElements_ext_eq_leviM
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅)
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    (he : Function.Injective e) :
    Subgroup.closure {g | ∃ γ ∈ CFSG.LieType.RootSystem.roots (D.isFiniteType.submatrix he) ∅,
      ∃ c, x (Restrict.ext e γ) c = g} = leviM D (Set.range e) :=
  le_antisymm (closure_rootElements_ext_le_leviM hct hdiv hpar he)
    (leviM_le_closure_rootElements_ext hpar he)

theorem leviM_range_ne_bot
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    (hm : 1 ≤ m) : leviM D (Set.range e) ≠ ⊥ := by
  let j : Fin m := ⟨0, by omega⟩
  have hroot : Pi.single (e j) 1 ∈ D.roots := Or.inl ⟨1, e j, by simp⟩
  have hx0 : x (Pi.single (e j) 1) 0 = 1 := by
    have h := (hpar (Pi.single (e j) 1) hroot).2.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := x (Pi.single (e j) 1) 0) (by rw [← h, mul_one])
  have hx1 : x (Pi.single (e j) 1) 1 ≠ 1 := by
    intro h1
    have h10 : (1 : k) = 0 :=
      (hpar (Pi.single (e j) 1) hroot).2.2 (by rw [h1, hx0])
    exact one_ne_zero h10
  have hmem : x (Pi.single (e j) 1) 1 ∈ leviM D (Set.range e) := by
    have hx : x (Pi.single (e j) 1) 1 ∈ D.rootGroup (Pi.single (e j) 1) :=
      ((hpar (Pi.single (e j) 1) hroot).1 _).mpr ⟨1, rfl⟩
    refine rankOne_le_leviM (Set.mem_range_self j) ?_
    rw [rankOne]
    exact Subgroup.mem_sup_left hx
  intro hbot
  exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hmem))

end CFSG.GroupTheory.GomiLeviExc
