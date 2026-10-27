module

public import CFSG.LieType.Steinberg.RankTwo.ReparamRelations
public import CFSG.LieType.RootSystem.Restrict

public section

namespace CFSG.GroupTheory.GomiLeviExc

open CFSG.LieType.Steinberg CFSG.LieType.RootSystem.Restrict
open scoped commutatorElement

section Defs

variable {ι k G : Type*} [Field k] [Group G]

open Classical in
@[expose] def IsCharTwoSteinberg (R : Set (ι → ℤ)) (x : (ι → ℤ) → k → G) : Prop :=
  (∀ γ ∈ R, ∀ c d : k, x γ (c + d) = x γ c * x γ d) ∧
    ∀ α ∈ R, ∀ β ∈ R, α + β ≠ 0 → ∀ c d : k,
      ⁅x α c, x β d⁆ = if α + β ∈ R then x (α + β) (c * d) else 1

end Defs

section Presentation

variable {ι k G H : Type*} [Fintype ι] [DecidableEq ι] [Field k] [Group G] [Group H]
  {Φ : RootSystem ι}

theorem commutatorFormula_one
    (hsl : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 → ∀ p ∈ expPairs Φ α β, p = (1, 1))
    {x : (ι → ℤ) → k → G} (hx : IsCharTwoSteinberg Φ.roots x) (O : CommOrder Φ) :
    CommutatorFormula x O fun _ _ _ => 1 := by
  intro α hα β hβ hαβ c d
  have hmem : ∀ p ∈ O.list α β, p = (1, 1) := fun p hp =>
    hsl α hα β hβ hαβ p ((O.mem_iff α hα β hβ hαβ p).1 hp)
  rw [hx.2 α hα β hβ hαβ c d]
  cases hL : O.list α β with
  | nil =>
      have hroot : α + β ∉ Φ.roots := by
        intro h
        have hp : (1, 1) ∈ O.list α β :=
          (O.mem_iff α hα β hβ hαβ (1, 1)).2
            ⟨by norm_num, by norm_num, by simpa using h⟩
        rw [hL] at hp
        exact List.not_mem_nil hp
      rw [if_neg hroot]
      simp
  | cons p L' =>
      have hp : p = (1, 1) := hmem p (by simp [hL])
      subst p
      have hL' : L' = [] := by
        cases L' with
        | nil => rfl
        | cons q L'' =>
            have hnd : ((1, 1) :: q :: L'').Nodup := by simpa [hL] using O.nodup α β
            have hq : q = (1, 1) := hmem q (by simp [hL])
            rw [hq] at hnd
            simp at hnd
      subst L'
      have hroot : α + β ∈ Φ.roots := by
        have hp : (1, 1) ∈ O.list α β := by simp [hL]
        have := (O.mem_iff α hα β hβ hαβ (1, 1)).1 hp
        simpa using this.2.2
      rw [if_pos hroot]
      simp

theorem exists_hom_of_isCharTwoSteinberg
    (hsl : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 → ∀ p ∈ expPairs Φ α β, p = (1, 1))
    {x : (ι → ℤ) → k → G} (hO : Nonempty (CommOrder Φ)) (hx : PresentationB (Φ := Φ) x)
    (hxs : IsCharTwoSteinberg Φ.roots x) {y : (ι → ℤ) → k → H}
    (hys : IsCharTwoSteinberg Φ.roots y) :
    ∃ φ : G →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (x γ c) = y γ c := by
  obtain ⟨O⟩ := hO
  obtain ⟨φ, hφ, -⟩ := RankTwo.existsUnique_hom_of_presentationB hx O
    (commutatorFormula_one hsl hxs O) ⟨hys.1, commutatorFormula_one hsl hys O⟩
  exact ⟨φ, hφ⟩

theorem range_eq_closure_of_presentationB {x : (ι → ℤ) → k → G}
    (hO : Nonempty (CommOrder Φ)) (hx : PresentationB (Φ := Φ) x) (φ : G →* H)
    {y : (ι → ℤ) → k → H} (hφ : ∀ γ ∈ Φ.roots, ∀ c, φ (x γ c) = y γ c) :
    φ.range = Subgroup.closure {h | ∃ γ ∈ Φ.roots, ∃ c, y γ c = h} := by
  obtain ⟨O⟩ := hO
  obtain ⟨C, -, hC⟩ := (hx O).1
  obtain ⟨hrel, hbij⟩ := (hx O).2 C hC
  let ex : ChevGen Φ k → G := fun p => x p.1.1 p.2
  have hgen : Subgroup.closure (Set.range ex) = ⊤ := by
    have hmap := MonoidHom.map_closure (PresentedGroup.toGroup hrel)
      (Set.range (PresentedGroup.of : ChevGen Φ k → ChevPresented Φ k O C))
    rw [PresentedGroup.closure_range_of, Subgroup.map_top,
      MonoidHom.range_eq_top.2 hbij.2] at hmap
    have himg : Set.range ex = (PresentedGroup.toGroup hrel) '' Set.range
        (PresentedGroup.of : ChevGen Φ k → ChevPresented Φ k O C) := by
      rw [← Set.range_comp]
      congr 1
      funext p
      simp [ex, chevEval]
    rw [himg, ← hmap]
  have hrange : φ.range = Subgroup.closure (φ '' Set.range ex) := by
    rw [← MonoidHom.map_closure φ (Set.range ex), hgen, Subgroup.map_top]
  rw [hrange]
  refine congrArg Subgroup.closure ?_
  ext a
  constructor
  · rintro ⟨-, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.1.1, p.1.2, p.2, (hφ p.1.1 p.1.2 p.2).symm⟩
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨ex (⟨γ, hγ⟩, c), ⟨(⟨γ, hγ⟩, c), rfl⟩, hφ γ hγ c⟩

end Presentation

section Ext

variable {I C k G : Type} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C] [Field k]
  [Group G]

theorem IsCharTwoSteinberg.ext {A : Matrix I I ℤ} {hA : TauCeti.IsFiniteType A} {e : C → I}
    (he : Function.Injective e) {x : (I → ℤ) → k → G}
    (hx : IsCharTwoSteinberg (CFSG.LieType.RootSystem.roots hA ∅) x) :
    IsCharTwoSteinberg (CFSG.LieType.RootSystem.roots (hA.submatrix he) ∅)
      fun γ c => x (CFSG.LieType.RootSystem.Restrict.ext e γ) c := by
  have hzero : CFSG.LieType.RootSystem.Restrict.ext e (0 : C → ℤ) = 0 := by
    change Function.extend e (fun _ => (0 : ℤ)) (fun _ => (0 : ℤ)) = fun _ => (0 : ℤ)
    exact Function.extend_const e (0 : ℤ)
  have hroot : ∀ γ, CFSG.LieType.RootSystem.Restrict.ext e γ ∈
      CFSG.LieType.RootSystem.roots hA ∅ ↔
      γ ∈ CFSG.LieType.RootSystem.roots (hA.submatrix he) ∅ := fun γ =>
    CFSG.LieType.RootSystem.Restrict.ext_mem_roots_iff he hA γ
  have hαβ' : ∀ α ∈ CFSG.LieType.RootSystem.roots (hA.submatrix he) ∅,
      ∀ β ∈ CFSG.LieType.RootSystem.roots (hA.submatrix he) ∅, α + β ≠ 0 →
      CFSG.LieType.RootSystem.Restrict.ext e α +
        CFSG.LieType.RootSystem.Restrict.ext e β ≠ 0 := by
    intro α _ β _ hαβ h
    apply hαβ
    refine CFSG.LieType.RootSystem.Restrict.ext_injective he ?_
    rw [CFSG.LieType.RootSystem.Restrict.ext_add he, h, hzero]
  refine ⟨fun γ hγ c d => hx.1 _ ((hroot γ).2 hγ) c d, ?_⟩
  intro α hα β hβ hαβ c d
  dsimp only
  rw [hx.2 _ ((hroot α).2 hα) _ ((hroot β).2 hβ) (hαβ' α hα β hβ hαβ) c d]
  rw [← CFSG.LieType.RootSystem.Restrict.ext_add he]
  by_cases h : α + β ∈ CFSG.LieType.RootSystem.roots (hA.submatrix he) ∅
  · rw [if_pos ((hroot (α + β)).2 h), if_pos h]
  · rw [if_neg (fun hh => h ((hroot (α + β)).1 hh)), if_neg h]

end Ext

end CFSG.GroupTheory.GomiLeviExc
