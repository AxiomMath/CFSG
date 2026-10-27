module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmGlue
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmNorm

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7

@[expose] def ruW7Word : List (Fin 7 × Bool) :=
  (List.replicate 7 [(5, true), (0, true), (2, true), (6, true)]).flatten

variable {G : Type} [Group G] {z : G} {A : Subgroup G}

@[expose] noncomputable def ruLetterImg (f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G)))
    (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G))) : Fin 7 → G :=
  ![((f₁ ⟨PresentedGroup.of 0, mem_letterSub (by decide)⟩ : ↥(centralizer ({z} : Set G))) : G),
    ((f₁ ⟨PresentedGroup.of 1, mem_letterSub (by decide)⟩ : ↥(centralizer ({z} : Set G))) : G),
    ((f₁ ⟨PresentedGroup.of 2, mem_letterSub (by decide)⟩ : ↥(centralizer ({z} : Set G))) : G),
    ((f₁ ⟨PresentedGroup.of 3, mem_letterSub (by decide)⟩ : ↥(centralizer ({z} : Set G))) : G),
    ((f₁ ⟨PresentedGroup.of 4, mem_letterSub (by decide)⟩ : ↥(centralizer ({z} : Set G))) : G),
    ((f₁ ⟨PresentedGroup.of 5, mem_letterSub (by decide)⟩ : ↥(centralizer ({z} : Set G))) : G),
    ((f₂ ⟨PresentedGroup.of 6, mem_letterSub (by decide)⟩ : ↥(normalizer (A : Set G))) : G)]

omit [Group G] in
theorem lift_ruW7Word {H : Type*} [Group H] (g : Fin 7 → H) :
    FreeGroup.lift g (FreeGroup.mk ruW7Word) = (g 5 * g 0 * g 2 * g 6) ^ 7 := by
  rw [ruW7Word, FreeGroup.lift_mk]
  simp [pow_succ, mul_assoc]

theorem range_le_of_letterSub {l : List (Fin 7)} {K : Type*} [Group K]
    (φ : ↥(letterSub l) →* K) {H : Subgroup K}
    (h : ∀ i (hi : i ∈ l), φ ⟨PresentedGroup.of i, mem_letterSub hi⟩ ∈ H) : φ.range ≤ H := by
  have htop : closure (((↑) : ↥(letterSub l) → Pi7) ⁻¹'
      ((fun i => (PresentedGroup.of i : Pi7)) '' {i | i ∈ l})) = ⊤ :=
    closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure, closure_le]
  rintro _ ⟨⟨x, hx⟩, ⟨i, hi, rfl⟩, rfl⟩
  exact h i hi

theorem exists_hom_of_edgeAgree {R : List (List (Fin 7 × Bool))}
    (hR : ∀ r ∈ R, ((∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))) ∧ pi7Word r = 1) ∨
      ((∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7))) ∧ pi7Word r = 1) ∨ r = ruW7Word)
    (f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G))) (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hag : RuEdgeAgree f₁ f₂ (MonoidHom.id _))
    (hw : (ruLetterImg f₁ f₂ 5 * ruLetterImg f₁ f₂ 0 * ruLetterImg f₁ f₂ 2 *
      ruLetterImg f₁ f₂ 6) ^ 7 = 1) :
    ∃ Φ : PG 7 R →* G, (∀ i, Φ (PresentedGroup.of i) = ruLetterImg f₁ f₂ i) ∧
      centralizer ({z} : Set G) ≤ Φ.range ∧ normalizer (A : Set G) ≤ Φ.range := by
  set g := ruLetterImg f₁ f₂ with hgdef
  set φ₁ : ↥ruM1 →* G := (centralizer ({z} : Set G)).subtype.comp f₁.toMonoidHom with hφ₁
  set φ₂ : ↥ruM2 →* G := (normalizer (A : Set G)).subtype.comp f₂.toMonoidHom with hφ₂
  have hg₁ : ∀ i (hi : i ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))),
      φ₁ ⟨PresentedGroup.of i, mem_letterSub hi⟩ = g i := by
    intro i hi
    fin_cases i
    all_goals first
      | rfl
      | exact absurd hi (by decide)
  have hg₂ : ∀ i (hi : i ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7))),
      φ₂ ⟨PresentedGroup.of i, mem_letterSub hi⟩ = g i := by
    intro i hi
    fin_cases i
    all_goals first
      | rfl
      | exact absurd hi (by decide)
      | exact (hag ⟨PresentedGroup.of _, mem_letterSub (by decide)⟩).symm
  have hrels : ∀ r ∈ {r : FreeGroup (Fin 7) | r ∈ R.map FreeGroup.mk},
      FreeGroup.lift g r = 1 := by
    rintro _ hr
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
    rcases hR w hw' with ⟨h, h1⟩ | ⟨h, h1⟩ | rfl
    · exact lift_eq_one_of_letterSub (l := [0, 1, 2, 3, 4, 5]) φ₁ hg₁ h1 h
    · exact lift_eq_one_of_letterSub (l := [0, 1, 2, 3, 4, 6]) φ₂ hg₂ h1 h
    · rw [lift_ruW7Word]
      exact hw
  set Φ : PG 7 R →* G := PresentedGroup.toGroup hrels with hΦ
  have hof : ∀ i, Φ (PresentedGroup.of i) = g i := fun i => PresentedGroup.toGroup.of hrels
  refine ⟨Φ, hof, fun y hy => ?_, fun y hy => ?_⟩
  · have hle : φ₁.range ≤ Φ.range := range_le_of_letterSub (l := [0, 1, 2, 3, 4, 5]) φ₁
      fun i hi => ⟨PresentedGroup.of i, (hof i).trans (hg₁ i hi).symm⟩
    refine hle ⟨f₁.symm ⟨y, hy⟩, ?_⟩
    rw [hφ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  · have hle : φ₂.range ≤ Φ.range := range_le_of_letterSub (l := [0, 1, 2, 3, 4, 6]) φ₂
      fun i hi => ⟨PresentedGroup.of i, (hof i).trans (hg₂ i hi).symm⟩
    refine hle ⟨f₂.symm ⟨y, hy⟩, ?_⟩
    rw [hφ₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl

end CFSG.ComponentClassification.GMS78.RuAsm
