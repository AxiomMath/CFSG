module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Family

variable {X : Type*} [Group X]

@[expose] def TwinFamily (𝓕 : Set (Subgroup X)) (a : ℕ) : Prop :=
  ∃ F : Fin a → Subgroup X, (∀ i, F i ∈ 𝓕) ∧ Function.Injective F ∧
    (∀ i j, i ≠ j → Commutes (F i) (F j)) ∧
    ∀ i j, ∀ S ∈ 𝓕, (S = F i ∨ Commutes S (F i)) ↔ (S = F j ∨ Commutes S (F j))

variable {𝓕 : Set (Subgroup X)} {a : ℕ}

@[expose] def IsTwinPair (𝓕 : Set (Subgroup X)) (R₀ R₁ : Subgroup X) : Prop :=
  R₀ ∈ 𝓕 ∧ R₁ ∈ 𝓕 ∧ R₀ ≠ R₁ ∧ Commutes R₀ R₁ ∧
    ∀ S ∈ 𝓕, S ≠ R₀ → S ≠ R₁ → (Commutes S R₀ ↔ Commutes S R₁)

theorem isTwinPair_of_closed {R₀ R₁ : Subgroup X} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕) (hne : R₀ ≠ R₁)
    (hc : Commutes R₀ R₁)
    (h : ∀ S ∈ 𝓕, (S = R₀ ∨ Commutes S R₀) ↔ (S = R₁ ∨ Commutes S R₁)) : IsTwinPair 𝓕 R₀ R₁ :=
  ⟨h₀, h₁, hne, hc, fun S hS h0 h1 => by
    have := h S hS
    simp only [h0, h1, false_or] at this
    exact this⟩

theorem TwinFamily.exists_two (h : TwinFamily 𝓕 a) (ha : 2 ≤ a) :
    ∃ R₀ R₁ : Subgroup X, IsTwinPair 𝓕 R₀ R₁ := by
  obtain ⟨F, hF, hinj, hcomm, htw⟩ := h
  let i₀ : Fin a := ⟨0, by omega⟩
  let i₁ : Fin a := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := fun e => by simpa [i₀, i₁] using congrArg Fin.val e
  exact ⟨F i₀, F i₁, isTwinPair_of_closed (hF i₀) (hF i₁) (fun e => hne (hinj e))
    (hcomm i₀ i₁ hne) (htw i₀ i₁)⟩

theorem TwinFamily.exists_three (h : TwinFamily 𝓕 a) (ha : 3 ≤ a) :
    ∃ R₀ R₁ R₂ : Subgroup X, IsTwinPair 𝓕 R₀ R₁ ∧ IsTwinPair 𝓕 R₀ R₂ ∧ IsTwinPair 𝓕 R₁ R₂ ∧
      R₂ ∈ 𝓕 ∧ Commutes R₀ R₂ ∧ Commutes R₁ R₂ := by
  obtain ⟨F, hF, hinj, hcomm, htw⟩ := h
  let i₀ : Fin a := ⟨0, by omega⟩
  let i₁ : Fin a := ⟨1, by omega⟩
  let i₂ : Fin a := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := fun e => by simpa [i₀, i₁] using congrArg Fin.val e
  have h02 : i₀ ≠ i₂ := fun e => by simpa [i₀, i₂] using congrArg Fin.val e
  have h12 : i₁ ≠ i₂ := fun e => by simpa [i₁, i₂] using congrArg Fin.val e
  refine ⟨F i₀, F i₁, F i₂, isTwinPair_of_closed (hF i₀) (hF i₁) (fun e => h01 (hinj e))
    (hcomm i₀ i₁ h01) (htw i₀ i₁), isTwinPair_of_closed (hF i₀) (hF i₂) (fun e => h02 (hinj e))
    (hcomm i₀ i₂ h02) (htw i₀ i₂), isTwinPair_of_closed (hF i₁) (hF i₂) (fun e => h12 (hinj e))
    (hcomm i₁ i₂ h12) (htw i₁ i₂), hF i₂, hcomm i₀ i₂ h02, hcomm i₁ i₂ h12⟩

end Family

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem commutes_map_equiv (e : X ≃* Y) {A B : Subgroup X} :
    Commutes (A.map e.toMonoidHom) (B.map e.toMonoidHom) ↔ Commutes A B := by
  constructor
  · intro h x hx y hy
    apply e.injective
    rw [map_mul, map_mul]
    exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

theorem TwinFamily.of_equiv (e : X ≃* Y) {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} {a : ℕ}
    (h : ∀ R : Subgroup X, R ∈ 𝓕 ↔ R.map e.toMonoidHom ∈ 𝓖) (hT : TwinFamily 𝓕 a) :
    TwinFamily 𝓖 a := by
  obtain ⟨F, hF, hinj, hcomm, htw⟩ := hT
  refine ⟨fun i => (F i).map e.toMonoidHom, fun i => (h _).mp (hF i), fun i j hij => ?_,
    fun i j hij => (commutes_map_equiv e).mpr (hcomm i j hij), fun i j S' hS' => ?_⟩
  · exact hinj (Subgroup.map_injective e.injective hij)
  · set S : Subgroup X := S'.map e.symm.toMonoidHom with hS
    have hSe : S.map e.toMonoidHom = S' := by
      rw [hS, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
        ext y; simp
      rw [this, Subgroup.map_id]
    have hSmem : S ∈ 𝓕 := (h S).mpr (hSe ▸ hS')
    have key : ∀ k, (S' = (F k).map e.toMonoidHom ∨ Commutes S' ((F k).map e.toMonoidHom)) ↔
        (S = F k ∨ Commutes S (F k)) := by
      intro k
      rw [← hSe, ← commutes_map_equiv e (A := S) (B := F k)]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl (Subgroup.map_injective e.injective h1)
        · exact Or.inr h1
      · rintro (h1 | h1)
        · exact Or.inl (by rw [h1])
        · exact Or.inr h1
    rw [key i, key j]
    exact htw i j S hSmem

end Transport

section Model

variable {p : ℕ} [Fact p.Prime]

theorem modelTwinClass_iff (t : StatedLieTag) (n e a : ℕ) :
    ModelTwinClass p t n e a ↔
      TwinFamily (fundamentalSubgroups t (modelUniv t n p e Fact.out).D) a := Iff.rfl

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
