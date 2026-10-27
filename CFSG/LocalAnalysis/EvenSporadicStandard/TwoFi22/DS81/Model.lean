module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

structure LocalModel (Λ : Type*) [Group Λ] (E : Subgroup Λ) : Prop where
  card_E : Nat.card E = 2 ^ 11
  E_sq : ∀ e ∈ E, e ^ 2 = 1
  center_le : center Λ ≤ E
  fuse : ∀ s : Λ, orderOf s = 2 → ∃ l : Λ, l⁻¹ * s * l ∈ E
  gen : normalizer (E : Set Λ) ≤
    E ⊔ closure {y | y ∈ normalizer (E : Set Λ) ∧ Odd (orderOf y)}
  odd_index : Odd (normalizer (E : Set Λ)).index
  unique : ∀ B : Subgroup Λ, B ≤ normalizer (E : Set Λ) → (∀ b ∈ B, b ^ 2 = 1) →
    Nat.card B = 2 ^ 11 → B = E
  sq : ∀ a : Λ, a ^ 2 ∈ center Λ → a ^ 2 = 1
  rank : ∀ σ : MulAut Λ, σ * σ = 1 → (∀ l : Λ, σ ≠ MulAut.conj l) →
    ∀ B : Subgroup Λ, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) → Nat.card B ≤ 2 ^ 8
  aut_cent : ∀ σ : MulAut Λ, (∀ e ∈ E, σ e = e) → ∃ x ∈ E, σ = MulAut.conj x

namespace LocalModel

variable {Λ Λ' : Type*} [Group Λ] [Group Λ']

theorem of_mulEquiv (ψ : Λ ≃* Λ') {E : Subgroup Λ} (M : LocalModel Λ E) :
    LocalModel Λ' (E.map ψ.toMonoidHom) := by
  have hmem : ∀ {x : Λ'}, x ∈ E.map ψ.toMonoidHom ↔ ψ.symm x ∈ E := fun {x} =>
    Subgroup.mem_map_equiv
  have hN : ∀ {x : Λ'}, x ∈ normalizer ((E.map ψ.toMonoidHom : Subgroup Λ') : Set Λ') ↔
      ψ.symm x ∈ normalizer (E : Set Λ) := by
    intro x
    rw [mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · intro h y
      have := h (ψ y)
      rw [hmem, hmem] at this
      simpa using this
    · intro h y
      rw [hmem, hmem]
      have := h (ψ.symm y)
      simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← M.card_E]
    exact Nat.card_congr (ψ.subgroupMap E).toEquiv.symm
  · intro e he
    rw [hmem] at he
    have := M.E_sq _ he
    rw [← map_pow] at this
    simpa using congrArg ψ this
  · intro z hz
    rw [hmem]
    refine M.center_le ?_
    rw [mem_center_iff] at hz ⊢
    intro g
    have := hz (ψ g)
    have h4 := congrArg ψ.symm this
    simpa using h4
  · intro s hs
    obtain ⟨l, hl⟩ := M.fuse (ψ.symm s) (by rw [MulEquiv.orderOf_eq]; exact hs)
    refine ⟨ψ l, ?_⟩
    rw [hmem]
    simpa using hl
  · intro x hx
    have h1 : ψ.symm x ∈ E ⊔ closure {y | y ∈ normalizer (E : Set Λ) ∧ Odd (orderOf y)} :=
      M.gen (hN.1 hx)
    have h2 : x ∈ (E ⊔ closure {y | y ∈ normalizer (E : Set Λ) ∧ Odd (orderOf y)}).map
        ψ.toMonoidHom := ⟨ψ.symm x, h1, by simp⟩
    rw [Subgroup.map_sup, MonoidHom.map_closure] at h2
    refine sup_le_sup_left (closure_mono ?_) _ h2
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨hN.2 (by simpa using hy1), ?_⟩
    simpa [MulEquiv.orderOf_eq] using hy2
  · have : normalizer ((E.map ψ.toMonoidHom : Subgroup Λ') : Set Λ') =
        (normalizer (E : Set Λ)).map ψ.toMonoidHom := by
      ext x
      rw [hN, Subgroup.mem_map_equiv]
    rw [this, Subgroup.index_map_of_bijective ψ.bijective]
    exact M.odd_index
  · intro B' hB' hB'2 hB'c
    have hle : B'.map ψ.symm.toMonoidHom ≤ normalizer (E : Set Λ) := by
      rintro _ ⟨b, hb, rfl⟩
      exact hN.1 (by simpa using hB' hb)
    have hsq : ∀ b ∈ B'.map ψ.symm.toMonoidHom, b ^ 2 = 1 := by
      rintro _ ⟨b, hb, rfl⟩
      have := hB'2 b hb
      rw [← map_pow] at *
      simp [this]
    have hc : Nat.card (B'.map ψ.symm.toMonoidHom) = 2 ^ 11 := by
      rw [← hB'c]
      exact Nat.card_congr (ψ.symm.subgroupMap B').toEquiv.symm
    have := M.unique _ hle hsq hc
    have h3 := congrArg (fun A => A.map ψ.toMonoidHom) this
    simp only [Subgroup.map_map] at h3
    have e : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id Λ' := by
      ext x; simp
    rw [e, Subgroup.map_id] at h3
    exact h3
  · intro a' ha'
    have ha : ψ.symm a' ^ 2 ∈ center Λ := by
      rw [mem_center_iff] at ha' ⊢
      intro g
      have := ha' (ψ g)
      have h4 := congrArg ψ.symm this
      simpa [map_pow] using h4
    have := M.sq _ ha
    have h5 := congrArg ψ this
    simpa [map_pow] using h5
  · intro σ' hσ'2 hσ'out B' hB'2 hB'fix
    set σ : MulAut Λ := (ψ.trans σ').trans ψ.symm with hσ
    have hσσ : σ * σ = 1 := by
      ext x
      have := congrArg (fun f : MulAut Λ' => f (ψ x)) hσ'2
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      simp [hσ, MulAut.mul_apply, this]
    have hσout : ∀ l : Λ, σ ≠ MulAut.conj l := by
      intro l hl
      apply hσ'out (ψ l)
      ext y
      have := congrArg (fun f : MulAut Λ => ψ (f (ψ.symm y))) hl
      simpa [hσ, MulAut.conj_apply, map_mul, map_inv] using this
    have hBsq : ∀ b ∈ B'.map ψ.symm.toMonoidHom, b ^ 2 = 1 := by
      rintro _ ⟨b, hb, rfl⟩
      have := hB'2 b hb
      simp [← map_pow, this]
    have hBfix : ∀ b ∈ B'.map ψ.symm.toMonoidHom, σ b = b := by
      rintro _ ⟨b, hb, rfl⟩
      simp [hσ, hB'fix b hb]
    have := M.rank σ hσσ hσout _ hBsq hBfix
    exact (Nat.card_congr (ψ.symm.subgroupMap B').toEquiv).trans_le this
  · intro σ' hσ'
    set σ : MulAut Λ := (ψ.trans σ').trans ψ.symm with hσ
    have hfix : ∀ e ∈ E, σ e = e := by
      intro e he
      have hψe : ψ e ∈ E.map ψ.toMonoidHom := ⟨e, he, rfl⟩
      simp [hσ, hσ' _ hψe]
    obtain ⟨x, hx, hxσ⟩ := M.aut_cent σ hfix
    refine ⟨ψ x, ⟨x, hx, rfl⟩, ?_⟩
    ext y
    have := congrArg (fun f : MulAut Λ => ψ (f (ψ.symm y))) hxσ
    simpa [hσ, MulAut.conj_apply, map_mul, map_inv] using this

end LocalModel

end CFSG.EvenSporadicStandard.TwoFi22.DS81
