module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDBase

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

theorem aff8_eq_iff {u u' : (ZMod 8)ˣ} {b b' : ZMod 8} :
    aff8 u b = aff8 u' b' ↔ u = u' ∧ b = b' :=
  ⟨aff8_injective, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩

theorem aff8_eq_one_iff {u : (ZMod 8)ˣ} {b : ZMod 8} : aff8 u b = 1 ↔ u = 1 ∧ b = 0 := by
  rw [← aff8_one, aff8_eq_iff]

@[expose] def affSub (p : (ZMod 8)ˣ → ZMod 8 → Prop) (h1 : p 1 0)
    (hmul : ∀ u b u' b', p u b → p u' b' → p (u * u') (b + u * b'))
    (hinv : ∀ u b, p u b → p u⁻¹ (-(u⁻¹ * b))) : Subgroup (Perm (ZMod 8)) where
  carrier := {σ | ∃ u b, aff8 u b = σ ∧ p u b}
  one_mem' := ⟨1, 0, aff8_one, h1⟩
  mul_mem' := by
    rintro _ _ ⟨u, b, rfl, hp⟩ ⟨u', b', rfl, hp'⟩
    exact ⟨_, _, (aff8_mul u u' b b').symm, hmul u b u' b' hp hp'⟩
  inv_mem' := by
    rintro _ ⟨u, b, rfl, hp⟩
    exact ⟨_, _, (aff8_inv u b).symm, hinv u b hp⟩

theorem aff8_mem_affSub {p : (ZMod 8)ˣ → ZMod 8 → Prop} {h1 hmul hinv} {u : (ZMod 8)ˣ}
    {b : ZMod 8} : aff8 u b ∈ affSub p h1 hmul hinv ↔ p u b := by
  constructor
  · rintro ⟨u', b', h, hp⟩
    obtain ⟨rfl, rfl⟩ := aff8_injective h
    exact hp
  · exact fun hp => ⟨u, b, rfl, hp⟩

@[expose] def pB (u : (ZMod 8)ˣ) (b : ZMod 8) : Prop := (u = 1 ∨ u = u5) ∧ (b = 0 ∨ b = 4)

@[expose] def pE (e : ZMod 8) (u : (ZMod 8)ˣ) (b : ZMod 8) : Prop :=
  pB u b ∨ ((u = u3 ∨ u = -1) ∧ (b = e ∨ b = e + 4))

@[expose] def pTE (_ : (ZMod 8)ˣ) (b : ZMod 8) : Prop := dbit8 b = 0

instance (u : (ZMod 8)ˣ) (b : ZMod 8) : Decidable (pB u b) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (e : ZMod 8) (u : (ZMod 8)ˣ) (b : ZMod 8) : Decidable (pE e u b) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (u : (ZMod 8)ˣ) (b : ZMod 8) : Decidable (pTE u b) :=
  inferInstanceAs (Decidable (dbit8 b = 0))

theorem pB_one : pB 1 0 := by decide

theorem pB_mul : ∀ u b u' b', pB u b → pB u' b' → pB (u * u') (b + u * b') := by decide

theorem pB_inv : ∀ u b, pB u b → pB u⁻¹ (-(u⁻¹ * b)) := by decide

theorem pE_one (e : ZMod 8) : pE e 1 0 := Or.inl pB_one

theorem pE_mul : ∀ e : ZMod 8, (e = 0 ∨ e = 2) → ∀ u b u' b', pE e u b → pE e u' b' →
    pE e (u * u') (b + u * b') := by decide

theorem pE_inv : ∀ e : ZMod 8, (e = 0 ∨ e = 2) → ∀ u b, pE e u b → pE e u⁻¹ (-(u⁻¹ * b)) := by
  decide

theorem pTE_mul : ∀ u b u' b', pTE u b → pTE u' b' → pTE (u * u') (b + u * b') := by decide

theorem pTE_inv : ∀ u b, pTE u b → pTE u⁻¹ (-(u⁻¹ * b)) := by decide

@[expose] def PB : Subgroup (Perm (ZMod 8)) := affSub pB pB_one pB_mul pB_inv

@[expose] def PE₀ : Subgroup (Perm (ZMod 8)) :=
  affSub (pE 0) (pE_one 0) (pE_mul 0 (Or.inl rfl)) (pE_inv 0 (Or.inl rfl))

@[expose] def PE₂ : Subgroup (Perm (ZMod 8)) :=
  affSub (pE 2) (pE_one 2) (pE_mul 2 (Or.inr rfl)) (pE_inv 2 (Or.inr rfl))

@[expose] def PTE : Subgroup (Perm (ZMod 8)) := affSub pTE (by decide) pTE_mul pTE_inv

theorem mem_PB {u : (ZMod 8)ˣ} {b : ZMod 8} : aff8 u b ∈ PB ↔ pB u b := aff8_mem_affSub

theorem mem_PE₀ {u : (ZMod 8)ˣ} {b : ZMod 8} : aff8 u b ∈ PE₀ ↔ pE 0 u b := aff8_mem_affSub

theorem mem_PE₂ {u : (ZMod 8)ˣ} {b : ZMod 8} : aff8 u b ∈ PE₂ ↔ pE 2 u b := aff8_mem_affSub

theorem mem_PTE {u : (ZMod 8)ˣ} {b : ZMod 8} : aff8 u b ∈ PTE ↔ dbit8 b = 0 := aff8_mem_affSub

theorem PB_le_PE₀ : PB ≤ PE₀ := by
  rintro _ ⟨u, b, rfl, h⟩
  exact mem_PE₀.mpr (Or.inl h)

theorem PB_le_PE₂ : PB ≤ PE₂ := by
  rintro _ ⟨u, b, rfl, h⟩
  exact mem_PE₂.mpr (Or.inl h)

theorem pE_inter : ∀ u b, pE 0 u b → pE 2 u b → pB u b := by decide

theorem PE₀_inf_PE₂ : PE₀ ⊓ PE₂ = PB := by
  refine le_antisymm ?_ (le_inf PB_le_PE₀ PB_le_PE₂)
  rintro _ ⟨⟨u, b, rfl, h₀⟩, h₂⟩
  exact mem_PB.mpr (pE_inter u b h₀ (mem_PE₂.mp h₂))

theorem sq_pTE : ∀ u b, dbit8 b = 0 → aff8 u b ^ 2 = 1 → pE 0 u b ∨ pE 2 u b := by
  intro u b
  simp only [pow_two, aff8_mul, aff8_eq_one_iff]
  revert u b
  decide

theorem mem_PE_of_sq {σ : Perm (ZMod 8)} (hσ : σ ∈ PTE) (h2 : σ ^ 2 = 1) :
    σ ∈ PE₀ ∨ σ ∈ PE₂ := by
  obtain ⟨u, b, rfl, hb⟩ := hσ
  rcases sq_pTE u b hb h2 with h | h
  · exact Or.inl (mem_PE₀.mpr h)
  · exact Or.inr (mem_PE₂.mpr h)

theorem comm_pTE : ∀ u b u' b', dbit8 b = 0 → dbit8 b' = 0 → aff8 u b ^ 2 = 1 →
    aff8 u' b' ^ 2 = 1 → aff8 u b * aff8 u' b' = aff8 u' b' * aff8 u b → ¬ pE 0 u b →
    pE 0 u' b' ∨ pE 2 u' b' → pE 2 u' b' := by
  intro u b u' b'
  simp only [pow_two, aff8_mul, aff8_eq_one_iff, aff8_eq_iff]
  revert u b u' b'
  decide

theorem mem_PE₂_of_comm {σ τ : Perm (ZMod 8)} (hσ : σ ∈ PTE) (hτ : τ ∈ PTE) (hσ2 : σ ^ 2 = 1)
    (hτ2 : τ ^ 2 = 1) (hστ : σ * τ = τ * σ) (hσE : σ ∉ PE₀) : τ ∈ PE₂ := by
  obtain ⟨u, b, rfl, hb⟩ := hσ
  obtain ⟨u', b', rfl, hb'⟩ := hτ
  have h := mem_PE_of_sq (mem_PTE.mpr hb') hτ2
  rw [mem_PE₀, mem_PE₂] at h
  rw [mem_PE₀] at hσE
  exact mem_PE₂.mpr (comm_pTE u b u' b' hb hb' hσ2 hτ2 hστ hσE h)

theorem conj_odd_pE : ∀ u b u' b', dbit8 b = 1 →
    (pE 0 u' b' → pE 2 (u * u' * u⁻¹) (b + u * b' + u * u' * (-(u⁻¹ * b)))) ∧
    (pE 2 u' b' → pE 0 (u * u' * u⁻¹) (b + u * b' + u * u' * (-(u⁻¹ * b)))) := by decide

theorem conj_mem_PE_of_odd {u : (ZMod 8)ˣ} {b : ZMod 8} (hb : dbit8 b = 1)
    {σ : Perm (ZMod 8)} :
    (σ ∈ PE₀ → aff8 u b * σ * (aff8 u b)⁻¹ ∈ PE₂) ∧
      (σ ∈ PE₂ → aff8 u b * σ * (aff8 u b)⁻¹ ∈ PE₀) := by
  constructor
  · rintro ⟨u', b', rfl, h⟩
    rw [aff8_inv, aff8_mul, aff8_mul, mem_PE₂]
    exact (conj_odd_pE u b u' b' hb).1 h
  · rintro ⟨u', b', rfl, h⟩
    rw [aff8_inv, aff8_mul, aff8_mul, mem_PE₀]
    exact (conj_odd_pE u b u' b' hb).2 h

theorem conj_odd_pB : ∀ u b u' b', pB u' b' → pB (u * u' * u⁻¹) (b + u * b' + u * u' *
    (-(u⁻¹ * b))) := by decide

theorem conj_mem_PB {u : (ZMod 8)ˣ} {b : ZMod 8} {σ : Perm (ZMod 8)} (hσ : σ ∈ PB) :
    aff8 u b * σ * (aff8 u b)⁻¹ ∈ PB := by
  obtain ⟨u', b', rfl, h⟩ := hσ
  rw [aff8_inv, aff8_mul, aff8_mul, mem_PB]
  exact conj_odd_pB u b u' b' h

theorem comm_odd_pTE : ∀ u b u' b', dbit8 b = 1 → dbit8 b' = 0 → aff8 u' b' ^ 2 = 1 →
    aff8 u b * aff8 u' b' = aff8 u' b' * aff8 u b → (u' = 1 ∧ (b' = 0 ∨ b' = 4)) := by
  intro u b u' b'
  simp only [pow_two, aff8_mul, aff8_eq_one_iff, aff8_eq_iff]
  revert u b u' b'
  decide

theorem eq_of_comm_odd {u : (ZMod 8)ˣ} {b : ZMod 8} (hb : dbit8 b = 1) {σ : Perm (ZMod 8)}
    (hσ : σ ∈ PTE) (h2 : σ ^ 2 = 1) (hc : aff8 u b * σ = σ * aff8 u b) : σ = 1 ∨ σ = z8 := by
  obtain ⟨u', b', rfl, hb'⟩ := hσ
  obtain ⟨rfl, h | h⟩ := comm_odd_pTE u b u' b' hb hb' h2 hc <;> subst h
  · exact Or.inl aff8_one
  · exact Or.inr rfl

theorem conj_d8_of_odd : ∀ u b, dbit8 b = 1 → aff8 u b ^ 2 = 1 → ∃ v : (ZMod 8)ˣ, ∃ c : ZMod 8,
    (v = 1 ∨ v = -1) ∧ aff8 v (2 * c) * aff8 u b * (aff8 v (2 * c))⁻¹ = d8 := by
  intro u b
  simp only [pow_two, aff8_inv, aff8_mul, aff8_eq_one_iff, aff8_eq_iff, d8]
  revert u b
  decide

theorem exists_conj_d8 {u : (ZMod 8)ˣ} {b : ZMod 8} (hb : dbit8 b = 1) (h2 : aff8 u b ^ 2 = 1) :
    ∃ ρ ∈ R8, ρ * aff8 u b * ρ⁻¹ = d8 := by
  obtain ⟨v, c, hv, h⟩ := conj_d8_of_odd u b hb h2
  exact ⟨_, ⟨v, c, hv, rfl⟩, h⟩

theorem conj_k8_odd : ∀ u b, dbit8 b = 1 → aff8 u b * k8 * (aff8 u b)⁻¹ ≠ k8 := by
  intro u b
  simp only [aff8_inv, aff8_mul, k8]
  revert u b
  decide

theorem not_comm_k8 {u : (ZMod 8)ˣ} {b : ZMod 8} (hb : dbit8 b = 1) :
    aff8 u b * k8 ≠ k8 * aff8 u b := by
  intro h
  apply conj_k8_odd u b hb
  rw [h, mul_inv_cancel_right]

theorem sq_R8 : ∀ v c, (v = 1 ∨ v = -1) → aff8 v (2 * c) ^ 2 = 1 ∨ aff8 v (2 * c) ^ 2 = z8 := by
  intro v c
  simp only [pow_two, aff8_mul, aff8_eq_one_iff, aff8_eq_iff, z8]
  revert v c
  decide

theorem sq_mem_R8 {ρ : Perm (ZMod 8)} (hρ : ρ ∈ R8) : ρ ^ 2 = 1 ∨ ρ ^ 2 = z8 := by
  obtain ⟨v, c, hv, rfl⟩ := hρ
  exact sq_R8 v c hv

theorem inv_R8 : ∀ v c, (v = 1 ∨ v = -1) → aff8 v (2 * c) ^ 2 ≠ 1 →
    aff8 v (2 * c) = aff8 1 2 ∨ aff8 v (2 * c) = aff8 1 6 := by
  intro v c
  simp only [pow_two, aff8_mul, aff8_eq_iff]
  revert v c
  decide

theorem refl_R8 : ∀ v c, (v = 1 ∨ v = -1) → ∀ s : ZMod 8, (s = 2 ∨ s = 6) →
    aff8 v (2 * c) * aff8 1 s * (aff8 v (2 * c))⁻¹ = (aff8 1 s)⁻¹ → v = -1 := by
  intro v c hv s hs
  simp only [aff8_inv, aff8_mul, aff8_eq_iff]
  revert v c s
  decide

theorem refl_mem : ∀ e : ZMod 8, dbit8 e = 0 → ∀ s : ZMod 8, (s = 2 ∨ s = 6) →
    (pE 0 (-1) e ∧ pE 2 (-1) (s + e)) ∨ (pE 2 (-1) e ∧ pE 0 (-1) (s + e)) := by decide

variable {X : Type} [Group X] {t : X} {L : Subgroup X}

@[expose] noncomputable def pre (A : L2Data t L) (P : Subgroup (Perm (ZMod 8))) : Subgroup X :=
  (P.comap A.ψ).map A.T.subtype

variable {A : L2Data t L}

theorem mem_pre {P : Subgroup (Perm (ZMod 8))} {g : X} :
    g ∈ pre A P ↔ g ∈ A.T ∧ ψX A g ∈ P := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, by change ψX A (g' : X) ∈ P; rw [ψX_of_mem g'.2]; exact hg'⟩
  · rintro ⟨hg, hP⟩
    exact ⟨⟨g, hg⟩, by rw [ψX_of_mem hg] at hP; exact hP, rfl⟩

theorem pre_le_T (P : Subgroup (Perm (ZMod 8))) : pre A P ≤ A.T := fun _ hg => (mem_pre.mp hg).1

theorem pre_inf (P Q : Subgroup (Perm (ZMod 8))) : pre A (P ⊓ Q) = pre A P ⊓ pre A Q := by
  ext g
  simp only [mem_inf, mem_pre]
  tauto

theorem t_mem_pre (P : Subgroup (Perm (ZMod 8))) : t ∈ pre A P :=
  mem_pre.mpr ⟨A.t_mem_T, by rw [ψX_t]; exact one_mem _⟩

theorem ψX_mem_H8' {g : X} (hg : g ∈ A.T) : ∃ u b, aff8 u b = ψX A g := by
  rw [ψX_of_mem hg]
  exact A.ψ_mem_H8 _

variable [Finite X]

theorem mem_of_ψX_eq (C : A.CaseKD) {H : Subgroup X} (htH : t ∈ H) {g h : X} (hg : g ∈ A.T)
    (hh : h ∈ H) (hhT : h ∈ A.T) (hψ : ψX A g = ψX A h) : g ∈ H := by
  have hK : h⁻¹ * g ∈ A.K := by
    rw [← ψX_eq_one_iff (mul_mem (inv_mem hhT) hg), ψX_mul (inv_mem hhT) hg, ψX_inv hhT, hψ,
      inv_mul_cancel]
  have e : g = h * (h⁻¹ * g) := by group
  rw [e]
  rcases L2KD.eq_one_or_eq_t_of_mem_K C hK with h1 | h1 <;> rw [h1]
  · rw [mul_one]
    exact hh
  · exact mul_mem hh htH

theorem eq_or_eq_mul_t (C : A.CaseKD) {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T)
    (hψ : ψX A g = ψX A h) : g = h ∨ g = h * t := by
  have hK : h⁻¹ * g ∈ A.K := by
    rw [← ψX_eq_one_iff (mul_mem (inv_mem hh) hg), ψX_mul (inv_mem hh) hg, ψX_inv hh, hψ,
      inv_mul_cancel]
  rcases L2KD.eq_one_or_eq_t_of_mem_K C hK with h1 | h1
  · left
    calc g = h * (h⁻¹ * g) := by group
      _ = h := by rw [h1, mul_one]
  · right
    calc g = h * (h⁻¹ * g) := by group
      _ = h * t := by rw [h1]

end CFSG.ComponentClassification.HSFLit.KD46
