module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin.Amalg

open Equiv Equiv.Perm CFSG.ComponentClassification.PresentationLocal

variable {m N : ℕ}

@[expose] noncomputable def extPerm (ε : Fin N ↪ Fin m) : Perm (Fin N) →* Perm (Fin m) :=
  Perm.extendDomainHom ε.toEquivRange

theorem extPerm_apply_mem (ε : Fin N ↪ Fin m) (σ : Perm (Fin N)) (i : Fin N) :
    extPerm ε σ (ε i) = ε (σ i) := by
  classical
  have := Perm.extendDomain_apply_image σ ε.toEquivRange i
  simpa [extPerm] using this

theorem extPerm_apply_not_mem (ε : Fin N ↪ Fin m) (σ : Perm (Fin N)) {x : Fin m}
    (hx : x ∉ Set.range ε) : extPerm ε σ x = x := by
  classical
  exact Perm.extendDomain_apply_not_subtype σ ε.toEquivRange hx

theorem sign_extPerm (ε : Fin N ↪ Fin m) (σ : Perm (Fin N)) :
    Perm.sign (extPerm ε σ) = Perm.sign σ := by
  classical
  exact Perm.sign_extendDomain σ ε.toEquivRange

theorem extPerm_injective (ε : Fin N ↪ Fin m) : Function.Injective (extPerm ε) := by
  intro σ τ h
  refine Equiv.ext fun i => ε.injective ?_
  rw [← extPerm_apply_mem, ← extPerm_apply_mem, h]

@[expose] noncomputable def altExt (ε : Fin N ↪ Fin m) :
    alternatingGroup (Fin N) →* alternatingGroup (Fin m) :=
  ((extPerm ε).comp (alternatingGroup (Fin N)).subtype).codRestrict _ fun σ => by
    rw [MonoidHom.comp_apply, mem_alternatingGroup, sign_extPerm]
    exact σ.2

theorem altExt_coe (ε : Fin N ↪ Fin m) (σ : alternatingGroup (Fin N)) :
    ((altExt ε σ : alternatingGroup (Fin m)) : Perm (Fin m)) = extPerm ε σ := rfl

theorem altExt_injective (ε : Fin N ↪ Fin m) : Function.Injective (altExt ε) := fun _ _ h =>
  Subtype.ext (extPerm_injective ε (congrArg Subtype.val h))

theorem exists_altExt_eq (ε : Fin N ↪ Fin m) (π : alternatingGroup (Fin m))
    (hπ : ∀ x, x ∉ Set.range ε → (π : Perm (Fin m)) x = x) :
    ∃ σ : alternatingGroup (Fin N), altExt ε σ = π := by
  classical
  have hrange : ∀ i, (π : Perm (Fin m)) (ε i) ∈ Set.range ε := by
    intro i
    by_contra h
    have h1 := hπ _ h
    exact h (by rw [(π : Perm (Fin m)).injective h1]; exact Set.mem_range_self i)
  set f : Fin N → Fin N := fun i => (hrange i).choose with hf
  have hfi : ∀ i, ε (f i) = (π : Perm (Fin m)) (ε i) := fun i => (hrange i).choose_spec
  have hinj : Function.Injective f := fun i j hij =>
    ε.injective ((π : Perm (Fin m)).injective (by rw [← hfi, ← hfi, hij]))
  set σ₀ : Perm (Fin N) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hext : extPerm ε σ₀ = π := by
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ Set.range ε
    · obtain ⟨i, rfl⟩ := hx
      rw [extPerm_apply_mem]
      exact hfi i
    · rw [extPerm_apply_not_mem ε _ hx, hπ x hx]
  have hσ₀ : σ₀ ∈ alternatingGroup (Fin N) := by
    rw [mem_alternatingGroup, ← sign_extPerm ε, hext]
    exact π.2
  exact ⟨⟨σ₀, hσ₀⟩, Subtype.ext hext⟩

section Carmichael

variable (hm : 3 ≤ m) (hN : 3 ≤ N)

theorem two_le_of_fix (ε : Fin N ↪ Fin m) (h0 : ε ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (h1 : ε ⟨1, by omega⟩ = ⟨1, by omega⟩) (j : CarmichaelIndex N) : 2 ≤ ((ε j.1 : Fin m) : ℕ) := by
  have hj := j.2
  have hne0 : ε j.1 ≠ ⟨0, by omega⟩ := fun h => by
    rw [← h0] at h
    have := congrArg Fin.val (ε.injective h)
    simp at this
    omega
  have hne1 : ε j.1 ≠ ⟨1, by omega⟩ := fun h => by
    rw [← h1] at h
    have := congrArg Fin.val (ε.injective h)
    simp at this
    omega
  by_contra hlt
  push Not at hlt
  interval_cases hv : ((ε j.1 : Fin m) : ℕ)
  · exact hne0 (Fin.ext hv)
  · exact hne1 (Fin.ext hv)

include hm hN in
theorem altExt_carmichaelCycle (ε : Fin N ↪ Fin m) (h0 : ε ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (h1 : ε ⟨1, by omega⟩ = ⟨1, by omega⟩) (j : CarmichaelIndex N) :
    altExt ε (carmichaelCycle j) = carmichaelCycle ⟨ε j.1, two_le_of_fix hm hN ε h0 h1 j⟩ := by
  have hj := j.2
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rw [altExt_coe]
  show extPerm ε (carmichaelPerm j) x = carmichaelPerm ⟨ε j.1, two_le_of_fix hm hN ε h0 h1 j⟩ x
  have hk := two_le_of_fix hm hN ε h0 h1 j
  by_cases hx : x ∈ Set.range ε
  · obtain ⟨i, rfl⟩ := hx
    rw [extPerm_apply_mem, carmichaelPerm_apply, carmichaelPerm_apply]
    have hi0 : ((ε i : Fin m) : ℕ) = 0 ↔ (i : ℕ) = 0 := by
      constructor
      · intro h
        have : ε i = ε ⟨0, by omega⟩ := by rw [h0]; exact Fin.ext h
        exact congrArg Fin.val (ε.injective this)
      · intro h
        have : i = ⟨0, by omega⟩ := Fin.ext h
        rw [this, h0]
    have hi1 : ((ε i : Fin m) : ℕ) = 1 ↔ (i : ℕ) = 1 := by
      constructor
      · intro h
        have : ε i = ε ⟨1, by omega⟩ := by rw [h1]; exact Fin.ext h
        exact congrArg Fin.val (ε.injective this)
      · intro h
        have : i = ⟨1, by omega⟩ := Fin.ext h
        rw [this, h1]
    have hij : ε i = ε j.1 ↔ i = j.1 := ε.injective.eq_iff
    by_cases c0 : (i : ℕ) = 0
    · rw [ite_eq_left c0, ite_eq_left (hi0.mpr c0), ← h1]
    · rw [ite_eq_right c0, ite_eq_right (fun h => c0 (hi0.mp h))]
      by_cases c1 : (i : ℕ) = 1
      · rw [ite_eq_left c1, ite_eq_left (hi1.mpr c1)]
      · rw [ite_eq_right c1, ite_eq_right (fun h => c1 (hi1.mp h))]
        by_cases c2 : i = j.1
        · rw [ite_eq_left c2, ite_eq_left (hij.mpr c2), h0]
        · rw [ite_eq_right c2, ite_eq_right (fun h => c2 (hij.mp h))]
  · rw [extPerm_apply_not_mem ε _ hx, carmichaelPerm_apply]
    have hx0 : (x : ℕ) ≠ 0 := fun h => hx ⟨⟨0, by omega⟩, by rw [h0]; exact (Fin.ext h).symm⟩
    have hx1 : (x : ℕ) ≠ 1 := fun h => hx ⟨⟨1, by omega⟩, by rw [h1]; exact (Fin.ext h).symm⟩
    have hxk : x ≠ ε j.1 := fun h => hx ⟨j.1, h.symm⟩
    rw [ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hxk]

end Carmichael

section Glue

variable {A : Type*} [Group A]

theorem mul_comm_of_supp {T₁ T₂ : Set (Fin m)} (hT : Disjoint T₁ T₂) {x y : Perm (Fin m)}
    (hx : ∀ p ∉ T₁, x p = p) (hy : ∀ p ∉ T₂, y p = p) : x * y = y * x := by
  have hd : Perm.Disjoint x y := fun p => by
    by_cases h : p ∈ T₁
    · exact Or.inr (hy p (Set.disjoint_left.mp hT h))
    · exact Or.inl (hx p h)
  exact hd.commute.eq

theorem two_le_of_image (ε : Fin N ↪ Fin m) (hm : 3 ≤ m) (hN : 3 ≤ N)
    (h0 : ε ⟨0, by omega⟩ = ⟨0, by omega⟩) (h1 : ε ⟨1, by omega⟩ = ⟨1, by omega⟩) {j : Fin N}
    {k : CarmichaelIndex m} (hj : ε j = k.1) : 2 ≤ (j : ℕ) := by
  have hk := k.2
  by_contra hlt
  push Not at hlt
  interval_cases hv : (j : ℕ)
  · have : j = ⟨0, by omega⟩ := Fin.ext hv
    rw [this, h0] at hj
    have := congrArg Fin.val hj
    simp at this
    omega
  · have : j = ⟨1, by omega⟩ := Fin.ext hv
    rw [this, h1] at hj
    have := congrArg Fin.val hj
    simp at this
    omega

theorem exists_hom_of_two_charts (hm : 3 ≤ m) (hN : 3 ≤ N) (ε₁ ε₂ : Fin N ↪ Fin m)
    (h₁0 : ε₁ ⟨0, by omega⟩ = ⟨0, by omega⟩) (h₁1 : ε₁ ⟨1, by omega⟩ = ⟨1, by omega⟩)
    (h₂0 : ε₂ ⟨0, by omega⟩ = ⟨0, by omega⟩) (h₂1 : ε₂ ⟨1, by omega⟩ = ⟨1, by omega⟩)
    {q₁ q₂ a' c p₁ p₂ : Fin m}
    (hr₁ : ∀ x, x ∈ Set.range ε₁ ↔ x ≠ p₁ ∧ x ≠ p₂)
    (hr₂ : ∀ x, x ∈ Set.range ε₂ ↔ x ≠ q₁ ∧ x ≠ q₂)
    {T₁ T₂ : Set (Fin m)} (hT : Disjoint T₁ T₂)
    (hq₁ : q₁ ∈ T₁) (hq₂ : q₂ ∈ T₁) (h0T : (⟨0, by omega⟩ : Fin m) ∈ T₁) (ha' : a' ∈ T₁)
    (h1T : (⟨1, by omega⟩ : Fin m) ∈ T₂) (hc : c ∈ T₂) (hp₁ : p₁ ∈ T₂) (hp₂ : p₂ ∈ T₂)
    (ha'0 : a' ≠ ⟨0, by omega⟩) (ha'q₁ : a' ≠ q₁) (ha'q₂ : a' ≠ q₂)
    (hc1 : c ≠ ⟨1, by omega⟩) (hcp₁ : c ≠ p₁) (hcp₂ : c ≠ p₂)
    (f₁ f₂ : alternatingGroup (Fin N) →* A)
    (hagree : ∀ σ σ', altExt ε₁ σ = altExt ε₂ σ' → f₁ σ = f₂ σ')
    (hcross : ∀ σ σ' : alternatingGroup (Fin N), (∀ x ∉ T₁, extPerm ε₁ (σ : Perm (Fin N)) x = x) →
      (∀ x ∉ T₂, extPerm ε₂ (σ' : Perm (Fin N)) x = x) → f₁ σ * f₂ σ' = f₂ σ' * f₁ σ) :
    ∃ f : alternatingGroup (Fin m) →* A, f.comp (altExt ε₁) = f₁ ∧ f.comp (altExt ε₂) = f₂ := by
  classical
  set o : Fin m := ⟨0, by omega⟩ with ho
  set e : Fin m := ⟨1, by omega⟩ with he
  have hne : ∀ {u v : Fin m}, u ∈ T₁ → v ∈ T₂ → u ≠ v := fun hu hv h =>
    Set.disjoint_left.mp hT hu (h ▸ hv)
  have hc₁ : ∀ k : CarmichaelIndex m, k.1 ≠ p₁ → k.1 ≠ p₂ →
      ∃ σ, altExt ε₁ σ = carmichaelCycle k := by
    intro k h1 h2
    obtain ⟨j, hj⟩ := (hr₁ k.1).mpr ⟨h1, h2⟩
    refine ⟨carmichaelCycle ⟨j, two_le_of_image ε₁ hm hN h₁0 h₁1 hj⟩, ?_⟩
    rw [altExt_carmichaelCycle hm hN ε₁ h₁0 h₁1]
    exact congrArg carmichaelCycle (Subtype.ext hj)
  have hc₂ : ∀ k : CarmichaelIndex m, k.1 ≠ q₁ → k.1 ≠ q₂ →
      ∃ σ, altExt ε₂ σ = carmichaelCycle k := by
    intro k h1 h2
    obtain ⟨j, hj⟩ := (hr₂ k.1).mpr ⟨h1, h2⟩
    refine ⟨carmichaelCycle ⟨j, two_le_of_image ε₂ hm hN h₂0 h₂1 hj⟩, ?_⟩
    rw [altExt_carmichaelCycle hm hN ε₂ h₂0 h₂1]
    exact congrArg carmichaelCycle (Subtype.ext hj)
  have hpq : ∀ k : CarmichaelIndex m, ¬ (k.1 ≠ p₁ ∧ k.1 ≠ p₂) → k.1 ≠ q₁ ∧ k.1 ≠ q₂ := by
    intro k h
    have hk : k.1 ∈ T₂ := by
      by_cases h1 : k.1 = p₁
      · exact h1 ▸ hp₁
      · have : k.1 = p₂ := by by_contra h2; exact h ⟨h1, h2⟩
        exact this ▸ hp₂
    exact ⟨fun h' => hne hq₁ hk h'.symm, fun h' => hne hq₂ hk h'.symm⟩
  set x : CarmichaelIndex m → A := fun k =>
    if h : k.1 ≠ p₁ ∧ k.1 ≠ p₂ then f₁ (hc₁ k h.1 h.2).choose
    else f₂ (hc₂ k (hpq k h).1 (hpq k h).2).choose with hxdef
  have hfix : ∀ (ε : Fin N ↪ Fin m) (σ : alternatingGroup (Fin N)) (k : CarmichaelIndex m),
      altExt ε σ = carmichaelCycle k → k.1 ∈ Set.range ε := by
    intro ε σ k hσ
    by_contra hk
    have h1 : extPerm ε σ k.1 = k.1 := extPerm_apply_not_mem ε _ hk
    have h2 : carmichaelPerm k k.1 = o := by
      have := k.2
      rw [carmichaelPerm_apply, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    have h3 : extPerm ε σ k.1 = carmichaelPerm k k.1 := by
      rw [← altExt_coe, hσ]
      rfl
    rw [h1, h2] at h3
    have := congrArg Fin.val h3
    have hk2 := k.2
    simp [ho] at this
    omega
  have hx₁ : ∀ k σ, altExt ε₁ σ = carmichaelCycle k → x k = f₁ σ := by
    intro k σ hσ
    have h : k.1 ≠ p₁ ∧ k.1 ≠ p₂ := (hr₁ k.1).mp (hfix ε₁ σ k hσ)
    rw [hxdef]
    simp only [dite_eq_left h]
    exact congrArg f₁ (altExt_injective ε₁ ((hc₁ k h.1 h.2).choose_spec.trans hσ.symm))
  have hx₂ : ∀ k σ, altExt ε₂ σ = carmichaelCycle k → x k = f₂ σ := by
    intro k σ hσ
    rw [hxdef]
    by_cases h : k.1 ≠ p₁ ∧ k.1 ≠ p₂
    · simp only [dite_eq_left h]
      exact hagree _ _ ((hc₁ k h.1 h.2).choose_spec.trans hσ.symm)
    · simp only [dite_eq_right h]
      exact congrArg f₂ (altExt_injective ε₂
        ((hc₂ k (hpq k h).1 (hpq k h).2).choose_spec.trans hσ.symm))
  have hrep : ∀ k : CarmichaelIndex m, (∃ σ, altExt ε₁ σ = carmichaelCycle k) ∨
      (∃ σ, altExt ε₂ σ = carmichaelCycle k) := by
    intro k
    by_cases h : k.1 ≠ p₁ ∧ k.1 ≠ p₂
    · exact Or.inl (hc₁ k h.1 h.2)
    · exact Or.inr (hc₂ k (hpq k h).1 (hpq k h).2)
  have hx3 : ∀ k, x k ^ 3 = 1 := by
    intro k
    rcases hrep k with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
    · rw [hx₁ k σ hσ, ← map_pow]
      have : σ ^ 3 = 1 := altExt_injective ε₁ (by
        rw [map_pow, hσ, carmichaelCycle_pow_three, map_one])
      rw [this, map_one]
    · rw [hx₂ k σ hσ, ← map_pow]
      have : σ ^ 3 = 1 := altExt_injective ε₂ (by
        rw [map_pow, hσ, carmichaelCycle_pow_three, map_one])
      rw [this, map_one]
  have hsame₁ : ∀ i j : CarmichaelIndex m, i ≠ j → (∃ σ, altExt ε₁ σ = carmichaelCycle i) →
      (∃ σ, altExt ε₁ σ = carmichaelCycle j) → (x i * x j) ^ 2 = 1 := by
    rintro i j hij ⟨σi, hσi⟩ ⟨σj, hσj⟩
    rw [hx₁ i σi hσi, hx₁ j σj hσj, ← map_mul, ← map_pow]
    have : (σi * σj) ^ 2 = 1 := altExt_injective ε₁ (by
      rw [map_pow, map_mul, hσi, hσj, carmichaelCycle_mul_sq i j hij, map_one])
    rw [this, map_one]
  have hsame₂ : ∀ i j : CarmichaelIndex m, i ≠ j → (∃ σ, altExt ε₂ σ = carmichaelCycle i) →
      (∃ σ, altExt ε₂ σ = carmichaelCycle j) → (x i * x j) ^ 2 = 1 := by
    rintro i j hij ⟨σi, hσi⟩ ⟨σj, hσj⟩
    rw [hx₂ i σi hσi, hx₂ j σj hσj, ← map_mul, ← map_pow]
    have : (σi * σj) ^ 2 = 1 := altExt_injective ε₂ (by
      rw [map_pow, map_mul, hσi, hσj, carmichaelCycle_mul_sq i j hij, map_one])
    rw [this, map_one]
  have ho₁ : o ∈ Set.range ε₁ := ⟨_, h₁0⟩
  have ho₂ : o ∈ Set.range ε₂ := ⟨_, h₂0⟩
  have he₁ : e ∈ Set.range ε₁ := ⟨_, h₁1⟩
  have he₂ : e ∈ Set.range ε₂ := ⟨_, h₂1⟩
  have hout₁ : ∀ w, w ∉ Set.range ε₁ → w = p₁ ∨ w = p₂ := fun w hw => by
    by_contra h
    push Not at h
    exact hw ((hr₁ w).mpr h)
  have hout₂ : ∀ w, w ∉ Set.range ε₂ → w = q₁ ∨ w = q₂ := fun w hw => by
    by_contra h
    push Not at h
    exact hw ((hr₂ w).mpr h)
  have hfour : ∀ w, (w = q₁ ∨ w = q₂ ∨ w = p₁ ∨ w = p₂) → w ≠ o ∧ w ≠ e := by
    intro w hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨fun h => ((hr₂ _).mp (h ▸ ho₂)).1 rfl, fun h => ((hr₂ _).mp (h ▸ he₂)).1 rfl⟩
    · exact ⟨fun h => ((hr₂ _).mp (h ▸ ho₂)).2 rfl, fun h => ((hr₂ _).mp (h ▸ he₂)).2 rfl⟩
    · exact ⟨fun h => ((hr₁ _).mp (h ▸ ho₁)).1 rfl, fun h => ((hr₁ _).mp (h ▸ he₁)).1 rfl⟩
    · exact ⟨fun h => ((hr₁ _).mp (h ▸ ho₁)).2 rfl, fun h => ((hr₁ _).mp (h ▸ he₁)).2 rfl⟩
  have hval0 : ∀ w : Fin m, w ≠ o → (w : ℕ) ≠ 0 := fun w h h' => h (Fin.ext h')
  have hval1 : ∀ w : Fin m, w ≠ e → (w : ℕ) ≠ 1 := fun w h h' => h (Fin.ext h')
  have hcrossPair : ∀ q p : CarmichaelIndex m, (q.1 = q₁ ∨ q.1 = q₂) → (p.1 = p₁ ∨ p.1 = p₂) →
      (x q * x p) ^ 2 = 1 := by
    intro q p hq hp
    have hqT : q.1 ∈ T₁ := by rcases hq with h | h <;> rw [h] <;> assumption
    have hpT : p.1 ∈ T₂ := by rcases hp with h | h <;> rw [h] <;> assumption
    have hq2 := q.2
    have hp2 := p.2
    have hqo : q.1 ≠ o := (hfour q.1 (by rcases hq with h | h <;> simp [h])).1
    have hpe : p.1 ≠ e := (hfour p.1 (by rcases hp with h | h <;> simp [h])).2
    have hqa' : q.1 ≠ a' := by rcases hq with h | h <;> rw [h] <;> [exact ha'q₁.symm; exact ha'q₂.symm]
    have hpc : p.1 ≠ c := by rcases hp with h | h <;> rw [h] <;> [exact hcp₁.symm; exact hcp₂.symm]
    have hoa' : o ≠ a' := ha'0.symm
    have hec : e ≠ c := hc1.symm
    have hqp : q ≠ p := fun h => hne hqT hpT (congrArg Subtype.val h)
    set X : Perm (Fin m) := swap q.1 a' * swap q.1 o with hX
    set Yp : Perm (Fin m) := swap e c * swap e p.1 with hY
    have hXA : X ∈ alternatingGroup (Fin m) :=
      (isThreeCycle_swap_mul_swap_same hqa' hqo ha'0).mem_alternatingGroup
    have hYA : Yp ∈ alternatingGroup (Fin m) :=
      (isThreeCycle_swap_mul_swap_same hec hpe.symm hpc.symm).mem_alternatingGroup
    have hXfix : ∀ w, w ≠ q.1 → w ≠ a' → w ≠ o → X w = w := fun w h1 h2 h3 => by
      rw [hX, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
    have hYfix : ∀ w, w ≠ e → w ≠ c → w ≠ p.1 → Yp w = w := fun w h1 h2 h3 => by
      rw [hY, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
    have hXs : ∀ w ∉ T₁, X w = w := fun w hw =>
      hXfix w (fun h => hw (h ▸ hqT)) (fun h => hw (h ▸ ha')) (fun h => hw (h ▸ h0T))
    have hYs : ∀ w ∉ T₂, Yp w = w := fun w hw =>
      hYfix w (fun h => hw (h ▸ h1T)) (fun h => hw (h ▸ hc)) (fun h => hw (h ▸ hpT))
    have hXq : X q.1 = o := by
      rw [hX, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hqo.symm hoa']
    have hYe : Yp e = p.1 := by
      rw [hY, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpe hpc]
    have hcq : carmichaelPerm q q.1 = o := by
      rw [carmichaelPerm_apply, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left rfl]
    have hcp : carmichaelPerm p e = p.1 := by
      rw [carmichaelPerm_apply, ite_eq_right (by simp [he]), ite_eq_left (by simp [he])]
    have hcfix : ∀ (k : CarmichaelIndex m) (w : Fin m), w ≠ o → w ≠ e → w ≠ k.1 →
        carmichaelPerm k w = w := fun k w h0 h1 hk => by
      rw [carmichaelPerm_apply, ite_eq_right (hval0 w h0), ite_eq_right (hval1 w h1),
        ite_eq_right hk]
    set S : Perm (Fin m) := X⁻¹ * carmichaelPerm q with hS
    set S' : Perm (Fin m) := carmichaelPerm p * Yp⁻¹ with hS'
    have hSfix : ∀ w, (w = q₁ ∨ w = q₂ ∨ w = p₁ ∨ w = p₂) → S w = w := by
      intro w hw
      obtain ⟨hwo, hwe⟩ := hfour w hw
      show X⁻¹ (carmichaelPerm q w) = w
      by_cases hwq : w = q.1
      · rw [hwq, hcq, Perm.inv_eq_iff_eq, hXq]
      · have hwa' : w ≠ a' := by
          rcases hw with rfl | rfl | rfl | rfl
          · exact ha'q₁.symm
          · exact ha'q₂.symm
          · exact fun h => hne ha' hp₁ h.symm
          · exact fun h => hne ha' hp₂ h.symm
        rw [hcfix q w hwo hwe hwq, Perm.inv_eq_iff_eq, hXfix w hwq hwa' hwo]
    have hS'fix : ∀ w, (w = q₁ ∨ w = q₂ ∨ w = p₁ ∨ w = p₂) → S' w = w := by
      intro w hw
      obtain ⟨hwo, hwe⟩ := hfour w hw
      show carmichaelPerm p (Yp⁻¹ w) = w
      by_cases hwp : w = p.1
      · have : Yp⁻¹ p.1 = e := by rw [Perm.inv_eq_iff_eq, hYe]
        rw [hwp, this, hcp]
      · have hwc : w ≠ c := by
          rcases hw with rfl | rfl | rfl | rfl
          · exact hne hq₁ hc
          · exact hne hq₂ hc
          · exact hcp₁.symm
          · exact hcp₂.symm
        have : Yp⁻¹ w = w := by rw [Perm.inv_eq_iff_eq, hYfix w hwe hwc hwp]
        rw [this, hcfix p w hwo hwe hwp]
    have hfix₁ : ∀ π : Perm (Fin m), (∀ w, (w = q₁ ∨ w = q₂ ∨ w = p₁ ∨ w = p₂) → π w = w) →
        ∀ w, w ∉ Set.range ε₁ → π w = w := fun π hπ w hw => by
      rcases hout₁ w hw with h | h
      · exact hπ w (Or.inr (Or.inr (Or.inl h)))
      · exact hπ w (Or.inr (Or.inr (Or.inr h)))
    have hfix₂ : ∀ π : Perm (Fin m), (∀ w, (w = q₁ ∨ w = q₂ ∨ w = p₁ ∨ w = p₂) → π w = w) →
        ∀ w, w ∉ Set.range ε₂ → π w = w := fun π hπ w hw => by
      rcases hout₂ w hw with h | h
      · exact hπ w (Or.inl h)
      · exact hπ w (Or.inr (Or.inl h))
    obtain ⟨ξ, hξ⟩ := exists_altExt_eq ε₁ ⟨X, hXA⟩ fun w hw => by
      rcases hout₁ w hw with h | h
      · exact hXs w fun hT' => hne hT' hp₁ h
      · exact hXs w fun hT' => hne hT' hp₂ h
    obtain ⟨υ, hυ⟩ := exists_altExt_eq ε₂ ⟨Yp, hYA⟩ fun w hw => by
      rcases hout₂ w hw with h | h
      · exact hYs w fun hT' => hne hq₁ hT' h.symm
      · exact hYs w fun hT' => hne hq₂ hT' h.symm
    have hSA : S ∈ alternatingGroup (Fin m) :=
      (alternatingGroup (Fin m)).mul_mem ((alternatingGroup (Fin m)).inv_mem hXA)
        (carmichaelPerm_mem q)
    have hS'A : S' ∈ alternatingGroup (Fin m) :=
      (alternatingGroup (Fin m)).mul_mem (carmichaelPerm_mem p)
        ((alternatingGroup (Fin m)).inv_mem hYA)
    have hSS'fix : ∀ w, (w = q₁ ∨ w = q₂ ∨ w = p₁ ∨ w = p₂) → (S * S') w = w := fun w hw => by
      rw [Perm.mul_apply, hS'fix w hw, hSfix w hw]
    obtain ⟨ζs₁, hζs₁⟩ := exists_altExt_eq ε₁ ⟨S, hSA⟩ (hfix₁ S hSfix)
    obtain ⟨ζs₂, hζs₂⟩ := exists_altExt_eq ε₂ ⟨S, hSA⟩ (hfix₂ S hSfix)
    obtain ⟨ζt₂, hζt₂⟩ := exists_altExt_eq ε₂ ⟨S', hS'A⟩ (hfix₂ S' hS'fix)
    obtain ⟨ζu₁, hζu₁⟩ := exists_altExt_eq ε₁ ⟨S * S',
      (alternatingGroup (Fin m)).mul_mem hSA hS'A⟩ (hfix₁ _ hSS'fix)
    have hxq : x q = f₁ (ξ * ζs₁) := hx₁ q _ (by
      rw [map_mul, hξ, hζs₁]
      apply Subtype.ext
      show X * S = carmichaelPerm q
      rw [hS, mul_inv_cancel_left])
    have hxp : x p = f₂ (ζt₂ * υ) := hx₂ p _ (by
      rw [map_mul, hζt₂, hυ]
      apply Subtype.ext
      show S' * Yp = carmichaelPerm p
      rw [hS', inv_mul_cancel_right])
    have hF₁ : f₁ ζs₁ = f₂ ζs₂ := hagree _ _ (hζs₁.trans hζs₂.symm)
    have hF₂ : f₁ ζu₁ = f₂ (ζs₂ * ζt₂) := hagree _ _ (by
      rw [hζu₁, map_mul, hζs₂, hζt₂]
      rfl)
    have hF : f₁ ζs₁ * f₂ ζt₂ = f₁ ζu₁ := by rw [hF₁, ← map_mul, hF₂]
    have hxy : f₁ ξ * f₂ υ = f₂ υ * f₁ ξ := hcross ξ υ
      (by rw [← altExt_coe, hξ]; exact hXs) (by rw [← altExt_coe, hυ]; exact hYs)
    have key : (x q * x p) ^ 2 = f₁ (ξ * ζu₁ * ξ) * f₂ (υ * (ζs₂ * ζt₂) * υ) := by
      rw [hxq, hxp, map_mul, map_mul]
      calc (f₁ ξ * f₁ ζs₁ * (f₂ ζt₂ * f₂ υ)) ^ 2
          = (f₁ ξ * (f₁ ζs₁ * f₂ ζt₂) * f₂ υ) ^ 2 := by group
        _ = (f₁ ξ * f₁ ζu₁ * f₂ υ) ^ 2 := by rw [hF]
        _ = f₁ ξ * f₁ ζu₁ * (f₂ υ * f₁ ξ) * f₁ ζu₁ * f₂ υ := by rw [pow_two]; group
        _ = f₁ ξ * f₁ ζu₁ * (f₁ ξ * f₂ υ) * f₁ ζu₁ * f₂ υ := by rw [hxy]
        _ = f₁ ξ * f₁ ζu₁ * f₁ ξ * (f₂ υ * f₁ ζu₁ * f₂ υ) := by group
        _ = f₁ ξ * f₁ ζu₁ * f₁ ξ * (f₂ υ * f₂ (ζs₂ * ζt₂) * f₂ υ) := by rw [← hF₂]
        _ = f₁ (ξ * ζu₁ * ξ) * f₂ (υ * (ζs₂ * ζt₂) * υ) := by simp only [map_mul]
    have hcc : (carmichaelPerm q * carmichaelPerm p) ^ 2 = 1 :=
      congrArg Subtype.val (carmichaelCycle_mul_sq q p hqp)
    have hdec : carmichaelPerm q * carmichaelPerm p = X * (S * S') * Yp := by
      rw [hS, hS']
      group
    have hXY : X * Yp = Yp * X := mul_comm_of_supp hT hXs hYs
    have h1 : X * (S * S') * Yp * (X * (S * S') * Yp) = 1 := by
      rw [← hdec, ← pow_two]
      exact hcc
    have h2 : X * (S * S') * X * (Yp * (S * S') * Yp) = 1 := by
      calc X * (S * S') * X * (Yp * (S * S') * Yp)
          = X * (S * S') * (X * Yp) * (S * S') * Yp := by group
        _ = X * (S * S') * (Yp * X) * (S * S') * Yp := by rw [hXY]
        _ = X * (S * S') * Yp * (X * (S * S') * Yp) := by group
        _ = 1 := h1
    have hu : altExt ε₁ (ξ * ζu₁ * ξ) = altExt ε₂ ((υ * (ζs₂ * ζt₂) * υ)⁻¹) := by
      rw [map_mul, map_mul, hξ, hζu₁, map_inv, map_mul, map_mul, map_mul, hυ, hζs₂, hζt₂]
      apply Subtype.ext
      show X * (S * S') * X = (Yp * (S * S') * Yp)⁻¹
      exact eq_inv_of_mul_eq_one_left h2
    rw [key, hagree _ _ hu, map_inv, inv_mul_cancel]
  have hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := by
    intro i j hij
    by_cases hi : i.1 ≠ p₁ ∧ i.1 ≠ p₂
    · by_cases hj : j.1 ≠ p₁ ∧ j.1 ≠ p₂
      · exact hsame₁ i j hij (hc₁ i hi.1 hi.2) (hc₁ j hj.1 hj.2)
      · have hj' := hpq j hj
        by_cases hi2 : i.1 ≠ q₁ ∧ i.1 ≠ q₂
        · exact hsame₂ i j hij (hc₂ i hi2.1 hi2.2) (hc₂ j hj'.1 hj'.2)
        · have hiq : i.1 = q₁ ∨ i.1 = q₂ := by
            by_contra h
            push Not at h
            exact hi2 h
          have hjp : j.1 = p₁ ∨ j.1 = p₂ := by
            by_contra h
            push Not at h
            exact hj h
          exact hcrossPair i j hiq hjp
    · have hi' := hpq i hi
      by_cases hj2 : j.1 ≠ q₁ ∧ j.1 ≠ q₂
      · exact hsame₂ i j hij (hc₂ i hi'.1 hi'.2) (hc₂ j hj2.1 hj2.2)
      · have hjq : j.1 = q₁ ∨ j.1 = q₂ := by
          by_contra h
          push Not at h
          exact hj2 h
        have hip : i.1 = p₁ ∨ i.1 = p₂ := by
          by_contra h
          push Not at h
          exact hi h
        have h := hcrossPair j i hjq hip
        calc (x i * x j) ^ 2 = (x j)⁻¹ * (x j * x i) ^ 2 * x j := by
              rw [pow_two, pow_two]
              group
          _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  obtain ⟨F, hF⟩ := exists_hom_carmichaelCycle hm x hx3 hxx
  refine ⟨F, ?_, ?_⟩
  · refine MonoidHom.eq_of_eqOn_dense (closure_range_carmichaelCycle hN) ?_
    rintro _ ⟨j, rfl⟩
    rw [MonoidHom.comp_apply, altExt_carmichaelCycle hm hN ε₁ h₁0 h₁1, hF]
    exact hx₁ _ _ (altExt_carmichaelCycle hm hN ε₁ h₁0 h₁1 j)
  · refine MonoidHom.eq_of_eqOn_dense (closure_range_carmichaelCycle hN) ?_
    rintro _ ⟨j, rfl⟩
    rw [MonoidHom.comp_apply, altExt_carmichaelCycle hm hN ε₂ h₂0 h₂1, hF]
    exact hx₂ _ _ (altExt_carmichaelCycle hm hN ε₂ h₂0 h₂1 j)

end Glue

end CFSG.ClassicalInvolution.Q3.TC.Thin.Amalg
