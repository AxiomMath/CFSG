module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanBasic

public section

namespace CFSG.QuasithinUnique.ONan

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

theorem hyperplane_transitive (S : Setting X R A C)
    (hX : ∀ W : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hA : 2 ≤ finrank (ZMod 2) A) (hC : finrank (ZMod 2) C = 1) :
    ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w := by
  classical
  obtain ⟨c, hc0, hCc⟩ := finrank_eq_one_iff'.mp hC
  have hcC : (c : V) ∈ C := c.2
  have hc0' : (c : V) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hCc' : ∀ e ∈ C, e = 0 ∨ e = (c : V) := by
    intro e he
    obtain ⟨k, hk⟩ := hCc ⟨e, he⟩
    have hk' : k • (c : V) = e := congrArg Subtype.val hk
    rcases zmod_smul_eq k (c : V) with h | h
    · left; rw [← hk', h]
    · right; rw [← hk', h]
  generalize (c : V) = c' at hcC hc0' hCc'
  let Δ : Set V := {d | ∃ x ∈ X, x c' = d}
  have hΔx : ∀ x ∈ X, ∀ d ∈ Δ, x d ∈ Δ := by
    rintro x hx _ ⟨y, hy, rfl⟩
    exact ⟨x * y, X.mul_mem hx hy, rfl⟩
  have hΔ0 : ∀ d ∈ Δ, d ≠ 0 := by
    rintro _ ⟨y, hy, rfl⟩ h
    exact hc0' ((map_eq_zero_iff y y.injective).mp h)
  have hΔc : c' ∈ Δ := ⟨1, X.one_mem, rfl⟩
  have hmove : ∀ d ∈ Δ, ∀ a ∈ A, ∀ e ∈ C, a + e = d → a ≠ 0 →
      ∀ a' ∈ A, a' ≠ 0 → a' + e ∈ Δ := by
    intro d hd a ha e he hde ha0 a' ha' ha'0
    obtain ⟨r, hr, hra⟩ := S.trans a ha a' ha' ha0 ha'0
    have := hΔx r (S.le hr) d hd
    rwa [← hde, map_add, hra, S.fixes r hr e he] at this
  have hAinv : ¬ ∀ x ∈ X, ∀ a ∈ A, x a ∈ A := by
    intro h
    rcases hX A h with h0 | h1
    · rw [h0, finrank_bot] at hA
      omega
    · exact hc0' (S.eq_zero_of_mem (h1 ▸ Submodule.mem_top) hcC)
  have hCinv : ¬ ∀ x ∈ X, ∀ e ∈ C, x e ∈ C := by
    intro h
    rcases hX C h with h0 | h1
    · have : c' ∈ (⊥ : Submodule (ZMod 2) V) := h0 ▸ hcC
      exact hc0' ((Submodule.mem_bot _).mp this)
    · obtain ⟨a, haA, ha0, -⟩ := exists_mem_ne_two A hA 0 0
      exact ha0 (S.eq_zero_of_mem haA (h1 ▸ Submodule.mem_top))
  have hall : ∀ v : V, v ≠ 0 → v ∈ Δ := by
    by_cases h1 : ∃ a ∈ A, a ≠ 0 ∧ a ∈ Δ
    · by_cases h2 : ∃ a ∈ A, a ≠ 0 ∧ a + c' ∈ Δ
      · obtain ⟨a₁, ha₁A, ha₁0, ha₁Δ⟩ := h1
        obtain ⟨a₂, ha₂A, ha₂0, ha₂Δ⟩ := h2
        intro v hv
        obtain ⟨a, haA, e, heC, rfl⟩ := S.decomp v
        by_cases ha0 : a = 0
        · subst ha0
          rcases hCc' e heC with rfl | rfl
          · exact absurd (zero_add 0) hv
          · rw [zero_add]; exact hΔc
        · rcases hCc' e heC with rfl | rfl
          · have := hmove a₁ ha₁Δ a₁ ha₁A 0 (Submodule.zero_mem _) (add_zero _) ha₁0 a haA ha0
            exact this
          · exact hmove _ ha₂Δ a₂ ha₂A e heC rfl ha₂0 a haA ha0
      · exfalso
        obtain ⟨a₁, ha₁A, ha₁0, ha₁Δ⟩ := h1
        have hA0 : ∀ a ∈ A, a ≠ 0 → a ∈ Δ := by
          intro a ha ha0
          have := hmove a₁ ha₁Δ a₁ ha₁A 0 (Submodule.zero_mem _) (add_zero _) ha₁0 a ha ha0
          rwa [add_zero] at this
        have hβ : ∀ d ∈ Δ, d = c' ∨ (d ∈ A ∧ d ≠ 0) := by
          intro d hd
          obtain ⟨a, haA, e, heC, rfl⟩ := S.decomp d
          by_cases ha0 : a = 0
          · subst ha0
            rw [zero_add] at hd ⊢
            rcases hCc' e heC with h | h
            · exact absurd h (hΔ0 _ hd)
            · exact Or.inl h
          · rcases hCc' e heC with rfl | rfl
            · rw [add_zero] at hd ⊢
              exact Or.inr ⟨haA, ha0⟩
            · exact absurd ⟨a, haA, ha0, hd⟩ h2
        apply hAinv
        intro x hx a ha
        by_cases ha0 : a = 0
        · rw [ha0, map_zero]; exact Submodule.zero_mem _
        have hxa : x a ∈ Δ := hΔx x hx a (hA0 a ha ha0)
        rcases hβ _ hxa with hxac | ⟨hxaA, -⟩
        · exfalso
          obtain ⟨a', ha'A, ha'0, ha'a⟩ := exists_mem_ne_two A hA 0 a
          have hxa' : x a' ∈ Δ := hΔx x hx a' (hA0 a' ha'A ha'0)
          have hsum : a + a' ∈ Δ :=
            hA0 (a + a') (A.add_mem ha ha'A) ((add_ne_zero_iff_ne a a').mpr (Ne.symm ha'a))
          have hxsum : x (a + a') ∈ Δ := hΔx x hx _ hsum
          rw [map_add, hxac] at hxsum
          rcases hβ _ hxsum with h | ⟨hA', -⟩
          · have h' : x a' = 0 := by simpa using h
            exact ha'0 ((map_eq_zero_iff x x.injective).mp h')
          · rcases hβ _ hxa' with h' | ⟨hxa'A, -⟩
            · exact ha'a (x.injective (h'.trans hxac.symm))
            · have : c' ∈ A := by
                have := A.add_mem hA' hxa'A
                rwa [add_add_self] at this
              exact hc0' (S.eq_zero_of_mem this hcC)
        · exact hxaA
    · by_cases h2 : ∃ a ∈ A, a ≠ 0 ∧ a + c' ∈ Δ
      · exfalso
        obtain ⟨a₂, ha₂A, ha₂0, ha₂Δ⟩ := h2
        have hAc : ∀ a ∈ A, a ≠ 0 → a + c' ∈ Δ := by
          intro a ha ha0
          exact hmove _ ha₂Δ a₂ ha₂A c' hcC rfl ha₂0 a ha ha0
        have hγ : ∀ d ∈ Δ, d + c' ∈ A := by
          intro d hd
          obtain ⟨a, haA, e, heC, rfl⟩ := S.decomp d
          by_cases ha0 : a = 0
          · subst ha0
            rw [zero_add] at hd ⊢
            rcases hCc' e heC with h | h
            · exact absurd h (hΔ0 _ hd)
            · rw [h, ZModModule.add_self]; exact Submodule.zero_mem _
          · rcases hCc' e heC with rfl | rfl
            · rw [add_zero] at hd
              exact absurd ⟨a, haA, ha0, hd⟩ h1
            · rwa [add_add_self]
        apply hAinv
        intro x hx a ha
        by_cases ha0 : a = 0
        · rw [ha0, map_zero]; exact Submodule.zero_mem _
        have hw : x (a + c') + c' ∈ A := hγ _ (hΔx x hx _ (hAc a ha ha0))
        have hu : x c' + c' ∈ A := hγ _ (hΔx x hx _ hΔc)
        have hxa : x a = (x (a + c') + c') + (x c' + c') := by
          rw [map_add, add_assoc (x a) (x c') c', add_add_self]
        rw [hxa]
        exact A.add_mem hw hu
      · exfalso
        have hα : ∀ d ∈ Δ, d ∈ C := by
          intro d hd
          obtain ⟨a, haA, e, heC, rfl⟩ := S.decomp d
          by_cases ha0 : a = 0
          · subst ha0
            rw [zero_add]; exact heC
          · rcases hCc' e heC with rfl | rfl
            · rw [add_zero] at hd
              exact absurd ⟨a, haA, ha0, hd⟩ h1
            · exact absurd ⟨a, haA, ha0, hd⟩ h2
        apply hCinv
        intro x hx e he
        rcases hCc' e he with rfl | rfl
        · rw [map_zero]; exact Submodule.zero_mem _
        · exact hα _ (hΔx x hx _ hΔc)
  intro v w hv hw
  obtain ⟨x, hx, hxv⟩ := hall v hv
  obtain ⟨y, hy, hyw⟩ := hall w hw
  refine ⟨y * x⁻¹, X.mul_mem hy (X.inv_mem hx), ?_⟩
  rw [← hxv, ← hyw]
  simp

end CFSG.QuasithinUnique.ONan
