module

public import CFSG.Timmesfeld.ARS.ExclNSExceptional

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS.ExclNS

@[expose] def f4q : Fin 4 → ℤ := ![2, 2, 1, 1]

theorem f4q_pos : ∀ k, 0 < f4q k := by decide

theorem f4q_symm : ∀ i j, f4q i * f4M i j = f4q j * f4M j i := by decide

@[expose] def formF (x y : Fin 4 → ℤ) : ℤ :=
  x ⬝ᵥ Matrix.mulVec (Matrix.of fun i j => f4q i * f4M i j) y

variable (hA : TauCeti.IsFiniteType f4M)

noncomputable abbrev form : InvForm f4M := InvForm.ofSymmetrizer hA f4q f4q_pos f4q_symm

theorem form_apply (x y : Fin 4 → ℤ) : (form hA).Q x y = formF x y :=
  symForm_apply _ x y

theorem form_le_four {ε : Fin 4 → ℤ} (hε : ε ∈ roots hA ∅) : (form hA).Q ε ε ≤ 4 := by
  obtain ⟨i, hi⟩ := (form hA).exists_eq_of_mem_roots hA hε
  rw [hi, form_apply]
  fin_cases i <;> decide

theorem form_weylAction_single (w : (coxeterMatrix hA).Group) (i : Fin 4) :
    (form hA).Q (weylAction hA w (Pi.single i 1)) (weylAction hA w (Pi.single i 1)) =
      formF (Pi.single i 1) (Pi.single i 1) := by
  rw [(form hA).weylAction hA w, form_apply]

theorem form_neg_right (γ δ : Fin 4 → ℤ) : (form hA).Q γ (-δ) = -(form hA).Q γ δ :=
  map_neg _ δ

theorem form_neg_left (γ δ : Fin 4 → ℤ) : (form hA).Q (-γ) δ = -(form hA).Q γ δ := by
  rw [(form hA).symm, form_neg_right, (form hA).symm]

theorem form_add_left (x y z : Fin 4 → ℤ) :
    (form hA).Q (x + y) z = (form hA).Q x z + (form hA).Q y z := by
  rw [map_add, LinearMap.add_apply]

theorem form_add_smul (γ δ : Fin 4 → ℤ) (a b : ℤ) :
    (form hA).Q (a • γ + b • δ) (a • γ + b • δ) =
      a ^ 2 * (form hA).Q γ γ + 2 * a * b * (form hA).Q γ δ + b ^ 2 * (form hA).Q δ δ := by
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    (form hA).symm δ γ]
  ring

theorem norm_le_of_root {γ δ : Fin 4 → ℤ} {a b : ℕ} (h : a • γ + b • δ ∈ roots hA ∅) :
    (a : ℤ) ^ 2 * (form hA).Q γ γ + 2 * a * b * (form hA).Q γ δ +
      (b : ℤ) ^ 2 * (form hA).Q δ δ ≤ 4 := by
  have h4 := form_le_four hA h
  have e1 : a • γ = (a : ℤ) • γ := by simp
  have e2 : b • δ = (b : ℤ) • δ := by simp
  rwa [e1, e2, form_add_smul] at h4

theorem forall_notMem_openCone_of_nonneg {γ δ : Fin 4 → ℤ} (hg : 0 ≤ (form hA).Q γ γ)
    (hd : 0 ≤ (form hA).Q δ δ) (hc : 0 ≤ (form hA).Q γ δ)
    (h : 4 < (form hA).Q γ γ + (form hA).Q δ δ + 2 * (form hA).Q γ δ) :
    ∀ ε ∈ roots hA ∅, ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ε = a • γ + b • δ := by
  rintro ε hε ⟨a, b, ha, hb, rfl⟩
  have hn := norm_le_of_root hA hε
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have h1 : (form hA).Q γ γ ≤ (a : ℤ) ^ 2 * (form hA).Q γ γ :=
    le_mul_of_one_le_left hg (by nlinarith)
  have h2 : (form hA).Q δ δ ≤ (b : ℤ) ^ 2 * (form hA).Q δ δ :=
    le_mul_of_one_le_left hd (by nlinarith)
  have h3 : 2 * (form hA).Q γ δ ≤ 2 * a * b * (form hA).Q γ δ := by
    have hab : (1 : ℤ) ≤ a * b := by nlinarith
    nlinarith
  linarith

theorem eq_add_of_mem_openCone_long {γ δ ε : Fin 4 → ℤ} (hg : (form hA).Q γ γ = 4)
    (hd : (form hA).Q δ δ = 4) (hc : (form hA).Q γ δ = -2)
    (hε : ε ∈ openCone (roots hA ∅) γ δ) : ε = γ + δ := by
  obtain ⟨hεR, a, b, ha, hb, rfl⟩ := hε
  have hn := norm_le_of_root hA hεR
  rw [hg, hd, hc] at hn
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have e1 : (a : ℤ) = 1 := by nlinarith
  have e2 : (b : ℤ) = 1 := by nlinarith
  have : a = 1 := by exact_mod_cast e1
  have : b = 1 := by exact_mod_cast e2
  subst a b
  simp

theorem eq_of_mem_openCone_shortLong {γ δ ε : Fin 4 → ℤ} (hg : (form hA).Q γ γ = 2)
    (hd : (form hA).Q δ δ = 4) (hc : (form hA).Q γ δ = -2)
    (hε : ε ∈ openCone (roots hA ∅) γ δ) : ε = γ + δ ∨ ε = 2 • γ + δ := by
  obtain ⟨hεR, a, b, ha, hb, rfl⟩ := hε
  have hn := norm_le_of_root hA hεR
  rw [hg, hd, hc] at hn
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have e2 : (b : ℤ) = 1 := by nlinarith [sq_nonneg ((a : ℤ) - b)]
  have : b = 1 := by exact_mod_cast e2
  subst b
  have ha2 : (a : ℤ) ≤ 2 := by nlinarith
  have : a ≤ 2 := by exact_mod_cast ha2
  interval_cases a
  · left; simp
  · right; simp

theorem linIndepPair_of_ne {γ δ : Fin 4 → ℤ} (hγ : γ ∈ roots hA ∅) (hδ : δ ∈ roots hA ∅)
    (h1 : δ ≠ γ) (h2 : δ ≠ -γ) : LinIndepPair γ δ := by
  by_contra h
  rcases eq_or_eq_neg_of_not_linIndepPair hA rfl hγ hδ h with e | e
  · exact h1 e
  · exact h2 e

theorem mem_roots_of_eq {v : Fin 4 → ℤ} (w : (coxeterMatrix hA).Group) (i : Fin 4)
    (h : weylAction hA w (Pi.single i 1) = v) : v ∈ roots hA ∅ :=
  Or.inl ⟨w, i, h.symm⟩

theorem weylAction_simple_eq (k : Fin 4) (v : Fin 4 → ℤ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple k) v = reflF f4M k v := by
  rw [weylAction_simple, reflection_eq_reflF]

end CFSG.LargeExtraspecial.A2Mod.FrF
