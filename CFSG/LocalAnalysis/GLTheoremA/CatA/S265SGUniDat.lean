module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniFam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F] {σ : F ≃+* F} {d : ℕ}

private theorem exists_eigenchar {G : Type} [Group G] (ρ : G →* Matrix (Fin d) (Fin d) F)
    {v : Fin d → F} (hv : v ≠ 0) (hev : ∀ g, ∃ a : F, ρ g *ᵥ v = a • v) :
    ∃ θ : G →* Fˣ, ∀ g, ρ g *ᵥ v = (θ g : F) • v := by
  choose a ha using hev
  have hmul : ∀ g g', a (g * g') = a g * a g' := fun g g' => by
    refine smul_left_injective F hv ?_
    show a (g * g') • v = (a g * a g') • v
    rw [← ha, map_mul, ← Matrix.mulVec_mulVec, ha g', Matrix.mulVec_smul, ha g, smul_smul,
      mul_comm]
  have h1 : a 1 = 1 := by
    refine smul_left_injective F hv ?_
    show a 1 • v = (1 : F) • v
    rw [← ha, map_one, Matrix.one_mulVec, one_smul]
  exact ⟨MonoidHom.toHomUnits ⟨⟨a, h1⟩, hmul⟩, fun g => ha g⟩

private theorem map_eq_self_of_cube {ω : F} (hω : IsPrimitiveRoot ω 3) (hσω : σ ω = ω) {a : F}
    (ha : a ^ 3 = 1) : σ a = a := by
  obtain ⟨i, -, rfl⟩ := hω.eq_pow_of_pow_eq_one ha
  rw [map_pow, hσω]

private theorem eig_partner {M : Matrix (Fin d) (Fin d) F} (hM : conjTr σ M * M = 1)
    {u w : Fin d → F} {a b : F} (hu : M *ᵥ u = a • u) (hw : M *ᵥ w = b • w)
    (huw : herm σ u w = 1) (ha : σ a = a) : b = a⁻¹ := by
  have h1 := herm_mulVec (σ := σ) M u w
  rw [hM, Matrix.one_mulVec, hu, hw, herm_smul_left, herm_smul_right, ha, huw] at h1
  exact eq_inv_of_mul_eq_one_right (by simpa using h1)

theorem SG.exists_sl2_data (hσ : IsUnitaryInvolution σ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (hσω : σ ω = ω) (hd : 6 ≤ d) {G : Type} [Group G] [Finite G]
    (hcomm : ∀ g g' : G, g * g' = g' * g) (hg3 : ∀ g : G, g ^ 3 = 1)
    (ρ : G →* Matrix (Fin d) (Fin d) F) (hρ : ∀ g, conjTr σ (ρ g) * ρ g = 1) (g₀ : G) :
    ∃ (x y : Fin 2 → Fin d → F) (z : Fin d → F),
      (∀ i j, herm σ (x i) (x j) = 0) ∧ (∀ i j, herm σ (y i) (y j) = 0) ∧
      (∀ i j, herm σ (x i) (y j) = if i = j then 1 else 0) ∧ z ≠ 0 ∧
      (∀ i, herm σ (x i) z = 0) ∧ (∀ i, herm σ (y i) z = 0) ∧
      ∃ K : Subgroup G, K.index ≤ 3 ∧ g₀ ∈ K ∧ ∀ g ∈ K, ∃ a : F,
        (∀ i, ρ g *ᵥ x i = a • x i) ∧ (∀ i, ρ g *ᵥ y i = a⁻¹ • y i) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin d) (Fin d) F ≃ₐ[F] ((Fin d → F) →ₗ[F] Fin d → F),
      ∀ M x, T M x = M *ᵥ x :=
    ⟨Matrix.toLinAlgEquiv', fun M x => Matrix.toLinAlgEquiv'_apply M x⟩
  obtain ⟨u, w, hp, hω₀⟩ := SG.exists_hypPairs_family (S := fun g => T (ρ g)) (k := 3) hσ hω hσω
    (fun g g' => by
      show T (ρ g) * T (ρ g') = T (ρ g') * T (ρ g)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm g g'])
    (fun g => by rw [← map_pow, ← map_pow, hg3 g, map_one, map_one])
    (fun g x y => by
      simp only [hT]
      rw [herm_mulVec, hρ, Matrix.one_mulVec]) (by omega) g₀
  have heu : ∀ g j, ∃ a : F, ρ g *ᵥ u j = a • u j := fun g j => by
    simpa only [hT] using (hp g).eu j
  have hω₀' : ∀ j, ρ g₀ *ᵥ u j = u j ∨ ρ g₀ *ᵥ u j = ω • u j := fun j => by
    simpa only [hT] using hω₀ j
  have hww : ∀ j, herm σ (u j) (w j) = 1 := fun j => by simpa using (hp g₀).uw j j
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => by
    have h1 := hww j
    rw [h0, herm_zero_left] at h1
    exact zero_ne_one h1
  choose θ hθ using fun j => exists_eigenchar ρ (hu0 j) fun g => heu g j
  have hw : ∀ j g, ρ g *ᵥ w j = (θ j g : F)⁻¹ • w j := fun j g => by
    obtain ⟨b, hb⟩ : ∃ b : F, ρ g *ᵥ w j = b • w j := by simpa only [hT] using (hp g).ew j
    have hc : (θ j g : F) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hg3, map_one, Units.val_one]
    rwa [eig_partner (hρ g) (hθ j g) hb (hww j) (map_eq_self_of_cube hω hσω hc)] at hb
  have hg0 : ∀ j, (θ j g₀ : F) = 1 ∨ (θ j g₀ : F) = ω := fun j => by
    rcases hω₀' j with h1 | h1 <;> rw [hθ j g₀] at h1
    · exact Or.inl (smul_left_injective F (hu0 j) (by simpa using h1))
    · exact Or.inr (smul_left_injective F (hu0 j) h1)
  obtain ⟨k, l, hkl, hfkl⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin 3 => decide ((θ j g₀ : F) = 1)) (by simp)
  simp only [decide_eq_decide] at hfkl
  have hsame : (θ k g₀ : F) = θ l g₀ := by
    rcases hg0 k with h1 | h1 <;> rcases hg0 l with h2 | h2
    · rw [h1, h2]
    · exact ((hω.ne_one (by norm_num)) (h2 ▸ hfkl.1 h1)).elim
    · exact ((hω.ne_one (by norm_num)) (h1 ▸ hfkl.2 h2)).elim
    · rw [h1, h2]
  obtain ⟨m, hmk, hml⟩ : ∃ m : Fin 3, m ≠ k ∧ m ≠ l :=
    (by decide : ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 3, m ≠ k ∧ m ≠ l) k l hkl
  have hinj : ∀ i j : Fin 2, ![k, l] i = ![k, l] j ↔ i = j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hkl, hkl.symm]
  have hne : ∀ i : Fin 2, m ≠ ![k, l] i := by
    intro i
    fin_cases i
    · simpa using hmk
    · simpa using hml
  refine ⟨fun i => u (![k, l] i), fun i => w (![k, l] i), u m, fun i j => (hp g₀).uu _ _,
    fun i j => (hp g₀).ww _ _, fun i j => ?_, hu0 m, fun i => (hp g₀).uu _ _, fun i => ?_,
    (θ k / θ l).ker, ?_, ?_, fun g hg => ?_⟩
  · rw [(hp g₀).uw]
    exact if_congr (hinj i j) rfl rfl
  · rw [herm_conj σ hσ.invol (u m) (w (![k, l] i)), (hp g₀).uw, if_neg (hne i), map_zero]
  · rw [Subgroup.index_ker]
    refine (Subgroup.card_le_of_le (K := rootsOfUnity 3 F) ?_).trans (card_rootsOfUnity F 3)
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow, hg3, map_one]
  · rw [MonoidHom.mem_ker, MonoidHom.div_apply, div_eq_one]
    exact Units.ext hsame
  · rw [MonoidHom.mem_ker, MonoidHom.div_apply, div_eq_one] at hg
    have hθi : ∀ i : Fin 2, θ (![k, l] i) g = θ k g := by
      intro i
      fin_cases i
      · rfl
      · exact hg.symm
    refine ⟨θ k g, fun i => ?_, fun i => ?_⟩
    · show ρ g *ᵥ u (![k, l] i) = _
      rw [hθ, hθi]
    · show ρ g *ᵥ w (![k, l] i) = _
      rw [hw, hθi]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
