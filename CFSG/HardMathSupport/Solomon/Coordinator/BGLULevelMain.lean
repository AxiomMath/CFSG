module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLULevel
public import CFSG.ClassicalGroups.Unitary.Generation
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUFrame

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem exists_decomp_of_perp (hσ : ∀ c, σ (σ c) = c) {a b w : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) (haw : herm σ a w = 0)
    (hbw : herm σ b w = 0) (hw : herm σ w w ≠ 0) {y : Fin 3 → K} (hy : herm σ a y = 0) :
    ∃ α γ : K, y = α • a + γ • w ∧ (γ = 0 ↔ herm σ w y = 0) :=
  ⟨herm σ b y, herm σ w y / herm σ w w, eq_add_of_herm_left_eq_zero hσ ha hb hab haw hbw hw hy,
    by rw [div_eq_zero_iff]; simp [hw]⟩

theorem level_eq_top (hσ' : IsUnitaryInvolution σ) (h3 : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)
    (H : Subgroup (SUid σ 3)) {a b w y₀ : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) (haw : herm σ a w = 0)
    (hbw : herm σ b w = 0) (hw : herm σ w w ≠ 0)
    (hXa : ∀ (c : K) (hc : c + σ c = 0), tv hσ'.invol ha hc ∈ H)
    (hXb : ∀ (c : K) (hc : c + σ c = 0), tv hσ'.invol hb hc ∈ H)
    (𝒯 R : Set K) (h𝒯 : ∀ t ∈ 𝒯, t ≠ 0 ∧ ∃ g ∈ H, g • a = t • a ∧ g • w = w)
    (hy₀ : herm σ a y₀ = 0) (hy₀w : herm σ w y₀ ≠ 0)
    (hR : ∀ μ ∈ R, μ • y₀ ∈ EichSet σ hσ'.invol H ha)
    (hspan : ∀ z : K, z ∈ AddSubgroup.closure {z | ∃ t ∈ 𝒯, ∃ μ ∈ R, z = σ t * μ}) :
    H = ⊤ := by
  have hσ := hσ'.invol
  obtain ⟨ν₀, l, hdec, hl⟩ := exists_decomp_of_perp hσ ha hb hab haw hbw hw hy₀
  have hl0 : l ≠ 0 := fun h => hy₀w (hl.mp h)
  let M : AddSubgroup K :=
    { carrier := {μ | μ • y₀ ∈ EichSet σ hσ H ha}
      zero_mem' := by
        show (0 : K) • y₀ ∈ EichSet σ hσ H ha
        rw [zero_smul, ← zero_smul K a]
        exact EichSet.smul_a_mem hσ hXa 0
      add_mem' := fun {μ μ'} hμ hμ' => by
        show (μ + μ') • y₀ ∈ EichSet σ hσ H ha
        rw [add_smul]
        exact EichSet.add_mem hσ hμ hμ'
      neg_mem' := fun {μ} hμ => by
        show (-μ) • y₀ ∈ EichSet σ hσ H ha
        rw [neg_smul]
        exact EichSet.neg_mem hσ hμ }
  have hMall : ∀ μ : K, μ • y₀ ∈ EichSet σ hσ H ha := by
    have hle : AddSubgroup.closure {z | ∃ t ∈ 𝒯, ∃ μ ∈ R, z = σ t * μ} ≤ M := by
      rw [AddSubgroup.closure_le]
      rintro z ⟨t, ht, μ, hμ, rfl⟩
      obtain ⟨ht0, g, hg, hga, hgw⟩ := h𝒯 t ht
      have h1 := EichSet.conj_mem hσ hg ht0 hga (hR μ hμ)
      have hgy : g • y₀ = (ν₀ * t) • a + l • w := by
        rw [hdec, smul_add, smul_comm g ν₀ a, hga, smul_comm g l w, hgw, smul_smul]
      have h2 : (σ t * μ) • y₀ =
          σ t • g • μ • y₀ + (-(σ t * μ * ν₀ * (t - 1))) • a := by
        rw [smul_comm g μ y₀, hgy, hdec]
        module
      show (σ t * μ) • y₀ ∈ EichSet σ hσ H ha
      rw [h2]
      exact EichSet.add_mem hσ h1 (EichSet.smul_a_mem hσ hXa _)
    exact fun μ => hle (hspan μ)
  have hperp : ∀ y, herm σ a y = 0 → y ∈ EichSet σ hσ H ha := by
    intro y hy
    obtain ⟨α, γ, hydec, -⟩ := exists_decomp_of_perp hσ ha hb hab haw hbw hw hy
    have : y = (α - γ * ν₀ / l) • a + (γ / l) • y₀ := by
      rw [hydec, hdec]
      match_scalars <;> field_simp
      ring
    rw [this]
    exact EichSet.add_mem hσ (EichSet.smul_a_mem hσ hXa _) (hMall _)
  have htv : tvSet σ 3 ⊆ (H : Set (SUid σ 3)) := by
    rintro g ⟨v, c, hv, hc, hgv⟩
    by_cases hav : herm σ a v = 0
    ·
      obtain ⟨α, γ, hvdec, hγ⟩ := exists_decomp_of_perp hσ ha hb hab haw hbw hw hav
      have hγ0 : γ = 0 := by
        have hwa : herm σ w a = 0 := herm_eq_zero_comm σ hσ haw
        have : herm σ v v = σ γ * γ * herm σ w w := by
          rw [hvdec]
          simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, haw, hwa]
          ring
        rw [hv] at this
        rcases mul_eq_zero.mp this.symm with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact (map_eq_zero_iff σ σ.injective).mp h
          · exact h
        · exact absurd h hw
      have hc2 : (c * (σ α * α)) + σ (c * (σ α * α)) = 0 := by
        rw [map_mul, map_mul, hσ]
        linear_combination (σ α * α) * hc
      have : g = tv hσ ha hc2 := by
        apply ext_smul
        intro x
        rw [hgv, tv_smul, hvdec, hγ0, zero_smul, add_zero]
        simp only [herm_smul_left, smul_smul]
        match_scalars <;> ring
      show g ∈ H
      rw [this]
      exact hXa _ hc2
    · set l₁ := herm σ a v with hl₁
      have hl₁0 : l₁ ≠ 0 := hav
      set v' := l₁⁻¹ • v with hv'
      have hv'v' : herm σ v' v' = 0 := by
        rw [hv', herm_smul_left, herm_smul_right, hv, mul_zero, mul_zero]
      have hav' : herm σ a v' = 1 := by
        rw [hv', herm_smul_right, ← hl₁, inv_mul_cancel₀ hl₁0]
      have hc1 : (c * (σ l₁ * l₁)) + σ (c * (σ l₁ * l₁)) = 0 := by
        rw [map_mul, map_mul, hσ, mul_comm l₁ (σ l₁)]
        linear_combination (σ l₁ * l₁) * hc
      have hy : herm σ a (v' - b) = 0 := by rw [herm_sub_right, hav', hab, sub_self]
      have hcu : herm σ v' b + σ (herm σ v' b) = -herm σ (v' - b) (v' - b) := by
        have e : σ (herm σ v' b) = herm σ b v' := (herm_conj σ hσ v' b).symm
        rw [e, herm_sub_left, herm_sub_right, herm_sub_right, hv'v', hb]
        ring
      have hu : eichler hσ ha hy hcu ∈ H :=
        EichSet.mem_all hσ hXa (hperp _ hy) hy _ hcu
      have hub : eichler hσ ha hy hcu • b = v' := by
        rw [eichler_smul, hab, herm_sub_left, hb]
        module
      have hteq : g = eichler hσ ha hy hcu * tv hσ hb hc1 * (eichler hσ ha hy hcu)⁻¹ := by
        apply ext_smul
        intro x
        rw [conj_smul_of_tv _ _ (fun u => tv_smul hσ hb hc1 u), hub, hgv, hv']
        simp only [herm_smul_left, smul_smul, map_inv₀]
        have hs : σ l₁ ≠ 0 := (map_ne_zero σ).mpr hl₁0
        match_scalars <;> field_simp
      show g ∈ H
      rw [hteq]
      exact H.mul_mem (H.mul_mem hu (hXb _ hc1)) (H.inv_mem hu)
  have hT : T σ 3 ≤ H := by
    rw [T, Subgroup.closure_le]
    exact htv
  rw [eq_top_iff]
  intro g _
  have := T_eq_top hσ' (n := 3) (by norm_num) (fun _ => h3)
  exact hT (this ▸ Subgroup.mem_top g)

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
