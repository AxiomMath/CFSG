module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEQ2
public import CFSG.ClassicalInvolution.Q3.Sec13RecogLabel
import CFSG.ClassicalInvolution.Q3.Sec13RecogQ8
import CFSG.ClassicalInvolution.Q3.TL4D1ML32D
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32B
import CFSG.ClassicalInvolution.Q3.AE.FanoPack

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

section DeqiEFano

open CFSG.ClassicalInvolution.Q3.AE

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def deqi_E_inL32 (g : Equiv.Perm (Fin 7)) : Bool :=
  fanoLines.all fun s => decide (s.map g.toEmbedding ∈ fanoLines) &&
    decide (s.map g⁻¹.toEmbedding ∈ fanoLines)

theorem deqi_E_inL32_iff (g : Equiv.Perm (Fin 7)) : deqi_E_inL32 g = true ↔ g ∈ l32 := by
  simp only [deqi_E_inL32, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, l32,
    stabFamily]
  rfl

@[expose] def deqi_E_PS (i₀ : Fin 7) (ℓ : Finset (Fin 7)) : Finset (Equiv.Perm (Fin 7)) :=
  Finset.univ.filter fun g => decide (g i₀ = i₀) && decide (∀ p ∈ ℓ, g p = p) && deqi_E_inL32 g

theorem deqi_E_PS_card : ∀ i₀ : Fin 7, ∀ ℓ ∈ fanoLines, i₀ ∈ ℓ → (deqi_E_PS i₀ ℓ).card = 4 := by
  intro i₀ ℓ hℓ hi
  exact FanoPack.card_PS i₀ ℓ hℓ hi _ fun g => by
    simp only [deqi_E_PS, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq, deqi_E_inL32_iff, FanoPack.psP, and_assoc]

theorem deqi_E_two_points : ∀ ℓ ∈ fanoLines, ∃ a ∈ ℓ, ∃ b ∈ ℓ, a ≠ b := by
  decide +kernel

@[expose] def deqi_E_blockPres (i₀ : Fin 7) (T : Equiv.Perm (Fin 7)) : Prop :=
  ∀ ℓ ∈ fanoLines, i₀ ∈ ℓ → ∀ p ∈ ℓ, T p ∈ ℓ

instance deqi_E_blockPres_dec (i₀ : Fin 7) (T : Equiv.Perm (Fin 7)) :
    Decidable (deqi_E_blockPres i₀ T) := by
  unfold deqi_E_blockPres; infer_instance

set_option maxRecDepth 100000 in
theorem deqi_E_key : ∀ i₀ : Fin 7, ∀ ℓ ∈ fanoLines, i₀ ∈ ℓ →
    ∀ c : Equiv.Perm (Fin 7), c i₀ = i₀ → c * c * c = 1 → c ≠ 1 → deqi_E_inL32 c = true →
    ∃ A ∈ deqi_E_PS i₀ ℓ, ∃ T ∈ deqi_E_PS i₀ ℓ, deqi_E_blockPres i₀ T ∧ T ≠ 1 ∧ A ≠ 1 ∧
      A ≠ T ∧ A * A = 1 ∧ T * T = 1 ∧ A * T ∈ deqi_E_PS i₀ ℓ ∧ A * c * A * c = 1 ∧
      (c * T * c⁻¹) * A * (c * T * c⁻¹) = A * T := by
  intro i₀ ℓ hℓ hi c h1 h2 h3 h4
  have memPS : ∀ g, g ∈ deqi_E_PS i₀ ℓ ↔ FanoPack.psP i₀ ℓ g := fun g => by
    simp only [deqi_E_PS, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq, deqi_E_inL32_iff, FanoPack.psP, and_assoc]
  obtain ⟨A, hA, T, hT, hb, h5, h6, h7, h8, h9, hAT, h10, h11⟩ :=
    FanoPack.key_PS i₀ ℓ hℓ hi c h1 h2 h3 ((deqi_E_inL32_iff c).1 h4)
  exact ⟨A, (memPS A).2 hA, T, (memPS T).2 hT, hb, h5, h6, h7, h8, h9, (memPS _).2 hAT, h10, h11⟩

set_option maxRecDepth 100000 in
theorem deqi_E_moves : ∀ i₀ : Fin 7, ∀ ℓ ∈ fanoLines, i₀ ∈ ℓ →
    ∀ c : Equiv.Perm (Fin 7), c i₀ = i₀ → c * c * c = 1 → c ≠ 1 → deqi_E_inL32 c = true →
    ℓ.map c.toEmbedding ≠ ℓ := by
  intro i₀ ℓ hℓ hi c h1 h2 h3 h4
  exact FanoPack.moves_PS i₀ ℓ hℓ hi c h1 h2 h3 ((deqi_E_inL32_iff c).1 h4)

open CFSG.ClassicalInvolution.Q3.AE

set_option maxRecDepth 100000 in
theorem deqi_E_PS_sq : ∀ i₀ : Fin 7, ∀ ℓ ∈ fanoLines, i₀ ∈ ℓ →
    ∀ g ∈ deqi_E_PS i₀ ℓ, g * g = 1 := by
  intro i₀ ℓ hℓ hi g hg
  refine FanoPack.sq_PS i₀ ℓ hℓ hi g ?_
  simpa only [deqi_E_PS, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
    decide_eq_true_eq, deqi_E_inL32_iff, FanoPack.psP, and_assoc] using hg

end DeqiEFano

private theorem deqi_A_braid {Γ : Type*} [Group Γ] {a b : Γ} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : a * b * a = b * a * b := by
  have ea : ∀ x : Γ, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have eb : ∀ x : Γ, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  have hcube : a * b * a * b * a * b = 1 := by
    rw [← h]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hxy : (a * b * a) * (b * a * b) = 1 := by
    simpa only [mul_assoc] using hcube
  have hxx : (a * b * a) * (a * b * a) = 1 := by
    simp only [mul_assoc, ea, eb, ha, hb]
  calc a * b * a = (a * b * a)⁻¹ := (inv_eq_of_mul_eq_one_right hxx).symm
    _ = b * a * b := (eq_inv_of_mul_eq_one_right hxy).symm

theorem coxeterA3_card_le {Γ : Type*} [Group Γ] [Finite Γ] {t₁ t₂ t₃ : Γ} (h₁ : t₁ * t₁ = 1)
    (h₂ : t₂ * t₂ = 1) (h₃ : t₃ * t₃ = 1) (h₁₃ : t₁ * t₃ = t₃ * t₁) (h₁₂ : (t₁ * t₂) ^ 3 = 1)
    (h₂₃ : (t₂ * t₃) ^ 3 = 1) : Nat.card ↥(Subgroup.closure ({t₁, t₂, t₃} : Set Γ)) ≤ 24 := by
  classical
  have e₁ : ∀ x : Γ, t₁ * (t₁ * x) = x := fun x => by rw [← mul_assoc, h₁, one_mul]
  have e₂ : ∀ x : Γ, t₂ * (t₂ * x) = x := fun x => by rw [← mul_assoc, h₂, one_mul]
  have e₃ : ∀ x : Γ, t₃ * (t₃ * x) = x := fun x => by rw [← mul_assoc, h₃, one_mul]
  have hb₁₂ : t₁ * t₂ * t₁ = t₂ * t₁ * t₂ := deqi_A_braid h₁ h₂ h₁₂
  have hb₂₃ : t₂ * t₃ * t₂ = t₃ * t₂ * t₃ := deqi_A_braid h₂ h₃ h₂₃
  have hi₁ : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right h₁
  have hi₂ : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right h₂
  have hi₃ : t₃⁻¹ = t₃ := inv_eq_of_mul_eq_one_right h₃
  have c₁₃ : ∀ a : Γ, t₁ * (t₃ * a) = t₃ * (t₁ * a) := fun a => by
    rw [← mul_assoc t₁ t₃ a, h₁₃, mul_assoc]
  obtain ⟨B, hB⟩ : ∃ B : Finset Γ, B = {1, t₁, t₂, t₁ * t₂, t₂ * t₁, t₁ * t₂ * t₁} :=
    ⟨_, rfl⟩
  have hone : (1 : Γ) ∈ B := by
    rw [hB]
    simp
  have hB₁ : ∀ x ∈ B, t₁ * x ∈ B := by
    intro x hx
    rw [hB] at hx ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with h | h | h | h | h | h <;> rw [h]
    · simp
    · simp [h₁]
    · simp
    · simp [← mul_assoc, h₁]
    · simp [← mul_assoc]
    · simp [← mul_assoc, h₁]
  have k1 : t₂ * (t₁ * t₂) = t₁ * t₂ * t₁ := by
    rw [← mul_assoc, ← hb₁₂]
  have k2 : t₂ * (t₁ * t₂ * t₁) = t₁ * t₂ := by
    calc t₂ * (t₁ * t₂ * t₁) = (t₂ * t₁ * t₂) * t₁ := by simp only [mul_assoc]
      _ = (t₁ * t₂ * t₁) * t₁ := by rw [hb₁₂]
      _ = t₁ * t₂ := by rw [mul_assoc (t₁ * t₂) t₁ t₁, h₁, mul_one]
  have hB₂ : ∀ x ∈ B, t₂ * x ∈ B := by
    intro x hx
    rw [hB] at hx ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with h | h | h | h | h | h <;> rw [h]
    · simp
    · simp
    · simp [h₂]
    · simp [k1]
    · simp [← mul_assoc, h₂]
    · simp [k2]
  obtain ⟨S, hS⟩ : ∃ S : Finset Γ, S = B ∪ B.image (fun a => t₃ * a) ∪
      B.image (fun a => t₂ * t₃ * a) ∪ B.image (fun a => t₁ * t₂ * t₃ * a) := ⟨_, rfl⟩
  have mem₀ : ∀ x ∈ B, x ∈ S := fun x hx => by
    rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have mem₁ : ∀ a ∈ B, t₃ * a ∈ S := fun a ha => by
    rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y => t₃ * y) ha)))
  have mem₂ : ∀ a ∈ B, t₂ * t₃ * a ∈ S := fun a ha => by
    rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun y => t₂ * t₃ * y) ha))
  have mem₃ : ∀ a ∈ B, t₁ * t₂ * t₃ * a ∈ S := fun a ha => by
    rw [hS]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y => t₁ * t₂ * t₃ * y) ha)
  have k3 : ∀ a : Γ, t₂ * (t₁ * t₂ * t₃ * a) = t₁ * t₂ * t₃ * (t₁ * a) := fun a => by
    calc t₂ * (t₁ * t₂ * t₃ * a) = (t₂ * t₁ * t₂) * (t₃ * a) := by simp only [mul_assoc]
      _ = (t₁ * t₂ * t₁) * (t₃ * a) := by rw [hb₁₂]
      _ = (t₁ * t₂) * (t₁ * t₃) * a := by simp only [mul_assoc]
      _ = (t₁ * t₂) * (t₃ * t₁) * a := by rw [h₁₃]
      _ = t₁ * t₂ * t₃ * (t₁ * a) := by simp only [mul_assoc]
  have k4 : ∀ a : Γ, t₃ * (t₂ * t₃ * a) = t₂ * t₃ * (t₂ * a) := fun a => by
    calc t₃ * (t₂ * t₃ * a) = (t₃ * t₂ * t₃) * a := by simp only [mul_assoc]
      _ = (t₂ * t₃ * t₂) * a := by rw [← hb₂₃]
      _ = t₂ * t₃ * (t₂ * a) := by simp only [mul_assoc]
  have k5 : ∀ a : Γ, t₃ * (t₁ * t₂ * t₃ * a) = t₁ * t₂ * t₃ * (t₂ * a) := fun a => by
    calc t₃ * (t₁ * t₂ * t₃ * a) = (t₃ * t₁) * (t₂ * t₃) * a := by simp only [mul_assoc]
      _ = (t₁ * t₃) * (t₂ * t₃) * a := by rw [← h₁₃]
      _ = t₁ * (t₃ * t₂ * t₃) * a := by simp only [mul_assoc]
      _ = t₁ * (t₂ * t₃ * t₂) * a := by rw [← hb₂₃]
      _ = t₁ * t₂ * t₃ * (t₂ * a) := by simp only [mul_assoc]
  have hS₁ : ∀ x ∈ S, t₁ * x ∈ S := by
    intro x hx
    rw [hS] at hx
    simp only [Finset.mem_union, Finset.mem_image] at hx
    rcases hx with ((hx | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact mem₀ _ (hB₁ x hx)
    · rw [c₁₃ a]
      exact mem₁ _ (hB₁ a ha)
    · simpa only [mul_assoc] using mem₃ a ha
    · have h4 : t₁ * (t₁ * t₂ * t₃ * a) = t₂ * t₃ * a := by simp only [mul_assoc, e₁]
      rw [h4]
      exact mem₂ a ha
  have hS₂ : ∀ x ∈ S, t₂ * x ∈ S := by
    intro x hx
    rw [hS] at hx
    simp only [Finset.mem_union, Finset.mem_image] at hx
    rcases hx with ((hx | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact mem₀ _ (hB₂ x hx)
    · simpa only [mul_assoc] using mem₂ a ha
    · have h4 : t₂ * (t₂ * t₃ * a) = t₃ * a := by simp only [mul_assoc, e₂]
      rw [h4]
      exact mem₁ a ha
    · rw [k3 a]
      exact mem₃ _ (hB₁ a ha)
  have hS₃ : ∀ x ∈ S, t₃ * x ∈ S := by
    intro x hx
    rw [hS] at hx
    simp only [Finset.mem_union, Finset.mem_image] at hx
    rcases hx with ((hx | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact mem₁ _ hx
    · rw [e₃]
      exact mem₀ a ha
    · rw [k4 a]
      exact mem₂ _ (hB₂ a ha)
    · rw [k5 a]
      exact mem₃ _ (hB₂ a ha)
  have hsub : ∀ g ∈ Subgroup.closure ({t₁, t₂, t₃} : Set Γ), g ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => exact mem₀ 1 hone
    | mul_left x hx y _ ih =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h <;> rw [h]
      · exact hS₁ y ih
      · exact hS₂ y ih
      · exact hS₃ y ih
    | inv_mul_cancel x hx y _ ih =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h <;> rw [h]
      · rw [hi₁]
        exact hS₁ y ih
      · rw [hi₂]
        exact hS₂ y ih
      · rw [hi₃]
        exact hS₃ y ih
  have hcard : S.card ≤ 24 := by
    have hBc : B.card ≤ 6 := by
      rw [hB]
      exact Finset.card_le_six
    have hI : ∀ f : Γ → Γ, (B.image f).card ≤ 6 := fun f => Finset.card_image_le.trans hBc
    have h1 := Finset.card_union_le (B ∪ B.image (fun a => t₃ * a) ∪
      B.image (fun a => t₂ * t₃ * a)) (B.image (fun a => t₁ * t₂ * t₃ * a))
    have h2 := Finset.card_union_le (B ∪ B.image (fun a => t₃ * a))
      (B.image (fun a => t₂ * t₃ * a))
    have h3 := Finset.card_union_le B (B.image (fun a => t₃ * a))
    have h4 := hI (fun a => t₃ * a)
    have h5 := hI (fun a => t₂ * t₃ * a)
    have h6 := hI (fun a => t₁ * t₂ * t₃ * a)
    rw [hS]
    omega
  have hle : (Subgroup.closure ({t₁, t₂, t₃} : Set Γ) : Set Γ) ⊆ (S : Set Γ) :=
    fun g hg => hsub g hg
  have hncard : (Subgroup.closure ({t₁, t₂, t₃} : Set Γ) : Set Γ).ncard ≤ S.card := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hle
  show Nat.card (Subgroup.closure ({t₁, t₂, t₃} : Set Γ) : Set Γ) ≤ 24
  rw [Nat.card_coe_set_eq]
  omega

theorem exists_wr_hom_of_blocks {X : Type} [Finite X] [MulAction G X] {n : ℕ}
    (σ : G →* Equiv.Perm (Fin n)) (B : X → Fin n) (hB : ∀ (g : G) (x : X), B (g • x) = σ g (B x))
    (hfib : ∀ i : Fin n, Nat.card {x : X // B x = i} = 2) (p : Fin n → X) (hp : ∀ i, B (p i) = i)
    (hfaith : Function.Injective (MulAction.toPermHom G X)) :
    ∃ ψ : G →* AE.Wr n, Function.Injective ψ ∧ (∀ g : G, (ψ g).perm = σ g) ∧
      ∀ (g : G) (i : Fin n), (ψ g).vec i = 0 ↔ g • p ((σ g).symm i) = p i := by
  classical
  have hq' : ∀ i : Fin n, ∃ q : X, ∀ x : X, B x = i → x = p i ∨ x = q := by
    intro i
    obtain ⟨y, hy, hy'⟩ :=
      (Nat.card_eq_two_iff' (⟨p i, hp i⟩ : {x : X // B x = i})).1 (hfib i)
    refine ⟨y.1, fun x hx => ?_⟩
    by_cases hxp : x = p i
    · exact Or.inl hxp
    · exact Or.inr (congrArg Subtype.val (hy' ⟨x, hx⟩ (fun h => hxp (congrArg Subtype.val h))))
  choose q hq using hq'
  have hpair : ∀ (i : Fin n) (a c : X), B a = i → B c = i → a ≠ c → (a = p i ↔ c ≠ p i) := by
    intro i a c ha hc hac
    rcases hq i a ha with h1 | h1 <;> rcases hq i c hc with h2 | h2
    · exact absurd (h1.trans h2.symm) hac
    · exact iff_of_true h1 (fun h => hac (h1.trans h.symm))
    · exact iff_of_false (fun h => hac (h.trans h2.symm)) (fun h => h h2)
    · exact absurd (h1.trans h2.symm) hac
  have aux : ∀ (g : G) (i j : Fin n) (x : X), σ g j = i → B x = j →
      (if g • x = p i then (0 : ZMod 2) else 1) =
        (if g • p j = p i then 0 else 1) + (if x = p j then 0 else 1) := by
    intro g i j x hgj hx
    have ha : B (g • p j) = i := by rw [hB, hp, hgj]
    have hc : B (g • x) = i := by rw [hB, hx, hgj]
    by_cases hxp : x = p j
    · subst hxp
      simp
    · have hac : g • p j ≠ g • x := fun h => hxp (MulAction.injective g h).symm
      have hiff := hpair i (g • p j) (g • x) ha hc hac
      by_cases h1 : g • p j = p i
      · have h2 : g • x ≠ p i := hiff.1 h1
        rw [if_neg h2, if_pos h1, if_neg hxp, zero_add]
      · have h2 : g • x = p i := by
          by_contra h2
          exact h1 (hiff.2 h2)
        rw [if_pos h2, if_neg h1, if_neg hxp]
        decide
  have hi : ∀ (g h : G) (i : Fin n), (σ (g * h)).symm i = (σ h).symm ((σ g).symm i) := by
    intro g h i
    rw [map_mul, Equiv.symm_apply_eq, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  obtain ⟨F, hF⟩ : ∃ F : G → AE.Wr n, ∀ g : G,
      F g = ⟨fun i => if g • p ((σ g).symm i) = p i then 0 else 1, σ g⟩ :=
    ⟨fun g => ⟨fun i => if g • p ((σ g).symm i) = p i then 0 else 1, σ g⟩, fun g => rfl⟩
  have hFperm : ∀ g : G, (F g).perm = σ g := fun g => by rw [hF]
  have hFvec : ∀ (g : G) (i : Fin n),
      (F g).vec i = if g • p ((σ g).symm i) = p i then 0 else 1 := fun g i => by rw [hF]
  have hFmul : ∀ g h : G, F (g * h) = F g * F h := by
    intro g h
    rw [hF, hF, hF]
    refine CFSG.ClassicalInvolution.Q3.AE.Wr.ext (funext fun i => ?_) (map_mul σ g h)
    show (if (g * h) • p ((σ (g * h)).symm i) = p i then (0 : ZMod 2) else 1) =
      (if g • p ((σ g).symm i) = p i then (0 : ZMod 2) else 1) +
        (if h • p ((σ h).symm ((σ g).symm i)) = p ((σ g).symm i) then (0 : ZMod 2) else 1)
    rw [hi, mul_smul]
    exact aux g i ((σ g).symm i) (h • p ((σ h).symm ((σ g).symm i)))
      (Equiv.apply_symm_apply _ _) (by rw [hB, hp, Equiv.apply_symm_apply])
  obtain ⟨ψ, hψ⟩ : ∃ ψ : G →* AE.Wr n, ∀ g : G, ψ g = F g :=
    ⟨MonoidHom.mk' F hFmul, fun g => rfl⟩
  refine ⟨ψ, ?_, fun g => by rw [hψ, hFperm], fun g i => ?_⟩
  ·
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hψ] at hg
    have hσ1 : σ g = 1 := by
      rw [← hFperm g, hg, CFSG.ClassicalInvolution.Q3.AE.Wr.one_perm]
    have hv0 : ∀ i, (F g).vec i = 0 := fun i => by
      simp [hg, CFSG.ClassicalInvolution.Q3.AE.Wr.one_vec]
    have hsym : ∀ i, (σ g).symm i = i := fun i => by
      rw [Equiv.symm_apply_eq, hσ1, Equiv.Perm.one_apply]
    have hfix : ∀ i : Fin n, g • p i = p i := by
      intro i
      have h0 := hv0 i
      rw [hFvec, hsym i] at h0
      by_contra hne
      rw [if_neg hne] at h0
      exact absurd h0 (by decide)
    have hfixX : ∀ (i : Fin n) (x : X), B x = i → g • x = x := by
      intro i x hx
      have hgx : B (g • x) = i := by simp [hB, hx, hσ1]
      rcases hq i (g • x) hgx with h1 | h1 <;> rcases hq i x hx with h2 | h2
      · exact h1.trans h2.symm
      · have hxp : x = p i := MulAction.injective g (h1.trans (hfix i).symm)
        exact h1.trans hxp.symm
      · have hgxp : g • x = p i := by rw [h2, hfix]
        exact hgxp.trans h2.symm
      · exact h1.trans h2.symm
    apply hfaith
    rw [map_one]
    ext x
    rw [MulAction.toPermHom_apply, Equiv.Perm.one_apply]
    exact hfixX (B x) x rfl
  ·
    rw [hψ, hFvec]
    by_cases h : g • p ((σ g).symm i) = p i
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]
      exact ⟨fun h0 => absurd h0 (by decide), fun h' => absurd h' h⟩

private theorem deqi_F_eq_one_or_eq_of_mem_zpowers {z x : G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  have hk : z ^ k = z ^ (k % (orderOf z : ℤ)) := (zpow_mod_orderOf z k).symm
  rw [hord] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk]
    have h0' : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
    rw [h0']
    exact zpow_zero z
  · right
    rw [hk]
    have h1' : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
    rw [h1']
    exact zpow_one z

private theorem deqi_F_central_of_q8 {L : Subgroup G} {z i j : G} (hQ : Q8Data L z i j) :
    ∀ x ∈ L, z * x = x * z := by
  have hzi : Commute z i := by
    show z * i = i * z
    rw [← hQ.sq_i, mul_assoc]
  have hzj : Commute z j := by
    show z * j = j * z
    rw [← hQ.sq_j, mul_assoc]
  intro x hx
  rcases hQ.nf x hx with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · rw [h1]
    simp
  · rw [h1]
  · rw [h1]
    exact hzi.eq
  · rw [h1]
    exact ((Commute.refl z).mul_right hzi).eq
  · rw [h1]
    exact hzj.eq
  · rw [h1]
    exact ((Commute.refl z).mul_right hzj).eq
  · rw [h1]
    exact (hzi.mul_right hzj).eq
  · rw [h1]
    exact ((Commute.refl z).mul_right (hzi.mul_right hzj)).eq

private theorem deqi_F_conjSub_pSpan_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G)
    (H : Subgroup G) :
    conjSub g (pSpan (omegaHyp Ω H)) ≤ pSpan (omegaHyp Ω (conjSub g H)) := by
  show Subgroup.map (MulAut.conj g).toMonoidHom (pSpan (omegaHyp Ω H)) ≤ _
  rw [Subgroup.map_le_iff_le_comap]
  refine pSpan_le fun L hL => ?_
  intro x hx
  rw [Subgroup.mem_comap]
  obtain ⟨hLΩ, u, huH, hu⟩ : L ∈ Ω ∧ ∃ u ∈ H, IsUniqueInvolution L u := hL
  have hconj : conjSub g L ∈ omegaHyp Ω (conjSub g H) :=
    ⟨hΩ g L hLΩ, g * u * g⁻¹, conj_mem_conjSub huH, hu.conj g⟩
  exact le_pSpan hconj (conj_mem_conjSub hx)

theorem deqi_C_exists_embedPerm {n : ℕ} {ι : Fin 4 ↪ Fin n} {τ : Equiv.Perm (Fin n)}
    (hfix : ∀ x, x ∉ Set.range ι → τ x = x) :
    ∃ d : Equiv.Perm (Fin 4), τ = AE.embedPerm ι d ∧ ∀ i, τ (ι i) = ι (d i) := by
  have hmem : ∀ i, ∃ j, ι j = τ (ι i) := by
    intro i
    by_contra hcon
    have hnot : τ (ι i) ∉ Set.range ι := by
      rintro ⟨j, hj⟩
      exact hcon ⟨j, hj⟩
    have h1 : τ (τ (ι i)) = τ (ι i) := hfix _ hnot
    exact hnot ⟨i, (τ.injective h1).symm⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : τ (ι i) = τ (ι j) := by rw [← hf i, ← hf j, hij]
    exact ι.injective (τ.injective h1)
  let d : Equiv.Perm (Fin 4) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hd : ∀ i, τ (ι i) = ι (d i) := fun i => (hf i).symm
  refine ⟨d, Equiv.ext fun x => ?_, hd⟩
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [AE.embedPerm_apply]
    exact hd i
  · rw [AE.embedPerm_of_not_mem ι d hx]
    exact hfix x hx

theorem deqi_C_perm_fin4 : ∀ d : Equiv.Perm (Fin 4), (∀ i, d (d i) = i) → (∀ i, d i ≠ i) →
    d = AE.d₁ ∨ d = AE.d₂ ∨ d = AE.d₃ := by
  decide +kernel

theorem deqi_C_kList_check : ∀ (v : Fin 4 → ZMod 2) (d : Equiv.Perm (Fin 4)),
    (d = 1 ∨ d = AE.d₁ ∨ d = AE.d₂ ∨ d = AE.d₃) → ∑ i, v i = 0 →
    ∃ x ∈ AE.kList, ∃ y ∈ AE.kStarList, x * y = (⟨v, d⟩ : AE.Wr 4) := by
  decide +kernel

theorem deqi_C_wsum_allOnes : AE.Wr.wsum (AE.Wr.allOnes 7) = 1 := by
  decide

theorem deqi_C_mem_sup_of_perm {α : Finset (Fin 7)} (hα : α.card = 4) {a : AE.Wr 7}
    (hv : ∀ x, x ∉ α → a.vec x = 0) (hw : AE.Wr.wsum a = 0)
    (hp : ∃ d : Equiv.Perm (Fin 4), (d = 1 ∨ d = AE.d₁ ∨ d = AE.d₂ ∨ d = AE.d₃) ∧
      a.perm = AE.embedPerm (AE.emb α hα) d) :
    a ∈ AE.memAt α hα true ⊔ AE.memAt α hα false := by
  obtain ⟨d, hd, hpd⟩ := hp
  have hrange : Set.range (AE.emb α hα) = (α : Set (Fin 7)) := AE.range_emb α hα
  obtain ⟨v, hsupp⟩ : ∃ v : Fin 4 → ZMod 2, ∀ x, a.vec x = AE.embedVec (AE.emb α hα) v x := by
    refine ⟨fun i => a.vec (AE.emb α hα i), fun x => ?_⟩
    by_cases hx : x ∈ Set.range (AE.emb α hα)
    · obtain ⟨i, rfl⟩ := hx
      rw [AE.embedVec_apply]
    · rw [AE.embedVec_of_not_mem _ _ hx]
      apply hv
      rw [hrange] at hx
      exact fun hxα => hx (Finset.mem_coe.mpr hxα)
  have hea : AE.embed (AE.emb α hα) ⟨v, d⟩ = a := by
    refine AE.Wr.ext (funext fun x => ?_) ?_
    · rw [AE.embed_vec]
      exact (hsupp x).symm
    · rw [AE.embed_perm]
      exact hpd.symm
  have hsum : ∑ i, v i = 0 := by
    calc ∑ i, v i = ∑ x, AE.embedVec (AE.emb α hα) v x := (AE.sum_embedVec _ v).symm
      _ = ∑ x, a.vec x := Finset.sum_congr rfl fun x _ => (hsupp x).symm
      _ = 0 := hw
  obtain ⟨x, hx, y, hy, hxy⟩ := deqi_C_kList_check v d hd hsum
  have hX : AE.embed (AE.emb α hα) x ∈ AE.memAt α hα true :=
    Subgroup.mem_map_of_mem _ (AE.mem_kQ.mpr hx)
  have hY : AE.embed (AE.emb α hα) y ∈ AE.memAt α hα false :=
    Subgroup.mem_map_of_mem _ (AE.mem_kQStar.mpr hy)
  rw [← hea, ← hxy, map_mul]
  exact Subgroup.mul_mem_sup hX hY

section DeqiG

variable {Ω : Set (Subgroup G)}

private theorem deqi_G_faithful {M : Subgroup G} (hcore : M.normalCore = ⊥) :
    Function.Injective (MulAction.toPermHom G (G ⧸ M)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ (MulAction.toPermHom G (G ⧸ M)).ker := MonoidHom.mem_ker.mpr hg
  rw [← Subgroup.normalCore_eq_ker, hcore, Subgroup.mem_bot] at hmem
  exact hmem

private theorem deqi_G_mul_inv_eq_one :
    ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → b⁻¹ * a = 1 := by
  decide

private theorem deqi_G_ofAdd_one_ne_one : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
  decide

private theorem deqi_G_wsum_eq_zero {K : Type} [Group K] (hK : commutator K = ⊤) (f : K →* AE.Wr 7)
    (g : K) : AE.Wr.wsum (f g) = 0 := by
  let φ : K →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (AE.Wr.wsum (f x))
      map_one' := by simp [AE.wsum_one]
      map_mul' := fun x y => by simp [AE.wsum_mul] }
  have hle : commutator K ≤ φ.ker := by
    unfold commutator
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [hK] at hle
  have hg : g ∈ φ.ker := hle (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hg
  have hg' : Multiplicative.ofAdd (AE.Wr.wsum (f g)) = Multiplicative.ofAdd 0 := hg
  exact Multiplicative.ofAdd.injective hg'

private theorem deqi_G_card_sumZero : Nat.card {v : Fin 7 → ZMod 2 // ∑ i, v i = 0} = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem deqi_G_card_l32 : Nat.card (AE.l32 : Subgroup (Equiv.Perm (Fin 7))) = 168 :=
  (Nat.card_congr TL4.sl3TwoEquivL32.toEquiv).symm.trans TL4.card_sl3Two

private theorem deqi_G_card_le_of_perm {K : Subgroup (AE.Wr 7)} (hK : K ≤ AE.aeSub 7)
    (hA : ∀ x ∈ K, (x : AE.Wr 7).perm ∈ AE.l32) : Nat.card K ≤ 168 * 64 := by
  let f : K →* Equiv.Perm (Fin 7) := (AE.permHom 7).comp K.subtype
  have hf : ∀ x : K, f x = (x : AE.Wr 7).perm := fun x => rfl
  have hrange : f.range ≤ AE.l32 := by
    rintro _ ⟨x, rfl⟩
    rw [hf]
    exact hA _ x.2
  have hsum : ∀ x : f.ker, ∑ i, ((x : K) : AE.Wr 7).vec i = 0 := fun x =>
    (AE.mem_aeSub.mp (hK (x : K).2)).1
  have hkerc : Nat.card f.ker ≤ Nat.card {v : Fin 7 → ZMod 2 // ∑ i, v i = 0} := by
    refine Nat.card_le_card_of_injective
      (fun x : f.ker => (⟨((x : K) : AE.Wr 7).vec, hsum x⟩ :
        {v : Fin 7 → ZMod 2 // ∑ i, v i = 0})) ?_
    intro x y hxy
    have hv : ((x : K) : AE.Wr 7).vec = ((y : K) : AE.Wr 7).vec := congrArg Subtype.val hxy
    have hx1 : f x = 1 := MonoidHom.mem_ker.mp x.2
    have hy1 : f y = 1 := MonoidHom.mem_ker.mp y.2
    rw [hf] at hx1 hy1
    exact Subtype.ext (Subtype.ext (AE.Wr.ext hv (hx1.trans hy1.symm)))
  rw [deqi_G_card_sumZero] at hkerc
  have hq : Nat.card (K ⧸ f.ker) ≤ 168 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact (Subgroup.card_le_of_le hrange).trans (le_of_eq deqi_G_card_l32)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
  exact Nat.mul_le_mul hq hkerc

private theorem deqi_G_card_aeSubOver_le :
    Nat.card (AE.aeSubOver AE.l32 : Subgroup (AE.Wr 7)) ≤ 168 * 64 :=
  deqi_G_card_le_of_perm (fun _ hx => (Subgroup.mem_inf.mp hx).1)
    (fun _ hx => Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).2)

private theorem deqi_G_range_eq_aeSubOver {ψ : G →* AE.Wr 7} {σ : G →* Equiv.Perm (Fin 7)}
    (hperm : ∀ g : G, (ψ g).perm = σ g) (hσ : ∀ g : G, σ g ∈ AE.l32)
    (hinj : Function.Injective ψ) (hcomm : commutator G = ⊤) (hcard : Nat.card G = 168 * 64) :
    ψ.range = AE.aeSubOver AE.l32 := by
  have hle : ψ.range ≤ AE.aeSubOver AE.l32 := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨AE.mem_aeSub.mpr ⟨deqi_G_wsum_eq_zero hcomm ψ g, ?_⟩, ?_⟩
    · rw [hperm g]
      exact TL4.l32_sign _ (hσ g)
    · refine Subgroup.mem_comap.mpr ?_
      show (ψ g).perm ∈ AE.l32
      rw [hperm g]
      exact hσ g
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hψ : Nat.card ψ.range = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hψ, hcard]
  exact deqi_G_card_aeSubOver_le

private theorem deqi_G_conjSub_pSpan_omegaHyp (hΩ : ConjInvariant Ω) {H : Subgroup G} (g : G) :
    conjSub g (pSpan (omegaHyp Ω H)) = pSpan (omegaHyp Ω (conjSub g H)) := by
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr (pSpan_le fun L hL => ?_)
    obtain ⟨hLΩ, u, huH, hu⟩ := hL
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_pSpan ⟨hΩ g L hLΩ, g * u * g⁻¹, conj_mem_conjSub huH, hu.conj g⟩
  · refine pSpan_le fun L' hL' => ?_
    obtain ⟨hL'Ω, u', hu'H, hu'⟩ := hL'
    have hmem : conjSub g⁻¹ L' ∈ omegaHyp Ω H :=
      ⟨hΩ g⁻¹ L' hL'Ω, g⁻¹ * u' * g⁻¹⁻¹, by
        rw [inv_inv]; exact mem_conjSub_iff.mp hu'H, hu'.conj g⁻¹⟩
    rw [← conjSub_conjSub_inv g L']
    exact Subgroup.map_mono (le_pSpan hmem)

private theorem deqi_G_mem_fix_base (hΩ : ConjInvariant Ω) {H₀ H : Subgroup G} {gi : G}
    (hgi : conjSub gi H₀ = H) {g : G} (hg : g ∈ pSpan (omegaHyp Ω H)) :
    g • (QuotientGroup.mk gi : G ⧸ pSpan (omegaHyp Ω H₀)) = QuotientGroup.mk gi := by
  have h1 : g ∈ conjSub gi (pSpan (omegaHyp Ω H₀)) := by
    rw [deqi_G_conjSub_pSpan_omegaHyp hΩ gi, hgi]
    exact hg
  rw [mem_conjSub_iff] at h1
  show (QuotientGroup.mk (g * gi) : G ⧸ pSpan (omegaHyp Ω H₀)) = QuotientGroup.mk gi
  refine Eq.symm ?_
  rw [QuotientGroup.eq, ← mul_assoc]
  exact h1

private noncomputable def deqi_G_block (lab : Subgroup G → Fin 7) (H₀ : Subgroup G)
    (hM : pSpan (omegaHyp Ω H₀) ≤ Subgroup.normalizer (H₀ : Set G)) :
    G ⧸ pSpan (omegaHyp Ω H₀) → Fin 7 :=
  Quotient.lift (s := QuotientGroup.leftRel (pSpan (omegaHyp Ω H₀)))
    (fun g => lab (conjSub g H₀)) fun a b hab => by
      have hm : a⁻¹ * b ∈ Subgroup.normalizer (H₀ : Set G) :=
        hM (QuotientGroup.leftRel_apply.mp hab)
      have hconj : conjSub b H₀ = conjSub a H₀ := by
        rw [← mul_inv_cancel_left a b, conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hm]
      show lab (conjSub a H₀) = lab (conjSub b H₀)
      rw [hconj]

private theorem deqi_G_block_smul {lab : Subgroup G → Fin 7} {H₀ : Subgroup G}
    {σ : G →* Equiv.Perm (Fin 7)}
    (hM : pSpan (omegaHyp Ω H₀) ≤ Subgroup.normalizer (H₀ : Set G))
    (hlabConj : ∀ (g : G) (H : Subgroup G), IsHyp Ω H → lab (conjSub g H) = σ g (lab H))
    (hconj : ∀ a : G, IsHyp Ω (conjSub a H₀)) (g : G) (x : G ⧸ pSpan (omegaHyp Ω H₀)) :
    deqi_G_block lab H₀ hM (g • x) = σ g (deqi_G_block lab H₀ hM x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  show lab (conjSub (g * a) H₀) = σ g (lab (conjSub a H₀))
  rw [conjSub_mul]
  exact hlabConj g _ (hconj a)

private theorem deqi_G_fibre_card {lab : Subgroup G → Fin 7} {H₀ : Subgroup G}
    (hM : pSpan (omegaHyp Ω H₀) ≤ Subgroup.normalizer (H₀ : Set G))
    (hlab : ∀ H H' : Subgroup G, IsHyp Ω H → IsHyp Ω H' → lab H = lab H' → H = H')
    (hconj : ∀ a : G, IsHyp Ω (conjSub a H₀))
    {χ : Subgroup.normalizer (H₀ : Set G) →* Multiplicative (ZMod 2)}
    (hker : χ.ker = (pSpan (omegaHyp Ω H₀)).subgroupOf (Subgroup.normalizer (H₀ : Set G)))
    {s : Subgroup.normalizer (H₀ : Set G)} (hχs : χ s ≠ 1)
    {gi : G} {Hi : Subgroup G} (hgi : conjSub gi H₀ = Hi) (hHi : IsHyp Ω Hi) (i : Fin 7)
    (hi : lab Hi = i) :
    Nat.card {x : G ⧸ pSpan (omegaHyp Ω H₀) // deqi_G_block lab H₀ hM x = i} = 2 := by
  have hmem : ∀ x : Subgroup.normalizer (H₀ : Set G),
      χ x = 1 ↔ (x : G) ∈ pSpan (omegaHyp Ω H₀) := by
    intro x
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hsM : (s : G) ∉ pSpan (omegaHyp Ω H₀) := fun h' => hχs ((hmem s).mpr h')
  have hblock : ∀ g : G,
      deqi_G_block lab H₀ hM (QuotientGroup.mk g) = i ↔ conjSub g H₀ = Hi := by
    intro g
    show lab (conjSub g H₀) = i ↔ conjSub g H₀ = Hi
    constructor
    · intro hg
      exact hlab _ _ (hconj g) hHi (hg.trans hi.symm)
    · intro hg
      rw [hg, hi]
  have hNgi : ∀ g : G, conjSub g H₀ = Hi → gi⁻¹ * g ∈ Subgroup.normalizer (H₀ : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hg, ← hgi, conjSub_inv_conjSub]
  have hclass : ∀ g : G, conjSub g H₀ = Hi →
      (QuotientGroup.mk g : G ⧸ pSpan (omegaHyp Ω H₀)) = QuotientGroup.mk gi ∨
        (QuotientGroup.mk g : G ⧸ pSpan (omegaHyp Ω H₀)) = QuotientGroup.mk (gi * s) := by
    intro g hg
    by_cases hnM : gi⁻¹ * g ∈ pSpan (omegaHyp Ω H₀)
    · exact Or.inl (Eq.symm (QuotientGroup.eq.mpr hnM))
    · refine Or.inr (Eq.symm ?_)
      rw [QuotientGroup.eq]
      have hn1 : χ ⟨gi⁻¹ * g, hNgi g hg⟩ ≠ 1 := fun h' => hnM ((hmem _).mp h')
      have hsn : χ (s⁻¹ * ⟨gi⁻¹ * g, hNgi g hg⟩) = 1 := by
        rw [map_mul, map_inv]
        exact deqi_G_mul_inv_eq_one _ _ hn1 hχs
      have hsn' : (s : G)⁻¹ * (gi⁻¹ * g) ∈ pSpan (omegaHyp Ω H₀) := (hmem _).mp hsn
      have e : (gi * s)⁻¹ * g = (s : G)⁻¹ * (gi⁻¹ * g) := by group
      rw [e]
      exact hsn'
  have hB0 : deqi_G_block lab H₀ hM (QuotientGroup.mk gi) = i := (hblock gi).mpr hgi
  have hB1 : deqi_G_block lab H₀ hM (QuotientGroup.mk (gi * s)) = i := by
    refine (hblock (gi * s)).mpr ?_
    rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp s.2, hgi]
  have hne : (QuotientGroup.mk gi : G ⧸ pSpan (omegaHyp Ω H₀)) ≠ QuotientGroup.mk (gi * s) := by
    intro h'
    rw [QuotientGroup.eq, inv_mul_cancel_left] at h'
    exact hsM h'
  rw [Nat.card_eq_two_iff' (⟨QuotientGroup.mk gi, hB0⟩ :
    {x : G ⧸ pSpan (omegaHyp Ω H₀) // deqi_G_block lab H₀ hM x = i})]
  refine ⟨⟨QuotientGroup.mk (gi * s), hB1⟩, fun h' => hne (congrArg Subtype.val h').symm, ?_⟩
  rintro ⟨y, hy⟩ hyne
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y
  have hyg : deqi_G_block lab H₀ hM (QuotientGroup.mk g) = i := by
    rw [hg]
    exact hy
  rcases hclass g ((hblock g).mp hyg) with h1 | h1
  · exact absurd (Subtype.ext (hg.symm.trans h1) :
      (⟨y, hy⟩ : {x : G ⧸ pSpan (omegaHyp Ω H₀) // deqi_G_block lab H₀ hM x = i}) =
        ⟨QuotientGroup.mk gi, hB0⟩) hyne
  · exact Subtype.ext (hg.symm.trans h1)

end DeqiG

open scoped Matrix

private theorem deqi_D_eq_one_or_eq_of_mem_zpowers {c x : G} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  have hk : c ^ k = c ^ (k % (orderOf c : ℤ)) := (zpow_mod_orderOf c k).symm
  rw [hord] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk]
    have h0' : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
    rw [h0']
    exact zpow_zero c
  · right
    rw [hk]
    have h1' : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
    rw [h1']
    exact zpow_one c

private theorem deqi_D_mulVec_transv (v μ w : Fin 3 → ZMod 2) :
    (1 + Matrix.vecMulVec v μ) *ᵥ w = w + (μ ⬝ᵥ w) • v := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  simp

private theorem deqi_D_transv_of_cols {v : Fin 3 → ZMod 2} (hv : v ≠ 0)
    {A : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hcol : ∀ j : Fin 3, A *ᵥ Pi.single j 1 = Pi.single j 1 ∨
      A *ᵥ Pi.single j 1 = Pi.single j 1 + v)
    (hAv : A *ᵥ v = v) :
    ∃ μ : Fin 3 → ZMod 2, μ ⬝ᵥ v = 0 ∧ A = 1 + Matrix.vecMulVec v μ := by
  have hμ : ∀ j : Fin 3, ∃ m : ZMod 2, A *ᵥ Pi.single j 1 = Pi.single j 1 + m • v := by
    intro j
    rcases hcol j with h1 | h1
    · exact ⟨0, by rw [h1, zero_smul, add_zero]⟩
    · exact ⟨1, by rw [h1, one_smul]⟩
  choose μ hμ using hμ
  have hA : A = 1 + Matrix.vecMulVec v μ := by
    ext r j
    have h1 := congrFun (hμ j) r
    rw [Matrix.mulVec_single_one] at h1
    simp only [Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply] at h1
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec, Matrix.of_apply,
      Pi.single_apply]
    rw [h1, mul_comm]
  refine ⟨μ, ?_, hA⟩
  have hAv' := hAv
  rw [hA, deqi_D_mulVec_transv] at hAv'
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  have h2 := congrFun hAv' i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
  have h3 : (μ ⬝ᵥ v) * v i = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact h4
  · exact absurd h4 hi

private theorem deqi_D_card_filter : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    (Finset.univ.filter (fun μ : Fin 3 → ZMod 2 => μ ⬝ᵥ v = 0)).card ≤ 4 := by
  decide

private theorem deqi_D_transv_ncard {v : Fin 3 → ZMod 2} (hv : v ≠ 0) :
    Set.ncard {A : Matrix (Fin 3) (Fin 3) (ZMod 2) |
      ∃ μ : Fin 3 → ZMod 2, μ ⬝ᵥ v = 0 ∧ A = 1 + Matrix.vecMulVec v μ} ≤ 4 := by
  have hset : {A : Matrix (Fin 3) (Fin 3) (ZMod 2) |
      ∃ μ : Fin 3 → ZMod 2, μ ⬝ᵥ v = 0 ∧ A = 1 + Matrix.vecMulVec v μ} =
      (fun μ : Fin 3 → ZMod 2 => 1 + Matrix.vecMulVec v μ) ''
        ↑(Finset.univ.filter (fun μ : Fin 3 → ZMod 2 => μ ⬝ᵥ v = 0)) := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨μ, hμ, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨μ, hμ, rfl⟩
  rw [hset]
  refine (Set.ncard_image_le (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact deqi_D_card_filter v hv

private def deqi_D_X1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private def deqi_D_X2 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 0, 0, 1]

private def deqi_D_Ta : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

private def deqi_D_Tb : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

private def deqi_D_L : Fin 6 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![1, deqi_D_X1, deqi_D_X2, deqi_D_X1 * deqi_D_X2, deqi_D_X2 * deqi_D_X1,
    deqi_D_X1 * deqi_D_X2 * deqi_D_X1]

private def deqi_D_E : Fin 4 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![1, deqi_D_Ta, deqi_D_Tb, deqi_D_Ta * deqi_D_Tb]

private theorem deqi_D_inj :
    Function.Injective (fun p : Fin 6 × Fin 4 => deqi_D_L p.1 * deqi_D_E p.2) := by
  decide

def deqi_E_E (i₀ : Fin 7) : Subgroup (Multiplicative (Fin 7 → ZMod 2)) where
  carrier := {f | f.toAdd i₀ = 0 ∧ ∑ x, f.toAdd x = 0}
  mul_mem' := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    refine ⟨?_, ?_⟩
    · simp [toAdd_mul, ha0, hb0]
    · simp [toAdd_mul, Finset.sum_add_distrib, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha0, ha⟩
    refine ⟨?_, ?_⟩
    · simp [toAdd_inv, ha0]
    · simp [toAdd_inv, Finset.sum_neg_distrib, ha]

def deqi_E_pi : Multiplicative (Fin 7 → ZMod 2) := Multiplicative.ofAdd fun _ => 1

def deqi_E_theta (i₀ : Fin 7) (f : Multiplicative (Fin 7 → ZMod 2)) : ZMod 2 :=
  ∑ x ∈ Finset.univ.erase i₀, f.toAdd x

theorem deqi_E_card_all : ∀ i₀ : Fin 7,
    (Finset.univ.filter fun f : Multiplicative (Fin 7 → ZMod 2) =>
      f.toAdd i₀ = 0 ∧ ∑ x, f.toAdd x = 0).card = 32 := by
  decide +kernel

theorem deqi_E_sum_erase_comp (i₀ : Fin 7) (τ : Equiv.Perm (Fin 7)) (hτ : τ i₀ = i₀)
    (g : Fin 7 → ZMod 2) :
    ∑ x ∈ Finset.univ.erase i₀, g (τ x) = ∑ x ∈ Finset.univ.erase i₀, g x := by
  have h1 : ∑ x, g (τ x) = ∑ x, g x := Equiv.sum_comp τ g
  have h2 := Finset.sum_erase_add Finset.univ (fun x => g (τ x)) (Finset.mem_univ i₀)
  have h3 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i₀)
  rw [hτ] at h2
  have h4 : ∑ x ∈ Finset.univ.erase i₀, g (τ x) + g i₀ =
      ∑ x ∈ Finset.univ.erase i₀, g x + g i₀ := by rw [h2, h3, h1]
  exact add_right_cancel h4

theorem deqi_E_theta_eq_zero_of_norm (i₀ : Fin 7) (τ : Equiv.Perm (Fin 7)) (hτ : τ i₀ = i₀)
    (f : Multiplicative (Fin 7 → ZMod 2)) (c : ZMod 2)
    (hc : ∀ x, f.toAdd x + f.toAdd (τ x) + f.toAdd (τ (τ x)) = c) :
    deqi_E_theta i₀ f = 0 := by
  have hττ : (τ * τ) i₀ = i₀ := by simp [hτ]
  have hsum : ∑ x ∈ Finset.univ.erase i₀, (f.toAdd x + f.toAdd (τ x) + f.toAdd (τ (τ x))) =
      ∑ x ∈ Finset.univ.erase i₀, c := Finset.sum_congr rfl fun x _ => hc x
  have hA : ∑ x ∈ Finset.univ.erase i₀, f.toAdd (τ (τ x)) = deqi_E_theta i₀ f := by
    have := deqi_E_sum_erase_comp i₀ (τ * τ) hττ (fun x => f.toAdd x)
    simpa [deqi_E_theta, mul_apply] using this
  have hB : ∑ x ∈ Finset.univ.erase i₀, f.toAdd (τ x) = deqi_E_theta i₀ f :=
    deqi_E_sum_erase_comp i₀ τ hτ (fun x => f.toAdd x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB] at hsum
  have h6 : ∑ x ∈ Finset.univ.erase i₀, c = 0 := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Fintype.card_fin, show (7 - 1 : ℕ) = 6 from rfl]
    have h6' : ∀ a : ZMod 2, (6 : ℕ) • a = 0 := by decide
    exact h6' c
  rw [h6] at hsum
  have key : ∀ a : ZMod 2, a + a + a = 0 → a = 0 := by decide
  exact key _ hsum

theorem deqi_E_pi_toAdd (x : Fin 7) : deqi_E_pi.toAdd x = 1 := by simp [deqi_E_pi]

theorem deqi_E_mul_pi_toAdd (f : Multiplicative (Fin 7 → ZMod 2)) (x : Fin 7) :
    (f * deqi_E_pi).toAdd x = f.toAdd x + 1 := by
  rw [toAdd_mul, Pi.add_apply, deqi_E_pi_toAdd]

theorem deqi_E_mem_iff (i₀ : Fin 7) (f : Multiplicative (Fin 7 → ZMod 2)) :
    (f ∈ deqi_E_E i₀ ∨ f * deqi_E_pi ∈ deqi_E_E i₀) ↔ deqi_E_theta i₀ f = 0 := by
  have hsplit : ∑ x, f.toAdd x = deqi_E_theta i₀ f + f.toAdd i₀ := by
    unfold deqi_E_theta
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
  have hpi : ∑ x, (f * deqi_E_pi).toAdd x = ∑ x, f.toAdd x + 1 := by
    simp only [deqi_E_mul_pi_toAdd, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hE1 : f ∈ deqi_E_E i₀ ↔ f.toAdd i₀ = 0 ∧ ∑ x, f.toAdd x = 0 := Iff.rfl
  have hE2 : f * deqi_E_pi ∈ deqi_E_E i₀ ↔
      f.toAdd i₀ + 1 = 0 ∧ ∑ x, f.toAdd x + 1 = 0 := by
    change (f * deqi_E_pi).toAdd i₀ = 0 ∧ ∑ x, (f * deqi_E_pi).toAdd x = 0 ↔ _
    rw [hpi, deqi_E_mul_pi_toAdd]
  rw [hE1, hE2, hsplit]
  have key : ∀ a t : ZMod 2, ((a = 0 ∧ t + a = 0) ∨ (a + 1 = 0 ∧ t + a + 1 = 0)) ↔ t = 0 := by
    decide
  exact key _ _

theorem deqi_E_theta_indicator (i₀ : Fin 7) (A : Finset (Fin 7)) (hA : A.card = 4) :
    deqi_E_theta i₀ (Multiplicative.ofAdd fun x => if x ∈ A then 1 else 0) = 0 ↔ i₀ ∉ A := by
  have hfilt : (Finset.univ.erase i₀).filter (· ∈ A) = A.erase i₀ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  have hsum : deqi_E_theta i₀ (Multiplicative.ofAdd fun x => if x ∈ A then 1 else 0) =
      ((A.erase i₀).card : ZMod 2) := by
    unfold deqi_E_theta
    simp only [toAdd_ofAdd]
    rw [Finset.sum_boole, hfilt]
  rw [hsum]
  by_cases hi : i₀ ∈ A
  · rw [Finset.card_erase_of_mem hi, hA]
    simp only [hi, not_true_eq_false, iff_false]
    decide
  · rw [Finset.erase_eq_of_notMem hi, hA]
    simp only [hi, not_false_eq_true, iff_true]
    decide

theorem deqi_E_coxeter_data {Γ : Type*} [Group Γ] [Finite Γ] {a b c : Γ}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (hc : c * c * c = 1)
    (hcac : a * c * a = c⁻¹) (hn : (c * (a * b) * c⁻¹) * a * (c * (a * b) * c⁻¹)⁻¹ = b) :
    Nat.card ↥(Subgroup.closure ({a, c * a * c⁻¹, b} : Set Γ)) ≤ 24 := by
  have hc3 : c ^ 3 = 1 := by rw [pow_succ, pow_two]; exact hc
  have hcinv3 : c⁻¹ ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  have h₂ : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
    calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [ha]; group
  have hat : a * (c * a * c⁻¹) = c⁻¹ * c⁻¹ := by
    calc a * (c * a * c⁻¹) = (a * c * a) * c⁻¹ := by group
      _ = c⁻¹ * c⁻¹ := by rw [hcac]
  have h₁₂ : (a * (c * a * c⁻¹)) ^ 3 = 1 := by
    rw [hat, (Commute.refl c⁻¹).mul_pow 3, hcinv3, one_mul]
  have ht₂inv : (c * a * c⁻¹)⁻¹ = c * a * c⁻¹ := inv_eq_of_mul_eq_one_right h₂
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haba : a * b * a = b := by
    calc a * b * a = b * a * a := by rw [hab]
      _ = b := by rw [mul_assoc, ha, mul_one]
  have hnt : Commute (c * (a * b) * c⁻¹) (c * a * c⁻¹) := by
    show (c * (a * b) * c⁻¹) * (c * a * c⁻¹) = (c * a * c⁻¹) * (c * (a * b) * c⁻¹)
    calc (c * (a * b) * c⁻¹) * (c * a * c⁻¹) = c * (a * b * a) * c⁻¹ := by group
      _ = c * b * c⁻¹ := by rw [haba]
      _ = c * (a * (a * b)) * c⁻¹ := by rw [← mul_assoc a a b, ha, one_mul]
      _ = (c * a * c⁻¹) * (c * (a * b) * c⁻¹) := by group
  have hbt : b * (c * a * c⁻¹) =
      (c * (a * b) * c⁻¹) * (a * (c * a * c⁻¹)) * (c * (a * b) * c⁻¹)⁻¹ := by
    calc b * (c * a * c⁻¹) = ((c * (a * b) * c⁻¹) * a * (c * (a * b) * c⁻¹)⁻¹) *
          (c * a * c⁻¹) := by rw [hn]
      _ = (c * (a * b) * c⁻¹) * (a * ((c * (a * b) * c⁻¹)⁻¹ * (c * a * c⁻¹))) := by group
      _ = (c * (a * b) * c⁻¹) * (a * ((c * a * c⁻¹) * (c * (a * b) * c⁻¹)⁻¹)) := by
          rw [hnt.inv_left.eq]
      _ = _ := by group
  have h₂₃ : (c * a * c⁻¹ * b) ^ 3 = 1 := by
    have hbt3 : (b * (c * a * c⁻¹)) ^ 3 = 1 := by
      rw [hbt, conj_pow, h₁₂, mul_one, mul_inv_cancel]
    have htb : (c * a * c⁻¹) * b = (b * (c * a * c⁻¹))⁻¹ := by
      rw [mul_inv_rev, ht₂inv, hbinv]
    rw [htb, inv_pow, hbt3, inv_one]
  exact coxeterA3_card_le ha h₂ hb hab h₁₂ h₂₃

namespace DE2Hyp

variable {Ω : Set (Subgroup G)} (h : DE2Hyp Ω)
include h

theorem deqi_conjSub_pSpan_omegaHyp {H : Subgroup G} (g : G) :
    conjSub g (pSpan (omegaHyp Ω H)) = pSpan (omegaHyp Ω (conjSub g H)) := by
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr (pSpan_le fun L hL => ?_)
    obtain ⟨hLΩ, u, huH, hu⟩ := hL
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_pSpan ⟨h.hyp.conjInvariant g L hLΩ, g * u * g⁻¹, conj_mem_conjSub huH, hu.conj g⟩
  · refine pSpan_le fun L' hL' => ?_
    obtain ⟨hL'Ω, u', hu'H, hu'⟩ := hL'
    have hmem : conjSub g⁻¹ L' ∈ omegaHyp Ω H :=
      ⟨h.hyp.conjInvariant g⁻¹ L' hL'Ω, g⁻¹ * u' * g⁻¹⁻¹, by
        rw [inv_inv]; exact mem_conjSub_iff.mp hu'H, hu'.conj g⁻¹⟩
    rw [← conjSub_conjSub_inv g L']
    exact Subgroup.map_mono (le_pSpan hmem)

theorem pSpan_omegaHyp_le_normalizer {H : Subgroup G} (hH : IsHyp Ω H) :
    pSpan (omegaHyp Ω H) ≤ Subgroup.normalizer (H : Set G) := by
  refine pSpan_le fun L hL => ?_
  obtain ⟨hLΩ, u, huH, hu⟩ := hL
  exact h.toDEHyp.le_normalizer_hyp_of_mem hLΩ hu hH huH

theorem card_normalizer_hyp {H : Subgroup G} (hH : IsHyp Ω H) :
    Nat.card ↥(Subgroup.normalizer (H : Set G)) * 7 = Nat.card G := by
  have hidx : (Subgroup.normalizer (H : Set G)).index = 7 := by
    have hcard : Nat.card (G ⧸ Subgroup.normalizer (H : Set G)) =
        Nat.card {H' : Subgroup G // IsHyp Ω H'} := by
      refine Nat.card_eq_of_bijective
        (Quotient.lift (s := QuotientGroup.leftRel (Subgroup.normalizer (H : Set G)))
          (fun g : G => (⟨conjSub g H, h.isHyp_conjSub hH g⟩ :
            {H' : Subgroup G // IsHyp Ω H'}))
          ?_) ⟨?_, ?_⟩
      · intro a b hab
        have hn : a⁻¹ * b ∈ Subgroup.normalizer (H : Set G) :=
          QuotientGroup.leftRel_apply.mp hab
        have h1 : conjSub (a⁻¹ * b) H = H := mem_normalizer_iff_conjSub_eq.mp hn
        apply Subtype.ext
        show conjSub a H = conjSub b H
        calc conjSub a H = conjSub a (conjSub (a⁻¹ * b) H) := by rw [h1]
          _ = conjSub b H := by rw [← conjSub_mul, mul_inv_cancel_left]
      · intro x y hxy
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        have hab : conjSub a H = conjSub b H := congrArg Subtype.val hxy
        rw [QuotientGroup.eq]
        have h1 : conjSub a⁻¹ (conjSub b H) = H := by
          rw [← hab, conjSub_inv_conjSub]
        rw [← conjSub_mul] at h1
        exact mem_normalizer_iff_conjSub_eq.mpr h1
      · rintro ⟨H', hH'⟩
        obtain ⟨g, hg⟩ := h.exists_conj_hyp hH hH'
        exact ⟨(g : G ⧸ Subgroup.normalizer (H : Set G)), Subtype.ext hg⟩
    rw [Subgroup.index, hcard]
    show Nat.card ↥{H' : Subgroup G | IsHyp Ω H'} = 7
    rw [Nat.card_coe_set_eq, h.card_isHyp]
  rw [← hidx, Subgroup.card_mul_index]

private theorem deqi_D_exists_member {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) :
    ∃ K ∈ Ω, IsUniqueInvolution K x := by
  rcases h.mem_zGroup_iff.mp hx with h1 | h1
  · exact absurd h1 hx1
  · exact h1

private theorem deqi_D_conjMat_cols {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {K : Subgroup G} (hK : K ∈ Ω) {c : G} (hc : IsUniqueInvolution K c)
    {v : Fin 3 → ZMod 2} (hcv : c = TL4.e8Coord e v) {k : G} (hk : k ∈ K) (j : Fin 3) :
    TL4.conjMat he k *ᵥ Pi.single j 1 = Pi.single j 1 ∨
      TL4.conjMat he k *ᵥ Pi.single j 1 = Pi.single j 1 + v := by
  have hx : ∀ y ∈ zGroup Ω, k * y * k⁻¹ ∈ zGroup Ω :=
    fun y hy => h.zGroup_normal.conj_mem y hy k
  have hcolj : TL4.conjMat he k *ᵥ Pi.single j 1 = TL4.e8Inv he (k * e j * k⁻¹) := by
    have h1 : TL4.e8Coord e (TL4.conjMat he k *ᵥ Pi.single j 1) = k * e j * k⁻¹ := by
      rw [← TL4.conj_e8Coord he hx (Pi.single j 1), TL4.e8Coord_single]
    rw [← h1, TL4.e8Inv_e8Coord he]
  have hinvj : TL4.e8Inv he (e j) = Pi.single j 1 := by
    rw [← TL4.e8Coord_single (e := e) j]
    exact TL4.e8Inv_e8Coord he _
  have hinvc : TL4.e8Inv he (c * e j) = v + Pi.single j 1 := by
    rw [hcv, ← TL4.e8Coord_single (e := e) j, ← TL4.e8Coord_add he]
    exact TL4.e8Inv_e8Coord he _
  have hdc : dComm (e j) k ∈ Subgroup.zpowers c := h.dComm_mem_zpowers hK hc (he.mem j) hk
  have hkey : k * e j * k⁻¹ = e j ∨ k * e j * k⁻¹ = c * e j := by
    have hinv : (dComm (e j) k)⁻¹ ∈ Subgroup.zpowers c := (Subgroup.zpowers c).inv_mem hdc
    have hx : (dComm (e j) k)⁻¹ = k * e j * k⁻¹ * (e j)⁻¹ := by
      unfold dComm
      group
    rw [hx] at hinv
    rcases deqi_D_eq_one_or_eq_of_mem_zpowers hc.sq hc.ne_one hinv with h1 | h1
    · exact Or.inl (mul_inv_eq_one.mp h1)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h1)
  rcases hkey with h1 | h1
  · left
    rw [hcolj, h1, hinvj]
  · right
    rw [hcolj, h1, hinvc, add_comm]

private theorem deqi_D_conjMat_fix {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {K : Subgroup G} (hK : K ∈ Ω) {c : G} (hc : IsUniqueInvolution K c)
    {v : Fin 3 → ZMod 2} (hcv : c = TL4.e8Coord e v) {k : G} (hk : k ∈ K) :
    TL4.conjMat he k *ᵥ v = v := by
  have hn : conjSub k K = K := mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hk)
  have hkc : k * c * k⁻¹ = c := hc.conj_eq hn
  apply TL4.e8Coord_injective he
  rw [← TL4.conj_e8Coord he (fun y hy => h.zGroup_normal.conj_mem y hy k), ← hcv, hkc]

private theorem deqi_D_conjMat_form {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {K : Subgroup G} (hK : K ∈ Ω) {c : G} (hc : IsUniqueInvolution K c)
    {v : Fin 3 → ZMod 2} (hcv : c = TL4.e8Coord e v) (hv : v ≠ 0) {k : G} (hk : k ∈ K) :
    ∃ μ : Fin 3 → ZMod 2, μ ⬝ᵥ v = 0 ∧ TL4.conjMat he k = 1 + Matrix.vecMulVec v μ :=
  deqi_D_transv_of_cols hv (fun j => deqi_D_conjMat_cols h he hK hc hcv hk j)
    (deqi_D_conjMat_fix h he hK hc hcv hk)

private theorem deqi_D_image_ncard {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {K : Subgroup G} (hK : K ∈ Ω) {c : G} (hc : IsUniqueInvolution K c) :
    Set.ncard {A : Matrix (Fin 3) (Fin 3) (ZMod 2) | ∃ k ∈ K, TL4.conjMat he k = A} = 4 := by
  set f : K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := (h.rhoD he).comp K.subtype
  have hker : f.ker.map K.subtype = K ⊓ Subgroup.centralizer (zGroup Ω : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [← h.rhoD_ker he]
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hy)
    · rintro ⟨hxK, hxc⟩
      have hxk : x ∈ (h.rhoD he).ker := by
        rw [h.rhoD_ker he]
        exact hxc
      exact ⟨⟨x, hxK⟩, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hxk), rfl⟩
  have hker2 : Nat.card f.ker = 2 := by
    have h1 := Subgroup.card_map_of_injective (f := K.subtype) (K := f.ker) Subtype.val_injective
    rw [hker, h.inf_centralizer_zGroup hK hc, card_zpowers_of_involution hc.sq hc.ne_one] at h1
    exact h1.symm
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [hker2] at hsplit
  have hquot : Nat.card (K ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hK8 : Nat.card K = 8 := h.card K hK
  have hrange : Nat.card f.range = 4 := by omega
  let coe : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    fun A => (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hset : {A : Matrix (Fin 3) (Fin 3) (ZMod 2) | ∃ k ∈ K, TL4.conjMat he k = A} =
      coe '' (f.range : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) := by
    ext A
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨h.rhoD he k, MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨⟨k, hk⟩, hkx⟩ := MonoidHom.mem_range.mp hx
      exact ⟨k, hk, by rw [← hkx]; rfl⟩
  have hinj : Function.Injective coe := fun A B hAB => Subtype.ext hAB
  rw [hset, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  exact hrange

private theorem deqi_D_realized {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {K : Subgroup G} (hK : K ∈ Ω) {c : G} (hc : IsUniqueInvolution K c)
    {v : Fin 3 → ZMod 2} (hcv : c = TL4.e8Coord e v) (hv : v ≠ 0)
    (μ : Fin 3 → ZMod 2) (hμ : μ ⬝ᵥ v = 0) :
    ∃ k ∈ K, TL4.conjMat he k = 1 + Matrix.vecMulVec v μ := by
  have hsub : {A : Matrix (Fin 3) (Fin 3) (ZMod 2) | ∃ k ∈ K, TL4.conjMat he k = A} ⊆
      {A : Matrix (Fin 3) (Fin 3) (ZMod 2) |
        ∃ μ' : Fin 3 → ZMod 2, μ' ⬝ᵥ v = 0 ∧ A = 1 + Matrix.vecMulVec v μ'} := by
    rintro A ⟨k, hk, rfl⟩
    exact deqi_D_conjMat_form h he hK hc hcv hv hk
  have hcount := deqi_D_image_ncard h he hK hc
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcount]; exact deqi_D_transv_ncard hv)
  have hmem : (1 + Matrix.vecMulVec v μ) ∈
      {A : Matrix (Fin 3) (Fin 3) (ZMod 2) |
        ∃ μ' : Fin 3 → ZMod 2, μ' ⬝ᵥ v = 0 ∧ A = 1 + Matrix.vecMulVec v μ'} :=
    ⟨μ, hμ, rfl⟩
  rw [← heq] at hmem
  obtain ⟨k, hk, hkA⟩ := hmem
  exact ⟨k, hk, hkA⟩

private theorem deqi_D_adapted_basis {H : Subgroup G} (hH : IsHyp Ω H) :
    ∃ e : Fin 3 → G, TL4.E8Basis (zGroup Ω) e ∧ e 0 ∈ H ∧ e 1 ∈ H := by
  have hHc : Nat.card H = 4 := hH.2
  have hbot : (⊥ : Subgroup G) < H := by
    refine lt_of_le_of_ne bot_le ?_
    intro heq
    rw [← heq, Subgroup.card_bot] at hHc
    norm_num at hHc
  obtain ⟨a, haH, ha1⟩ := SetLike.exists_of_lt hbot
  have ha1' : a ≠ 1 := fun h1 => ha1 (by rw [h1]; exact Subgroup.one_mem _)
  have haD : a ∈ zGroup Ω := hH.1 haH
  have haa : a * a = 1 := h.zGroup_mul_self a haD
  have hza : Nat.card (Subgroup.zpowers a) = 2 := card_zpowers_of_involution haa ha1'
  have hzlt : Subgroup.zpowers a < H := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr haH) ?_
    intro heq
    rw [← heq, hza] at hHc
    norm_num at hHc
  obtain ⟨b, hbH, hb⟩ := SetLike.exists_of_lt hzlt
  have hb1 : b ≠ 1 := fun h1 => hb (by rw [h1]; exact Subgroup.one_mem _)
  have hba : b ≠ a := fun h1 => hb (by rw [h1]; exact Subgroup.mem_zpowers a)
  have hHD : H < zGroup Ω := by
    refine lt_of_le_of_ne hH.1 ?_
    intro heq
    have h8 := h.card_zGroup
    rw [← heq] at h8
    omega
  obtain ⟨d, hdD, hdH⟩ := SetLike.exists_of_lt hHD
  refine ⟨![a, b, d], ⟨fun x hx => h.zGroup_mul_self x hx, h.card_zGroup, ?_, ha1',
    ⟨hb1, hba⟩, ⟨?_, ?_, ?_, ?_⟩⟩, haH, hbH⟩
  · intro k
    fin_cases k
    exacts [haD, hH.1 hbH, hdD]
  · intro h1
    have h1' : d = 1 := h1
    exact hdH (by rw [h1']; exact H.one_mem)
  · intro h1
    have h1' : d = a := h1
    exact hdH (by rw [h1']; exact haH)
  · intro h1
    have h1' : d = b := h1
    exact hdH (by rw [h1']; exact hbH)
  · intro h1
    have h1' : d = a * b := h1
    exact hdH (by rw [h1']; exact H.mul_mem haH hbH)

private theorem deqi_D_card_ge {H : Subgroup G} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) (ha : e 0 ∈ H) (hb : e 1 ∈ H) :
    24 ≤ Nat.card ↥((pSpan (omegaHyp Ω H) ⊔ pCore 2 G).map (h.rhoD he)) := by
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = pSpan (omegaHyp Ω H) ⊔ pCore 2 G := ⟨_, rfl⟩
  rw [← hS]
  have hKS : ∀ {K : Subgroup G}, K ∈ Ω → ∀ {x : G}, x ∈ H → IsUniqueInvolution K x →
      K ≤ S := by
    intro K hK x hxH hKx
    have hmem : K ∈ omegaHyp Ω H :=
      show K ∈ Ω ∧ ∃ u ∈ H, IsUniqueInvolution K u from ⟨hK, x, hxH, hKx⟩
    rw [hS]
    exact (le_pSpan hmem).trans le_sup_left
  obtain ⟨Ka, hKa, hKa'⟩ := deqi_D_exists_member h (he.mem 0) he.ne0
  obtain ⟨Kb, hKb, hKb'⟩ := deqi_D_exists_member h (he.mem 1) he.ne1.1
  have hKaS : Ka ≤ S := hKS hKa ha hKa'
  have hKbS : Kb ≤ S := hKS hKb hb hKb'
  have hA0 : e 0 = TL4.e8Coord e (Pi.single 0 1) := (TL4.e8Coord_single 0).symm
  have hA1 : e 1 = TL4.e8Coord e (Pi.single 1 1) := (TL4.e8Coord_single 1).symm
  have hv0 : (Pi.single 0 1 : Fin 3 → ZMod 2) ≠ 0 := by decide
  have hv1 : (Pi.single 1 1 : Fin 3 → ZMod 2) ≠ 0 := by decide
  obtain ⟨k1, hk1, hk1m⟩ := deqi_D_realized h he hKa hKa' hA0 hv0 (Pi.single 1 1) (by decide)
  obtain ⟨k2, hk2, hk2m⟩ := deqi_D_realized h he hKa hKa' hA0 hv0 (Pi.single 2 1) (by decide)
  obtain ⟨k3, hk3, hk3m⟩ := deqi_D_realized h he hKb hKb' hA1 hv1 (Pi.single 0 1) (by decide)
  obtain ⟨k4, hk4, hk4m⟩ := deqi_D_realized h he hKb hKb' hA1 hv1 (Pi.single 2 1) (by decide)
  obtain ⟨T, hT⟩ : ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)),
      T = S.map (h.rhoD he) := ⟨_, rfl⟩
  rw [← hT]
  have hval : ∀ k : G, ((h.rhoD he k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = TL4.conjMat he k := fun k => rfl
  obtain ⟨x1, hx1, hx1T⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = deqi_D_X1 ∧ x ∈ T :=
    ⟨h.rhoD he k1, by rw [hval, hk1m]; decide,
      by rw [hT]; exact Subgroup.mem_map_of_mem _ (hKaS hk1)⟩
  obtain ⟨x2, hx2, hx2T⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = deqi_D_X2 ∧ x ∈ T :=
    ⟨h.rhoD he k3, by rw [hval, hk3m]; decide,
      by rw [hT]; exact Subgroup.mem_map_of_mem _ (hKbS hk3)⟩
  obtain ⟨ta, hta, htaT⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = deqi_D_Ta ∧ x ∈ T :=
    ⟨h.rhoD he k2, by rw [hval, hk2m]; decide,
      by rw [hT]; exact Subgroup.mem_map_of_mem _ (hKaS hk2)⟩
  obtain ⟨tb, htb, htbT⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = deqi_D_Tb ∧ x ∈ T :=
    ⟨h.rhoD he k4, by rw [hval, hk4m]; decide,
      by rw [hT]; exact Subgroup.mem_map_of_mem _ (hKbS hk4)⟩
  obtain ⟨lw, hlwT, hlw⟩ : ∃ lw : Fin 6 → Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (∀ i, lw i ∈ T) ∧ ∀ i, (lw i : Matrix (Fin 3) (Fin 3) (ZMod 2)) = deqi_D_L i :=
    ⟨![1, x1, x2, x1 * x2, x2 * x1, x1 * x2 * x1], by
      intro i
      fin_cases i <;> simp [mul_mem, one_mem, hx1T, hx2T],
      by
      intro i
      fin_cases i <;> simp [deqi_D_L, Matrix.SpecialLinearGroup.coe_mul, hx1, hx2]⟩
  obtain ⟨ew, hewT, hew⟩ : ∃ ew : Fin 4 → Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (∀ j, ew j ∈ T) ∧ ∀ j, (ew j : Matrix (Fin 3) (Fin 3) (ZMod 2)) = deqi_D_E j :=
    ⟨![1, ta, tb, ta * tb], by
      intro j
      fin_cases j <;> simp [mul_mem, one_mem, htaT, htbT],
      by
      intro j
      fin_cases j <;> simp [deqi_D_E, Matrix.SpecialLinearGroup.coe_mul, hta, htb]⟩
  have hF : Function.Injective (fun p : Fin 6 × Fin 4 =>
      (⟨lw p.1 * ew p.2, mul_mem (hlwT p.1) (hewT p.2)⟩ : ↥T)) := by
    intro p q hpq
    have h1 : lw p.1 * ew p.2 = lw q.1 * ew q.2 := congrArg Subtype.val hpq
    have h2 : deqi_D_L p.1 * deqi_D_E p.2 = deqi_D_L q.1 * deqi_D_E q.2 := by
      have h3 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) =>
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul, hlw, hew] at h3
      exact h3
    exact deqi_D_inj h2
  have hcard := Nat.card_le_card_of_injective _ hF
  simpa using hcard

theorem normalizer_hyp_eq_sup {H : Subgroup G} (hH : IsHyp Ω H) :
    Subgroup.normalizer (H : Set G) = pSpan (omegaHyp Ω H) ⊔ pCore 2 G := by
  have hQc : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G :=
    h.centralizer_zGroup_eq_pCore
  have hQN : pCore 2 G ≤ Subgroup.normalizer (H : Set G) := by
    intro x hx
    rw [← hQc] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have hcomm : n * x = x * n := Subgroup.mem_centralizer_iff.mp hx n (hH.1 hn)
      have hxn : x * n * x⁻¹ = n := by
        rw [← hcomm]
        group
      rw [hxn]
      exact hn
    · intro hn
      have hcomm : x * n * x⁻¹ * x = x * (x * n * x⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hx _ (hH.1 hn)
      have h1 : x * n = x * (x * n * x⁻¹) := by
        rw [← hcomm]
        group
      have hnx : n = x * n * x⁻¹ := mul_left_cancel h1
      rw [hnx]
      exact hn
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = pSpan (omegaHyp Ω H) ⊔ pCore 2 G := ⟨_, rfl⟩
  rw [← hS]
  have hSN : S ≤ Subgroup.normalizer (H : Set G) := by
    rw [hS]
    exact sup_le (h.pSpan_omegaHyp_le_normalizer hH) hQN
  obtain ⟨e, he, ha, hb⟩ := deqi_D_adapted_basis h hH
  have hsurj : Function.Surjective (h.rhoD he) := MonoidHom.range_eq_top.mp (h.rhoD_range he)
  have hkerS : (h.rhoD he).ker ≤ S := by
    rw [h.rhoD_ker he, hQc, hS]
    exact le_sup_right
  have hSeq : (S.map (h.rhoD he)).comap (h.rhoD he) = S := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerS]
  have hTidx : S.index = (S.map (h.rhoD he)).index := by
    have h1 := Subgroup.index_comap_of_surjective (H := S.map (h.rhoD he)) hsurj
    rw [hSeq] at h1
    exact h1
  have hTcard : (S.map (h.rhoD he)).index * Nat.card ↥(S.map (h.rhoD he)) = 168 := by
    rw [Subgroup.index_mul_card, TL4.card_sl3Two]
  have h24 : 24 ≤ Nat.card ↥(S.map (h.rhoD he)) := by
    rw [hS]
    exact deqi_D_card_ge h he ha hb
  have hTi : (S.map (h.rhoD he)).index ≤ 7 := by
    have h1 : (S.map (h.rhoD he)).index * 24 ≤
        (S.map (h.rhoD he)).index * Nat.card ↥(S.map (h.rhoD he)) :=
      Nat.mul_le_mul_left _ h24
    omega
  have hSi : S.index ≤ 7 := by omega
  have hG : Nat.card G = 10752 := by
    have h1 := Subgroup.card_mul_index (Subgroup.centralizer (zGroup Ω : Set G))
    rw [h.index_centralizer_zGroup, hQc, h.card_pCore_eq] at h1
    omega
  have hNc := h.card_normalizer_hyp hH
  have hSc : Nat.card ↥S * S.index = Nat.card G := Subgroup.card_mul_index S
  have hSS : 1536 ≤ Nat.card ↥S := by
    have h1 : Nat.card ↥S * S.index ≤ Nat.card ↥S * 7 := Nat.mul_le_mul_left _ hSi
    omega
  exact (Subgroup.eq_of_le_of_card_ge hSN (by omega)).symm

omit h in
noncomputable def deqi_E_N0 (C : Coords Ω) (H : Subgroup G) : Subgroup G :=
  (deqi_E_E (C.lab H)).map C.β

omit h in
theorem deqi_E_pi_mul_self : deqi_E_pi * deqi_E_pi = 1 := by
  apply Multiplicative.toAdd.injective
  funext x
  simp only [toAdd_mul, Pi.add_apply, deqi_E_pi_toAdd, toAdd_one, Pi.zero_apply]
  decide

omit h in
theorem deqi_E_beta_pi (C : Coords Ω) : C.β deqi_E_pi = 1 :=
  (C.ker_eq deqi_E_pi).mpr (Or.inr rfl)

omit h in
theorem deqi_E_eq_one_or_pi_of_beta (C : Coords Ω) {f : Multiplicative (Fin 7 → ZMod 2)}
    (hf : C.β f = 1) : f = 1 ∨ f = deqi_E_pi := by
  rcases (C.ker_eq f).mp hf with h | h
  · left
    exact Multiplicative.toAdd.injective (by simpa using h)
  · right
    apply Multiplicative.toAdd.injective
    simpa [deqi_E_pi] using h

omit h in
theorem deqi_E_mem_N0_iff (C : Coords Ω) (H : Subgroup G) (f : Multiplicative (Fin 7 → ZMod 2)) :
    C.β f ∈ deqi_E_N0 C H ↔ deqi_E_theta (C.lab H) f = 0 := by
  rw [← deqi_E_mem_iff (C.lab H) f]
  constructor
  · rintro ⟨e, he, hef⟩
    have h1 : C.β (e⁻¹ * f) = 1 := by rw [map_mul, map_inv, ← hef, inv_mul_cancel]
    rcases deqi_E_eq_one_or_pi_of_beta C h1 with h2 | h2
    · left
      have hfe : f = e := (inv_mul_eq_one.mp h2).symm
      rw [hfe]
      exact he
    · right
      have hf : f = e * deqi_E_pi := by rw [← h2, mul_inv_cancel_left]
      rw [hf, mul_assoc, deqi_E_pi_mul_self, mul_one]
      exact he
  · intro h
    rcases h with h | h
    · exact ⟨f, h, rfl⟩
    · refine ⟨f * deqi_E_pi, h, ?_⟩
      rw [map_mul, deqi_E_beta_pi, mul_one]

omit h in
theorem deqi_E_N0_le (C : Coords Ω) (H : Subgroup G) : deqi_E_N0 C H ≤ pCore 2 G := by
  rintro _ ⟨f, -, rfl⟩
  rw [← C.range_eq]
  exact ⟨f, rfl⟩

omit h in
theorem deqi_E_card_E (i₀ : Fin 7) : Nat.card (deqi_E_E i₀) = 32 := by
  have e : Nat.card (deqi_E_E i₀) = Nat.card {f : Multiplicative (Fin 7 → ZMod 2) //
      f.toAdd i₀ = 0 ∧ ∑ x, f.toAdd x = 0} := rfl
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype, deqi_E_card_all i₀]

omit h in
theorem deqi_E_N0_card (C : Coords Ω) (H : Subgroup G) : Nat.card (deqi_E_N0 C H) = 32 := by
  have hinj : Function.Injective ((C.β).comp (deqi_E_E (C.lab H)).subtype) := by
    intro e₁ e₂ he
    have h0 : C.β e₁.1 = C.β e₂.1 := he
    have h' : C.β (e₁.1⁻¹ * e₂.1) = 1 := by
      rw [map_mul, map_inv, h0, inv_mul_cancel]
    apply Subtype.ext
    rcases deqi_E_eq_one_or_pi_of_beta C h' with h2 | h2
    · exact inv_mul_eq_one.mp h2
    · exfalso
      have hmem : e₁.1⁻¹ * e₂.1 ∈ deqi_E_E (C.lab H) :=
        (deqi_E_E _).mul_mem ((deqi_E_E _).inv_mem e₁.2) e₂.2
      rw [h2] at hmem
      exact absurd hmem.1 (by simp [deqi_E_pi_toAdd])
  have hrange : (C.β.comp (deqi_E_E (C.lab H)).subtype).range = deqi_E_N0 C H := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.1, e.2, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact deqi_E_card_E (C.lab H)

omit h in
theorem deqi_E_sigma_fix (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : C.σ g (C.lab H) = C.lab H := by
  have h1 := C.lab_conj g H hH
  rw [mem_normalizer_iff_conjSub_eq.mp hg] at h1
  exact h1.symm

omit h in
theorem deqi_E_conj_mem_N0 (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ deqi_E_N0 C H) :
    n * x * n⁻¹ ∈ deqi_E_N0 C H := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hτ : (C.σ n).symm (C.lab H) = C.lab H := by
    conv_lhs => rw [← deqi_E_sigma_fix C hH hn]
    exact Equiv.symm_apply_apply _ _
  have hs : ∑ x ∈ Finset.univ.erase (C.lab H), f.toAdd ((C.σ n).symm x) =
      ∑ x ∈ Finset.univ.erase (C.lab H), f.toAdd x :=
    deqi_E_sum_erase_comp (C.lab H) _ hτ (fun y => f.toAdd y)
  rw [C.conj_eq n f, deqi_E_mem_N0_iff]
  unfold deqi_E_theta at *
  simp only [toAdd_ofAdd]
  rw [hs]
  exact (deqi_E_mem_iff (C.lab H) f).mp (Or.inl hf)

omit h in
theorem deqi_E_comm_mem_N0 (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) {q n : G}
    (hq : q ∈ pCore 2 G) (hn : n ∈ Subgroup.normalizer (H : Set G)) :
    q * n * q⁻¹ * n⁻¹ ∈ deqi_E_N0 C H := by
  obtain ⟨f, rfl⟩ : q ∈ C.β.range := by rw [C.range_eq]; exact hq
  have hτ : (C.σ n).symm (C.lab H) = C.lab H := by
    conv_lhs => rw [← deqi_E_sigma_fix C hH hn]
    exact Equiv.symm_apply_apply _ _
  have hs : ∑ x ∈ Finset.univ.erase (C.lab H), f.toAdd ((C.σ n).symm x) =
      ∑ x ∈ Finset.univ.erase (C.lab H), f.toAdd x :=
    deqi_E_sum_erase_comp (C.lab H) _ hτ (fun y => f.toAdd y)
  have key : C.β f * n * (C.β f)⁻¹ * n⁻¹ = C.β (f * (Multiplicative.ofAdd fun i =>
      f.toAdd ((C.σ n).symm i))⁻¹) := by
    calc C.β f * n * (C.β f)⁻¹ * n⁻¹ = C.β f * (n * C.β f * n⁻¹)⁻¹ := by group
      _ = C.β f * (C.β (Multiplicative.ofAdd fun i => f.toAdd ((C.σ n).symm i)))⁻¹ := by
          rw [C.conj_eq n f]
      _ = _ := by rw [map_mul, map_inv]
  rw [key, deqi_E_mem_N0_iff]
  unfold deqi_E_theta
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hs]
  simp

omit h in
theorem deqi_E_card_line : ∀ ℓ ∈ AE.fanoLines, ℓ.card = 3 := by
  decide +kernel

omit h in
theorem deqi_E_mem_N0_iff_mem_zGroup (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) {x : G}
    (hx : x ∈ zGroup Ω) : x ∈ deqi_E_N0 C H ↔ x ∈ H := by
  classical
  by_cases hx1 : x = 1
  · subst hx1
    exact ⟨fun _ => H.one_mem, fun _ => (deqi_E_N0 C H).one_mem⟩
  obtain ⟨ℓ, hℓ, hline⟩ := C.line x hx hx1
  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin 7), A = Finset.univ.filter fun i =>
      ∃ H' : Subgroup G, IsHyp Ω H' ∧ C.lab H' = i ∧ x ∉ H' := ⟨_, rfl⟩
  have hAmem : ∀ i, i ∈ A ↔ i ∉ ℓ := by
    intro i
    rw [hA, Finset.mem_filter]
    constructor
    · rintro ⟨-, H', hH', hlab, hxH'⟩ hi
      exact hxH' ((hline H' hH').mpr (hlab ▸ hi))
    · intro hi
      obtain ⟨H', hH', hlab⟩ := C.lab_surj i
      refine ⟨Finset.mem_univ _, H', hH', hlab, fun hxH' => hi ?_⟩
      rw [← hlab]
      exact (hline H' hH').mp hxH'
  have hAeq : A = ℓᶜ := by
    ext i
    rw [hAmem, Finset.mem_compl]
  have hAcard : A.card = 4 := by
    rw [hAeq, Finset.card_compl, deqi_E_card_line ℓ hℓ, Fintype.card_fin]
  have hi0 : C.lab H ∈ A ↔ x ∉ H := by
    rw [hA, Finset.mem_filter]
    constructor
    · rintro ⟨-, H', hH', hlab, hxH'⟩ hxH
      exact hxH' (by rw [C.lab_inj H' H hH' hH hlab]; exact hxH)
    · intro hxH
      exact ⟨Finset.mem_univ _, H, hH, rfl, hxH⟩
  have hfun : (fun i => if i ∈ A then (1 : ZMod 2) else 0) = fun i =>
      if (∃ H' : Subgroup G, IsHyp Ω H' ∧ C.lab H' = i ∧ x ∉ H') then 1 else 0 := by
    funext i
    by_cases hi : ∃ H' : Subgroup G, IsHyp Ω H' ∧ C.lab H' = i ∧ x ∉ H'
    · have hiA : i ∈ A := by rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩
      simp [hiA, hi]
    · have hiA : i ∉ A := by
        rw [hA, Finset.mem_filter]
        exact fun h' => hi h'.2
      simp [hiA, hi]
  have hfx : x = C.β (Multiplicative.ofAdd fun i => if i ∈ A then (1 : ZMod 2) else 0) := by
    rw [hfun]
    exact C.zRel x hx hx1
  have key : C.β (Multiplicative.ofAdd fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈
      deqi_E_N0 C H ↔ x ∈ H := by
    rw [deqi_E_mem_N0_iff, deqi_E_theta_indicator (C.lab H) A hAcard, hi0]
    exact not_not
  rw [← hfx] at key
  exact key

omit h in
theorem deqi_E_card_inf_le_two {H H' : Subgroup G} (hH : IsHyp Ω H) (hH' : IsHyp Ω H')
    (hne : H' ≠ H) : Nat.card ↥(H ⊓ H') ≤ 2 := by
  have hle : H ⊓ H' ≤ H := inf_le_left
  have hdvd : Nat.card ↥(H ⊓ H') ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hle
  rw [hH.2] at hdvd
  have hne4 : Nat.card ↥(H ⊓ H') ≠ 4 := by
    intro h4
    apply hne
    have hHH' : H ⊓ H' = H := Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hH.2])
    have hHle : H ≤ H' := hHH' ▸ inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hHle (by rw [hH'.2, hH.2])).symm
  have hpos : 0 < Nat.card ↥(H ⊓ H') := Nat.card_pos
  have hle4 : Nat.card ↥(H ⊓ H') ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have key : ∀ k < 5, 0 < k → k ≠ 4 → k ∣ 4 → k ≤ 2 := by decide
  exact key _ (by omega) hpos hne4 hdvd

omit h in
theorem deqi_E_exists_outside {H Ha Hb : Subgroup G} (hH : IsHyp Ω H) (hHa : IsHyp Ω Ha)
    (hHb : IsHyp Ω Hb) (hneA : Ha ≠ H) (hneB : Hb ≠ H) :
    ∃ u ∈ H, u ∉ Ha ∧ u ∉ Hb := by
  by_contra hcon
  have hsub : (H : Set G) ⊆ ((H ⊓ Ha : Subgroup G) : Set G) ∪ ((H ⊓ Hb : Subgroup G) : Set G) := by
    intro u hu
    by_contra hn
    apply hcon
    refine ⟨u, hu, fun hua => hn (Or.inl ?_), fun hub => hn (Or.inr ?_)⟩
    · exact ⟨hu, hua⟩
    · exact ⟨hu, hub⟩
  have hA := deqi_E_card_inf_le_two hH hHa hneA
  have hB := deqi_E_card_inf_le_two hH hHb hneB
  have h1 : (H : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hH.2
  have hcov := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hinter := Set.ncard_union_add_ncard_inter ((H ⊓ Ha : Subgroup G) : Set G)
    ((H ⊓ Hb : Subgroup G) : Set G)
  have hA' : ((H ⊓ Ha : Subgroup G) : Set G).ncard ≤ 2 := by
    rw [← Nat.card_coe_set_eq]; exact hA
  have hB' : ((H ⊓ Hb : Subgroup G) : Set G).ncard ≤ 2 := by
    rw [← Nat.card_coe_set_eq]; exact hB
  have hI : 0 < (((H ⊓ Ha : Subgroup G) : Set G) ∩ ((H ⊓ Hb : Subgroup G) : Set G)).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, (H ⊓ Ha).one_mem, (H ⊓ Hb).one_mem⟩
  omega

omit h in
theorem deqi_E_exists_sigma_eq (h : DE2Hyp Ω) (C : Coords Ω) {H Ha Hb : Subgroup G}
    (hH : IsHyp Ω H) (hHa : IsHyp Ω Ha) (hHb : IsHyp Ω Hb) (hneA : Ha ≠ H) (hneB : Hb ≠ H) :
    ∃ m ∈ pSpan (omegaHyp Ω H), C.σ m (C.lab Ha) = C.lab Hb := by
  obtain ⟨u, huH, huA, huB⟩ := deqi_E_exists_outside hH hHa hHb hneA hneB
  have hu1 : u ≠ 1 := fun h1 => huA (h1 ▸ Ha.one_mem)
  obtain ⟨L, hL, hLu⟩ : ∃ L ∈ Ω, IsUniqueInvolution L u := by
    rcases h.mem_zGroup_iff.mp (hH.1 huH) with h1 | h1
    · exact absurd h1 hu1
    · exact h1
  obtain ⟨k, hk, hkconj⟩ := h.exists_conj_hyp_of_not_mem hL hLu hHa hHb huA huB
  have hLM : L ∈ omegaHyp Ω H := ⟨hL, u, huH, hLu⟩
  refine ⟨k, le_pSpan hLM hk, ?_⟩
  rw [← C.lab_conj k Ha hHa, hkconj]

omit h in
theorem deqi_E_pCore_le_normalizer (h : DE2Hyp Ω) {H : Subgroup G} (hH : IsHyp Ω H)
    {q : G} (hq : q ∈ pCore 2 G) : q ∈ Subgroup.normalizer (H : Set G) := by
  have hqC : q ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
    rw [h.centralizer_zGroup_eq_pCore]
    exact hq
  have hcommH : ∀ x ∈ H, q * x = x * q := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hqC x (hH.1 hx)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hc := hcommH y hy
    have : q * y * q⁻¹ = y := by rw [hc]; group
    rw [this]
    exact hy
  · intro hz
    have hc := hcommH _ hz
    have h2 : q⁻¹ * (q * y * q⁻¹) * q = q * y * q⁻¹ := by
      calc q⁻¹ * (q * y * q⁻¹) * q = q⁻¹ * ((q * y * q⁻¹) * q) := by group
        _ = q⁻¹ * (q * (q * y * q⁻¹)) := by rw [hc]
        _ = q * y * q⁻¹ := by group
    have h3 : q⁻¹ * (q * y * q⁻¹) * q = y := by group
    rw [← h3, h2]
    exact hz

omit h in
theorem deqi_E_pSpan_conj_mem (h : DE2Hyp Ω) {H : Subgroup G} (hH : IsHyp Ω H) {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) {x : G}
    (hx : x ∈ pSpan (omegaHyp Ω H)) : n * x * n⁻¹ ∈ pSpan (omegaHyp Ω H) := by
  have hc : conjSub n H = H := mem_normalizer_iff_conjSub_eq.mp hn
  have hM : conjSub n (pSpan (omegaHyp Ω H)) = pSpan (omegaHyp Ω H) := by
    rw [deqi_conjSub_pSpan_omegaHyp h, hc]
  have hmem : n * x * n⁻¹ ∈ conjSub n (pSpan (omegaHyp Ω H)) := by
    rw [mem_conjSub_iff, show n⁻¹ * (n * x * n⁻¹) * n = x by group]
    exact hx
  rw [hM] at hmem
  exact hmem

omit h in
theorem deqi_E_conj_single (C : Coords Ω) {m : G} {a b : Fin 7} (hab : C.σ m a = b) :
    m * C.β (Multiplicative.ofAdd (Pi.single a (1 : ZMod 2))) * m⁻¹ =
      C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))) := by
  rw [C.conj_eq m]
  congr 2
  funext i
  simp only [toAdd_ofAdd, Pi.single_apply, Equiv.symm_apply_eq, hab]

omit h in
theorem deqi_E_single_mul_self (b : Fin 7) :
    Multiplicative.ofAdd (Pi.single b (1 : ZMod 2) : Fin 7 → ZMod 2) *
      Multiplicative.ofAdd (Pi.single b (1 : ZMod 2) : Fin 7 → ZMod 2) = 1 := by
  apply Multiplicative.toAdd.injective
  funext x
  simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply, toAdd_one, Pi.zero_apply]
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  by_cases hx : x = b
  · subst hx
    simp only [Pi.single_eq_same]
    exact key 1
  · simp [Pi.single_eq_of_ne hx]

omit h in
theorem deqi_E_pair_mem (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H)
    {a b : Fin 7} (ha : a ≠ C.lab H) (hb : b ≠ C.lab H) :
    C.β (Multiplicative.ofAdd (Pi.single a (1 : ZMod 2))) *
        C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))) ∈
      pSpan (omegaHyp Ω H) := by
  obtain ⟨Ha, hHa, hla⟩ := C.lab_surj a
  obtain ⟨Hb, hHb, hlb⟩ := C.lab_surj b
  have hneA : Ha ≠ H := by
    rintro rfl
    exact ha hla.symm
  have hneB : Hb ≠ H := by
    rintro rfl
    exact hb hlb.symm
  obtain ⟨m, hm, hσ⟩ := h.deqi_E_exists_sigma_eq C hH hHa hHb hneA hneB
  rw [hla, hlb] at hσ
  have hmN : m ∈ Subgroup.normalizer (H : Set G) := h.pSpan_omegaHyp_le_normalizer hH hm
  have hqQ : C.β (Multiplicative.ofAdd (Pi.single a (1 : ZMod 2))) ∈ pCore 2 G := by
    rw [← C.range_eq]
    exact ⟨_, rfl⟩
  have hqN := h.deqi_E_pCore_le_normalizer hH hqQ
  have hconj := deqi_E_conj_single C hσ
  have hr2' : C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))) *
      C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))) = 1 := by
    rw [← map_mul, deqi_E_single_mul_self, map_one]
  have hrinv : (C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))))⁻¹ =
      C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))) :=
    inv_eq_of_mul_eq_one_right hr2'
  set q := C.β (Multiplicative.ofAdd (Pi.single a (1 : ZMod 2))) with hq_def
  set r := C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))) with hr_def
  have h2 : m * q⁻¹ * m⁻¹ = r := by
    calc m * q⁻¹ * m⁻¹ = (m * q * m⁻¹)⁻¹ := by group
      _ = r := by rw [hconj, hrinv]
  have h3 : q * r = (q * m * q⁻¹) * m⁻¹ := by
    calc q * r = q * (m * q⁻¹ * m⁻¹) := by rw [h2]
      _ = (q * m * q⁻¹) * m⁻¹ := by group
  rw [h3]
  exact (pSpan _).mul_mem (h.deqi_E_pSpan_conj_mem hH hqN hm) ((pSpan _).inv_mem hm)

omit h in
theorem deqi_E_indicator_mem (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) :
    ∀ n : ℕ, ∀ s : Finset (Fin 7), s.card = n → C.lab H ∉ s → Even n →
      C.β (Multiplicative.ofAdd fun y => if y ∈ s then (1 : ZMod 2) else 0) ∈
        pSpan (omegaHyp Ω H) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hsi hev
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hempty : s = ∅ := Finset.card_eq_zero.mp hs
      subst hempty
      have hfun : (fun y : Fin 7 => if y ∈ (∅ : Finset (Fin 7)) then (1 : ZMod 2) else 0) = 0 := by
        funext y
        simp
      rw [hfun, ofAdd_zero, map_one]
      exact (pSpan _).one_mem
    · have hn2 : 2 ≤ s.card := by
        obtain ⟨k, hk⟩ := hev
        omega
      have h1s : 1 < s.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1s
      have hcard' : ((s.erase a).erase b).card = n - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
          Finset.card_erase_of_mem ha, hs]
        omega
      have hsi' : C.lab H ∉ (s.erase a).erase b := fun hmem =>
        hsi (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
      have hev' : Even (n - 2) := by
        obtain ⟨k, hk⟩ := hev
        exact ⟨k - 1, by omega⟩
      have hIH := ih (n - 2) (by omega) ((s.erase a).erase b) hcard' hsi' hev'
      have hai : a ≠ C.lab H := fun e => hsi (by rw [← e]; exact ha)
      have hbi : b ≠ C.lab H := fun e => hsi (by rw [← e]; exact hb)
      have hpair := h.deqi_E_pair_mem C hH hai hbi
      have hfun : (fun y : Fin 7 => if y ∈ s then (1 : ZMod 2) else 0) =
          (fun y => if y ∈ (s.erase a).erase b then (1 : ZMod 2) else 0) +
            (Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2)) := by
        funext y
        by_cases hya : y = a
        · subst hya
          simp [ha, Finset.mem_erase, hab, Pi.single_apply]
        · by_cases hyb : y = b
          · subst hyb
            simp [hb, Finset.mem_erase, hab, Pi.single_apply]
          · simp [Finset.mem_erase, hya, hyb, Pi.single_apply]
      have e1 : (Multiplicative.ofAdd fun y => if y ∈ s then (1 : ZMod 2) else 0) =
          (Multiplicative.ofAdd fun y => if y ∈ (s.erase a).erase b then (1 : ZMod 2) else 0) *
            (Multiplicative.ofAdd (Pi.single a (1 : ZMod 2)) *
              Multiplicative.ofAdd (Pi.single b (1 : ZMod 2))) := by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_ofAdd]
        exact hfun
      have hsplit : C.β (Multiplicative.ofAdd fun y => if y ∈ s then (1 : ZMod 2) else 0) =
          C.β (Multiplicative.ofAdd fun y => if y ∈ (s.erase a).erase b then (1 : ZMod 2) else 0) *
            (C.β (Multiplicative.ofAdd (Pi.single a (1 : ZMod 2))) *
              C.β (Multiplicative.ofAdd (Pi.single b (1 : ZMod 2)))) := by
        rw [e1, map_mul, map_mul]
      rw [hsplit]
      exact (pSpan _).mul_mem hIH hpair

omit h in
theorem deqi_E_N0_le_pSpan (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) :
    deqi_E_N0 C H ≤ pSpan (omegaHyp Ω H) := by
  classical
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨hf0, hfs⟩ := hf
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin 7), s = Finset.univ.filter fun y => f.toAdd y = 1 := ⟨_, rfl⟩
  have hval : ∀ y, f.toAdd y = if y ∈ s then (1 : ZMod 2) else 0 := by
    intro y
    have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases key (f.toAdd y) with h1 | h1
    · rw [h1, if_neg]
      rw [hs, Finset.mem_filter]
      rintro ⟨-, h2⟩
      rw [h1] at h2
      exact absurd h2 (by decide)
    · rw [h1, if_pos]
      rw [hs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h1⟩
  have hf_eq : f = Multiplicative.ofAdd fun y => if y ∈ s then (1 : ZMod 2) else 0 := by
    apply Multiplicative.toAdd.injective
    funext y
    rw [toAdd_ofAdd]
    exact hval y
  have hsum : ∑ y, f.toAdd y = (s.card : ZMod 2) := by
    rw [Finset.sum_congr rfl (fun y _ => hval y), Finset.sum_boole]
    congr 2
    ext y
    simp
  have heven : Even s.card := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← hsum]
    exact hfs
  have hsi : C.lab H ∉ s := by
    intro hmem
    have := hval (C.lab H)
    rw [if_pos hmem, hf0] at this
    exact absurd this (by decide)
  rw [hf_eq]
  exact h.deqi_E_indicator_mem C hH s.card s rfl hsi heven

omit h in
theorem deqi_E_mem_of_card_le_two {I : Subgroup G} (hI : Nat.card I ≤ 2) {u x : G}
    (hu : u ∈ I) (hu1 : u ≠ 1) (hx : x ∈ I) : x = 1 ∨ x = u := by
  have hsub : ({1, u} : Set G) ⊆ (I : Set G) := by
    intro y hy
    rcases hy with rfl | rfl
    · exact I.one_mem
    · exact hu
  have hcard : (I : Set G).ncard ≤ ({1, u} : Set G).ncard := by
    rw [Set.ncard_pair (Ne.symm hu1), ← Nat.card_coe_set_eq]
    exact hI
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hx' : x ∈ ({1, u} : Set G) := by
    rw [heq]
    exact hx
  rcases hx' with rfl | rfl
  · left; rfl
  · right; rfl

omit h in
theorem deqi_E_sigma_maps_line (h : DE2Hyp Ω) (C : Coords Ω) {u : G} {ℓ : Finset (Fin 7)}
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ)) {g : G}
    (hgu : g * u * g⁻¹ = u) {p : Fin 7} (hp : p ∈ ℓ) : C.σ g p ∈ ℓ := by
  obtain ⟨H', hH', hlab⟩ := C.lab_surj p
  have huH' : u ∈ H' := (hline H' hH').mpr (hlab ▸ hp)
  have hconj : g⁻¹ * u * g = u := by
    conv_lhs => rw [← hgu]
    group
  have hgH : g⁻¹ * u * g ∈ H' := by
    rw [hconj]
    exact huH'
  have huc : u ∈ conjSub g H' := mem_conjSub_iff.mpr hgH
  have hlabc := (hline (conjSub g H') (h.isHyp_conjSub hH' g)).mp huc
  rw [C.lab_conj g H' hH', hlab] at hlabc
  exact hlabc

omit h in
theorem deqi_E_mem_pCore_of_sigma_eq_one (h : DE2Hyp Ω) (C : Coords Ω) {g : G}
    (hg : C.σ g = 1) : g ∈ pCore 2 G := by
  rw [← h.centralizer_zGroup_eq_pCore, Subgroup.mem_centralizer_iff]
  intro d hd
  by_cases hd1 : d = 1
  · subst hd1
    simp
  obtain ⟨ℓ, hℓ, hline⟩ := C.line d hd hd1
  obtain ⟨a, ha, b, hb, hab⟩ := deqi_E_two_points ℓ hℓ
  obtain ⟨H₁, hH₁, hl1⟩ := C.lab_surj a
  obtain ⟨H₂, hH₂, hl2⟩ := C.lab_surj b
  have hd₁ : d ∈ H₁ := (hline H₁ hH₁).mpr (hl1 ▸ ha)
  have hd₂ : d ∈ H₂ := (hline H₂ hH₂).mpr (hl2 ▸ hb)
  have hne : H₂ ≠ H₁ := by
    intro e
    apply hab
    rw [← hl1, ← hl2, e]
  have hnorm : ∀ H' : Subgroup G, IsHyp Ω H' → g ∈ Subgroup.normalizer (H' : Set G) := by
    intro H' hH'
    apply mem_normalizer_iff_conjSub_eq.mpr
    apply C.lab_inj _ _ (h.isHyp_conjSub hH' g) hH'
    rw [C.lab_conj g H' hH', hg, Equiv.Perm.one_apply]
  have hx₁ : g * d * g⁻¹ ∈ H₁ := (Subgroup.mem_normalizer_iff.mp (hnorm H₁ hH₁) d).mp hd₁
  have hx₂ : g * d * g⁻¹ ∈ H₂ := (Subgroup.mem_normalizer_iff.mp (hnorm H₂ hH₂) d).mp hd₂
  have hI := deqi_E_card_inf_le_two hH₁ hH₂ hne
  have hdI : d ∈ H₁ ⊓ H₂ := ⟨hd₁, hd₂⟩
  have hd1I : d ≠ 1 := hd1
  rcases deqi_E_mem_of_card_le_two hI hdI hd1I (⟨hx₁, hx₂⟩ : g * d * g⁻¹ ∈ H₁ ⊓ H₂) with hx | hx
  · exact absurd (mul_left_cancel ((mul_inv_eq_one.mp hx).trans (mul_one g).symm)) hd1
  · exact (mul_inv_eq_iff_eq_mul.mp hx).symm

omit h in
theorem deqi_E_centralize_of_sigma_line (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G}
    (hH : IsHyp Ω H) {u : G} {ℓ : Finset (Fin 7)}
    (hline : ∀ H' : Subgroup G, IsHyp Ω H' → (u ∈ H' ↔ C.lab H' ∈ ℓ))
    (hℓ : ℓ ∈ AE.fanoLines) (huH : u ∈ H) (hu1 : u ≠ 1) {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) (hstab : ∀ p ∈ ℓ, C.σ n p ∈ ℓ) :
    n * u * n⁻¹ = u := by
  have hi0 : C.lab H ∈ ℓ := (hline H hH).mp huH
  have hℓ3 : ℓ.card = 3 := deqi_E_card_line ℓ hℓ
  obtain ⟨p, hpℓ, hpi⟩ : ∃ p ∈ ℓ, p ≠ C.lab H := by
    have hpos : 0 < (ℓ.erase (C.lab H)).card := by
      rw [Finset.card_erase_of_mem hi0, hℓ3]
      norm_num
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    exact ⟨p, Finset.mem_of_mem_erase hp, Finset.ne_of_mem_erase hp⟩
  obtain ⟨H', hH', hlab⟩ := C.lab_surj p
  have huH' : u ∈ H' := (hline H' hH').mpr (hlab ▸ hpℓ)
  have hH'' := h.isHyp_conjSub hH' n
  have hu'' : u ∈ conjSub n H' := (hline (conjSub n H') hH'').mpr (by
    rw [C.lab_conj n H' hH', hlab]
    exact hstab p hpℓ)
  have hne : conjSub n H' ≠ H := by
    intro e
    have hlab'' : C.lab (conjSub n H') = C.lab H := by rw [e]
    rw [C.lab_conj n H' hH', hlab] at hlab''
    have hfix : C.σ n (C.lab H) = C.lab H := deqi_E_sigma_fix C hH hn
    have := (C.σ n).injective (hlab''.trans hfix.symm)
    exact hpi this
  have hmemH : n * u * n⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hn u).mp huH
  have hmemH'' : n * u * n⁻¹ ∈ conjSub n H' := by
    rw [mem_conjSub_iff, show n⁻¹ * (n * u * n⁻¹) * n = u by group]
    exact huH'
  have hI := deqi_E_card_inf_le_two hH hH'' hne
  have huI : u ∈ H ⊓ conjSub n H' := ⟨huH, hu''⟩
  rcases deqi_E_mem_of_card_le_two hI huI hu1 (⟨hmemH, hmemH''⟩ : n * u * n⁻¹ ∈ H ⊓ conjSub n H')
    with hx | hx
  · exact absurd (mul_left_cancel ((mul_inv_eq_one.mp hx).trans (mul_one n).symm)) hu1
  · exact hx

omit h in
theorem deqi_E_mem_PS_iff {i₀ : Fin 7} {ℓ : Finset (Fin 7)} {g : Equiv.Perm (Fin 7)} :
    g ∈ deqi_E_PS i₀ ℓ ↔ g i₀ = i₀ ∧ (∀ p ∈ ℓ, g p = p) ∧ g ∈ AE.l32 := by
  unfold deqi_E_PS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq,
    deqi_E_inL32_iff]
  tauto

omit h in
theorem deqi_E_PS_comm : ∀ i₀ : Fin 7, ∀ ℓ ∈ AE.fanoLines, i₀ ∈ ℓ →
    ∀ g ∈ deqi_E_PS i₀ ℓ, ∀ g' ∈ deqi_E_PS i₀ ℓ, g * g' = g' * g := by
  intro i₀ ℓ hℓ hi g hg g' hg'
  have hgg : g * g' ∈ deqi_E_PS i₀ ℓ := by
    rw [deqi_E_mem_PS_iff] at hg hg' ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    obtain ⟨h1', h2', h3'⟩ := hg'
    exact ⟨by rw [Equiv.Perm.mul_apply, h1', h1],
      fun p hp => by rw [Equiv.Perm.mul_apply, h2' p hp, h2 p hp],
      AE.l32.mul_mem h3 h3'⟩
  have hsq1 := deqi_E_PS_sq i₀ ℓ hℓ hi g hg
  have hsq2 := deqi_E_PS_sq i₀ ℓ hℓ hi g' hg'
  have hsq3 := deqi_E_PS_sq i₀ ℓ hℓ hi (g * g') hgg
  have e1 : (g * g')⁻¹ = g * g' := inv_eq_of_mul_eq_one_right hsq3
  have e2 : g⁻¹ = g := inv_eq_of_mul_eq_one_right hsq1
  have e3 : g'⁻¹ = g' := inv_eq_of_mul_eq_one_right hsq2
  calc g * g' = (g * g')⁻¹ := e1.symm
    _ = g'⁻¹ * g⁻¹ := mul_inv_rev g g'
    _ = g' * g := by rw [e2, e3]

omit h in
theorem deqi_E_sigma_mem_PS (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) (hzH : z ∈ H)
    {ℓ : Finset (Fin 7)}
    (hline : ∀ H' : Subgroup G, IsHyp Ω H' → (z ∈ H' ↔ C.lab H' ∈ ℓ)) {k : G} (hk : k ∈ K) :
    C.σ k ∈ deqi_E_PS (C.lab H) ℓ := by
  rw [deqi_E_mem_PS_iff]
  refine ⟨?_, ?_, C.σ_mem k⟩
  · exact deqi_E_sigma_fix C hH (h.le_normalizer_hyp_of_mem hK hz hH hzH hk)
  · intro p hp
    obtain ⟨H', hH', hlab⟩ := C.lab_surj p
    have hzH' : z ∈ H' := (hline H' hH').mpr (hlab ▸ hp)
    have hkN := h.le_normalizer_hyp_of_mem hK hz hH' hzH' hk
    rw [← hlab]
    exact deqi_E_sigma_fix C hH' hkN

omit h in
theorem deqi_E_sigma_zpowers (h : DE2Hyp Ω) (C : Coords Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {g : G} (hg : g ∈ Subgroup.zpowers z) :
    C.σ g = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨H', hH', hlab⟩ := C.lab_surj i
  have hgK : g ∈ K := Subgroup.zpowers_le.mpr hz.mem hg
  have hN : g ∈ Subgroup.normalizer (H' : Set G) := by
    by_cases hzH' : z ∈ H'
    · exact h.le_normalizer_hyp_of_mem hK hz hH' hzH' hgK
    · have hmem : g ∈ K ⊓ Subgroup.normalizer (H' : Set G) := by
        rw [h.inf_normalizer_hyp_of_not_mem hK hz hH' hzH']
        exact hg
      exact (Subgroup.mem_inf.mp hmem).2
  rw [← hlab, Equiv.Perm.one_apply]
  exact deqi_E_sigma_fix C hH' hN

omit h in
theorem deqi_E_card_zpowers {z : G} (hz : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz) hz1]

omit h in
theorem deqi_E_exists_sigma_eq_of_mem_PS (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G}
    (hH : IsHyp Ω H) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hzH : z ∈ H) {ℓ : Finset (Fin 7)} (hℓ : ℓ ∈ AE.fanoLines)
    (hline : ∀ H' : Subgroup G, IsHyp Ω H' → (z ∈ H' ↔ C.lab H' ∈ ℓ))
    {A : Equiv.Perm (Fin 7)} (hA : A ∈ deqi_E_PS (C.lab H) ℓ) : ∃ k ∈ K, C.σ k = A := by
  classical
  set φ : K →* Equiv.Perm (Fin 7) := (C.σ : G →* Equiv.Perm (Fin 7)).comp K.subtype with hφ
  have hker : φ.ker = (Subgroup.zpowers z).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk1
      have hkpC : (k : G) ∈ pCore 2 G := deqi_E_mem_pCore_of_sigma_eq_one h C hk1
      have hkI : (k : G) ∈ K ⊓ pCore 2 G := ⟨k.2, hkpC⟩
      rw [h.inf_pCore hK hz] at hkI
      exact hkI
    · intro hk
      exact deqi_E_sigma_zpowers h C hK hz hk
  have hcard_ker : Nat.card φ.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hz.mem)).toEquiv]
    exact deqi_E_card_zpowers hz.sq hz.ne_one
  have hcardK : Nat.card K = 8 := h.card K hK
  have hidx := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hcard_ker, hcardK] at hidx
  have hrange : Nat.card φ.range = 4 := by omega
  have hi0 : C.lab H ∈ ℓ := (hline H hH).mp hzH
  have hPS4 : (deqi_E_PS (C.lab H) ℓ).card = 4 := deqi_E_PS_card (C.lab H) ℓ hℓ hi0
  have hsub : (φ.range : Set (Equiv.Perm (Fin 7))) ⊆ (deqi_E_PS (C.lab H) ℓ : Set _) := by
    rintro _ ⟨k, rfl⟩
    exact deqi_E_sigma_mem_PS h C hH hK hz hzH hline k.2
  have hrange' : (φ.range : Set (Equiv.Perm (Fin 7))).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hrange
  have hcard : ((deqi_E_PS (C.lab H) ℓ : Finset _) : Set (Equiv.Perm (Fin 7))).ncard ≤
      (φ.range : Set (Equiv.Perm (Fin 7))).ncard := by
    rw [Set.ncard_coe_finset, hPS4, hrange']
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hAmem : A ∈ (φ.range : Set (Equiv.Perm (Fin 7))) := by
    rw [heq]
    exact hA
  obtain ⟨k, hk⟩ := hAmem
  exact ⟨k.1, k.2, hk⟩

omit h in
theorem deqi_E_zpowers_eq_one_or {z : G} (hz : z * z = 1) (hz1 : z ≠ 1) {k : G}
    (hk : k ∈ Subgroup.zpowers z) : k = 1 ∨ k = z :=
  deqi_E_mem_of_card_le_two (I := Subgroup.zpowers z) (u := z)
    (le_of_eq (deqi_E_card_zpowers hz hz1)) (Subgroup.mem_zpowers z) hz1 hk

omit h in
theorem deqi_E_conj_eq_self_of_mem {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    {k : G} (hk : k ∈ K) : k * z * k⁻¹ = z := by
  have hmem : k * z * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hz.mem) (K.inv_mem hk)
  have hsq : (k * z * k⁻¹) * (k * z * k⁻¹) = 1 := by
    calc (k * z * k⁻¹) * (k * z * k⁻¹) = k * (z * z) * k⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ hmem hsq with h1 | h1
  · exact absurd (mul_left_cancel ((mul_inv_eq_one.mp h1).trans (mul_one k).symm)) hz.ne_one
  · exact h1

omit h in
theorem deqi_E_mem_zpowers_of_sigma_one (h : DE2Hyp Ω) (C : Coords Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) {k : G} (hk : k ∈ K)
    (hσ : C.σ k = 1) : k ∈ Subgroup.zpowers z := by
  have hkI : k ∈ K ⊓ pCore 2 G := ⟨hk, deqi_E_mem_pCore_of_sigma_eq_one h C hσ⟩
  rw [h.inf_pCore hK hz] at hkI
  exact hkI

omit h in
theorem deqi_E_mem_N0_of_norm (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H)
    {q c : G} (hq : q ∈ pCore 2 G) (hc : c ∈ Subgroup.normalizer (H : Set G))
    (hc3 : c ^ 3 = 1) (hqc : (q * c⁻¹) ^ 3 = 1) : q ∈ deqi_E_N0 C H := by
  obtain ⟨f, rfl⟩ : q ∈ C.β.range := by
    rw [C.range_eq]
    exact hq
  have hfix := deqi_E_sigma_fix C hH hc
  have hsymm : ∀ i, (C.σ c⁻¹).symm i = C.σ c i := by
    intro i
    rw [map_inv]
    rfl
  have hc1 : c⁻¹ * C.β f * c = C.β (Multiplicative.ofAdd fun i => f.toAdd (C.σ c i)) := by
    have := C.conj_eq c⁻¹ f
    rw [inv_inv] at this
    rw [this]
    congr 2
    funext i
    rw [hsymm i]
  have hc2 : c⁻¹ * (c⁻¹ * C.β f * c) * c =
      C.β (Multiplicative.ofAdd fun i => f.toAdd (C.σ c (C.σ c i))) := by
    rw [hc1]
    have := C.conj_eq c⁻¹ (Multiplicative.ofAdd fun i => f.toAdd (C.σ c i))
    rw [inv_inv] at this
    rw [this]
    congr 2
    funext i
    simp only [toAdd_ofAdd]
    rw [hsymm i]
  have c3inv : c⁻¹ ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  have key : C.β f * (c⁻¹ * C.β f * c) * (c⁻¹ * (c⁻¹ * C.β f * c) * c) * c⁻¹ ^ 3 = 1 := by
    have e : (C.β f * c⁻¹) ^ 3 = C.β f * (c⁻¹ * C.β f * c) *
        (c⁻¹ * (c⁻¹ * C.β f * c) * c) * c⁻¹ ^ 3 := by
      rw [pow_three']
      group
    rw [← e]
    exact hqc
  rw [c3inv, mul_one, hc2, hc1, ← map_mul, ← map_mul] at key
  have hθ : deqi_E_theta (C.lab H) f = 0 := by
    rcases (C.ker_eq _).mp key with h0 | h1
    · refine deqi_E_theta_eq_zero_of_norm (C.lab H) (C.σ c) hfix f 0 (fun i => ?_)
      have := congrFun h0 i
      simpa [toAdd_mul, toAdd_ofAdd, add_assoc] using this
    · refine deqi_E_theta_eq_zero_of_norm (C.lab H) (C.σ c) hfix f 1 (fun i => ?_)
      have := congrFun h1 i
      simpa [toAdd_mul, toAdd_ofAdd, add_assoc] using this
  exact (deqi_E_mem_N0_iff C H f).mpr hθ

omit h in
theorem deqi_E_F1_mem_N0 (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) {x c : G}
    (hc : c ∈ Subgroup.normalizer (H : Set G)) (hc3 : c ^ 3 = 1)
    (hxx : C.σ x * C.σ x = 1) (hF : C.σ x * C.σ c * C.σ x * C.σ c = 1) :
    x * c * x⁻¹ * c ∈ deqi_E_N0 C H := by
  have hinv : C.σ x⁻¹ = C.σ x := by
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right hxx
  have hσq : C.σ (x * c * x⁻¹ * c) = 1 := by
    rw [map_mul, map_mul, map_mul, hinv]
    exact hF
  have hqpC := deqi_E_mem_pCore_of_sigma_eq_one h C hσq
  apply deqi_E_mem_N0_of_norm C hH hqpC hc hc3
  have e : x * c * x⁻¹ * c * c⁻¹ = x * c * x⁻¹ := by group
  rw [e]
  rw [conj_pow, hc3]
  group

omit h in
theorem deqi_E_sq_eq_z (h : DE2Hyp Ω) (C : Coords Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {x : G} (hxK : x ∈ K) (hx1 : C.σ x ≠ 1)
    (hxx : C.σ x * C.σ x = 1) : x * x = z := by
  have hxxK : x * x ∈ K := K.mul_mem hxK hxK
  have hσ : C.σ (x * x) = 1 := by
    rw [map_mul]
    exact hxx
  have hmem := deqi_E_mem_zpowers_of_sigma_one h C hK hz hxxK hσ
  rcases deqi_E_zpowers_eq_one_or hz.sq hz.ne_one hmem with h1 | h1
  · exfalso
    rcases hz.unique x hxK h1 with h2 | h2
    · exact hx1 (by rw [h2, map_one])
    · exact hx1 (by rw [h2]; exact deqi_E_sigma_zpowers h C hK hz (Subgroup.mem_zpowers z))
  · exact h1

omit h in
theorem deqi_E_comm_mem_zpowers (h : DE2Hyp Ω) (C : Coords Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hcomm : C.σ x * C.σ y = C.σ y * C.σ x) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z := by
  have hwK : (x * y)⁻¹ * (y * x) ∈ K :=
    K.mul_mem (K.inv_mem (K.mul_mem hx hy)) (K.mul_mem hy hx)
  have hσw : C.σ ((x * y)⁻¹ * (y * x)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hcomm, inv_mul_cancel]
  have hw := deqi_E_mem_zpowers_of_sigma_one h C hK hz hwK hσw
  rcases deqi_E_zpowers_eq_one_or hz.sq hz.ne_one hw with hw1 | hwz
  · have hyx1 : y * x = x * y := (inv_mul_eq_one.mp hw1).symm
    have e : x * y * x⁻¹ * y⁻¹ = 1 := by
      calc x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ := by group
        _ = (x * y) * (x * y)⁻¹ := by rw [hyx1]
        _ = 1 := by group
    rw [e]
    exact Subgroup.one_mem _
  · have hyx : y * x = (x * y) * z := by
      rw [← hwz]
      group
    have hzinv : z⁻¹ = z := by
      rw [inv_eq_iff_mul_eq_one, hz.sq]
    have hcen := deqi_E_conj_eq_self_of_mem hz (K.mul_mem hx hy)
    have e : x * y * x⁻¹ * y⁻¹ = z := by
      calc x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ := by group
        _ = (x * y) * ((x * y) * z)⁻¹ := by rw [hyx]
        _ = (x * y) * (z⁻¹ * (x * y)⁻¹) := by group
        _ = (x * y) * (z * (x * y)⁻¹) := by rw [hzinv]
        _ = (x * y) * z * (x * y)⁻¹ := by group
        _ = z := hcen
    rw [e]
    exact Subgroup.mem_zpowers z

omit h in
theorem deqi_E_not_mem_pCore_of_cube {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    c ∉ pCore 2 G := by
  intro hcQ
  have hpg : IsPGroup 2 (pCore 2 G) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpg) ⟨c, hcQ⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc3) with h1 | h1
  · exact hc1 (orderOf_eq_one_iff.mp h1)
  · rw [h1] at hk
    rcases k with _ | k
    · norm_num at hk
    · rw [pow_succ] at hk
      omega

omit h in
theorem deqi_E_sigma_conj_xy (C : Coords Ω) {c x y : G} {A T : Equiv.Perm (Fin 7)}
    (hAA : A * A = 1) (hx : C.σ x = A) (hy : C.σ y = A * T) :
    C.σ (c * (x * y) * c⁻¹) = C.σ c * T * (C.σ c)⁻¹ := by
  rw [map_mul, map_mul, map_mul, map_inv, hx, hy, ← mul_assoc A A T, hAA, one_mul]

omit h in
theorem deqi_E_stab_line {c' T : Equiv.Perm (Fin 7)} (hc : deqi_E_inL32 c' = true) {i₀ : Fin 7}
    (hc0 : c' i₀ = i₀) (hT : deqi_E_blockPres i₀ T) {ℓ : Finset (Fin 7)}
    (hℓ : ℓ ∈ AE.fanoLines) (hi0 : i₀ ∈ ℓ) : ∀ p ∈ ℓ, (c' * T * c'⁻¹) p ∈ ℓ := by
  have hℓ' : ℓ.map c'⁻¹.toEmbedding ∈ AE.fanoLines := by
    have := List.all_eq_true.mp hc ℓ hℓ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hi0' : i₀ ∈ ℓ.map c'⁻¹.toEmbedding := by
    refine Finset.mem_map.mpr ⟨i₀, hi0, ?_⟩
    show c'⁻¹ i₀ = i₀
    exact Equiv.Perm.inv_eq_iff_eq.mpr hc0.symm
  intro p hp
  have hq : c'⁻¹ p ∈ ℓ.map c'⁻¹.toEmbedding := Finset.mem_map.mpr ⟨p, hp, rfl⟩
  have hTq := hT _ hℓ' hi0' _ hq
  obtain ⟨r, hr, hrq⟩ := Finset.mem_map.mp hTq
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hrq]
  simpa using hr

omit h in
theorem deqi_E_n_centralizes (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) (hzH : z ∈ H)
    {ℓ : Finset (Fin 7)} (hℓ : ℓ ∈ AE.fanoLines)
    (hline : ∀ H' : Subgroup G, IsHyp Ω H' → (z ∈ H' ↔ C.lab H' ∈ ℓ))
    {c x y : G} (hcN : c ∈ Subgroup.normalizer (H : Set G)) (hxK : x ∈ K) (hyK : y ∈ K)
    (hstab : ∀ p ∈ ℓ, C.σ (c * (x * y) * c⁻¹) p ∈ ℓ) :
    c * (x * y) * c⁻¹ * z * (c * (x * y) * c⁻¹)⁻¹ = z := by
  have hxyN : x * y ∈ Subgroup.normalizer (H : Set G) :=
    Subgroup.mul_mem _ (h.le_normalizer_hyp_of_mem hK hz hH hzH hxK)
      (h.le_normalizer_hyp_of_mem hK hz hH hzH hyK)
  have hnN : c * (x * y) * c⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hxyN) (Subgroup.inv_mem _ hcN)
  exact deqi_E_centralize_of_sigma_line h C hH hline hℓ hzH hz.ne_one hnN hstab

omit h in
theorem deqi_E_nxn_mem_zpowers (h : DE2Hyp Ω) (C : Coords Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {n x y : G} (hnK : n * x * n⁻¹ ∈ K) (hyK : y ∈ K)
    (hσ : C.σ (n * x * n⁻¹ * y⁻¹) = 1) : n * x * n⁻¹ * y⁻¹ ∈ Subgroup.zpowers z :=
  deqi_E_mem_zpowers_of_sigma_one h C hK hz (K.mul_mem hnK (K.inv_mem hyK)) hσ

omit h in
theorem deqi_E_card_normalizer (h : DE2Hyp Ω) {H : Subgroup G} (hH : IsHyp Ω H) :
    Nat.card ↥(Subgroup.normalizer (H : Set G)) = 1536 := by
  have hG : Nat.card G = 10752 := by
    have h1 := Subgroup.card_mul_index (Subgroup.centralizer (zGroup Ω : Set G))
    rw [h.index_centralizer_zGroup, h.centralizer_zGroup_eq_pCore, h.card_pCore_eq] at h1
    omega
  have h2 := h.card_normalizer_hyp hH
  omega

omit h in
theorem deqi_E_quot_eq_of_mul_inv_mem {α : Type*} [Group α] (S : Subgroup α) [S.Normal]
    {u v : α} (hS : u * v⁻¹ ∈ S) : (QuotientGroup.mk u : α ⧸ S) = QuotientGroup.mk v := by
  rw [QuotientGroup.eq]
  have h1 : v * u⁻¹ ∈ S := by
    have := S.inv_mem hS
    simpa [mul_inv_rev] using this
  have h2 := Subgroup.Normal.conj_mem ‹S.Normal› _ h1 u⁻¹
  have e : u⁻¹ * (v * u⁻¹) * u⁻¹⁻¹ = u⁻¹ * v := by group
  rw [e] at h2
  exact h2

omit h in
theorem deqi_E_N0_subgroupOf_normal (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) :
    ((deqi_E_N0 C H).subgroupOf (Subgroup.normalizer (H : Set G))).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := deqi_E_conj_mem_N0 C hH g.2 hn
  simpa using this

omit h in
theorem deqi_E_card_M_le_data (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) :
    ∃ (K : Subgroup G) (_ : K ∈ Ω) (z : G) (_ : IsUniqueInvolution K z) (_ : z ∈ H) (_ : z ≠ 1),
      ∃ (ℓ : Finset (Fin 7)) (_ : ℓ ∈ AE.fanoLines),
        (∀ H' : Subgroup G, IsHyp Ω H' → (z ∈ H' ↔ C.lab H' ∈ ℓ)) ∧ C.lab H ∈ ℓ := by
  obtain ⟨z, hzH, hz1⟩ : ∃ z ∈ H, z ≠ 1 := by
    haveI : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH.2]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (1 : H)
    exact ⟨x.1, x.2, fun e => hx (Subtype.ext e)⟩
  obtain ⟨K, hK, hz⟩ : ∃ K ∈ Ω, IsUniqueInvolution K z := by
    rcases h.mem_zGroup_iff.mp (hH.1 hzH) with h1 | h1
    · exact absurd h1 hz1
    · obtain ⟨L, hL, hLz⟩ := h1
      exact ⟨L, hL, hLz⟩
  obtain ⟨ℓ, hℓ, hline⟩ := C.line z (hH.1 hzH) hz1
  exact ⟨K, hK, z, hz, hzH, hz1, ℓ, hℓ, hline, (hline H hH).mp hzH⟩

omit h in
theorem deqi_E_mul_inv_mem_N0_of_sigma (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G}
    (hH : IsHyp Ω H) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hzN0 : z ∈ deqi_E_N0 C H) {w k : G} (hw : w ∈ K) (hk : k ∈ K) (hσ : C.σ w = C.σ k) :
    w * k⁻¹ ∈ deqi_E_N0 C H := by
  have hv : k⁻¹ * w ∈ K := K.mul_mem (K.inv_mem hk) hw
  have hσv : C.σ (k⁻¹ * w) = 1 := by
    rw [map_mul, map_inv, hσ, inv_mul_cancel]
  have hvz := deqi_E_mem_zpowers_of_sigma_one h C hK hz hv hσv
  rcases deqi_E_zpowers_eq_one_or hz.sq hz.ne_one hvz with h1 | h1
  · have hw' : w = k := by
      calc w = k * (k⁻¹ * w) := by group
        _ = k := by rw [h1, mul_one]
    rw [hw', mul_inv_cancel]
    exact (deqi_E_N0 C H).one_mem
  · have hw' : w = k * z := by
      calc w = k * (k⁻¹ * w) := by group
        _ = k * z := by rw [h1]
    have hcen : k * z * k⁻¹ = z := deqi_E_conj_eq_self_of_mem hz hk
    rw [hw', hcen]
    exact hzN0

omit h in
theorem deqi_E_twin_cases (h : DE2Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {q : G} (hq : q ∈ pCore 2 G) (hflip : conjSub q K ≠ K)
    {L : Subgroup G} (hL : L ∈ twinSet Ω K) : L = K ∨ L = conjSub q K := by
  obtain ⟨p, r, hpr, hS⟩ := Set.ncard_eq_two.mp (h.twin2 K hK)
  have hKS : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hcS : conjSub q K ∈ twinSet Ω K := h.conjSub_mem_twinSet hq hK
  rw [hS] at hKS hcS hL
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hKS hcS hL
  by_cases hLK : L = K
  · exact Or.inl hLK
  · right
    rcases hKS with e1 | e1 <;> rcases hcS with e2 | e2 <;> rcases hL with e3 | e3 <;>
      simp_all

omit h in
theorem deqi_E_mem_H_cases {H : Subgroup G} (hH : IsHyp Ω H) {z c : G} (hzH : z ∈ H)
    (hz1 : z ≠ 1) (hcN : c ∈ Subgroup.normalizer (H : Set G)) (hc3 : c ^ 3 = 1)
    (hcz : c * z * c⁻¹ ≠ z) {u : G} (huH : u ∈ H) (hu1 : u ≠ 1) :
    u = z ∨ u = c * z * c⁻¹ ∨ u = c⁻¹ * z * c := by
  have hczH : c * z * c⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hcN z).mp hzH
  have hc'zH : c⁻¹ * z * c ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) z).mp hzH
    simpa using this
  have hcc : c * c = c⁻¹ :=
    eq_inv_of_mul_eq_one_left (show c * c * c = 1 by rw [← pow_three']; exact hc3)
  have hd2 : c⁻¹ * z * c ≠ z := by
    intro e
    apply hcz
    calc c * z * c⁻¹ = c * (c⁻¹ * z * c) * c⁻¹ := by rw [e]
      _ = z := by group
  have hd3 : c * z * c⁻¹ ≠ c⁻¹ * z * c := by
    intro e
    apply hd2
    calc c⁻¹ * z * c = c * c * z * (c * c)⁻¹ := by rw [hcc, inv_inv]
      _ = c * (c * z * c⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * z * c) * c⁻¹ := by rw [e]
      _ = z := by group
  have hsub : ({z, c * z * c⁻¹, c⁻¹ * z * c} : Set G) ⊆ (H : Set G) \ {1} := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    refine ⟨?_, ?_⟩
    · rcases hy with rfl | rfl | rfl
      · exact hzH
      · exact hczH
      · exact hc'zH
    · simp only [Set.mem_singleton_iff]
      rcases hy with rfl | rfl | rfl
      · exact hz1
      · intro e
        exact hz1 (mul_left_cancel ((mul_inv_eq_one.mp e).trans (mul_one c).symm))
      · intro e
        have h1 : c⁻¹ * z = c⁻¹ := by
          have := mul_eq_one_iff_eq_inv.mp e
          exact this
        exact hz1 (mul_left_cancel (h1.trans (mul_one c⁻¹).symm))
  have hcard3 : ({z, c * z * c⁻¹, c⁻¹ * z * c} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hd3]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun e => hcz e.symm, fun e => hd2 e.symm⟩
  have hdiff : ((H : Set G) \ {1}).ncard = 3 := by
    rw [Set.ncard_diff_singleton_of_mem H.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hH.2
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard3, hdiff]) (Set.toFinite _)
  have hu : u ∈ ({z, c * z * c⁻¹, c⁻¹ * z * c} : Set G) := by
    rw [heq]
    exact ⟨huH, hu1⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hu

omit h in
theorem deqi_E_card_M_le (h : DE2Hyp Ω) (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) :
    Nat.card ↥(pSpan (omegaHyp Ω H)) ≤ 768 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK, z, hz, hzH, hz1, ℓ, hℓ, hline, hi0⟩ := deqi_E_card_M_le_data h C hH
  have hN3 : 3 ∣ Nat.card ↥(Subgroup.normalizer (H : Set G)) := by
    rw [deqi_E_card_normalizer h hH]
    norm_num
  obtain ⟨g3, hg3⟩ := exists_prime_orderOf_dvd_card' 3 hN3
  obtain ⟨c, hcN, hc3, hc1⟩ : ∃ c ∈ Subgroup.normalizer (H : Set G), c ^ 3 = 1 ∧ c ≠ 1 := by
    refine ⟨(g3 : G), g3.2, ?_, ?_⟩
    · have h1 : g3 ^ 3 = 1 := by
        rw [← hg3]
        exact pow_orderOf_eq_one g3
      have h2 := congrArg (fun y : Subgroup.normalizer (H : Set G) => (y : G)) h1
      simpa using h2
    · intro e
      have h1 : g3 = 1 := Subtype.ext e
      rw [h1, orderOf_one] at hg3
      norm_num at hg3
  have hσc1 : C.σ c ≠ 1 := fun e =>
    deqi_E_not_mem_pCore_of_cube hc3 hc1 (deqi_E_mem_pCore_of_sigma_eq_one h C e)
  have hσc3 : C.σ c * C.σ c * C.σ c = 1 := by
    have h1 : C.σ (c * c * c) = 1 := by
      rw [← pow_three', hc3, map_one]
    simpa only [map_mul] using h1
  have hσc0 : C.σ c (C.lab H) = C.lab H := deqi_E_sigma_fix C hH hcN
  have hσcL : deqi_E_inL32 (C.σ c) = true := (deqi_E_inL32_iff _).mpr (C.σ_mem c)
  obtain ⟨A, hA, T, hT, hTblock, hT1, hA1, hAT, hAA, hTT, hBPS, hF1, hNrel⟩ :=
    deqi_E_key (C.lab H) ℓ hℓ hi0 (C.σ c) hσc0 hσc3 hσc1 hσcL
  obtain ⟨x, hxK, hxσ⟩ := deqi_E_exists_sigma_eq_of_mem_PS h C hH hK hz hzH hℓ hline hA
  obtain ⟨y, hyK, hyσ⟩ := deqi_E_exists_sigma_eq_of_mem_PS h C hH hK hz hzH hℓ hline hBPS
  have hxN : x ∈ Subgroup.normalizer (H : Set G) := h.le_normalizer_hyp_of_mem hK hz hH hzH hxK
  have hyN : y ∈ Subgroup.normalizer (H : Set G) := h.le_normalizer_hyp_of_mem hK hz hH hzH hyK
  have hzN0 : z ∈ deqi_E_N0 C H := (deqi_E_mem_N0_iff_mem_zGroup C hH (hH.1 hzH)).mpr hzH
  have hAA' : C.σ x * C.σ x = 1 := by
    rw [hxσ]
    exact hAA
  have hx1 : C.σ x ≠ 1 := by
    rw [hxσ]
    exact hA1
  have hxx : x * x = z := deqi_E_sq_eq_z h C hK hz hxK hx1 hAA'
  have hyy' : C.σ y * C.σ y = 1 := by
    rw [hyσ]
    exact deqi_E_PS_sq (C.lab H) ℓ hℓ hi0 (A * T) hBPS
  have hy1 : C.σ y ≠ 1 := by
    rw [hyσ]
    intro e
    apply hAT
    calc A = A * T * T := by rw [mul_assoc, hTT, mul_one]
      _ = T := by rw [e, one_mul]
  have hyy : y * y = z := deqi_E_sq_eq_z h C hK hz hyK hy1 hyy'
  have hcomm : C.σ x * C.σ y = C.σ y * C.σ x := by
    rw [hxσ, hyσ]
    exact deqi_E_PS_comm (C.lab H) ℓ hℓ hi0 A hA (A * T) hBPS
  have hcomm' : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z :=
    deqi_E_comm_mem_zpowers h C hK hz hxK hyK hcomm
  have hcz : c * z * c⁻¹ ≠ z := by
    intro e
    apply deqi_E_moves (C.lab H) ℓ hℓ hi0 (C.σ c) hσc0 hσc3 hσc1 hσcL
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      exact deqi_E_sigma_maps_line h C hline e hp
    · rw [Finset.card_map]
  have hF : C.σ x * C.σ c * C.σ x * C.σ c = 1 := by
    rw [hxσ]
    exact hF1
  have hq' : x * c * x⁻¹ * c ∈ deqi_E_N0 C H := deqi_E_F1_mem_N0 h C hH hcN hc3 hAA' hF
  have hσn : C.σ (c * (x * y) * c⁻¹) = C.σ c * T * (C.σ c)⁻¹ :=
    deqi_E_sigma_conj_xy C hAA hxσ hyσ
  have hstab : ∀ p ∈ ℓ, C.σ (c * (x * y) * c⁻¹) p ∈ ℓ := by
    rw [hσn]
    exact deqi_E_stab_line hσcL hσc0 hTblock hℓ hi0
  have hnz : c * (x * y) * c⁻¹ * z * (c * (x * y) * c⁻¹)⁻¹ = z :=
    deqi_E_n_centralizes h C hH hK hz hzH hℓ hline hcN hxK hyK hstab
  have hMc : conjSub c K ∈ Ω := h.hyp.conjInvariant c K hK
  have hnot : conjSub c K ∉ twinSet Ω K := by
    intro hmem
    obtain ⟨z', hz'K, hz'J⟩ := hmem.2
    have e1 : z = z' := hz.eq hz'K
    have hcz' : IsUniqueInvolution (conjSub c K) (c * z * c⁻¹) := hz.conj c
    have e2 : c * z * c⁻¹ = z' := hcz'.eq hz'J
    exact hcz (e2.trans e1.symm)
  have hnmem : c * (x * y) * c⁻¹ ∈ conjSub c K ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine ⟨mem_conjSub_iff.mpr ?_, ?_⟩
    · rw [show c⁻¹ * (c * (x * y) * c⁻¹) * c = x * y by group]
      exact K.mul_mem hxK hyK
    · show c * (x * y) * c⁻¹ ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * (x * y) * c⁻¹ * z
          = (c * (x * y) * c⁻¹ * z * (c * (x * y) * c⁻¹)⁻¹) * (c * (x * y) * c⁻¹) := by group
        _ = z * (c * (x * y) * c⁻¹) := by rw [hnz]
  have hnK : c * (x * y) * c⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (h.card_inf_centralizer_of_not_mem_twinSet hK hMc hnot hz).2.2 K ⟨hK, z, hz, hz⟩ hnmem
  have hnxnK : c * (x * y) * c⁻¹ * x * (c * (x * y) * c⁻¹)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hnK x).mp hxK
  have hσnxn : C.σ (c * (x * y) * c⁻¹ * x * (c * (x * y) * c⁻¹)⁻¹ * y⁻¹) = 1 := by
    have key : ∀ m : G, C.σ (m * x * m⁻¹ * y⁻¹) = C.σ m * A * (C.σ m)⁻¹ * (A * T)⁻¹ := by
      intro m
      simp only [map_mul, map_inv, hxσ, hyσ]
    rw [key, hσn]
    have hinv : (C.σ c * T * (C.σ c)⁻¹)⁻¹ = C.σ c * T * (C.σ c)⁻¹ := by
      apply inv_eq_of_mul_eq_one_right
      calc (C.σ c * T * (C.σ c)⁻¹) * (C.σ c * T * (C.σ c)⁻¹)
          = C.σ c * (T * T) * (C.σ c)⁻¹ := by group
        _ = 1 := by rw [hTT]; group
    rw [hinv, hNrel, mul_inv_cancel]
  have hnxn_N0 : c * (x * y) * c⁻¹ * x * (c * (x * y) * c⁻¹)⁻¹ * y⁻¹ ∈ deqi_E_N0 C H :=
    Subgroup.zpowers_le.mpr hzN0
      (deqi_E_nxn_mem_zpowers h C hK hz hnxnK hyK hσnxn)
  have hxcxc : x * c * x * c ∈ deqi_E_N0 C H := by
    have hcz' : c⁻¹ * z * c ∈ deqi_E_N0 C H := by
      have := deqi_E_conj_mem_N0 C hH (Subgroup.inv_mem _ hcN) hzN0
      simpa using this
    have e : x * c * x * c = (x * c * x⁻¹ * c) * (c⁻¹ * z * c) := by
      rw [← hxx]
      group
    rw [e]
    exact (deqi_E_N0 C H).mul_mem hq' hcz'
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  haveI hS0 : (((deqi_E_N0 C H).subgroupOf N)).Normal := deqi_E_N0_subgroupOf_normal C hH
  let X : N := ⟨x, hxN⟩
  let Y : N := ⟨y, hyN⟩
  let Cc : N := ⟨c, hcN⟩
  let mk : N →* N ⧸ (deqi_E_N0 C H).subgroupOf N := QuotientGroup.mk' _
  have hmk_eq : ∀ u v : N, (u : G) * (v : G)⁻¹ ∈ deqi_E_N0 C H → mk u = mk v := by
    intro u v huv
    apply deqi_E_quot_eq_of_mul_inv_mem ((deqi_E_N0 C H).subgroupOf N)
    rw [Subgroup.mem_subgroupOf]
    simpa using huv
  have hmk1 : ∀ u : N, (u : G) ∈ deqi_E_N0 C H → mk u = 1 := by
    intro u hu
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hu
  have hXX : mk X * mk X = 1 := by
    rw [← map_mul]
    apply hmk1
    show x * x ∈ deqi_E_N0 C H
    rw [hxx]
    exact hzN0
  have hYY : mk Y * mk Y = 1 := by
    rw [← map_mul]
    apply hmk1
    show y * y ∈ deqi_E_N0 C H
    rw [hyy]
    exact hzN0
  have hab : mk X * mk Y = mk Y * mk X := by
    have key := hmk_eq (X * Y) (Y * X) (by
      show x * y * (y * x)⁻¹ ∈ deqi_E_N0 C H
      have e : x * y * (y * x)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
      rw [e]
      exact (Subgroup.zpowers_le.mpr hzN0) hcomm')
    rw [map_mul, map_mul] at key
    exact key
  have hcc3 : mk Cc * mk Cc * mk Cc = 1 := by
    rw [← map_mul, ← map_mul]
    have h3 : Cc * Cc * Cc = 1 := by
      apply Subtype.ext
      show c * c * c = 1
      rw [← pow_three']
      exact hc3
    rw [h3, map_one]
  have hcac : mk X * mk Cc * mk X = (mk Cc)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h1 : mk X * mk Cc * mk X * mk Cc = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul]
      apply hmk1
      show x * c * x * c ∈ deqi_E_N0 C H
      exact hxcxc
    exact h1
  have hn : ((mk Cc) * (mk X * mk Y) * (mk Cc)⁻¹) * mk X *
      ((mk Cc) * (mk X * mk Y) * (mk Cc)⁻¹)⁻¹ = mk Y := by
    have huv : ((Cc * (X * Y) * Cc⁻¹ * X * (Cc * (X * Y) * Cc⁻¹)⁻¹ : N) : G) *
        ((Y : N) : G)⁻¹ ∈ deqi_E_N0 C H := by
      show c * (x * y) * c⁻¹ * x * (c * (x * y) * c⁻¹)⁻¹ * y⁻¹ ∈ deqi_E_N0 C H
      exact hnxn_N0
    have key := hmk_eq (Cc * (X * Y) * Cc⁻¹ * X * (Cc * (X * Y) * Cc⁻¹)⁻¹) Y huv
    simpa only [map_mul, map_inv] using key
  have hcox := deqi_E_coxeter_data hXX hYY hab hcc3 hcac hn
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup (N ⧸ (deqi_E_N0 C H).subgroupOf N),
      W = Subgroup.closure ({mk X, mk Cc * mk X * (mk Cc)⁻¹, mk Y} :
        Set (N ⧸ (deqi_E_N0 C H).subgroupOf N)) := ⟨_, rfl⟩
  have hWcard : Nat.card ↥W ≤ 24 := by rw [hWdef]; exact hcox
  have hXW : mk X ∈ W := by rw [hWdef]; exact Subgroup.subset_closure (by simp)
  have hYW : mk Y ∈ W := by rw [hWdef]; exact Subgroup.subset_closure (by simp)
  have hTW : mk Cc * mk X * (mk Cc)⁻¹ ∈ W := by
    rw [hWdef]; exact Subgroup.subset_closure (by simp)
  have hcW : mk Cc ∈ W := by
    have hinv : (mk Cc)⁻¹ = mk Cc * mk Cc :=
      inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hcc3)
    have e : mk X * (mk Cc * mk X * (mk Cc)⁻¹) = mk Cc := by
      calc mk X * (mk Cc * mk X * (mk Cc)⁻¹) = (mk X * mk Cc * mk X) * (mk Cc)⁻¹ := by group
        _ = (mk Cc)⁻¹ * (mk Cc)⁻¹ := by rw [hcac]
        _ = mk Cc := by
          rw [hinv]
          calc mk Cc * mk Cc * (mk Cc * mk Cc) = mk Cc * (mk Cc * mk Cc * mk Cc) := by group
            _ = mk Cc := by rw [hcc3, mul_one]
    have h1 := W.mul_mem hXW hTW
    rwa [e] at h1
  obtain ⟨Sw, hSdef⟩ : ∃ Sw : Subgroup G, Sw = (W.comap mk).map N.subtype := ⟨_, rfl⟩
  have hmemS : ∀ w (hw : w ∈ N), mk ⟨w, hw⟩ ∈ W → w ∈ Sw := fun w hw hW => by
    rw [hSdef]; exact Subgroup.mem_map.mpr ⟨⟨w, hw⟩, hW, rfl⟩
  have hcS : c ∈ Sw := hmemS c hcN hcW
  have hPS_fin : ∀ g ∈ deqi_E_PS (C.lab H) ℓ, g = 1 ∨ g = A ∨ g = A * T ∨ g = T := by
    have hsub : ({1, A, A * T, T} : Finset (Equiv.Perm (Fin 7))) ⊆ deqi_E_PS (C.lab H) ℓ := by
      intro g hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact deqi_E_mem_PS_iff.mpr ⟨by simp, fun p _ => rfl, AE.l32.one_mem⟩
      · exact hA
      · exact hBPS
      · exact hT
    have hcard4 : ({1, A, A * T, T} : Finset (Equiv.Perm (Fin 7))).card = 4 := by
      have hA1' : (1 : Equiv.Perm (Fin 7)) ≠ A := fun e => hA1 e.symm
      have hB1 : (1 : Equiv.Perm (Fin 7)) ≠ A * T := fun e => by
        apply hAT
        calc A = A * T * T := by rw [mul_assoc, hTT, mul_one]
          _ = T := by rw [← e, one_mul]
      have hT1' : (1 : Equiv.Perm (Fin 7)) ≠ T := fun e => hT1 e.symm
      have hAB : A ≠ A * T := fun e => hT1 (mul_left_cancel (e.symm.trans (mul_one A).symm))
      have hBT : A * T ≠ T := fun e => hA1 (mul_right_cancel (e.trans (one_mul T).symm))
      have hn1 : (1 : Equiv.Perm (Fin 7)) ∉ ({A, A * T, T} : Finset (Equiv.Perm (Fin 7))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hA1', hB1, hT1'⟩
      have hn2 : A ∉ ({A * T, T} : Finset (Equiv.Perm (Fin 7))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hAB, hAT⟩
      rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
        Finset.card_pair hBT]
    have heq := Finset.eq_of_subset_of_card_le hsub
      (le_of_eq (by rw [hcard4, deqi_E_PS_card (C.lab H) ℓ hℓ hi0]))
    intro g hg
    rw [← heq] at hg
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hg
  have hKW : ∀ w ∈ K, ∃ hw : w ∈ N, mk ⟨w, hw⟩ ∈ W := by
    intro w hw
    have hwN : w ∈ N := h.le_normalizer_hyp_of_mem hK hz hH hzH hw
    refine ⟨hwN, ?_⟩
    rcases hPS_fin _ (deqi_E_sigma_mem_PS h C hH hK hz hzH hline hw) with e | e | e | e
    · have hk := deqi_E_mul_inv_mem_N0_of_sigma h C hH hK hz hzN0 hw K.one_mem
        (by rw [map_one, e])
      rw [hmk_eq ⟨w, hwN⟩ 1 (by simpa using hk), map_one]
      exact W.one_mem
    · have hk := deqi_E_mul_inv_mem_N0_of_sigma h C hH hK hz hzN0 hw hxK (by rw [hxσ, e])
      rw [hmk_eq ⟨w, hwN⟩ X hk]
      exact hXW
    · have hk := deqi_E_mul_inv_mem_N0_of_sigma h C hH hK hz hzN0 hw hyK (by rw [hyσ, e])
      rw [hmk_eq ⟨w, hwN⟩ Y hk]
      exact hYW
    · have hxyK : x * y ∈ K := K.mul_mem hxK hyK
      have hk := deqi_E_mul_inv_mem_N0_of_sigma h C hH hK hz hzN0 hw hxyK
        (by rw [map_mul, hxσ, hyσ, ← mul_assoc, hAA, one_mul, e])
      rw [hmk_eq ⟨w, hwN⟩ (X * Y) hk, map_mul]
      exact W.mul_mem hXW hYW
  have hTw : ∀ L ∈ twinSet Ω K, ∀ w ∈ L, w ∈ Sw := by
    intro L hL w hw
    obtain ⟨q, hqQ, hq1⟩ := h.exists_flip hK
    have hflip : conjSub q K ≠ K := by
      intro e
      rw [flipVal, if_pos e] at hq1
      exact absurd hq1 (by decide)
    rcases deqi_E_twin_cases h hK hz hqQ hflip hL with rfl | rfl
    · obtain ⟨hwN, hwW⟩ := hKW w hw
      exact hmemS w hwN hwW
    · obtain ⟨k, hk, hwq⟩ : ∃ k ∈ K, w = q * k * q⁻¹ :=
        ⟨q⁻¹ * w * q, mem_conjSub_iff.mp hw, by group⟩
      subst hwq
      obtain ⟨hkN, hkW⟩ := hKW k hk
      have hqN : q ∈ N := h.deqi_E_pCore_le_normalizer hH hqQ
      have hwN : q * k * q⁻¹ ∈ N := N.mul_mem (N.mul_mem hqN hkN) (N.inv_mem hqN)
      have hcom : q * k * q⁻¹ * k⁻¹ ∈ deqi_E_N0 C H := deqi_E_comm_mem_N0 C hH hqQ hkN
      refine hmemS _ hwN ?_
      rw [hmk_eq ⟨q * k * q⁻¹, hwN⟩ ⟨k, hkN⟩ hcom]
      exact hkW
  have hgen : ∀ g ∈ Sw, ∀ L' : Subgroup G, (∀ x ∈ L', x ∈ Sw) →
      ∀ w, g⁻¹ * w * g ∈ L' → w ∈ Sw := by
    intro g hg L' hL' w hw
    have h1 := Sw.mul_mem (Sw.mul_mem hg (hL' _ hw)) (Sw.inv_mem hg)
    have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    rwa [e] at h1
  have hMS : ∀ L ∈ omegaHyp Ω H, ∀ w ∈ L, w ∈ Sw := by
    intro L hL w hw
    obtain ⟨hLΩ, u, huH, hu⟩ := hL
    rcases deqi_E_mem_H_cases hH hzH hz1 hcN hc3 hcz huH hu.ne_one with hue | hue | hue
    · rw [hue] at hu
      exact hTw L ⟨hLΩ, z, hz, hu⟩ w hw
    · rw [hue] at hu
      have hu' : IsUniqueInvolution (conjSub c⁻¹ L) z := by
        have h1 := hu.conj c⁻¹
        rwa [show c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z by group] at h1
      have hmem : conjSub c⁻¹ L ∈ twinSet Ω K :=
        ⟨h.hyp.conjInvariant c⁻¹ L hLΩ, z, hz, hu'⟩
      refine hgen c hcS (conjSub c⁻¹ L) (fun x hx => hTw _ hmem x hx) w ?_
      rw [mem_conjSub_iff, inv_inv, show c * (c⁻¹ * w * c) * c⁻¹ = w by group]
      exact hw
    · rw [hue] at hu
      have hu' : IsUniqueInvolution (conjSub c L) z := by
        have h1 := hu.conj c
        rwa [show c * (c⁻¹ * z * c) * c⁻¹ = z by group] at h1
      have hmem : conjSub c L ∈ twinSet Ω K :=
        ⟨h.hyp.conjInvariant c L hLΩ, z, hz, hu'⟩
      refine hgen c⁻¹ (Sw.inv_mem hcS) (conjSub c L) (fun x hx => hTw _ hmem x hx) w ?_
      rw [mem_conjSub_iff, inv_inv, show c⁻¹ * (c * w * c⁻¹) * c = w by group]
      exact hw
  have hpS : pSpan (omegaHyp Ω H) ≤ Sw := by
    refine pSpan_le fun L hL => ?_
    intro w hw
    exact hMS L hL w hw
  have hI : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : (W.comap mk).index = W.index :=
    Subgroup.index_comap_of_surjective W (QuotientGroup.mk'_surjective _)
  have hN0N : deqi_E_N0 C H ≤ N := fun x hx =>
    h.deqi_E_pCore_le_normalizer hH (deqi_E_N0_le C H hx)
  have hN0card : Nat.card ↥((deqi_E_N0 C H).subgroupOf N) = 32 := by
    rw [← deqi_E_N0_card C H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN0N).toEquiv
  have hsub_card : Nat.card ↥Sw = Nat.card ↥(W.comap mk) := by
    rw [hSdef]; exact Subgroup.card_map_of_injective Subtype.val_injective
  have hA1' := (W.comap mk).card_mul_index
  have hA2 := W.card_mul_index
  have hA4 := ((deqi_E_N0 C H).subgroupOf N).card_mul_index
  have hkey : Nat.card ↥(W.comap mk) * W.index = (32 * Nat.card ↥W) * W.index := by
    calc Nat.card ↥(W.comap mk) * W.index = Nat.card ↥(W.comap mk) * (W.comap mk).index := by
          rw [hidx]
      _ = Nat.card ↥N := hA1'
      _ = Nat.card ↥((deqi_E_N0 C H).subgroupOf N) * ((deqi_E_N0 C H).subgroupOf N).index :=
          hA4.symm
      _ = 32 * ((deqi_E_N0 C H).subgroupOf N).index := by rw [hN0card]
      _ = 32 * Nat.card (N ⧸ (deqi_E_N0 C H).subgroupOf N) := rfl
      _ = 32 * (Nat.card ↥W * W.index) := by rw [hA2]
      _ = (32 * Nat.card ↥W) * W.index := by ring
  have hcard_W : Nat.card ↥(W.comap mk) = 32 * Nat.card ↥W :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hI) hkey
  calc Nat.card ↥(pSpan (omegaHyp Ω H)) ≤ Nat.card ↥Sw := Subgroup.card_le_of_le hpS
    _ = 32 * Nat.card ↥W := by rw [hsub_card, hcard_W]
    _ ≤ 32 * 24 := Nat.mul_le_mul_left 32 hWcard
    _ = 768 := by norm_num

theorem deqi_E_inf_pCore_eq (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) :
    pSpan (omegaHyp Ω H) ⊓ pCore 2 G = deqi_E_N0 C H := by
  have hN0M : deqi_E_N0 C H ≤ pSpan (omegaHyp Ω H) := deqi_E_N0_le_pSpan h C hH
  have hN0Q : deqi_E_N0 C H ≤ pCore 2 G := deqi_E_N0_le C H
  have hle : deqi_E_N0 C H ≤ pSpan (omegaHyp Ω H) ⊓ pCore 2 G := le_inf hN0M hN0Q
  have hMle : Nat.card ↥(pSpan (omegaHyp Ω H)) ≤ 768 := deqi_E_card_M_le h C hH
  have hNcard : Nat.card ↥(Subgroup.normalizer (H : Set G)) = 1536 :=
    deqi_E_card_normalizer h hH
  have hQcard : Nat.card ↥(pCore 2 G) = 64 := h.card_pCore_eq
  have hN0card : Nat.card ↥(deqi_E_N0 C H) = 32 := deqi_E_N0_card C H
  have hN : Subgroup.normalizer (H : Set G) = pSpan (omegaHyp Ω H) ⊔ pCore 2 G :=
    h.normalizer_hyp_eq_sup hH
  have hQN : pCore 2 G ≤ Subgroup.normalizer (H : Set G) := by
    rw [hN]; exact le_sup_right
  have hs : (pCore 2 G).relIndex (Subgroup.normalizer (H : Set G)) =
      (pCore 2 G).relIndex (pSpan (omegaHyp Ω H)) := by
    rw [hN]; exact Subgroup.relIndex_sup_right (H := pSpan (omegaHyp Ω H)) (K := pCore 2 G)
  have h1 : (pCore 2 G).relIndex (Subgroup.normalizer (H : Set G)) *
      Nat.card ↥(pCore 2 G ⊓ Subgroup.normalizer (H : Set G)) =
        Nat.card ↥(Subgroup.normalizer (H : Set G)) := Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr hQN, hQcard, hNcard, hs] at h1
  have h2 : (pCore 2 G).relIndex (pSpan (omegaHyp Ω H)) *
      Nat.card ↥(pCore 2 G ⊓ pSpan (omegaHyp Ω H)) = Nat.card ↥(pSpan (omegaHyp Ω H)) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_comm (pCore 2 G) (pSpan (omegaHyp Ω H))] at h2
  have h24 : (pCore 2 G).relIndex (pSpan (omegaHyp Ω H)) = 24 := by omega
  rw [h24] at h2
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem inf_pCore_relIndex {H : Subgroup G} (hH : IsHyp Ω H) :
    (pSpan (omegaHyp Ω H) ⊓ pCore 2 G).relIndex (pCore 2 G) = 2 := by
  obtain ⟨C⟩ := h.exists_coords
  rw [deqi_E_inf_pCore_eq h C hH]
  have h1 : (deqi_E_N0 C H).relIndex (pCore 2 G) *
      Nat.card ↥(deqi_E_N0 C H ⊓ pCore 2 G) = Nat.card ↥(pCore 2 G) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr (deqi_E_N0_le C H), deqi_E_N0_card, h.card_pCore_eq] at h1
  omega

theorem inf_zGroup_eq {H : Subgroup G} (hH : IsHyp Ω H) :
    pSpan (omegaHyp Ω H) ⊓ zGroup Ω = H := by
  obtain ⟨C⟩ := h.exists_coords
  apply le_antisymm
  · rintro g ⟨hgM, hgD⟩
    have hgQ : g ∈ pSpan (omegaHyp Ω H) ⊓ pCore 2 G := ⟨hgM, h.zGroup_le_pCore hgD⟩
    rw [deqi_E_inf_pCore_eq h C hH] at hgQ
    exact (deqi_E_mem_N0_iff_mem_zGroup C hH hgD).mp hgQ
  · intro x hx
    refine ⟨?_, hH.1 hx⟩
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · obtain ⟨L, hL, hLx⟩ : ∃ L ∈ Ω, IsUniqueInvolution L x := by
        rcases h.mem_zGroup_iff.mp (hH.1 hx) with h1 | h1
        · exact absurd h1 hx1
        · exact h1
      exact le_pSpan (L := L) (P := omegaHyp Ω H) ⟨hL, x, hx, hLx⟩ hLx.mem

omit h in
theorem deqi_conjSub_eq_of_centralizes {K : Subgroup G} (hK : K ≤ zGroup Ω) {q : G}
    (hq : q ∈ Subgroup.centralizer (zGroup Ω : Set G)) : conjSub q K = K := by
  have hcomm : ∀ y ∈ zGroup Ω, q⁻¹ * y * q = y := fun y hy => by
    have hyq : y * q = q * y := (Subgroup.mem_centralizer_iff.mp hq) y hy
    calc q⁻¹ * y * q = q⁻¹ * (y * q) := by rw [mul_assoc]
      _ = y := by rw [hyq]; group
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have hk : q⁻¹ * (q⁻¹ * x * q) * q = q⁻¹ * x * q := hcomm _ (hK hx)
    have hkq : (q⁻¹ * x * q) * q = q * (q⁻¹ * x * q) := by
      calc (q⁻¹ * x * q) * q = q * (q⁻¹ * (q⁻¹ * x * q) * q) := by group
        _ = q * (q⁻¹ * x * q) := by rw [hk]
    have hxk : x = q⁻¹ * x * q := by
      calc x = (q * (q⁻¹ * x * q)) * q⁻¹ := by group
        _ = ((q⁻¹ * x * q) * q) * q⁻¹ := by rw [hkq]
        _ = q⁻¹ * x * q := by group
    rw [hxk]
    exact hx
  · intro hx
    rw [hcomm x (hK hx)]
    exact hx

theorem exists_chi {H : Subgroup G} (hH : IsHyp Ω H) :
    ∃ χ : Subgroup.normalizer (H : Set G) →* Multiplicative (ZMod 2),
      χ.ker = (pSpan (omegaHyp Ω H)).subgroupOf (Subgroup.normalizer (H : Set G)) ∧
        Function.Surjective χ := by
  classical
  set N : Subgroup G := Subgroup.normalizer (H : Set G) with hNdef
  set M : Subgroup G := pSpan (omegaHyp Ω H) with hMdef
  set Q : Subgroup G := pCore 2 G with hQdef
  have hMnorm : ∀ g ∈ N, ∀ x ∈ M, g * x * g⁻¹ ∈ M := by
    intro g hg x hx
    have hc : conjSub g H = H := mem_normalizer_iff_conjSub_eq.mp hg
    have hcM : conjSub g M = M := by
      rw [hMdef, h.deqi_conjSub_pSpan_omegaHyp g, hc]
    have hmem : g * x * g⁻¹ ∈ conjSub g M := conj_mem_conjSub hx
    rwa [hcM] at hmem
  have hQN : Q ≤ N := by
    intro q hq
    have hqC : q ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      rw [h.centralizer_zGroup_eq_pCore]
      exact hq
    exact mem_normalizer_iff_conjSub_eq.mpr (deqi_conjSub_eq_of_centralizes hH.1 hqC)
  have hNeq : N = M ⊔ Q := h.normalizer_hyp_eq_sup hH
  haveI hKn : (M.subgroupOf N).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hMnorm g.1 g.2 x hx
    simpa using this⟩
  set K : Subgroup N := M.subgroupOf N with hKdef
  let f : ↥Q →* N ⧸ K := (QuotientGroup.mk' K).comp (Subgroup.inclusion hQN)
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    have hn : (n : G) ∈ M ⊔ Q := by
      rw [← hNeq]
      exact n.2
    obtain ⟨m, hm, q, hq, hmq⟩ := Subgroup.mem_sup_of_normal_right.mp hn
    have hqN : q⁻¹ ∈ N := hQN (Subgroup.inv_mem _ hq)
    refine ⟨⟨q, hq⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, hKdef, Subgroup.mem_subgroupOf]
    show (q⁻¹ * (n : G)) ∈ M
    have := hMnorm q⁻¹ hqN m hm
    rw [← hmq]
    simpa [mul_assoc] using this
  have hker : f.ker = (M ⊓ Q).subgroupOf Q := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp
  have hcard : Nat.card (N ⧸ K) = 2 := by
    have e := QuotientGroup.quotientKerEquivOfSurjective f hf_surj
    rw [← Nat.card_congr e.toEquiv, hker]
    have hrel := h.inf_pCore_relIndex hH
    rw [Subgroup.relIndex] at hrel
    exact hrel
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (N ⧸ K) := isCyclic_of_prime_card hcard
  let e : (N ⧸ K) ≃* Multiplicative (ZMod 2) :=
    (zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_, ?_⟩
  · ext x
    simp [MonoidHom.mem_ker, e, QuotientGroup.eq_one_iff]
  · exact e.surjective.comp (QuotientGroup.mk'_surjective K)

private theorem deqi_F_q8 {L : Subgroup G} (hL : L ∈ Ω) {z : G} (hz : IsUniqueInvolution L z) :
    ∃ i j : G, Q8Data L z i j := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hz (h.isQuatSub_of_mem hL) (h.card L hL)
  exact ⟨i, j, ⟨hz, hi, hj, hii, hjj, hji, hNF⟩⟩

private theorem deqi_F_mem_normalizer {H H' : Subgroup G} (hH : IsHyp Ω H) (hH' : IsHyp Ω H')
    {c : G} (hc : c ∈ (pSpan (omegaHyp Ω H)).normalCore) :
    c ∈ Subgroup.normalizer (H' : Set G) := by
  obtain ⟨g, hg⟩ := h.exists_conj_hyp hH hH'
  have hc' : ∀ b : G, b * c * b⁻¹ ∈ pSpan (omegaHyp Ω H) := hc
  have hgc : g⁻¹ * c * g ∈ pSpan (omegaHyp Ω H) := by
    have h1 := hc' g⁻¹
    rwa [inv_inv] at h1
  have hcM : c ∈ pSpan (omegaHyp Ω H') := by
    rw [← hg]
    exact deqi_F_conjSub_pSpan_le h.hyp.conjInvariant g H (mem_conjSub_iff.mpr hgc)
  exact h.pSpan_omegaHyp_le_normalizer hH' hcM

private theorem deqi_F_mem_centralizer {H : Subgroup G} (hH : IsHyp Ω H) {c : G}
    (hc : c ∈ (pSpan (omegaHyp Ω H)).normalCore) :
    c ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
  have key : ∀ d ∈ zGroup Ω, c * d * c⁻¹ = d := by
    intro d hd
    by_cases hd1 : d = 1
    · subst hd1
      simp
    obtain ⟨L, hL, hdL⟩ := (h.mem_zGroup_iff.mp hd).resolve_left hd1
    obtain ⟨i, j, hQ⟩ := h.deqi_F_q8 hL hdL
    have hy : c * d * c⁻¹ ∈ zGroup Ω := h.zGroup_normal.conj_mem d hd c
    by_contra hyd
    have hy1 : c * d * c⁻¹ ≠ 1 := by
      intro e
      apply hd1
      calc d = c⁻¹ * (c * d * c⁻¹) * c := by group
        _ = 1 := by rw [e]; group
    obtain ⟨k, hkL, hk⟩ : ∃ k ∈ L, dComm (c * d * c⁻¹) k ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : 1 * (c * d * c⁻¹)⁻¹ ∈ Subgroup.zpowers d :=
        h.eq_of_dComm_eq hL hdL hy (one_mem _) (fun k hk => by
          rw [hcon k hk]
          simp [dComm])
      rw [one_mul] at h1
      rcases deqi_F_eq_one_or_eq_of_mem_zpowers hdL.sq hdL.ne_one h1 with h2 | h2
      · exact hy1 (inv_eq_one.mp h2)
      · apply hyd
        calc c * d * c⁻¹ = ((c * d * c⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
          _ = d := by rw [h2]; exact inv_eq_of_mul_eq_one_right hdL.sq
    have hkz : k ∉ Subgroup.zpowers d := by
      intro hkd
      rcases deqi_F_eq_one_or_eq_of_mem_zpowers hdL.sq hdL.ne_one hkd with h2 | h2
      · exact hk (by rw [h2]; simp [dComm])
      · exact hk (by rw [h2]; exact dComm_eq_one_iff.mpr (h.zGroup_comm _ hy _ hd))
    have hH' : IsHyp Ω (zGroup Ω ⊓ Subgroup.centralizer ({k} : Set G)) :=
      ⟨inf_le_left, h.card_zGroup_inf_centralizer hL hdL hkL hkz⟩
    have hdH : d ∈ zGroup Ω ⊓ Subgroup.centralizer ({k} : Set G) :=
      Subgroup.mem_inf.mpr
        ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr (deqi_F_central_of_q8 hQ k hkL)⟩
    have hcN := h.deqi_F_mem_normalizer hH hH' hc
    have hyH : c * d * c⁻¹ ∈ zGroup Ω ⊓ Subgroup.centralizer ({k} : Set G) :=
      (Subgroup.mem_set_normalizer_iff.mp hcN d).mp hdH
    exact hk (dComm_eq_one_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyH).2))
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h1 := key d hd
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

private theorem deqi_F_absurd_of_mem_core {H : Subgroup G} (hH : IsHyp Ω H) {u : G}
    (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (huC : u ∈ (pSpan (omegaHyp Ω H)).normalCore) :
    False := by
  obtain ⟨L', hL', huL⟩ := (h.mem_zGroup_iff.mp hu).resolve_left hu1
  have hc' : ∀ b : G, b * u * b⁻¹ ∈ pSpan (omegaHyp Ω H) := huC
  have hsub : zGroup Ω ≤ H := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact H.one_mem
    · obtain ⟨L, hL, hxL⟩ := (h.mem_zGroup_iff.mp hx).resolve_left hx1
      obtain ⟨g, hg⟩ := h.exists_conj_involution hL' hL huL hxL
      have hxM : x ∈ pSpan (omegaHyp Ω H) := by
        rw [← hg]
        exact hc' g
      have hxI : x ∈ pSpan (omegaHyp Ω H) ⊓ zGroup Ω := Subgroup.mem_inf.mpr ⟨hxM, hx⟩
      rw [h.inf_zGroup_eq hH] at hxI
      exact hxI
  have hcard := Subgroup.card_le_of_le hsub
  rw [h.card_zGroup] at hcard
  obtain ⟨-, hH4⟩ := hH
  rw [hH4] at hcard
  omega

theorem core_MH_eq_bot {H : Subgroup G} (hH : IsHyp Ω H) :
    (pSpan (omegaHyp Ω H)).normalCore = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  by_contra hne
  have hcC : c ∈ Subgroup.centralizer (zGroup Ω : Set G) := h.deqi_F_mem_centralizer hH hc
  rw [h.centralizer_zGroup_eq_pCore] at hcC
  by_cases hcD : c ∈ zGroup Ω
  · exact h.deqi_F_absurd_of_mem_core hH hcD hne hc
  · have hflip : ∃ L ∈ Ω, flipVal L c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hcD (h.mem_zGroup_of_flipVal_eq_zero hcC hcon)
    obtain ⟨L, hL, hL0⟩ := hflip
    have hL1 : flipVal L c = 1 := by
      have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact key _ hL0
    obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hL
    obtain ⟨i, j, hQ⟩ := h.deqi_F_q8 hL hu
    have hnorm := h.norm_identity hL hQ hcC
    rw [if_pos hL1] at hnorm
    have hA : i * c * i⁻¹ ∈ (pSpan (omegaHyp Ω H)).normalCore :=
      (pSpan (omegaHyp Ω H)).normalCore_normal.conj_mem c hc i
    have hB : j * c * j⁻¹ ∈ (pSpan (omegaHyp Ω H)).normalCore :=
      (pSpan (omegaHyp Ω H)).normalCore_normal.conj_mem c hc j
    have hC : i * j * c * (i * j)⁻¹ ∈ (pSpan (omegaHyp Ω H)).normalCore :=
      (pSpan (omegaHyp Ω H)).normalCore_normal.conj_mem c hc (i * j)
    have huC : u ∈ (pSpan (omegaHyp Ω H)).normalCore := by
      rw [← hnorm]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hA) hB) hC
    have huD : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨L, hL, hu⟩)
    exact h.deqi_F_absurd_of_mem_core hH huD hu.ne_one huC

structure WrData (C : Coords Ω) where
  ψ : G →* AE.Wr 7
  inj : Function.Injective ψ
  range_eq : ψ.range = AE.aeSubOver AE.l32
  perm_eq : ∀ g : G, (ψ g).perm = C.σ g
  vec_zero : ∀ H : Subgroup G, IsHyp Ω H → ∀ g ∈ pSpan (omegaHyp Ω H),
    (ψ g).vec (C.lab H) = 0

private theorem deqi_G_card_G : Nat.card G = 168 * 64 := by
  have hidx := Subgroup.index_mul_card (Subgroup.centralizer (zGroup Ω : Set G))
  rw [h.index_centralizer_zGroup, h.centralizer_zGroup_eq_pCore, h.card_pCore_eq] at hidx
  exact hidx.symm

theorem exists_wrData (C : Coords Ω) : Nonempty (WrData C) := by
  obtain ⟨H₀, hH₀, -⟩ := C.lab_surj 0
  choose Hf hHf using C.lab_surj
  choose gf hgf using fun i : Fin 7 => h.exists_conj_hyp hH₀ (hHf i).1
  have hM : pSpan (omegaHyp Ω H₀) ≤ Subgroup.normalizer (H₀ : Set G) :=
    h.pSpan_omegaHyp_le_normalizer hH₀
  have hconj : ∀ a : G, IsHyp Ω (conjSub a H₀) := fun a => h.isHyp_conjSub hH₀ a
  obtain ⟨χ, hker, hsurj⟩ := h.exists_chi hH₀
  obtain ⟨s, hs⟩ := hsurj (Multiplicative.ofAdd 1)
  have hχs : χ s ≠ 1 := by
    rw [hs]
    exact deqi_G_ofAdd_one_ne_one
  have hB : ∀ (g : G) (x : G ⧸ pSpan (omegaHyp Ω H₀)),
      deqi_G_block C.lab H₀ hM (g • x) = C.σ g (deqi_G_block C.lab H₀ hM x) :=
    fun g x => deqi_G_block_smul hM (fun g H hH => C.lab_conj g H hH) hconj g x
  have hfib : ∀ i : Fin 7, Nat.card {x : G ⧸ pSpan (omegaHyp Ω H₀) //
      deqi_G_block C.lab H₀ hM x = i} = 2 := fun i =>
    deqi_G_fibre_card hM C.lab_inj hconj hker hχs (hgf i) (hHf i).1 i (hHf i).2
  have hp : ∀ i : Fin 7, deqi_G_block C.lab H₀ hM (QuotientGroup.mk (gf i)) = i := fun i => by
    show C.lab (conjSub (gf i) H₀) = i
    rw [hgf i, (hHf i).2]
  obtain ⟨ψ, hinj, hperm, hvec⟩ := exists_wr_hom_of_blocks C.σ (deqi_G_block C.lab H₀ hM) hB
    hfib (fun i => (QuotientGroup.mk (gf i) : G ⧸ pSpan (omegaHyp Ω H₀))) hp
    (deqi_G_faithful (h.core_MH_eq_bot hH₀))
  have hrange : ψ.range = AE.aeSubOver AE.l32 :=
    deqi_G_range_eq_aeSubOver hperm C.σ_mem hinj h.commutator_eq_top h.deqi_G_card_G
  refine ⟨⟨ψ, hinj, hrange, hperm, ?_⟩⟩
  intro H hH g hg
  have hgN : g ∈ Subgroup.normalizer (H : Set G) := h.pSpan_omegaHyp_le_normalizer hH hg
  have hfix : conjSub g H = H := mem_normalizer_iff_conjSub_eq.mp hgN
  have hσ : (C.σ g).symm (C.lab H) = C.lab H := by
    rw [Equiv.symm_apply_eq, ← C.lab_conj g H hH, hfix]
  have hHf' : Hf (C.lab H) = H := C.lab_inj _ _ (hHf _).1 hH (hHf _).2
  have hgfH : conjSub (gf (C.lab H)) H₀ = H := (hgf _).trans hHf'
  rw [hvec g (C.lab H), hσ]
  exact deqi_G_mem_fix_base h.hyp.conjInvariant hgfH hg

omit h in
theorem deqi_C_wsum_eq_zero (C : Coords Ω) (W : WrData C) (g : G) :
    AE.Wr.wsum (W.ψ g) = 0 := by
  have hmem : W.ψ g ∈ AE.aeSubOver AE.l32 := by
    rw [← W.range_eq]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  exact (AE.mem_aeSub.mp (Subgroup.mem_inf.mp hmem).1).1

theorem deqi_C_mkQ_comp_injective (C : Coords Ω) (W : WrData C) :
    Function.Injective ((AE.mkQ 7).comp W.ψ) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg => ?_
  have hg' : AE.mkQ 7 (W.ψ g) = AE.mkQ 7 1 := by
    rw [map_one]
    exact hg
  rcases AE.mkQ_eq_iff.mp hg' with h1 | h1
  · rw [mul_one, inv_eq_one] at h1
    exact W.inj (h1.trans (map_one W.ψ).symm)
  · exfalso
    have h2 : (W.ψ g)⁻¹ = AE.Wr.allOnes 7 := by
      rw [mul_one] at h1
      exact h1
    have h3 : AE.Wr.wsum (W.ψ g)⁻¹ = AE.Wr.wsum (W.ψ g) := AE.wsum_inv _
    rw [h2, deqi_C_wsum_allOnes, deqi_C_wsum_eq_zero C W g] at h3
    exact absurd h3 (by decide)

omit h in
theorem deqi_C_exists_hyp (C : Coords Ω) {u : G} {ℓ : Finset (Fin 7)}
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ)) (i : Fin 7) :
    ∃ H : Subgroup G, IsHyp Ω H ∧ C.lab H = i ∧ (u ∈ H ↔ i ∈ ℓ) := by
  obtain ⟨H, hH, hlab⟩ := C.lab_surj i
  exact ⟨H, hH, hlab, by rw [hline H hH, hlab]⟩

omit h in
theorem deqi_C_sigma_fix (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : C.σ g (C.lab H) = C.lab H := by
  have h1 := C.lab_conj g H hH
  rw [mem_normalizer_iff_conjSub_eq.mp hg] at h1
  exact h1.symm

theorem deqi_C_mem_normalizer_of_sigma_fix (C : Coords Ω) {H : Subgroup G} (hH : IsHyp Ω H)
    {g : G} (hg : C.σ g (C.lab H) = C.lab H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hc : IsHyp Ω (conjSub g H) := h.isHyp_conjSub hH g
  have h1 : C.lab (conjSub g H) = C.lab H := by rw [C.lab_conj g H hH, hg]
  exact mem_normalizer_iff_conjSub_eq.mpr (C.lab_inj _ _ hc hH h1)

theorem deqi_C_sigma_eq_one {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    (C : Coords Ω) {g : G} (hg : g ∈ Subgroup.zpowers u) : C.σ g = 1 := by
  ext i
  obtain ⟨H, hH, hlab⟩ := C.lab_surj i
  have hN : g ∈ Subgroup.normalizer (H : Set G) := by
    by_cases huH : u ∈ H
    · exact h.le_normalizer_hyp_of_mem hK hu hH huH (Subgroup.zpowers_le.mpr hu.mem hg)
    · have hgK : g ∈ K ⊓ Subgroup.normalizer (H : Set G) := by
        rw [h.inf_normalizer_hyp_of_not_mem hK hu hH huH]
        exact hg
      exact (Subgroup.mem_inf.mp hgK).2
  rw [← hlab, Equiv.Perm.one_apply, deqi_C_sigma_fix C hH hN]

theorem deqi_C_mem_zpowers_of_fix {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) (C : Coords Ω) {ℓ : Finset (Fin 7)}
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ)) {g : G} (hg : g ∈ K)
    {i : Fin 7} (hi : i ∉ ℓ) (hfix : C.σ g i = i) : g ∈ Subgroup.zpowers u := by
  obtain ⟨H, hH, hlab, hiff⟩ := deqi_C_exists_hyp C hline i
  have huH : u ∉ H := fun h1 => hi (hiff.mp h1)
  have hN : g ∈ Subgroup.normalizer (H : Set G) :=
    h.deqi_C_mem_normalizer_of_sigma_fix C hH (by rw [hlab]; exact hfix)
  rw [← h.inf_normalizer_hyp_of_not_mem hK hu hH huH]
  exact Subgroup.mem_inf.mpr ⟨hg, hN⟩

theorem deqi_C_sigma_fix_of_mem_line {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) (C : Coords Ω) {ℓ : Finset (Fin 7)}
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ)) {g : G} (hg : g ∈ K)
    {i : Fin 7} (hi : i ∈ ℓ) : C.σ g i = i := by
  obtain ⟨H, hH, hlab, hiff⟩ := deqi_C_exists_hyp C hline i
  have huH : u ∈ H := hiff.mpr hi
  rw [← hlab]
  exact deqi_C_sigma_fix C hH (h.le_normalizer_hyp_of_mem hK hu hH huH hg)

theorem deqi_C_vec_eq_zero_of_mem_line {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) (C : Coords Ω) {ℓ : Finset (Fin 7)} (W : WrData C)
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ)) {g : G} (hg : g ∈ K)
    {i : Fin 7} (hi : i ∈ ℓ) : (W.ψ g).vec i = 0 := by
  obtain ⟨H, hH, hlab, hiff⟩ := deqi_C_exists_hyp C hline i
  have hK' : K ≤ pSpan (omegaHyp Ω H) := le_pSpan ⟨hK, u, hiff.mpr hi, hu⟩
  have h0 := W.vec_zero H hH g (hK' hg)
  rw [hlab] at h0
  exact h0

theorem deqi_C_exists_not_comm {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  obtain ⟨i, j, hi, hj, -, -, hcomm, -⟩ := exists_q8_gen hu (h.isQuatSub_of_mem hK) (h.card K hK)
  refine ⟨i, hi, j, hj, fun hc => hu.ne_one ?_⟩
  have h1 : u * (i * j) = i * j := by rw [← hcomm, ← hc]
  exact mul_right_cancel (h1.trans (one_mul _).symm)

theorem deqi_C_sigma_embed {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    (C : Coords Ω) {ℓ : Finset (Fin 7)}
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ))
    (ι : Fin 4 ↪ Fin 7) (hι : Set.range ι = ((ℓᶜ : Finset (Fin 7)) : Set (Fin 7))) {g : G}
    (hg : g ∈ K) :
    ∃ d : Equiv.Perm (Fin 4), (d = 1 ∨ d = AE.d₁ ∨ d = AE.d₂ ∨ d = AE.d₃) ∧
      C.σ g = AE.embedPerm ι d := by
  by_cases hex : ∃ i ∈ ℓᶜ, C.σ g i = i
  · obtain ⟨i, hi, hfix⟩ := hex
    have hz := h.deqi_C_mem_zpowers_of_fix hK hu C hline hg (Finset.mem_compl.mp hi) hfix
    exact ⟨1, Or.inl rfl, by rw [AE.embedPerm_one, h.deqi_C_sigma_eq_one hK hu C hz]⟩
  push Not at hex
  have hmemα : ∀ i, ι i ∈ ℓᶜ := fun i => by
    have h1 : ι i ∈ Set.range ι := Set.mem_range_self i
    rw [hι] at h1
    exact Finset.mem_coe.mp h1
  have hfixout : ∀ x, x ∉ Set.range ι → C.σ g x = x := by
    intro x hx
    rw [hι] at hx
    have hxℓ : x ∈ ℓ := by
      by_contra hcon
      exact hx (Finset.mem_coe.mpr (Finset.mem_compl.mpr hcon))
    exact h.deqi_C_sigma_fix_of_mem_line hK hu C hline hg hxℓ
  obtain ⟨d, hdσ, hd⟩ := deqi_C_exists_embedPerm hfixout
  have hsq : C.σ g * C.σ g = 1 := by
    rw [← map_mul]
    apply h.deqi_C_sigma_eq_one hK hu C
    rcases mul_self_eq_one_or_eq_of_q8 hu (h.card K hK) (h.deqi_C_exists_not_comm hK hu) hg
      with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers u
  have hdd : ∀ i, d (d i) = i := by
    intro i
    apply ι.injective
    have h1 : C.σ g (C.σ g (ι i)) = ι i := by
      have h2 := congrArg (fun π : Equiv.Perm (Fin 7) => π (ι i)) hsq
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h2
    rw [← hd (d i), ← hd i]
    exact h1
  have hfpf : ∀ i, d i ≠ i := by
    intro i hdi
    apply hex (ι i) (hmemα i)
    rw [hd i, hdi]
  exact ⟨d, Or.inr (deqi_C_perm_fin4 d hdd hfpf), hdσ⟩

theorem deqi_C_mem_sup {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    (C : Coords Ω) {ℓ : Finset (Fin 7)} (W : WrData C)
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ)) (hα : ℓᶜ.card = 4) {g : G}
    (hg : g ∈ K) : W.ψ g ∈ AE.memAt ℓᶜ hα true ⊔ AE.memAt ℓᶜ hα false := by
  obtain ⟨d, hd, hσ⟩ :=
    h.deqi_C_sigma_embed hK hu C hline (AE.emb ℓᶜ hα) (AE.range_emb ℓᶜ hα) hg
  refine deqi_C_mem_sup_of_perm hα (fun x hx => ?_) (deqi_C_wsum_eq_zero C W g) ⟨d, hd, ?_⟩
  · exact h.deqi_C_vec_eq_zero_of_mem_line hK hu C W hline hg (by simpa using hx)
  · rw [W.perm_eq g, hσ]

theorem deqi_C_map_le {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    (C : Coords Ω) {ℓ : Finset (Fin 7)} (W : WrData C)
    (hline : ∀ H : Subgroup G, IsHyp Ω H → (u ∈ H ↔ C.lab H ∈ ℓ)) (hα : ℓᶜ.card = 4) :
    K.map ((AE.mkQ 7).comp W.ψ) ≤ AE.memBar ℓᶜ hα true ⊔ AE.memBar ℓᶜ hα false := by
  rintro _ ⟨g, hg, rfl⟩
  have hmem := Subgroup.mem_map_of_mem (AE.mkQ 7) (h.deqi_C_mem_sup hK hu C W hline hα hg)
  rw [Subgroup.map_sup] at hmem
  exact hmem

theorem exists_label (C : Coords Ω) (W : WrData C) :
    ∃ K ∈ Ω, ∃ α ∈ AE.e64Sets, ∃ (hα : α.card = 4) (b : Bool),
      K.map ((AE.mkQ 7).comp W.ψ) = AE.memBar α hα b := by
  obtain ⟨K, hK, -⟩ := h.exists_ne
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  obtain ⟨ℓ, hℓ, hline⟩ :=
    C.line u (h.mem_zGroup_iff.mpr (Or.inr ⟨K, hK, hu⟩)) hu.ne_one
  have hα : ℓᶜ.card = 4 := AE.fanoLines_compl_card ℓ hℓ
  have hφ := deqi_C_mkQ_comp_injective h C W
  have hcard : Nat.card (K.map ((AE.mkQ 7).comp W.ψ)) = 8 := by
    rw [Subgroup.card_map_of_injective hφ, h.card K hK]
  have hw : IsUniqueInvolution (K.map ((AE.mkQ 7).comp W.ψ)) ((AE.mkQ 7).comp W.ψ u) :=
    { mem := Subgroup.mem_map_of_mem _ hu.mem
      ne_one := fun h1 => hu.ne_one (hφ (h1.trans (map_one ((AE.mkQ 7).comp W.ψ)).symm))
      sq := by rw [← map_mul, hu.sq, map_one]
      unique := by
        rintro y ⟨g, hg, rfl⟩ hy
        have hgg : g * g = 1 := hφ (by rw [map_one, map_mul]; exact hy)
        rcases hu.unique g hg hgg with rfl | rfl
        · exact Or.inl (map_one _)
        · exact Or.inr rfl }
  have hmap := h.deqi_C_map_le hK hu C W hline hα
  rcases eq_memBar_of_le_sup_memBar (by norm_num) hmap hcard hw with heq | heq
  · exact ⟨K, hK, ℓᶜ, ⟨ℓ, hℓ, rfl⟩, hα, true, heq⟩
  · exact ⟨K, hK, ℓᶜ, ⟨ℓ, hℓ, rfl⟩, hα, false, heq⟩

theorem nonempty_aeIdentOn_e64 : Nonempty (AEIdentOn Ω 7 AE.e64Sets AE.e64Sub) := by
  obtain ⟨C⟩ := h.exists_coords
  obtain ⟨W⟩ := h.exists_wrData C
  obtain ⟨K, hK, α, hαS, hα, b, hKφ⟩ := h.exists_label C W
  have hwsum : ∀ g : G, AE.Wr.wsum (W.ψ g) = 0 := fun g => by
    have hmem : W.ψ g ∈ AE.aeSubOver AE.l32 := by
      rw [← W.range_eq]
      exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
    exact (AE.mem_aeSub.mp (Subgroup.mem_inf.mp hmem).1).1
  have hinj : Function.Injective ((AE.mkQ 7).comp W.ψ) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [MonoidHom.comp_apply] at hg
    rcases AE.mkQ_eq_iff.mp (hg.trans (map_one (AE.mkQ 7)).symm) with h1 | h1
    · have h2 : W.ψ g = 1 := inv_eq_one.mp (by simpa using h1)
      exact W.inj (h2.trans (map_one W.ψ).symm)
    · exfalso
      have h3 : (W.ψ g)⁻¹ = AE.Wr.allOnes 7 := by simpa using h1
      have h4 : W.ψ g = AE.Wr.allOnes 7 := by
        rw [← inv_inv (W.ψ g), h3]
        exact inv_eq_of_mul_eq_one_right (AE.allOnes_mul_self 7)
      have hw := hwsum g
      rw [h4] at hw
      exact absurd hw (by decide)
  have hrange : ((AE.mkQ 7).comp W.ψ).range = AE.e64Sub := by
    rw [MonoidHom.range_comp, W.range_eq]
    rfl
  exact nonempty_aeIdentOn_e64_of_hom h.hyp.conjInvariant h.trans h.gen _ hinj hrange hK hαS hα
    hKφ

end DE2Hyp

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem aeIdentOn_e64_of_zGroup_eq (h9 : Perp9 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hDE : zGroup Ω = eGroup Ω K) (hV : (twinSet Ω K).ncard = 2) :
    Nonempty (AEIdentOn Ω 7 AE.e64Sets AE.e64Sub) := by
  have hD : DEHyp Ω := h.dEHyp_of_zGroup_eq h9 hK hDE
  exact DE2Hyp.nonempty_aeIdentOn_e64
    (show DE2Hyp Ω from ⟨hD, fun L hL => (hD.twinSet_ncard_eq hL hK).trans hV⟩)

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
