module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitAct

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

variable {G : Type} [Group G] {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) {ρ : G}
  (hρ : ρ = x₀ ∨ ρ = t * x₀)
include hS hρ

omit hρ in
theorem x₀_commute_t : x₀ * t = t * x₀ := hS.commute_of_mem_K (mem_sup_right (mem_zpowers x₀))

theorem rho_sq : ρ * ρ = 1 := by
  rcases hρ with rfl | rfl
  · exact hS.inputs.outer.sq
  · calc t * x₀ * (t * x₀) = t * (x₀ * t) * x₀ := by group
      _ = t * t * (x₀ * x₀) := by rw [hS.x₀_commute_t]; group
      _ = 1 := by rw [hS.shape.mul_self, hS.inputs.outer.sq, one_mul]

theorem rho_normalizes_U : ∀ y ∈ U, ρ * y * ρ⁻¹ ∈ U := by
  intro y hy
  rcases hρ with rfl | rfl
  · exact hS.inputs.outer.normalizes_U y hy
  · have h1 := hS.inputs.outer.normalizes_U y hy
    have hc : (x₀ * y * x₀⁻¹) * t = t * (x₀ * y * x₀⁻¹) :=
      hS.shape.commute_of_mem (hS.rad.U_le_L h1)
    rw [show t * x₀ * y * (t * x₀)⁻¹ = t * (x₀ * y * x₀⁻¹) * t⁻¹ by group, ← hc,
      mul_inv_cancel_right]
    exact h1

theorem zpow_rho (n : ℤ) : ρ ^ n = 1 ∨ ρ ^ n = ρ := by
  have h2 := hS.rho_sq hρ
  have hinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right h2
  induction n using Int.induction_on with
  | zero => exact Or.inl (zpow_zero ρ)
  | succ n ih =>
    rw [_root_.zpow_add_one]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr (one_mul ρ)
    · exact Or.inl h2
  | pred n ih =>
    rw [_root_.zpow_sub_one, hinv]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr (one_mul ρ)
    · exact Or.inl h2

theorem mem_Urho_iff {x : G} : x ∈ U ⊔ zpowers ρ ↔ ∃ y ∈ U, x = y ∨ x = y * ρ := by
  constructor
  · intro hx
    obtain ⟨y, hy, n, rfl⟩ := (Stage0.mem_sup_zpowers_iff (Stage0.mem_normalizer_of_mul_self
      (hS.rho_sq hρ) (hS.rho_normalizes_U hρ))).1 hx
    rcases hS.zpow_rho hρ n with h | h <;> rw [h]
    · exact ⟨y, hy, Or.inl (mul_one y)⟩
    · exact ⟨y, hy, Or.inr rfl⟩
  · rintro ⟨y, hy, rfl | rfl⟩
    · exact mem_sup_left hy
    · exact mul_mem (mem_sup_left hy) (mem_sup_right (mem_zpowers ρ))

theorem rho_mem_TH : ρ ∈ U ⊔ zpowers x₀ ⊔ zpowers t := by
  rcases hρ with rfl | rfl
  · exact mem_sup_left (mem_sup_right (mem_zpowers _))
  · exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem Urho_le_TH : U ⊔ zpowers ρ ≤ U ⊔ zpowers x₀ ⊔ zpowers t :=
  sup_le (le_sup_left.trans le_sup_left) (zpowers_le.2 (hS.rho_mem_TH hρ))

theorem t_not_mem_Urho : t ∉ U ⊔ zpowers ρ := by
  intro ht
  obtain ⟨y, hy, h | h⟩ := (hS.mem_Urho_iff hρ).1 ht
  · exact hS.shape.not_mem (h ▸ hS.rad.U_le_L hy)
  · rcases hρ with rfl | rfl
    · exact hS.t_not_mem_H₀ (h ▸ mul_mem (hS.L_le_H₀ (hS.rad.U_le_L hy))
        (hS.K_le_H₀ (mem_sup_right (mem_zpowers _))))
    · have hyt := hS.shape.commute_of_mem (hS.rad.U_le_L hy)
      have : y * x₀ = 1 := by
        have e : t * (y * x₀) = t := by
          calc t * (y * x₀) = y * t * x₀ := by rw [← mul_assoc, hyt]
            _ = t := by rw [mul_assoc]; exact h.symm
        simpa using e
      apply hS.inputs.outer.not_mem
      rw [eq_inv_of_mul_eq_one_right this]
      exact inv_mem (hS.rad.U_le_L hy)

end CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX

namespace CFSG.EvenSmallLie.OmegaEight.Chain.Config

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SplitIn

variable {G : Type} [Group G] {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {k : ℕ} {A : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) k A) {ρ : G} (hρ : ρ = x₀ ∨ ρ = t * x₀)
include hS hC hρ

theorem Urho_le_normalizerX [Finite G] : U ⊔ zpowers ρ ≤ normalizer (A : Set G) :=
  (hS.Urho_le_TH hρ).trans (hC.TH_le_normalizerX hS)

theorem t_not_mem_MX [Finite G] : t ∉ A ⊔ (U ⊔ zpowers ρ) := by
  intro ht
  obtain ⟨c, hc, y, hy, hcy⟩ :=
    exists_mul_of_mem_sup_normalizer (hC.Urho_le_normalizerX hS hρ) ht
  have hyt := hS.commute_of_mem_TH (hS.Urho_le_TH hρ hy)
  have hct : c * t = t * c := by
    have hc' : c = t * y⁻¹ := by rw [hcy]; group
    rw [hc', mul_assoc, (Commute.inv_left hyt), ← mul_assoc]
  have hcQ := (hC.commute_iffX hS hc).1 hct
  exact hS.t_not_mem_Urho hρ (hcy ▸ mul_mem (mem_sup_left (hS.rad.Q_le_U hcQ)) hy)

theorem relIndex_MX [Finite G] :
    (A ⊔ (U ⊔ zpowers ρ)).relIndex (A ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)) = 2 := by
  have htn := hC.t_not_mem_MX hS hρ
  have hρM : ρ ∈ A ⊔ (U ⊔ zpowers ρ) := mem_sup_right (mem_sup_right (mem_zpowers ρ))
  have hx₀t : x₀ * t = t * x₀ := hS.x₀_commute_t
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_sup_right (mem_zpowers t)), fun b hb => ?_⟩
  set M : Subgroup G := A ⊔ (U ⊔ zpowers ρ)
  have htM : t ∈ normalizer (M : Set G) := by
    refine mem_normalizer_sup hC.t_mem_normalizer (mem_normalizer_of_conj_mem fun y hy => ?_)
    rw [← hS.commute_of_mem_TH (hS.Urho_le_TH hρ hy), mul_inv_cancel_right]
    exact hy
  have hx₀M : x₀ ∈ M ⊔ zpowers t := by
    rcases hρ with rfl | rfl
    · exact mem_sup_left hρM
    · have : x₀ = t * (t * x₀) := by rw [← mul_assoc, hS.shape.mul_self, one_mul]
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hρM)
  have hle : A ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t) ≤ M ⊔ zpowers t :=
    sup_le (le_sup_left.trans le_sup_left) (sup_le (sup_le
      ((le_sup_left.trans le_sup_right).trans le_sup_left) (zpowers_le.2 hx₀M)) le_sup_right)
  obtain ⟨m, hm, n, hbm⟩ := (Stage0.mem_sup_zpowers_iff htM).1 (hle hb)
  rcases hS.shape.mem_zpowers_iff.1 (zpow_mem (mem_zpowers t) n) with h | h <;> rw [h] at hbm
  · rw [mul_one] at hbm
    exact Or.inr ⟨hbm ▸ hm, fun h' => htn (by simpa [hbm] using mul_mem (inv_mem hm) h')⟩
  · refine Or.inl ⟨by rw [hbm, mul_assoc, hS.shape.mul_self, mul_one]; exact hm, fun h' => htn ?_⟩
    have := mul_mem (inv_mem hm) h'
    rwa [hbm, inv_mul_cancel_left] at this

theorem exists_conj_decompX [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hT : Terminal t (P ⊔ zpowers x₀) k A) :
    ∃ g : G, Odd ((A ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)).relIndex (centralizer {g * t * g⁻¹})) ∧
      ∃ b ∈ A, ∃ h ∈ U ⊔ zpowers ρ, g * t * g⁻¹ = b * h ∧ h ∉ Q ∧ h * h ∈ Q := by
  let T : Sylow 2 G := ⟨A ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t), hC.isPGroup_TX hS,
    fun hV hle => hC.seitz_sylowX hS hT hV hle⟩
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact hS.shape.mul_self
  obtain ⟨g, hgM, hodd⟩ := CFSG.Monster.B.Recog.exists_conj_mem_odd_relIndex_of_transfer T
    (hC.relIndex_MX hS hρ) ht2 (fun K hK => mem_of_index_two hG hnab hK t)
  refine ⟨g, hodd, ?_⟩
  obtain ⟨b, hb, h, hh, hbh⟩ :=
    exists_mul_of_mem_sup_normalizer (hC.Urho_le_normalizerX hS hρ) hgM
  have hu2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.shape.mul_self]
    group
  have huA : g * t * g⁻¹ ∉ A := hC.conj_not_mem_AX hS g
  refine ⟨b, hb, h, hh, hbh, fun hq => huA (hbh ▸ mul_mem hb (hC.level.Q_le hq)), ?_⟩
  have e : h * h = (b * (h * b * h⁻¹))⁻¹ := by
    have h1 : b * h * (b * h) = 1 := hbh ▸ hu2
    calc h * h = (b * (h * b * h⁻¹))⁻¹ * (b * h * (b * h)) := by group
      _ = (b * (h * b * h⁻¹))⁻¹ := by rw [h1, mul_one]
  have hhA : h * b * h⁻¹ ∈ A :=
    (mem_normalizer_iff.1 (hC.Urho_le_normalizerX hS hρ hh) b).1 hb
  have hA' : h * h ∈ A := e ▸ inv_mem (mul_mem hb hhA)
  have hht := hS.commute_of_mem_TH (hS.Urho_le_TH hρ hh)
  have hC' : h * h * t = t * (h * h) := by rw [mul_assoc, hht, ← mul_assoc, hht, mul_assoc]
  exact (hC.commute_iffX hS hA').1 hC'

end CFSG.EvenSmallLie.OmegaEight.Chain.Config
