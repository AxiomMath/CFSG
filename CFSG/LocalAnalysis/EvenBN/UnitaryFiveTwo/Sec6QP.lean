module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Str
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6QG

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer L44Sylow
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (pstd sigmaSL msigma rootSL map_sigmaSL_rootSL
  map_sigmaSL_range_zero rootSL_le_pstd blockSL2_transvection_one_zero)
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open scoped MatrixGroups

section Roots

variable {G : Type} [Group G]

theorem transvection_fin2_eq_lowerSL (c : F4) :
    Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c = lowerSL c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, lowerSL, Matrix.one_apply,
      Matrix.single_apply]

theorem mem_rootSL_lower (k : Fin 3) {x : SL(4, F4)} (hx : x ∈ rootSL F4 k.succ k.castSucc) :
    ∃ a : F4, x = blockSL2 F4 3 k (lowerSL a) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, c, rfl⟩ := hx
    refine ⟨c, ?_⟩
    rw [← transvection_fin2_eq_lowerSL, blockSL2_transvection_one_zero F4 k one_ne_zero c]
  | one => exact ⟨0, by rw [lowerSL_zero, map_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [← lowerSL_mul, map_mul]⟩
  | inv x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rw [← map_inv, inv_eq_of_mul_eq_one_right (lowerSL_mul_self a)]⟩

theorem blockSL2_lowerSL_mem_rootSL (k : Fin 3) (a : F4) :
    blockSL2 F4 3 k (lowerSL a) ∈ rootSL F4 k.succ k.castSucc := by
  rw [← transvection_fin2_eq_lowerSL, blockSL2_transvection_one_zero F4 k one_ne_zero a]
  exact Subgroup.subset_closure ⟨_, a, rfl⟩

theorem lowerSL_ne_one {a : F4} (ha : a ≠ 0) : lowerSL a ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F4) => (A : Matrix (Fin 2) (Fin 2) F4) 1 0) h
  simp [lowerSL] at this
  exact ha this

theorem gam_lower_entries {φ : SL(4, F4) →* G} (hφ : Function.Injective φ) (k : Fin 3) {g : G}
    (hg : g ∈ (rootSL F4 k.succ k.castSucc).map φ) (hgΓ : g ∈ gam φ k) :
    (gamEquiv hφ k ⟨g, hgΓ⟩ : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (gamEquiv hφ k ⟨g, hgΓ⟩ : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧
      (gamEquiv hφ k ⟨g, hgΓ⟩ : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨a, rfl⟩ := mem_rootSL_lower k hx
  rw [gamEquiv_apply_mk hφ k (lowerSL a) hgΓ]
  simp [lowerSL]

theorem gam_lower_nontrivial {φ : SL(4, F4) →* G} (hφ : Function.Injective φ) (k : Fin 3) :
    ∃ (g : G) (hg : g ∈ (rootSL F4 k.succ k.castSucc).map φ) (hgΓ : g ∈ gam φ k),
      gamEquiv hφ k ⟨g, hgΓ⟩ ≠ 1 := by
  refine ⟨φ (blockSL2 F4 3 k (lowerSL 1)), ⟨_, blockSL2_lowerSL_mem_rootSL k 1, rfl⟩,
    mem_gam.2 ⟨_, rfl⟩, ?_⟩
  rw [gamEquiv_apply_mk hφ k (lowerSL 1)]
  exact lowerSL_ne_one one_ne_zero

theorem root_image_comm_sq {φ : SL(4, F4) →* G} (k : Fin 3) :
    (∀ a ∈ (rootSL F4 k.succ k.castSucc).map φ, ∀ b ∈ (rootSL F4 k.succ k.castSucc).map φ,
      a * b = b * a) ∧
      ∀ a ∈ (rootSL F4 k.succ k.castSucc).map φ, a * a = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := mem_rootSL_lower k hx
    obtain ⟨b, rfl⟩ := mem_rootSL_lower k hy
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, lowerSL_mul, lowerSL_mul]
    exact congrArg (fun z => φ (blockSL2 F4 3 k (lowerSL z))) (add_comm a b)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := mem_rootSL_lower k hx
    rw [← map_mul, ← map_mul, lowerSL_mul_self, map_one, map_one]

end Roots

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem exists_quad_pkg (h : d.Hyp) (hK : d.KLinear)
    (hD : d.D₁ ≤ normalizer (d.D₂ : Set G)) :
    ∃ U₁ U₂ : Subgroup G, U₁ ≤ d.M ⊔ d.Y ∧ U₂ ≤ d.M ⊔ d.Y ∧ d.M ⊔ d.Y ≤ U₁ ⊔ U₂ ⊔ d.Y ∧
      (∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) ∧ (∀ a ∈ U₁, a * a = 1) ∧
      (∀ a ∈ U₂, ∀ b ∈ U₂, a * b = b * a) ∧ (∀ a ∈ U₂, a * a = 1) ∧
      (∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a) ∧
      (∀ u ∈ U₁, ∀ x ∈ d.D₂, u * x * u⁻¹ * x⁻¹ ∈ d.V₃) ∧
      (∀ u ∈ U₂, ∀ x ∈ d.D₂, u * x * u⁻¹ * x⁻¹ ∈ d.V₃) ∧
      (∀ c ∈ d.V₃, ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂, ∃ x₁ ∈ d.D₂, ∃ x₂ ∈ d.D₂, ∃ y ∈ d.Y,
        c = (u₁ * x₁ * u₁⁻¹ * x₁⁻¹) * (u₂ * x₂ * u₂⁻¹ * x₂⁻¹) * y) := by
  have hK₁ := h.comm_M_V₂_mem_W_linear hK
  have hKY := h.M_le_normalizer_Y_linear hK
  obtain ⟨φ, hinj, hrange, hequiv, hpstd⟩ := h.exists_standard_position hK
  have hs : StdLin d φ := ⟨hinj, hrange, hequiv, hpstd⟩
  obtain ⟨A, y, hA01, hAA, hy, hv⟩ := hs.exists_weyl h hK
  obtain ⟨A', hA'⟩ : ∃ A' : SL(2, F4), blockSL2 F4 3 2 A' = sigmaSL F4 (blockSL2 F4 3 0 A) := by
    have : sigmaSL F4 (blockSL2 F4 3 0 A) ∈ (blockSL2 F4 3 2).range := by
      rw [← map_sigmaSL_range_zero F4]
      exact Subgroup.mem_map_of_mem (sigmaSL F4).toMonoidHom (MonoidHom.mem_range.2 ⟨A, rfl⟩)
    exact MonoidHom.mem_range.1 this
  set w₁ : G := φ (blockSL2 F4 3 0 A) with hw₁def
  set w₂ : G := φ (sigmaSL F4 (blockSL2 F4 3 0 A)) with hw₂def
  set y₀ : G := φ y with hy₀def
  have hy₀Y : y₀ ∈ d.Y := (hs.mem_YK_iff h).2 hy
  have hv' : d.v = y₀ * (w₁ * w₂) := hv
  set Γ₁ : Subgroup G := gam φ 0 with hΓ₁def
  set Γ₂ : Subgroup G := gam φ 2 with hΓ₂def
  set U₁ : Subgroup G := (rootSL F4 1 0).map φ with hU₁def
  set U₂ : Subgroup G := (rootSL F4 3 2).map φ with hU₂def
  have hw₁Γ : w₁ ∈ Γ₁ := mem_gam.2 ⟨A, rfl⟩
  have hw₂Γ : w₂ ∈ Γ₂ := mem_gam.2 ⟨A', by rw [hA']⟩
  have hw₁sq : w₁ * w₁ = 1 := by
    rw [hw₁def, ← map_mul, ← map_mul, hAA, map_one, map_one]
  have hw₂sq : w₂ * w₂ = 1 := by
    rw [hw₂def, ← map_mul, ← map_mul, ← map_mul, hAA, map_one, map_one, map_one]
  have hcomm : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨A₁, rfl⟩ := mem_gam.1 ha
    obtain ⟨B₂, rfl⟩ := mem_gam.1 hb
    rw [← map_mul, ← map_mul, blockSL2_comm]
  have hU₁Γ : U₁ ≤ Γ₁ := Subgroup.map_mono rootSL_le_range₀
  have hU₂Γ : U₂ ≤ Γ₂ := Subgroup.map_mono rootSL_le_range₂
  have hU₁MY : U₁ ≤ d.M ⊔ d.Y := by
    rw [← hs.pstd]
    exact Subgroup.map_mono (rootSL_le_pstd F4 (by decide))
  have hU₂MY : U₂ ≤ d.M ⊔ d.Y := by
    rw [← hs.pstd]
    exact Subgroup.map_mono (rootSL_le_pstd F4 (by decide))
  have hgen₁ : Γ₁ ≤ U₁ ⊔ U₁.map (MulAut.conj w₁).toMonoidHom := by
    have := Subgroup.map_mono (f := φ) (range₀_le_sup hA01)
    rw [Subgroup.map_sup, map_map_conj] at this
    exact this
  have hconjU : U₁.map (MulAut.conj d.t).toMonoidHom = U₂ := by
    rw [hU₁def, hs.map_conj_t h, map_sigmaSL_rootSL]
    rfl
  have hconjΓ : Γ₁.map (MulAut.conj d.t).toMonoidHom = Γ₂ := by
    rw [hΓ₁def, gam, hs.map_conj_t h, map_sigmaSL_range_zero]
    rfl
  have hgen₂ : Γ₂ ≤ U₂ ⊔ U₂.map (MulAut.conj w₂).toMonoidHom := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj d.t).toMonoidHom) hgen₁
    rw [Subgroup.map_sup, map_map_conj, hconjU, hconjΓ] at h1
    have hw : (MulAut.conj d.t).toMonoidHom w₁ = w₂ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hw₁def, hs.equiv]
    rw [hw] at h1
    exact h1
  have hΓ₁Y : Γ₁ ≤ normalizer (d.Y : Set G) := by
    intro g hg
    obtain ⟨B, rfl⟩ := mem_gam.1 hg
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ YK, φ x' = x := by
      rw [hs.Y_eq h] at hx
      exact hx
    have e : φ (blockSL2 F4 3 0 B) * φ x' * (φ (blockSL2 F4 3 0 B))⁻¹ =
        φ (blockSL2 F4 3 0 B * x' * (blockSL2 F4 3 0 B)⁻¹) := by simp
    rw [e]
    exact (hs.mem_YK_iff h).2 (blockSL2_conj_YK₀ B hx')
  have hΓ₂Y : Γ₂ ≤ normalizer (d.Y : Set G) := by
    intro g hg
    obtain ⟨B, rfl⟩ := mem_gam.1 hg
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ YK, φ x' = x := by
      rw [hs.Y_eq h] at hx
      exact hx
    have e : φ (blockSL2 F4 3 2 B) * φ x' * (φ (blockSL2 F4 3 2 B))⁻¹ =
        φ (blockSL2 F4 3 2 B * x' * (blockSL2 F4 3 2 B)⁻¹) := by simp
    rw [e]
    exact (hs.mem_YK_iff h).2 (blockSL2_conj_YK₂ B hx')
  set N : Subgroup G := normalizer (d.D₂ : Set G) with hNdef
  have hMY_N : d.M ⊔ d.Y ≤ N := (h.MY_le_normDY_lin hKY hD).trans inf_le_left
  have hvN : d.v ∈ N := h.v_mem_normalizer_D₂
  have hv₁N : w₁ * w₂ ∈ N := by
    have : w₁ * w₂ = y₀⁻¹ * d.v := by rw [hv']; group
    rw [this]
    exact N.mul_mem (N.inv_mem (d.D₂.le_normalizer (h.Y_le_D₂ hy₀Y))) hvN
  have hconj₁ : ∀ u ∈ U₁, w₁ * u * w₁⁻¹ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by
    intro u hu
    have hu' : w₁⁻¹ * u * w₁ ∈ Γ₁ :=
      Γ₁.mul_mem (Γ₁.mul_mem (Γ₁.inv_mem hw₁Γ) (hU₁Γ hu)) hw₁Γ
    have hc := hcomm _ hu' _ hw₂Γ
    have hinv₁ : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right hw₁sq
    calc w₁ * u * w₁⁻¹ = w₁⁻¹ * u * w₁ := by rw [hinv₁]
      _ = w₂⁻¹ * (w₁⁻¹ * u * w₁ * w₂) := by rw [hc]; group
      _ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by group
  have hconj₂ : ∀ u ∈ U₂, w₂ * u * w₂⁻¹ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by
    intro u hu
    have hc : w₁ * u = u * w₁ := hcomm _ hw₁Γ _ (hU₂Γ hu)
    have hinv₂ : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hw₂sq
    calc w₂ * u * w₂⁻¹ = w₂⁻¹ * u * w₂ := by rw [hinv₂]
      _ = w₂⁻¹ * (w₁⁻¹ * u * w₁) * w₂ := by
        rw [show w₁⁻¹ * u * w₁ = u by rw [mul_assoc, ← hc]; group]
      _ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by group
  have hΓ₁N : Γ₁ ≤ N := le_of_gen_conj (hU₁MY.trans hMY_N) hv₁N hgen₁ hconj₁
  have hΓ₂N : Γ₂ ≤ N := le_of_gen_conj (hU₂MY.trans hMY_N) hv₁N hgen₂ hconj₂
  have hΓ₁' : Γ₁ ≤ ModSplit.normDY d.D₂ d.Y := le_inf hΓ₁N hΓ₁Y
  have hΓ₂' : Γ₂ ≤ ModSplit.normDY d.D₂ d.Y := le_inf hΓ₂N hΓ₂Y
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY2 : IsPGroup 2 ↥(d.M ⊔ d.Y) := IsPGroup.of_card (n := 12) (h.card_M_sup_Y hK)
  have hp₁ : IsPGroup 2 ↥U₁ := hMY2.to_le hU₁MY
  have hp₂ : IsPGroup 2 ↥U₂ := hMY2.to_le hU₂MY
  have hfix : ∀ x ∈ d.D₂, (∀ g ∈ Γ₁, g * x * g⁻¹ * x⁻¹ ∈ d.Y) →
      (∀ g ∈ Γ₂, g * x * g⁻¹ * x⁻¹ ∈ d.Y) → x ∈ d.Y := by
    intro x hx h₁ h₂
    refine h.fixed_D₂_Y hx (fun k hk => ?_)
    have hΓ₁C : Γ₁ ≤ centModSub d.Y x := fun g hg => ⟨hΓ₁Y hg, h₁ g hg⟩
    have hΓ₂C : Γ₂ ≤ centModSub d.Y x := fun g hg => ⟨hΓ₂Y hg, h₂ g hg⟩
    have hYC : d.Y ≤ centModSub d.Y x := fun z hz => by
      refine ⟨d.Y.le_normalizer hz, ?_⟩
      have hc : x * z = z * x := Data.Hyp.D₂_comm_Y' hx hz
      have : z * x * z⁻¹ * x⁻¹ = 1 := by
        rw [← hc]
        group
      rw [this]
      exact d.Y.one_mem
    have hMYC : d.M ⊔ d.Y ≤ centModSub d.Y x := by
      intro z hz
      obtain ⟨u₁, hu₁, u₂, hu₂, y', hy', rfl⟩ := hs.mem_MY_decomp hz
      exact mul_mem (mul_mem (hΓ₁C (hU₁Γ ⟨u₁, hu₁, rfl⟩)) (hΓ₂C (hU₂Γ ⟨u₂, hu₂, rfl⟩)))
        (hYC ((hs.mem_YK_iff h).2 hy'))
    have hvC : d.v ∈ centModSub d.Y x := by
      rw [hv']
      exact mul_mem (hYC hy₀Y) (mul_mem (hΓ₁C hw₁Γ) (hΓ₂C hw₂Γ))
    have hK₂C : d.K₂ ≤ centModSub d.Y x := by
      rw [Data.K₂_eq_sup_conj]
      refine sup_le (fun z hz => hMYC (mem_sup_left (StdLin.X₂_le_M' h hz))) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem hvC (hMYC (mem_sup_left (StdLin.X₂_le_M' h hz)))) (inv_mem hvC)
    have hkC := (hK₂C hk).2
    have e : x⁻¹ * (k * x * k⁻¹) = x⁻¹ * (k * x * k⁻¹ * x⁻¹) * x := by group
    rw [e]
    have hcc : x * (k * x * k⁻¹ * x⁻¹) = (k * x * k⁻¹ * x⁻¹) * x :=
      Data.Hyp.D₂_comm_Y' hx hkC
    have e2 : x⁻¹ * (k * x * k⁻¹ * x⁻¹) * x = k * x * k⁻¹ * x⁻¹ := by
      calc x⁻¹ * (k * x * k⁻¹ * x⁻¹) * x = x⁻¹ * ((k * x * k⁻¹ * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (k * x * k⁻¹ * x⁻¹)) := by rw [hcc]
        _ = k * x * k⁻¹ * x⁻¹ := by group
    rw [e2]
    exact hkC
  have hLU := h.liftFixG_U_eq_V₃_lin hK₁ hKY hD hΓ₁' hΓ₂' hU₁MY hU₂MY hw₁Γ hw₂Γ hw₁sq hw₂sq
    hcomm hU₁Γ hU₂Γ hgen₁ hgen₂ hfix hy₀Y hv'
  obtain ⟨c1, c2, c3, c4⟩ := h.splitting_D₂_lin hK₁ hKY hD (gamEquiv hinj 0) (gamEquiv hinj 2)
    hconjU hp₁ hp₂ hΓ₁' hΓ₂' hU₁MY hU₂MY hw₁Γ hw₂Γ hw₁sq hw₂sq hcomm hU₁Γ hU₂Γ hgen₁ hgen₂ hfix
    hy₀Y hv'
  obtain ⟨hJ₁, hJ₂, hJ₃⟩ := ModSplit.quadG d.D₂ d.Y h.Y_le_D₂
    (fun x hx y hy => h.D₂_commutator_mem_Y hK₁ hx hy) (fun x hx => h.D₂_mul_self_mem_Y hK₁ hx)
    h.card_D₂ h.card_Y hΓ₁' hΓ₂' (gamEquiv hinj 0) (gamEquiv hinj 2) hcomm hU₁Γ hU₂Γ
    (fun g hg => gam_lower_entries hinj 0 hg (hU₁Γ hg))
    (fun g hg => gam_lower_entries hinj 2 hg (hU₂Γ hg))
    (by
      obtain ⟨g, hg, hgΓ, hne⟩ := gam_lower_nontrivial hinj 0
      exact ⟨g, hg, hne⟩)
    (by
      obtain ⟨g, hg, hgΓ, hne⟩ := gam_lower_nontrivial hinj 2
      exact ⟨g, hg, hne⟩)
    c1 c2 c3 c4 (by rw [hLU, h.card_V₃ hK₁])
  rw [hLU] at hJ₁ hJ₂ hJ₃
  refine ⟨U₁, U₂, hU₁MY, hU₂MY, ?_, (root_image_comm_sq (φ := φ) 0).1,
    (root_image_comm_sq (φ := φ) 0).2, (root_image_comm_sq (φ := φ) 2).1,
    (root_image_comm_sq (φ := φ) 2).2, fun a ha b hb => hcomm a (hU₁Γ ha) b (hU₂Γ hb),
    hJ₁, hJ₂, hJ₃⟩
  intro x hx
  obtain ⟨u₁, hu₁, u₂, hu₂, y', hy', rfl⟩ := hs.mem_MY_decomp hx
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left ⟨u₁, hu₁, rfl⟩))
    (mem_sup_left (mem_sup_right ⟨u₂, hu₂, rfl⟩))) (mem_sup_right ((hs.mem_YK_iff h).2 hy'))

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
