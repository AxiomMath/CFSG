module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusRes
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviUnipotent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

section ScalarMod

variable {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M]

@[expose] def ScalarMod (Sup T : Submodule K M) (g : M → M) (a : K) : Prop :=
  ∀ v ∈ Sup, g v - a • v ∈ T

theorem ScalarMod.mul {Sup T : Submodule K M} {g g' : M ≃ₗ[K] M} {a a' : K}
    (hg : ScalarMod Sup T g a) (hg' : ScalarMod Sup T g' a') (hgT : ∀ w ∈ T, g w ∈ T) :
    ScalarMod Sup T (g * g') (a * a') := by
  intro v hv
  have h : (g * g') v - (a * a') • v = g (g' v - a' • v) + a' • (g v - a • v) := by
    simp only [LinearEquiv.mul_apply, map_sub, map_smul, smul_sub, mul_smul]
    rw [smul_comm a' a v]
    abel
  rw [h]
  exact T.add_mem (hgT _ (hg' v hv)) (T.smul_mem _ (hg v hv))

theorem ScalarMod.inv {Sup T : Submodule K M} {g : M ≃ₗ[K] M} {a : K}
    (hg : ScalarMod Sup T g a) (ha : a ≠ 0) (hgS : ∀ w ∈ Sup, g.symm w ∈ Sup) :
    ScalarMod Sup T (g⁻¹ : M ≃ₗ[K] M) a⁻¹ := by
  intro v hv
  have hw := hgS v hv
  have h1 := hg _ hw
  rw [LinearEquiv.apply_symm_apply] at h1
  have h2 := T.smul_mem a⁻¹ (T.neg_mem h1)
  have h3 : (g⁻¹ : M ≃ₗ[K] M) v - a⁻¹ • v = a⁻¹ • -(v - a • g.symm v) := by
    rw [smul_neg, smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul, neg_sub]
    rfl
  rw [h3]
  exact h2

theorem ScalarMod.commutator {Sup T : Submodule K M} {g₁ g₂ : M ≃ₗ[K] M} {a₁ a₂ : K}
    (h₁ : ScalarMod Sup T g₁ a₁) (h₂ : ScalarMod Sup T g₂ a₂) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hT₁ : ∀ w ∈ T, g₁ w ∈ T) (hT₂ : ∀ w ∈ T, g₂ w ∈ T)
    (hT₁' : ∀ w ∈ T, (g₁⁻¹ : M ≃ₗ[K] M) w ∈ T)
    (hS₁ : ∀ w ∈ Sup, g₁.symm w ∈ Sup) (hS₂ : ∀ w ∈ Sup, g₂.symm w ∈ Sup) :
    ScalarMod Sup T (⁅g₁, g₂⁆ : M ≃ₗ[K] M) 1 := by
  have h3 := h₁.inv ha₁ hS₁
  have h4 := h₂.inv ha₂ hS₂
  have h5 := (((h₁.mul h₂ hT₁).mul h3 (by
    intro w hw
    exact hT₁ _ (hT₂ _ hw))).mul h4 (by
      intro w hw
      exact hT₁ _ (hT₂ _ (hT₁' _ hw))))
  have e : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = 1 := by field_simp
  rw [e] at h5
  rw [commutatorElement_def]
  exact h5

end ScalarMod

section Sim

variable {K : Type} [Field K] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

@[expose] def IsSim
    (g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
    (μ : K) : Prop :=
  ∀ x y, polar (quadTail r (minusTailForm K b c)) (g x) (g y) =
    μ * polar (quadTail r (minusTailForm K b c)) x y

theorem IsSim.mul {g g' : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))} {μ μ' : K} (hg : IsSim (b := b) (c := c) g μ)
    (hg' : IsSim (b := b) (c := c) g' μ') : IsSim (b := b) (c := c) (g * g') (μ * μ') := by
  intro x y
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, hg', mul_assoc]

theorem IsSim.inv {g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))} {μ : K} (hμ : μ ≠ 0)
    (hg : IsSim (b := b) (c := c) g μ) : IsSim (b := b) (c := c) (g⁻¹) μ⁻¹ := by
  intro x y
  have h := hg (g⁻¹ x) (g⁻¹ y)
  have e1 : g (g⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have e2 : g (g⁻¹ y) = y := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rw [e1, e2] at h
  rw [h]
  field_simp

theorem IsSim.commutator {g₁ g₂ : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))} {μ₁ μ₂ : K} (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0)
    (h₁ : IsSim (b := b) (c := c) g₁ μ₁) (h₂ : IsSim (b := b) (c := c) g₂ μ₂) :
    ∀ x y, polar (quadTail r (minusTailForm K b c)) (⁅g₁, g₂⁆ x) (⁅g₁, g₂⁆ y) =
      polar (quadTail r (minusTailForm K b c)) x y := by
  intro x y
  have h := (((h₁.mul h₂).mul (h₁.inv hμ₁)).mul (h₂.inv hμ₂)) x y
  have e : μ₁ * μ₂ * μ₁⁻¹ * μ₂⁻¹ = 1 := by field_simp
  rw [e, one_mul] at h
  rw [commutatorElement_def]
  exact h

end Sim

section Unip

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

theorem commutator_pow_eq_one (hd : OrthCuts r d) {g₁ g₂ : 𝕍 ≃ₗ[K] 𝕍} {μ₁ μ₂ : K}
    (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0) (hs₁ : IsSim (b := b) (c := c) g₁ μ₁)
    (hs₂ : IsSim (b := b) (c := c) g₂ μ₂)
    (hf₁ : ∀ (i : Fin (s + 1)) (v : 𝕍), g₁ v ∈ tailFlag K (Fin 2 → K) r (d i) ↔
      v ∈ tailFlag K (Fin 2 → K) r (d i))
    (hf₂ : ∀ (i : Fin (s + 1)) (v : 𝕍), g₂ v ∈ tailFlag K (Fin 2 → K) r (d i) ↔
      v ∈ tailFlag K (Fin 2 → K) r (d i))
    (hsc₁ : ∀ l : Fin s, ∃ a : K, a ≠ 0 ∧ ScalarMod (tailFlag K (Fin 2 → K) r (d l.succ))
      (tailFlag K (Fin 2 → K) r (d l.castSucc)) g₁ a)
    (hsc₂ : ∀ l : Fin s, ∃ a : K, a ≠ 0 ∧ ScalarMod (tailFlag K (Fin 2 → K) r (d l.succ))
      (tailFlag K (Fin 2 → K) r (d l.castSucc)) g₂ a)
    (hres : ∀ v : 𝕍, IsResPerp hd.last v →
      (⁅g₁, g₂⁆ : 𝕍 ≃ₗ[K] 𝕍) v - v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s))) :
    (⁅g₁, g₂⁆ : 𝕍 ≃ₗ[K] 𝕍) ^ 2 ^ (2 * s + 1) = 1 := by
  set h : 𝕍 ≃ₗ[K] 𝕍 := ⁅g₁, g₂⁆ with hh
  have hiso : ∀ x y, polarBilin (quadTail r (minusTailForm K b c)) (h x) (h y) =
      polarBilin (quadTail r (minusTailForm K b c)) x y := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply]
    exact IsSim.commutator hμ₁ hμ₂ hs₁ hs₂ x y
  let F : ℕ → Submodule K 𝕍 := fun i =>
    tailFlag K (Fin 2 → K) r (if h : i ≤ s then d ⟨i, Nat.lt_succ_of_le h⟩ else d (Fin.last s))
  have hFl : ∀ (i : ℕ) (hi : i ≤ s),
      F i = tailFlag K (Fin 2 → K) r (d ⟨i, Nat.lt_succ_of_le hi⟩) := fun i hi => by
    simp [F, hi]
  have hsymm : ∀ (g : 𝕍 ≃ₗ[K] 𝕍) (T : Submodule K 𝕍), (∀ v, g v ∈ T ↔ v ∈ T) →
      ∀ w ∈ T, g.symm w ∈ T := fun g T hg w hw => (hg _).1 (by rwa [LinearEquiv.apply_symm_apply])
  have hpow := CFSG.SeitzReduction.OmegaPilot.sub_one_pow_eq_zero_of_isotropic_flag
    (polarBilin (quadTail r (minusTailForm K b c))) (g := h) hiso F
    (by
      rw [hFl 0 (by omega),
        show (⟨0, Nat.lt_succ_of_le (Nat.zero_le s)⟩ : Fin (s + 1)) = 0 from rfl,
        hd.zero, tailFlag_zero])
    s (fun i hi => by
      rw [hFl i (by omega), hFl (i + 1) (by omega)]
      exact orthTailFlag_mono (hd.mono.monotone (Fin.mk_le_mk.2 (by omega))))
    (fun i hi v hv => by
      rw [hFl (i + 1) (by omega)] at hv
      rw [hFl i (by omega)]
      obtain ⟨a₁, ha₁, hc₁⟩ := hsc₁ ⟨i, hi⟩
      obtain ⟨a₂, ha₂, hc₂⟩ := hsc₂ ⟨i, hi⟩
      have := ScalarMod.commutator hc₁ hc₂ ha₁ ha₂
        (fun w hw => (hf₁ _ w).2 hw) (fun w hw => (hf₂ _ w).2 hw)
        (hsymm g₁ _ (hf₁ _)) (hsymm g₁ _ (hf₁ _)) (hsymm g₂ _ (hf₂ _)) v hv
      rwa [one_smul] at this)
    (fun v hv => by
      rw [hFl s (by omega)] at hv ⊢
      refine hres v
        ((polar_tailFlag_eq_zero_iff (qB := minusTailForm K b c) hd.last).1 fun w hw => ?_)
      rw [polar_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hv) w hw)
  exact CFSG.SeitzReduction.OmegaPilot.pow_two_pow_eq_one_of_sub_one_pow_eq_zero hpow

end Unip

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
