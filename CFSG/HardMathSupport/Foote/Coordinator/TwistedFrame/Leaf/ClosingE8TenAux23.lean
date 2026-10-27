module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux22
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux19

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem mRoots_not_Bset {μ : Fin Tag.E8.rank → ℤ} (hμ : μ ∈ mRoots) :
    μ ∉ CoordsAux.Bset TwClass.e8Ten := by
  rintro ⟨-, hS⟩
  obtain ⟨α, hα, hαJ, hne⟩ := mRoots_not_S₁ μ hμ
  exact hne (hS.2 α ⟨mem_rootFinset.1 hα, hαJ⟩)

section Steps

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem X₁_mul {x y : ModGL Tag.E8 K} (hx : x ∈ TwClass.e8Ten.X₁ D) (hy : y ∈ TwClass.e8Ten.X₁ D) :
    x * y ∈ TwClass.e8Ten.X₁ D := (TwClass.e8Ten.X₁ D).mul_mem hx hy

theorem X₁_inv {x : ModGL Tag.E8 K} (hx : x ∈ TwClass.e8Ten.X₁ D) : x⁻¹ ∈ TwClass.e8Ten.X₁ D :=
  (TwClass.e8Ten.X₁ D).inv_mem hx

theorem X₁_le_adjoint {x : ModGL Tag.E8 K} (hx : x ∈ TwClass.e8Ten.X₁ D) :
    x ∈ adjointGroup Tag.E8 K :=
  ((mem_frame_iff' D TwClass.e8Ten.S₁ x).1 hx).1

theorem zstep (hK : Nat.card K = 2) {H : Subgroup (ModGL Tag.E8 K)}
    (hHG : H ≤ adjointGroup Tag.E8 K)
    (hb : TwBasic (TwClass.e8Ten.X₁ D) (TwClass.e8Ten.X₂ D))
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {w : ModGL Tag.E8 K} (hwQ : w ∈ Qθ Tag.E8 K)
    (hwB : conjSub w (Heis.Uneg Tag.E8 K) ≤ H)
    (hwR : ∀ r : ModGL Tag.E8 K, r ∈ Rθ (TwClass.e8Ten.X₁ D) → r * w = w * r)
    {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8) (hγ0 : γ 7 = 0)
    (hZ : ∃ Z ∈ Agp D, ∃ ζ : D.L, ζ ≠ 0 ∧ ΨE D Z = pinnedX Tag.E8 D.L γ ζ)
    (hno : ¬ ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D))
    {ν : Fin Tag.E8.rank → ℤ} (hν : ν ∈ mRoots) (hνγ : ν + γ ∈ mRoots) : κF D w ν = 0 := by
  obtain ⟨Z, hZA, ζ, hζ, hΨ⟩ := hZ
  by_contra hne
  apply hno
  have hM : ActsBy (ΨE D Z) (actOp aE8 γ ζ) := by
    rw [hΨ]
    exact actsBy_pinnedX hγ hγ0 ζ
  refine RB_step D hK hHG hb hXH hwQ hwB hwR hZA hM (mRoots_not_Bset hνγ) ?_
  rw [actOp_eval, add_sub_cancel_right]
  intro h
  have hνd : ν ∈ deg1Roots :=
    mem_deg1Roots.2 ⟨(mem_mRoots.1 hν).1, (mem_mRoots.1 hν).2.1⟩
  have hA : (aE8 γ ν : D.L) ≠ 0 :=
    aE8_cast_ne_zero hγ hγ0 hνd (by
      rw [add_comm]
      exact mem_rootFinset.2 (mem_mRoots.1 hνγ).1)
  have h' : ζ * (aE8 γ ν : D.L) * κF D w ν = 0 := by
    have : κF D w (ν + γ) - (κF D w (ν + γ) + ζ * (aE8 γ ν : D.L) * κF D w ν) =
        -(ζ * (aE8 γ ν : D.L) * κF D w ν) := by ring
    rw [this] at h
    exact neg_eq_zero.1 h
  exact hne ((mul_eq_zero.1 h').resolve_left (mul_ne_zero hζ hA))

theorem conj_mem_R (hK : Nat.card K = 2) {ℓ : ModGL Tag.E8 K} (hℓ : ℓ ∈ TwClass.e8Ten.X₁ D)
    (hℓL : ΨE D ℓ ∈ Lθ Tag.E8 D.L) {r : ModGL Tag.E8 K} (hr : r ∈ Rθ (TwClass.e8Ten.X₁ D)) :
    ℓ * r * ℓ⁻¹ ∈ Rθ (TwClass.e8Ten.X₁ D) := by
  refine ⟨X₁_mul D (X₁_mul D hℓ hr.1) (X₁_inv D hℓ), ?_⟩
  have hrQ : r ∈ Qθ Tag.E8 K := hr.2
  have hΨQ : ΨE D (ℓ * r * ℓ⁻¹) ∈ Qθ Tag.E8 D.L := by
    rw [ΨE_mul, ΨE_mul, ΨE_inv]
    exact Lθ_conj_mem_Qθ hℓL (ΨE_Qθ D hrQ)
  refine mem_Qθ_of_bc D hK (X₁_le_adjoint D (X₁_mul D (X₁_mul D hℓ hr.1) (X₁_inv D hℓ))) ?_
  rw [bc_eq_conj D]
  exact Lθ_conj_mem_Qθ (gE_mem_Lθ D) hΨQ

theorem conj_step (hK : Nat.card K = 2) {H : Subgroup (ModGL Tag.E8 K)}
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {ℓ : ModGL Tag.E8 K} (hℓ : ℓ ∈ TwClass.e8Ten.X₁ D) (hℓL : ΨE D ℓ ∈ Lθ Tag.E8 D.L)
    (hℓU : ∀ u : ModGL Tag.E8 K, u ∈ Heis.Uneg Tag.E8 K → ℓ * u = u * ℓ)
    {T : Fn D.L →ₗ[D.L] Fn D.L} (hT : ActsBy (ΨE D ℓ) T)
    {w : ModGL Tag.E8 K} (hwQ : w ∈ Qθ Tag.E8 K) (hwB : conjSub w (Heis.Uneg Tag.E8 K) ≤ H)
    (hwR : ∀ r : ModGL Tag.E8 K, r ∈ Rθ (TwClass.e8Ten.X₁ D) → r * w = w * r) :
    ℓ * w * ℓ⁻¹ ∈ Qθ Tag.E8 K ∧ conjSub (ℓ * w * ℓ⁻¹) (Heis.Uneg Tag.E8 K) ≤ H ∧
      (∀ r : ModGL Tag.E8 K, r ∈ Rθ (TwClass.e8Ten.X₁ D) →
        r * (ℓ * w * ℓ⁻¹) = (ℓ * w * ℓ⁻¹) * r) ∧ κF D (ℓ * w * ℓ⁻¹) = T (κF D w) := by
  have hX₁H : TwClass.e8Ten.X₁ D ≤ H := le_sup_left.trans hXH
  have hℓH : ℓ ∈ H := hX₁H hℓ
  have hΨwQ : ΨE D w ∈ Qθ Tag.E8 D.L := ΨE_Qθ D hwQ
  obtain ⟨hcQ, hcc⟩ := hT _ hΨwQ
  have hΨ : ΨE D (ℓ * w * ℓ⁻¹) = ΨE D ℓ * ΨE D w * (ΨE D ℓ)⁻¹ := by
    rw [ΨE_mul, ΨE_mul, ΨE_inv]
  have hadj : ℓ * w * ℓ⁻¹ ∈ adjointGroup Tag.E8 K :=
    mul_mem (mul_mem (X₁_le_adjoint D hℓ) (Qθ_le_adjointGroup Tag.E8 K hwQ))
      (inv_mem (X₁_le_adjoint D hℓ))
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine mem_Qθ_of_bc D hK hadj ?_
    rw [bc_eq_conj D, hΨ]
    exact Lθ_conj_mem_Qθ (gE_mem_Lθ D) hcQ
  · intro x hx
    obtain ⟨u, hu, hxu⟩ : ∃ u : ModGL Tag.E8 K, u ∈ Heis.Uneg Tag.E8 K ∧
        x = (ℓ * w * ℓ⁻¹) * u * (ℓ * w * ℓ⁻¹)⁻¹ :=
      ⟨(ℓ * w * ℓ⁻¹)⁻¹ * x * (ℓ * w * ℓ⁻¹), mem_conjSub_iff.1 hx, by group⟩
    have hℓu : ℓ⁻¹ * u * ℓ = u := by
      have h := hℓU u hu
      calc ℓ⁻¹ * u * ℓ = ℓ⁻¹ * (u * ℓ) := by group
        _ = ℓ⁻¹ * (ℓ * u) := by rw [h]
        _ = u := by group
    have hwu : w * u * w⁻¹ ∈ H := hwB (mem_conjSub_iff.2 (by
      have e : w⁻¹ * (w * u * w⁻¹) * w = u := by group
      rw [e]
      exact hu))
    have hx_eq : x = ℓ * (w * u * w⁻¹) * ℓ⁻¹ := by
      rw [hxu]
      calc (ℓ * w * ℓ⁻¹) * u * (ℓ * w * ℓ⁻¹)⁻¹
          = ℓ * w * (ℓ⁻¹ * u * ℓ) * w⁻¹ * ℓ⁻¹ := by group
        _ = ℓ * (w * u * w⁻¹) * ℓ⁻¹ := by rw [hℓu]; group
    rw [hx_eq]
    exact mul_mem (mul_mem hℓH hwu) (inv_mem hℓH)
  · intro r hr
    have hr' : ℓ⁻¹ * r * ℓ ∈ Rθ (TwClass.e8Ten.X₁ D) := by
      have h := conj_mem_R D hK (X₁_inv D hℓ) (by rw [ΨE_inv]; exact inv_mem hℓL) hr
      simpa [inv_inv] using h
    have h1 := hwR _ hr'
    calc r * (ℓ * w * ℓ⁻¹) = ℓ * ((ℓ⁻¹ * r * ℓ) * w) * ℓ⁻¹ := by group
      _ = ℓ * (w * (ℓ⁻¹ * r * ℓ)) * ℓ⁻¹ := by rw [h1]
      _ = (ℓ * w * ℓ⁻¹) * r := by group
  · rw [κF_eq, κF_eq, hΨ, hcc]

end Steps

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
