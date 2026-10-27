module

public import CFSG.LargeExtraspecial.DW2AElevenBasic
public import CFSG.LargeExtraspecial.DW2ModThree
public import CFSG.LargeExtraspecial.DW2AFive

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms

namespace Alpha

variable {G : Type} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

variable (S W) in
@[expose] def OutTwo : Prop :=
  ∀ y ∈ Ybar S, ∃ k : ℕ, ∃ x ∈ XbarL S W, ∃ c ∈ Ybar S, (∀ x' ∈ XbarL S W, c * x' = x' * c) ∧
    y ^ 2 ^ k = x * c

theorem outTwo_of_outer (hA : Hyp S W) (hOut : IsPGroup 2 (Outer (Xbar S W))) : OutTwo S W := by
  rintro _ ⟨m, hm, rfl⟩
  have hN := Mbar_le_normalizer_Xbar hA hm
  have hN' := Mbar_le_normalizer_Xbar hA (S.Mbar.inv_mem hm)
  obtain ⟨σ, hσ1⟩ : ∃ σ : MulAut (Xbar S W), ∀ x : Xbar S W, (σ x : S.O) = m * x * m⁻¹ :=
    ⟨{ toFun := fun x => ⟨m * x * m⁻¹, (mem_normalizer_iff.mp hN x).mp x.2⟩
       invFun := fun x => ⟨m⁻¹ * x * m, by simpa using (mem_normalizer_iff.mp hN' x).mp x.2⟩
       left_inv := fun x => Subtype.ext (by simp [mul_assoc])
       right_inv := fun x => Subtype.ext (by simp [mul_assoc])
       map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }, fun x => rfl⟩
  have hσ : ∀ (j : ℕ) (x : Xbar S W), ((σ ^ j) x : S.O) = m ^ j * x * (m ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hσ1, pow_succ]
      group
  obtain ⟨k, hk⟩ := hOut (QuotientGroup.mk σ)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  obtain ⟨x, hx⟩ := hk
  have hcX : ∀ x' ∈ Xbar S W,
      (x : S.O)⁻¹ * m ^ 2 ^ k * x' = x' * ((x : S.O)⁻¹ * m ^ 2 ^ k) := by
    intro x' hx'
    have h1 := congrArg (fun φ : MulAut (Xbar S W) => ((φ ⟨x', hx'⟩ : Xbar S W) : S.O)) hx
    simp only [MulAut.conj_apply, coe_mul, coe_inv] at h1
    rw [hσ] at h1
    calc (x : S.O)⁻¹ * m ^ 2 ^ k * x' =
        (x : S.O)⁻¹ * (m ^ 2 ^ k * x' * (m ^ 2 ^ k)⁻¹) * m ^ 2 ^ k := by group
      _ = (x : S.O)⁻¹ * ((x : S.O) * x' * (x : S.O)⁻¹) * m ^ 2 ^ k := by rw [h1]
      _ = x' * ((x : S.O)⁻¹ * m ^ 2 ^ k) := by group
  have hcM : (x : S.O)⁻¹ * m ^ 2 ^ k ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.inv_mem (Xbar_le_Mbar x.2)) (S.Mbar.pow_mem hm _)
  refine ⟨k, S.O.subtype (x : S.O), ⟨(x : S.O), x.2, rfl⟩,
    S.O.subtype ((x : S.O)⁻¹ * m ^ 2 ^ k), ⟨_, hcM, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul, hcX x' hx']
  · rw [← map_pow, ← map_mul, mul_inv_cancel_left]

theorem commSub_XbarL_le_perp (hA : Hyp S W) : commSub (XbarL S W) ⊤ ≤ perp S W :=
  commSub_le_iff.mpr fun _ ⟨_, hx, hxy⟩ v _ => hxy ▸ Xbar_sub_mem_perp hA hx v

theorem perp_ne_top (hA : Hyp S W) : perp S W ≠ ⊤ := by
  intro h
  apply hA.ne_bot
  rw [← perp_perp W, h]
  exact LinearMap.BilinForm.orthogonal_top_eq_bot S.q_nondegenerate

theorem false_of_regular_of_nondeg (hP : NondegWeaklyClosed S) {h₀ : G}
    (hx₀ : IsDx S W h₀)
    {U : Submodule (ZMod 2) S.Qt} (hU : IsInv (Ybar S) U) (hr : rad S.q.polarBilin U = ⊥)
    (h0 : U ≠ ⊥) (htop : U ≠ ⊤) : False :=
  hx₀.ne_z (hP U (fun m v hv => hU _ (ρ_mem_Ybar m) v hv) hr h0 htop h₀ hx₀.1)

theorem false_of_alpha_of_nondeg [IsSimpleGroup G] (hA : Hyp S W) (hn : 2 ≤ S.width)
    (hP : NondegWeaklyClosed S) {h₀ : G}
    (hx₀ : IsDx S W h₀) (h2 : OutTwo S W) : False := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨t₁, ht₁, t₂, ht₂, h1, h2', h12⟩ := exists_two_mem_Abar hA (by omega) hx₀
  have ht₁X : (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ XbarL S W := ⟨t₁, Abar_le_Xbar hx₀ ht₁, rfl⟩
  have hprop : commSub (XbarL S W) ⊤ ≠ ⊤ := fun h =>
    perp_ne_top hA (eq_top_iff.mpr (h ▸ commSub_XbarL_le_perp hA))
  by_cases h1F : OneFactor (XbarL S W)
  ·
    obtain ⟨T₁, hT₁⟩ := Abar_isTypeA hA hx₀ ht₁ h1
    obtain ⟨T₂, hT₂⟩ := Abar_isTypeA hA hx₀ ht₂ h2'
    have hne : commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠
        ⊥ := by
      intro h
      have hm : S.cl (h₀ * S.z * h₀⁻¹) ∈ commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
          commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hT₁, hT₂⟩
      rw [h, Submodule.mem_bot] at hm
      exact hx₀.cl_ne_zero hm
    have hne' : commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠
        commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      intro h
      have hle : commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
        h ▸ inf_le_right
      exact h12 (Subtype.ext (OrthoF2.eq_of_commSpace_eq S.q_nondegenerate T₁ T₂
        (Submodule.eq_of_le_of_finrank_eq hle (by rw [T₁.2.2.2.1, T₂.2.2.2.1]))))
    obtain ⟨U, hU, hU0, hUt, hUr, -⟩ := dw2_2_3 S.q_nondegenerate S.polarBilin_isRefl
      Ybar_le_isometryGroup noNormalTwo_Ybar
      (fun v hv => eq_zero_of_forall_ρ_apply_eq S (by omega) fun m => hv _ (ρ_mem_Ybar m))
      XbarL_le_Ybar (Ybar_le_normalizer_XbarL hA) h2 ht₁X ⟨t₂, Abar_le_Xbar hx₀ ht₂, rfl⟩
      (isSpTypeA_of_isTypeA T₁) (isSpTypeA_of_isTypeA T₂) hne hne' h1F hprop
    exact false_of_regular_of_nondeg hP hx₀ hU hUr hU0 hUt
  ·
    have hr := rad_stab_eq_bot S.q_nondegenerate S.polarBilin_isAlt
      (XbarL_le_Ybar.trans Ybar_le_isometryGroup) (isA2Class hA hn hx₀ ht₁ h1)
      (noNormalTwo_XbarL hA) (hasFourGroup hA hn hx₀) h1F
    refine false_of_regular_of_nondeg hP hx₀ (fun y hy v hv => ?_) hr (fun h0 => ?_) (fun htop => ?_)
    · have hyX : ∀ x ∈ XbarL S W, y * x * y⁻¹ ∈ XbarL S W := fun x hx =>
        (mem_normalizer_iff.mp (Ybar_le_normalizer_XbarL hA hy) x).mp hx
      exact apply_mem_iterComm hyX (fun _ _ => Submodule.mem_top) (finrank (ZMod 2) S.Qt) v hv
    · have hbot := eq_bot_of_isUnip (noNormalTwo_XbarL hA)
        (⟨finrank (ZMod 2) S.Qt, le_of_eq h0⟩ : IsUnip (XbarL S W) ⊥ ⊤)
      rw [hbot, mem_bot] at ht₁X
      exact h1 (Subtype.ext ht₁X)
    · apply hprop
      rw [eq_top_iff, ← htop]
      exact (commSub_stab isInv_top).ge

end Alpha

end CFSG.LargeExtraspecial.DW
