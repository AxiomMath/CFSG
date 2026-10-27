module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RF
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame

public section

namespace CFSG.ClassicalInvolution.Asc77.T7S2R

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
open scoped MatrixGroups

section Basic

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

theorem comm_La_neg_one_of_involution (F : Frame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1)
    (hspan : ∀ y ∈ F.span, g y ∈ F.span) : g * F.La (-1) = F.La (-1) * g := by
  have hgg' : ∀ y, g (g y) = y := fun y => by
    have := congrArg (fun h : V ≃ₗ[K] V => h y) hgg
    simpa using this
  have hperp : ∀ r ∈ F.perp, g r ∈ F.perp := by
    intro r hr
    rw [Frame.mem_perp_iff_forall_incl] at hr ⊢
    intro Y
    have h1 : polar Q (g r) (F.incl Y) = polar Q r (g (F.incl Y)) := by
      rw [← polar_map_of_mem hg (g r) (F.incl Y), hgg']
    rw [h1]
    obtain ⟨Y', hY'⟩ := hspan (F.incl Y) ⟨Y, rfl⟩
    rw [← hY']
    exact hr Y'
  refine LinearEquiv.ext fun y => ?_
  have hr : y - F.incl (F.coords y) ∈ F.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  have hu : F.incl (F.coords y) ∈ F.span := ⟨_, rfl⟩
  have hy : y = F.incl (F.coords y) + (y - F.incl (F.coords y)) := by abel
  have hgu := hspan _ hu
  have hgr := hperp _ hr
  have e1 : F.La (-1) y = -F.incl (F.coords y) + (y - F.incl (F.coords y)) := by
    conv_lhs => rw [hy]
    rw [map_add, CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_span F hu,
      CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_perp F hr]
  have hgy : g y = g (F.incl (F.coords y)) + g (y - F.incl (F.coords y)) := by
    conv_lhs => rw [hy]
    rw [map_add]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, map_add, map_neg, hgy, map_add,
    CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_span F hgu,
    CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_perp F hgr]

theorem sign_mem_span_toFrame (F₀ : HypFrame Q m) {T : V ≃ₗ[K] V} {σ : Fin m → K}
    (hTσ : ∀ k r, T (F₀.vec k r) = σ k • F₀.vec k r) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    {y : V} (hy : y ∈ (F₀.toFrame hij s t).span) : T y ∈ (F₀.toFrame hij s t).span := by
  obtain ⟨X, rfl⟩ := hy
  rw [Frame.incl_apply]
  have e1 : T (F₀.toFrame hij s t).e₁ = σ i • F₀.vec i s := hTσ i s
  have e2 : T (F₀.toFrame hij s t).f₁ = σ i • F₀.vec i (!s) := hTσ i (!s)
  have e3 : T (F₀.toFrame hij s t).e₂ = σ j • F₀.vec j t := hTσ j t
  have e4 : T (F₀.toFrame hij s t).f₂ = σ j • F₀.vec j (!t) := hTσ j (!t)
  simp only [map_add, map_smul, e1, e2, e3, e4]
  have m1 := CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hij s t
    (Or.inl rfl) s
  have m2 := CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hij s t
    (Or.inl rfl) (!s)
  have m3 := CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hij s t
    (Or.inr rfl) t
  have m4 := CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hij s t
    (Or.inr rfl) (!t)
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ m1)
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ m2)
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ m3)
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ m4)

theorem La_neg_one_comm_toFrame (F₀ : HypFrame Q m) {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) :
    (F₀.toFrame hab true true).La (-1) * (F₀.toFrame hbc true true).La (-1) =
      (F₀.toFrame hbc true true).La (-1) * (F₀.toFrame hab true true).La (-1) :=
  (comm_La_neg_one_of_involution (F₀.toFrame hab true true)
    (Frame.La_mem_orthogonalGroup (F₀.toFrame hbc true true) (-1))
    (Frame.La_neg_one_mul_self (F₀.toFrame hbc true true))
    (fun _ hy => sign_mem_span_toFrame F₀
      (fun k r => CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_toFrame_vec F₀ hbc
        true true k r) hab true true hy)).symm

end Basic

section Weyl

@[expose] def weyl (K : Type) [Field K] : SL(2, K) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

variable {K : Type} [Field K]

theorem coe_weyl : ((weyl K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem coe_weyl_inv :
    (((weyl K)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_weyl, Matrix.adjugate_fin_two_of]
  simp

end Weyl

section Main

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {m : ℕ}

theorem elementaryGroup_le_normE_sup_toFrame (hQ : (polarBilin Q).Nondegenerate)
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (h7 : 7 ≤ Module.finrank K V)
    (F₀ : HypFrame Q m) {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    elementaryGroup Q ≤ normE Q (F₀.toFrame hab true true).La.range ⊔
      normE Q (F₀.toFrame hbc true true).La.range := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card' hodd
  have hc := La_neg_one_comm_toFrame F₀ hab hbc
  have hperp₁ : ∀ r, F₀.vec c r ∈ (F₀.toFrame hab true true).perp := fun r =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_perp_toFrame F₀ hab true true hac.symm
      hbc.symm r
  have hspan₁ : ∀ r, F₀.vec b r ∈ (F₀.toFrame hab true true).span := fun r =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hab true true
      (Or.inr rfl) r
  refine elementaryGroup_le_normE_sup hQ hodd h5 h7 (F₀.toFrame hab true true)
    (F₀.toFrame hbc true true) hc (weyl K) ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [negSpace_La_neg_one h2] at hx1 hx2
    have hxe := (Frame.mem_span_iff (F₀.toFrame hbc true true)).mp hx2
    have hpc : ∀ r, polar Q x (F₀.vec c r) = 0 := fun r => by
      have h := (Frame.mem_perp_iff_forall_incl (F₀.toFrame hab true true)).mp (hperp₁ r)
      obtain ⟨Y, hY⟩ := hx1
      rw [← hY, polar_comm]
      exact h Y
    have hf₂ : polar Q x (F₀.toFrame hbc true true).f₂ = 0 := hpc (!true)
    have he₂ : polar Q x (F₀.toFrame hbc true true).e₂ = 0 := hpc true
    have hX01 : (F₀.toFrame hbc true true).coords x 0 1 = 0 := by
      simp [Frame.coords_apply, hf₂]
    have hX10 : (F₀.toFrame hbc true true).coords x 1 0 = 0 := by
      simp [Frame.coords_apply, he₂]
    have hg : (F₀.toFrame hbc true true).La (weyl K) x = (F₀.toFrame hbc true true).incl
        ((weyl K : Matrix (Fin 2) (Fin 2) K) * (F₀.toFrame hbc true true).coords x) := by
      conv_lhs => rw [hxe]
      rw [Frame.La_apply_incl]
    have hY00 : ((weyl K : Matrix (Fin 2) (Fin 2) K) *
        (F₀.toFrame hbc true true).coords x) 0 0 = 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, coe_weyl, hX10]
    have hY11 : ((weyl K : Matrix (Fin 2) (Fin 2) K) *
        (F₀.toFrame hbc true true).coords x) 1 1 = 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, coe_weyl, hX01]
    have hmem : (F₀.toFrame hbc true true).incl ((weyl K : Matrix (Fin 2) (Fin 2) K) *
        (F₀.toFrame hbc true true).coords x) ∈ (F₀.toFrame hab true true).perp := by
      rw [Frame.incl_apply, hY00, hY11]
      simp only [zero_smul, zero_add]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hperp₁ true))
        (Submodule.smul_mem _ _ (hperp₁ (!true)))
    rw [hg]
    refine ⟨mem_posSpace_iff'.mpr ?_, mem_negSpace_iff'.mpr ?_⟩
    · rw [CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_perp _ hmem, one_smul]
    · rw [CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_span _ ⟨_, rfl⟩,
        neg_one_smul]
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [posSpace_La_neg_one h2] at hx1
    rw [negSpace_La_neg_one h2] at hx2
    have hxe := (Frame.mem_span_iff (F₀.toFrame hbc true true)).mp hx2
    have hpb : ∀ r, polar Q x (F₀.vec b r) = 0 := fun r => by
      have h := (Frame.mem_perp_iff_forall_incl (F₀.toFrame hab true true)).mp hx1
      obtain ⟨Y, hY⟩ := hspan₁ r
      rw [← hY]
      exact h Y
    have hf₁ : polar Q x (F₀.toFrame hbc true true).f₁ = 0 := hpb (!true)
    have he₁ : polar Q x (F₀.toFrame hbc true true).e₁ = 0 := hpb true
    have hX00 : (F₀.toFrame hbc true true).coords x 0 0 = 0 := by
      simp [Frame.coords_apply, hf₁]
    have hX11 : (F₀.toFrame hbc true true).coords x 1 1 = 0 := by
      simp [Frame.coords_apply, he₁]
    have hg : (F₀.toFrame hbc true true).La (weyl K)⁻¹ x = (F₀.toFrame hbc true true).incl
        (((weyl K)⁻¹ : SL(2, K)) * (F₀.toFrame hbc true true).coords x) := by
      conv_lhs => rw [hxe]
      rw [Frame.La_apply_incl]
    have hY01 : ((((weyl K)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        (F₀.toFrame hbc true true).coords x) 0 1 = 0 := by
      rw [coe_weyl_inv]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hX11]
    have hY10 : ((((weyl K)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        (F₀.toFrame hbc true true).coords x) 1 0 = 0 := by
      rw [coe_weyl_inv]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hX00]
    have hmem : (F₀.toFrame hbc true true).incl ((((weyl K)⁻¹ : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) * (F₀.toFrame hbc true true).coords x) ∈
        (F₀.toFrame hab true true).span := by
      rw [Frame.incl_apply, hY01, hY10]
      simp only [neg_zero, zero_smul, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hspan₁ true))
        (Submodule.smul_mem _ _ (hspan₁ (!true)))
    rw [hg]
    refine ⟨mem_negSpace_iff'.mpr ?_, mem_negSpace_iff'.mpr ?_⟩
    · rw [CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_span _ hmem, neg_one_smul]
    · rw [CFSG.ClassicalInvolution.Balance.Bootstrap.La_neg_one_of_mem_span _ ⟨_, rfl⟩,
        neg_one_smul]

end Main

end CFSG.ClassicalInvolution.Asc77.T7S2R
