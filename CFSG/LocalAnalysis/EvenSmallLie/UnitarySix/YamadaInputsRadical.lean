module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsInvol

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix Module
open scoped MatrixGroups

theorem exists_le_le_finrank_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {R W : Submodule K V} (hRW : R ≤ W) {m : ℕ}
    (h1 : finrank K R ≤ m) (h2 : m ≤ finrank K W) :
    ∃ X : Submodule K V, R ≤ X ∧ X ≤ W ∧ finrank K X = m := by
  induction hk : m - finrank K R generalizing R with
  | zero => exact ⟨R, le_rfl, hRW, by omega⟩
  | succ k ih =>
    have hlt : finrank K R < finrank K W := by omega
    have hne : R ≠ W := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    obtain ⟨w, hwW, hwR⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hRW hne)
    have hR' := Submodule.finrank_sup_span_singleton hwR
    obtain ⟨X, hX1, hX2, hX3⟩ := ih (R := R ⊔ Submodule.span K {w})
      (sup_le hRW ((Submodule.span_singleton_le_iff_mem _ _).mpr hwW)) (by omega) (by omega)
    exact ⟨X, le_sup_left.trans hX1, hX2, hX3⟩

section Radical

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ}

omit [CharP F 2] in
theorem mul_sub_one_mulVec' (M N : Matrix (Fin n) (Fin n) F) (x : Fin n → F) :
    (M * N - 1) *ᵥ x = (M - 1) *ᵥ (N *ᵥ x) + (N - 1) *ᵥ x := by
  rw [mulVec_mulVec, ← add_mulVec]
  congr 1
  noncomm_ring

@[expose] def IsRadical (W : Submodule F (Fin n → F)) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ v, (M - 1) *ᵥ v ∈ W) ∧ ∀ w ∈ W, (M - 1) *ᵥ w = 0

omit [CharP F 2] in
theorem IsRadical.mul {W : Submodule F (Fin n → F)} {M N : Matrix (Fin n) (Fin n) F}
    (hM : IsRadical W M) (hN : IsRadical W N) : IsRadical W (M * N) := by
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [mul_sub_one_mulVec']
    exact W.add_mem (hM.1 _) (hN.1 v)
  · have hNw : N *ᵥ w = w := by
      have := hN.2 w hw
      rwa [sub_mulVec, one_mulVec, sub_eq_zero] at this
    rw [mul_sub_one_mulVec', hNw, hM.2 w hw, hN.2 w hw, add_zero]

theorem IsRadical.mul_self {W : Submodule F (Fin n → F)} {M : Matrix (Fin n) (Fin n) F}
    (hM : IsRadical W M) : M * M = 1 := by
  have h0 : (M - 1) * (M - 1) = 0 := by
    ext i j
    have := hM.2 _ (hM.1 (Pi.single j 1))
    rw [mulVec_mulVec, mulVec_single_one] at this
    exact congrFun this i
  have h2 : M * M = 1 + (M - 1) * (M - 1) + (2 : F) • (M - 1) := by
    rw [two_smul]
    noncomm_ring
  rw [h2, h0, CharTwo.two_eq_zero, zero_smul, add_zero, add_zero]

@[expose] def radicalSub (W : Submodule F (Fin n → F)) : Subgroup SL(n, F) where
  carrier := {x | IsRadical W (x : Matrix (Fin n) (Fin n) F)}
  mul_mem' {x y} hx hy := by
    have := IsRadical.mul hx hy
    rwa [← Matrix.SpecialLinearGroup.coe_mul] at this
  one_mem' := ⟨fun v => by simp, fun w _ => by simp⟩
  inv_mem' {x} hx := by
    have h : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Subtype.ext hx.mul_self)
    rw [Set.mem_ofPred_eq, h]
    exact hx

theorem radicalSub_le_centralizer {W : Submodule F (Fin n → F)} {g : SL(n, F)}
    (hgW : ∀ v, ((g : Matrix (Fin n) (Fin n) F) - 1) *ᵥ v ∈ W)
    (hWg : ∀ w ∈ W, ((g : Matrix (Fin n) (Fin n) F) - 1) *ᵥ w = 0) :
    radicalSub W ≤ centralizer ({g} : Set SL(n, F)) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  set X := (x : Matrix (Fin n) (Fin n) F) - 1
  set N := (g : Matrix (Fin n) (Fin n) F) - 1
  have h1 : X * N = 0 := by
    ext i j
    have := hx.2 _ (hgW (Pi.single j 1))
    rw [mulVec_mulVec, mulVec_single_one] at this
    exact congrFun this i
  have h2 : N * X = 0 := by
    ext i j
    have := hWg _ (hx.1 (Pi.single j 1))
    rw [mulVec_mulVec, mulVec_single_one] at this
    exact congrFun this i
  have : (x : Matrix (Fin n) (Fin n) F) * g - g * x = X * N - N * X := by
    simp only [X, N]
    noncomm_ring
  rw [h1, h2, sub_self, sub_eq_zero] at this
  exact congrFun (congrFun this i) j

theorem isPGroup_radicalSub (W : Submodule F (Fin n → F)) : IsPGroup 2 (radicalSub W) := by
  intro x
  refine ⟨1, Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)⟩
  rw [pow_one, sq, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, x.2.mul_self]
  rfl

theorem card_radicalSub [Finite F] (W : Submodule F (Fin n → F)) :
    Nat.card F ^ ((n - finrank F W) * finrank F W) ≤ Nat.card (radicalSub W) := by
  classical
  set T : ((Fin n → F) ⧸ W →ₗ[F] W) → Matrix (Fin n) (Fin n) F :=
    fun f => LinearMap.toMatrix' (W.subtype ∘ₗ f ∘ₗ W.mkQ)
  have hrad : ∀ f, IsRadical W (1 + T f) := fun f => by
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [add_sub_cancel_left, LinearMap.toMatrix'_mulVec]
      exact (f _).2
    · rw [add_sub_cancel_left, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply,
        LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hw,
        map_zero, map_zero]
  have hdet : ∀ f, (1 + T f).det = 1 := fun f =>
    eq_one_of_sq_eq_one_of_charTwo (by rw [← det_mul, (hrad f).mul_self, det_one])
  let Φ : ((Fin n → F) ⧸ W →ₗ[F] W) → radicalSub W := fun f => ⟨⟨1 + T f, hdet f⟩, hrad f⟩
  have hΦ : Function.Injective Φ := by
    intro f f' hff
    have hT : T f = T f' := by
      have := congrArg (fun x : radicalSub W => ((x : SL(n, F)) : Matrix (Fin n) (Fin n) F)) hff
      exact add_left_cancel this
    have hT' : W.subtype ∘ₗ f ∘ₗ W.mkQ = W.subtype ∘ₗ f' ∘ₗ W.mkQ :=
      LinearMap.toMatrix'.injective hT
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W q
    exact Subtype.ext (LinearMap.congr_fun hT' v)
  have hcard : Nat.card ((Fin n → F) ⧸ W →ₗ[F] W) =
      Nat.card F ^ ((n - finrank F W) * finrank F W) := by
    rw [Module.natCard_eq_pow_finrank (K := F), Module.finrank_linearMap]
    congr 2
    have := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fin_fun] at this
    omega
  rw [← hcard]
  exact Nat.card_le_card_of_injective Φ hΦ

theorem exists_twoSubgroup_le_centralizer [Finite F] {m : ℕ} (hn : n = 2 * m) (g : SL(n, F))
    (hg : g * g = 1) : ∃ Q : Subgroup SL(n, F), Q ≤ centralizer ({g} : Set SL(n, F)) ∧
      IsPGroup 2 Q ∧ Nat.card F ^ (m * m) ≤ Nat.card Q := by
  classical
  set N := (g : Matrix (Fin n) (Fin n) F) - 1 with hN
  have hgg : (g : Matrix (Fin n) (Fin n) F) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_one]
  have hNN : N * N = 0 := by
    have h2 : (g : Matrix (Fin n) (Fin n) F) * g = 1 + N * N + (2 : F) • N := by
      rw [two_smul, hN]
      noncomm_ring
    rw [hgg, CharTwo.two_eq_zero, zero_smul, add_zero] at h2
    have := congrArg (· - 1) h2
    simpa using this.symm
  set f := Matrix.toLin' N
  have hRK : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, hNN,
      zero_mulVec]
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrank
  have hle := Submodule.finrank_mono hRK
  obtain ⟨W, hRW, hWK, hWm⟩ := exists_le_le_finrank_eq hRK (m := m) (by omega) (by omega)
  refine ⟨radicalSub W, radicalSub_le_centralizer (fun v => hRW ⟨v, rfl⟩)
    (fun w hw => hWK hw), isPGroup_radicalSub W, ?_⟩
  have := card_radicalSub W
  rwa [hWm, show n - m = m by omega] at this

end Radical

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
