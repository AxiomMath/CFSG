module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RG

public section

namespace CFSG.ClassicalInvolution.Asc77.T7S2R

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Overlap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

@[expose] def pairMap (F₀ : HypFrame Q m) (b : Fin m) : (Fin 2 → K) →ₗ[K] V where
  toFun c := c 0 • F₀.vec b true + c 1 • F₀.vec b false
  map_add' c d := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

theorem pairMap_apply (F₀ : HypFrame Q m) (b : Fin m) (c : Fin 2 → K) :
    pairMap F₀ b c = c 0 • F₀.vec b true + c 1 • F₀.vec b false := rfl

theorem polar_pairMap_false (F₀ : HypFrame Q m) (b : Fin m) (c : Fin 2 → K) :
    polar Q (pairMap F₀ b c) (F₀.vec b false) = c 0 := by
  simp [pairMap_apply, polar_add_left, polar_smul_left, F₀.polar_vec_vec]

theorem polar_pairMap_true (F₀ : HypFrame Q m) (b : Fin m) (c : Fin 2 → K) :
    polar Q (pairMap F₀ b c) (F₀.vec b true) = c 1 := by
  simp [pairMap_apply, polar_add_left, polar_smul_left, F₀.polar_vec_vec]

theorem pairMap_injective (F₀ : HypFrame Q m) (b : Fin m) :
    Function.Injective (pairMap F₀ b : (Fin 2 → K) →ₗ[K] V) := by
  intro c d h
  funext i
  fin_cases i
  · have := congrArg (fun x => polar Q x (F₀.vec b false)) h
    simpa [polar_pairMap_false] using this
  · have := congrArg (fun x => polar Q x (F₀.vec b true)) h
    simpa [polar_pairMap_true] using this

theorem inf_span_toFrame_eq (F₀ : HypFrame Q m) {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    (F₀.toFrame hab true true).span ⊓ (F₀.toFrame hbc true true).span =
      LinearMap.range (pairMap F₀ b) := by
  have hperp₁ : ∀ r, F₀.vec c r ∈ (F₀.toFrame hab true true).perp := fun r =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_perp_toFrame F₀ hab true true hac.symm
      hbc.symm r
  have hspan₁ : ∀ r, F₀.vec b r ∈ (F₀.toFrame hab true true).span := fun r =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hab true true
      (Or.inr rfl) r
  have hspan₂ : ∀ r, F₀.vec b r ∈ (F₀.toFrame hbc true true).span := fun r =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hbc true true
      (Or.inl rfl) r
  ext x
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨hx1, hx2⟩
    have hxe := (Frame.mem_span_iff (F₀.toFrame hbc true true)).mp hx2
    have hpc : ∀ r, polar Q x (F₀.vec c r) = 0 := fun r => by
      have h := (Frame.mem_perp_iff_forall_incl (F₀.toFrame hab true true)).mp (hperp₁ r)
      obtain ⟨Y, hY⟩ := hx1
      rw [← hY, polar_comm]
      exact h Y
    have hf₂ : polar Q x (F₀.toFrame hbc true true).f₂ = 0 := hpc (!true)
    have he₂ : polar Q x (F₀.toFrame hbc true true).e₂ = 0 := hpc true
    refine ⟨![polar Q x (F₀.vec b false), polar Q x (F₀.vec b true)], ?_⟩
    rw [pairMap_apply]
    conv_rhs => rw [hxe]
    rw [Frame.incl_apply]
    simp [Frame.coords_apply, hf₂, he₂]
    rfl
  · rintro ⟨c, rfl⟩
    rw [pairMap_apply]
    exact ⟨Submodule.add_mem _ (Submodule.smul_mem _ _ (hspan₁ true))
        (Submodule.smul_mem _ _ (hspan₁ false)),
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hspan₂ true))
        (Submodule.smul_mem _ _ (hspan₂ false))⟩

end Overlap

section Pair

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {m : ℕ}

omit [Finite K] [FiniteDimensional K V] in
theorem finrank_inf_span_toFrame (F₀ : HypFrame Q m) {a b c : Fin m} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) :
    Module.finrank K ↥((F₀.toFrame hab true true).span ⊓ (F₀.toFrame hbc true true).span) = 2 := by
  rw [inf_span_toFrame_eq F₀ hab hbc hac,
    LinearMap.finrank_range_of_inj (pairMap_injective F₀ b)]
  simp

theorem linearPair_toFrame (hodd : Odd (Nat.card K)) (F₀ : HypFrame Q m) {a b c : Fin m}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ W, LinearBlockStandardPair K W (F₀.toFrame hab true true).La.range
      (F₀.toFrame hbc true true).La.range := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card' hodd
  have hc := La_neg_one_comm_toFrame F₀ hab hbc
  have hspan₁ : ∀ r, F₀.vec b r ∈ (F₀.toFrame hab true true).span := fun r =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hab true true
      (Or.inr rfl) r
  have hspan₂ : ∀ r, F₀.vec b r ∈ (F₀.toFrame hbc true true).span := fun r =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.vec_mem_span_toFrame F₀ hbc true true
      (Or.inl rfl) r
  have h₁ : IsFundamental Q (F₀.toFrame hab true true).La.range
      ((F₀.toFrame hab true true).La (-1)) := IsFundamental.of_frame _
  have h₂ : IsFundamental Q (F₀.toFrame hbc true true).La.range
      ((F₀.toFrame hbc true true).La (-1)) := IsFundamental.of_frame _
  have hdim : Module.finrank K ↥(negSpace ((F₀.toFrame hab true true).La (-1)) ⊓
      negSpace ((F₀.toFrame hbc true true).La (-1))) = 2 := by
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2]
    exact finrank_inf_span_toFrame F₀ hab hbc hac
  have hN : (F₀.toFrame hbc true true).La (-1) ∈
      Subgroup.normalizer ((F₀.toFrame hab true true).La.range : Set (V ≃ₗ[K] V)) :=
    (mem_normalizer_iff_even hodd h₁ h₂ hc).mpr (by rw [hdim]; exact even_two)
  have hC : (F₀.toFrame hbc true true).La (-1) ∉
      Subgroup.centralizer ((F₀.toFrame hab true true).La.range : Set (V ≃ₗ[K] V)) := by
    intro hcent
    have hcent' : ∀ A : SL(2, K), (F₀.toFrame hbc true true).La (-1) *
        (F₀.toFrame hab true true).La A =
        (F₀.toFrame hab true true).La A * (F₀.toFrame hbc true true).La (-1) := fun A =>
      ((Subgroup.mem_centralizer_iff.mp hcent) _ ⟨A, rfl⟩).symm
    rcases Frame.orth_or_eq h2 hc.symm hcent' with horth | heq
    · obtain ⟨X, hX⟩ := hspan₁ true
      obtain ⟨Y, hY⟩ := hspan₂ false
      have h := horth X Y
      rw [hX, hY, F₀.polar_vec_vec] at h
      simp at h
    · rw [heq, inf_idem, negSpace_La_neg_one h2, Frame.finrank_span] at hdim
      omega
  have hsing : HasSingularVector Q (negSpace ((F₀.toFrame hab true true).La (-1)) ⊓
      negSpace ((F₀.toFrame hbc true true).La (-1))) := by
    refine ⟨F₀.vec b true, ?_, ?_, F₀.map_vec b true⟩
    · rw [Submodule.mem_inf, negSpace_La_neg_one h2, negSpace_La_neg_one h2]
      exact ⟨hspan₁ true, hspan₂ true⟩
    · intro h0
      have h := F₀.polar_vec_not b true
      rw [h0] at h
      simp at h
  exact ⟨_, (lemma_6_10 hodd h₁ h₂ hc hN hC).2 hsing⟩

end Pair

end CFSG.ClassicalInvolution.Asc77.T7S2R
