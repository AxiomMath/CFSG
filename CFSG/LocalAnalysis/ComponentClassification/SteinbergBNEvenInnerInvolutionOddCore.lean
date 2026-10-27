module

public import CFSG.LieType.Chevalley.SteinbergBNInvariantRadical
public import CFSG.LieType.Chevalley.EvenExceptionalActorCoverage
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityRadical

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

theorem finite_mulAut_of_finite {C : Type*} [Group C] [Finite C] : Finite (MulAut C) :=
  Finite.of_injective (fun φ : MulAut C => (φ : C → C)) DFunLike.coe_injective

namespace RootWeightDatum

variable {K : Type} [Field K] (D : RootWeightDatum K)

theorem pPrimeCore_inf_centralizer_eq_bot [Finite K] [CharP K 2] (hA : D.actors.Normal) {e : ℕ}
    (hidx : D.actors.index = 2 ^ e) (H : Subgroup (MulAut D.group))
    (hH : (MulAut.conj : D.group →* MulAut D.group).range ≤ H) {α : MulAut D.group}
    (hα : α ∈ (MulAut.conj : D.group →* MulAut D.group).range) (hα2 : orderOf α = 2) :
    CFSG.pPrimeCore 2 ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfin, hZ, hmain⟩ := D.root_p_subgroup_diagonal_field_invariant_radical (K := K) 2
  have hιinj : Function.Injective (MulAut.conj : D.group →* MulAut D.group) := conj_injective hZ
  obtain ⟨t, rfl⟩ := hα
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ hιinj t]
    exact hα2
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  set Q := Subgroup.zpowers t
  have hQ : Q ≠ ⊥ := fun h => ht1 (Subgroup.zpowers_eq_bot.1 h)
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨g, J, U, hJ, -, -, hUp, hNQU, hpt, hle⟩ := hmain Q hQ hQp
  refine full_inner_p_centralizer_core_from_equivariant_radical hZ 2 (A := ⊤) (A₀ := D.actors)
    (hA.subgroupOf ⊤) D.conj_range_le_actors (by rw [Subgroup.relIndex_top_right, hidx]) ht hUp
    (fun β hβ hfix => hle ((hpt β).1 ⟨hβ, hfix⟩)) (fun β hβ hcomm u hu => ?_) H hH le_top
  have hβt : β t = t := by
    apply hιinj
    rw [← mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
  have hβQ : β ∈ setwiseStabilizer D.actors Q := by
    refine ⟨hβ, ?_⟩
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hβt]
  have hβU := (hNQU hβQ).2
  rw [← hβU]
  exact ⟨u, hu, rfl⟩

end RootWeightDatum

theorem pow_eq_one_of_apply_eq_pow {K : Type} [Field K] [Finite K] {q m : ℕ} (σ : K ≃+* K)
    (hK : Nat.card K = q ^ m) (hσ : ∀ c, σ c = c ^ q) : σ ^ m = 1 := by
  have h : ∀ (n : ℕ) (c : K), (σ ^ n) c = c ^ (q ^ n) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, ih, hσ, ← pow_mul, pow_succ']
  have := Fintype.ofFinite K
  refine RingEquiv.ext fun c => ?_
  rw [h, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rfl

theorem even_exceptional_inner_involution_full_centralizer_odd_core :
    (∀ (τ : Tag) (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ (τ = .G2 ∧ 2 ≤ f)) →
      ∀ H : Subgroup (MulAut (adjointGroup τ K)),
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ≤ H →
        ∀ α ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range,
          orderOf α = 2 → CFSG.pPrimeCore 2 ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) ∧
    ∀ (t : TwistTag) (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f →
      Nat.card K = (2 ^ f) ^ t.order → (∀ c, σ c = c ^ 2 ^ f) →
      ∀ H : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)),
        (MulAut.conj : graphFixedRootGroup t K σ.toRingHom →*
          MulAut (graphFixedRootGroup t K σ.toRingHom)).range ≤ H →
        ∀ α ∈ (MulAut.conj : graphFixedRootGroup t K σ.toRingHom →*
          MulAut (graphFixedRootGroup t K σ.toRingHom)).range,
          orderOf α = 2 → CFSG.pPrimeCore 2 ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun τ f K _ hf hK hτ H hH α hα hα2 => ?_,
    fun t f K _ σ hf hK hσ H hH α hα hα2 => ?_⟩
  · have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    obtain ⟨hN, hle, -⟩ := even_exceptional_diagonal_field_actor_coverage.1 τ f K hf hK hτ
    have : Finite (adjointGroup τ K) := by
      have := finite_modGL (τ := τ) (K := K)
      infer_instance
    have : Finite (MulAut (adjointGroup τ K)) := finite_mulAut_of_finite
    have h0 := Subgroup.index_ne_zero_of_finite (H := diagonalFieldActors τ K)
    obtain ⟨e, he⟩ : ∃ e, (diagonalFieldActors τ K).index = 2 ^ e := by
      rcases (show (diagonalFieldActors τ K).index = 1 ∨ (diagonalFieldActors τ K).index = 2 by
        omega) with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    exact (RootWeightDatum.ordinary τ : RootWeightDatum K).pPrimeCore_inf_centralizer_eq_bot hN
      he H hH hα hα2
  · have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := f * t.order)
      (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
    have hσm : σ ^ t.order = 1 := pow_eq_one_of_apply_eq_pow σ hK hσ
    have htop := (even_exceptional_diagonal_field_actor_coverage.2 t f K σ hf hK hσ).1
    have hN : (fixedDiagonalFieldActors t K σ).Normal := by
      rw [htop]
      infer_instance
    have hidx : (fixedDiagonalFieldActors t K σ).index = 2 ^ 0 := by
      rw [htop, Subgroup.index_top, pow_zero]
    exact (RootWeightDatum.fixed t σ hσm : RootWeightDatum K).pPrimeCore_inf_centralizer_eq_bot
      hN hidx H hH hα hα2

end CFSG.LieType.Chevalley
