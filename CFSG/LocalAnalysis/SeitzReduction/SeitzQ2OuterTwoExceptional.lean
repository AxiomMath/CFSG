module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwo
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

variable {K : Type} [Field K]

theorem card_outer_adjointGroup_F4_two
    (hK : Nat.card K = 2) : Nat.card (Outer (adjointGroup .F4 K)) = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ₀, -, hsurj, hker⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK, pow_one])
  set Θ : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * 1)) := Θ₀ with hΘ
  have hinner : inner (adjointGroup .F4 K) = Θ.ker := hker.symm
  have : Θ.ker.Normal := Θ.normal_ker
  have e : Outer (adjointGroup .F4 K) ≃* Multiplicative (ZMod (2 * 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (ZMod (2 * 1)) = 2
  rw [Nat.card_zmod]

theorem card_outer_eq_two_of_mulEquiv_F4_two
    {L : Type*} [Group L] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K) :
    Nat.card (Outer L) = 2 := by
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact card_outer_adjointGroup_F4_two hK

theorem card_outer_le_two_of_mulEquiv_F4_two
    {L : Type*} [Group L] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K) :
    Finite (Outer L) ∧ Nat.card (Outer L) ≤ 2 := by
  have h := card_outer_eq_two_of_mulEquiv_F4_two hK e
  exact ⟨Nat.finite_of_card_ne_zero (by omega), h.le⟩

theorem isPGroup_outer_of_mulEquiv_F4_two
    {L : Type*} [Group L] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K) :
    IsPGroup 2 (Outer L) :=
  IsPGroup.of_card (n := 1) (by rw [card_outer_eq_two_of_mulEquiv_F4_two hK e, pow_one])

theorem isCyclic_outer_adjointGroup_F4
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) : IsCyclic (Outer (adjointGroup .F4 K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ₀, -, hsurj, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  set Θ : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * f)) := Θ₀ with hΘ
  have hinner : inner (adjointGroup .F4 K) = Θ.ker := hker.symm
  have : Θ.ker.Normal := Θ.normal_ker
  have e : Outer (adjointGroup .F4 K) ≃* Multiplicative (ZMod (2 * f)) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  exact (MulEquiv.isCyclic e).2 inferInstance

theorem isCyclic_outer_of_mulEquiv_F4
    {L : Type*} [Group L] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .F4 K) : IsCyclic (Outer L) :=
  (MulEquiv.isCyclic (equivalence e)).2 (isCyclic_outer_adjointGroup_F4 hf hK)

theorem card_outer_adjointGroup_E6_two_le
    (hK : Nat.card K = 2) :
    Finite (Outer (adjointGroup .E6 K)) ∧ Nat.card (Outer (adjointGroup .E6 K)) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  refine finite_outer_and_card_le_two_of_forall
    (fun b => exactNormalAut .E6 K (fun _ => 1) (RingEquiv.refl K) (if b then 1 else 0))
    fun α => ?_
  obtain ⟨g, a, σ, ε, hα⟩ := (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 α
  have ha : a = fun _ => 1 := funext fun i => units_eq_one_of_natCard_eq_two hK (a i)
  have hσ : σ = RingEquiv.refl K := ringEquiv_eq_refl_of_card_eq_two hK σ
  subst ha hσ
  have hαe : α = MulAut.conj g * exactNormalAut .E6 K (fun _ => 1) (RingEquiv.refl K) ε := by
    ext h
    rw [hα h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_exactNormalAut]
    simp only [mul_assoc]
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.2
    omega
  refine ⟨decide ((ε : ℕ) = 1), ?_⟩
  have hb : (if decide ((ε : ℕ) = 1) then 1 else 0) = (ε : ℕ) := by
    rcases hε with h | h <;> simp [h]
  simp only [hb]
  rw [hαe, mul_inv_cancel_right]
  exact ⟨g, rfl⟩

theorem card_outer_le_two_of_mulEquiv_E6_two
    {L : Type*} [Group L] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E6 K) :
    Finite (Outer L) ∧ Nat.card (Outer L) ≤ 2 :=
  finite_outer_and_card_le_two_of_mulEquiv e (card_outer_adjointGroup_E6_two_le hK)

theorem isPGroup_outer_of_mulEquiv_E6_two
    {L : Type*} [Group L] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E6 K) :
    IsPGroup 2 (Outer L) := by
  obtain ⟨hfin, hcard⟩ := card_outer_le_two_of_mulEquiv_E6_two hK e
  exact isPGroup_two_of_card_le_two hcard

end CFSG.SeitzReduction.SeitzQ2
