module

public import CFSG.LieType.ChevTwo.OutDataGen
import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outOddAbelian_of_E6
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ChevalleyExceptionalModel S .E6 2 f) : OutOddAbelian S := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  obtain ⟨Φ, -, -, hdvd⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  have hdet : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
  rw [hdet] at hdvd
  have hring := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have hz2 : Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rfl
  have : Finite (Multiplicative (ZMod (exactE Tag.E6))) :=
    Nat.finite_of_card_ne_zero (by rw [hz2]; omega)
  refine OutOddAbelian.of_mulEquiv e.symm
    ⟨RingAut K × Multiplicative (ZMod (exactE Tag.E6)), inferInstance, Φ, ?_,
      Odd.of_dvd_nat (by decide) hdvd, fun T hT => ?_⟩
  · intro x y
    exact Prod.ext (CFSG.RankThree.PartOne.OutStructure.ringAut_comm K _ _) (mul_comm _ _)
  · exact card_le_four_of_prod hz2.le T hT

theorem outOddAbelian_of_twistedE6
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ChevalleyExceptionalModel S .twistedE6 2 f) : OutOddAbelian S := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel S .E6 (2 ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 Nat.prime_two hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf1 K hcard σ' hσ'
  have hK2 : Nat.card K = 2 ^ (f * 2) := by rw [hcard, ← pow_mul]; rfl
  have hring := card_ringAut_and_isCyclic Nat.prime_two K hK2
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have : Finite (twistedE6RootGroup K σ') := Finite.of_equiv S (e.trans E).toEquiv
  have hinner : inner (twistedE6RootGroup K σ') ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  let Φ : Outer (twistedE6RootGroup K σ') →* RingAut K := QuotientGroup.lift _ Θ hinner
  have h3 : ∀ x : Φ.ker, x ^ 3 = 1 := by
    rintro ⟨x, hx⟩
    induction x using QuotientGroup.induction_on with
    | H α =>
      have hα : α ∈ twistedE6Inn K σ' ⊔ twistedE6Diag K σ' := by
        rw [← hker]
        exact hx
      have h1 := hcube (QuotientGroup.mk ⟨α, hα⟩)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
      apply Subtype.ext
      show (QuotientGroup.mk α : Outer (twistedE6RootGroup K σ')) ^ 3 = 1
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact h1
  have hpg : IsPGroup 3 Φ.ker := fun x => ⟨1, by rw [pow_one]; exact h3 x⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Outer (twistedE6RootGroup K σ')) := finite_outer_of_finite _
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  refine OutOddAbelian.of_mulEquiv (e.trans E).symm
    ⟨RingAut K, inferInstance, Φ, CFSG.RankThree.PartOne.OutStructure.ringAut_comm K, ?_,
      fun T hT => (card_le_two_of_isCyclic_of_sq T hT).trans (by norm_num)⟩
  rw [hn]
  exact Odd.pow (by decide)

end CFSG.LieType.ChevTwo
