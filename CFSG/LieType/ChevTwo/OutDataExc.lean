module

public import CFSG.LieType.ChevTwo.OutDataE6
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.Quasithin.H13.NQCatExceptional
import CFSG.Sporadic.Schreier.TitsOuterTwo
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outOddAbelian_of_E7E8
    {S : Type} [Group S] [Finite S] (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf1 : 1 ≤ f)
    (hm : UntwistedChevalleyModel S τ (2 ^ f)) : OutOddAbelian S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf1 K hK τ hτ
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  have : Finite (adjointGroup τ K) := Finite.of_equiv S e.toEquiv
  exact OutOddAbelian.of_mulEquiv e.symm (OutOddAbelian.of_ker_eq_inner Θ hker)

theorem outOddAbelian_of_F4
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : ChevalleyExceptionalModel S .F4 2 f) :
    OutOddAbelian S := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf1 K hK
  have : NeZero (2 * f) := ⟨by omega⟩
  have : Finite (adjointGroup .F4 K) := Finite.of_equiv S e.toEquiv
  exact OutOddAbelian.of_mulEquiv e.symm (OutOddAbelian.of_ker_eq_inner Θ hker)

theorem outOddAbelian_of_trialityD4
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : ChevalleyExceptionalModel S .trialityD4 2 f) :
    OutOddAbelian S :=
  OutOddAbelian.of_isCyclic (CFSG.Quasithin.H13.NQCat.outer_isCyclic_of_even_trialityD4_model
    h.1.2.1 h)

theorem outOddAbelian_of_twistedF4
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : ReeTitsModel S .twistedF4 2 f) :
    OutOddAbelian S :=
  OutOddAbelian.of_isCyclic
    (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions
      S 2 f h).2.2.2.1

theorem outOddAbelian_of_suzuki
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : SuzukiModel S 2 f) : OutOddAbelian S :=
  OutOddAbelian.of_isCyclic
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 f h).1.1

theorem outOddAbelian_of_tits
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : ReeTitsModel S .Tits 2 f) : OutOddAbelian S :=
  OutOddAbelian.of_card_eq_two
    (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound S 2 f h).2.2.1

theorem outOddAbelian_of_isChevTwoExc_of_tits
    (hT : ∀ (T : Type) [Group T] [Finite T] (hv : TauCeti.LieTypeIndex.tits.Valid),
      (T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.tits, hv⟩) → OutOddAbelian T)
    {S : Type} [Group S] [Finite S] (h : IsChevTwoExc S) : OutOddAbelian S := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  cases d with
  | E6 q =>
    exact outOddAbelian_of_E6 (f := q.exponent) ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e6 q hv hd e⟩
  | E7 q =>
    exact outOddAbelian_of_E7E8 .E7 (Or.inl rfl) q.exponent_pos
      (CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e7 q hv hd e)
  | E8 q =>
    exact outOddAbelian_of_E7E8 .E8 (Or.inr rfl) q.exponent_pos
      (CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e8 q hv hd e)
  | F4 q =>
    exact outOddAbelian_of_F4 (f := q.exponent) ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.f4 q hv hd e⟩
  | twistedE6 q =>
    exact outOddAbelian_of_twistedE6 (f := q.exponent) ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.twistedE6 q hv hd e⟩
  | trialityD4 q =>
    exact outOddAbelian_of_trialityD4 (f := q.exponent) ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.trialityD4 q hv hd e⟩
  | suzuki m =>
    exact outOddAbelian_of_suzuki (CFSG.StandardType.ChevTwo.suzukiModel_of_valid m hv e)
  | reeF4 a =>
    exact outOddAbelian_of_twistedF4 (CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 a hv e)
  | tits => exact hT S hv e
  | A _ _ | twistedA _ _ | B _ _ | C _ _ | D _ _ | twistedD _ _ | G2 _ | reeG2 _ => exact hd.elim

theorem outOddAbelian_of_isChevTwoExc
    {S : Type} [Group S] [Finite S] (h : IsChevTwoExc S) : OutOddAbelian S :=
  outOddAbelian_of_isChevTwoExc_of_tits
    (fun T _ _ hv e => outOddAbelian_of_tits
      (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e)) h

end CFSG.LieType.ChevTwo
