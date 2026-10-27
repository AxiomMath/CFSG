module

public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

@[expose] def TightSecExactR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ∀ L ∈ Φ, ∀ M ∈ omegaNbr Φ L, (∃ g : X, conjSub g L = M) →
        classicalInvolutionOddCore ↥L = ⊥

section Gen

variable {X : Type} [Group X] [Finite X] {r : ℕ} {Φ : Set (Subgroup X)}

theorem oddCore_eq_bot_of_isPGroup {L : Subgroup X} (hL : IsPGroup 2 ↥L) :
    classicalInvolutionOddCore ↥L = ⊥ := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥L)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥L
  obtain ⟨k, hk⟩ := (hL.to_subgroup (classicalInvolutionOddCore ↥L)).exists_card_eq
  rw [hk] at hodd
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩)
      (Nat.not_even_iff_odd.mpr hodd)

omit [Finite X] in
theorem isPGroup_of_oddCore_eq_bot (h : TypeRFam r Φ) {L : Subgroup X} (hL : L ∈ Φ)
    (hO : classicalInvolutionOddCore ↥L = ⊥) : IsPGroup 2 ↥L :=
  (h.twoGroup L hL).of_injective (QuotientGroup.mk' (classicalInvolutionOddCore ↥L))
    ((MonoidHom.ker_eq_bot_iff _).mp ((QuotientGroup.ker_mk' _).trans hO))

theorem le_normalizer_of_isPGroup (h : TypeRFam r Φ) {L M : Subgroup X}
    (hM : M ∈ omegaNbr Φ L) (hM2 : IsPGroup 2 ↥M) :
    M ≤ Subgroup.normalizer (L : Set X) := by
  obtain ⟨hMΦ, -, T, hT, hTM, hTN⟩ := hM
  have hTsyl : IsSylow2In T M := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hMΦ hT hTM
  have hMT : M = T := hTsyl.2.2 M le_rfl hM2 hTM
  rw [hMT]
  exact hTN

theorem commutes_of_exact (h : TypeRFam r Φ) {L M : Subgroup X} (hL : L ∈ Φ)
    (hM : M ∈ omegaNbr Φ L) (hOL : classicalInvolutionOddCore ↥L = ⊥)
    (hOM : classicalInvolutionOddCore ↥M = ⊥) : Commutes L M := by
  have hΦ := h.hyp
  have hMΦ : M ∈ Φ := hM.1
  have hne : M ≠ L := hM.2.1
  have hL2 := isPGroup_of_oddCore_eq_bot h hL hOL
  have hM2 := isPGroup_of_oddCore_eq_bot h hMΦ hOM
  have hMN : M ≤ Subgroup.normalizer (L : Set X) := le_normalizer_of_isPGroup h hM hM2
  have hLM : L ∈ omegaNbr Φ M := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hL hMΦ hM
  have hLN : L ≤ Subgroup.normalizer (M : Set X) := le_normalizer_of_isPGroup h hLM hL2
  have hoL : oddCoreOf L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨_hxL, hx'⟩ := mem_oddCoreOf_iff.mp hx
    rw [hOL, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  intro l hl m hm
  have hlm : ⁅l, m⁆ ∈ L ⊓ M := by
    refine ⟨?_, ?_⟩
    · have h1 : m * l⁻¹ * m⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hMN hm) l⁻¹).mp (L.inv_mem hl)
      rw [commutatorElement_def]
      have : l * m * l⁻¹ * m⁻¹ = l * (m * l⁻¹ * m⁻¹) := by group
      rw [this]
      exact L.mul_mem hl h1
    · have h1 : l * m * l⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hLN hl) m).mp hm
      rw [commutatorElement_def]
      exact M.mul_mem h1 (M.inv_mem hm)
  have hc : ⁅l, m⁆ = 1 := by
    obtain ⟨hv, hv1⟩ := hΦ.omega4 L hL M hMΦ (Ne.symm hne)
    have hLM2 : IsPGroup 2 ↥(L ⊓ M) := hL2.to_le inf_le_left
    obtain ⟨k, hk⟩ := hLM2.exists_card_eq
    have hval : padicValNat 2 (Nat.card ↥(L ⊓ M)) = k := by
      rw [hk, padicValNat.prime_pow]
    rcases Nat.lt_or_ge k 1 with hk0 | hk1
    · have hk0' : k = 0 := by omega
      rw [hk0', pow_zero] at hk
      have hbot : L ⊓ M = ⊥ := Subgroup.eq_bot_of_card_eq _ hk
      rw [hbot, Subgroup.mem_bot] at hlm
      exact hlm
    · have hk1' : padicValNat 2 (Nat.card ↥(L ⊓ M)) = 1 := by omega
      have hmem : ⁅l, m⁆ ∈ ⁅L, M⁆ := Subgroup.commutator_mem_commutator hl hm
      have h2 := hv1 hk1' hmem
      rw [hoL, bot_inf_eq, Subgroup.mem_bot] at h2
      exact h2
  exact commutatorElement_eq_one_iff_mul_comm.mp hc

end Gen

end CFSG.ClassicalInvolution.Q3.TL4
