module

public import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.SylowNormalizerNotCentralizing
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
import CFSG.FeitThompson.Local.AveragingProjectionFixedVectors
import CFSG.FeitThompson.OddOrder.SemidirectReassociation
import CFSG.FeitThompson.Representations.PrimeComplementNoFixedVectorCentralizes

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsPrimeCentralizerKernelSetup p H R R0 V K U N P)

namespace IsPrimeCentralizerKernelSetup

include hc

theorem V_le_H : V ≤ H := by rw [hc.V_eq]; exact map_subtype_le _

theorem isElementaryAbelian_V : IsElementaryAbelian p V := by
  have := Fact.mk hc.prime_p
  rw [hc.V_eq]
  exact isElementaryAbelian_map_subtype_fittingRaw_of_minimal hc.admissible
    hc.not_hasPLengthLeOne hc.minimal

theorem isPGroup_P : IsPGroup p ↥P := IsPGroup.of_card hc.card_P

theorem coprime_natCard_K_R0 : (Nat.card ↥K).Coprime (Nat.card ↥R0) :=
  (hc.admissible.coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hc.K_le_H)).coprime_dvd_right
    (Subgroup.card_dvd_of_le hc.admissible.le)

theorem coprime_natCard_R0_P : (Nat.card ↥R0).Coprime (Nat.card ↥P) := by
  have := Fact.mk hc.prime_p
  rw [hc.card_P]
  exact Nat.Coprime.pow_right _
    ((Nat.coprime_primes hc.admissible.prime_card hc.prime_p).2
      (Ne.symm (ne_natCard_of_minimal hc.admissible hc.not_hasPLengthLeOne hc.minimal)))

theorem not_dvd_natCard_sup_K_R0 : ¬ p ∣ Nat.card ↥(K ⊔ R0) := by
  have := Fact.mk hc.prime_p
  rw [natCard_sup_eq_mul_of_le_normalizer (hc.admissible.le.trans hc.R_le_normalizer_K)
    hc.inf_K_R0]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hc.prime_p).1 hdvd with h | h
  · exact hc.prime_p.one_lt.ne' (hc.coprime_card_K.symm.eq_one_of_dvd h)
  · exact ne_natCard_of_minimal hc.admissible hc.not_hasPLengthLeOne hc.minimal
      ((Nat.prime_dvd_prime_iff_eq hc.prime_p hc.admissible.prime_card).1 h)

theorem inf_V_centralizer_R0_le : V ⊓ centralizer (R0 : Set G) ≤ centralizer (R0 : Set G) ⊓ H :=
  le_inf inf_le_right (inf_le_left.trans hc.V_le_H)

theorem inf_V_centralizer_R0_ne_bot : V ⊓ centralizer (R0 : Set G) ≠ ⊥ := by
  intro h0
  have := Fact.mk hc.prime_p
  have _isolv : Group.IsSolvable G := hc.admissible.isSolvable
  obtain ⟨d, -, -, e, ρ, -, hρact⟩ := hc.exists_injective_gl_rep
  have hKL : K ≤ K ⊔ R0 := le_sup_left
  have hR0L : R0 ≤ K ⊔ R0 := le_sup_right
  have hnormR0K : R0 ≤ normalizer (K : Set G) := hc.admissible.le.trans hc.R_le_normalizer_K
  have _iK : (K.subgroupOf (K ⊔ R0)).Normal := normal_subgroupOf_sup hnormR0K
  have hcompl : (K.subgroupOf (K ⊔ R0)).IsComplement' (R0.subgroupOf (K ⊔ R0)) :=
    isComplement'_subgroupOf_sup hnormR0K (disjoint_iff.2 hc.inf_K_R0)
  have hcardK : Nat.card ↥(K.subgroupOf (K ⊔ R0)) = Nat.card ↥K :=
    Nat.card_congr (subgroupOfEquivOfLe hKL).toEquiv
  have hcardR0 : Nat.card ↥(R0.subgroupOf (K ⊔ R0)) = Nat.card ↥R0 :=
    Nat.card_congr (subgroupOfEquivOfLe hR0L).toEquiv
  have hcop : (Nat.card ↥(K.subgroupOf (K ⊔ R0))).Coprime
      (Nat.card ↥(R0.subgroupOf (K ⊔ R0))) := by
    rw [hcardK, hcardR0]; exact hc.coprime_natCard_K_R0
  have hrprime : (Nat.card ↥(R0.subgroupOf (K ⊔ R0))).Prime := by
    rw [hcardR0]; exact hc.admissible.prime_card
  have hodd : Odd (Nat.card ↥(K ⊔ R0)) := hc.admissible.odd_card_subgroup _
  have hinv : Representation.invariants
      ((glRepresentation ρ).comp (R0.subgroupOf (K ⊔ R0)).subtype) = ⊥ := by
    refine le_bot_iff.1 fun w hw => ?_
    have hw' := (Representation.mem_invariants _ w).1 hw
    obtain ⟨v, hvw⟩ : ∃ v : ↥V, Multiplicative.toAdd (e v) = w :=
      ⟨e.symm (Multiplicative.ofAdd w), by simp⟩
    have hfix : ∀ x ∈ R0, (x : G) * (v : G) * (x : G)⁻¹ = (v : G) := by
      intro x hx
      have hxL : (⟨x, hR0L hx⟩ : ↥(K ⊔ R0)) ∈ R0.subgroupOf (K ⊔ R0) :=
        Subgroup.mem_subgroupOf.2 hx
      have h1 := hw' ⟨⟨x, hR0L hx⟩, hxL⟩
      rw [MonoidHom.comp_apply, glRepresentation_apply_apply] at h1
      simp only [Subgroup.coe_subtype] at h1
      rw [← hvw] at h1
      have h4 : hc.actionV ⟨x, hR0L hx⟩ v = v :=
        e.injective (Multiplicative.toAdd.injective (by rw [← hρact ⟨x, hR0L hx⟩ v, h1]))
      have h5 := hc.actionV_apply_coe ⟨x, hR0L hx⟩ v
      rw [h4] at h5
      exact h5.symm
    have hvmem : (v : G) ∈ V ⊓ centralizer (R0 : Set G) :=
      ⟨v.2, mem_centralizer_iff.2 fun x hx => mul_inv_eq_iff_eq_mul.1 (hfix x hx)⟩
    rw [h0, Subgroup.mem_bot] at hvmem
    rw [← hvw, show v = 1 from Subtype.ext hvmem, map_one]
    rfl
  have hmain := forall_apply_eq_self_of_mem_commutator_of_invariants_eq_bot_zmod
    (K := K.subgroupOf (K ⊔ R0)) (R := R0.subgroupOf (K ⊔ R0)) hodd hcompl hcop hrprime
    hc.not_dvd_natCard_sup_K_R0 (glRepresentation ρ) hinv
  have hbot : (⁅K.subgroupOf (K ⊔ R0), R0.subgroupOf (K ⊔ R0)⁆ : Subgroup ↥(K ⊔ R0)) = ⊥ := by
    refine (eq_bot_iff_forall _).2 fun x hx => ?_
    have hact : ∀ v : ↥V, hc.actionV x v = v := fun v => by
      have h1 := hmain x hx (Multiplicative.toAdd (e v))
      rw [glRepresentation_apply_apply] at h1
      have h2 := hρact x v
      rw [h1] at h2
      exact e.injective (Multiplicative.toAdd.injective h2.symm)
    exact hc.injective_actionV (by rw [map_one]; exact MulEquiv.ext hact)
  have hbot' : (⁅K, R0⁆ : Subgroup G) = ⊥ := by
    have h := congrArg (Subgroup.map (K ⊔ R0).subtype) hbot
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hR0L, Subgroup.map_bot] at h
  exact hc.commutator_R0_ne_bot hbot'

theorem natCard_inf_V_centralizer_R0 : Nat.card ↥(V ⊓ centralizer (R0 : Set G)) = p := by
  have := Fact.mk hc.prime_p
  set E : Subgroup G := V ⊓ centralizer (R0 : Set G) with hE
  have hEA : IsElementaryAbelian p E := hc.isElementaryAbelian_V.mono inf_le_left
  have _iZW : IsZGroup ↥(centralizer (R0 : Set G) ⊓ H) := hc.admissible.isZGroup_centralizer
  have _iZE : IsZGroup ↥E := isZGroup_of_le hc.inf_V_centralizer_R0_le
  have _iNil : Group.IsNilpotent ↥E := hEA.isPGroup.isNilpotent
  have _iCyc : IsCyclic ↥E := inferInstance
  have _iNt : Nontrivial ↥E :=
    (Subgroup.nontrivial_iff_ne_bot E).2 hc.inf_V_centralizer_R0_ne_bot
  exact natCard_eq_of_isCyclic_of_forall_pow_eq_one hc.prime_p inferInstance
    fun x => Subtype.ext (by simpa using hEA.pow_eq_one x.2)

theorem inf_P_centralizer_R0_eq_bot : P ⊓ centralizer (R0 : Set G) = ⊥ := by
  have := Fact.mk hc.prime_p
  set E : Subgroup G := V ⊓ centralizer (R0 : Set G) with hE
  set Q : Subgroup G := P ⊓ centralizer (R0 : Set G) with hQ
  have hEcard : Nat.card ↥E = p := hc.natCard_inf_V_centralizer_R0
  have _iVn : V.Normal := hc.normal_V
  have hQnorm : Q ≤ normalizer (E : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_of_normal hg, Subgroup.le_normalizer hg.2⟩
  have hPV : P ⊓ V = ⊥ := by
    rw [eq_bot_iff, ← hc.inf_V_N]
    exact le_inf inf_le_right (inf_le_left.trans hc.P_le_N)
  have hEQ : E ⊓ Q = ⊥ :=
    le_bot_iff.1 ((le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_left) :
      E ⊓ Q ≤ P ⊓ V).trans hPV.le)
  obtain ⟨k, hk⟩ := (hc.isPGroup_P.to_subgroup (Q.subgroupOf P)).exists_card_eq
  have hQcard : Nat.card ↥Q = p ^ k := by
    rw [← hk]
    exact (Nat.card_congr (subgroupOfEquivOfLe (K := P) (H := Q) inf_le_left).toEquiv).symm
  have hsupcard : Nat.card ↥(E ⊔ Q) = p ^ (k + 1) := by
    rw [natCard_sup_eq_mul_of_le_normalizer hQnorm hEQ, hEcard, hQcard, pow_succ, mul_comm]
  have hPH : P ≤ H := hc.P_le_N.trans hc.N_le_H
  have hsuple : E ⊔ Q ≤ centralizer (R0 : Set G) ⊓ H :=
    sup_le hc.inf_V_centralizer_R0_le (le_inf inf_le_right (inf_le_left.trans hPH))
  have _iZW : IsZGroup ↥(centralizer (R0 : Set G) ⊓ H) := hc.admissible.isZGroup_centralizer
  have _iZS : IsZGroup ↥(E ⊔ Q) := isZGroup_of_le hsuple
  have _iNilS : Group.IsNilpotent ↥(E ⊔ Q) := (IsPGroup.of_card hsupcard).isNilpotent
  have _iCycS : IsCyclic ↥(E ⊔ Q) := inferInstance
  by_contra hQne
  obtain ⟨Q0, hQ0Q, hQ0card⟩ :=
    exists_le_natCard_eq_prime hc.prime_p (IsPGroup.of_card hQcard) hQne
  have hQ0E : Q0 = E :=
    eq_of_le_of_natCard_eq_of_isCyclic (A := E ⊔ Q) (hQ0Q.trans le_sup_right) le_sup_left
      (by rw [hQ0card, hEcard])
  have hle : Q0 ≤ E ⊓ Q := le_inf hQ0E.le hQ0Q
  rw [hEQ, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hQ0card
  exact hc.prime_p.one_lt.ne' hQ0card.symm

theorem commutator_P_R0_eq : (⁅P, R0⁆ : Subgroup G) = P := by
  have _isolv : Group.IsSolvable G := hc.admissible.isSolvable
  have hnorm : R0 ≤ normalizer (P : Set G) := hc.admissible.le.trans hc.R_le_normalizer_P
  refine le_antisymm ((Subgroup.commutator_mono (le_refl P) hnorm).trans
    (commutator_normalizer_le P)) ?_
  exact le_commutator_of_coprime_of_inf_centralizer_eq_bot hnorm hc.coprime_natCard_R0_P
    hc.inf_P_centralizer_R0_eq_bot

theorem primeCentralizerFixedLine :
    Nat.card ↥(V ⊓ centralizer (R0 : Set G)) = p ∧ P ⊓ centralizer (R0 : Set G) = ⊥ ∧
      (⁅P, R0⁆ : Subgroup G) = P :=
  ⟨hc.natCard_inf_V_centralizer_R0, hc.inf_P_centralizer_R0_eq_bot, hc.commutator_P_R0_eq⟩

end IsPrimeCentralizerKernelSetup

end CFSG.FeitThompson

end
