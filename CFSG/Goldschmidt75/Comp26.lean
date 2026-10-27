module

public import CFSG.Goldschmidt.Steps.Balance
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Fixed
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Normalizes

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open CFSG.ClassicalInvolution.Balance.LocalBalance (commute_pCore_of_mem_involutionOddCore
  eq_bot_of_centralizes_pCore_of_centralizes_components conjSub_eq_of_mem_involutionOddCore
  commute_of_moved commute_of_isComponent_centralizer)

variable {L : Type*} [Group L] [Finite L]

theorem exists_component_of_oddCore (hO : goldschmidtOddCore L = ⊥) {t : L} (ht : orderOf t = 2)
    {X : Subgroup L} (hX1 : X ≠ ⊥) (hX : X ≤ oddCoreOf (centralizer ({t} : Set L))) :
    ∃ K : Subgroup L, CFSG.IsComponent K ∧ t ∈ normalizer (K : Set L) ∧
      X ≤ normalizer (K : Set L) ∧ t ∉ centralizer (K : Set L) ∧
      ¬ X ≤ centralizer (K : Set L) := by
  by_contra hcon
  push Not at hcon
  apply hX1
  have hf2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hXodd : Odd (Nat.card X) :=
    Odd.of_dvd_nat (CFSG.Goldschmidt.Balance.odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le hX)
  have hO' : CFSG.pPrimeCore 2 L = ⊥ := by rwa [← goldschmidtOddCore_eq_pPrimeCore]
  refine eq_bot_of_centralizes_pCore_of_centralizes_components hO' hXodd ?_ ?_
  · intro d hd
    rw [mem_centralizer_iff]
    intro q hq
    have h := commute_pCore_of_mem_involutionOddCore ht (hX hd) q hq
    calc q * d = d * q * d⁻¹ * d := by rw [h]
      _ = d * q := by group
  · intro K hK
    by_cases hcen : ∀ k ∈ K, t * k = k * t
    · have hKC : K ≤ centralizer ({t} : Set L) := fun k hk =>
        mem_centralizer_singleton_iff.mpr (hcen k hk).symm
      intro d hd
      rw [mem_centralizer_iff]
      intro k hk
      exact (commute_of_isComponent_centralizer (hX hd) hKC
        (CFSG.LocalCores.component_overgroup hK hKC) k hk).symm
    · by_cases hmov : CFSG.ClassicalInvolution.Balance.LocalBalance.conjSub t K ≠ K
      · intro d hd
        rw [mem_centralizer_iff]
        intro k hk
        exact (commute_of_moved hK hf2 hmov (hX hd) k hk).symm
      · push Not at hmov
        have hXN : X ≤ normalizer (K : Set L) := fun d hd =>
          CFSG.ClassicalInvolution.Balance.LocalBalance.mem_normalizer_of_conjSub_eq
            (conjSub_eq_of_mem_involutionOddCore hK hf2 hmov (hX hd))
        have htN : t ∈ normalizer (K : Set L) :=
          CFSG.ClassicalInvolution.Balance.LocalBalance.mem_normalizer_of_conjSub_eq hmov
        refine hcon K hK htN hXN ?_
        intro htc
        apply hcen
        intro k hk
        exact (mem_centralizer_iff.mp htc k hk).symm

omit [Finite L] in
theorem commutator_le_of_le_normalizer {B K : Subgroup L} (hB : B ≤ normalizer (K : Set L)) :
    ⁅K, B⁆ ≤ K := by
  rw [commutator_le]
  intro k hk b hb
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  have := (mem_normalizer_iff.mp (hB hb) k⁻¹).mp (K.inv_mem hk)
  exact K.mul_mem hk (by simpa [mul_assoc] using this)

omit [Finite L] in
theorem commutator_le_centralizer_of_centralizes {A B K : Subgroup L}
    (hA : A ≤ centralizer (K : Set L)) (hB : B ≤ normalizer (K : Set L)) :
    ⁅B, A⁆ ≤ centralizer (K : Set L) := by
  have hKA : ⁅K, A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hA)
  have h1 : ⁅⁅A, K⁆, B⁆ = ⊥ := by
    rw [commutator_comm A K, hKA, commutator_bot_left]
  have h2 : ⁅⁅K, B⁆, A⁆ = ⊥ :=
    le_bot_iff.mp (hKA ▸ Subgroup.commutator_mono (commutator_le_of_le_normalizer hB) le_rfl)
  exact commutator_eq_bot_iff_le_centralizer.mp (commutator_commutator_eq_bot_of_rotate h1 h2)

theorem oddCoreOf_le_centralizer_of_component {V K : Subgroup L} (hK : CFSG.IsComponent K)
    (hKV : K ≤ centralizer (V : Set L)) :
    oddCoreOf (centralizer (V : Set L)) ≤ centralizer (K : Set L) := by
  set C := centralizer (V : Set L)
  have hsolv : Group.IsSolvable (goldschmidtOddCore C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card C)
  have hsub : (goldschmidtOddCore C).IsSubnormal :=
    (inferInstance : (goldschmidtOddCore C).Normal).isSubnormal
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv hsub).1 _
    (CFSG.LocalCores.component_overgroup hK hKV)
  rintro _ ⟨r, hr, rfl⟩
  rw [mem_centralizer_iff]
  intro k hk
  have hmem : (⟨k, hKV hk⟩ : C) ∈ K.subgroupOf C := hk
  have := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hmem) r hr
  exact (congrArg Subtype.val this).symm

theorem eq_bot_of_coreSep_balance (hO : goldschmidtOddCore L = ⊥) {V₁ V₂ X : Subgroup L}
    {t : L} (hsep : ∀ K : Subgroup L, CFSG.IsComponent K →
      V₁ ≤ centralizer (K : Set L) ∨ V₂ ≤ centralizer (K : Set L))
    (ht : orderOf t = 2) (hX : X ≤ oddCoreOf (centralizer ({t} : Set L)))
    (hV₁ : IsPGroup 2 V₁) (hV₂ : IsPGroup 2 V₂)
    (hV₁N : V₁ ≤ normalizer (X : Set L)) (hV₂N : V₂ ≤ normalizer (X : Set L))
    (hC₁ : X ⊓ centralizer (V₁ : Set L) ≤ oddCoreOf (centralizer (V₁ : Set L)))
    (hC₂ : X ⊓ centralizer (V₂ : Set L) ≤ oddCoreOf (centralizer (V₂ : Set L))) : X = ⊥ := by
  by_contra hX1
  obtain ⟨K, hK, -, hXK, -, hXC⟩ := exists_component_of_oddCore hO ht hX1 hX
  have hXodd : Odd (Nat.card X) :=
    Odd.of_dvd_nat (CFSG.Goldschmidt.Balance.odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le hX)
  have hcop : Nat.Coprime 2 (Nat.card X) := Nat.coprime_two_left.mpr hXodd
  apply hXC
  have key : ∀ V : Subgroup L, IsPGroup 2 V → V ≤ normalizer (X : Set L) →
      X ⊓ centralizer (V : Set L) ≤ oddCoreOf (centralizer (V : Set L)) →
      V ≤ centralizer (K : Set L) → X ≤ centralizer (K : Set L) := by
    intro V hV hVN hC hVK
    have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
      Nat.prime_two V X hV hVN hcop
    rw [← hfac]
    refine sup_le (commutator_le_centralizer_of_centralizes hVK hXK) (hC.trans ?_)
    exact oddCoreOf_le_centralizer_of_component hK fun k hk =>
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (Subgroup.mem_centralizer_iff.mp (hVK hv) k hk).symm
  rcases hsep K hK with h | h
  · exact key V₁ hV₁ hV₁N hC₁ h
  · exact key V₂ hV₂ hV₂N hC₂ h

end CFSG.Goldschmidt75
