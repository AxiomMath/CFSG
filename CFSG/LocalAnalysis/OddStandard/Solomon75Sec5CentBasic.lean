module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneCount2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section LPlus

variable {X : Type} [Group X] [Finite X]

theorem IsIntrinsicIn.le_LPlusIn {H M : Subgroup X} {u : X} (h : IsIntrinsicIn X H M u) :
    M ≤ LPlusIn H := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMH : M ≤ H := h.2.2.1.1
  have hM' : IsPComponent 2 (M.subgroupOf H) := h.2.2.1.2
  intro m hm
  refine ⟨⟨m, hMH hm⟩, ?_, rfl⟩
  rw [LPlus_eq_pLayer_sup_NPlus]
  exact Subgroup.mem_sup_left ((le_sSup hM' : M.subgroupOf H ≤ pLayer ↥H 2) hm)

end LPlus

section Cover

variable {n : ℕ} {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem AhatData.CoverSetup.normal_odd_eq_bot (hn : 5 ≤ n) (C : AhatData.CoverSetup n K)
    {P : Subgroup K} [P.Normal] (hP : Odd (Nat.card P)) : P = ⊥ := by
  classical
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  have hQn : (P.map C.π).Normal := Subgroup.Normal.map ‹P.Normal› C.π C.surj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map C.π) with h | h
  · have hle : P ≤ center K := by
      rw [← C.ker]
      intro x hx
      have : C.π x ∈ P.map C.π := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    have h1 : Nat.card P ∣ Nat.card (center K) := Subgroup.card_dvd_of_le hle
    rw [C.center_card] at h1
    have h2 : Nat.card P = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at hP
        exact absurd hP (by decide)
    exact Subgroup.eq_bot_of_card_eq P h2
  · exfalso
    have h1 : Nat.card (P.map C.π) ∣ Nat.card P := Subgroup.card_map_dvd P C.π
    rw [h, Subgroup.card_top] at h1
    have h2 := Odd.of_dvd_nat hP h1
    have h3 := even_card_alternatingGroup (α := Fin n) (by rw [Fintype.card_fin]; omega)
    exact (Nat.not_even_iff_odd.2 h2) h3

theorem AhatData.CoverSetup.normal_pgroup_le_center (hn : 5 ≤ n) (C : AhatData.CoverSetup n K)
    {P : Subgroup K} [P.Normal] (hP : IsPGroup 2 ↥P) : P ≤ center K := by
  classical
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  have hQn : (P.map C.π).Normal := Subgroup.Normal.map ‹P.Normal› C.π C.surj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map C.π) with h | h
  · rw [← C.ker]
    intro x hx
    have : C.π x ∈ P.map C.π := ⟨x, hx, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have h1 : Nat.card (P.map C.π) ∣ Nat.card P := Subgroup.card_map_dvd P C.π
    rw [h, Subgroup.card_top, hk, card_alternatingGroup_eq (by rw [Fintype.card_fin]; omega),
      Fintype.card_fin] at h1
    obtain ⟨m, hm⟩ : 6 ∣ n.factorial :=
      (show 6 ∣ Nat.factorial 3 by decide).trans (Nat.factorial_dvd_factorial (by omega))
    have h3 : 3 ∣ n.factorial / 2 := ⟨m, by omega⟩
    have h4 : 3 ∣ 2 ^ k := h3.trans h1
    have h5 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega

end Cover

section Misc

variable {X : Type} [Group X]

theorem ne_bot_of_isDoubleCoverOfAlt {E : Subgroup X} {m : ℕ}
    (h : IsDoubleCoverOfAlt (↥E ⧸ pPrimeCore 2 ↥E) m) : E ≠ ⊥ := by
  have hc : Nat.card (Subgroup.center (↥E ⧸ pPrimeCore 2 ↥E)) = 2 := h.2.1
  have hnt : Nontrivial (↥E ⧸ pPrimeCore 2 ↥E) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have h1 : Nat.card (Subgroup.center (↥E ⧸ pPrimeCore 2 ↥E)) = 1 :=
      Nat.card_of_subsingleton (1 : Subgroup.center (↥E ⧸ pPrimeCore 2 ↥E))
    omega
  have : Nontrivial ↥E := (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥E)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot E).1 this

end Misc

section Model

variable {X : Type} [Group X] {n : ℕ} {A : Subgroup X}

theorem AhatModel.perm_eq_one_of_commutator_central (hn : 8 ≤ n) (M : AhatModel X n A) {c : X}
    (hc : c ∈ normalizer (A : Set X))
    (h : ∀ y : M.K, M.autOf c hc y * y⁻¹ ∈ Subgroup.center M.K) : M.perm c hc = 1 := by
  apply M.perm_eq_of_induces hn hc
  refine ⟨fun y => ?_⟩
  have h1 : M.C.ρ (M.autOf c hc y * y⁻¹) = 1 := (M.C.ρ_eq_one_iff).2 (h y)
  rw [map_mul, map_inv] at h1
  simpa using mul_inv_eq_one.1 h1

end Model

end CFSG.OddStandard.Solomon75
