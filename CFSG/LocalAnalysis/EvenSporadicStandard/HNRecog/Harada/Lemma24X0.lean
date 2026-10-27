module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup
open scoped Pointwise

private theorem factorization_480_two : (480 : ℕ).factorization 2 = 5 := by
  have h : (480 : ℕ) = 2 ^ 5 * 15 := by norm_num
  rw [h, Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime (2 ^ 5) 15),
    Nat.factorization_pow_self (by decide : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 15)]

theorem exists_largest_perfect (Q : Type*) [Group Q] [Finite Q] :
    ∃ X : Subgroup Q, X.Normal ∧ ⁅X, X⁆ = X ∧ ∀ M : Subgroup Q, ⁅M, M⁆ = M → M ≤ X := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (derivedSeries_antitone (G := Q))
  refine ⟨derivedSeries Q n, derivedSeries_normal (G := Q) n, ?_, ?_⟩
  · have h := hn (n + 1) (Nat.le_succ n)
    rw [derivedSeries_succ] at h
    exact h.symm
  · intro M hM
    have hMle : ∀ k, M ≤ derivedSeries Q k := by
      intro k
      induction k with
      | zero => exact le_top
      | succ k ih =>
        rw [derivedSeries_succ]
        calc M = ⁅M, M⁆ := hM.symm
          _ ≤ ⁅derivedSeries Q k, derivedSeries Q k⁆ := Subgroup.commutator_mono ih ih
    exact hMle n

theorem le_of_isPGroup_of_normal {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    {X S : Subgroup Q} (hX : X.Normal) (hSX : S ≤ X) (hS : IsPGroup p S)
    (hmax : ∀ R : Subgroup Q, IsPGroup p R → Nat.card R ≤ Nat.card S) :
    ∀ R : Subgroup Q, IsPGroup p R → R ≤ X := by
  have hcardS : Nat.card S = p ^ (Nat.card Q).factorization p := by
    obtain ⟨P, hSP⟩ := hS.exists_le_sylow
    have hle : Nat.card S ≤ Nat.card P := Subgroup.card_le_of_le hSP
    have hP : Nat.card P = p ^ (Nat.card Q).factorization p := P.card_eq_multiplicity
    have hge : p ^ (Nat.card Q).factorization p ≤ Nat.card S := by
      rw [← hP]
      exact hmax P.1 P.isPGroup'
    exact le_antisymm (hP ▸ hle) hge
  let P₀ : Sylow p Q := Sylow.ofCard S hcardS
  have hP₀ : (P₀ : Subgroup Q) = S := Sylow.coe_ofCard S hcardS
  intro R hR
  obtain ⟨P₁, hRP₁⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P₀ P₁
  have hconjS : (MulAut.conj g • S : Subgroup Q) ≤ X := by
    intro x hx
    obtain ⟨s, hs, hsm⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) S).mp hx
    rw [← hsm]
    simpa using hX.conj_mem s (hSX hs) g
  have hP₁eq : (P₁ : Subgroup Q) = MulAut.conj g • S := by
    rw [← hg, Sylow.coe_subgroup_smul, hP₀]
  exact (hRP₁.trans (le_of_eq hP₁eq)).trans hconjS

theorem le_of_card_eq_480 {Q : Type*} [Group Q] [Finite Q] {X C M : Subgroup Q}
    (h2 : ∀ R : Subgroup Q, IsPGroup 2 R → R ≤ X) (hC : Nat.card C = 480) (hMC : M ≤ C)
    (hMX : M ≤ X) (hM : Nat.card M = 60) : C ≤ X := by
  have h60 : 60 ∣ Nat.card ↥(C ⊓ X) := by
    have hle : M ≤ C ⊓ X := le_inf hMC hMX
    have h := Subgroup.card_dvd_of_le hle
    rwa [hM] at h
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 C))
  have hScard : Nat.card S = 32 := by
    rw [Sylow.card_eq_multiplicity, hC, factorization_480_two]
    norm_num
  have h32 : 32 ∣ Nat.card ↥(C ⊓ X) := by
    have hle : S.1.map C.subtype ≤ C ⊓ X :=
      le_inf (Subgroup.map_subtype_le S.1) (h2 _ (S.isPGroup'.map C.subtype))
    have hcard : Nat.card (S.1.map C.subtype) = 32 := by
      rw [Subgroup.card_subtype, hScard]
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hdvd : 480 ∣ Nat.card ↥(C ⊓ X) := by
    have h := Nat.lcm_dvd h32 h60
    norm_num at h
    exact h
  have hle480 : Nat.card ↥(C ⊓ X) ≤ 480 := by
    have h := Subgroup.card_le_of_le (H := C ⊓ X) (K := C) inf_le_left
    rwa [hC] at h
  have hcardD : Nat.card ↥(C ⊓ X) = 480 := by
    have hpos : 0 < Nat.card ↥(C ⊓ X) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, (C ⊓ X).one_mem⟩⟩, inferInstance⟩
    exact le_antisymm hle480 (Nat.le_of_dvd hpos hdvd)
  have heq : C ⊓ X = C := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardD, hC])
  rw [← heq]
  exact inf_le_right

end CFSG.EvenSporadicStandard.HNRecog.Harada
