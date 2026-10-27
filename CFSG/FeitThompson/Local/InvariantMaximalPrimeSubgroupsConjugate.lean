module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Local.MaximalNormalizedPSubgroupSingletonTrivial
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup
import CFSG.FeitThompson.OddOrder.PGroupNormalizerCondition
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {q : ℕ}

theorem card_lt_card_of_lt [Finite G] {X Y : Subgroup G} (h : X < Y) :
    Nat.card X < Nat.card Y :=
  Set.Finite.card_lt_card (Set.toFinite _) (show (X : Set G) ⊂ (Y : Set G) from h)

theorem card_lt_card_inf_normalizer_of_isPGroup [Finite G] (hq : q.Prime) {P I : Subgroup G}
    (hP : IsPGroup q P) (hIP : I < P) :
    Nat.card I < Nat.card (P ⊓ normalizer (I : Set G) : Subgroup G) := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hJ : I.subgroupOf P < ⊤ :=
    lt_top_iff_ne_top.2 fun h => absurd (Subgroup.subgroupOf_eq_top.1 h) hIP.not_ge
  have hlt := lt_normalizer_of_natCard_eq_pow hq hn hJ
  rw [← Subgroup.subgroupOf_normalizer_eq hIP.le] at hlt
  have h1 := card_lt_card_of_lt hlt
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIP.le).toEquiv,
    ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : normalizer (I : Set G) ⊓ P ≤ P)).toEquiv] at h1
  rwa [inf_comm P (normalizer (I : Set G))]

private theorem exists_conj_inv_smul_eq_aux [Finite G] [IsSimpleGroup G]
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) :
    ∀ n : ℕ, ∀ Q₁ Q₂ H : Subgroup G, Nat.card G - Nat.card (Q₁ ⊓ Q₂ : Subgroup G) ≤ n →
      Q₁ ∈ maximalNormalizedPSubgroups A q → Q₂ ∈ maximalNormalizedPSubgroups A q →
      H < ⊤ → A ≤ H → (Q₁ ⊓ H : Subgroup G) ≠ ⊥ → (Q₂ ⊓ H : Subgroup G) ≠ ⊥ →
      ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ := by
  intro n
  induction n with
  | zero =>
    intro Q₁ Q₂ H hmeas _ _ _ _ _ _
    have htop : (Q₁ ⊓ Q₂ : Subgroup G) = ⊤ :=
      Subgroup.eq_top_of_le_card (H := (Q₁ ⊓ Q₂ : Subgroup G)) (by omega)
    have h1 : Q₁ = ⊤ := top_le_iff.1 (htop.ge.trans inf_le_left)
    have h2 : Q₂ = ⊤ := top_le_iff.1 (htop.ge.trans inf_le_right)
    exact ⟨1, one_mem _, by simp [h1, h2]⟩
  | succ n ih =>
    intro Q₁ Q₂ H hmeas hQ₁ hQ₂ hHtop hAH hn1 hn2
    by_cases hEq : Q₁ = Q₂
    · exact ⟨1, one_mem _, by simp [hEq]⟩
    set I : Subgroup G := Q₁ ⊓ Q₂
    have hIQ₁ : I < Q₁ := by
      refine inf_le_left.lt_of_ne fun h => hEq ?_
      exact (eq_of_mem_of_le hQ₁ (isPGroup_of_mem hQ₂) (le_normalizer_of_mem hQ₂)
        (h.ge.trans inf_le_right)).symm
    have hIQ₂ : I < Q₂ := by
      refine inf_le_right.lt_of_ne fun h => hEq ?_
      exact eq_of_mem_of_le hQ₂ (isPGroup_of_mem hQ₁) (le_normalizer_of_mem hQ₁)
        (h.ge.trans inf_le_left)
    obtain ⟨H', hH'top, hAH', hc1, hc2⟩ :
        ∃ H' : Subgroup G, H' < ⊤ ∧ A ≤ H' ∧
          Nat.card I < Nat.card (Q₁ ⊓ H' : Subgroup G) ∧
          Nat.card I < Nat.card (Q₂ ⊓ H' : Subgroup G) := by
      by_cases hIbot : I = ⊥
      · refine ⟨H, hHtop, hAH, ?_, ?_⟩
        · rw [hIbot, Subgroup.card_bot]
          exact (Subgroup.one_lt_card_iff_ne_bot _).2 hn1
        · rw [hIbot, Subgroup.card_bot]
          exact (Subgroup.one_lt_card_iff_ne_bot _).2 hn2
      · exact ⟨normalizer (I : Set G),
          normalizer_lt_top_of_isSimpleGroup (bot_lt_iff_ne_bot.2 hIbot) (hIQ₁.trans_le le_top),
          le_trans (le_inf (le_normalizer_of_mem hQ₁) (le_normalizer_of_mem hQ₂))
            Subgroup.inf_normalizer_le_normalizer_inf,
          card_lt_card_inf_normalizer_of_isPGroup hq (isPGroup_of_mem hQ₁) hIQ₁,
          card_lt_card_inf_normalizer_of_isPGroup hq (isPGroup_of_mem hQ₂) hIQ₂⟩
    have hn2' : (Q₂ ⊓ H' : Subgroup G) ≠ ⊥ :=
      (Subgroup.one_lt_card_iff_ne_bot _).1 (lt_of_le_of_lt Nat.card_pos hc2)
    obtain ⟨h, hh, Q₃, hQ₃, hb1, hb2⟩ :=
      exists_mem_inf_exists_mem_maximalNormalizedPSubgroups hsolv hAbot hAtop hcon hq hqπ hQ₁ hQ₂
        hH'top hAH'
    rw [Subgroup.mem_inf] at hh
    obtain ⟨hhK, hhH'⟩ := hh
    have hhA : MulAut.conj h⁻¹ • A = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1
        (inv_mem (Subgroup.centralizer_le_normalizer _
          (constrainedCentralizerCore_le_centralizer A hhK)))
    have hQ₁' : (MulAut.conj h⁻¹ • Q₁ : Subgroup G) ∈ maximalNormalizedPSubgroups A q :=
      smul_mem_maximalNormalizedPSubgroups hhA hQ₁
    have hsmulinf : (MulAut.conj h⁻¹ • (Q₁ ⊓ H') : Subgroup G) =
        (MulAut.conj h⁻¹ • Q₁ : Subgroup G) ⊓ H' := by
      rw [Subgroup.smul_inf, Subgroup.conj_smul_eq_self_of_mem (inv_mem hhH')]
    have hcardsmul : Nat.card (MulAut.conj h⁻¹ • (Q₁ ⊓ H') : Subgroup G) =
        Nat.card (Q₁ ⊓ H' : Subgroup G) := natCard_conj_smul _ _
    have hg1 : Nat.card I < Nat.card ((MulAut.conj h⁻¹ • Q₁ : Subgroup G) ⊓ Q₃ : Subgroup G) := by
      refine hc1.trans_le ?_
      rw [← hcardsmul]
      exact Subgroup.card_le_of_le hb1
    have hg3 : Nat.card I < Nat.card (Q₃ ⊓ Q₂ : Subgroup G) := by
      refine hc2.trans_le ?_
      rw [inf_comm Q₃ Q₂]
      exact Subgroup.card_le_of_le hb2
    have hnn1 : ((MulAut.conj h⁻¹ • Q₁ : Subgroup G) ⊓ H' : Subgroup G) ≠ ⊥ := by
      refine (Subgroup.one_lt_card_iff_ne_bot _).1 ?_
      rw [← hsmulinf, hcardsmul]
      exact lt_of_le_of_lt Nat.card_pos hc1
    have hnn3 : (Q₃ ⊓ H' : Subgroup G) ≠ ⊥ := by
      refine (Subgroup.one_lt_card_iff_ne_bot _).1
        (lt_of_lt_of_le (lt_of_le_of_lt Nat.card_pos hc2) (Subgroup.card_le_of_le ?_))
      exact le_inf (le_trans hb2 inf_le_right) inf_le_right
    obtain ⟨k₁, hk₁, hk₁eq⟩ := ih _ Q₃ H' (by omega) hQ₁' hQ₃ hH'top hAH' hnn1 hnn3
    obtain ⟨k₂, hk₂, hk₂eq⟩ := ih Q₃ Q₂ H' (by omega) hQ₃ hQ₂ hH'top hAH' hnn3 hn2'
    refine ⟨h * k₁ * k₂, mul_mem (mul_mem hhK hk₁) hk₂, ?_⟩
    calc MulAut.conj (h * k₁ * k₂)⁻¹ • Q₁
        = MulAut.conj k₂⁻¹ • (MulAut.conj k₁⁻¹ • (MulAut.conj h⁻¹ • Q₁ : Subgroup G)) := by
          rw [mul_inv_rev, mul_inv_rev, map_mul, map_mul, mul_smul, mul_smul]
      _ = Q₂ := by rw [hk₁eq, hk₂eq]

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq [Finite G] [IsSimpleGroup G]
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A Q₁ Q₂ H : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) (hHtop : H < ⊤) (hAH : A ≤ H)
    (hn1 : (Q₁ ⊓ H : Subgroup G) ≠ ⊥) (hn2 : (Q₂ ⊓ H : Subgroup G) ≠ ⊥) :
    ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ :=
  exists_conj_inv_smul_eq_aux hsolv hAbot hAtop hcon hq hqπ
    (Nat.card G - Nat.card (Q₁ ⊓ Q₂ : Subgroup G)) Q₁ Q₂ H le_rfl hQ₁ hQ₂ hHtop hAH hn1 hn2

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_odd [Finite G]
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (_hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A Q₁ Q₂ H : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) (hHtop : H < ⊤) (hAH : A ≤ H)
    (hn1 : (Q₁ ⊓ H : Subgroup G) ≠ ⊥) (hn2 : (Q₂ ⊓ H : Subgroup G) ≠ ⊥) :
    ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ :=
  have := hsimple
  exists_mem_constrainedCentralizerCore_conj_inv_smul_eq hsolv hAbot hAtop hcon hq hqπ hQ₁ hQ₂
    hHtop hAH hn1 hn2

theorem exists_mem_constrainedCentralizerCore_forall_mem_iff [Finite G] [IsSimpleGroup G]
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A Q₁ Q₂ H : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) (hHtop : H < ⊤) (hAH : A ≤ H)
    (hn1 : (Q₁ ⊓ H : Subgroup G) ≠ ⊥) (hn2 : (Q₂ ⊓ H : Subgroup G) ≠ ⊥) :
    ∃ k ∈ constrainedCentralizerCore A, ∀ x : G, x ∈ Q₂ ↔ k * x * k⁻¹ ∈ Q₁ := by
  obtain ⟨k, hk, hkeq⟩ := exists_mem_constrainedCentralizerCore_conj_inv_smul_eq hsolv hAbot hAtop
    hcon hq hqπ hQ₁ hQ₂ hHtop hAH hn1 hn2
  exact ⟨k, hk, fun x => by rw [← hkeq, mem_conj_inv_smul_iff]⟩

end

end CFSG.FeitThompson

