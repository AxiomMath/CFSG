module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.TwoGroup

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem swap_package [Finite G] (hLB : LayerBalanceAt G) (hglaub : GlaubermanSimplePerfect)
    {B : Subgroup G} (hB : MaximalF B) {z y : G} {M : Subgroup G} (hz : GoodInv B z)
    (hS : SwapConfig B z y M) (hM : MaximalF M) {P : Subgroup G}
    (hPy : P ≤ centralizer ({y} : Set G)) (hPB : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p)
    (hPz : ∀ p ∈ P, p * z = z * p) (hzP : z ∈ P) :
    (P ⊓ normalizer (M : Set G)).relIndex P = 2 ∧
      ∀ r ∈ P ⊓ normalizer (M : Set G), orderOf r = 2 →
        BadInv B r ∧ IsCompIn M (centralizer ({r} : Set G)) ∧
          IsCompIn (cj z M) (centralizer ({r} : Set G)) := by
  refine ⟨hS.relIndex_normalizer_eq_two hPy hPB hzP, ?_⟩
  intro r hr hr2
  have hrP : r ∈ P := hr.1
  have hrN : r ∈ normalizer (M : Set G) := hr.2
  have hrB : ∀ b ∈ B, r * b = b * r := hPB r hrP
  have hrM : ∀ m ∈ M, r * m = m * r := (hS.centralizes_of_mem_normalizer hrN hrB).1
  have hrz : r * z = z * r := hPz r hrP
  have hry : r * y = y * r := Subgroup.mem_centralizer_singleton_iff.1 (hPy hrP)
  exact involution_bad_and_isCompIn hLB hglaub hB hz hS hM hr2 hrz hry hrM

theorem false_of_four_components [Finite G] {X B M N M' N' : Subgroup G}
    (hB : ¬ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hM : IsCompIn M X) (hN : IsCompIn N X) (hM' : IsCompIn M' X) (hN' : IsCompIn N' X)
    (h1 : M' ≠ M) (h2 : M' ≠ N) (h3 : N' ≠ M) (h4 : N' ≠ N)
    (hBMN : B ≤ M ⊔ N) (hBMN' : B ≤ M' ⊔ N') : False := by
  apply hB
  intro b hb b' hb'
  have hM'c : M' ≤ centralizer ({b} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_le_sup_of_ne hM hN hM' h1 h2 hBMN b hb l hl).symm
  have hN'c : N' ≤ centralizer ({b} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_le_sup_of_ne hM hN hN' h3 h4 hBMN b hb l hl).symm
  have hb'' : b' ∈ centralizer ({b} : Set G) := (sup_le hM'c hN'c) (hBMN' hb')
  exact (Subgroup.mem_centralizer_singleton_iff.1 hb'').symm

theorem false_of_commuting_bad_pair [Finite G] (hLB : LayerBalanceAt G)
    (hglaub : GlaubermanSimplePerfect) {B : Subgroup G} (hB : MaximalF B) {z y y' : G}
    (hz : GoodInv B z) (hy : BadInv B y) (hy' : BadInv B y') (hw : GoodInv B (y * y'))
    {P : Subgroup G} (hP : IsPGroup 2 P) (h8 : 8 ≤ Nat.card P)
    (hPB : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p) (hzP : z ∈ P) (hPz : ∀ p ∈ P, p * z = z * p)
    (hyP : y ∈ P) (hy'P : y' ∈ P) (hPy : ∀ p ∈ P, p * y = y * p)
    (hPy' : ∀ p ∈ P, p * y' = y' * p) : False := by
  have hzy : z * y = y * z := (hPz y hyP).symm
  have hzy' : z * y' = y' * z := (hPz y' hy'P).symm
  obtain ⟨M, hS, hM, -⟩ := exists_swapConfig hLB hglaub hB hz hy hzy
  obtain ⟨M', hS', hM', -⟩ := exists_swapConfig hLB hglaub hB hz hy' hzy'
  have hPyc : P ≤ centralizer ({y} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hPy p hp)
  have hPy'c : P ≤ centralizer ({y'} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hPy' p hp)
  obtain ⟨hRi, hRinv⟩ := swap_package hLB hglaub hB hz hS hM hPyc hPB hPz hzP
  obtain ⟨hR'i, hR'inv⟩ := swap_package hLB hglaub hB hz hS' hM' hPy'c hPB hPz hzP
  have hyN : y ∈ normalizer (M : Set G) :=
    mem_normalizer_of_centralizes fun m hm =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hS.isCompIn.1 hm)).symm
  have hyR : y ∈ P ⊓ normalizer (M : Set G) := ⟨hyP, hyN⟩
  have hy'notR : y' ∉ P ⊓ normalizer (M : Set G) := by
    intro hy'R
    have hyy'R : y * y' ∈ P ⊓ normalizer (M : Set G) :=
      (P ⊓ normalizer (M : Set G)).mul_mem hyR hy'R
    exact (hRinv (y * y') hyy'R hw.1).1.not_goodInv hw
  have hM'neM : M' ≠ M := by
    intro hEq
    apply hy'notR
    refine ⟨hy'P, ?_⟩
    rw [← hEq]
    exact mem_normalizer_of_centralizes (M := M') fun m hm =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hS'.isCompIn.1 hm)).symm
  have hM'neCj : M' ≠ cj z M := by
    intro hEq
    apply hy'notR
    refine ⟨hy'P, ?_⟩
    have hzy'conj : z * y' * z⁻¹ = y' := by rw [hzy']; group
    have h1 : cj z (centralizer ({y'} : Set G)) = centralizer ({y'} : Set G) := by
      rw [cj_centralizer_singleton z y', hzy'conj]
    have h2 : cj z M' ≤ centralizer ({y'} : Set G) := h1 ▸ cj_mono z hS'.isCompIn.1
    rw [hEq, cj_cj_of_mul_self hS.x_mul_self M] at h2
    exact mem_normalizer_of_centralizes (M := M) fun m hm =>
      (Subgroup.mem_centralizer_singleton_iff.1 (h2 hm)).symm
  have hCjM'neM : cj z M' ≠ M := by
    intro hEq
    apply hM'neCj
    have h := congrArg (cj z) hEq
    rw [cj_cj_of_mul_self hS'.x_mul_self M'] at h
    exact h
  have hCjM'neCj : cj z M' ≠ cj z M := by
    intro hEq
    apply hM'neM
    have h := congrArg (cj z) hEq
    rw [cj_cj_of_mul_self hS'.x_mul_self M', cj_cj_of_mul_self hS.x_mul_self M] at h
    exact h
  obtain ⟨w, hwRR', hw2⟩ :=
    exists_involution_inf (R := P ⊓ normalizer (M : Set G))
      (R' := P ⊓ normalizer (M' : Set G)) hP h8 inf_le_left inf_le_left hRi hR'i
  have hMw : IsCompIn M (centralizer ({w} : Set G)) := (hRinv w hwRR'.1 hw2).2.1
  have hCjw : IsCompIn (cj z M) (centralizer ({w} : Set G)) := (hRinv w hwRR'.1 hw2).2.2
  have hM'w : IsCompIn M' (centralizer ({w} : Set G)) := (hR'inv w hwRR'.2 hw2).2.1
  have hCj'w : IsCompIn (cj z M') (centralizer ({w} : Set G)) :=
    (hR'inv w hwRR'.2 hw2).2.2
  exact false_of_four_components (X := centralizer ({w} : Set G)) (IsCompIn.not_commute hz.2)
    hMw hCjw hM'w hCj'w hM'neM hM'neCj hCjM'neM hCjM'neCj hS.le_sup hS'.le_sup

end CFSG.EvenSporadicStandard.Induction.ThmU
