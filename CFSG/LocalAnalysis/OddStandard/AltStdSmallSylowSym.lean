module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmallSylow
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.AltStdSmall

open Equiv Equiv.Perm Subgroup

section PermSym

variable {α : Type*} [DecidableEq α]

theorem apply_mem_pair_of_commute_swap {w : Perm α} {x y : α} (hxy : x ≠ y)
    (hw : w * swap x y = swap x y * w) :
    (w x = x ∧ w y = y) ∨ (w x = y ∧ w y = x) := by
  have h1 : swap (w x) (w y) = swap x y := by
    rw [swap_apply_apply, hw, mul_inv_cancel_right]
  have hwxy : w x ≠ w y := fun h => hxy (w.injective h)
  have hx : w x = x ∨ w x = y := by
    by_contra hne
    push Not at hne
    have h2 := congrArg (fun f : Perm α => f (w x)) h1
    simp only [swap_apply_left] at h2
    rw [swap_apply_of_ne_of_ne hne.1 hne.2] at h2
    exact hwxy h2.symm
  have hy : w y = x ∨ w y = y := by
    by_contra hne
    push Not at hne
    have h2 := congrArg (fun f : Perm α => f (w y)) h1
    simp only [swap_apply_right] at h2
    rw [swap_apply_of_ne_of_ne hne.1 hne.2] at h2
    exact hwxy h2
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.trans hy.symm) hwxy
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (hx.trans hy.symm) hwxy

end PermSym

section SylowSym

variable {n : ℕ}

def pairA (hn : 8 ≤ n) (i : Fin 4) : Fin n := ⟨2 * i, by have := i.isLt; omega⟩

def pairB (hn : 8 ≤ n) (i : Fin 4) : Fin n := ⟨2 * i + 1, by have := i.isLt; omega⟩

def pairSwap (hn : 8 ≤ n) (i : Fin 4) : Perm (Fin n) := swap (pairA hn i) (pairB hn i)

theorem pairA_ne_pairB (hn : 8 ≤ n) (i j : Fin 4) : pairA hn i ≠ pairB hn j := by
  simp only [pairA, pairB, ne_eq, Fin.mk.injEq]
  omega

theorem pairSwap_commute (hn : 8 ≤ n) (i j : Fin 4) :
    Commute (pairSwap hn i) (pairSwap hn j) := by
  by_cases hij : i = j
  · rw [hij]
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    apply Equiv.Perm.Disjoint.commute
    intro x
    by_cases hx : x = pairA hn i ∨ x = pairB hn i
    · right
      have h1 : x ≠ pairA hn j := by
        rcases hx with rfl | rfl <;> simp only [pairA, pairB, ne_eq, Fin.mk.injEq] <;> omega
      have h2 : x ≠ pairB hn j := by
        rcases hx with rfl | rfl <;> simp only [pairA, pairB, ne_eq, Fin.mk.injEq] <;> omega
      exact swap_apply_of_ne_of_ne h1 h2
    · left
      push Not at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem isPGroup_closure_pairSwap (hn : 8 ≤ n) :
    IsPGroup 2 (closure (Set.range (pairSwap hn))) := by
  have hcomm : (Set.range (pairSwap hn)).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact pairSwap_commute hn i j
  have hab := Subgroup.isMulCommutative_closure hcomm
  have hsq : ∀ x ∈ closure (Set.range (pairSwap hn)), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact swap_mul_self _ _
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := by
        have := hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ihx, inv_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  exact Subtype.ext (hsq g g.2)

theorem eq_of_mem_center_sylow_sym (hn8 : 8 ≤ n) (hn9 : n ≤ 9) {P : Subgroup (Perm (Fin n))}
    (hP : IsPGroup 2 P) (hcard : 2 ^ 7 ∣ Nat.card P) {w w' : Perm (Fin n)} (hw : w ∈ P)
    (hw' : w' ∈ P) (hwc : ∀ p ∈ P, w * p = p * w) (hw'c : ∀ p ∈ P, w' * p = p * w')
    (hw1 : w ≠ 1) (hw'1 : w' ≠ 1) : w = w' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hEP₀⟩ := (isPGroup_closure_pairSwap hn8).exists_le_sylow
  obtain ⟨P₁, hPP₁⟩ := hP.exists_le_sylow
  have hP₁card : Nat.card P₁ ∣ 2 ^ 7 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P₁.isPGroup'
    have hdvd : Nat.card (P₁ : Subgroup (Perm (Fin n))) ∣ Nat.card (Perm (Fin n)) :=
      card_subgroup_dvd_card _
    rw [hk, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
    rw [hk]
    refine Nat.pow_dvd_pow 2 ?_
    by_contra hk7
    have h8 : 2 ^ 8 ∣ n.factorial := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    interval_cases n <;> revert h8 <;> decide
  have hPeq : P = P₁ := Subgroup.eq_of_le_of_card_ge hPP₁
    (Nat.le_of_dvd (Nat.card_pos) (hP₁card.trans hcard))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin n)) P₀ P₁
  have hmem : ∀ x ∈ (P₀ : Subgroup (Perm (Fin n))), g * x * g⁻¹ ∈ P := by
    intro x hx
    rw [hPeq, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hx, rfl⟩
  set a : Fin 4 → Fin n := fun i => g (pairA hn8 i) with ha
  set b : Fin 4 → Fin n := fun i => g (pairB hn8 i) with hb
  have hab : ∀ i j, a i ≠ b j := fun i j h => pairA_ne_pairB hn8 i j (g.injective h)
  have hσP : ∀ i, swap (a i) (b i) ∈ P := by
    intro i
    rw [ha, hb, swap_apply_apply]
    exact hmem _ (hEP₀ (subset_closure ⟨i, rfl⟩))
  have houtside : ∀ k : Fin n, (∀ i, k ≠ a i ∧ k ≠ b i) → ((g⁻¹ k : Fin n) : ℕ) = 8 := by
    intro k hk
    by_contra hne
    have hlt : ((g⁻¹ k : Fin n) : ℕ) < 8 := by
      have := (g⁻¹ k).isLt
      by_contra hge
      omega
    set c : Fin n := g⁻¹ k with hc
    have hk' : k = g c := by rw [hc]; exact (Equiv.apply_symm_apply g k).symm
    set i : Fin 4 := ⟨(c : ℕ) / 2, by omega⟩
    rcases Nat.even_or_odd (c : ℕ) with ⟨m, hm⟩ | ⟨m, hm⟩
    · apply (hk i).1
      rw [hk', ha]
      congr 1
      ext
      simp only [pairA, i]
      omega
    · apply (hk i).2
      rw [hk', hb]
      congr 1
      ext
      simp only [pairB, i]
      omega
  have hdescr : ∀ v ∈ P, (∀ p ∈ P, v * p = p * v) → v ≠ 1 →
      (∀ i, v (a i) = b i ∧ v (b i) = a i) ∧ ∀ k : Fin n, (∀ i, k ≠ a i ∧ k ≠ b i) → v k = k := by
    intro v hv hvc hv1
    have hpair : ∀ i, (v (a i) = a i ∧ v (b i) = b i) ∨ (v (a i) = b i ∧ v (b i) = a i) :=
      fun i => apply_mem_pair_of_commute_swap (hab i i) (hvc _ (hσP i))
    have hfix : ∀ k : Fin n, (∀ i, k ≠ a i ∧ k ≠ b i) → v k = k := by
      intro k hk
      have hvk : ∀ i, v k ≠ a i ∧ v k ≠ b i := by
        intro i
        rcases hpair i with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨fun h => (hk i).1 (v.injective (h.trans h1.symm)),
            fun h => (hk i).2 (v.injective (h.trans h2.symm))⟩
        · exact ⟨fun h => (hk i).2 (v.injective (h.trans h2.symm)),
            fun h => (hk i).1 (v.injective (h.trans h1.symm))⟩
      have e1 := houtside k hk
      have e2 := houtside (v k) hvk
      have : g⁻¹ (v k) = g⁻¹ k := Fin.ext (e2.trans e1.symm)
      exact g⁻¹.injective this
    have hv2 : v * v = 1 := by
      ext k
      simp only [Perm.coe_mul, Function.comp_apply, Perm.coe_one, id_eq]
      by_cases hk : ∀ i, k ≠ a i ∧ k ≠ b i
      · rw [hfix k hk, hfix k hk]
      · push Not at hk
        obtain ⟨i, hi⟩ := hk
        by_cases hka : k = a i
        · subst hka
          rcases hpair i with ⟨h1, -⟩ | ⟨h1, h2⟩
          · rw [h1, h1]
          · rw [h1, h2]
        · have hkb := hi hka
          subst hkb
          rcases hpair i with ⟨-, h2⟩ | ⟨h1, h2⟩
          · rw [h2, h2]
          · rw [h2, h1]
    have hsupp := support_card_eq_eight_of_comm_sym (by rw [Fintype.card_fin]; exact hn8)
      (by rw [Fintype.card_fin]; exact hn9) hcard hv2 hv1 (fun p hp => (hvc p hp).symm)
    refine ⟨fun i => ?_, hfix⟩
    rcases hpair i with ⟨h1, h2⟩ | h
    · exfalso
      have hsub : v.support ⊆ (Finset.univ.erase (a i)).erase (b i) := by
        intro k hk
        rw [mem_support] at hk
        refine Finset.mem_erase.2 ⟨fun h => hk (h ▸ h2), Finset.mem_erase.2
          ⟨fun h => hk (h ▸ h1), Finset.mem_univ _⟩⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨(hab i i).symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        hsupp] at this
      omega
    · exact h
  obtain ⟨hw1', hw2'⟩ := hdescr w hw hwc hw1
  obtain ⟨hv1', hv2'⟩ := hdescr w' hw' hw'c hw'1
  ext k
  by_cases hk : ∀ i, k ≠ a i ∧ k ≠ b i
  · rw [hw2' k hk, hv2' k hk]
  · push Not at hk
    obtain ⟨i, hi⟩ := hk
    by_cases hka : k = a i
    · rw [hka, (hw1' i).1, (hv1' i).1]
    · rw [hi hka, (hw1' i).2, (hv1' i).2]

end SylowSym

end CFSG.OddStandard.AltStdSmall
