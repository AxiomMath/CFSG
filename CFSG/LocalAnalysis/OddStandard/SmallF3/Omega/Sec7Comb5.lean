module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped CharTwo

variable {G : Type} [Group G]

private def evec5 (i : Fin 5) : Fin 5 → ZMod 2 :=
  Pi.single i 1

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private lemma isEvenVec_add {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

private lemma isEvenVec_evec_add {i j : Fin 5} (_hij : i ≠ j) :
    IsEvenVec (evec5 i + evec5 j) := by
  have hi : (∑ k : Fin 5, evec5 i k) = 1 := by
    simp only [evec5]
    rw [Finset.sum_pi_single']
    simp
  have hj : (∑ k : Fin 5, evec5 j k) = 1 := by
    simp only [evec5]
    rw [Finset.sum_pi_single']
    simp
  unfold IsEvenVec
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hi, hj]
  decide

private lemma charTwo_add_add_self (a b : Fin 5 → ZMod 2) : a + (b + a) = b := by
  rw [add_comm b a, CharTwo.add_cancel_left]

theorem permVec_add (σ : Equiv.Perm (Fin 5)) (v w : Fin 5 → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := by
  funext i
  simp [permVec, Pi.add_apply]

private theorem isEvenVec_permVec {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (σ : Equiv.Perm (Fin 5)) :
    IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec at *
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ.symm v]
  exact hv

private lemma permVec_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    permVec (τ * σ) v = permVec τ (permVec σ v) := by
  funext i
  simp only [permVec, Function.comp_apply]
  congr 1

private lemma permVec_one {n : ℕ} (v : Fin n → ZMod 2) :
    permVec (1 : Equiv.Perm (Fin n)) v = v := by
  funext i
  simp [permVec, Equiv.Perm.one_def]

private lemma permVec_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permVec σ (0 : Fin n → ZMod 2) = 0 := by
  funext i
  simp [permVec]

private lemma permVec_evec5 (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    permVec σ (evec5 i) = evec5 (σ i) := by
  funext l
  simp only [permVec, Function.comp_apply, evec5, Pi.single_apply, Equiv.symm_apply_eq]

private lemma exists_perm_pair {j k a b : Fin 5} (hjk : j ≠ k) (hab : a ≠ b) :
    ∃ τ : Equiv.Perm (Fin 5), τ j = a ∧ τ k = b := by
  have h2 : MulAction.IsMultiplyPretransitive (Equiv.Perm (Fin 5)) (Fin 5) 2 :=
    Equiv.Perm.isMultiplyPretransitive (Fin 5) 2
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨τ, hτa, hτb⟩ := h2 hjk hab
  exact ⟨τ, by simpa [Equiv.Perm.smul_def] using hτa,
    by simpa [Equiv.Perm.smul_def] using hτb⟩

private lemma add_permVec_swap {v : Fin 5 → ZMod 2} {j k : Fin 5} (hjk : j ≠ k)
    (hvj : v j = 1) (hvk : v k = 0) :
    v + permVec (Equiv.swap j k) v = evec5 j + evec5 k := by
  funext l
  simp only [evec5, Pi.add_apply, permVec, Function.comp_apply, Equiv.symm_swap,
    Equiv.swap_apply_def]
  rcases eq_or_ne l j with rfl | hlj
  · rw [if_pos rfl, hvk]
    simp [hvj, Pi.single_eq_same, Pi.single_eq_of_ne hjk]
  · rcases eq_or_ne l k with rfl | hlk
    · rw [if_neg hlj, if_pos rfl, hvj]
      simp [hvk, Pi.single_eq_same, Pi.single_eq_of_ne hlj]
    · rw [if_neg hlj, if_neg hlk, Pi.single_eq_of_ne hlj, Pi.single_eq_of_ne hlk]
      exact CharTwo.add_self_eq_zero (v l)

private lemma exists_two_support {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hv0 : v ≠ 0) :
    ∃ i j : Fin 5, i ≠ j ∧ v i ≠ 0 ∧ v j ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext fun i => by simpa using h i)
  refine ⟨i, ?_⟩
  by_contra h
  have hji : ∀ j, i ≠ j → v j = 0 := by
    intro j hij
    by_contra hvj
    exact h ⟨j, hij, hi, hvj⟩
  have hsum : (∑ k, v k) = v i := by
    rw [Finset.sum_eq_single i]
    · intro b _ hb; exact hji b (Ne.symm hb)
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  change (∑ k, v k) = 0 at hv
  rw [hsum] at hv
  exact hi hv

private lemma evenVec_mem_of_evec_add (B : AddSubgroup (Fin 5 → ZMod 2))
    (hB : ∀ i j : Fin 5, i ≠ j → evec5 i + evec5 j ∈ B) :
    ∀ v : Fin 5 → ZMod 2, IsEvenVec v → v ∈ B := by
  intro v hv
  have key : ∀ (n : ℕ) (v : Fin 5 → ZMod 2), IsEvenVec v → vecWeight v = n → v ∈ B := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hw
      by_cases hv0 : v = 0
      · subst hv0
        exact B.zero_mem
      · obtain ⟨i, j, hij, hi, hj⟩ := exists_two_support hv hv0
        have hXeven : IsEvenVec (evec5 i + evec5 j) := isEvenVec_evec_add hij
        have hu_even : IsEvenVec (v + (evec5 i + evec5 j)) := isEvenVec_add hv hXeven
        have hlt : vecWeight (v + (evec5 i + evec5 j)) < vecWeight v := by
          have hsub : (Finset.univ.filter fun k => (v + (evec5 i + evec5 j)) k ≠ 0) ⊆
              (Finset.univ.filter fun k => v k ≠ 0).erase i := by
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            have hki : k ≠ i := by
              rintro rfl
              exact hk (by simp [Pi.add_apply, evec5, Pi.single_eq_same,
                zmod2_eq_one_of_ne_zero hi, Pi.single_eq_of_ne hij])
            have hkj : k ≠ j := by
              rintro rfl
              exact hk (by simp [Pi.add_apply, evec5, Pi.single_eq_same,
                zmod2_eq_one_of_ne_zero hj, Pi.single_eq_of_ne (Ne.symm hij)])
            exact ⟨hki, by simpa only [Pi.add_apply, evec5, Pi.single_eq_of_ne hki,
              Pi.single_eq_of_ne hkj, add_zero] using hk⟩
          have hcard : vecWeight (v + (evec5 i + evec5 j)) ≤ vecWeight v - 1 := by
            unfold vecWeight
            calc (Finset.univ.filter fun k => (v + (evec5 i + evec5 j)) k ≠ 0).card
                ≤ ((Finset.univ.filter fun k => v k ≠ 0).erase i).card :=
                  Finset.card_le_card hsub
              _ = (Finset.univ.filter fun k => v k ≠ 0).card - 1 :=
                  Finset.card_erase_of_mem (by simp [hi])
          have hpos : 0 < vecWeight v := by
            unfold vecWeight
            exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
          omega
        have hu_mem : v + (evec5 i + evec5 j) ∈ B :=
          ih (vecWeight (v + (evec5 i + evec5 j))) (by rw [← hw]; exact hlt)
            (v + (evec5 i + evec5 j)) hu_even rfl
        have hgen : evec5 i + evec5 j ∈ B := hB i j hij
        have hgoal : v = (evec5 i + evec5 j) + (v + (evec5 i + evec5 j)) :=
          (charTwo_add_add_self (evec5 i + evec5 j) v).symm
        rw [hgoal]
        exact B.add_mem hgen hu_mem
  exact key (vecWeight v) v hv rfl

theorem even_mem_closure_orbit {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hv0 : v ≠ 0)
    (hw : IsEvenVec w) :
    w ∈ AddSubgroup.closure (Set.range fun σ : Equiv.Perm (Fin 5) => permVec σ v) := by
  classical
  let W : AddSubgroup (Fin 5 → ZMod 2) :=
    AddSubgroup.closure (Set.range fun σ : Equiv.Perm (Fin 5) => permVec σ v)
  change w ∈ W
  have hgen : ∀ σ : Equiv.Perm (Fin 5), permVec σ v ∈ W := fun σ =>
    AddSubgroup.subset_closure ⟨σ, rfl⟩
  have hvW : v ∈ W := by
    simpa [permVec_one] using hgen 1
  have hinv : ∀ (τ : Equiv.Perm (Fin 5)) {x : Fin 5 → ZMod 2}, x ∈ W → permVec τ x ∈ W := by
    intro τ x hx
    refine AddSubgroup.closure_induction (p := fun x _ => permVec τ x ∈ W) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨σ, rfl⟩
      rw [← permVec_mul σ τ v]
      exact hgen (τ * σ)
    · rw [permVec_zero]
      exact W.zero_mem
    · intro x y _ _ ihx ihy
      rw [permVec_add]
      exact W.add_mem ihx ihy
    · intro x _ ihx
      rw [CharTwo.neg_eq]
      exact ihx
  have hjnz : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext fun j => by simpa using h j)
  obtain ⟨j, hj⟩ := hjnz
  have hkz : ∃ k, v k = 0 := by
    by_contra h
    push Not at h
    have h1 : ∀ i : Fin 5, v i = 1 := fun i => zmod2_eq_one_of_ne_zero (h i)
    have hsum : (∑ i : Fin 5, v i) = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => h1 i)]
      decide
    rw [IsEvenVec] at hv
    rw [hsum] at hv
    exact one_ne_zero hv
  obtain ⟨k, hk⟩ := hkz
  have hjk : j ≠ k := by rintro rfl; exact hj hk
  have hpair : evec5 j + evec5 k ∈ W := by
    have hswap := add_permVec_swap (v := v) (j := j) (k := k) hjk
      (zmod2_eq_one_of_ne_zero hj) hk
    rw [← hswap]
    exact W.add_mem hvW (hgen (Equiv.swap j k))
  have hbase : ∀ a b : Fin 5, a ≠ b → evec5 a + evec5 b ∈ W := by
    intro a b hab
    obtain ⟨τ, hτa, hτb⟩ := exists_perm_pair hjk hab
    have hconj : permVec τ (evec5 j + evec5 k) = evec5 a + evec5 b := by
      rw [permVec_add, permVec_evec5, permVec_evec5, hτa, hτb]
    rw [← hconj]
    exact hinv τ hpair
  exact evenVec_mem_of_evec_add W hbase w hw

private lemma permModule_map_zero {n : ℕ} {φ : (Fin n → ZMod 2) → G} {E H : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin n))} (h : IsPermModuleVia IsEvenVec φ E H Alt) :
    φ 0 = 1 := by
  have hz : IsEvenVec (0 : Fin n → ZMod 2) := by unfold IsEvenVec; simp
  have hmul : φ 0 * φ 0 = φ 0 := by
    simpa using (h.1 0 0 hz hz).symm
  exact mul_eq_right.mp hmul

theorem closure_conj_eq_of_permModule {φ : (Fin 5 → ZMod 2) → G} {E N : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ E N ⊤) (hN : N ≤ normalizer (E : Set G)) {z : G}
    (hz : z ∈ E) (hz1 : z ≠ 1) : E = Subgroup.closure (conjClassIn N z) := by
  classical
  let C : Set G := conjClassIn N z
  obtain ⟨v₀, hv₀, hv₀φ⟩ := (h.2.2.1 z).mp hz
  have hv₀0 : v₀ ≠ 0 := by
    intro h0
    apply hz1
    rw [← hv₀φ, h0, permModule_map_zero h]
  have hz0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by unfold IsEvenVec; simp
  have hE_le : E ≤ Subgroup.closure C := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (h.2.2.1 x).mp hx
    have hu_mem := even_mem_closure_orbit hv₀ hv₀0 hu
    exact (AddSubgroup.closure_induction
      (p := fun u _ => IsEvenVec u ∧ φ u ∈ Subgroup.closure C)
      (fun u huS => by
        obtain ⟨σ, rfl⟩ := huS
        refine ⟨isEvenVec_permVec hv₀ σ, ?_⟩
        obtain ⟨n, hn, hnσ⟩ := h.2.2.2.2 σ (by simp)
        exact Subgroup.subset_closure ⟨n, hn, by rw [← hnσ v₀ hv₀, hv₀φ]⟩)
      ⟨hz0, by rw [permModule_map_zero h]; exact Subgroup.one_mem _⟩
      (fun x y _ _ ihx ihy => ⟨isEvenVec_add ihx.1 ihy.1, by
        rw [h.1 x y ihx.1 ihy.1]; exact Subgroup.mul_mem _ ihx.2 ihy.2⟩)
      (fun x _ ihx => by rw [CharTwo.neg_eq x]; exact ihx)
      hu_mem).2
  have hcl_le : Subgroup.closure C ≤ E := by
    apply (Subgroup.closure_le E).mpr
    rintro x ⟨n, hn, rfl⟩
    exact (mem_normalizer_iff.mp (hN hn) z).mp hz
  exact le_antisymm hE_le hcl_le

end CFSG.OddStandard.SmallF3.Omega
