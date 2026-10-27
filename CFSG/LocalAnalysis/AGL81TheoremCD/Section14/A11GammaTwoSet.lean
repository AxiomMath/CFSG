module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExtOne
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingPlaneCore

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α]

private def tc (a b c : α) : Perm α := swap a b * swap b c

private lemma tc_apply_a {a b c : α} (hab : a ≠ b) (hac : a ≠ c) :
    tc a b c a = b := by
  simp [tc, Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hab hac, swap_apply_left]

private lemma tc_apply_b {a b c : α} (hac : a ≠ c) (hbc : b ≠ c) :
    tc a b c b = c := by
  simp [tc, Equiv.Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm]

private lemma tc_apply_of_ne {a b c x : α} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    tc a b c x = x := by
  simp [tc, Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxc,
    swap_apply_of_ne_of_ne hxa hxb]

private lemma tc_support {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (tc a b c).support = {a, b, c} := by
  rw [tc, Equiv.Perm.support_swap_mul_swap]
  simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

private lemma tc_isThreeCycle {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (tc a b c).IsThreeCycle := by
  rw [← card_support_eq_three_iff, tc_support hab hac hbc]
  simp [hab, hac, hbc]

private lemma tc_conj (σ : Perm α) (a b c : α) :
    σ * tc a b c * σ⁻¹ = tc (σ a) (σ b) (σ c) := by
  simp only [tc, Equiv.swap_apply_apply]
  group

private lemma threeCycle_inv_eq_sq {g : Perm α} (hg : g.IsThreeCycle) : g⁻¹ = g * g := by
  apply inv_eq_of_mul_eq_one_left (a := g * g) (b := g)
  have h3 : g ^ 3 = 1 := by simpa [hg.orderOf] using pow_orderOf_eq_one g
  simpa [pow_succ, pow_two] using h3

private lemma threeCycle_eq_of_agree {g g' : Perm α} (hg : g.IsThreeCycle)
    (hg' : g'.IsThreeCycle) (hss : g.support = g'.support) {a : α}
    (ha : a ∈ g.support) (hga : g' a = g a) : g = g' := by
  have ha' : a ∈ g'.support := by rwa [← hss]
  have hsupp := hg.support_eq_iff_mem_support.mpr ha
  have hnd' := hg'.nodup_iff_mem_support.mpr ha'
  have hg'ga : g' (g a) = g (g a) := by
    have h1 : g' (g a) ∈ g'.support := (Equiv.Perm.apply_mem_support).2
      (by simpa [hga] using (Equiv.Perm.apply_mem_support).2 ha')
    have h2 : g' (g a) ∉ ({a, g a} : Finset α) := by
      rw [hga] at hnd'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      have hnd'' : (¬a = g a ∧ ¬a = g' (g a)) ∧ ¬g a = g' (g a) := by simpa using hnd'
      exact ⟨fun h => hnd''.1.2 h.symm, fun h => hnd''.2 h.symm⟩
    rw [← hss] at h1
    rw [hsupp] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h1a | h1b | h1c
    · exact (h2 (by simp [h1a])).elim
    · exact (h2 (by simp [h1b])).elim
    · exact h1c
  have hg'form : g' = swap a (g a) * swap (g a) (g (g a)) := by
    calc
      g' = swap a (g' a) * swap (g' a) (g' (g' a)) :=
        hg'.eq_swap_mul_swap_iff_mem_support.mpr ha'
      _ = swap a (g a) * swap (g a) (g (g a)) := by rw [hga, hg'ga]
  have hgform : g = swap a (g a) * swap (g a) (g (g a)) :=
    hg.eq_swap_mul_swap_iff_mem_support.mpr ha
  exact hgform.trans hg'form.symm

private lemma threeCycle_eq_or_eq_inv_of_support_eq {g g' : Perm α}
    (hg : g.IsThreeCycle) (hg' : g'.IsThreeCycle) (hss : g.support = g'.support) :
    g = g' ∨ g = g'⁻¹ := by
  have hne : (g.support : Finset α).Nonempty := by
    rw [← Finset.card_pos, hg.card_support]
    norm_num
  obtain ⟨a, ha⟩ := hne
  have ha' : a ∈ g'.support := by rwa [← hss]
  by_cases h : g' a = g a
  · left
    exact threeCycle_eq_of_agree hg hg' hss ha h
  · right
    have hg'a : g' a = g (g a) := by
      have h1 : g' a ∈ g'.support := (Equiv.Perm.apply_mem_support).2 ha'
      have h2 : g' a ≠ a := by simpa [Equiv.Perm.mem_support] using ha'
      rw [← hss] at h1
      have hsupp := hg.support_eq_iff_mem_support.mpr ha
      rw [hsupp] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with h1a | h1b | h1c
      · exact (h2 h1a).elim
      · exact (h h1b).elim
      · exact h1c
    have hg'a2 : g⁻¹ a = g (g a) := by
      rw [threeCycle_inv_eq_sq hg]
      rfl
    have hg' : g' = g⁻¹ := by
      exact threeCycle_eq_of_agree hg' hg.inv
        (by rw [Equiv.Perm.support_inv, hss])
        (by simpa [Equiv.Perm.support_inv, hss] using ha') (hg'a2.trans hg'a.symm)
    rw [hg']
    simp

private def pairThreeCycles (u v : α) : Set (Perm α) :=
  {g | g.IsThreeCycle ∧ u ∈ g.support ∧ v ∈ g.support}

private lemma conj_mem_pairClosure {u v : α} {σ τ : Perm α}
    (hσ : σ ∈ Subgroup.closure (pairThreeCycles u v))
    (hτ : τ ∈ Subgroup.closure (pairThreeCycles u v)) :
    σ * τ * σ⁻¹ ∈ Subgroup.closure (pairThreeCycles u v) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hτ) (Subgroup.inv_mem _ hσ)

private lemma tc_mem_pairClosure {u v k : α} (huv : u ≠ v) (huk : u ≠ k) (hvk : v ≠ k) :
    tc u v k ∈ Subgroup.closure (pairThreeCycles u v) := by
  apply Subgroup.subset_closure
  refine ⟨tc_isThreeCycle huv huk hvk, ?_, ?_⟩
  · rw [tc_support huv huk hvk]; simp
  · rw [tc_support huv huk hvk]; simp

private lemma tc_v_mem_pairClosure {u v p q : α} (huv : u ≠ v)
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (hpq : p ≠ q) :
    tc v p q ∈ Subgroup.closure (pairThreeCycles u v) := by
  have hσ : tc u v p ∈ Subgroup.closure (pairThreeCycles u v) :=
    tc_mem_pairClosure huv (Ne.symm hpu) (Ne.symm hpv)
  have hτ : tc u v q ∈ Subgroup.closure (pairThreeCycles u v) :=
    tc_mem_pairClosure huv (Ne.symm hqu) (Ne.symm hqv)
  have hconj := tc_conj (tc u v p) u v q
  have h1 : tc u v p u = v := tc_apply_a huv (Ne.symm hpu)
  have h2 : tc u v p v = p := tc_apply_b (Ne.symm hpu) (Ne.symm hpv)
  have h3 : tc u v p q = q := tc_apply_of_ne hqu hqv (Ne.symm hpq)
  rw [h1, h2, h3] at hconj
  rw [← hconj]
  exact conj_mem_pairClosure hσ hτ

private lemma tc_u_mem_pairClosure {u v p q c : α} (huv : u ≠ v)
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (hpq : p ≠ q)
    (hcu : c ≠ u) (hcv : c ≠ v) (hcp : c ≠ p) (hcq : c ≠ q) :
    tc u p q ∈ Subgroup.closure (pairThreeCycles u v) := by
  have hσ : tc v p c ∈ Subgroup.closure (pairThreeCycles u v) :=
    tc_v_mem_pairClosure huv hpu hpv hcu hcv (Ne.symm hcp)
  have hτ : tc u v q ∈ Subgroup.closure (pairThreeCycles u v) :=
    tc_mem_pairClosure huv (Ne.symm hqu) (Ne.symm hqv)
  have hconj := tc_conj (tc v p c) u v q
  have h1 : tc v p c u = u :=
    tc_apply_of_ne huv (Ne.symm hpu) (Ne.symm hcu)
  have h2 : tc v p c v = p := tc_apply_a (Ne.symm hpv) (Ne.symm hcv)
  have h3 : tc v p c q = q := tc_apply_of_ne hqv (Ne.symm hpq) (Ne.symm hcq)
  rw [h1, h2, h3] at hconj
  rw [← hconj]
  exact conj_mem_pairClosure hσ hτ

private lemma tc_general_mem_pairClosure {u v a b c d : α} (huv : u ≠ v)
    (hau : a ≠ u) (hav : a ≠ v) (hbu : b ≠ u) (hbv : b ≠ v)
    (hcu : c ≠ u) (hcv : c ≠ v) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdu : d ≠ u) (hdv : d ≠ v) (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) :
    tc a b c ∈ Subgroup.closure (pairThreeCycles u v) := by
  have hσ : tc v a d ∈ Subgroup.closure (pairThreeCycles u v) :=
    tc_v_mem_pairClosure huv hau hav hdu hdv (Ne.symm hda)
  have hτ : tc v b c ∈ Subgroup.closure (pairThreeCycles u v) :=
    tc_v_mem_pairClosure huv hbu hbv hcu hcv hbc
  have hconj := tc_conj (tc v a d) v b c
  have h1 : tc v a d v = a := tc_apply_a (Ne.symm hav) (Ne.symm hdv)
  have h2 : tc v a d b = b := tc_apply_of_ne hbv (Ne.symm hab) (Ne.symm hdb)
  have h3 : tc v a d c = c := tc_apply_of_ne hcv (Ne.symm hac) (Ne.symm hdc)
  rw [h1, h2, h3] at hconj
  rw [← hconj]
  exact conj_mem_pairClosure hσ hτ

private lemma tc_mem_of_both {u v k : α} (huv : u ≠ v) (huk : u ≠ k) (hvk : v ≠ k)
    {g : Perm α} (hg : g.IsThreeCycle) (hgs : g.support = {u, v, k}) :
    g ∈ Subgroup.closure (pairThreeCycles u v) := by
  have hgen : tc u v k ∈ Subgroup.closure (pairThreeCycles u v) :=
    tc_mem_pairClosure huv huk hvk
  have htc3 : (tc u v k).IsThreeCycle := tc_isThreeCycle huv huk hvk
  have hss : g.support = (tc u v k).support := by
    rw [hgs, tc_support huv huk hvk]
  rcases threeCycle_eq_or_eq_inv_of_support_eq hg htc3 hss with h | h
  · rw [h]; exact hgen
  · rw [h]; exact Subgroup.inv_mem _ hgen

private lemma isThreeCycle_mem_pairClosure_of_mem_mem {u v : α} (huv : u ≠ v)
    {g : Perm α} (hg : g.IsThreeCycle) (hu : u ∈ g.support) (hv : v ∈ g.support) :
    g ∈ Subgroup.closure (pairThreeCycles u v) := by
  classical
  let T := (g.support.erase u).erase v
  have hT2 : (g.support.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem hu, hg.card_support]
  have hT : T.card = 1 := by
    change ((g.support.erase u).erase v).card = 1
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hv⟩), hT2]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hT
  have hkT : k ∈ T := by rw [hk]; simp
  have hku : k ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hkT).2).1
  have hkv : k ≠ v := (Finset.mem_erase.mp hkT).1
  have hsup : g.support = {u, v, k} := by
    have h1 : insert v T = g.support.erase u := by
      change insert v ((g.support.erase u).erase v) = g.support.erase u
      exact Finset.insert_erase (Finset.mem_erase.mpr ⟨huv.symm, hv⟩)
    have h2 : insert u (g.support.erase u) = g.support := Finset.insert_erase hu
    calc
      g.support = insert u (g.support.erase u) := h2.symm
      _ = insert u (insert v T) := by rw [h1]
      _ = {u, v, k} := by rw [hk]
  exact tc_mem_of_both huv (Ne.symm hku) (Ne.symm hkv) hg hsup

private lemma isThreeCycle_mem_pairClosure_of_mem_notMem {u v : α} (huv : u ≠ v)
    (hcard : 6 ≤ Fintype.card α) {g : Perm α} (hg : g.IsThreeCycle)
    (hu : u ∈ g.support) (hv : v ∉ g.support) :
    g ∈ Subgroup.closure (pairThreeCycles u v) := by
  classical
  let p := g u
  let q := g (g u)
  have hpu : p ≠ u := by
    intro h
    exact (Equiv.Perm.mem_support.mp hu) h
  have hpv : p ≠ v := by
    intro h
    exact hv (h ▸ (Equiv.Perm.apply_mem_support).2 hu)
  have hq_supp : q ∈ g.support := (Equiv.Perm.apply_mem_support).2
    ((Equiv.Perm.apply_mem_support).2 hu)
  have hg3 : g ^ 3 = 1 := by simpa [hg.orderOf] using pow_orderOf_eq_one g
  have hgq : g q = u := by
    have := congrArg (fun t : Perm α => t u) hg3
    simpa [q, pow_succ, pow_two] using this
  have hqu : q ≠ u := by
    intro h
    have hp : p = u := by
      calc p = g u := rfl
        _ = g q := by rw [h]
        _ = u := hgq
    exact hpu hp
  have hqv : q ≠ v := by
    intro h
    exact hv (h ▸ hq_supp)
  have hpq : p ≠ q := by
    intro h
    exact hpu (g.injective (by simpa [p, q] using h)).symm
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 ∉ ({u, v, p, q} : Finset α) := by
    have hlt : ({u, v, p, q} : Finset α).card < Fintype.card α := by
      have := Finset.card_le_four (a := u) (b := v) (c := p) (d := q)
      omega
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({u, v, p, q} : Finset α)) (t := Finset.univ) (by simpa using hlt)
    exact ⟨x, hx⟩
  have hcu : c0 ≠ u := by intro h; exact hc0 (by simp [h])
  have hcv : c0 ≠ v := by intro h; exact hc0 (by simp [h])
  have hcp : c0 ≠ p := by intro h; exact hc0 (by simp [h])
  have hcq : c0 ≠ q := by intro h; exact hc0 (by simp [h])
  have hformu : g = tc u p q := by
    simpa [tc, p, q] using hg.eq_swap_mul_swap_iff_mem_support.mpr hu
  rw [hformu]
  exact tc_u_mem_pairClosure huv hpu hpv hqu hqv hpq hcu hcv hcp hcq

private lemma isThreeCycle_mem_pairClosure_of_notMem_mem {u v : α} (huv : u ≠ v)
    (hcard : 6 ≤ Fintype.card α) {g : Perm α} (hg : g.IsThreeCycle)
    (hu : u ∉ g.support) (hv : v ∈ g.support) :
    g ∈ Subgroup.closure (pairThreeCycles u v) := by
  classical
  let p := g v
  let q := g (g v)
  have hpv : p ≠ v := by
    intro h
    exact (Equiv.Perm.mem_support.mp hv) h
  have hpu : p ≠ u := by
    intro h
    exact hu (h ▸ (Equiv.Perm.apply_mem_support).2 hv)
  have hq_supp : q ∈ g.support := (Equiv.Perm.apply_mem_support).2
    ((Equiv.Perm.apply_mem_support).2 hv)
  have hg3 : g ^ 3 = 1 := by simpa [hg.orderOf] using pow_orderOf_eq_one g
  have hgq : g q = v := by
    have := congrArg (fun t : Perm α => t v) hg3
    simpa [q, pow_succ, pow_two] using this
  have hqv : q ≠ v := by
    intro h
    have hp : p = v := by
      calc p = g v := rfl
        _ = g q := by rw [h]
        _ = v := hgq
    exact hpv hp
  have hqu : q ≠ u := by
    intro h
    exact hu (h ▸ hq_supp)
  have hpq : p ≠ q := by
    intro h
    exact hpv (g.injective (by simpa [p, q] using h)).symm
  have hformv : g = tc v p q := by
    simpa [tc, p, q] using hg.eq_swap_mul_swap_iff_mem_support.mpr hv
  rw [hformv]
  exact tc_v_mem_pairClosure huv hpu hpv hqu hqv hpq

private lemma isThreeCycle_mem_pairClosure_of_notMem_notMem {u v : α} (huv : u ≠ v)
    (hcard : 6 ≤ Fintype.card α) {g : Perm α} (hg : g.IsThreeCycle)
    (hu : u ∉ g.support) (hv : v ∉ g.support) :
    g ∈ Subgroup.closure (pairThreeCycles u v) := by
  classical
  obtain ⟨a, ha⟩ : g.support.Nonempty := hg.isCycle.nonempty_support
  let b := g a
  let c := g (g a)
  have hnd : [a, g a, g (g a)].Nodup := hg.nodup_iff_mem_support.mpr ha
  have hnd' : (a ≠ g a ∧ a ≠ g (g a)) ∧ a ≠ g a := by
    simpa using hnd
  have hab : a ≠ b := by simpa [b] using hnd'.1.1
  have hac : a ≠ c := by simpa [c] using hnd'.1.2
  have hbc : b ≠ c := by
    intro h
    exact hnd'.2 (g.injective (by simpa [b, c] using h))
  have hform : g = tc a b c := by
    simpa [tc, b, c] using hg.eq_swap_mul_swap_iff_mem_support.mpr ha
  have hsupp : g.support = {a, b, c} := by
    simpa [b, c] using hg.support_eq_iff_mem_support.mpr ha
  obtain ⟨d, hd⟩ : ∃ d, d ∉ ({u, v, a, b, c} : Finset α) := by
    have hlt : ({u, v, a, b, c} : Finset α).card < Fintype.card α := by
      have := Finset.card_le_five (a := u) (b := v) (c := a) (d := b) (e := c)
      omega
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({u, v, a, b, c} : Finset α)) (t := Finset.univ) (by simpa using hlt)
    exact ⟨x, hx⟩
  have hdu : d ≠ u := by intro h; exact hd (by simp [h])
  have hdv : d ≠ v := by intro h; exact hd (by simp [h])
  have hda : d ≠ a := by intro h; exact hd (by simp [h])
  have hdb : d ≠ b := by intro h; exact hd (by simp [h])
  have hdc : d ≠ c := by intro h; exact hd (by simp [h])
  have hau : a ≠ u := by
    intro h; exact hu (h ▸ (show a ∈ g.support from by rw [hsupp]; simp))
  have hav : a ≠ v := by
    intro h; exact hv (h ▸ (show a ∈ g.support from by rw [hsupp]; simp))
  have hbu : b ≠ u := by
    intro h; exact hu (h ▸ (show b ∈ g.support from by rw [hsupp]; simp))
  have hbv : b ≠ v := by
    intro h; exact hv (h ▸ (show b ∈ g.support from by rw [hsupp]; simp))
  have hcu : c ≠ u := by
    intro h; exact hu (h ▸ (show c ∈ g.support from by rw [hsupp]; simp))
  have hcv : c ≠ v := by
    intro h; exact hv (h ▸ (show c ∈ g.support from by rw [hsupp]; simp))
  rw [hform]
  exact tc_general_mem_pairClosure huv hau hav hbu hbv hcu hcv hab hac hbc
    hdu hdv hda hdb hdc

private lemma isThreeCycle_mem_pairClosure {u v : α} (huv : u ≠ v)
    (hcard : 6 ≤ Fintype.card α) {g : Perm α} (hg : g.IsThreeCycle) :
    g ∈ Subgroup.closure (pairThreeCycles u v) := by
  by_cases hu : u ∈ g.support
  · by_cases hv : v ∈ g.support
    · exact isThreeCycle_mem_pairClosure_of_mem_mem huv hg hu hv
    · exact isThreeCycle_mem_pairClosure_of_mem_notMem huv hcard hg hu hv
  · by_cases hv : v ∈ g.support
    · exact isThreeCycle_mem_pairClosure_of_notMem_mem huv hcard hg hu hv
    · exact isThreeCycle_mem_pairClosure_of_notMem_notMem huv hcard hg hu hv

private theorem closure_pairThreeCycles_eq_alternating {u v : α} (huv : u ≠ v)
    (hcard : 6 ≤ Fintype.card α) :
    Subgroup.closure (pairThreeCycles u v) = alternatingGroup α := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨hg, -, -⟩
    exact hg.mem_alternatingGroup
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro g hg
    exact isThreeCycle_mem_pairClosure huv hcard hg

private lemma exists_two_fixed_points
    {F : Subgroup (alternatingGroup (Fin 11))}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hcard : Nat.card F = 9) :
    ∃ u v : Fin 11, u ≠ v ∧ u ∈ MulAction.fixedPoints F (Fin 11) ∧
      v ∈ MulAction.fixedPoints F (Fin 11) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Fix := MulAction.fixedPoints F (Fin 11)
  have hmod := hF.isPGroup.card_modEq_card_fixedPoints (Fin 11)
  have hmod' : Nat.card Fix % 3 = 2 := by
    change Nat.card (Fin 11) % 3 = Nat.card Fix % 3 at hmod
    rw [Nat.card_fin] at hmod
    omega
  have hne : Fix ≠ Set.univ := by
    intro huniv
    have hbot : F = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      apply Subtype.ext
      apply Equiv.ext
      intro a
      have hfix : a ∈ Fix := by rw [huniv]; exact Set.mem_univ a
      have h := (MulAction.mem_fixedPoints.mp hfix) ⟨x, hx⟩
      change (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) a = a at h
      simpa using h
    rw [hbot] at hcard
    simp at hcard
  have hss : Fix ⊂ (Set.univ : Set (Fin 11)) := Set.ssubset_univ_iff.mpr hne
  have hlt' : Fix.ncard < 11 := by
    have h := Set.ncard_lt_ncard hss
    rwa [Set.ncard_univ, Nat.card_fin] at h
  have hmod'' : Fix.ncard % 3 = 2 := by rwa [Nat.card_coe_set_eq] at hmod'
  have hge' : 2 ≤ Fix.ncard := by
    have h := Nat.mod_add_div Fix.ncard 3
    omega
  have hnt : Fix.Nontrivial := by
    rw [← Set.one_lt_ncard_iff_nontrivial]
    omega
  obtain ⟨u, v, huv, hsub⟩ := hnt.pair_subset
  exact ⟨u, v, huv, hsub (by simp), hsub (by simp)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma orbit_card_nine {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w) :
    (MulAction.orbit F w).ncard = 9 := by
  classical
  have hstab : MulAction.stabilizer F w = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hxne
    have hfix : x • w = w := (MulAction.mem_stabilizer_iff.mp hx)
    have hfix' : (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w = w := by
      change (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w = w at hfix
      exact hfix
    exact hw x hxne hfix'
  have hstabcard : Nat.card (MulAction.stabilizer F w) = 1 := by
    rw [hstab]
    simp
  have hidx : (MulAction.stabilizer F w).index = (MulAction.orbit F w).ncard :=
    MulAction.index_stabilizer F w
  have hprod := Subgroup.index_mul_card (MulAction.stabilizer F w)
  rw [hidx, hstabcard, mul_one, hFcard] at hprod
  exact hprod

private lemma not_mem_orbit_of_fixed {F : Subgroup (alternatingGroup (Fin 11))}
    {w u : Fin 11} (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hu : u ∈ MulAction.fixedPoints F (Fin 11)) :
    u ∉ MulAction.orbit F w := by
  classical
  have hcardF : Fintype.card F = 9 := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hxne⟩ : ∃ x : F, x ≠ 1 :=
    Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card F) 1
  have hw_not_fix : w ∉ MulAction.fixedPoints F (Fin 11) := by
    intro hwfix
    have hfix := (MulAction.mem_fixedPoints.mp hwfix) x
    change (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w = w at hfix
    exact hw x hxne hfix
  intro huO
  obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp huO
  have hyu : y • u = u := (MulAction.mem_fixedPoints.mp hu) y
  have hwu : y • w = y • u := by rw [hy, hyu]
  have hw_eq_u : w = u := by
    have := congrArg (fun z => (y⁻¹) • z) hwu
    simpa using this
  exact hw_not_fix (hw_eq_u ▸ hu)

private lemma orbit_compl_eq_pair {F : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11} (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (huv : u ≠ v)
    (hu : u ∈ MulAction.fixedPoints F (Fin 11))
    (hv : v ∈ MulAction.fixedPoints F (Fin 11)) :
    (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)) := by
  classical
  have horb : (MulAction.orbit F w).ncard = 9 := orbit_card_nine hFcard hw
  have hcomp : (MulAction.orbit F w)ᶜ.ncard = 2 := by
    rw [Set.ncard_compl, horb]
    simp [Nat.card_fin]
  have hsub : ({u, v} : Set (Fin 11)) ⊆ (MulAction.orbit F w)ᶜ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact not_mem_orbit_of_fixed hFcard hw hu
    · exact not_mem_orbit_of_fixed hFcard hw hv
  have hpair : ({u, v} : Set (Fin 11)).ncard = 2 := Set.ncard_pair huv
  have hle : (MulAction.orbit F w)ᶜ.ncard ≤ ({u, v} : Set (Fin 11)).ncard := by
    rw [hcomp, hpair]
  exact (Set.eq_of_subset_of_ncard_le hsub hle).symm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma mem_Y_of_commute {F Y : Subgroup (alternatingGroup (Fin 11))}
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    {xA cA : alternatingGroup (Fin 11)} (hxA : xA ∈ F) (hxne : xA ≠ 1)
    (hcomm : Commute cA xA) : cA ∈ Y := by
  have hle : Subgroup.zpowers xA ≤
      Subgroup.centralizer ({cA} : Set (alternatingGroup (Fin 11))) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.eq.symm
  have hmem : cA ∈ Subgroup.centralizer
      (Subgroup.zpowers xA : Set (alternatingGroup (Fin 11))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' := hle hh
    rwa [Subgroup.mem_centralizer_singleton_iff] at hh'
  have hnorm : cA ∈ Subgroup.normalizer
      (Subgroup.zpowers xA : Set (alternatingGroup (Fin 11))) :=
    (Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers xA : Set (alternatingGroup (Fin 11)))) hmem
  exact hcond (Subgroup.zpowers xA) (Subgroup.zpowers_le.mpr hxA)
    (by rw [Subgroup.zpowers_ne_bot]; exact hxne) hnorm

private lemma cycleOf_mem_Y {F Y : Subgroup (alternatingGroup (Fin 11))}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    {x : F} (hx : x ≠ 1) {p : Fin 11}
    (hxp : (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) p ≠ p) :
    ∃ h3 : (((x : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf p).IsThreeCycle,
      (⟨(((x : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf p),
        h3.mem_alternatingGroup⟩ : alternatingGroup (Fin 11)) ∈ Y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set xA : alternatingGroup (Fin 11) := (x : F).1 with hxA
  set xP : Perm (Fin 11) := (xA : Perm (Fin 11)) with hxP
  have hxneA : xA ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    exact h
  have hxPne : xP ≠ 1 := by
    intro h
    apply hxneA
    apply Subtype.ext
    exact h
  have hx3A : xA ^ 3 = 1 := hF.2 xA x.2
  have hx3P : xP ^ 3 = 1 := by
    simpa [hxP] using congrArg (fun g : alternatingGroup (Fin 11) =>
      (g : Perm (Fin 11))) hx3A
  have hxorder : orderOf xP = 3 := orderOf_eq_prime hx3P hxPne
  set γ : Perm (Fin 11) := xP.cycleOf p with hγ
  have hγmem : γ ∈ xP.cycleFactorsFinset := by
    rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
    exact Equiv.Perm.mem_support.mpr hxp
  have hγcycle : γ.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hγmem).1
  have hγorder : orderOf γ = 3 :=
    CFSG.RankThree.GroupTheory.orderOf_eq_of_mem_cycleFactorsFinset
      Nat.prime_three hxorder hγmem
  have hγcard : γ.support.card = 3 := by
    rw [← hγcycle.orderOf, hγorder]
  have hγ3 : γ.IsThreeCycle := card_support_eq_three_iff.mp hγcard
  let γA : alternatingGroup (Fin 11) := ⟨γ, hγ3.mem_alternatingGroup⟩
  have hcommP : Commute γ xP := Equiv.Perm.self_mem_cycle_factors_commute hγmem
  have hcommA : Commute γA xA := by
    rw [Commute]
    apply Subtype.ext
    exact hcommP.eq
  exact ⟨hγ3, mem_Y_of_commute hcond x.2 hxneA hcommA⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma moves_of_mem_orbit {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    (hFcomm : IsMulCommutative F)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    {x : F} (hx : x ≠ 1) {p : Fin 11} (hp : p ∈ MulAction.orbit F w) :
    (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) p ≠ p := by
  classical
  haveI : IsMulCommutative F := hFcomm
  let xP : Perm (Fin 11) := ((x : alternatingGroup (Fin 11)) : Perm (Fin 11))
  obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp hp
  have hy' : (((y : alternatingGroup (Fin 11)) : Perm (Fin 11))) w = p := by
    change (((y : alternatingGroup (Fin 11)) : Perm (Fin 11))) w = p at hy
    exact hy
  intro hxp
  have hcommute_apply :
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11)))
        ((((y : alternatingGroup (Fin 11)) : Perm (Fin 11))) w) =
      (((y : alternatingGroup (Fin 11)) : Perm (Fin 11)))
        ((((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w) := by
    have h := congrArg
      (fun g : F => (((g : alternatingGroup (Fin 11)) : Perm (Fin 11))) w)
      (mul_comm' x y)
    simpa [Equiv.Perm.mul_apply] using h
  have hx_eq : (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w = w := by
    apply (((y : alternatingGroup (Fin 11)) : Perm (Fin 11))).injective
    calc
      (((y : alternatingGroup (Fin 11)) : Perm (Fin 11)))
          ((((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w)
          = (((x : alternatingGroup (Fin 11)) : Perm (Fin 11)))
            ((((y : alternatingGroup (Fin 11)) : Perm (Fin 11))) w) :=
        hcommute_apply.symm
      _ = (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) p := by rw [hy']
      _ = p := hxp
      _ = (((y : alternatingGroup (Fin 11)) : Perm (Fin 11))) w := hy'.symm
  exact hw x hx hx_eq

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private noncomputable def orbitFinset (F : Subgroup (alternatingGroup (Fin 11))) (w : Fin 11) :
    Finset (Fin 11) := (Set.toFinite (MulAction.orbit F w)).toFinset

private lemma mem_orbitFinset {F : Subgroup (alternatingGroup (Fin 11))} {w z : Fin 11} :
    z ∈ orbitFinset F w ↔ z ∈ MulAction.orbit F w := by
  change z ∈ (Set.toFinite (MulAction.orbit F w)).toFinset ↔
    z ∈ MulAction.orbit F w
  exact Set.Finite.mem_toFinset _

private lemma orbitFinset_card {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w) :
    (orbitFinset F w).card = 9 := by
  rw [orbitFinset, ← Set.ncard_eq_toFinset_card (MulAction.orbit F w)
    (Set.toFinite (MulAction.orbit F w))]
  exact orbit_card_nine hFcard hw

private lemma support_subset_orbitFinset {F : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    (x : F) :
    (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))).support ⊆ orbitFinset F w := by
  intro z hz
  rw [mem_orbitFinset]
  by_contra hzO
  have hzcompl : z ∈ ({u, v} : Set (Fin 11)) := by rwa [← hcompl]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzcompl
  rcases hzcompl with rfl | rfl
  · exact (Equiv.Perm.mem_support.mp hz) (hfixu x)
  · exact (Equiv.Perm.mem_support.mp hz) (hfixv x)

private def orbitCycles (F : Subgroup (alternatingGroup (Fin 11))) (w : Fin 11) :
    Set (alternatingGroup (Fin 11)) :=
  {g | ∃ (x : F) (p : Fin 11), x ≠ 1 ∧ p ∈ MulAction.orbit F w ∧
    (g : Perm (Fin 11)) = (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))).cycleOf p}

private noncomputable def orbitH (F : Subgroup (alternatingGroup (Fin 11))) (w : Fin 11) :
    Subgroup (alternatingGroup (Fin 11)) :=
  Subgroup.closure (orbitCycles F w)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma orbitCycles_support_subset {F : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    {g : alternatingGroup (Fin 11)} (hg : g ∈ orbitCycles F w) :
    (g : Perm (Fin 11)).support ⊆ orbitFinset F w := by
  obtain ⟨x, p, hx, hp, hgperm⟩ := hg
  rw [hgperm]
  exact (Equiv.Perm.support_cycleOf_le
    (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) p).trans
    (support_subset_orbitFinset hcompl hfixu hfixv x)

private lemma orbitH_support_subset {F : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    {h : alternatingGroup (Fin 11)} (hh : h ∈ orbitH F w) :
    (h : Perm (Fin 11)).support ⊆ orbitFinset F w := by
  change h ∈ Subgroup.closure (orbitCycles F w) at hh
  refine Subgroup.closure_induction (G := alternatingGroup (Fin 11))
    (k := orbitCycles F w)
    (p := fun g _ => (g : Perm (Fin 11)).support ⊆ orbitFinset F w)
    (mem := ?_) (one := ?_) (mul := ?_) (inv := ?_) hh
  · intro g hg
    exact orbitCycles_support_subset hcompl hfixu hfixv hg
  · rw [Subgroup.coe_one]
    simp
  · intro a b ha hb hsa hsb
    refine (Equiv.Perm.support_mul_le (a : Perm (Fin 11)) (b : Perm (Fin 11))).trans ?_
    rw [Finset.sup_eq_union]
    exact Finset.union_subset hsa hsb
  · intro a ha hsa
    rw [Subgroup.coe_inv, Equiv.Perm.support_inv]
    exact hsa

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma stabilizer_eq_bot_of_mem_orbit {F : Subgroup (alternatingGroup (Fin 11))}
    {w p : Fin 11} (hstab : MulAction.stabilizer F w = ⊥)
    (hp : p ∈ MulAction.orbit F w) :
    MulAction.stabilizer F p = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxp : x • p = p := MulAction.mem_stabilizer_iff.mp hx
  obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp hp
  have hconj : y⁻¹ * x * y ∈ MulAction.stabilizer F w := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      (y⁻¹ * x * y) • w = y⁻¹ • (x • (y • w)) := by simp [mul_smul]
      _ = y⁻¹ • (x • p) := by rw [hy]
      _ = y⁻¹ • p := by rw [hxp]
      _ = y⁻¹ • (y • w) := by rw [hy]
      _ = w := by simp
  rw [hstab, Subgroup.mem_bot] at hconj
  have hx1 : x = 1 := by
    calc
      x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = y * 1 * y⁻¹ := by rw [hconj]
      _ = 1 := by group
  exact hx1

private lemma eq_of_smul_eq_of_mem_orbit {F : Subgroup (alternatingGroup (Fin 11))}
    {w p : Fin 11} (hstab : MulAction.stabilizer F w = ⊥)
    (hp : p ∈ MulAction.orbit F w) {f g : F} (h : f • p = g • p) : f = g := by
  classical
  have hstabp : MulAction.stabilizer F p = ⊥ :=
    stabilizer_eq_bot_of_mem_orbit hstab hp
  have hmem : g⁻¹ * f ∈ MulAction.stabilizer F p := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      (g⁻¹ * f) • p = g⁻¹ • (f • p) := by simp [mul_smul]
      _ = g⁻¹ • (g • p) := by rw [h]
      _ = p := by simp
  rw [hstabp, Subgroup.mem_bot] at hmem
  have : f = g := by
    have := congrArg (fun z : F => g * z) hmem
    simpa using this
  exact this

private lemma orbitH_le_Y {F Y : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w) :
    orbitH F w ≤ Y := by
  classical
  rw [orbitH, Subgroup.closure_le]
  rintro g ⟨x, p, hx, hp, hgperm⟩
  have hxp : (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) p ≠ p :=
    moves_of_mem_orbit hF.1 hw hx hp
  obtain ⟨h3, hmemY⟩ := cycleOf_mem_Y hF hcond hx hxp
  have hg : g = (⟨(((x : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf p),
      h3.mem_alternatingGroup⟩ : alternatingGroup (Fin 11)) := by
    apply Subtype.ext
    exact hgperm
  rw [hg]
  exact hmemY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private noncomputable def orbitG (F : Subgroup (alternatingGroup (Fin 11))) (w : Fin 11) :
    Subgroup (Perm ↥(orbitFinset F w)) :=
  ((orbitH F w).map (Subgroup.subtype (alternatingGroup (Fin 11)))).comap
    (Equiv.Perm.ofSubtype (p := fun x : Fin 11 => x ∈ orbitFinset F w))

private lemma subtypePerm_of_support_subset {f : Perm (Fin 11)} {s : Finset (Fin 11)}
    (hs : f.support ⊆ s) :
    Equiv.Perm.ofSubtype (f.subtypePerm (Equiv.Perm.isInvariant_of_support_le hs)) = f :=
  Equiv.Perm.ofSubtype_subtypePerm (Equiv.Perm.isInvariant_of_support_le hs)
    (fun x hx => hs (Equiv.Perm.mem_support.mpr hx))

private lemma subtypePerm_apply_val {F : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    {h : alternatingGroup (Fin 11)} (hh : h ∈ orbitH F w) {x : Fin 11}
    (hx : x ∈ orbitFinset F w) :
    ((((h : Perm (Fin 11)).subtypePerm
      (Equiv.Perm.isInvariant_of_support_le
        (orbitH_support_subset hcompl hfixu hfixv hh))) ⟨x, hx⟩ : ↥(orbitFinset F w)) : Fin 11) =
      (h : Perm (Fin 11)) x :=
  rfl

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma orbitG_exists_smul_eq {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    (x y : ↥(orbitFinset F w)) :
    ∃ σ : ↥(orbitG F w), σ • x = y := by
  classical
  have hxO : (x : Fin 11) ∈ MulAction.orbit F w := mem_orbitFinset.mp x.2
  have hyO : (y : Fin 11) ∈ MulAction.orbit F w := mem_orbitFinset.mp y.2
  have horb : MulAction.orbit F (x : Fin 11) = MulAction.orbit F w :=
    MulAction.orbit_eq_iff.mpr hxO
  have hyIn : (y : Fin 11) ∈ MulAction.orbit F (x : Fin 11) := by
    rw [horb]
    exact hyO
  obtain ⟨f, hf⟩ := MulAction.mem_orbit_iff.mp hyIn
  have hf' : (((f : alternatingGroup (Fin 11)) : Perm (Fin 11))) (x : Fin 11) =
      (y : Fin 11) := by
    change (((f : alternatingGroup (Fin 11)) : Perm (Fin 11))) (x : Fin 11) = (y : Fin 11) at hf
    exact hf
  by_cases hf1 : f = 1
  · refine ⟨1, ?_⟩
    rw [one_smul]
    exact Subtype.ext (by rw [← hf']; simp [hf1])
  · have hxp : (((f : alternatingGroup (Fin 11)) : Perm (Fin 11))) (x : Fin 11) ≠
        (x : Fin 11) := moves_of_mem_orbit hF.1 hw hf1 hxO
    obtain ⟨h3, hmemY⟩ := cycleOf_mem_Y hF hcond hf1 hxp
    let γA : alternatingGroup (Fin 11) :=
      ⟨(((f : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf (x : Fin 11)),
        h3.mem_alternatingGroup⟩
    have hγH' : γA ∈ Subgroup.closure (orbitCycles F w) :=
      Subgroup.subset_closure ⟨f, (x : Fin 11), hf1, hxO, rfl⟩
    have hγH : γA ∈ orbitH F w := hγH' 
    have hγsupp : (γA : Perm (Fin 11)).support ⊆ orbitFinset F w :=
      orbitH_support_subset (h := γA) hcompl hfixu hfixv (hh := hγH)
    have hσmem : (((γA : Perm (Fin 11)).subtypePerm
        (Equiv.Perm.isInvariant_of_support_le hγsupp))) ∈ orbitG F w := by
      rw [orbitG, Subgroup.mem_comap]
      refine Subgroup.mem_map.mpr ⟨γA, hγH, ?_⟩
      exact (subtypePerm_of_support_subset hγsupp).symm
    let σ : ↥(orbitG F w) :=
      Subtype.mk (((γA : Perm (Fin 11)).subtypePerm
        (Equiv.Perm.isInvariant_of_support_le hγsupp))) hσmem
    exact ⟨σ, by
      apply Subtype.ext
      show (((σ : Perm ↥(orbitFinset F w)) ⟨(x : Fin 11), x.2⟩ : ↥(orbitFinset F w)) : Fin 11) =
        (y : Fin 11)
      dsimp only [σ]
      rw [subtypePerm_apply_val (u := u) (v := v) (h := γA) (hcompl := hcompl)
        (hfixu := hfixu) (hfixv := hfixv) (hh := hγH)]
      show (((f : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf (x : Fin 11)) (x : Fin 11) =
        (y : Fin 11)
      rw [Equiv.Perm.cycleOf_apply_self, hf']⟩

private lemma orbitG_isPretransitive {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    MulAction.IsPretransitive ↥(orbitG F w) ↥(orbitFinset F w) :=
  MulAction.IsPretransitive.mk fun x y =>
    orbitG_exists_smul_eq hF hcond hFcard hw hcompl hfixu hfixv x y

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma subtypePerm_isThreeCycle {f : Perm (Fin 11)} {s : Finset (Fin 11)}
    (hs : f.support ⊆ s) (hf : f.IsThreeCycle) :
    (f.subtypePerm (Equiv.Perm.isInvariant_of_support_le hs)).IsThreeCycle := by
  classical
  rw [← card_support_eq_three_iff, Equiv.Perm.support_subtypePerm]
  have hbij : ({x : ↥s | f ↑x ≠ ↑x} : Finset ↥s).card = f.support.card := by
    refine Finset.card_bij (fun a _ => (a : Fin 11)) ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact Equiv.Perm.mem_support.mpr ha.2
    · intro a _ b _ h
      exact Subtype.ext h
    · intro b hb
      refine ⟨⟨b, hs (Equiv.Perm.mem_support.mpr ?_)⟩, ?_, rfl⟩
      · exact (Equiv.Perm.mem_support.mp hb)
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Equiv.Perm.mem_support.mp hb⟩
  rw [hbij, hf.card_support]

private lemma orbitG_has_threeCycle {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    ∃ σ : ↥(orbitG F w), (σ : Perm ↥(orbitFinset F w)).IsThreeCycle := by
  classical
  have hcardF : Fintype.card F = 9 := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hxne⟩ : ∃ x : F, x ≠ 1 :=
    Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card F) 1
  have hpos : 0 < (orbitFinset F w).card := by
    rw [orbitFinset_card hFcard hw]
    norm_num
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hpO : p ∈ MulAction.orbit F w := mem_orbitFinset.mp hp
  have hxp : (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) p ≠ p :=
    moves_of_mem_orbit hF.1 hw hxne hpO
  obtain ⟨h3, hmemY⟩ := cycleOf_mem_Y hF hcond hxne hxp
  let γA : alternatingGroup (Fin 11) :=
    ⟨(((x : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf p), h3.mem_alternatingGroup⟩
  have hγH : γA ∈ orbitH F w := by
    change γA ∈ Subgroup.closure (orbitCycles F w)
    exact Subgroup.subset_closure ⟨x, p, hxne, hpO, rfl⟩
  have hγsupp : (γA : Perm (Fin 11)).support ⊆ orbitFinset F w :=
    orbitH_support_subset hcompl hfixu hfixv hγH
  have hσmem : (((γA : Perm (Fin 11)).subtypePerm
      (Equiv.Perm.isInvariant_of_support_le hγsupp))) ∈ orbitG F w := by
    rw [orbitG, Subgroup.mem_comap]
    refine Subgroup.mem_map.mpr ⟨γA, hγH, ?_⟩
    exact (subtypePerm_of_support_subset hγsupp).symm
  refine ⟨⟨_, hσmem⟩, ?_⟩
  exact subtypePerm_isThreeCycle hγsupp h3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma block_ncard_eq_three {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    {B : Set ↥(orbitFinset F w)}
    (hB : MulAction.IsBlock ↥(orbitG F w) B)
    (hBnt : B.Nontrivial) (hBne : B ≠ Set.univ) :
    B.ncard = 3 := by
  classical
  letI : MulAction ↥(orbitG F w) ↥(orbitFinset F w) :=
    Subgroup.instMulActionSubtypeMem (S := orbitG F w)
  letI : MulAction ↥(orbitG F w) (Set ↥(orbitFinset F w)) := Set.mulActionSet
  haveI : MulAction.IsPretransitive ↥(orbitG F w) ↥(orbitFinset F w) :=
    orbitG_isPretransitive hF hcond hFcard hw hcompl hfixu hfixv
  have hcard9 : Nat.card ↥(orbitFinset F w) = 9 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, orbitFinset_card hFcard hw]
  have hprod := MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq hB hBnt.nonempty
  rw [hcard9] at hprod
  have hB2 : 2 ≤ B.ncard := by
    have h := Set.one_lt_ncard_iff_nontrivial.mpr hBnt
    omega
  have horb2 : 2 ≤ (MulAction.orbit ↥(orbitG F w) B).ncard := by
    have hnt : (MulAction.orbit ↥(orbitG F w) B).Nontrivial := by
      obtain ⟨p, hpB⟩ := hBnt.nonempty
      obtain ⟨q, hqB⟩ := (Set.ne_univ_iff_exists_notMem B).mp hBne
      obtain ⟨g, hgp⟩ :=
        (MulAction.IsPretransitive.exists_smul_eq (M := ↥(orbitG F w)) p q)
      have hgB : g • B ≠ B := by
        intro h
        apply hqB
        rw [← h, ← hgp]
        exact Set.smul_mem_smul_set (α := ↥(orbitG F w)) hpB
      exact Set.nontrivial_of_mem_mem_ne (MulAction.mem_orbit_self B)
        (MulAction.mem_orbit B g) hgB.symm
    have h := Set.one_lt_ncard_iff_nontrivial.mpr hnt
    omega
  have hBle : B.ncard ≤ 4 := by
    have h2 : B.ncard * 2 ≤ B.ncard * (MulAction.orbit ↥(orbitG F w) B).ncard :=
      Nat.mul_le_mul_left _ horb2
    omega
  have hdv : B.ncard ∣ 9 := ⟨_, hprod.symm⟩
  interval_cases B.ncard <;> first | (norm_num at hdv; done) | rfl

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma exists_notMem_zpowers_union {F : Subgroup (alternatingGroup (Fin 11))}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9) (f1 f2 : F) :
    ∃ f : F, f ∉ Subgroup.zpowers f1 ∧ f ∉ Subgroup.zpowers f2 := by
  classical
  have hle : ∀ f : F, Nat.card (Subgroup.zpowers f) ≤ 3 := by
    intro f
    rw [Nat.card_zpowers]
    have h3 : (f : alternatingGroup (Fin 11)) ^ 3 = 1 := hF.2 f f.2
    have hdiv : orderOf (f : alternatingGroup (Fin 11)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one h3
    have hcoe : orderOf (f : alternatingGroup (Fin 11)) = orderOf f :=
      Subgroup.orderOf_coe f
    rw [hcoe] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hle1 : (Subgroup.zpowers f1 : Set F).ncard ≤ 3 := by
    rw [← Set.fintypeCard_eq_ncard, ← Nat.card_eq_fintype_card]
    exact hle f1
  have hle2 : (Subgroup.zpowers f2 : Set F).ncard ≤ 3 := by
    rw [← Set.fintypeCard_eq_ncard, ← Nat.card_eq_fintype_card]
    exact hle f2
  have hunion : ((Subgroup.zpowers f1 : Set F) ∪ (Subgroup.zpowers f2 : Set F)).ncard ≤ 6 := by
    have h := Set.ncard_union_le (Subgroup.zpowers f1 : Set F) (Subgroup.zpowers f2 : Set F)
    omega
  have hlt : ((Subgroup.zpowers f1 : Set F) ∪ (Subgroup.zpowers f2 : Set F)).ncard <
      (Set.univ : Set F).ncard := by
    rw [Set.ncard_univ, hFcard]
    omega
  obtain ⟨f, -, hf⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  simp only [Set.mem_union, not_or] at hf
  exact ⟨f, hf.1, hf.2⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma stabilizer_w_eq_bot {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w) :
    MulAction.stabilizer F w = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hxne
  have hfix : x • w = w := MulAction.mem_stabilizer_iff.mp hx
  change (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w = w at hfix
  exact hw x hxne hfix

private lemma mem_zpowers_of_sq_eq {G : Type*} [Group G] {f g : G}
    (hf3 : f ^ 3 = 1) (h : f ^ 2 = g) : f ∈ Subgroup.zpowers g := by
  have hmul : f * g = 1 := by
    rw [← h]
    calc f * (f ^ 2) = f ^ 3 := by group
      _ = 1 := hf3
  have hf : f = g⁻¹ := mul_eq_one_iff_eq_inv.mp hmul
  rw [hf]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers g)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private structure BlockSetup (F : Subgroup (alternatingGroup (Fin 11))) (w : Fin 11)
    (B : Set ↥(orbitFinset F w)) where
  p : ↥(orbitFinset F w)
  q1 : ↥(orbitFinset F w)
  q2 : ↥(orbitFinset F w)
  f1 : F
  f2 : F
  f : F
  hpB : p ∈ B
  hq1B : q1 ∈ B
  hq2B : q2 ∈ B
  hq1ne : q1 ≠ p
  hq2ne : q2 ≠ p
  hdiff : B \ {p} = {q1, q2}
  hf1P : (((f1 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) = (q1 : Fin 11)
  hf2P : (((f2 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) = (q2 : Fin 11)
  hf1out : f ∉ Subgroup.zpowers f1
  hf2out : f ∉ Subgroup.zpowers f2
  hfne : f ≠ 1
  hfp_ne : (((f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) ≠ (p : Fin 11)
  hfpO : (((f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) ∈ orbitFinset F w

private lemma exists_block_setup {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    {Y : Subgroup (alternatingGroup (Fin 11))} {u v : Fin 11}
    {B : Set ↥(orbitFinset F w)}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hB : MulAction.IsBlock ↥(orbitG F w) B)
    (hBnt : B.Nontrivial) (hBne : B ≠ Set.univ) :
    Nonempty (BlockSetup F w B) := by
  classical
  have hBcard : B.ncard = 3 :=
    block_ncard_eq_three hF hcond hFcard hw hcompl hfixu hfixv hB hBnt hBne
  obtain ⟨p, hpB⟩ := hBnt.nonempty
  have hdiffcard : (B \ {p}).ncard = 2 := by
    have h := Set.ncard_diff_singleton_add_one hpB
    omega
  obtain ⟨q1, q2, _, hdiff⟩ := Set.ncard_eq_two.mp hdiffcard
  have hq1diff : q1 ∈ B \ {p} := by rw [hdiff]; simp
  have hq2diff : q2 ∈ B \ {p} := by rw [hdiff]; simp
  have hq1B : q1 ∈ B := (Set.mem_diff q1).mp hq1diff |>.1
  have hq1ne : q1 ≠ p := by
    have h := (Set.mem_diff q1).mp hq1diff |>.2
    simpa using h
  have hq2B : q2 ∈ B := (Set.mem_diff q2).mp hq2diff |>.1
  have hq2ne : q2 ≠ p := by
    have h := (Set.mem_diff q2).mp hq2diff |>.2
    simpa using h
  have hpO : (p : Fin 11) ∈ MulAction.orbit F w := mem_orbitFinset.mp p.2
  have hq1in : (q1 : Fin 11) ∈ MulAction.orbit F (p : Fin 11) := by
    rw [MulAction.orbit_eq_iff.mpr hpO]
    exact mem_orbitFinset.mp q1.2
  have hq2in : (q2 : Fin 11) ∈ MulAction.orbit F (p : Fin 11) := by
    rw [MulAction.orbit_eq_iff.mpr hpO]
    exact mem_orbitFinset.mp q2.2
  obtain ⟨f1, hf1eq⟩ := MulAction.mem_orbit_iff.mp hq1in
  obtain ⟨f2, hf2eq⟩ := MulAction.mem_orbit_iff.mp hq2in
  have hf1P : (((f1 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) =
      (q1 : Fin 11) := by
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hf1eq
  have hf2P : (((f2 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) =
      (q2 : Fin 11) := by
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hf2eq
  obtain ⟨f, hf1out, hf2out⟩ := exists_notMem_zpowers_union hF hFcard f1 f2
  have hfne : f ≠ 1 := by
    intro hf1
    exact hf1out (by rw [hf1]; exact Subgroup.one_mem _)
  have hfp_ne : (((f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) ≠
      (p : Fin 11) := moves_of_mem_orbit hF.1 hw hfne hpO
  have hfpO : (((f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (p : Fin 11) ∈
      orbitFinset F w :=
    support_subset_orbitFinset hcompl hfixu hfixv f
      ((Equiv.Perm.apply_mem_support).2 (Equiv.Perm.mem_support.mpr hfp_ne))
  exact ⟨⟨p, q1, q2, f1, f2, f, hpB, hq1B, hq2B, hq1ne, hq2ne, hdiff,
    hf1P, hf2P, hf1out, hf2out, hfne, hfp_ne, hfpO⟩⟩

private def blockFP {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    {B : Set ↥(orbitFinset F w)} (S : BlockSetup F w B) : Fin 11 :=
  (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (S.p : Fin 11)

private structure BlockGamma {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    {B : Set ↥(orbitFinset F w)} (S : BlockSetup F w B) where
  γA : alternatingGroup (Fin 11)
  hγH : γA ∈ orbitH F w
  hγsupp : (γA : Perm (Fin 11)).support ⊆ orbitFinset F w
  σ : ↥(orbitG F w)
  hγp : (γA : Perm (Fin 11)) (S.p : Fin 11) = blockFP S
  hsuppγ : (γA : Perm (Fin 11)).support = {(S.p : Fin 11), blockFP S,
    (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (blockFP S)}
  hσval : (σ : Perm ↥(orbitFinset F w)) =
    ((γA : Perm (Fin 11)).subtypePerm (Equiv.Perm.isInvariant_of_support_le hγsupp))
  hσp : (σ : Perm ↥(orbitFinset F w)) ⟨(S.p : Fin 11), S.p.2⟩ =
    ⟨blockFP S, S.hfpO⟩

private lemma exists_block_gamma {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    {Y : Subgroup (alternatingGroup (Fin 11))} {u v : Fin 11}
    {B : Set ↥(orbitFinset F w)} (S : BlockSetup F w B)
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    Nonempty (BlockGamma S) := by
  classical
  obtain ⟨h3, _hmemY⟩ := cycleOf_mem_Y hF hcond S.hfne
    (show blockFP S ≠ (S.p : Fin 11) from S.hfp_ne)
  let γA : alternatingGroup (Fin 11) :=
    ⟨(((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf (S.p : Fin 11),
      h3.mem_alternatingGroup⟩
  have hγH : γA ∈ orbitH F w := by
    change γA ∈ Subgroup.closure (orbitCycles F w)
    exact Subgroup.subset_closure ⟨S.f, (S.p : Fin 11), S.hfne,
      mem_orbitFinset.mp S.p.2, rfl⟩
  have hγsupp : (γA : Perm (Fin 11)).support ⊆ orbitFinset F w :=
    orbitH_support_subset hcompl hfixu hfixv hγH
  have hσmem : (((γA : Perm (Fin 11)).subtypePerm
      (Equiv.Perm.isInvariant_of_support_le hγsupp))) ∈ orbitG F w := by
    rw [orbitG, Subgroup.mem_comap]
    refine Subgroup.mem_map.mpr ⟨γA, hγH, ?_⟩
    exact (subtypePerm_of_support_subset hγsupp).symm
  let σ : ↥(orbitG F w) :=
    Subtype.mk (((γA : Perm (Fin 11)).subtypePerm
      (Equiv.Perm.isInvariant_of_support_le hγsupp))) hσmem
  have hγp : (γA : Perm (Fin 11)) (S.p : Fin 11) = blockFP S := by
    change (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf (S.p : Fin 11)
      (S.p : Fin 11) = blockFP S
    exact Equiv.Perm.cycleOf_apply_self _ _
  have hγmem : (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf (S.p : Fin 11) ∈
      (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleFactorsFinset := by
    rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
    exact Equiv.Perm.mem_support.mpr (show blockFP S ≠ (S.p : Fin 11) from S.hfp_ne)
  have hp_suppγ : (S.p : Fin 11) ∈ (γA : Perm (Fin 11)).support :=
    Equiv.Perm.mem_support.mpr (by rw [hγp]; exact S.hfp_ne)
  have hγfp : (γA : Perm (Fin 11)) (blockFP S) =
      (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (blockFP S) := by
    change (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)).cycleOf (S.p : Fin 11)
      (blockFP S) =
      (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (blockFP S)
    exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hγmem).2 (blockFP S)
      (by rw [← hγp]; exact (Equiv.Perm.apply_mem_support).2 hp_suppγ)
  have hsuppγ : (γA : Perm (Fin 11)).support = {(S.p : Fin 11), blockFP S,
      (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (blockFP S)} := by
    have h := h3.support_eq_iff_mem_support.mpr hp_suppγ
    rwa [hγp, hγfp] at h
  have hσp : (σ : Perm ↥(orbitFinset F w)) ⟨(S.p : Fin 11), S.p.2⟩ =
      ⟨blockFP S, S.hfpO⟩ := by
    apply Subtype.ext
    dsimp only [σ]
    rw [subtypePerm_apply_val (u := u) (v := v) (h := γA) (hcompl := hcompl)
      (hfixu := hfixu) (hfixv := hfixv) (hh := hγH)]
    exact hγp
  exact ⟨⟨γA, hγH, hγsupp, σ, hγp, hsuppγ, rfl, hσp⟩⟩

private lemma block_q1_notsupp {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    {B : Set ↥(orbitFinset F w)} (S : BlockSetup F w B) (G : BlockGamma S)
    (hF : CFSG.Open.IsElemAbelian 3 F) (hstab : MulAction.stabilizer F w = ⊥) :
    (S.q1 : Fin 11) ∉ (G.γA : Perm (Fin 11)).support := by
  rw [G.hsuppγ]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  have hpO : (S.p : Fin 11) ∈ MulAction.orbit F w := mem_orbitFinset.mp S.p.2
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact S.hq1ne (Subtype.ext h)
  · intro h
    have hfeq : S.f = S.f1 := by
      apply eq_of_smul_eq_of_mem_orbit hstab hpO
      change blockFP S = (((S.f1 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11))
        (S.p : Fin 11)
      rw [← h, S.hf1P]
    exact S.hf1out (hfeq ▸ Subgroup.mem_zpowers S.f1)
  · intro h
    have hf2eq : S.f ^ 2 = S.f1 := by
      apply eq_of_smul_eq_of_mem_orbit hstab hpO
      change (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (blockFP S) =
        (((S.f1 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (S.p : Fin 11)
      rw [← h, S.hf1P]
    have hf3 : S.f ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hF.2 (S.f : alternatingGroup (Fin 11)) S.f.2
    exact S.hf1out (mem_zpowers_of_sq_eq hf3 hf2eq)

private lemma block_q2_notsupp {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    {B : Set ↥(orbitFinset F w)} (S : BlockSetup F w B) (G : BlockGamma S)
    (hF : CFSG.Open.IsElemAbelian 3 F) (hstab : MulAction.stabilizer F w = ⊥) :
    (S.q2 : Fin 11) ∉ (G.γA : Perm (Fin 11)).support := by
  rw [G.hsuppγ]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  have hpO : (S.p : Fin 11) ∈ MulAction.orbit F w := mem_orbitFinset.mp S.p.2
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact S.hq2ne (Subtype.ext h)
  · intro h
    have hfeq : S.f = S.f2 := by
      apply eq_of_smul_eq_of_mem_orbit hstab hpO
      change blockFP S = (((S.f2 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11))
        (S.p : Fin 11)
      rw [← h, S.hf2P]
    exact S.hf2out (hfeq ▸ Subgroup.mem_zpowers S.f2)
  · intro h
    have hf2eq : S.f ^ 2 = S.f2 := by
      apply eq_of_smul_eq_of_mem_orbit hstab hpO
      change (((S.f : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (blockFP S) =
        (((S.f2 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) (S.p : Fin 11)
      rw [← h, S.hf2P]
    have hf3 : S.f ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hF.2 (S.f : alternatingGroup (Fin 11)) S.f.2
    exact S.hf2out (mem_zpowers_of_sq_eq hf3 hf2eq)

private lemma block_final {F : Subgroup (alternatingGroup (Fin 11))} {w : Fin 11}
    {u v : Fin 11} {B : Set ↥(orbitFinset F w)} (S : BlockSetup F w B) (G : BlockGamma S)
    (hq1 : (S.q1 : Fin 11) ∉ (G.γA : Perm (Fin 11)).support)
    (hq2 : (S.q2 : Fin 11) ∉ (G.γA : Perm (Fin 11)).support)
    (hstab : MulAction.stabilizer F w = ⊥)
    (hB : MulAction.IsBlock ↥(orbitG F w) B)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) : False := by
  letI : MulAction ↥(orbitG F w) ↥(orbitFinset F w) :=
    Subgroup.instMulActionSubtypeMem (S := orbitG F w)
  letI : MulAction ↥(orbitG F w) (Set ↥(orbitFinset F w)) := Set.mulActionSet
  have hfp_notin_B : (⟨blockFP S, S.hfpO⟩ : ↥(orbitFinset F w)) ∉ B := by
    intro hmem
    have hmemdiff : (⟨blockFP S, S.hfpO⟩ : ↥(orbitFinset F w)) ∈ B \ {S.p} := by
      refine Set.mem_diff _ |>.mpr ⟨hmem, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro h
      exact S.hfp_ne (Subtype.ext_iff.mp h)
    rw [S.hdiff] at hmemdiff
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemdiff
    rcases hmemdiff with h | h
    · have hval : blockFP S = (S.q1 : Fin 11) := congrArg Subtype.val h
      have hfeq : S.f = S.f1 := by
        apply eq_of_smul_eq_of_mem_orbit hstab (mem_orbitFinset.mp S.p.2)
        change blockFP S = (((S.f1 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11))
          (S.p : Fin 11)
        rw [hval, S.hf1P]
      exact S.hf1out (hfeq ▸ Subgroup.mem_zpowers S.f1)
    · have hval : blockFP S = (S.q2 : Fin 11) := congrArg Subtype.val h
      have hfeq : S.f = S.f2 := by
        apply eq_of_smul_eq_of_mem_orbit hstab (mem_orbitFinset.mp S.p.2)
        change blockFP S = (((S.f2 : F) : alternatingGroup (Fin 11)) : Perm (Fin 11))
          (S.p : Fin 11)
        rw [hval, S.hf2P]
      exact S.hf2out (hfeq ▸ Subgroup.mem_zpowers S.f2)
  have hσq1 : (G.σ : Perm ↥(orbitFinset F w)) S.q1 = S.q1 := by
    apply Subtype.ext
    rw [show (G.σ : Perm (↥(orbitFinset F w))) = ((G.γA : Perm (Fin 11)).subtypePerm
      (Equiv.Perm.isInvariant_of_support_le G.hγsupp)) from G.hσval]
    rw [subtypePerm_apply_val (u := u) (v := v) (h := G.γA) (hcompl := hcompl)
      (hfixu := hfixu) (hfixv := hfixv) (hh := G.hγH)]
    exact Equiv.Perm.notMem_support.mp hq1
  have hσq2 : (G.σ : Perm ↥(orbitFinset F w)) S.q2 = S.q2 := by
    apply Subtype.ext
    rw [show (G.σ : Perm (↥(orbitFinset F w))) = ((G.γA : Perm (Fin 11)).subtypePerm
      (Equiv.Perm.isInvariant_of_support_le G.hγsupp)) from G.hσval]
    rw [subtypePerm_apply_val (u := u) (v := v) (h := G.γA) (hcompl := hcompl)
      (hfixu := hfixu) (hfixv := hfixv) (hh := G.hγH)]
    exact Equiv.Perm.notMem_support.mp hq2
  have hσB_ne : G.σ • B ≠ B := by
    intro hEq
    have hp_mem : (G.σ : Perm ↥(orbitFinset F w)) ⟨(S.p : Fin 11), S.p.2⟩ ∈ G.σ • B := by
      have h := Set.smul_mem_smul_set (s := B) (a := G.σ) S.hpB
      change (G.σ : Perm ↥(orbitFinset F w)) S.p ∈ G.σ • B at h
      exact h
    rw [hEq] at hp_mem
    exact hfp_notin_B (G.hσp ▸ hp_mem)
  have hq1σB : S.q1 ∈ G.σ • B := by
    have h := Set.smul_mem_smul_set (s := B) (a := G.σ) S.hq1B
    change (G.σ : Perm ↥(orbitFinset F w)) S.q1 ∈ G.σ • B at h
    rwa [hσq1] at h
  have hnotdisj : ¬ Disjoint (G.σ • B) B := by
    rw [Set.not_disjoint_iff_nonempty_inter]
    exact ⟨S.q1, hq1σB, S.hq1B⟩
  rcases hB.smul_eq_or_disjoint G.σ with h | h
  · exact hσB_ne h
  · exact hnotdisj h

private lemma block_contradiction {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    {B : Set ↥(orbitFinset F w)}
    (hB : MulAction.IsBlock ↥(orbitG F w) B)
    (hBnt : B.Nontrivial) (hBne : B ≠ Set.univ) : False := by
  classical
  obtain ⟨S⟩ := exists_block_setup hF hFcard hw hcompl hfixu hfixv hcond hB hBnt hBne
  obtain ⟨G⟩ := exists_block_gamma S hF hcond hcompl hfixu hfixv
  have hstab : MulAction.stabilizer F w = ⊥ := stabilizer_w_eq_bot hw
  have hq1 := block_q1_notsupp S G hF hstab
  have hq2 := block_q2_notsupp S G hF hstab
  exact block_final S G hq1 hq2 hstab hB hcompl hfixu hfixv

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma orbitG_isPreprimitive {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    MulAction.IsPreprimitive ↥(orbitG F w) ↥(orbitFinset F w) := by
  classical
  letI : MulAction ↥(orbitG F w) ↥(orbitFinset F w) :=
    Subgroup.instMulActionSubtypeMem (S := orbitG F w)
  haveI : MulAction.IsPretransitive ↥(orbitG F w) ↥(orbitFinset F w) :=
    orbitG_isPretransitive hF hcond hFcard hw hcompl hfixu hfixv
  refine MulAction.IsPreprimitive.mk ?_
  intro B hB
  by_cases hBsub : B.Subsingleton
  · exact Or.inl hBsub
  · right
    by_contra hBne
    exact block_contradiction hF hcond hFcard hw hcompl hfixu hfixv hB
      (Set.not_subsingleton_iff.mp hBsub) hBne

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma alternating_le_orbitG {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    alternatingGroup ↥(orbitFinset F w) ≤ orbitG F w := by
  obtain ⟨σ, hσ3⟩ := orbitG_has_threeCycle hF hcond hFcard hw hcompl hfixu hfixv
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (orbitG_isPreprimitive hF hcond hFcard hw hcompl hfixu hfixv) hσ3 σ.2

private lemma mem_orbitH_of_fixes {F Y : Subgroup (alternatingGroup (Fin 11))}
    {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    {g : alternatingGroup (Fin 11)}
    (hgu : (g : Perm (Fin 11)) u = u) (hgv : (g : Perm (Fin 11)) v = v) :
    g ∈ orbitH F w := by
  classical
  have hgsupp : (g : Perm (Fin 11)).support ⊆ orbitFinset F w := by
    intro x hx
    rw [mem_orbitFinset]
    by_contra hxO
    have hxcompl : x ∈ ({u, v} : Set (Fin 11)) := by rwa [← hcompl]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxcompl
    rcases hxcompl with rfl | rfl
    · exact (Equiv.Perm.mem_support.mp hx) hgu
    · exact (Equiv.Perm.mem_support.mp hx) hgv
  let σ : Perm ↥(orbitFinset F w) :=
    (g : Perm (Fin 11)).subtypePerm (Equiv.Perm.isInvariant_of_support_le hgsupp)
  have hσeven : σ ∈ alternatingGroup ↥(orbitFinset F w) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    dsimp only [σ]
    have h := Equiv.Perm.sign_ofSubtype
      ((g : Perm (Fin 11)).subtypePerm (Equiv.Perm.isInvariant_of_support_le hgsupp))
    rw [subtypePerm_of_support_subset hgsupp] at h
    rw [Equiv.Perm.mem_alternatingGroup.mp g.2] at h
    exact h.symm
  have hσmem : σ ∈ orbitG F w :=
    alternating_le_orbitG hF hcond hFcard hw hcompl hfixu hfixv hσeven
  rw [orbitG, Subgroup.mem_comap] at hσmem
  obtain ⟨h, hhH, hhEq⟩ := Subgroup.mem_map.mp hσmem
  have hof : Equiv.Perm.ofSubtype σ = (g : Perm (Fin 11)) :=
    subtypePerm_of_support_subset hgsupp
  have h_eq : h = g := by
    apply Subtype.ext
    exact hhEq.trans hof
  rwa [← h_eq]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma cycleFactorsFinset_card_three {x : Perm (Fin 11)}
    (hx3 : x ^ 3 = 1) (hxsupp : x.support.card = 9) :
    x.cycleFactorsFinset.card = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : x.cycleType = Multiset.replicate x.cycleType.card 3 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hx3
  have hsum : x.cycleType.sum = 9 := by
    rw [Equiv.Perm.sum_cycleType, hxsupp]
  have hcard : x.cycleType.card = 3 := by
    rw [hcyc] at hsum
    simp at hsum
    omega
  have hdef : x.cycleType = x.cycleFactorsFinset.val.map (Finset.card ∘ Equiv.Perm.support) :=
    Equiv.Perm.cycleType_def x
  rw [hdef] at hcard
  rwa [Multiset.card_map] at hcard

private noncomputable def swapA (c : Perm (Fin 11)) (hc : c.IsThreeCycle) : Fin 11 :=
  Classical.choose (CFSG.AGLEmbeddingD2.AltCentralExtOne.exists_swap_inv_of_isThreeCycle hc)

private noncomputable def swapB (c : Perm (Fin 11)) (hc : c.IsThreeCycle) : Fin 11 :=
  Classical.choose (Classical.choose_spec
    (CFSG.AGLEmbeddingD2.AltCentralExtOne.exists_swap_inv_of_isThreeCycle hc))

private noncomputable def sw (c : Perm (Fin 11)) : Perm (Fin 11) := by
  classical
  exact if h : c.IsThreeCycle then swap (swapA c h) (swapB c h) else 1

private lemma sw_spec {c : Perm (Fin 11)} (hc : c.IsThreeCycle) :
    sw c = swap (swapA c hc) (swapB c hc) ∧
    swapA c hc ∈ c.support ∧ swapB c hc ∈ c.support ∧ swapA c hc ≠ swapB c hc ∧
    swap (swapA c hc) (swapB c hc) * c * (swap (swapA c hc) (swapB c hc))⁻¹ = c⁻¹ := by
  have hspec := Classical.choose_spec (Classical.choose_spec
    (CFSG.AGLEmbeddingD2.AltCentralExtOne.exists_swap_inv_of_isThreeCycle hc))
  refine ⟨?_, hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩
  simp only [sw, dif_pos hc]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma sw_commute_cycle {c d : Perm (Fin 11)} (hc : c.IsThreeCycle)
    (hdisj : Disjoint c.support d.support) : Commute (sw c) d := by
  obtain ⟨hsw, ha, hb, hab, -⟩ := sw_spec hc
  rw [hsw]
  exact CFSG.AGLEmbeddingD2.AltCentralExtOne.commute_swap_of_notMem_support hab
    (Finset.disjoint_left.1 hdisj ha) (Finset.disjoint_left.1 hdisj hb)

private lemma sign_sw {c : Perm (Fin 11)} (hc : c.IsThreeCycle) : sign (sw c) = -1 := by
  obtain ⟨hsw, -, -, hab, -⟩ := sw_spec hc
  rw [hsw, Equiv.Perm.sign_swap hab]

private lemma mem_normalizer_zpowers_of_conj_inv {xA τA : alternatingGroup (Fin 11)}
    (h : τA * xA * τA⁻¹ = xA⁻¹) :
    τA ∈ Subgroup.normalizer
      (Subgroup.zpowers xA : Set (alternatingGroup (Fin 11))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj τA : alternatingGroup (Fin 11) →*
    alternatingGroup (Fin 11)) (Subgroup.zpowers xA) = Subgroup.zpowers xA
  have hmap := MonoidHom.map_zpowers (MulAut.conj τA : alternatingGroup (Fin 11) →*
    alternatingGroup (Fin 11)) xA
  rw [hmap]
  change Subgroup.zpowers ((MulAut.conj τA) xA) = Subgroup.zpowers xA
  rw [MulAut.conj_apply, h, Subgroup.zpowers_inv]

private lemma support_sw_subset {c : Perm (Fin 11)} (hc : c.IsThreeCycle)
    {S : Finset (Fin 11)} (hcS : c.support ⊆ S) : (sw c).support ⊆ S := by
  obtain ⟨hsw, ha, hb, hab, -⟩ := sw_spec hc
  rw [hsw, Equiv.Perm.support_swap hab]
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hcS ha
  · rw [Finset.mem_singleton.mp hx]
    exact hcS hb

private lemma sw_apply_of_notMem_support {c : Perm (Fin 11)} (hc : c.IsThreeCycle)
    {a : Fin 11} (ha : a ∉ c.support) : sw c a = a :=
  Equiv.Perm.notMem_support.mp (fun h => ha (support_sw_subset hc (Finset.Subset.refl _) h))

private lemma commute_swap_of_support_subset {α : Type*} [Fintype α] [DecidableEq α]
    {c : Perm α} {S : Finset α} {u v : α} (huv : u ≠ v) (hcS : c.support ⊆ S)
    (huS : u ∉ S) (hvS : v ∉ S) : Commute (swap u v) c :=
  CFSG.AGLEmbeddingD2.AltCentralExtOne.commute_swap_of_notMem_support huv
    (fun h => huS (hcS h)) (fun h => hvS (hcS h))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma cycleFactor_isThreeCycle {x c : Perm (Fin 11)} (hx3 : x ^ 3 = 1)
    (hxne : x ≠ 1) (hc : c ∈ x.cycleFactorsFinset) : c.IsThreeCycle := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxorder : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hcorder : orderOf c = 3 :=
    CFSG.RankThree.GroupTheory.orderOf_eq_of_mem_cycleFactorsFinset
      Nat.prime_three hxorder hc
  have hccycle : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  exact card_support_eq_three_iff.mp (by rw [← hccycle.orderOf, hcorder])

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

local instance instMulActionPermSet : MulAction (Perm (Fin 11)) (Set (Fin 11)) := Set.mulActionSet

private lemma perm_smul_pair_eq (σ : Perm (Fin 11)) {i j : Fin 11} (hij : i ≠ j) :
    σ • ({i, j} : Set (Fin 11)) = {i, j} ↔
      (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i) := by
  rw [show σ • ({i, j} : Set (Fin 11)) = σ '' ({i, j} : Set (Fin 11)) from rfl]
  rw [Set.image_pair]
  constructor
  · intro h
    have hi : σ i ∈ ({i, j} : Set (Fin 11)) := by
      rw [← h]
      exact Set.mem_insert _ _
    have hj : σ j ∈ ({i, j} : Set (Fin 11)) := by
      rw [← h]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with h1 | h1 <;> rcases hj with h2 | h2
    · exact absurd (σ.injective (h1.trans h2.symm)) hij
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (σ.injective (h1.trans h2.symm)) hij
  · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
    · rw [hi, hj]
    · rw [hi, hj, Set.pair_comm]

private lemma a11TwoSetStab_eq_stabilizer {i j : Fin 11} (hij : i ≠ j) :
    a11TwoSetStab i j =
      MulAction.stabilizer (alternatingGroup (Fin 11)) ({i, j} : Set (Fin 11)) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff]
  change (((σ : Perm (Fin 11)) i = i ∧ (σ : Perm (Fin 11)) j = j) ∨
      ((σ : Perm (Fin 11)) i = j ∧ (σ : Perm (Fin 11)) j = i)) ↔
    (σ : Perm (Fin 11)) • ({i, j} : Set (Fin 11)) = {i, j}
  exact (perm_smul_pair_eq (σ : Perm (Fin 11)) hij).symm

private lemma a11TwoSetStab_isCoatom {i j : Fin 11} (hij : i ≠ j) :
    IsCoatom (a11TwoSetStab i j) := by
  rw [a11TwoSetStab_eq_stabilizer hij]
  refine alternatingGroup.isCoatom_stabilizer_of_ncard_lt_ncard_compl ?_ ?_
  · exact Set.nontrivial_pair (α := Fin 11) hij
  · rw [Set.ncard_pair hij]
    have hcompl : (({i, j} : Set (Fin 11))ᶜ).ncard = 9 := by
      rw [Set.ncard_compl]
      rw [Set.ncard_pair hij]
      simp [Nat.card_fin]
    rw [hcompl]
    norm_num

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma conj_three_inv {G : Type*} [Group G] {a b c t u v s : G}
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ht : t * a * t⁻¹ = a⁻¹) (hu : u * b * u⁻¹ = b⁻¹) (hv : v * c * v⁻¹ = c⁻¹)
    (htb : Commute t b) (htc : Commute t c) (hua : Commute u a) (huc : Commute u c)
    (hva : Commute v a) (hvb : Commute v b)
    (hsa : Commute s a) (hsb : Commute s b) (hsc : Commute s c) :
    (t * u * v * s) * (a * b * c) * (t * u * v * s)⁻¹ = (a * b * c)⁻¹ := by
  have hconj : ∀ (x y : G), Commute x y → x * y * x⁻¹ = y := by
    intro x y hxy
    rw [hxy.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconj1 : v * (a * b * c) * v⁻¹ = a * b * c⁻¹ := by
    calc v * (a * b * c) * v⁻¹
        = (v * a * v⁻¹) * (v * b * v⁻¹) * (v * c * v⁻¹) := by group
      _ = a * b * c⁻¹ := by rw [hconj v a hva, hconj v b hvb, hv]
  have hconj2 : u * (a * b * c⁻¹) * u⁻¹ = a * b⁻¹ * c⁻¹ := by
    calc u * (a * b * c⁻¹) * u⁻¹
        = (u * a * u⁻¹) * (u * b * u⁻¹) * (u * c⁻¹ * u⁻¹) := by group
      _ = a * b⁻¹ * c⁻¹ := by
        rw [hconj u a hua, hu, hconj u c⁻¹ huc.inv_right]
  have hconj3 : t * (a * b⁻¹ * c⁻¹) * t⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ := by
    calc t * (a * b⁻¹ * c⁻¹) * t⁻¹
        = (t * a * t⁻¹) * (t * b⁻¹ * t⁻¹) * (t * c⁻¹ * t⁻¹) := by group
      _ = a⁻¹ * b⁻¹ * c⁻¹ := by
        rw [ht, hconj t b⁻¹ htb.inv_right, hconj t c⁻¹ htc.inv_right]
  have hfin : (a * b * c)⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ := by
    rw [show a * b * c = a * (b * c) from by group]
    rw [(hab.mul_right hac).mul_inv, hbc.mul_inv]
    exact (mul_assoc _ _ _).symm
  calc (t * u * v * s) * (a * b * c) * (t * u * v * s)⁻¹
      = t * u * v * (s * (a * b * c) * s⁻¹) * v⁻¹ * u⁻¹ * t⁻¹ := by group
    _ = t * u * v * (a * b * c) * v⁻¹ * u⁻¹ * t⁻¹ := by
        rw [hconj s (a * b * c) ((hsa.mul_right hsb).mul_right hsc)]
    _ = t * u * (v * (a * b * c) * v⁻¹) * u⁻¹ * t⁻¹ := by group
    _ = t * u * (a * b * c⁻¹) * u⁻¹ * t⁻¹ := by rw [hconj1]
    _ = t * (u * (a * b * c⁻¹) * u⁻¹) * t⁻¹ := by group
    _ = t * (a * b⁻¹ * c⁻¹) * t⁻¹ := by rw [hconj2]
    _ = a⁻¹ * b⁻¹ * c⁻¹ := hconj3
    _ = (a * b * c)⁻¹ := by rw [hfin]

private lemma cycleFactors_three_decomposition {x : Perm (Fin 11)}
    (hx3 : x ^ 3 = 1) (hxsupp : x.support.card = 9) :
    ∃ c₁ c₂ c₃ : Perm (Fin 11), c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
      x = c₁ * c₂ * c₃ ∧ c₁.IsThreeCycle ∧ c₂.IsThreeCycle ∧ c₃.IsThreeCycle ∧
      Disjoint c₁.support c₂.support ∧ Disjoint c₁.support c₃.support ∧
      Disjoint c₂.support c₃.support := by
  classical
  have hcard : x.cycleFactorsFinset.card = 3 :=
    cycleFactorsFinset_card_three hx3 hxsupp
  obtain ⟨c₁, c₂, c₃, hc12, hc13, hc23, hcyc⟩ := Finset.card_eq_three.mp hcard
  have hc1 : c₁ ∈ x.cycleFactorsFinset := by rw [hcyc]; simp
  have hc2 : c₂ ∈ x.cycleFactorsFinset := by rw [hcyc]; simp
  have hc3 : c₃ ∈ x.cycleFactorsFinset := by rw [hcyc]; simp
  obtain ⟨hdisj, hprod'⟩ := (Equiv.Perm.cycleFactorsFinset_eq_finset.mp hcyc).2
  have hprod : x = c₁ * c₂ * c₃ := by
    rw [← hprod']
    rw [Finset.noncommProd_insert_of_notMem]
    · rw [Finset.noncommProd_insert_of_notMem]
      · rw [Finset.noncommProd_singleton]
        rw [mul_assoc]
        rfl
      · simp [hc23]
    · simp [hc12, hc13]
  have hpd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint x
  have hd12 : Disjoint c₁.support c₂.support := by
    have h := hpd hc1 hc2 hc12
    rwa [Equiv.Perm.disjoint_iff_disjoint_support] at h
  have hd13 : Disjoint c₁.support c₃.support := by
    have h := hpd hc1 hc3 hc13
    rwa [Equiv.Perm.disjoint_iff_disjoint_support] at h
  have hd23 : Disjoint c₂.support c₃.support := by
    have h := hpd hc2 hc3 hc23
    rwa [Equiv.Perm.disjoint_iff_disjoint_support] at h
  have ht1 : c₁.IsThreeCycle := cycleFactor_isThreeCycle hx3 (by
    intro hx1; rw [hx1] at hxsupp; simp at hxsupp) hc1
  have ht2 : c₂.IsThreeCycle := cycleFactor_isThreeCycle hx3 (by
    intro hx1; rw [hx1] at hxsupp; simp at hxsupp) hc2
  have ht3 : c₃.IsThreeCycle := cycleFactor_isThreeCycle hx3 (by
    intro hx1; rw [hx1] at hxsupp; simp at hxsupp) hc3
  exact ⟨c₁, c₂, c₃, hc12, hc13, hc23, hprod, ht1, ht2, ht3, hd12, hd13, hd23⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma exists_tau_x {F : Subgroup (alternatingGroup (Fin 11))} {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    ∃ x : F, x ≠ 1 ∧
      ((((x : F) : alternatingGroup (Fin 11)) : Perm (Fin 11))).support.card = 9 := by
  classical
  have hcardF : Fintype.card F = 9 := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hxne⟩ : ∃ x : F, x ≠ 1 :=
    Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card F) 1
  let xP : Perm (Fin 11) := ((x : F) : alternatingGroup (Fin 11))
  have hsupp_le : xP.support ⊆ orbitFinset F w :=
    support_subset_orbitFinset hcompl hfixu hfixv x
  have hO_le : orbitFinset F w ⊆ xP.support := by
    intro p hp
    rw [Equiv.Perm.mem_support]
    exact moves_of_mem_orbit hF.1 hw hxne (mem_orbitFinset.mp hp)
  have hsupp9 : xP.support.card = 9 := by
    have hsupp_eq : xP.support = orbitFinset F w :=
      Finset.Subset.antisymm hsupp_le hO_le
    rw [hsupp_eq, orbitFinset_card hFcard hw]
  exact ⟨x, hxne, hsupp9⟩

private lemma exists_tau_cycles {F : Subgroup (alternatingGroup (Fin 11))} {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    ∃ (x : F) (_hx : x ≠ 1) (c₁ c₂ c₃ : Perm (Fin 11)),
      (((x : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) = c₁ * c₂ * c₃ ∧
      c₁.IsThreeCycle ∧ c₂.IsThreeCycle ∧ c₃.IsThreeCycle ∧
      Disjoint c₁.support c₂.support ∧ Disjoint c₁.support c₃.support ∧
      Disjoint c₂.support c₃.support ∧
      u ∉ c₁.support ∧ u ∉ c₂.support ∧ u ∉ c₃.support ∧
      v ∉ c₁.support ∧ v ∉ c₂.support ∧ v ∉ c₃.support := by
  classical
  obtain ⟨x, hxne, hsupp9⟩ := exists_tau_x hF hFcard hw hcompl hfixu hfixv
  let xP : Perm (Fin 11) := ((x : F) : alternatingGroup (Fin 11))
  have hx3 : xP ^ 3 = 1 := by
    have h := hF.2 ((x : F) : alternatingGroup (Fin 11)) x.2
    simpa [xP] using congrArg (fun g : alternatingGroup (Fin 11) =>
      (g : Perm (Fin 11))) h
  have hsupp_le : xP.support ⊆ orbitFinset F w :=
    support_subset_orbitFinset hcompl hfixu hfixv x
  obtain ⟨c₁, c₂, c₃, hc12, hc13, hc23, hxprod, hc1_3, hc2_3, hc3_3, hd12, hd13, hd23⟩ :=
    cycleFactors_three_decomposition hx3 hsupp9
  have hd12' : Disjoint c₁ c₂ := Equiv.Perm.disjoint_iff_disjoint_support.mpr hd12
  have hd13' : Disjoint c₁ c₃ := Equiv.Perm.disjoint_iff_disjoint_support.mpr hd13
  have hd23' : Disjoint c₂ c₃ := Equiv.Perm.disjoint_iff_disjoint_support.mpr hd23
  have hsupp_x : xP.support = c₁.support ∪ c₂.support ∪ c₃.support := by
    rw [hxprod, Equiv.Perm.Disjoint.support_mul (hd13'.mul_left hd23'),
      Equiv.Perm.Disjoint.support_mul hd12']
  have hc1O : c₁.support ⊆ orbitFinset F w := by
    intro a ha
    apply hsupp_le
    rw [hsupp_x]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
  have hc2O : c₂.support ⊆ orbitFinset F w := by
    intro a ha
    apply hsupp_le
    rw [hsupp_x]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
  have hc3O : c₃.support ⊆ orbitFinset F w := by
    intro a ha
    apply hsupp_le
    rw [hsupp_x]
    exact Finset.mem_union_right _ ha
  have huO : u ∉ orbitFinset F w := by
    intro huo
    have hu' : u ∈ (MulAction.orbit F w)ᶜ := by
      rw [hcompl]; exact Set.mem_insert u {v}
    exact hu' (mem_orbitFinset.mp huo)
  have hvO : v ∉ orbitFinset F w := by
    intro hvo
    have hv' : v ∈ (MulAction.orbit F w)ᶜ := by
      rw [hcompl]; exact Set.mem_insert_of_mem _ (Set.mem_singleton v)
    exact hv' (mem_orbitFinset.mp hvo)
  exact ⟨x, hxne, c₁, c₂, c₃, hxprod, hc1_3, hc2_3, hc3_3, hd12, hd13, hd23,
    fun h => huO (hc1O h), fun h => huO (hc2O h), fun h => huO (hc3O h),
    fun h => hvO (hc1O h), fun h => hvO (hc2O h), fun h => hvO (hc3O h)⟩

private lemma exists_swapping_normalizer_aux {F : Subgroup (alternatingGroup (Fin 11))}
    {u v : Fin 11} {x : F} {c₁ c₂ c₃ : Perm (Fin 11)}
    (hxprod : (((x : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) = c₁ * c₂ * c₃)
    (hc₁ : c₁.IsThreeCycle) (hc₂ : c₂.IsThreeCycle) (hc₃ : c₃.IsThreeCycle)
    (hd₁₂ : Disjoint c₁.support c₂.support) (hd₁₃ : Disjoint c₁.support c₃.support)
    (hd₂₃ : Disjoint c₂.support c₃.support)
    (hu₁ : u ∉ c₁.support) (hu₂ : u ∉ c₂.support) (hu₃ : u ∉ c₃.support)
    (hv₁ : v ∉ c₁.support) (hv₂ : v ∉ c₂.support) (hv₃ : v ∉ c₃.support)
    (huv : u ≠ v) :
    ∃ τ : alternatingGroup (Fin 11),
      ((τ : Perm (Fin 11))) u = v ∧ ((τ : Perm (Fin 11))) v = u ∧
      τ ∈ Subgroup.normalizer (Subgroup.zpowers
        ((x : F) : alternatingGroup (Fin 11)) : Set (alternatingGroup (Fin 11))) := by
  let t₁ : Perm (Fin 11) := sw c₁
  let t₂ : Perm (Fin 11) := sw c₂; let t₃ : Perm (Fin 11) := sw c₃
  have ht1u : t₁ u = u := by simpa [t₁] using sw_apply_of_notMem_support hc₁ hu₁
  have ht1v : t₁ v = v := by simpa [t₁] using sw_apply_of_notMem_support hc₁ hv₁
  have ht2u : t₂ u = u := by simpa [t₂] using sw_apply_of_notMem_support hc₂ hu₂
  have ht2v : t₂ v = v := by simpa [t₂] using sw_apply_of_notMem_support hc₂ hv₂
  have ht3u : t₃ u = u := by simpa [t₃] using sw_apply_of_notMem_support hc₃ hu₃
  have ht3v : t₃ v = v := by simpa [t₃] using sw_apply_of_notMem_support hc₃ hv₃
  have ht1c2 : Commute t₁ c₂ := by simpa [t₁] using sw_commute_cycle hc₁ hd₁₂
  have ht1c3 : Commute t₁ c₃ := by simpa [t₁] using sw_commute_cycle hc₁ hd₁₃
  have ht2c1 : Commute t₂ c₁ := by simpa [t₂] using sw_commute_cycle hc₂ hd₁₂.symm
  have ht2c3 : Commute t₂ c₃ := by simpa [t₂] using sw_commute_cycle hc₂ hd₂₃
  have ht3c1 : Commute t₃ c₁ := by simpa [t₃] using sw_commute_cycle hc₃ hd₁₃.symm
  have ht3c2 : Commute t₃ c₂ := by simpa [t₃] using sw_commute_cycle hc₃ hd₂₃.symm
  have hs1 : Commute (swap u v) c₁ :=
    commute_swap_of_support_subset huv (Finset.Subset.refl _) hu₁ hv₁
  have hs2 : Commute (swap u v) c₂ :=
    commute_swap_of_support_subset huv (Finset.Subset.refl _) hu₂ hv₂
  have hs3 : Commute (swap u v) c₃ :=
    commute_swap_of_support_subset huv (Finset.Subset.refl _) hu₃ hv₃
  have ht1inv : t₁ * c₁ * t₁⁻¹ = c₁⁻¹ := by
    simpa [t₁, (sw_spec hc₁).1] using (sw_spec hc₁).2.2.2.2
  have ht2inv : t₂ * c₂ * t₂⁻¹ = c₂⁻¹ := by
    simpa [t₂, (sw_spec hc₂).1] using (sw_spec hc₂).2.2.2.2
  have ht3inv : t₃ * c₃ * t₃⁻¹ = c₃⁻¹ := by
    simpa [t₃, (sw_spec hc₃).1] using (sw_spec hc₃).2.2.2.2
  have hsign1 : t₁.sign = -1 := by simpa [t₁] using sign_sw hc₁
  have hsign2 : t₂.sign = -1 := by simpa [t₂] using sign_sw hc₂
  have hsign3 : t₃.sign = -1 := by simpa [t₃] using sign_sw hc₃
  let τP : Perm (Fin 11) := t₁ * t₂ * t₃ * swap u v
  have hτsign : τP.sign = 1 := by
    simp only [τP, Equiv.Perm.sign_mul, hsign1, hsign2, hsign3,
      Equiv.Perm.sign_swap huv]
    norm_num
  let τA : alternatingGroup (Fin 11) :=
    ⟨τP, by rw [Equiv.Perm.mem_alternatingGroup]; exact hτsign⟩
  have hτu : (τA : Perm (Fin 11)) u = v := by
    change τP u = v
    simp only [τP, Equiv.Perm.mul_apply, Equiv.swap_apply_left, ht3v, ht2v, ht1v]
  have hτv : (τA : Perm (Fin 11)) v = u := by
    change τP v = u
    simp only [τP, Equiv.Perm.mul_apply, Equiv.swap_apply_right, ht3u, ht2u, ht1u]
  have hconjP : τP * (((x : F) : alternatingGroup (Fin 11)) : Perm (Fin 11)) * τP⁻¹ =
      (((x : F) : alternatingGroup (Fin 11)) : Perm (Fin 11))⁻¹ := by
    have hmain := conj_three_inv (a := c₁) (b := c₂) (c := c₃) (t := t₁) (u := t₂)
      (v := t₃) (s := swap u v)
      (Equiv.Perm.disjoint_iff_disjoint_support.mpr hd₁₂).commute
      (Equiv.Perm.disjoint_iff_disjoint_support.mpr hd₁₃).commute
      (Equiv.Perm.disjoint_iff_disjoint_support.mpr hd₂₃).commute
      ht1inv ht2inv ht3inv ht1c2 ht1c3 ht2c1 ht2c3 ht3c1 ht3c2 hs1 hs2 hs3
    rw [hxprod]
    exact hmain
  exact ⟨τA, hτu, hτv, mem_normalizer_zpowers_of_conj_inv (by
    apply Subtype.ext
    exact hconjP)⟩

private lemma exists_swapping_normalizer
    {F : Subgroup (alternatingGroup (Fin 11))} {w u v : Fin 11}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hFcard : Nat.card F = 9)
    (hw : ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w)
    (huv : u ≠ v)
    (hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)))
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v) :
    ∃ (x : F) (_hx : x ≠ 1) (τ : alternatingGroup (Fin 11)),
      ((τ : Perm (Fin 11))) u = v ∧ ((τ : Perm (Fin 11))) v = u ∧
      τ ∈ Subgroup.normalizer (Subgroup.zpowers
        (x : alternatingGroup (Fin 11)) : Set (alternatingGroup (Fin 11))) := by
  classical
  obtain ⟨x, hxne, c₁, c₂, c₃, hxprod, hc₁, hc₂, hc₃, hd₁₂, hd₁₃, hd₂₃,
    hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩ :=
    exists_tau_cycles hF hFcard hw hcompl hfixu hfixv
  obtain ⟨τ, hτu, hτv, hτnorm⟩ :=
    exists_swapping_normalizer_aux hxprod hc₁ hc₂ hc₃ hd₁₂ hd₁₃ hd₂₃
      hu₁ hu₂ hu₃ hv₁ hv₂ hv₃ huv
  exact ⟨x, hxne, τ, hτu, hτv, hτnorm⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma caseA_tc_mem_Y
    {F Y : Subgroup (alternatingGroup (Fin 11))} {u v k : Fin 11}
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hA : ∀ k : Fin 11, ∃ x : F, x ≠ 1 ∧
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) k = k)
    (huv : u ≠ v) (huk : u ≠ k) (hvk : v ≠ k) :
    (tc u v k : Perm (Fin 11)) ∈
      Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) := by
  classical
  obtain ⟨x, hxne, hxk⟩ := hA k
  let xP : Perm (Fin 11) := ((x : F) : alternatingGroup (Fin 11))
  have hxku : xP u = u := hfixu x
  have hxkv : xP v = v := hfixv x
  have hxkk : xP k = k := hxk
  have hswapuv : Commute (swap u v) xP :=
    CFSG.AGLEmbeddingD2.AltCentralExtOne.commute_swap_of_notMem_support huv
      (by rw [Equiv.Perm.notMem_support]; exact hxku)
      (by rw [Equiv.Perm.notMem_support]; exact hxkv)
  have hswapvk : Commute (swap v k) xP :=
    CFSG.AGLEmbeddingD2.AltCentralExtOne.commute_swap_of_notMem_support hvk
      (by rw [Equiv.Perm.notMem_support]; exact hxkv)
      (by rw [Equiv.Perm.notMem_support]; exact hxkk)
  have hcommP : Commute (tc u v k) xP := by
    simpa [tc] using hswapuv.mul_left hswapvk
  have htc3 : (tc u v k).IsThreeCycle := tc_isThreeCycle huv huk hvk
  let cA : alternatingGroup (Fin 11) := ⟨tc u v k, htc3.mem_alternatingGroup⟩
  have hcommA : Commute cA ((x : F) : alternatingGroup (Fin 11)) := by
    rw [Commute]
    apply Subtype.ext
    change tc u v k * xP = xP * tc u v k
    exact hcommP.eq
  have hxneA : ((x : F) : alternatingGroup (Fin 11)) ≠ 1 := by
    intro h
    exact hxne (Subtype.ext h)
  exact Subgroup.mem_map.mpr
    ⟨cA, mem_Y_of_commute (xA := ((x : F) : alternatingGroup (Fin 11)))
      hcond x.2 hxneA hcommA, rfl⟩

private lemma caseA_pairThreeCycles_le
    {F Y : Subgroup (alternatingGroup (Fin 11))} {u v : Fin 11}
    (hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u)
    (hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hA : ∀ k : Fin 11, ∃ x : F, x ≠ 1 ∧
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) k = k)
    (huv : u ≠ v) :
    pairThreeCycles u v ⊆
      (Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) : Set (Perm (Fin 11))) := by
  classical
  intro g hg
  obtain ⟨hg3, hgu, hgv⟩ := hg
  have hcard : g.support.card = 3 := hg3.card_support
  have hv' : v ∈ g.support.erase u := Finset.mem_erase.mpr ⟨huv.symm, hgv⟩
  have hcard2 : (g.support.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem hgu, hcard]
  have hcard3 : ((g.support.erase u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hv', hcard2]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard3
  have hkT : k ∈ (g.support.erase u).erase v := by rw [hk]; simp
  have hk_notv : k ≠ v := (Finset.mem_erase.mp hkT).1
  have hk_notu : k ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hkT).2).1
  have hsup : g.support = {u, v, k} := by
    have h1 : insert v ((g.support.erase u).erase v) = g.support.erase u :=
      Finset.insert_erase hv'
    have h2 : insert u (g.support.erase u) = g.support := Finset.insert_erase hgu
    calc g.support = insert u (g.support.erase u) := h2.symm
      _ = insert u (insert v ((g.support.erase u).erase v)) := by
          conv_lhs => rw [← h1]
      _ = insert u (insert v {k}) := by rw [hk]
      _ = {u, v, k} := rfl
  have huk : u ≠ k := Ne.symm hk_notu
  have hvk : v ≠ k := Ne.symm hk_notv
  have htc3 : (tc u v k).IsThreeCycle := tc_isThreeCycle huv huk hvk
  have hmem : (tc u v k : Perm (Fin 11)) ∈
      Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) :=
    caseA_tc_mem_Y hfixu hfixv hcond hA huv huk hvk
  have hmem_inv : ((tc u v k)⁻¹ : Perm (Fin 11)) ∈
      Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) :=
    Subgroup.inv_mem _ hmem
  have hge : g = tc u v k ∨ g = (tc u v k)⁻¹ :=
    threeCycle_eq_or_eq_inv_of_support_eq hg3 htc3
      (by rw [hsup, tc_support huv huk hvk])
  rcases hge with h | h
  · rwa [h]
  · rwa [h]

private lemma caseA_eq_top
    {F Y : Subgroup (alternatingGroup (Fin 11))}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hA : ∀ k : Fin 11, ∃ x : F, x ≠ 1 ∧
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) k = k) :
    Y = ⊤ := by
  classical
  obtain ⟨u, v, huv, hufix, hvfix⟩ := exists_two_fixed_points hF hFcard
  have hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u := by
    intro x
    exact MulAction.mem_fixedPoints.mp hufix x
  have hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v := by
    intro x
    exact MulAction.mem_fixedPoints.mp hvfix x
  have hpair : pairThreeCycles u v ⊆
      (Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) : Set (Perm (Fin 11))) :=
    caseA_pairThreeCycles_le hfixu hfixv hcond hA huv
  have hclosure : Subgroup.closure (pairThreeCycles u v) ≤
      Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) :=
    (Subgroup.closure_le (Y.map (Subgroup.subtype (alternatingGroup (Fin 11))))).mpr hpair
  have halt : alternatingGroup (Fin 11) ≤
      Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) := by
    have h := hclosure
    rw [closure_pairThreeCycles_eq_alternating (α := Fin 11) huv
      (by norm_num : 6 ≤ Fintype.card (Fin 11))] at h
    exact h
  rw [eq_top_iff]
  intro g _
  have hg' : (g : Perm (Fin 11)) ∈
      Y.map (Subgroup.subtype (alternatingGroup (Fin 11))) :=
    halt (show (g : Perm (Fin 11)) ∈ alternatingGroup (Fin 11) from g.2)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hg'
  rwa [show y = g from Subtype.ext hyx] at hy

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private lemma kFact_caseB {F Y : Subgroup (alternatingGroup (Fin 11))}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hB : ∃ w : Fin 11, ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w) :
    Y = ⊤ ∨ ∃ i j : Fin 11, i ≠ j ∧ Y = a11TwoSetStab i j := by
  classical
  obtain ⟨w, hw⟩ := hB
  obtain ⟨u, v, huv, hufix, hvfix⟩ := exists_two_fixed_points hF hFcard
  have hfixu : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u := by
    intro x
    exact MulAction.mem_fixedPoints.mp hufix x
  have hfixv : ∀ x : F, (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v := by
    intro x
    exact MulAction.mem_fixedPoints.mp hvfix x
  have hcompl : (MulAction.orbit F w)ᶜ = ({u, v} : Set (Fin 11)) :=
    orbit_compl_eq_pair hFcard hw huv hufix hvfix
  have hHleY : orbitH F w ≤ Y := orbitH_le_Y hF hcond hw
  obtain ⟨x, hxne, τ, hτu, hτv, hτnorm⟩ :=
    exists_swapping_normalizer hF hFcard hw huv hcompl hfixu hfixv
  have hτY : τ ∈ Y :=
    hcond (Subgroup.zpowers ((x : F) : alternatingGroup (Fin 11)))
      (Subgroup.zpowers_le.mpr x.2)
      (by
        rw [Subgroup.zpowers_ne_bot]
        intro h
        exact hxne (Subtype.ext h))
      hτnorm
  have hτinv_u : ((τ⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11)) u = v := by
    rw [show ((τ⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
        (τ : Perm (Fin 11)).symm from rfl, Equiv.symm_apply_eq]
    exact hτv.symm
  have hτinv_v : ((τ⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11)) v = u := by
    rw [show ((τ⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
        (τ : Perm (Fin 11)).symm from rfl, Equiv.symm_apply_eq]
    exact hτu.symm
  have hSleY : a11TwoSetStab u v ≤ Y := by
    intro σ hσ
    rcases hσ with ⟨hσu, hσv⟩ | ⟨hσu, hσv⟩
    · exact hHleY (mem_orbitH_of_fixes hF hcond hFcard hw hcompl hfixu hfixv hσu hσv)
    · have hfixu' : (((τ⁻¹ * σ : alternatingGroup (Fin 11)) : Perm (Fin 11))) u = u := by
        change ((τ⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11))
          (((σ : alternatingGroup (Fin 11)) : Perm (Fin 11)) u) = u
        rw [hσu, hτinv_v]
      have hfixv' : (((τ⁻¹ * σ : alternatingGroup (Fin 11)) : Perm (Fin 11))) v = v := by
        change ((τ⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11))
          (((σ : alternatingGroup (Fin 11)) : Perm (Fin 11)) v) = v
        rw [hσv, hτinv_u]
      have hmem : τ⁻¹ * σ ∈ orbitH F w :=
        mem_orbitH_of_fixes hF hcond hFcard hw hcompl hfixu hfixv hfixu' hfixv'
      rw [show σ = τ * (τ⁻¹ * σ) from by group]
      exact Y.mul_mem hτY (hHleY hmem)
  have hcoatom : IsCoatom (a11TwoSetStab u v) := a11TwoSetStab_isCoatom huv
  rcases hcoatom.le_iff.mp hSleY with h | h
  · exact Or.inl h
  · exact Or.inr ⟨u, v, huv, h⟩

private lemma kFact_caseA {F Y : Subgroup (alternatingGroup (Fin 11))}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9)
    (hcond : ∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (alternatingGroup (Fin 11))) ≤ Y)
    (hB : ¬ ∃ w : Fin 11, ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w) :
    Y = ⊤ ∨ ∃ i j : Fin 11, i ≠ j ∧ Y = a11TwoSetStab i j := by
  classical
  apply Or.inl
  apply caseA_eq_top hF hFcard hcond
  intro k
  by_contra h
  apply hB
  refine ⟨k, ?_⟩
  intro x hx
  by_contra hne
  exact h ⟨x, hx, by simpa using hne⟩

theorem kFactA11GammaTwoSet_holds : KFactA11GammaTwoSet := by
  intro F Y hF hFcard hcond
  by_cases hB : ∃ w : Fin 11, ∀ x : F, x ≠ 1 →
      (((x : alternatingGroup (Fin 11)) : Perm (Fin 11))) w ≠ w
  · exact kFact_caseB hF hFcard hcond hB
  · exact kFact_caseA hF hFcard hcond hB

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
