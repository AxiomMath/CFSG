module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

@[expose] def seg27AltFix (F : Set (Fin 8)) : Subgroup (Equiv.Perm (Fin 8)) :=
  alternatingGroup (Fin 8) ⊓ fixingSubgroup (Equiv.Perm (Fin 8)) F

private lemma seg27_cycleType_eq_singleton_of_prime_order (g : Equiv.Perm (Fin 8)) {p : ℕ}
    (hp : p.Prime) (hp4 : 4 < p) (hg : orderOf g = p) : g.cycleType = {p} := by
  have hprime : (orderOf g).Prime := by rwa [hg]
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hprime
  rw [hg] at hn
  have hsum : (Multiset.replicate (n + 1) p).sum ≤ 8 := by
    have h := Equiv.Perm.sum_cycleType_le g
    rw [hn] at h
    simpa using h
  simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hp5 : 5 ≤ p := by omega
  have h5 : (n + 1) * 5 ≤ 8 := (Nat.mul_le_mul_left (n + 1) hp5).trans hsum
  have hn0 : n = 0 := by omega
  rw [hn0] at hn
  simpa only [Nat.zero_add, Multiset.replicate_one] using hn

theorem seg27_mem_altFix {F : Set (Fin 8)} {g : Equiv.Perm (Fin 8)} :
    g ∈ seg27AltFix F ↔ g ∈ alternatingGroup (Fin 8) ∧ ∀ x ∈ F, g x = x := by
  rw [seg27AltFix, Subgroup.mem_inf, mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => by simpa using h2 x hx⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => by simpa using h2 x hx⟩

theorem seg27_card_altFix (F : Finset (Fin 8)) (hF : F.card ≤ 6) :
    Nat.card (seg27AltFix (F : Set (Fin 8))) = (8 - F.card).factorial / 2 := by
  haveI hmt8 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8)
      (Nat.card (Fin 8) - 2) :=
    alternatingGroup.isMultiplyPretransitive (Fin 8)
  have h8 : Nat.card (Fin 8) = 8 := Nat.card_fin 8
  have hF' : F.card ≤ Nat.card (Fin 8) - 2 := by rw [h8]; omega
  have hmt : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) F.card :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 8) - 2) hF' (Nat.sub_le _ _)
  have hindex : (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))).index *
      (8 - F.card).factorial = Nat.factorial 8 := by
    have h := hmt.index_of_fixingSubgroup_mul (s := (F : Set (Fin 8)))
      (by rw [Set.ncard_coe_finset])
    simpa [h8] using h
  have hcard_mul : Nat.card (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))) *
      (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))).index =
      Nat.card (alternatingGroup (Fin 8)) :=
    Subgroup.card_mul_index _
  have hGcard : Nat.card (alternatingGroup (Fin 8)) = Nat.factorial 8 / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have htwice : 2 * Nat.card (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))) =
      (8 - F.card).factorial := by
    have hA : (2 * Nat.card (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8)))) *
        (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))).index = Nat.factorial 8 := by
      rw [mul_assoc, hcard_mul, hGcard]
      norm_num [Nat.factorial]
    have hidxne : (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))).index ≠ 0 := by
      intro h0
      have : Nat.card (alternatingGroup (Fin 8)) = 0 := by rw [← hcard_mul, h0, mul_zero]
      rw [hGcard] at this
      norm_num [Nat.factorial] at this
    have hEq : (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))).index *
        (2 * Nat.card (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8)))) =
        (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))).index *
        (8 - F.card).factorial := by
      rw [mul_comm _ (2 * Nat.card (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))))]
      exact hA.trans hindex.symm
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hidxne) hEq
  have hmap : seg27AltFix (F : Set (Fin 8)) =
      (fixingSubgroup (alternatingGroup (Fin 8)) (F : Set (Fin 8))).map
        (alternatingGroup (Fin 8)).subtype := by
    ext g
    rw [seg27_mem_altFix, Subgroup.mem_map]
    constructor
    · rintro ⟨hgG, hgfix⟩
      refine ⟨⟨g, hgG⟩, ?_, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro y hy
      simpa [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using hgfix y hy
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, ?_⟩
      intro y hy
      have := (mem_fixingSubgroup_iff (M := ↥(alternatingGroup (Fin 8)))).mp hh y hy
      simpa [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using this
  rw [hmap, Subgroup.card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective]
  exact Nat.eq_div_of_mul_eq_right (by norm_num : (2 : ℕ) ≠ 0) htwice

theorem seg27_card_altFix_two {p q : Fin 8} (hpq : p ≠ q) :
    Nat.card (seg27AltFix {p, q}) = 360 := by
  let F : Finset (Fin 8) := {p, q}
  have hFcard : F.card = 2 := by
    simp only [F]
    exact Finset.card_pair hpq
  have h := seg27_card_altFix F (by omega)
  have hFset : (F : Set (Fin 8)) = {p, q} := by
    simp only [F, Finset.coe_insert, Finset.coe_singleton]
  rw [hFset, hFcard] at h
  norm_num [Nat.factorial] at h
  exact h

theorem seg27_card_altFix_three {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (seg27AltFix {i, j, k}) = 60 := by
  let F : Finset (Fin 8) := {i, j, k}
  have hFcard : F.card = 3 := by
    simp only [F]
    exact Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩
  have h := seg27_card_altFix F (by omega)
  have hFset : (F : Set (Fin 8)) = {i, j, k} := by
    simp only [F, Finset.coe_insert, Finset.coe_singleton]
  rw [hFset, hFcard] at h
  norm_num [Nat.factorial] at h
  exact h

theorem seg27_card_altFix_four {a b c d : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Nat.card (seg27AltFix {a, b, c, d}) = 12 := by
  let F : Finset (Fin 8) := {a, b, c, d}
  have hFcard : F.card = 4 := by
    simp only [F]
    exact Finset.card_eq_four.mpr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  have h := seg27_card_altFix F (by omega)
  have hFset : (F : Set (Fin 8)) = {a, b, c, d} := by
    simp only [F, Finset.coe_insert, Finset.coe_singleton]
  rw [hFset, hFcard] at h
  norm_num [Nat.factorial] at h
  exact h

theorem seg27_isCycle_of_orderOf_five {g : Equiv.Perm (Fin 8)} (hg : orderOf g = 5) :
    g.IsCycle ∧ g.support.card = 5 := by
  have hct : g.cycleType = {5} :=
    seg27_cycleType_eq_singleton_of_prime_order g (by decide) (by decide) hg
  have hcyc : g.IsCycle := by
    rw [← Equiv.Perm.card_cycleType_eq_one, hct]
    simp
  refine ⟨hcyc, ?_⟩
  have hsum : g.cycleType.sum = g.support.card := Equiv.Perm.sum_cycleType g
  rw [hct] at hsum
  simpa using hsum.symm

theorem seg27_card_fixed_of_orderOf_five {g : Equiv.Perm (Fin 8)} (hg : orderOf g = 5) :
    (Finset.univ.filter fun x => g x = x).card = 3 := by
  have hsupp := (seg27_isCycle_of_orderOf_five hg).2
  have hcompl : (Finset.univ.filter fun x => g x = x) = g.supportᶜ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Equiv.Perm.notMem_support]
  rw [hcompl, Finset.compl_eq_univ_sdiff,
    Finset.card_sdiff_of_subset (Finset.subset_univ g.support), Finset.card_univ,
    Fintype.card_fin, hsupp]

theorem seg27_not_fix_four_of_orderOf_five {g : Equiv.Perm (Fin 8)} (hg : orderOf g = 5)
    {a b c d : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (ha : g a = a) (hb : g b = b) (hc : g c = c) (hd : g d = d) : False := by
  classical
  have hcard := seg27_card_fixed_of_orderOf_five hg
  have hsub : ({a, b, c, d} : Finset (Fin 8)) ⊆ Finset.univ.filter (fun x => g x = x) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hFcard : ({a, b, c, d} : Finset (Fin 8)).card = 4 :=
    Finset.card_eq_four.mpr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  have hle := Finset.card_le_card hsub
  rw [hFcard, hcard] at hle
  omega

theorem seg27_exists_third_fixed_of_orderOf_five {g : Equiv.Perm (Fin 8)} (hg : orderOf g = 5)
    {p q : Fin 8} (hpq : p ≠ q) (hp : g p = p) (hq : g q = q) :
    ∃ o, o ≠ p ∧ o ≠ q ∧ g o = o ∧ ∀ x, g x = x → x = p ∨ x = q ∨ x = o := by
  classical
  let F : Finset (Fin 8) := Finset.univ.filter fun x => g x = x
  have hFcard : F.card = 3 := seg27_card_fixed_of_orderOf_five hg
  have hpF : p ∈ F := by simp [F, hp]
  have hqF : q ∈ F := by simp [F, hq]
  have herase_card : ((F.erase p).erase q).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm, hqF⟩),
      Finset.card_erase_of_mem hpF, hFcard]
  obtain ⟨o, ho⟩ := Finset.card_eq_one.mp herase_card
  have ho_mem : o ∈ (F.erase p).erase q := by rw [ho]; exact Finset.mem_singleton_self o
  have hoq : o ≠ q := (Finset.mem_erase.mp ho_mem).1
  have hop : o ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp ho_mem).2).1
  have hoF : o ∈ F := (Finset.mem_erase.mp (Finset.mem_erase.mp ho_mem).2).2
  have hgo : g o = o := by simpa [F] using hoF
  refine ⟨o, hop, hoq, hgo, ?_⟩
  intro x hx
  by_cases hxp : x = p
  · exact Or.inl hxp
  by_cases hxq : x = q
  · exact Or.inr (Or.inl hxq)
  · have hxF : x ∈ F := by simp [F, hx]
    have hxmem : x ∈ (F.erase p).erase q := by
      simp only [Finset.mem_erase]
      exact ⟨hxq, hxp, hxF⟩
    rw [ho] at hxmem
    exact Or.inr (Or.inr (Finset.mem_singleton.mp hxmem))

theorem seg27_fixed_eq_of_orderOf_five {g : Equiv.Perm (Fin 8)} (hg : orderOf g = 5)
    {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : g i = i) (hj : g j = j)
    (hk : g k = k) : ∀ x, g x = x → x = i ∨ x = j ∨ x = k := by
  classical
  let F : Finset (Fin 8) := Finset.univ.filter fun x => g x = x
  have hFcard : F.card = 3 := seg27_card_fixed_of_orderOf_five hg
  have hijk_card : ({i, j, k} : Finset (Fin 8)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩
  have hsub : ({i, j, k} : Finset (Fin 8)) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simpa [F] using hi
    · simpa [F] using hj
    · simpa [F] using hk
  have heq : ({i, j, k} : Finset (Fin 8)) = F :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hFcard, hijk_card])
  intro x hx
  have hxF : x ∈ F := by simpa [F] using hx
  rw [← heq] at hxF
  simpa using hxF

theorem seg27_exists_pow_eq_of_orderOf_five {g : Equiv.Perm (Fin 8)} (hg : orderOf g = 5)
    {x y : Fin 8} (hx : g x ≠ x) (hy : g y ≠ y) : ∃ n : ℕ, (g ^ n) x = y :=
  (seg27_isCycle_of_orderOf_five hg).1.exists_pow_eq hx hy

theorem seg27_exists_inv_altFix_inf (p₂ q₂ p₃ q₃ : Fin 8) :
    ∃ g ∈ seg27AltFix {p₂, q₂} ⊓ seg27AltFix {p₃, q₃}, orderOf g = 2 := by
  classical
  let F : Finset (Fin 8) := {p₂, q₂, p₃, q₃}
  have hF4 : F.card ≤ 4 := by
    simp only [F]
    exact Finset.card_le_four
  have h2dvd : 2 ∣ Nat.card (seg27AltFix (F : Set (Fin 8))) := by
    rw [seg27_card_altFix F (by omega)]
    have h4dvd : 4 ∣ (8 - F.card).factorial :=
      Nat.dvd_factorial (m := 4) (n := 8 - F.card) (by norm_num) (by omega)
    obtain ⟨k, hk⟩ := h4dvd
    rw [hk]
    have hdiv : 4 * k / 2 = 2 * k := by omega
    rw [hdiv]
    exact dvd_mul_right 2 k
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hcoe1 : ({p₂, q₂} : Set (Fin 8)) ⊆ (F : Set (Fin 8)) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> simp [F]
  have hcoe2 : ({p₃, q₃} : Set (Fin 8)) ⊆ (F : Set (Fin 8)) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> simp [F]
  have hsub1 : seg27AltFix (F : Set (Fin 8)) ≤ seg27AltFix ({p₂, q₂} : Set (Fin 8)) := by
    intro g hg
    rw [seg27_mem_altFix] at hg ⊢
    exact ⟨hg.1, fun z hz => hg.2 z (hcoe1 hz)⟩
  have hsub2 : seg27AltFix (F : Set (Fin 8)) ≤ seg27AltFix ({p₃, q₃} : Set (Fin 8)) := by
    intro g hg
    rw [seg27_mem_altFix] at hg ⊢
    exact ⟨hg.1, fun z hz => hg.2 z (hcoe2 hz)⟩
  exact ⟨(x : Equiv.Perm (Fin 8)),
    Subgroup.mem_inf.mpr ⟨hsub1 x.2, hsub2 x.2⟩,
    (Subgroup.orderOf_coe x).trans hx⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
