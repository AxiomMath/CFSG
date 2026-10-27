module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Orbits

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
  Certificates.TitsAschbacherE32
open CFSG.Quasithin (tπ twoF4H twoF4N)

theorem eElt_long_short
    {m : ℕ} (hm : m < 32) (h1 : 1 ≤ m) :
    (eTag m ≤ 1 → IsLong (eElt m)) ∧ (eTag m = 2 → IsShort (eElt m)) := by
  obtain ⟨c1, c2⟩ := exists_conj_eElt hm h1
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with h0 | h1'
    · rw [(eTag_facts.1 m hm h1).1 h0, elt_values.2.1, parrottV_twelve_eq]
      exact isLong_titsZ
    · obtain ⟨h, hh, he⟩ := c1 h1'
      rw [← he]
      exact isLong_parrottV_eleven.conj (titsD_le_titsA (titsH_le_titsD hh))
  · obtain ⟨h, hh, he⟩ := c2 ht
    rw [← he]
    exact isShort_parrottV_ten.conj (titsD_le_titsA (titsH_le_titsD hh))

theorem hatE_long
    : {e | e ∈ hatE ∧ IsLong e ∧ e ≠ titsZ} =
        {e | ∃ h ∈ titsH, h * parrottV 11 * h⁻¹ = e} ∧
      {e | e ∈ hatE ∧ IsLong e ∧ e ≠ titsZ}.ncard = 10 := by
  have hset : {e | e ∈ hatE ∧ IsLong e ∧ e ≠ titsZ} =
      {x | ∃ m < 32, (1 ≤ m ∧ eTag m = 1) ∧ eElt m = x} := by
    ext e
    constructor
    · rintro ⟨he, hl, hz⟩
      obtain ⟨m, hm, rfl⟩ := mem_hatE_iff.1 he
      have h1 : 1 ≤ m := by
        by_contra h0
        rw [show m = 0 by omega, elt_values.1] at hl
        exact hl.ne_one rfl
      refine ⟨m, hm, ⟨h1, ?_⟩, rfl⟩
      have h2 := eTag_facts.2.1 m hm
      have hne0 : eTag m ≠ 0 := fun h0 => hz (by
        rw [(eTag_facts.1 m hm h1).1 h0, elt_values.2.1, parrottV_twelve_eq])
      have hne2 : eTag m ≠ 2 := fun h2' =>
        not_isLong_of_isShort ((eElt_long_short hm h1).2 h2') hl
      omega
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      refine ⟨eElt_mem hm, (eElt_long_short hm h1).1 (by omega), fun hz => ?_⟩
      rw [← parrottV_twelve_eq, ← elt_values.2.1] at hz
      have := eElt_injOn hm (by norm_num) hz
      subst this
      exact absurd ht (by decide)
  refine ⟨?_, ?_⟩
  · rw [hset]
    ext e
    constructor
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact (exists_conj_eElt hm h1).1 ht
    · rintro ⟨h, hh, rfl⟩
      have hmem : h * parrottV 11 * h⁻¹ ∈ hatE := by
        have hn := twoF4H_le_normalizer_hatE (CFSG.Quasithin.le_extSub hh)
        rw [← elt_values.2.2.1]
        exact (mem_normalizer_iff.1 hn _).1 (eElt_mem (by norm_num))
      have hlong : IsLong (h * parrottV 11 * h⁻¹) :=
        isLong_parrottV_eleven.conj (titsD_le_titsA (titsH_le_titsD hh))
      have hne : h * parrottV 11 * h⁻¹ ≠ titsZ := fun he => by
        have hz : h * titsZ * h⁻¹ = titsZ :=
          by rw [mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hh), mul_inv_cancel_right]
        have : parrottV 11 = titsZ := by
          calc parrottV 11 = h⁻¹ * (h * parrottV 11 * h⁻¹) * h := by group
            _ = h⁻¹ * (h * titsZ * h⁻¹) * h := by rw [he, hz]
            _ = titsZ := by group
        rw [← parrottV_twelve_eq, ← elt_values.2.2.1, ← elt_values.2.1] at this
        exact absurd (eElt_injOn (by norm_num) (by norm_num) this) (by decide)
      have h' : h * parrottV 11 * h⁻¹ ∈ {e | e ∈ hatE ∧ IsLong e ∧ e ≠ titsZ} :=
        ⟨hmem, hlong, hne⟩
      rw [hset] at h'
      exact h'
  · rw [hset, ncard_image_range (fun a ha b hb h => eElt_injOn ha hb h), eTag_facts.2.2.1]

theorem hatE_short
    : {e | e ∈ hatE ∧ IsShort e} = {e | ∃ h ∈ titsH, h * parrottV 10 * h⁻¹ = e} ∧
      {e | e ∈ hatE ∧ IsShort e}.ncard = 20 := by
  have hset : {e | e ∈ hatE ∧ IsShort e} =
      {x | ∃ m < 32, (1 ≤ m ∧ eTag m = 2) ∧ eElt m = x} := by
    ext e
    constructor
    · rintro ⟨he, hs⟩
      obtain ⟨m, hm, rfl⟩ := mem_hatE_iff.1 he
      have h1 : 1 ≤ m := by
        by_contra h0
        rw [show m = 0 by omega, elt_values.1] at hs
        exact hs.ne_one rfl
      refine ⟨m, hm, ⟨h1, ?_⟩, rfl⟩
      have h2 := eTag_facts.2.1 m hm
      by_contra hne
      exact not_isLong_of_isShort hs ((eElt_long_short hm h1).1 (by omega))
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact ⟨eElt_mem hm, (eElt_long_short hm h1).2 ht⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    ext e
    constructor
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact (exists_conj_eElt hm h1).2 ht
    · rintro ⟨h, hh, rfl⟩
      have hmem : h * parrottV 10 * h⁻¹ ∈ hatE := by
        have hn := twoF4H_le_normalizer_hatE (CFSG.Quasithin.le_extSub hh)
        rw [← elt_values.2.2.2.1]
        exact (mem_normalizer_iff.1 hn _).1 (eElt_mem (by norm_num))
      have h' : h * parrottV 10 * h⁻¹ ∈ {e | e ∈ hatE ∧ IsShort e} :=
        ⟨hmem, isShort_parrottV_ten.conj (titsD_le_titsA (titsH_le_titsD hh))⟩
      rw [hset] at h'
      exact h'
  · rw [hset, ncard_image_range (fun a ha b hb h => eElt_injOn ha hb h), eTag_facts.2.2.2]

theorem hatE_long_or_short
    {e : Equiv.Perm (Fin 1755)} (he : e ∈ hatE) (he1 : e ≠ 1) : IsLong e ∨ IsShort e := by
  obtain ⟨m, hm, rfl⟩ := mem_hatE_iff.1 he
  have h1 : 1 ≤ m := by
    by_contra h0
    exact he1 (by rw [show m = 0 by omega, elt_values.1])
  rcases Nat.lt_or_ge (eTag m) 2 with h | h
  · exact Or.inl ((eElt_long_short hm h1).1 (by omega))
  · exact Or.inr ((eElt_long_short hm h1).2 (le_antisymm (eTag_facts.2.1 m hm) h))

theorem hatE_short_mul
    {e : Equiv.Perm (Fin 1755)} (he : e ∈ hatE) (hs : IsShort e) :
    ∃ e₁ ∈ hatE, ∃ e₂ ∈ hatE, IsLong e₁ ∧ IsLong e₂ ∧ e = e₁ * e₂ := by
  obtain ⟨m, hm, rfl⟩ := mem_hatE_iff.1 he
  have h1 : 1 ≤ m := by
    by_contra h0
    rw [show m = 0 by omega, elt_values.1] at hs
    exact hs.ne_one rfl
  have ht : eTag m = 2 := by
    have := eTag_facts.2.1 m hm
    by_contra hne
    exact not_isLong_of_isShort hs ((eElt_long_short hm h1).1 (by omega))
  have htab : ∀ m < 32, 1 ≤ m → eTag m = 2 → ∃ g ∈ eGenData, g.1 = m := by decide
  have htab' : ∀ g ∈ eGenData, g.2.1 < 32 ∧ g.2.2 < 32 ∧ 1 ≤ g.2.1 ∧ 1 ≤ g.2.2 ∧
      eTag g.2.1 ≤ 1 ∧ eTag g.2.2 ≤ 1 := by decide
  obtain ⟨g, hg, rfl⟩ := htab m hm h1 ht
  obtain ⟨a1, a2, b1, b2, t1, t2⟩ := htab' g hg
  have hc := List.all_eq_true.1 orbCheck_parts.2.2.1 g hg
  refine ⟨eElt g.2.1, eElt_mem a1, eElt g.2.2, eElt_mem a2, (eElt_long_short a1 b1).1 t1,
    (eElt_long_short a2 b2).1 t2, ?_⟩
  exact eq_of_eqA (rep_eArrs hm) (rep_compA (rep_eArrs a1) (rep_eArrs a2)) hc

theorem fElt_long_short
    {m : ℕ} (hm : m < 32) (h1 : 1 ≤ m) :
    (fTag m = 1 → IsLong (fElt m)) ∧ (2 ≤ fTag m → IsShort (fElt m)) := by
  obtain ⟨c1, c2, c3, -⟩ := exists_conj_fElt hm h1
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · obtain ⟨n, hn, he⟩ := c1 ht
    rw [← he, parrottV_twelve_eq]
    exact isLong_titsZ.conj (titsD_le_titsA (titsN_le_titsD hn))
  · rcases Nat.lt_or_ge (fTag m) 3 with h | h
    · obtain ⟨n, hn, he⟩ := c2 (by omega)
      rw [← he]
      exact isShort_parrottV_ten.conj (titsD_le_titsA (titsN_le_titsD hn))
    · obtain ⟨n, hn, he⟩ := c3 (le_antisymm ((fTag_facts.1 m hm h1).2) h)
      rw [← he]
      exact isShort_parrottV_nine.conj (titsD_le_titsA (titsN_le_titsD hn))

theorem parrottF_long
    : {f | f ∈ parrottF ∧ IsLong f} = {f | ∃ n ∈ titsN, n * titsZ * n⁻¹ = f} ∧
      {f | f ∈ parrottF ∧ IsLong f} = {titsZ, parrottV 11, titsZ * parrottV 11} ∧
      {f | f ∈ parrottF ∧ IsLong f}.ncard = 3 := by
  have hset : {f | f ∈ parrottF ∧ IsLong f} =
      {x | ∃ m < 32, (1 ≤ m ∧ fTag m = 1) ∧ fElt m = x} := by
    ext f
    constructor
    · rintro ⟨hf, hl⟩
      obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hf
      have h1 : 1 ≤ m := by
        by_contra h0
        rw [show m = 0 by omega, elt_values.2.2.2.2.2.1] at hl
        exact hl.ne_one rfl
      refine ⟨m, hm, ⟨h1, ?_⟩, rfl⟩
      have h2 := fTag_facts.1 m hm h1
      by_contra hne
      exact not_isLong_of_isShort ((fElt_long_short hm h1).2 (by omega)) hl
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact ⟨fElt_mem hm, (fElt_long_short hm h1).1 ht⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hset]
    ext f
    constructor
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      obtain ⟨n, hn, he⟩ := (exists_conj_fElt hm h1).1 ht
      exact ⟨n, hn, by rw [← he, parrottV_twelve_eq]⟩
    · rintro ⟨n, hn, rfl⟩
      have hmem : n * titsZ * n⁻¹ ∈ parrottF := by
        have hnN := twoF4N_le_normalizer_parrottF (CFSG.Quasithin.le_extSub hn)
        rw [← parrottV_twelve_eq, ← elt_values.2.2.2.2.2.2.1]
        exact (mem_normalizer_iff.1 hnN _).1 (fElt_mem (by norm_num))
      have h' : n * titsZ * n⁻¹ ∈ {f | f ∈ parrottF ∧ IsLong f} :=
        ⟨hmem, isLong_titsZ.conj (titsD_le_titsA (titsN_le_titsD hn))⟩
      rw [hset] at h'
      exact h'
  · rw [hset]
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      rcases (fTag_facts.2.1 m hm h1).1 ht with rfl | rfl | rfl
      · exact Or.inr (Or.inl elt_values.2.2.2.2.2.2.2.1)
      · exact Or.inl (by rw [elt_values.2.2.2.2.2.2.1, parrottV_twelve_eq])
      · refine Or.inr (Or.inr ?_)
        rw [elt_values.2.2.2.2.2.2.2.2.1, ← parrottV_twelve_eq]
        exact parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by decide) (by decide)
    · rintro (rfl | rfl | rfl)
      · exact ⟨16, by norm_num, ⟨by norm_num, by decide⟩, by
          rw [elt_values.2.2.2.2.2.2.1, parrottV_twelve_eq]⟩
      · exact ⟨8, by norm_num, ⟨by norm_num, by decide⟩, elt_values.2.2.2.2.2.2.2.1⟩
      · refine ⟨24, by norm_num, ⟨by norm_num, by decide⟩, ?_⟩
        rw [elt_values.2.2.2.2.2.2.2.2.1, ← parrottV_twelve_eq]
        exact parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by decide) (by decide)
  · rw [hset, ncard_image_range (fun a ha b hb h => fElt_injOn ha hb h)]
    decide

theorem parrottF_short_ten
    : {f | f ∈ parrottF ∧ IsShort f ∧ f ∈ parrottU 10} =
        {f | ∃ n ∈ titsN, n * parrottV 10 * n⁻¹ = f} ∧
      {f | f ∈ parrottF ∧ IsShort f ∧ f ∈ parrottU 10}.ncard = 4 := by
  have hset : {f | f ∈ parrottF ∧ IsShort f ∧ f ∈ parrottU 10} =
      {x | ∃ m < 32, (1 ≤ m ∧ fTag m = 2) ∧ fElt m = x} := by
    ext f
    constructor
    · rintro ⟨hf, hs, hU⟩
      obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hf
      have h1 : 1 ≤ m := by
        by_contra h0
        rw [show m = 0 by omega, elt_values.2.2.2.2.2.1] at hs
        exact hs.ne_one rfl
      refine ⟨m, hm, ⟨h1, ?_⟩, rfl⟩
      have h2 := (exists_conj_fElt hm h1).2.2.2.1 hU
      have hne1 : fTag m ≠ 1 := fun h' =>
        not_isLong_of_isShort hs ((fElt_long_short hm h1).1 h')
      have := (fTag_facts.1 m hm h1).1
      omega
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact ⟨fElt_mem hm, (fElt_long_short hm h1).2 (by omega),
        (exists_conj_fElt hm h1).2.2.2.2 (by omega)⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    ext f
    constructor
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact (exists_conj_fElt hm h1).2.1 ht
    · rintro ⟨n, hn, rfl⟩
      have hnN := twoF4N_le_normalizer_parrottF (CFSG.Quasithin.le_extSub hn)
      have hnU := twoF4N_le_normalizer_parrottU_ten (CFSG.Quasithin.le_extSub hn)
      have hmem : n * parrottV 10 * n⁻¹ ∈ parrottF := by
        rw [← elt_values.2.2.2.2.2.2.2.2.2.1]
        exact (mem_normalizer_iff.1 hnN _).1 (fElt_mem (by norm_num))
      have hU : n * parrottV 10 * n⁻¹ ∈ parrottU 10 :=
        (mem_normalizer_iff.1 hnU _).1 (subset_closure ⟨10, by norm_num, rfl⟩)
      have h' : n * parrottV 10 * n⁻¹ ∈ {f | f ∈ parrottF ∧ IsShort f ∧ f ∈ parrottU 10} :=
        ⟨hmem, isShort_parrottV_ten.conj (titsD_le_titsA (titsN_le_titsD hn)), hU⟩
      rw [hset] at h'
      exact h'
  · rw [hset, ncard_image_range (fun a ha b hb h => fElt_injOn ha hb h), fTag_facts.2.2.1]

theorem parrottF_short_nine
    : {f | f ∈ parrottF ∧ IsShort f ∧ f ∉ parrottU 10} =
        {f | ∃ n ∈ titsN, n * parrottV 9 * n⁻¹ = f} ∧
      {f | f ∈ parrottF ∧ IsShort f ∧ f ∉ parrottU 10}.ncard = 24 := by
  have hset : {f | f ∈ parrottF ∧ IsShort f ∧ f ∉ parrottU 10} =
      {x | ∃ m < 32, (1 ≤ m ∧ fTag m = 3) ∧ fElt m = x} := by
    ext f
    constructor
    · rintro ⟨hf, hs, hU⟩
      obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hf
      have h1 : 1 ≤ m := by
        by_contra h0
        rw [show m = 0 by omega, elt_values.2.2.2.2.2.1] at hs
        exact hs.ne_one rfl
      refine ⟨m, hm, ⟨h1, ?_⟩, rfl⟩
      have h2 : ¬ fTag m ≤ 2 := fun h => hU ((exists_conj_fElt hm h1).2.2.2.2 h)
      have := (fTag_facts.1 m hm h1).2
      omega
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact ⟨fElt_mem hm, (fElt_long_short hm h1).2 (by omega),
        fun hU => by have := (exists_conj_fElt hm h1).2.2.2.1 hU; omega⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    ext f
    constructor
    · rintro ⟨m, hm, ⟨h1, ht⟩, rfl⟩
      exact (exists_conj_fElt hm h1).2.2.1 ht
    · rintro ⟨n, hn, rfl⟩
      have hnN := twoF4N_le_normalizer_parrottF (CFSG.Quasithin.le_extSub hn)
      have hnU := twoF4N_le_normalizer_parrottU_ten (CFSG.Quasithin.le_extSub hn)
      have hmem : n * parrottV 9 * n⁻¹ ∈ parrottF := by
        rw [← elt_values.2.2.2.2.2.2.2.2.2.2]
        exact (mem_normalizer_iff.1 hnN _).1 (fElt_mem (by norm_num))
      have h9 : parrottV 9 ∉ parrottU 10 := fun h => by
        have := (exists_conj_fElt (m := 2) (by norm_num) (by norm_num)).2.2.2.1
          (by rw [elt_values.2.2.2.2.2.2.2.2.2.2]; exact h)
        exact absurd this (by decide)
      have hU : n * parrottV 9 * n⁻¹ ∉ parrottU 10 := fun h =>
        h9 ((mem_normalizer_iff.1 hnU _).2 h)
      have h' : n * parrottV 9 * n⁻¹ ∈ {f | f ∈ parrottF ∧ IsShort f ∧ f ∉ parrottU 10} :=
        ⟨hmem, isShort_parrottV_nine.conj (titsD_le_titsA (titsN_le_titsD hn)), hU⟩
      rw [hset] at h'
      exact h'
  · rw [hset, ncard_image_range (fun a ha b hb h => fElt_injOn ha hb h), fTag_facts.2.2.2]

theorem parrottF_long_or_short
    {f : Equiv.Perm (Fin 1755)} (hf : f ∈ parrottF) (hf1 : f ≠ 1) : IsLong f ∨ IsShort f := by
  obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hf
  have h1 : 1 ≤ m := by
    by_contra h0
    exact hf1 (by rw [show m = 0 by omega, elt_values.2.2.2.2.2.1])
  rcases Nat.lt_or_ge (fTag m) 2 with h | h
  · exact Or.inl ((fElt_long_short hm h1).1 (by have := (fTag_facts.1 m hm h1).1; omega))
  · exact Or.inr ((fElt_long_short hm h1).2 h)

theorem parrottV_eq_comm
    {i : ℕ}
    (hi : i ∈ ({7, 9, 10, 11, 12} : Set ℕ)) :
    ∃ a ∈ titsH, ∃ b ∈ titsH, a * b * a⁻¹ * b⁻¹ = parrottV i := by
  have htab : ∀ i ∈ [7, 9, 10, 11, 12], ∃ g ∈ fCommData, g.1 = i := by decide
  have hi' : i ∈ [7, 9, 10, 11, 12] := by
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨g, hg, rfl⟩ := htab i hi'
  have hc := List.all_eq_true.1 orbCheck_parts.2.2.2.2.2.2.2.2.2 g hg
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨ha, hb⟩, hab⟩ := hc
  obtain ⟨ra, haH⟩ := rep_hElt ha
  obtain ⟨rb, hbH⟩ := rep_hElt hb
  have hg13 : g.1 < 13 := by
    rcases hi with h | h | h | h | h <;> rw [h] <;> norm_num
  have e := eq_of_eqA (rep_compA ra rb) (rep_compA (rep_compA (rep_vA hg13) rb) ra) hab
  refine ⟨_, haH, _, hbH, ?_⟩
  rw [e]
  group

end CFSG.LocalAnalysis.EvenBN.Tits.Model
