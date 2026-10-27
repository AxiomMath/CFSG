module

public import CFSG.GH74.Uniqueness.Section14Lem44

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

variable {c : Ctx12 Z M} {n : ℕ} {Q : Sylow 2 ↥c.L}

theorem M_inf_NL (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) {x : X}
    (hxM : x ∈ M) (hxN : x ∈ normalizer (c.L : Set X)) :
    ∃ y ∈ centralizer (zHull Z M : Set X), ∃ d ∈ c.D, x = y * d := by
  obtain ⟨l, hl, d, hd, rfl⟩ := NL_eq h x hxN
  have hlM : l ∈ M := by
    have := M.mul_mem hxM (M.inv_mem (mem_inf.mp hd).1)
    simpa using this
  have hlB : (⟨l, hl⟩ : ↥c.L) ∈ Bender.borel (Q : Subgroup ↥c.L) := by
    change _ ∈ normalizer _
    rw [← hQ]
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hlM, hl⟩)
  obtain ⟨p, hp, k, hk, hpk⟩ := (h.benderCore S.invariant hQ).exists_mul_of_mem_borel hlB
  have hpk' : l = (p : X) * k := by simpa using congrArg Subtype.val hpk
  have hkK : (k : X) ∈ kGrp M c.t := by
    rw [K_eq_map h hQ]
    exact mem_map_of_mem _ hk
  have hkD : (k : X) ∈ c.D := by
    rw [h.k_eq'] at hkK
    exact (mem_inf.mp hkK).1
  have hpC : (p : X) ∈ centralizer (zHull Z M : Set X) := by
    rw [mem_centralizer_iff]
    intro m hm
    exact (Mo_central S h hQ _ (mem_map_of_mem _ hp) m hm).symm
  refine ⟨p, hpC, k * d, c.D.mul_mem hkD hd, ?_⟩
  rw [hpk', mul_assoc]

theorem lemma145a
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) {r : ℕ}
    (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) :
    ∀ g ∈ M, ∃ y ∈ centralizer (zHull Z M : Set X), ∃ d ∈ c.D, g = y * d := by
  intro g hg
  obtain ⟨s, hs, hsJ, hsq⟩ := Nat.Prime.not_coprime_iff_dvd.mp
    (lemma144b S h12 h131 h hQ hr hdvd hprim)
  have : Fact s.Prime := ⟨hs⟩
  have hq1 : Odd (2 ^ n - 1) := by
    rw [← h.k_card, ← h.k_eq']
    exact odd_card_K h
  have hs2 : s ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hq1) (even_iff_two_dvd.mpr hsq)
  have hsA : ¬ s ∣ 2 ^ (3 * n) * (2 ^ (2 * n) - 2 ^ n + 1) := by
    intro h1
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2))
    · have hQ1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have e : 2 ^ (2 * n) - 2 ^ n + 1 = (2 ^ n - 1) * 2 ^ n + 1 := by
        rw [show 2 * n = n + n by ring, pow_add]
        zify [hQ1, Nat.le_mul_of_pos_left (2 ^ n) (by positivity : 0 < 2 ^ n)]
        ring
      rw [e] at h2
      have h3 : s ∣ (2 ^ n - 1) * 2 ^ n := dvd_mul_of_dvd_left hsq _
      have := (Nat.dvd_add_right h3).mp h2
      exact hs.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨Qs, hQs⟩ := ABGLocalTools.exists_isSylowOf s (centralizer (c.L : Set X))
  have hJC0 : centralizer (c.L : Set X) ≤ centralizer (zHull Z M : Set X) := by
    intro j hj
    rw [mem_centralizer_iff]
    intro m hm
    exact (mem_centralizer_iff.mp hj) m (h.m_le hm)
  have hQsC0 : ABGLocalTools.IsSylowOf s Qs (centralizer (zHull Z M : Set X)) := by
    apply ABGLocalTools.isSylowOf_of_card (hQs.le.trans hJC0)
    rw [hQs.card_eq]
    congr 1
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hJC0) s
    · have h1 := card_C0_dvd S h12 h hQ
      have h2 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by
        refine Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) (by omega)) Nat.card_pos.ne')).mpr
        h1 s
      rw [Nat.factorization_mul (Nat.mul_ne_zero (by positivity) (by omega)) Nat.card_pos.ne',
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hsA, zero_add] at h2
      exact h2
  have hQs1 : Qs ≠ ⊥ := by
    intro hbot
    have := hQs.card_eq
    rw [hbot, card_bot] at this
    have h1 : 0 < (Nat.card (centralizer (c.L : Set X))).factorization s :=
      hs.factorization_pos_of_dvd Nat.card_pos.ne' hsJ
    have := Nat.one_lt_pow h1.ne' hs.one_lt
    omega
  have hC0n : ∀ x ∈ centralizer (zHull Z M : Set X),
      g⁻¹ * x * g ∈ centralizer (zHull Z M : Set X) := by
    intro x hx
    have := (mem_normalizer_iff.mp (M_le_normalizer_C0 h (M.inv_mem hg)) x).mp hx
    simpa using this
  have hQsg : Qs ≤ conjugate (centralizer (zHull Z M : Set X)) g := by
    intro x hx
    rw [mem_conjugate_iff]
    have := (mem_normalizer_iff.mp (M_le_normalizer_C0 h hg) x).mp (hQsC0.le hx)
    exact this
  obtain ⟨e, he, heg⟩ := exists_mul_mem_normalizer_of_isSylowOf hs hQsC0 hQsg
  have hegN : e * g ∈ normalizer (c.L : Set X) :=
    normalizer_le_of_le_J S h hQs.le hQs1 heg
  have hegM : e * g ∈ M := M.mul_mem (C0_le_M S he) hg
  obtain ⟨y, hy, d, hd, hyd⟩ := M_inf_NL S h hQ hegM hegN
  refine ⟨e⁻¹ * y, mul_mem (inv_mem he) hy, d, hd, ?_⟩
  rw [mul_assoc, ← hyd]
  group

theorem lemma145b
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) {r : ℕ}
    (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) :
    ∀ g ∈ M, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ centralizer (zHull Z M : Set X) := by
  intro g hg k hgk
  set C0 := centralizer (zHull Z M : Set X) with hC0
  have hMeq : M = c.D ⊔ C0 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, d, hd, rfl⟩ := lemma145a S h12 h131 h hQ hr hdvd hprim x hx
      exact mul_mem (mem_sup_right hy) (mem_sup_left hd)
    · exact sup_le inf_le_left (C0_le_M S)
  have hDN : c.D ≤ normalizer (C0 : Set X) := (inf_le_left : c.D ≤ M).trans (M_le_normalizer_C0 h)
  have hprod := card_sup_mul_card_inf' hDN
  rw [← hMeq, inf_comm, D_inf_C0 S h hQ] at hprod
  let C0' : Subgroup ↥M := C0.subgroupOf M
  have hC0'n : C0'.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (C0_le_M S)]
    exact M_le_normalizer_C0 h
  have hcardC0' : Nat.card C0' = Nat.card C0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (C0_le_M S)).toEquiv
  obtain ⟨d, hd, -, hdodd⟩ := card_D h
  have hq1 : Odd (2 ^ n - 1) := by
    rw [← h.k_card, ← h.k_eq']
    exact odd_card_K h
  have hindex : C0'.index * Nat.card (centralizer (c.L : Set X)) =
      (2 ^ n - 1) * d * Nat.card (centralizer (c.L : Set X)) := by
    have h1 := C0'.card_mul_index
    rw [hcardC0'] at h1
    have hC0pos : 0 < Nat.card C0 := Nat.card_pos
    have h2 : Nat.card C0 * (C0'.index * Nat.card (centralizer (c.L : Set X))) =
        Nat.card C0 * ((2 ^ n - 1) * d * Nat.card (centralizer (c.L : Set X))) := by
      calc Nat.card C0 * (C0'.index * Nat.card (centralizer (c.L : Set X)))
          = Nat.card M * Nat.card (centralizer (c.L : Set X)) := by rw [← h1]; ring
        _ = Nat.card C0 * Nat.card c.D := hprod
        _ = _ := by rw [hd]; ring
    exact Nat.eq_of_mul_eq_mul_left hC0pos h2
  have hindex' : C0'.index = (2 ^ n - 1) * d :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hindex
  have hodd : Odd C0'.index := by rw [hindex']; exact hq1.mul hdodd
  have := mem_of_odd_index C0' hodd (σ := (⟨g, hg⟩ : ↥M)) (k := k) (Subtype.ext (by simpa using hgk))
  exact mem_subgroupOf.mp this

end Sec14

end CFSG.GH74.Uniqueness
