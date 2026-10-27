module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Orbit
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Perm3

public section

open Equiv CFSG.LocalAnalysis.GLTheoremA.KD264Orbit

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenPerm

theorem orbit_bound_A10 {P : Subgroup (Perm (Fin 10))} (hP : CFSG.Open.IsElemAbelian 3 P) :
    Nat.card P ≤ 27 ∧ (27 ≤ Nat.card P → ∃ a ∈ P, (a.support).card = 3) := by
  constructor
  · by_contra h
    push_neg at h
    have := (orbit_pCycles (n := 10) Nat.prime_three (le_refl 3) P hP (by norm_num; omega)).1
    norm_num at this
    omega
  · intro hc
    obtain ⟨-, hex⟩ := orbit_pCycles (n := 10) Nat.prime_three (le_refl 3) P hP (by norm_num; exact hc)
    obtain ⟨a, b, ha, -, A, B, hA, -, -, hAs, -⟩ := hex (by norm_num)
    refine ⟨a, ha, ?_⟩
    have hsupp : a.support = A := by
      ext t
      rw [Equiv.Perm.mem_support]
      have := hAs 1 (by norm_num) t
      simpa using this
    rw [hsupp, hA]

theorem cyc_apply_other {p q r t : Fin 10} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (ht1 : t ≠ p) (ht2 : t ≠ q) (ht3 : t ≠ r) : (swap p q * swap q r) t = t := by
  simp [Perm.mul_apply, swap_apply_of_ne_of_ne ht2 ht3, swap_apply_of_ne_of_ne ht1 ht2]

theorem fix_comm_pow {σ x : Perm (Fin 10)} (h3 : σ ^ 3 = 1) (hc : (σ.support).card = 3)
    (hsg : Perm.sign σ = 1) (hx : Perm.sign x = 1)
    (hcomm : ∀ f : Perm (Fin 10), Perm.sign f = 1 → (∀ t ∈ σ.support, f t = t) → x * f = f * x) :
    ∃ i : ℕ, i < 3 ∧ x = σ ^ i := by
  classical
  have hfix : ∀ p, p ∉ σ.support → x p = p := by
    intro p hp
    by_contra hne
    have hpu : p ≠ x p := fun h => hne h.symm
    have hcompc : 1 < (σ.support ∪ {p, x p})ᶜ.card := by
      have h1 : (σ.support ∪ ({p, x p} : Finset (Fin 10))).card ≤ 5 := by
        have h2 := Finset.card_union_le σ.support ({p, x p} : Finset (Fin 10))
        have h3' : ({p, x p} : Finset (Fin 10)).card ≤ 2 := Finset.card_le_two
        omega
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.1 hcompc
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hq hr
    obtain ⟨hqs, hqp, hqu⟩ := hq
    obtain ⟨hrs, hrp, hru⟩ := hr
    have hpq : p ≠ q := fun h => hqp h.symm
    have hpr : p ≠ r := fun h => hrp h.symm
    set c : Perm (Fin 10) := swap p q * swap q r with hcdef
    have hcfix : ∀ t ∈ σ.support, c t = t := by
      intro t ht
      have ht1 : t ≠ p := fun h => hp (h ▸ ht)
      have ht2 : t ≠ q := fun h => hqs (h ▸ ht)
      have ht3 : t ≠ r := fun h => hrs (h ▸ ht)
      exact cyc_apply_other hpq hqr hpr ht1 ht2 ht3
    have hcsign : Perm.sign c = 1 := by
      rw [hcdef, Perm.sign_mul, Perm.sign_swap hpq, Perm.sign_swap hqr]
      norm_num
    have hxc : x * c = c * x := hcomm c hcsign hcfix
    have hcp : c p = q := by
      rw [hcdef, Perm.mul_apply, swap_apply_of_ne_of_ne hpq hpr, swap_apply_left]
    have hxq : x q = c (x p) := by
      have := congrArg (fun π : Perm (Fin 10) => π p) hxc
      simp only [Perm.mul_apply] at this
      rw [hcp] at this
      exact this
    have hcxp : c (x p) ≠ x p := by
      intro h
      exact hqp (x.injective (hxq.trans h))
    by_cases hout : x p = p ∨ x p = q ∨ x p = r
    · rcases hout with h | h | h
      · exact hne h
      · exact hqu h.symm
      · exact hru h.symm
    · push_neg at hout
      apply hcxp
      exact cyc_apply_other hpq hqr hpr hpu.symm hout.2.1 hout.2.2
  have hstab : ∀ t ∈ σ.support, x t ∈ σ.support := by
    intro t ht
    by_contra h
    have h1 := hfix (x t) h
    have h2 : x t = t := by
      have := congrArg x.symm h1
      simpa using this
    apply h
    rw [h2]
    exact ht
  obtain ⟨p0, hp0⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hc]
    norm_num
  obtain ⟨i, hi3, hip⟩ := KD1426Perm3.three_cycle_orbit h3 hc hp0 (x p0) (hstab p0 hp0)
  set g : Perm (Fin 10) := (σ ^ i)⁻¹ * x with hg
  have hgp : g p0 = p0 := by
    rw [hg, Perm.mul_apply, ← hip, Equiv.Perm.inv_eq_iff_eq]
  have hgfix : ∀ t, t ∉ σ.support → g t = t := by
    intro t ht
    have ht' : σ t = t := by
      simpa [Equiv.Perm.mem_support] using ht
    have h1 : (σ ^ i)⁻¹ t = t := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (Equiv.Perm.pow_apply_eq_self_of_apply_eq_self ht' i).symm
    rw [hg, Perm.mul_apply, hfix t ht, h1]
  have hgstab : ∀ t ∈ σ.support, g t ∈ σ.support := by
    intro t ht
    by_contra h
    have h1 := hgfix (g t) h
    have h2 : g t = t := by
      have := congrArg g.symm h1
      simpa using this
    apply h
    rw [h2]
    exact ht
  have hcard2 : (σ.support.erase p0).card = 2 := by
    rw [Finset.card_erase_of_mem hp0, hc]
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.1 (show 1 < (σ.support.erase p0).card by omega)
  obtain ⟨hqp, hqs⟩ := Finset.mem_erase.1 hq
  obtain ⟨hrp, hrs⟩ := Finset.mem_erase.1 hr
  have hsub : ({q, r} : Finset (Fin 10)) ⊆ σ.support.erase p0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h | h
    · rw [h]
      exact hq
    · rw [h]
      exact hr
  have heq2 : ({q, r} : Finset (Fin 10)) = σ.support.erase p0 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, Finset.card_pair hqr])
  have hS3 : ∀ t ∈ σ.support, t = p0 ∨ t = q ∨ t = r := by
    intro t ht
    by_cases h : t = p0
    · exact Or.inl h
    · have hm : t ∈ σ.support.erase p0 := Finset.mem_erase.2 ⟨h, ht⟩
      rw [← heq2] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      exact Or.inr hm
  have hgq : g q = q ∨ g q = r := by
    rcases hS3 (g q) (hgstab q hqs) with h | h | h
    · exact absurd (g.injective (h.trans hgp.symm)) hqp
    · exact Or.inl h
    · exact Or.inr h
  have hgr : g r = q ∨ g r = r := by
    rcases hS3 (g r) (hgstab r hrs) with h | h | h
    · exact absurd (g.injective (h.trans hgp.symm)) hrp
    · exact Or.inl h
    · exact Or.inr h
  rcases hgq with hgq | hgq
  ·
    have hgr' : g r = r := by
      rcases hgr with h | h
      · exact absurd (g.injective (h.trans hgq.symm)).symm hqr
      · exact h
    have hg1 : g = 1 := by
      ext t
      by_cases ht : t ∈ σ.support
      · rcases hS3 t ht with h | h | h
        · rw [h, hgp]
          rfl
        · rw [h, hgq]
          rfl
        · rw [h, hgr']
          rfl
      · rw [hgfix t ht]
        rfl
    refine ⟨i, hi3, ?_⟩
    have hx' : x = σ ^ i * g := by
      rw [hg, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hx', hg1, mul_one]
  ·
    exfalso
    have hgr' : g r = q := by
      rcases hgr with h | h
      · exact h
      · exact absurd (g.injective (hgq.trans h.symm)) hqr
    have hgswap : g = swap q r := by
      ext t
      by_cases ht : t ∈ σ.support
      · rcases hS3 t ht with h | h | h
        · rw [h, hgp, swap_apply_of_ne_of_ne (Ne.symm hqp) (Ne.symm hrp)]
        · rw [h, hgq, swap_apply_left]
        · rw [h, hgr', swap_apply_right]
      · have htq : t ≠ q := fun e => ht (e ▸ hqs)
        have htr : t ≠ r := fun e => ht (e ▸ hrs)
        rw [hgfix t ht, swap_apply_of_ne_of_ne htq htr]
    have hsgn : Perm.sign g = 1 := by
      rw [hg, map_mul, map_inv, map_pow, hsg, one_pow, inv_one, hx, mul_one]
    rw [hgswap, Perm.sign_swap hqr] at hsgn
    exact absurd hsgn (by decide)

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenPerm

end
