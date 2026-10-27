module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Excl2

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl

open Subgroup

section Dihedral

variable {K : Type*} [Group K]

structure DihRel (c r s : K) (m : ℕ) : Prop where
  c_sq : c ^ 2 = 1
  two_le : 2 ≤ m
  r_ord : orderOf r = 2 ^ m
  s_sq : s ^ 2 = 1
  srs : s * r * s⁻¹ = r⁻¹
  cr : c * r = r * c
  cs : c * s = s * c
  c_nmem : c ∉ closure ({r, s} : Set K)

@[expose] def z0 (r : K) (m : ℕ) : K := r ^ (2 ^ (m - 1))

theorem mul_zpow_of_inv {r s : K} (hsr : s * r * s⁻¹ = r⁻¹) (i : ℤ) :
    s * r ^ i = r ^ (-i) * s := by
  have h := conj_zpow (a := s) (b := r) (i := i)
  rw [hsr, inv_zpow'] at h
  calc s * r ^ i = (s * r ^ i * s⁻¹) * s := by group
    _ = r ^ (-i) * s := by rw [← h]

theorem zpow_mul_sq {r s : K} (hs : s ^ 2 = 1) (hsr : s * r * s⁻¹ = r⁻¹) (i : ℤ) :
    (r ^ i * s) ^ 2 = 1 := by
  have h1 : (r ^ i * s) ^ 2 = r ^ i * (s * r ^ i) * s := by rw [sq]; group
  rw [h1, mul_zpow_of_inv hsr]
  have h2 : r ^ i * (r ^ (-i) * s) * s = s ^ 2 := by rw [sq]; group
  rw [h2, hs]

theorem zpow_mul_conj {r s : K} (hs : s ^ 2 = 1) (hsr : s * r * s⁻¹ = r⁻¹) (i : ℤ) :
    (r ^ i * s) * r * (r ^ i * s)⁻¹ = r⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rwa [← sq])
  have h1 : (r ^ i * s) * r * (r ^ i * s)⁻¹ = r ^ i * (s * r * s⁻¹) * (r ^ i)⁻¹ := by group
  rw [h1, hsr]
  group

theorem exists_zpow_of_mem_closure_dih {r s : K} (hs : s ^ 2 = 1) (hsr : s * r * s⁻¹ = r⁻¹)
    {x : K} (hx : x ∈ closure ({r, s} : Set K)) : ∃ i : ℤ, x = r ^ i ∨ x = r ^ i * s := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rwa [← sq])
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, Or.inl (zpow_one _).symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨0, Or.inr (by simp)⟩
  | one => exact ⟨0, Or.inl (zpow_zero _).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, hi | hi⟩ := hx <;> obtain ⟨j, hj | hj⟩ := hy
    · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
    · exact ⟨i + j, Or.inr (by rw [hi, hj, zpow_add, mul_assoc])⟩
    · refine ⟨i - j, Or.inr ?_⟩
      rw [hi, hj, mul_assoc, mul_zpow_of_inv hsr, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨i - j, Or.inl ?_⟩
      have h1 : r ^ i * s * (r ^ j * s) = r ^ i * (s * r ^ j) * s := by group
      rw [hi, hj, h1, mul_zpow_of_inv hsr]
      have h2 : r ^ i * (r ^ (-j) * s) * s = r ^ (i - j) * s ^ 2 := by rw [sq]; group
      rw [h2, hs, mul_one]
  | inv x _ hx =>
    obtain ⟨i, hi | hi⟩ := hx
    · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [hi, mul_inv_rev, hsinv, ← zpow_neg, mul_zpow_of_inv hsr, neg_neg]

namespace DihRel

variable {c r s : K} {m : ℕ} (h : DihRel c r s m)

include h

theorem c_ne_one : c ≠ 1 := fun hc => h.c_nmem (hc ▸ one_mem _)

theorem orderOf_c : orderOf c = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h.c_sq h.c_ne_one

theorem zpow_eq_one_iff (i : ℤ) : r ^ i = 1 ↔ (2 : ℤ) ^ m ∣ i := by
  rw [← orderOf_dvd_iff_zpow_eq_one, h.r_ord]
  norm_cast

theorem r_sq_ne_one : r ^ 2 ≠ 1 := by
  intro h2
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [h.r_ord] at h3
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.two_le
  have h5 := Nat.le_of_dvd (by norm_num) h3
  omega

theorem r_ne_inv : r ≠ r⁻¹ := by
  intro h1
  apply h.r_sq_ne_one
  calc r ^ 2 = r * r := sq r
    _ = r * r⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel r

theorem orderOf_z0 : orderOf (z0 r m) = 2 := by
  have hm : m - 1 ≤ m := Nat.sub_le m 1
  rw [z0, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [h.r_ord]; exact pow_dvd_pow 2 hm),
    h.r_ord, Nat.pow_div hm two_pos]
  have : m - (m - 1) = 1 := by have := h.two_le; omega
  rw [this, pow_one]

theorem z0_ne_one : z0 r m ≠ 1 := by
  intro h1
  have := h.orderOf_z0
  rw [h1, orderOf_one] at this
  omega

theorem z0_sq : z0 r m ^ 2 = 1 := h.orderOf_z0 ▸ pow_orderOf_eq_one _

theorem z0_eq_zpow : z0 r m = r ^ ((2 : ℤ) ^ (m - 1)) := by
  rw [z0, ← zpow_natCast]
  norm_cast

theorem eq_z0_of_sq_eq_one {j : ℤ} (hne : r ^ j ≠ 1) (hsq : (r ^ j) ^ 2 = 1) :
    r ^ j = z0 r m := by
  have h1 : r ^ (j * 2) = 1 := by
    rw [zpow_mul]
    exact_mod_cast hsq
  rw [h.zpow_eq_one_iff] at h1
  have h2 : (2 : ℤ) ^ (m - 1) ∣ j := by
    have h3 : (2 : ℤ) ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      have := h.two_le
      omega
    rw [h3] at h1
    exact (mul_dvd_mul_iff_right (by norm_num)).mp h1
  obtain ⟨k, hk⟩ := h2
  have h3 : r ^ j = (z0 r m) ^ k := by
    rw [hk, zpow_mul, h.z0_eq_zpow]
  rcases zpow_eq_one_or_self h.orderOf_z0 k with h4 | h4
  · exact absurd (h3.trans h4) hne
  · exact h3.trans h4

theorem s_mul_zpow (i : ℤ) : s * r ^ i = r ^ (-i) * s := mul_zpow_of_inv h.srs i

theorem s_mul_r : s * r = r⁻¹ * s := by
  have := h.s_mul_zpow 1
  simpa using this

theorem commute_cr : Commute c r := h.cr

theorem z0_comm_c : z0 r m * c = c * z0 r m := ((Commute.pow_right h.commute_cr _).eq).symm

theorem s_comm_z0 : s * z0 r m = z0 r m * s := by
  have hinv : (z0 r m)⁻¹ = z0 r m := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h.z0_sq)
  have h1 : r ^ (-((2 : ℤ) ^ (m - 1))) = z0 r m := by
    rw [zpow_neg, ← h.z0_eq_zpow, hinv]
  calc s * z0 r m = s * r ^ ((2 : ℤ) ^ (m - 1)) := by rw [← h.z0_eq_zpow]
    _ = r ^ (-((2 : ℤ) ^ (m - 1))) * s := h.s_mul_zpow _
    _ = z0 r m * s := by rw [h1]

theorem exists_form {x : K} (hx : x ∈ closure ({c, r, s} : Set K)) :
    ∃ i : ℤ, x = r ^ i ∨ x = r ^ i * s ∨ x = c * r ^ i ∨ x = c * (r ^ i * s) := by
  have hcen : closure ({r, s} : Set K) ≤ centralizer ({c} : Set K) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h.cr.symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr h.cs.symm
  have key : ∃ (a : ℤ) (d : K), d ∈ closure ({r, s} : Set K) ∧ x = c ^ a * d := by
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 1, one_mem _, by simp⟩
      · exact ⟨0, y, Subgroup.subset_closure (by simp), by simp⟩
      · exact ⟨0, y, Subgroup.subset_closure (by simp), by simp⟩
    | one => exact ⟨0, 1, one_mem _, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, d, hd, rfl⟩ := hx
      obtain ⟨a', d', hd', rfl⟩ := hy
      refine ⟨a + a', d * d', mul_mem hd hd', ?_⟩
      have hdc : d * c = c * d := Subgroup.mem_centralizer_singleton_iff.mp (hcen hd)
      have hc : d * c ^ a' = c ^ a' * d :=
        (Commute.zpow_right (show Commute d c from hdc) a').eq
      calc c ^ a * d * (c ^ a' * d') = c ^ a * (d * c ^ a') * d' := by simp only [mul_assoc]
        _ = c ^ a * (c ^ a' * d) * d' := by rw [hc]
        _ = c ^ (a + a') * (d * d') := by rw [zpow_add]; simp only [mul_assoc]
    | inv x _ hx =>
      obtain ⟨a, d, hd, rfl⟩ := hx
      refine ⟨-a, d⁻¹, inv_mem hd, ?_⟩
      have hdc : d * c = c * d := Subgroup.mem_centralizer_singleton_iff.mp (hcen hd)
      have hcom : Commute d (c ^ a) := Commute.zpow_right (show Commute d c from hdc) a
      calc (c ^ a * d)⁻¹ = d⁻¹ * (c ^ a)⁻¹ := mul_inv_rev _ _
        _ = (c ^ a)⁻¹ * d⁻¹ := (Commute.inv_inv hcom).eq
        _ = c ^ (-a) * d⁻¹ := by rw [zpow_neg]
  obtain ⟨a, d, hd, rfl⟩ := key
  obtain ⟨i, hi | hi⟩ := exists_zpow_of_mem_closure_dih h.s_sq h.srs hd
  · refine ⟨i, ?_⟩
    rcases zpow_eq_one_or_self h.orderOf_c a with ha | ha
    · exact Or.inl (by rw [ha, hi, one_mul])
    · exact Or.inr (Or.inr (Or.inl (by rw [ha, hi])))
  · refine ⟨i, ?_⟩
    rcases zpow_eq_one_or_self h.orderOf_c a with ha | ha
    · exact Or.inr (Or.inl (by rw [ha, hi, one_mul]))
    · exact Or.inr (Or.inr (Or.inr (by rw [ha, hi])))

theorem sq_form {x : K} (hx : x ∈ closure ({c, r, s} : Set K)) :
    x ^ 2 = 1 ∨ ∃ i : ℤ, x ^ 2 = r ^ (2 * i) := by
  obtain ⟨i, hi | hi | hi | hi⟩ := h.exists_form hx
  · refine Or.inr ⟨i, ?_⟩
    rw [hi]
    group
  · exact Or.inl (by rw [hi]; exact zpow_mul_sq h.s_sq h.srs i)
  · refine Or.inr ⟨i, ?_⟩
    have hc : Commute c (r ^ i) := Commute.zpow_right h.commute_cr i
    rw [hi, hc.mul_pow, h.c_sq, one_mul]
    group
  · left
    have hc : Commute c (r ^ i * s) := (Commute.zpow_right h.commute_cr i).mul_right h.cs
    rw [hi, hc.mul_pow, h.c_sq, one_mul]
    exact zpow_mul_sq h.s_sq h.srs i

theorem not_comm_r_zpow_mul {t : K} (ht : t * r = r⁻¹ * t) (i : ℤ) :
    r * (r ^ i * t) ≠ r ^ i * t * r := by
  intro h1
  apply h.r_ne_inv
  have h2 : r ^ i * t * r = r ^ i * (r⁻¹ * t) := by rw [mul_assoc, ht]
  rw [h2] at h1
  have h3 : r * r ^ i = r ^ i * r⁻¹ := by
    have h4 : r * r ^ i * t = r ^ i * r⁻¹ * t := by
      calc r * r ^ i * t = r * (r ^ i * t) := by rw [mul_assoc]
        _ = r ^ i * (r⁻¹ * t) := h1
        _ = r ^ i * r⁻¹ * t := by rw [mul_assoc]
    exact mul_right_cancel h4
  have h4 : r * r ^ i = r ^ i * r := (Commute.zpow_right (Commute.refl r) i).eq
  rw [h4] at h3
  exact mul_left_cancel h3

theorem zpow_eq_of_comm_s {i : ℤ} (hi : s * r ^ i = r ^ i * s) : r ^ i = 1 ∨ r ^ i = z0 r m := by
  rw [h.s_mul_zpow] at hi
  have h1 : r ^ (-i) = r ^ i := mul_right_cancel hi
  by_cases hne : r ^ i = 1
  · exact Or.inl hne
  · right
    apply h.eq_z0_of_sq_eq_one hne
    calc (r ^ i) ^ 2 = r ^ i * r ^ i := sq _
      _ = r ^ i * r ^ (-i) := by rw [h1]
      _ = 1 := by rw [← zpow_add]; simp

theorem z0_central {q : K} (hq : q ∈ closure ({c, r, s} : Set K)) :
    q * z0 r m = z0 r m * q := by
  have hle : closure ({c, r, s} : Set K) ≤ centralizer ({z0 r m} : Set K) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl
    · exact h.z0_comm_c.symm
    · exact ((Commute.refl y).pow_right _).eq
    · exact h.s_comm_z0
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hq)

theorem c_central {q : K} (hq : q ∈ closure ({c, r, s} : Set K)) : q * c = c * q := by
  have hle : closure ({c, r, s} : Set K) ≤ centralizer ({c} : Set K) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl
    · rfl
    · exact h.cr.symm
    · exact h.cs.symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hq)

theorem central_cases {x : K} (hx : x ∈ closure ({c, r, s} : Set K))
    (hxc : ∀ q ∈ closure ({c, r, s} : Set K), q * x = x * q) :
    x = 1 ∨ x = z0 r m ∨ x = c ∨ x = c * z0 r m := by
  have hrM : r ∈ closure ({c, r, s} : Set K) := Subgroup.subset_closure (by simp)
  have hsM : s ∈ closure ({c, r, s} : Set K) := Subgroup.subset_closure (by simp)
  obtain ⟨i, hi | hi | hi | hi⟩ := h.exists_form hx
  · have h2 := hxc s hsM
    rw [hi] at h2
    rcases h.zpow_eq_of_comm_s h2 with h3 | h3
    · exact Or.inl (by rw [hi, h3])
    · exact Or.inr (Or.inl (by rw [hi, h3]))
  · exfalso
    have h2 := hxc r hrM
    rw [hi] at h2
    exact h.not_comm_r_zpow_mul h.s_mul_r i h2
  · have h2 := hxc s hsM
    rw [hi] at h2
    have h3 : s * r ^ i = r ^ i * s := by
      have h4 : c * (s * r ^ i) = c * (r ^ i * s) := by
        calc c * (s * r ^ i) = s * (c * r ^ i) := by rw [← mul_assoc, h.cs, mul_assoc]
          _ = c * r ^ i * s := h2
          _ = c * (r ^ i * s) := by rw [mul_assoc]
      exact mul_left_cancel h4
    rcases h.zpow_eq_of_comm_s h3 with h4 | h4
    · exact Or.inr (Or.inr (Or.inl (by rw [hi, h4, mul_one])))
    · exact Or.inr (Or.inr (Or.inr (by rw [hi, h4])))
  · exfalso
    have h2 := hxc r hrM
    rw [hi] at h2
    apply h.not_comm_r_zpow_mul h.s_mul_r i
    have h3 : r * (c * (r ^ i * s)) = c * (r * (r ^ i * s)) := by
      rw [← mul_assoc, ← h.cr, mul_assoc]
    have h4 : c * (r ^ i * s) * r = c * (r ^ i * s * r) := by rw [mul_assoc]
    rw [h3, h4] at h2
    exact mul_left_cancel h2

theorem noncentral_involution {e : K} (he : e ∈ closure ({c, r, s} : Set K)) (he2 : e ^ 2 = 1)
    (hnc : ¬ ∀ q ∈ closure ({c, r, s} : Set K), q * e = e * q) :
    e * r * e⁻¹ = r⁻¹ ∧ c * e = e * c ∧ s ∈ closure ({c, r, e} : Set K) := by
  have hrE : r ∈ closure ({c, r, e} : Set K) := Subgroup.subset_closure (by simp)
  have hcE : c ∈ closure ({c, r, e} : Set K) := Subgroup.subset_closure (by simp)
  have heE : e ∈ closure ({c, r, e} : Set K) := Subgroup.subset_closure (by simp)
  have hcentral : ∀ x : K, (x = 1 ∨ x = z0 r m ∨ x = c ∨ x = c * z0 r m) →
      ∀ q ∈ closure ({c, r, s} : Set K), q * x = x * q := by
    intro x hx q hq
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact h.z0_central hq
    · exact h.c_central hq
    · rw [← mul_assoc, h.c_central hq, mul_assoc, h.z0_central hq, mul_assoc]
  obtain ⟨i, hi | hi | hi | hi⟩ := h.exists_form he
  · exfalso
    apply hnc
    apply hcentral
    by_cases h1 : r ^ i = 1
    · exact Or.inl (by rw [hi, h1])
    · refine Or.inr (Or.inl ?_)
      rw [hi]
      apply h.eq_z0_of_sq_eq_one h1
      rw [← hi]
      exact he2
  · refine ⟨?_, ?_, ?_⟩
    · rw [hi]
      exact zpow_mul_conj h.s_sq h.srs i
    · rw [hi]
      exact ((Commute.zpow_right h.commute_cr i).mul_right h.cs).eq
    · have : s = (r ^ i)⁻¹ * e := by rw [hi]; group
      rw [this]
      exact mul_mem (inv_mem (zpow_mem hrE i)) heE
  · exfalso
    apply hnc
    apply hcentral
    have hc : Commute c (r ^ i) := Commute.zpow_right h.commute_cr i
    have h2 : (r ^ i) ^ 2 = 1 := by
      have := he2
      rw [hi, hc.mul_pow, h.c_sq, one_mul] at this
      exact this
    by_cases h1 : r ^ i = 1
    · exact Or.inr (Or.inr (Or.inl (by rw [hi, h1, mul_one])))
    · exact Or.inr (Or.inr (Or.inr (by rw [hi, h.eq_z0_of_sq_eq_one h1 h2])))
  · have hy : Commute c (r ^ i * s) := (Commute.zpow_right h.commute_cr i).mul_right h.cs
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (c * (r ^ i * s)) * r * (c * (r ^ i * s))⁻¹ =
          c * ((r ^ i * s) * r * (r ^ i * s)⁻¹) * c⁻¹ := by group
      rw [hi, h1, zpow_mul_conj h.s_sq h.srs i]
      have h2 : c * r⁻¹ = r⁻¹ * c := (h.commute_cr.inv_right).eq
      rw [h2]
      group
    · rw [hi]
      exact (Commute.refl c).mul_right hy |>.eq
    · have h1 : s = (r ^ i)⁻¹ * (c * e) := by
        rw [hi]
        have : c * (c * (r ^ i * s)) = c ^ 2 * (r ^ i * s) := by rw [sq, mul_assoc]
        rw [this, h.c_sq]
        group
      rw [h1]
      exact mul_mem (inv_mem (zpow_mem hrE i)) (mul_mem hcE heE)

theorem of_noncentral_involution {e : K} (he : e ∈ closure ({c, r, s} : Set K))
    (he2 : e ^ 2 = 1) (hnc : ¬ ∀ q ∈ closure ({c, r, s} : Set K), q * e = e * q) :
    DihRel c r e m ∧ closure ({c, r, e} : Set K) = closure ({c, r, s} : Set K) := by
  obtain ⟨hre, hce, hs⟩ := h.noncentral_involution he he2 hnc
  have hre' : e * r = r⁻¹ * e := by
    have : e * r * e⁻¹ * e = r⁻¹ * e := by rw [hre]
    simpa using this
  refine ⟨⟨h.c_sq, h.two_le, h.r_ord, he2, hre, h.cr, hce, ?_⟩, ?_⟩
  · intro hc
    obtain ⟨j, hj | hj⟩ := exists_zpow_of_mem_closure_dih he2 hre hc
    · apply h.c_nmem
      rw [hj]
      exact zpow_mem (Subgroup.subset_closure (by simp)) j
    · apply h.not_comm_r_zpow_mul hre' j
      rw [← hj]
      exact h.cr.symm
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact he
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact hs

end DihRel

theorem exists_mem_or_mul_mem {c r e : K} (hc2 : c ^ 2 = 1) (hcr : c * r = r * c)
    (hce : c * e = e * c) {U : Subgroup K} (hrU : r ∈ U) (heU : e ∈ U) {x : K}
    (hx : x ∈ closure ({c, r, e} : Set K)) : x ∈ U ∨ c * x ∈ U := by
  have hcen : closure ({c, r, e} : Set K) ≤ centralizer ({c} : Set K) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl
    · rfl
    · exact hcr.symm
    · exact hce.symm
  have hcomm : ∀ y ∈ closure ({c, r, e} : Set K), c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcen hy)).symm
  have hcc : c * c = 1 := by rw [← sq, hc2]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Or.inr (by rw [hcc]; exact one_mem U)
    · exact Or.inl hrU
    · exact Or.inl heU
  | one => exact Or.inl (one_mem U)
  | mul x y hx' hy' ihx ihy =>
    rcases ihx with hx | hx <;> rcases ihy with hy | hy
    · exact Or.inl (mul_mem hx hy)
    · refine Or.inr ?_
      have : c * (x * y) = x * (c * y) := by rw [← mul_assoc, hcomm x hx', mul_assoc]
      rw [this]
      exact mul_mem hx hy
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact mul_mem hx hy
    · refine Or.inl ?_
      have : x * y = (c * x) * (c * y) := by
        calc x * y = (c * c) * (x * y) := by rw [hcc, one_mul]
          _ = c * (c * x) * y := by simp only [mul_assoc]
          _ = c * (x * c) * y := by rw [hcomm x hx']
          _ = (c * x) * (c * y) := by simp only [mul_assoc]
      rw [this]
      exact mul_mem hx hy
  | inv x hx' ihx =>
    rcases ihx with hx | hx
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
      have : c * x⁻¹ = (c * x)⁻¹ := by
        have h1 : x⁻¹ * c = c * x⁻¹ := by
          have := hcomm x hx'
          calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * c) * x⁻¹ := by rw [this]
            _ = c * x⁻¹ := by group
        rw [mul_inv_rev, hcinv, h1]
      rw [this]
      exact inv_mem hx

end Dihedral

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl
