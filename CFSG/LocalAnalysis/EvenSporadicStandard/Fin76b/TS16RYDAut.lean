module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RN

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem pow_four_ne_one_of_orderOf {G : Type} [Group G] {s : G} (hord : orderOf s = 8) :
    s ^ 4 ≠ 1 := by
  intro h
  have h8 := orderOf_dvd_of_pow_eq_one h
  rw [hord] at h8
  exact absurd h8 (by norm_num)

theorem pow_add_eight_of {G : Type} [Group G] {s : G} (hs8 : s ^ 8 = 1) (k : ℕ) :
    s ^ (k + 8) = s ^ k := by
  rw [pow_add, hs8, mul_one]

theorem mul_self_mul_self_eq_pow_four {G : Type} [Group G] {s : G} :
    s * s * (s * s) = s ^ 4 := by
  have h : s ^ 4 = s ^ 2 * s ^ 2 := pow_add s 2 2
  rw [h, pow_two]

theorem pow_six_mul_pow_six {G : Type} [Group G] {s : G} (hs8 : s ^ 8 = 1) :
    s ^ 6 * s ^ 6 = s ^ 4 :=
  (pow_add s 6 6).symm.trans (pow_add_eight_of hs8 4)

theorem pow_two_mem_Dsub {G : Type} [Group G] {s z : G} (m : ℕ) : s ^ (2 * m) ∈ Dsub s z := by
  have e : s ^ (2 * m) = (s * s) ^ m := by rw [← pow_two, ← pow_mul]
  rw [e]
  exact pow_mem a_mem_Dsub m

theorem pow_two_succ_mul_z_mem_Dsub {G : Type} [Group G] {s z : G} (m : ℕ) :
    s ^ (2 * m + 1) * z ∈ Dsub s z := by
  have e : s ^ (2 * m + 1) * z = s ^ (2 * m) * (s * z) := by rw [pow_succ, mul_assoc]
  rw [e]
  exact mul_mem (pow_two_mem_Dsub m) b_mem_Dsub

theorem eq_s_two_or_six_of_sq_ne_one {G : Type} [Group G] {s z : G} (hz2 : z * z = 1)
    (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) {y : G} (hy : y ∈ Dsub s z) (hy2 : y * y ≠ 1) :
    y = s * s ∨ y = s ^ 6 := by
  rcases Dsub_parity hz2 hzs hs8 y hy with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [pow_eq_pow_mod (2 * k) hs8] at hy2 ⊢
    have hmod : 2 * k % 8 = 0 ∨ 2 * k % 8 = 2 ∨ 2 * k % 8 = 4 ∨ 2 * k % 8 = 6 := by omega
    rcases hmod with h | h | h | h <;> rw [h] at hy2 ⊢
    · exact (hy2 (by simp)).elim
    · exact Or.inl (pow_two s)
    · exact (hy2 ((pow_add s 4 4).symm.trans hs8)).elim
    · exact Or.inr rfl
  · exfalso
    apply hy2
    rw [sz_mul_sz hz2 hzs hs8, show 2 * k + 1 + 7 * (2 * k + 1) = 8 * (2 * k + 1) by ring,
      pow_mul, hs8, one_pow]

theorem inv_form_Dsub {G : Type} [Group G] {s z : G} (hz2 : z * z = 1)
    (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) (hord : orderOf s = 8) {y : G}
    (hy : y ∈ Dsub s z) (hy2 : y * y = 1) :
    y = 1 ∨ y = s ^ 4 ∨ y = s * z ∨ y = s ^ 3 * z ∨ y = s ^ 5 * z ∨ y = s ^ 7 * z := by
  rcases Dsub_parity hz2 hzs hs8 y hy with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [pow_eq_pow_mod (2 * k) hs8] at hy2 ⊢
    have hmod : 2 * k % 8 = 0 ∨ 2 * k % 8 = 2 ∨ 2 * k % 8 = 4 ∨ 2 * k % 8 = 6 := by omega
    rcases hmod with h | h | h | h <;> rw [h] at hy2 ⊢
    · exact Or.inl (pow_zero s)
    · have h4 : s ^ 4 = s ^ 2 * s ^ 2 := pow_add s 2 2
      exact (pow_four_ne_one_of_orderOf hord (h4.trans hy2)).elim
    · exact Or.inr (Or.inl rfl)
    · exact (pow_four_ne_one_of_orderOf hord ((pow_six_mul_pow_six hs8).symm.trans hy2)).elim
  · rw [pow_eq_pow_mod (2 * k + 1) hs8]
    have hmod : (2 * k + 1) % 8 = 1 ∨ (2 * k + 1) % 8 = 3 ∨ (2 * k + 1) % 8 = 5 ∨
        (2 * k + 1) % 8 = 7 := by omega
    rcases hmod with h | h | h | h <;> rw [h] <;> simp

theorem conj_pow_s_mul_self {G : Type} [Group G] {s : G} (k : ℕ) :
    s ^ k * (s * s) * (s ^ k)⁻¹ = s * s := by
  have hc : s ^ k * (s * s) = s * s * s ^ k :=
    ((Commute.pow_self s k).mul_right (Commute.pow_self s k)).eq
  rw [hc, mul_inv_cancel_right]

theorem conj_pow_s_mul_z {G : Type} [Group G] {s z : G} (hz2 : z * z = 1)
    (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) (k : ℕ) :
    s ^ k * (s * z) * (s ^ k)⁻¹ = s ^ (2 * k + 1) * z := by
  rw [mul_inv_eq_iff_eq_mul]
  calc s ^ k * (s * z) = s ^ (k + 1) * z := by rw [pow_succ, mul_assoc]
    _ = s ^ (9 * k + 1) * z := by
      rw [show 9 * k + 1 = (k + 1) + 8 * k by ring, pow_add s (k + 1) (8 * k), pow_mul, hs8,
        one_pow, mul_one]
    _ = s ^ (2 * k + 1) * (s ^ (7 * k) * z) := by
      rw [← mul_assoc, ← pow_add, show 2 * k + 1 + 7 * k = 9 * k + 1 by ring]
    _ = s ^ (2 * k + 1) * (z * s ^ k) := by rw [z_mul_pow_s hz2 hzs hs8 k]
    _ = s ^ (2 * k + 1) * z * s ^ k := by rw [mul_assoc]

theorem conj_z_pow_s {G : Type} [Group G] {s z : G} (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1)
    (j : ℕ) : z * s ^ j * (s * s) * (z * s ^ j)⁻¹ = s ^ 6 := by
  have h1 : z * s ^ j * (s * s) * (z * s ^ j)⁻¹ = z * (s ^ j * (s * s) * (s ^ j)⁻¹) * z⁻¹ := by
    group
  have hz : z * (s * s) * z⁻¹ = (s * s)⁻¹ := by
    calc z * (s * s) * z⁻¹ = (z * s * z⁻¹) * (z * s * z⁻¹) := by group
      _ = s⁻¹ * s⁻¹ := by rw [hzs]
      _ = (s * s)⁻¹ := by group
  rw [h1, conj_pow_s_mul_self j, hz]
  exact inv_eq_of_mul_eq_one_right (by rw [show s * s * s ^ 6 = s ^ 8 by group, hs8])

theorem conj_z_pow_s_mul_z {G : Type} [Group G] {s z : G} (hz2 : z * z = 1)
    (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) (j : ℕ) :
    z * s ^ j * (s * z) * (z * s ^ j)⁻¹ = s ^ (7 * (2 * j + 1)) * z := by
  have h1 : z * s ^ j * (s * z) * (z * s ^ j)⁻¹ = z * (s ^ j * (s * z) * (s ^ j)⁻¹) * z⁻¹ := by
    group
  rw [h1, conj_pow_s_mul_z hz2 hzs hs8 j]
  calc z * (s ^ (2 * j + 1) * z) * z⁻¹ = z * s ^ (2 * j + 1) := by group
    _ = s ^ (7 * (2 * j + 1)) * z := z_mul_pow_s hz2 hzs hs8 (2 * j + 1)

theorem Dsub_ext_of_gens {G : Type} [Group G] {s z : G} (ψ : MulAut ↥(Dsub s z))
    (a b : ↥(Dsub s z)) (ha : (a : G) = s * s) (hb : (b : G) = s * z) (s' : G)
    (hA' : s' * (s * s) * s'⁻¹ = ((ψ a : ↥(Dsub s z)) : G))
    (hB' : s' * (s * z) * s'⁻¹ = ((ψ b : ↥(Dsub s z)) : G)) :
    ∀ d : ↥(Dsub s z), ((ψ d : ↥(Dsub s z)) : G) = s' * d * s'⁻¹ := by
  have genA : ∀ u : ↥(Dsub s z), (u : G) = s * s →
      ((ψ u : ↥(Dsub s z)) : G) = s' * (s * s) * s'⁻¹ := by
    intro u hu
    rw [show u = a from Subtype.ext (hu.trans ha.symm), hA']
  have genB : ∀ u : ↥(Dsub s z), (u : G) = s * z →
      ((ψ u : ↥(Dsub s z)) : G) = s' * (s * z) * s'⁻¹ := by
    intro u hu
    rw [show u = b from Subtype.ext (hu.trans hb.symm), hB']
  have key : ∀ x (hx : x ∈ Subgroup.closure ({s * s, s * z} : Set G)),
      ((ψ ⟨x, hx⟩ : ↥(Dsub s z)) : G) = s' * x * s'⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · refine genA _ ?_
        rfl
      · refine genB _ ?_
        rfl
    | one =>
      show ((ψ 1 : ↥(Dsub s z)) : G) = s' * 1 * s'⁻¹
      rw [map_one, Subgroup.coe_one]
      group
    | mul x y hx hy ihx ihy =>
      show ((ψ ((⟨x, hx⟩ : ↥(Dsub s z)) * ⟨y, hy⟩) : ↥(Dsub s z)) : G) = s' * (x * y) * s'⁻¹
      rw [map_mul, Subgroup.coe_mul, ihx, ihy]
      group
    | inv x hx ih =>
      show ((ψ (⟨x, hx⟩ : ↥(Dsub s z))⁻¹ : ↥(Dsub s z)) : G) = s' * x⁻¹ * s'⁻¹
      rw [map_inv, Subgroup.coe_inv, ih]
      group
  intro d
  exact key d.1 d.2

theorem normalizes_Dsub {G : Type} [Group G] {S : Subgroup G} {s z t : G} (hS : S16Gen S s z t)
    {n : G} (hn : n ∈ normalizer (S : Set G)) (hnz : n * z * n⁻¹ = z) :
    ∀ d ∈ Dsub s z, n * d * n⁻¹ ∈ Dsub s z := by
  have hns : n * s * n⁻¹ ∈ S := (mem_normalizer_iff.1 hn s).1 hS.hs
  obtain ⟨i, j, hij⟩ := hS.hgen _ hns
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [z_pow_two_mul hS.hz2 r, mul_one] at hij
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
    ·
      exfalso
      have e : n * s ^ 4 * n⁻¹ = 1 := by
        rw [← conj_pow, hij, ← pow_mul, show 2 * m * 4 = 8 * m by ring, pow_mul, hS.hs8,
          one_pow]
      have h4 : s ^ 4 = 1 := by
        calc s ^ 4 = n⁻¹ * (n * s ^ 4 * n⁻¹) * n := by group
          _ = 1 := by rw [e]; group
      exact pow_four_ne_one_of_orderOf hS.hord h4
    · intro d hd
      rcases Dsub_parity hS.hz2 hS.hzs hS.hs8 d hd with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [← conj_pow, hij, ← pow_mul, show (2 * m + 1) * (2 * k) = 2 * ((2 * m + 1) * k) by ring]
        exact pow_two_mem_Dsub _
      · have key : n * (s ^ (2 * k + 1) * z) * n⁻¹ = s ^ ((2 * m + 1) * (2 * k + 1)) * z := by
          calc n * (s ^ (2 * k + 1) * z) * n⁻¹
              = (n * s ^ (2 * k + 1) * n⁻¹) * (n * z * n⁻¹) := by group
            _ = (n * s * n⁻¹) ^ (2 * k + 1) * z := by rw [conj_pow, hnz]
            _ = s ^ ((2 * m + 1) * (2 * k + 1)) * z := by rw [hij, ← pow_mul]
        rw [key]
        obtain ⟨q, hq⟩ : ∃ q, (2 * m + 1) * (2 * k + 1) = 2 * q + 1 :=
          ⟨2 * m * k + m + k, by ring⟩
        rw [hq]
        exact pow_two_succ_mul_z_mem_Dsub q
  ·
    exfalso
    rw [z_pow_two_mul_add_one hS.hz2 r] at hij
    have e : n * s ^ 2 * n⁻¹ = 1 := by
      rw [← conj_pow, hij, pow_two, sz_mul_sz hS.hz2 hS.hzs hS.hs8 i i,
        show i + 7 * i = 8 * i by ring, pow_mul, hS.hs8, one_pow]
    have h2 : s ^ 2 = 1 := by
      calc s ^ 2 = n⁻¹ * (n * s ^ 2 * n⁻¹) * n := by group
        _ = 1 := by rw [e]; group
    have h8 := orderOf_dvd_of_pow_eq_one h2
    rw [hS.hord] at h8
    exact absurd h8 (by norm_num)

theorem exists_induced_dauts {G : Type} [Group G] {S : Subgroup G} {s z t : G}
    (hS : S16Gen S s z t) (ψ : MulAut ↥(Dsub s z)) :
    ∃ s' ∈ S, ∀ d : ↥(Dsub s z), ((ψ d : ↥(Dsub s z)) : G) = s' * d * s'⁻¹ := by
  have hz2 := hS.hz2
  have hzs := hS.hzs
  have hs8 := hS.hs8
  obtain ⟨A, hAval⟩ : ∃ A : ↥(Dsub s z), (A : G) = s * s := ⟨⟨s * s, a_mem_Dsub⟩, rfl⟩
  obtain ⟨B, hBval⟩ : ∃ B : ↥(Dsub s z), (B : G) = s * z := ⟨⟨s * z, b_mem_Dsub⟩, rfl⟩
  have hAA : A * A ≠ 1 := by
    intro h
    have h' : s * s * (s * s) = 1 := by
      rw [← hAval, ← Subgroup.coe_mul, h, Subgroup.coe_one]
    exact pow_four_ne_one_of_orderOf hS.hord (mul_self_mul_self_eq_pow_four.symm.trans h')
  have hBB : B * B = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one, hBval]; exact b_sq hz2 hzs)
  have hsqA : ((ψ A : ↥(Dsub s z)) : G) * ((ψ A : ↥(Dsub s z)) : G) ≠ 1 := by
    intro h
    apply hAA
    apply ψ.injective
    rw [map_mul, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact h)
  have hsqB : ((ψ B : ↥(Dsub s z)) : G) * ((ψ B : ↥(Dsub s z)) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hBB, map_one, Subgroup.coe_one]
  have hA := eq_s_two_or_six_of_sq_ne_one hz2 hzs hs8 (ψ A).2 hsqA
  have hB : ((ψ B : ↥(Dsub s z)) : G) = s * z ∨ ((ψ B : ↥(Dsub s z)) : G) = s ^ 3 * z ∨
      ((ψ B : ↥(Dsub s z)) : G) = s ^ 5 * z ∨ ((ψ B : ↥(Dsub s z)) : G) = s ^ 7 * z := by
    rcases inv_form_Dsub hz2 hzs hs8 hS.hord (ψ B).2 hsqB with h | h | h | h | h | h
    ·
      exfalso
      have h1 : ψ B = 1 := Subtype.ext h
      have h2 : B = 1 := ψ.injective (h1.trans (map_one ψ).symm)
      have h3 : s * z = 1 := by rw [← hBval]; exact congrArg Subtype.val h2
      exact hS.hzns (by rw [← mul_eq_one_iff_inv_eq.1 h3]; exact inv_mem (mem_zpowers s))
    ·
      exfalso
      have hAA' : ((ψ (A * A) : ↥(Dsub s z)) : G) = s ^ 4 := by
        rw [map_mul, Subgroup.coe_mul]
        rcases hA with h' | h'
        · rw [h']
          exact mul_self_mul_self_eq_pow_four
        · rw [h']
          exact pow_six_mul_pow_six hs8
      have h4 : ψ (A * A) = ψ B := Subtype.ext (hAA'.trans h.symm)
      have h5 : A * A = B := ψ.injective h4
      have h7 : ((A * A : ↥(Dsub s z)) : G) = ((B : ↥(Dsub s z)) : G) := congrArg Subtype.val h5
      rw [Subgroup.coe_mul, hAval, hBval] at h7
      have h7' : s * z = s ^ 4 := h7.symm.trans mul_self_mul_self_eq_pow_four
      have h8 : z = s ^ 3 := mul_left_cancel (h7'.trans (pow_succ' s 3))
      exact hS.hzns (by rw [h8]; exact pow_mem (mem_zpowers s) 3)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases hA with hA | hA <;> rcases hB with hB | hB | hB | hB
  · refine ⟨s ^ 0, pow_mem hS.hs 0, Dsub_ext_of_gens ψ A B hAval hBval (s ^ 0) ?_ ?_⟩
    · rw [conj_pow_s_mul_self, hA]
    · rw [conj_pow_s_mul_z hz2 hzs hs8 0, hB] <;> norm_num
  · refine ⟨s ^ 1, pow_mem hS.hs 1, Dsub_ext_of_gens ψ A B hAval hBval (s ^ 1) ?_ ?_⟩
    · rw [conj_pow_s_mul_self, hA]
    · rw [conj_pow_s_mul_z hz2 hzs hs8 1, hB] <;> norm_num
  · refine ⟨s ^ 2, pow_mem hS.hs 2, Dsub_ext_of_gens ψ A B hAval hBval (s ^ 2) ?_ ?_⟩
    · rw [conj_pow_s_mul_self, hA]
    · rw [conj_pow_s_mul_z hz2 hzs hs8 2, hB] <;> norm_num
  · refine ⟨s ^ 3, pow_mem hS.hs 3, Dsub_ext_of_gens ψ A B hAval hBval (s ^ 3) ?_ ?_⟩
    · rw [conj_pow_s_mul_self, hA]
    · rw [conj_pow_s_mul_z hz2 hzs hs8 3, hB] <;> norm_num
  · refine ⟨z * s ^ 3, mul_mem hS.hzS (pow_mem hS.hs 3),
      Dsub_ext_of_gens ψ A B hAval hBval (z * s ^ 3) ?_ ?_⟩
    · rw [conj_z_pow_s hzs hs8 3, hA]
    · rw [conj_z_pow_s_mul_z hz2 hzs hs8 3, hB, pow_eq_pow_mod _ hs8] <;> norm_num
  · refine ⟨z * s ^ 2, mul_mem hS.hzS (pow_mem hS.hs 2),
      Dsub_ext_of_gens ψ A B hAval hBval (z * s ^ 2) ?_ ?_⟩
    · rw [conj_z_pow_s hzs hs8 2, hA]
    · rw [conj_z_pow_s_mul_z hz2 hzs hs8 2, hB, pow_eq_pow_mod _ hs8] <;> norm_num
  · refine ⟨z * s ^ 1, mul_mem hS.hzS (pow_mem hS.hs 1),
      Dsub_ext_of_gens ψ A B hAval hBval (z * s ^ 1) ?_ ?_⟩
    · rw [conj_z_pow_s hzs hs8 1, hA]
    · rw [conj_z_pow_s_mul_z hz2 hzs hs8 1, hB, pow_eq_pow_mod _ hs8] <;> norm_num
  · refine ⟨z * s ^ 0, mul_mem hS.hzS (pow_mem hS.hs 0),
      Dsub_ext_of_gens ψ A B hAval hBval (z * s ^ 0) ?_ ?_⟩
    · rw [conj_z_pow_s hzs hs8 0, hA]
    · rw [conj_z_pow_s_mul_z hz2 hzs hs8 0, hB, pow_eq_pow_mod _ hs8] <;> norm_num

end CFSG.EvenSporadicStandard.Fin76b
