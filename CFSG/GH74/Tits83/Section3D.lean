module

public import CFSG.GH74.Tits83.Section3C

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace TitsSystem

variable (T : TitsSystem G 8)

theorem lemma38_surj (hT : T.Normalized) {v x : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1)
    (hx : x ∈ T.U 5) :
    ∃ u' ∈ T.Uprime 2, ∃ d ∈ T.Uprime 4, ∃ c ∈ T.Uprime 6, ⁅v, u'⁆ = d * x * c := by
  by_cases hx1 : x = 1
  · subst hx1
    exact ⟨1, (T.Uprime 2).one_mem, 1, (T.Uprime 4).one_mem, 1, (T.Uprime 6).one_mem, by simp⟩
  have hmov : T.Moves (T.mu 8 v) (fun j => 24 - j) := by
    simpa using T.moves_mu (T.Uprime_le 8 hv) hv1
  have hmov' : T.Moves (T.mu 8 v)⁻¹ (fun j => 24 - j) := Moves.inv_refl T hmov
  set m : G := T.mu 8 v with hm
  set u : G := m⁻¹ * x * m with hu
  have hu_mem : u ∈ T.U 3 := by
    have h := Moves.conj_mem T hmov' (j := 5) hx
    rw [show (24 : ℤ) - 5 = 19 by norm_num,
      show (19 : ℤ) = 3 + 2 * ((8 : ℕ) : ℤ) * 1 by norm_num, U_add_two_mul T 3 1,
      inv_inv] at h
    rwa [← hu] at h
  have hu1 : u ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun y => m * y * m⁻¹) h
    simpa [hu, mul_assoc] using this
  obtain ⟨hu'2, hu'1⟩ := T.lemma38_mem hT hv hv1 hu_mem hu1
  set u' : G := (T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v with hu'
  have hu'_2 : u' ∈ T.Uprime 2 := by simpa [hu'] using hu'2
  have hu'_1 : u' ≠ 1 := by simpa [hu'] using hu'1
  have hii := T.lemma38_ii hT hv hv1 hu_mem hu1 hu'
  have hd_mem : T.mu 2 u' * v⁻¹ * (T.mu 2 u')⁻¹ ∈ T.Uprime 4 := by
    have h := T.mu_conj_mem_Uprime (i := 2) (j := 8) (T.Uprime_le 2 hu'_2) hu'_1
      ((T.Uprime 8).inv_mem hv)
    simpa using h
  have hc_mem : T.mu 8 v * u' * (T.mu 8 v)⁻¹ ∈ T.Uprime 6 := by
    have h := T.mu_conj_mem_Uprime (i := 8) (j := 2) (T.Uprime_le 8 hv) hv1 hu'_2
    have e : T.Uprime (2 * 8 + 8 - 2) = T.Uprime 6 := by
      rw [show (2 * 8 + 8 - 2 : ℤ) = 6 + 16 * 1 by norm_num, T.Uprime_add_two_mul]
    rwa [e] at h
  refine ⟨u', hu'_2, T.mu 2 u' * v⁻¹ * (T.mu 2 u')⁻¹, hd_mem,
    T.mu 8 v * u' * (T.mu 8 v)⁻¹, hc_mem, ?_⟩
  have hxu : T.mu 8 v * u * (T.mu 8 v)⁻¹ = x := by
    rw [hu, ← hm]
    group
  rw [hii, hxu]

theorem lemma39_surj (hT : T.Normalized) {v x : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1)
    (hx : x ∈ T.Uprime 6) : ∃ u ∈ T.U 3, ⁅u, v⁆ = x := by
  by_cases hx1 : x = 1
  · exact ⟨1, (T.U 3).one_mem, by simp [hx1]⟩
  have hmov : T.Moves (T.mu 8 v) (fun j => 24 - j) := by
    simpa using T.moves_mu (T.Uprime_le 8 hv) hv1
  have hmov' : T.Moves (T.mu 8 v)⁻¹ (fun j => 24 - j) := Moves.inv_refl T hmov
  have hmov'' : T.Moves (T.mu 8 v)⁻¹ (fun j => -1 * j + 24) := by
    simpa [sub_eq_add_neg, neg_one_mul, add_comm] using hmov'
  set m : G := T.mu 8 v with hm
  set x' : G := m⁻¹ * x * m with hx'def
  have hx'2 : x' ∈ T.Uprime 2 := by
    have h := Moves.conj_mem_Uprime T (Or.inr rfl) hmov'' (j := 6) hx
    have e : T.Uprime (-1 * 6 + 24) = T.Uprime 2 := by
      rw [show (-1 * 6 + 24 : ℤ) = 2 + 16 * 1 by norm_num, T.Uprime_add_two_mul]
    rw [e] at h
    simpa [hx'def, hm] using h
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    have h2 := congrArg (fun y => m * y * m⁻¹) h
    simpa [hx'def, mul_assoc] using h2
  obtain ⟨e, he, hone⟩ := T.lemma38_one hv hv1 hx'2 hx'1
  have hxe : T.mu 8 v * x' * (T.mu 8 v)⁻¹ = x := by
    rw [hx'def, ← hm]
    group
  have hA4 : T.mu 2 x' * v⁻¹ * (T.mu 2 x')⁻¹ ∈ T.Uprime 4 := by
    have h := T.mu_conj_mem_Uprime (i := 2) (j := 8) (T.Uprime_le 2 hx'2) hx'1
      ((T.Uprime 8).inv_mem hv)
    simpa using h
  have h1 : ⁅v, x'⁆ = T.mu 2 x' * v⁻¹ * (T.mu 2 x')⁻¹ * e * x := by
    rw [hone, hxe]
  set u : G := m⁻¹ * e * m with hu
  have hu_mem : u ∈ T.U 3 := by
    have h := Moves.conj_mem T hmov' (j := 5) he
    rw [show (24 : ℤ) - 5 = 19 by norm_num,
      show (19 : ℤ) = 3 + 2 * ((8 : ℕ) : ℤ) * 1 by norm_num, U_add_two_mul T 3 1,
      inv_inv] at h
    rwa [← hu] at h
  by_cases hu1 : u = 1
  · have he1 : e = 1 := by
      have h2 := congrArg (fun y => m * y * m⁻¹) hu1
      simpa [hu, mul_assoc] using h2
    have hmem : ⁅v, x'⁆ ∈ (T.Uprime 4 : Set G) * (T.Uprime 6 : Set G) := by
      refine Set.mem_mul.2 ⟨_, hA4, x, hx, ?_⟩
      rw [h1, he1]
      group
    exact absurd (T.lemma38_i hv hv1 hx'2 hmem) hx'1
  · obtain ⟨hu''2, hu''1⟩ := T.lemma38_mem hT hv hv1 hu_mem hu1
    set u'' : G := (T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v with hu''
    have hu''2' : u'' ∈ T.Uprime 2 := by simpa [hu''] using hu''2
    have hu''1' : u'' ≠ 1 := by simpa [hu''] using hu''1
    have hii := T.lemma38_ii hT hv hv1 hu_mem hu1 hu''
    have hue : T.mu 8 v * u * (T.mu 8 v)⁻¹ = e := by
      rw [hu, ← hm]
      group
    have hA''4 : T.mu 2 u'' * v⁻¹ * (T.mu 2 u'')⁻¹ ∈ T.Uprime 4 := by
      have h := T.mu_conj_mem_Uprime (i := 2) (j := 8) (T.Uprime_le 2 hu''2') hu''1'
        ((T.Uprime 8).inv_mem hv)
      simpa using h
    have hc''6 : T.mu 8 v * u'' * (T.mu 8 v)⁻¹ ∈ T.Uprime 6 := by
      have h := T.mu_conj_mem_Uprime (i := 8) (j := 2) (T.Uprime_le 8 hv) hv1 hu''2'
      have e : T.Uprime (2 * 8 + 8 - 2) = T.Uprime 6 := by
        rw [show (2 * 8 + 8 - 2 : ℤ) = 6 + 16 * 1 by norm_num, T.Uprime_add_two_mul]
      rwa [e] at h
    have h2 : ⁅v, u''⁆ = T.mu 2 u'' * v⁻¹ * (T.mu 2 u'')⁻¹ * e *
        (T.mu 8 v * u'' * (T.mu 8 v)⁻¹) := by
      rw [hii, hue]
    have hx'u'' : x' = u'' :=
      T.lemma38_i_inj hv hv1 hx'2 hu''2' hA4 hA''4 he hx hc''6 h1 h2
    refine ⟨u, hu_mem, ?_⟩
    have hxu : x = ⁅u, v⁆ := by
      rw [← hxe, hx'u'', hu'']
      group
    exact hxu.symm

private theorem Uprime_mul_self_six (hT : T.Normalized) {x : G} (hx : x ∈ T.Uprime 6) :
    x * x = 1 := by
  by_cases hx1 : x = 1
  · rw [hx1]
    simp
  obtain ⟨v, hv, hv1⟩ := T.exists_Uprime hT (j := 8) (by decide)
  obtain ⟨u, hu, hux⟩ := T.lemma39_surj hT hv hv1 hx
  have hu_uu : u * u = 1 := T.lemma35_i hT (j := 3) (by decide) hu
  have hT2 : (T.shift 2).Normalized := hT.shift (by decide : Even (2 : ℤ))
  have hv2 : v ∈ (T.shift 2).Uprime 6 := by rw [Uprime_shift]; simpa using hv
  have hu2 : u ∈ (T.shift 2).U 1 := by rw [shift_U]; simpa using hu
  have hmul := TitsSystem.lemma33_i_mul (T := T.shift 2) hT2 hu2 hu2 hv2
  rw [← hux, ← hmul, hu_uu]
  simp

theorem Uprime_mul_self (hT : T.Normalized) {j : ℤ} (hj : Even j) {x : G}
    (hx : x ∈ T.Uprime j) : x * x = 1 := by
  obtain ⟨k, rfl⟩ := hj
  have hs : Even (k + k - 6) := ⟨k - 3, by ring⟩
  have hx' : x ∈ (T.shift (k + k - 6)).Uprime 6 := by
    rw [Uprime_shift, show (6 : ℤ) + (k + k - 6) = k + k by ring]
    exact hx
  exact Uprime_mul_self_six (T := T.shift (k + k - 6)) (hT.shift hs) hx'

theorem mu_mul_self_Uprime (hT : T.Normalized) {j : ℤ} (hj : Even j) {x : G}
    (hx : x ∈ T.Uprime j) (hx1 : x ≠ 1) : T.mu j x * T.mu j x = 1 := by
  have hxx : x * x = 1 := T.Uprime_mul_self hT hj hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hmem : x ∈ T.U j := T.Uprime_le j hx
  have h := T.mu_inv (by norm_num : 3 ≤ (8 : ℕ)) hmem hx1
  rw [hxinv] at h
  simpa [← h] using inv_mul_cancel (T.mu j x)

theorem mem_Yc_sup_of_U_five (hT : T.Normalized) {x : G} (hx : x ∈ T.U 5) :
    x ∈ T.Yc ⊔ T.Uprime 4 := by
  obtain ⟨v, hv, hv1⟩ := T.exists_Uprime hT (j := 8) (by decide)
  obtain ⟨u', hu'2, d, hd4, c, hc6, hdec⟩ := T.lemma38_surj hT hv hv1 hx
  have hnorm : v ∈ Subgroup.normalizer ((T.Yc ⊔ T.Uprime 4 : Subgroup G) : Set G) :=
    T.le_normalizer_Yc_sup.2 (T.Uprime_le 8 hv)
  have hu'W : u' ∈ T.Yc ⊔ T.Uprime 4 := Subgroup.mem_sup_left (T.Uprime_two_le_Yc hu'2)
  have hdW : d ∈ T.Yc ⊔ T.Uprime 4 := Subgroup.mem_sup_right hd4
  have hcW : c ∈ T.Yc ⊔ T.Uprime 4 := Subgroup.mem_sup_left (T.Uprime_six_le_Yc hc6)
  have hcom : ⁅v, u'⁆ ∈ T.Yc ⊔ T.Uprime 4 := by
    have hvu : v * u' * v⁻¹ ∈ T.Yc ⊔ T.Uprime 4 :=
      (Subgroup.mem_normalizer_iff.mp hnorm u').mp hu'W
    have h := (T.Yc ⊔ T.Uprime 4).mul_mem hvu ((T.Yc ⊔ T.Uprime 4).inv_mem hu'W)
    simpa [commutatorElement_def] using h
  have hxeq : x = d⁻¹ * (d * x * c) * c⁻¹ := by group
  rw [hxeq, ← hdec]
  exact (T.Yc ⊔ T.Uprime 4).mul_mem
    ((T.Yc ⊔ T.Uprime 4).mul_mem ((T.Yc ⊔ T.Uprime 4).inv_mem hdW) hcom)
    ((T.Yc ⊔ T.Uprime 4).inv_mem hcW)

theorem lemma310_i (hT : T.Normalized) {g x : G} (hg : g ∈ T.U 0) (hx : x ∈ T.U 5) :
    ∃ a ∈ T.Uprime 2, ∃ b ∈ T.U 3, ∃ c ∈ T.U 4, ⁅g, x⁆ = a * b * c := by
  have hxW : x ∈ T.Yc ⊔ T.Uprime 4 := T.mem_Yc_sup_of_U_five hT hx
  have hnorm : g ∈ Subgroup.normalizer ((T.Yc ⊔ T.Uprime 4 : Subgroup G) : Set G) :=
    T.le_normalizer_Yc_sup.1 hg
  have hgxW : ⁅g, x⁆ ∈ T.Yc ⊔ T.Uprime 4 := by
    have hgx : g * x * g⁻¹ ∈ T.Yc ⊔ T.Uprime 4 :=
      (Subgroup.mem_normalizer_iff.mp hnorm x).mp hxW
    have h := (T.Yc ⊔ T.Uprime 4).mul_mem hgx ((T.Yc ⊔ T.Uprime 4).inv_mem hxW)
    simpa [commutatorElement_def] using h
  obtain ⟨aw, haw, c, hc6, hdec⟩ := Set.mem_mul.1 (T.Yc_sup_subset hgxW)
  obtain ⟨a, ha2, w, hw35, rfl⟩ := Set.mem_mul.1 haw
  have hwin14 : ⁅g, x⁆ ∈ win T.U 1 4 :=
    TitsSystem.commutator_mem_win (T := T) (j := 0) (a := 1) (b := 5) (by norm_num) (by norm_num)
      (by norm_num) hg (T.U_le_win (by norm_num) (by norm_num) hx)
  obtain ⟨w', hw'34, w5, hw55, hwdec⟩ :=
    TitsSystem.exists_mul_of_mem_win (T := T) (a := 3) (c := 4) (b := 5) (by norm_num) (by norm_num)
      (by norm_num) hw35
  have ha14 : a * w' ∈ win T.U 1 4 :=
    (win T.U 1 4).mul_mem (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 ha2))
      ((T.win_mono (by norm_num) le_rfl) hw'34)
  have hw5c : w5 * c ∈ win T.U 5 6 :=
    (win T.U 5 6).mul_mem ((T.win_mono le_rfl (by norm_num)) hw55)
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc6))
  have heq : (a * w') * (w5 * c) = ⁅g, x⁆ * 1 := by
    rw [mul_one, ← hdec, hwdec]
    group
  have hcmp := TitsSystem.eq_of_mul_eq_mul (T := T) (a := 1) (c := 4) (b := 6) (by norm_num)
    (by norm_num) (by norm_num) ha14 hwin14 hw5c (by simp) heq
  obtain ⟨b, hb, c', hc', hbdec⟩ :=
    TitsSystem.exists_mul_of_mem_win (T := T) (a := 3) (c := 3) (b := 4) (by norm_num) (by norm_num)
      (by norm_num) hw'34
  have hb3 : b ∈ T.U 3 := by simpa [T.win_self] using hb
  have hc'4 : c' ∈ T.U 4 := by simpa [T.win_self] using hc'
  refine ⟨a, ha2, b, hb3, c', hc'4, ?_⟩
  rw [← hcmp.1, hbdec]
  group

theorem lemma310_ii (hT : T.Normalized) {x g : G} (hx : x ∈ T.U 5) (hg : g ∈ T.U 8) :
    ⁅x, g⁆ ∈ T.Uprime 6 := by
  have hxW : x ∈ T.Yc ⊔ T.Uprime 4 := T.mem_Yc_sup_of_U_five hT hx
  have hnorm : g ∈ Subgroup.normalizer ((T.Yc ⊔ T.Uprime 4 : Subgroup G) : Set G) :=
    T.le_normalizer_Yc_sup.2 hg
  have hgxW : ⁅x, g⁆ ∈ T.Yc ⊔ T.Uprime 4 := by
    have hmem : g * x⁻¹ * g⁻¹ ∈ T.Yc ⊔ T.Uprime 4 :=
      (Subgroup.mem_normalizer_iff.mp hnorm x⁻¹).mp ((T.Yc ⊔ T.Uprime 4).inv_mem hxW)
    have h : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact (T.Yc ⊔ T.Uprime 4).mul_mem hxW hmem
  obtain ⟨aw, haw, c, hc6, hdec⟩ := Set.mem_mul.1 (T.Yc_sup_subset hgxW)
  obtain ⟨a, ha2, w, hw35, rfl⟩ := Set.mem_mul.1 haw
  have hwin67 : ⁅x, g⁆ ∈ win T.U 6 7 :=
    TitsSystem.commutator_mem_win (T := T) (j := 5) (a := 6) (b := 8) (by norm_num) (by norm_num)
      (by norm_num) hx (T.U_le_win (by norm_num) (by norm_num) hg)
  have haw25 : a * w ∈ win T.U 2 5 :=
    (win T.U 2 5).mul_mem (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 ha2))
      ((T.win_mono (by norm_num) le_rfl) hw35)
  have hc67 : c ∈ win T.U 6 7 :=
    T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc6)
  have heq : (a * w) * c = 1 * ⁅x, g⁆ := by
    rw [one_mul, ← hdec]
  have hcmp := TitsSystem.eq_of_mul_eq_mul (T := T) (a := 2) (c := 5) (b := 7) (by norm_num)
    (by norm_num) (by norm_num) haw25 (by simp) hc67 hwin67 heq
  rw [← hcmp.2]
  exact hc6

theorem lemma311 (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hv : v ∈ T.U 4) (huv : u * v = v * u) : v ∈ T.Uprime 4 := by
  have hmov : T.Moves (T.mu 1 u) (fun j => 10 - j) := by
    simpa using T.moves_mu hu hu1
  obtain ⟨y, hy5, h212⟩ := T.lemma212_iii (by norm_num : 3 ≤ (8 : ℕ)) (i := 1) (j := 4)
    (by norm_num) (by norm_num) hu hu1 hv huv
  have hyU5 : y ∈ T.U 5 := by simpa [T.win_self] using hy5
  have hmv6 : T.mu 1 u * v * (T.mu 1 u)⁻¹ ∈ T.U 6 := by
    have h := Moves.conj_mem T hmov (j := 4) hv
    rwa [show (10 : ℤ) - 4 = 6 by norm_num] at h
  have hnu9 : T.nu 1 u ∈ T.U 9 := by
    simpa using T.nu_mem hu hu1
  have hT4 : (T.shift 4).Normalized := hT.shift (by decide : Even (4 : ℤ))
  have hv4 : v⁻¹ ∈ (T.shift 4).U 0 := by
    rw [shift_U]
    simpa using (T.U 4).inv_mem hv
  have hnu4 : T.nu 1 u ∈ (T.shift 4).U 5 := by
    rw [shift_U]
    simpa using hnu9
  obtain ⟨a, ha6, b, hb7, c, hc8, h310⟩ :=
    TitsSystem.lemma310_i (T := T.shift 4) hT4 hv4 hnu4
  have ha6' : a ∈ T.Uprime 6 := by
    have h := ha6
    rw [Uprime_shift] at h
    simpa using h
  have hb7' : b ∈ T.U 7 := by
    have h := hb7
    rw [shift_U] at h
    simpa using h
  have hc8' : c ∈ T.U 8 := by
    have h := hc8
    rw [shift_U] at h
    simpa using h
  have h212' : ⁅v⁻¹, T.nu 1 u⁆ = y * (T.mu 1 u * v * (T.mu 1 u)⁻¹) := by
    have h : ⁅v⁻¹, T.nu 1 u⁆ = v⁻¹ * T.nu 1 u * v * (T.nu 1 u)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h, h212]
  have hz56 : ⁅v⁻¹, T.nu 1 u⁆ ∈ win T.U 5 6 := by
    rw [h212']
    exact (win T.U 5 6).mul_mem (T.U_le_win (by norm_num) (by norm_num) hyU5)
      (T.U_le_win (by norm_num) (by norm_num) hmv6)
  have hbc78 : b * c ∈ win T.U 7 8 :=
    (win T.U 7 8).mul_mem (T.U_le_win le_rfl (by norm_num) hb7')
      (T.U_le_win (by norm_num) le_rfl hc8')
  have hz68 : ⁅v⁻¹, T.nu 1 u⁆ ∈ win T.U 6 8 := by
    rw [h310]
    have hab67 : a * b ∈ win T.U 6 7 :=
      (win T.U 6 7).mul_mem (T.U_le_win le_rfl (by norm_num) (T.Uprime_le 6 ha6'))
        (T.U_le_win (by norm_num) le_rfl hb7')
    exact (win T.U 6 8).mul_mem ((T.win_mono (by norm_num) (by norm_num)) hab67)
      (T.U_le_win (by norm_num) le_rfl hc8')
  have hz6 : ⁅v⁻¹, T.nu 1 u⁆ ∈ T.U 6 := by
    have hmem : ⁅v⁻¹, T.nu 1 u⁆ ∈ win T.U 5 6 ⊓ win T.U 6 8 := ⟨hz56, hz68⟩
    rw [TitsSystem.win_inf_win (T := T) (a := 5) (b := 6) (c := 6) (d := 8) (by norm_num)] at hmem
    simpa [T.win_self] using hmem
  have hy6 : y ∈ T.U 6 := by
    have hyq : y = ⁅v⁻¹, T.nu 1 u⁆ * (T.mu 1 u * v * (T.mu 1 u)⁻¹)⁻¹ := by
      rw [h212']
      group
    rw [hyq]
    exact (T.U 6).mul_mem hz6 ((T.U 6).inv_mem hmv6)
  have hy1 : y = 1 := by
    have hbot : T.U 6 ⊓ T.U 5 = ⊥ :=
      TitsSystem.U_inf_U (T := T) (by norm_num) (by norm_num)
    have hmem : y ∈ T.U 6 ⊓ T.U 5 := ⟨hy6, hyU5⟩
    rw [hbot] at hmem
    simpa using hmem
  have hzq : ⁅v⁻¹, T.nu 1 u⁆ = T.mu 1 u * v * (T.mu 1 u)⁻¹ := by
    rw [h212', hy1, one_mul]
  have hbc6 : b * c ∈ T.U 6 := by
    have hbc : b * c = a⁻¹ * ⁅v⁻¹, T.nu 1 u⁆ := by
      rw [h310]
      group
    rw [hbc, hzq]
    exact (T.U 6).mul_mem (T.Uprime_le 6 ((T.Uprime 6).inv_mem ha6')) hmv6
  have hbc1 : b * c = 1 := by
    have hbot : T.U 6 ⊓ win T.U 7 8 = ⊥ := by
      have h := TitsSystem.win_inf_win (T := T) (a := 6) (b := 6) (c := 7) (d := 8) (by norm_num)
      rw [show win T.U 6 6 = T.U 6 from T.win_self 6] at h
      rw [h]
      simpa using TitsSystem.win_eq_bot (T := T) (a := 7) (b := 6) (by norm_num)
    have hmem : b * c ∈ T.U 6 ⊓ win T.U 7 8 := ⟨hbc6, hbc78⟩
    rw [hbot] at hmem
    simpa using hmem
  have haz : a = ⁅v⁻¹, T.nu 1 u⁆ := by
    have h : a * (b * c) = ⁅v⁻¹, T.nu 1 u⁆ := by
      have h' : a * b * c = ⁅v⁻¹, T.nu 1 u⁆ := h310.symm
      rwa [mul_assoc] at h'
    rwa [hbc1, mul_one] at h
  have hav : a = T.mu 1 u * v * (T.mu 1 u)⁻¹ := by rw [haz, hzq]
  have hveq : v = (T.mu 1 u)⁻¹ * a * T.mu 1 u := by
    rw [hav]
    group
  have hveq2 : v = T.mu 1 u⁻¹ * a * (T.mu 1 u⁻¹)⁻¹ := by
    rw [T.mu_inv (by norm_num : 3 ≤ (8 : ℕ)) hu hu1, inv_inv]
    exact hveq
  have hgoal : T.mu 1 u⁻¹ * a * (T.mu 1 u⁻¹)⁻¹ ∈ T.Uprime 4 :=
    T.mu_conj_mem_Uprime (i := 1) (j := 6) ((T.U 1).inv_mem hu) (inv_ne_one.mpr hu1) ha6'
  rw [hveq2]
  exact hgoal

theorem lemma312 (hT : T.Normalized) {g y : G} (hg : g ∈ T.U 0) (hy : y ∈ T.Uprime 6) :
    ∃ a ∈ T.Uprime 2, ∃ b ∈ T.U 3, ∃ c ∈ T.Uprime 4, ∃ e ∈ T.U 5, ⁅g, y⁆ = a * b * c * e := by
  have hy' : y ∈ (T.refl 8).Uprime 2 := by
    rw [Uprime_refl]
    simpa using hy
  have hg' : g ∈ (T.refl 8).U 8 := by
    rw [refl_U]
    simpa using hg
  obtain ⟨w, hw, a', ha', h36⟩ := TitsSystem.lemma36_i (T := T.refl 8) hy' hg'
  have hw35 : w ∈ win T.U 3 5 := by
    have h := hw
    rw [win_refl] at h
    simpa using h
  have ha'2 : a' ∈ T.Uprime 2 := by
    have h := ha'
    rw [Uprime_refl] at h
    simpa using h
  have hgy : ⁅g, y⁆ = a'⁻¹ * w⁻¹ := by
    rw [← commutatorElement_inv y g, h36, mul_inv_rev]
  obtain ⟨b, hb, r, hr, hwdec⟩ :=
    TitsSystem.exists_mul_of_mem_win (T := T) (a := 3) (c := 3) (b := 5) (by norm_num)
      (by norm_num) (by norm_num) ((win T.U 3 5).inv_mem hw35)
  obtain ⟨v, hv, e, he, hrdec⟩ :=
    TitsSystem.exists_mul_of_mem_win (T := T) (a := 4) (c := 4) (b := 5) (by norm_num)
      (by norm_num) (by norm_num) hr
  have hb3 : b ∈ T.U 3 := by simpa [T.win_self] using hb
  have hv4 : v ∈ T.U 4 := by simpa [T.win_self] using hv
  have he5 : e ∈ T.U 5 := by simpa [T.win_self] using he
  have hgydec : ⁅g, y⁆ = a'⁻¹ * b * v * e := by
    rw [hgy, hwdec, hrdec]
    group
  have key : ∀ x ∈ T.U 1, x * v * x⁻¹ = v := by
    intro x hx
    have hxg : x * g = g * x := by
      have h := TitsSystem.commutator_mem_win (T := T) (j := 0) (a := 1) (b := 1)
        (by norm_num) (by norm_num) (by norm_num) hg (T.U_le_win le_rfl le_rfl hx)
      rw [TitsSystem.win_eq_bot (T := T) (by norm_num)] at h
      have h1 : ⁅g, x⁆ = 1 := by simpa using h
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    have hcy : ⁅x, y⁆ ∈ T.Uprime 4 := T.lemma33_i hT hx hy
    have hcyy : ⁅x, y⁆ * y = y * ⁅x, y⁆ :=
      T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hcy (T.Uprime_le 6 hy)
    have hgc : ⁅g, ⁅x, y⁆⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (T.Uprime_comm (j := 4) (k := 0) (by norm_num) (by norm_num) hcy hg).symm
    have hconj : x * ⁅g, y⁆ * x⁻¹ = ⁅g, y⁆ := by
      have h1 : x * ⁅g, y⁆ * x⁻¹ = ⁅g, x * y * x⁻¹⁆ := by
        rw [conjugate_commutatorElement, hxg, show g * x * x⁻¹ = g by group]
      rw [h1, hxy, hcyy, commutatorElement_mul_right_eq_mul_conj g y ⁅x, y⁆, hgc]
      group
    have hxa : a'⁻¹ * x = x * a'⁻¹ :=
      T.Uprime_comm (j := 2) (k := 1) (by norm_num) (by norm_num)
        ((T.Uprime 2).inv_mem ha'2) hx
    have hxb : b * x = x * b := (T.lemma34_iv hT hx hb3).symm
    have hxe : e * x = x * e := (T.lemma34_iii hT hx he5).symm
    have hAx : x * a'⁻¹ * x⁻¹ = a'⁻¹ := by rw [← hxa]; group
    have hBx : x * b * x⁻¹ = b := by rw [← hxb]; group
    have hEx : x * e * x⁻¹ = e := by rw [← hxe]; group
    have hX : x * (a'⁻¹ * b * v * e) * x⁻¹ = a'⁻¹ * b * (x * v * x⁻¹) * e := by
      calc x * (a'⁻¹ * b * v * e) * x⁻¹
          = (x * a'⁻¹ * x⁻¹) * (x * b * x⁻¹) * (x * v * x⁻¹) * (x * e * x⁻¹) := by
              group
        _ = a'⁻¹ * b * (x * v * x⁻¹) * e := by rw [hAx, hBx, hEx]
    have h3 : a'⁻¹ * b * (x * v * x⁻¹) * e = a'⁻¹ * b * v * e := by
      rw [← hX, ← hgydec, hconj, hgydec]
    have hcancel := congrArg (fun z => (a'⁻¹ * b)⁻¹ * z * e⁻¹) h3
    simpa [mul_assoc] using hcancel
  obtain ⟨x, hx, hx1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot 1)
  have hxv : x * v = v * x := by
    have h := congrArg (fun z => z * x) (key x hx)
    simpa [mul_assoc] using h
  exact ⟨a'⁻¹, (T.Uprime 2).inv_mem ha'2, b, hb3, v, T.lemma311 hT hx hx1 hv4 hxv, e, he5,
    hgydec⟩

theorem lemma312' (hT : T.Normalized) {g y : G} (hg : g ∈ T.U 0) (hy : y ∈ T.Uprime 6) :
    ∃ a ∈ T.Uprime 2, ∃ b ∈ T.U 3, ∃ c ∈ T.Uprime 4, ∃ e ∈ T.U 5, ⁅y, g⁆ = a * b * c * e := by
  obtain ⟨a, ha2, b, hb3, c, hc4, e, he5, h⟩ := T.lemma312 hT hg hy
  have hab : a * b = b * a :=
    T.Uprime_comm (j := 2) (k := 3) (by norm_num) (by norm_num) ha2 hb3
  have hac : a * c = c * a :=
    T.Uprime_comm (j := 2) (k := 4) (by norm_num) (by norm_num) ha2 (T.Uprime_le 4 hc4)
  have hae : a * e = e * a :=
    T.Uprime_comm (j := 2) (k := 5) (by norm_num) (by norm_num) ha2 he5
  have hbc : b * c = c * b :=
    (T.Uprime_comm (j := 4) (k := 3) (by norm_num) (by norm_num) hc4 hb3).symm
  have hbe : b * e = e * b := T.comm_odd_add_two hT (j := 3) (by decide) hb3 he5
  have hce : c * e = e * c :=
    T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) hc4 he5
  have hAB : Commute a⁻¹ b⁻¹ := by
    show a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹
    simpa [mul_inv_rev] using (congrArg Inv.inv hab).symm
  have hAC : Commute a⁻¹ c⁻¹ := by
    show a⁻¹ * c⁻¹ = c⁻¹ * a⁻¹
    simpa [mul_inv_rev] using (congrArg Inv.inv hac).symm
  have hAE : Commute a⁻¹ e⁻¹ := by
    show a⁻¹ * e⁻¹ = e⁻¹ * a⁻¹
    simpa [mul_inv_rev] using (congrArg Inv.inv hae).symm
  have hBC : Commute b⁻¹ c⁻¹ := by
    show b⁻¹ * c⁻¹ = c⁻¹ * b⁻¹
    simpa [mul_inv_rev] using (congrArg Inv.inv hbc).symm
  have hBE : Commute b⁻¹ e⁻¹ := by
    show b⁻¹ * e⁻¹ = e⁻¹ * b⁻¹
    simpa [mul_inv_rev] using (congrArg Inv.inv hbe).symm
  have hCE : Commute c⁻¹ e⁻¹ := by
    show c⁻¹ * e⁻¹ = e⁻¹ * c⁻¹
    simpa [mul_inv_rev] using (congrArg Inv.inv hce).symm
  have hE : Commute e⁻¹ (c⁻¹ * (b⁻¹ * a⁻¹)) :=
    hCE.symm.mul_right (hBE.symm.mul_right hAE.symm)
  have hstep : e⁻¹ * c⁻¹ * b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ * e⁻¹ := by
    have h1 : e⁻¹ * c⁻¹ * b⁻¹ * a⁻¹ = e⁻¹ * (c⁻¹ * (b⁻¹ * a⁻¹)) := by group
    rw [h1, hE.eq]
    have h2 : c⁻¹ * (b⁻¹ * a⁻¹) = a⁻¹ * b⁻¹ * c⁻¹ := by
      rw [hAB.symm.eq, (hAC.symm.mul_right hBC.symm).eq]
    rw [h2]
  have hinv : ⁅y, g⁆ = (a * b * c * e)⁻¹ := by
    rw [← commutatorElement_inv g y, h]
  have hgoal : ⁅y, g⁆ = a⁻¹ * b⁻¹ * c⁻¹ * e⁻¹ := by
    rw [hinv, show (a * b * c * e)⁻¹ = e⁻¹ * c⁻¹ * b⁻¹ * a⁻¹ by
      simp only [mul_inv_rev]
      group]
    exact hstep
  exact ⟨a⁻¹, (T.Uprime 2).inv_mem ha2, b⁻¹, (T.U 3).inv_mem hb3, c⁻¹,
    (T.Uprime 4).inv_mem hc4, e⁻¹, (T.U 5).inv_mem he5, hgoal⟩

end TitsSystem

end CFSG.GH74.Tits83
