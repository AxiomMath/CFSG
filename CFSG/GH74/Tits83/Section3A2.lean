module

public import CFSG.GH74.Tits83.Section3A

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace TitsSystem

variable (T : TitsSystem G 8)

@[expose] def Yc : Subgroup G := normClosure2 (T.U 0) (T.U 8) (T.Uprime 2)

theorem Uprime_two_le_Yc : T.Uprime 2 ≤ T.Yc :=
  le_normClosure2 (T.U 0) (T.U 8) (T.Uprime 2)

theorem Uprime_six_le_Yc : T.Uprime 6 ≤ T.Yc := by
  have h := T.Uprime_le_of_le_normalizer (i := 4) (j := 2) (Y := T.Yc)
    (by simpa [Yc] using normClosure2_normalized_left (T.U 0) (T.U 8) (T.Uprime 2))
    (by simpa [Yc] using normClosure2_normalized_right (T.U 0) (T.U 8) (T.Uprime 2))
    T.Uprime_two_le_Yc
  rwa [show (2 : ℤ) * 4 - 2 = 6 by norm_num] at h

theorem le_normalizer_Yc :
    T.U 0 ≤ Subgroup.normalizer (T.Yc : Set G) ∧
      T.U 8 ≤ Subgroup.normalizer (T.Yc : Set G) :=
  ⟨by simpa [Yc] using normClosure2_normalized_left (T.U 0) (T.U 8) (T.Uprime 2),
   by simpa [Yc] using normClosure2_normalized_right (T.U 0) (T.U 8) (T.Uprime 2)⟩

theorem Yc_subset :
    (T.Yc : Set G) ⊆ (T.Uprime 2 : Set G) * (win T.U 3 5 : Set G) * (T.Uprime 6 : Set G) := by
  have hconj : ∀ u ∈ T.U 0, u ≠ 1 →
      (T.Uprime 2).map (MulAut.conj (T.mu 0 u)).toMonoidHom = T.Uprime 6 := by
    intro u hu hu1
    have hg : T.Moves (T.mu 0 u) (fun k => 8 - k) := by
      have h' := T.moves_mu (n := 8) hu hu1
      simpa only [show 2 * (0 : ℤ) + ((8 : ℕ) : ℤ) = 8 by ring] using h'
    rw [Moves.map_Uprime_refl T hg]
    rw [show (8 : ℤ) - 2 = 6 by norm_num]
  have hX : (T.Uprime 2 : Set G) ⊆ (T.Uprime 2 : Set G) * (win T.U 3 5 : Set G) *
      (T.Uprime 6 : Set G) := by
    intro x hx
    have h1 : x * 1 ∈ (T.Uprime 2 : Set G) * (win T.U 3 5 : Set G) :=
      Set.mul_mem_mul hx (Subgroup.one_mem _)
    have h2 : x * 1 * 1 ∈ ((T.Uprime 2 : Set G) * (win T.U 3 5 : Set G)) *
        (T.Uprime 6 : Set G) := Set.mul_mem_mul h1 (Subgroup.one_mem _)
    simpa using h2
  have hX0 : T.U 0 ≤ Subgroup.normalizer (T.Uprime 2 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have hywin : y ∈ win T.U (-2) 6 := T.U_le_win (by omega) (by omega) hy
    have hxy : x * y = y * x :=
      T.Uprime_comm_win (j := 2) (by norm_num) (by norm_num) hx hywin
    have hconj : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [hxy]
        _ = x := by group
    rw [hconj]
    exact hx
  have h := lemma214 (T := T) (n := 8) (by norm_num) (i := 2) (by norm_num) (by norm_num)
    (T.Uprime 2) (T.Uprime 6) (T.Uprime 2)
    (T.Uprime_le 2) (T.Uprime_le 6) hconj hX hX0
  simpa [Yc, show (2 : ℤ) + 1 = 3 by norm_num,
    show ((8 : ℕ) : ℤ) - 2 - 1 = 5 by norm_num] using h

theorem lemma36_i {a b : G} (ha : a ∈ T.Uprime 2) (hb : b ∈ T.U 8) :
    ∃ w ∈ win T.U 3 5, ∃ c ∈ T.Uprime 6, ⁅a, b⁆ = w * c := by
  by_cases hb1 : b = 1
  · exact ⟨1, (win T.U 3 5).one_mem, 1, (T.Uprime 6).one_mem, by simp [hb1]⟩
  · set u : G := T.nu' 8 b with hudef
    have hu0 : u ∈ T.U 0 := by
      have h := T.nu'_mem (n := 8) hb hb1
      have h' : T.U ((8 : ℤ) + ((8 : ℕ) : ℤ)) = T.U 0 := by
        rw [show (8 : ℤ) + ((8 : ℕ) : ℤ) = 0 + 2 * ((8 : ℕ) : ℤ) * 1 by norm_num,
          U_add_two_mul]
      rwa [h'] at h
    have hu1 : u ≠ 1 := T.nu'_ne_one (by norm_num) hb hb1
    have hnu : T.nu 0 u = b := by
      have h := (T.mu_nu' (n := 8) (by norm_num) hb hb1).2
      rw [show (8 : ℤ) + ((8 : ℕ) : ℤ) = 0 + 2 * ((8 : ℕ) : ℤ) * 1 by norm_num,
        T.nu_add_two_mul (by norm_num)] at h
      exact h
    have hcomm : u * a⁻¹ = a⁻¹ * u := by
      have hx : a⁻¹ ∈ T.Uprime 2 := (T.Uprime 2).inv_mem ha
      have hw : u ∈ win T.U (-2) 6 := T.U_le_win (by omega) (by omega) hu0
      exact (T.Uprime_comm_win (j := 2) (by norm_num) (by norm_num) hx hw).symm
    obtain ⟨y, hy, hyeq⟩ := T.lemma212_iii (n := 8) (by norm_num) (i := 0) (j := 2)
      (by norm_num) (by norm_num) hu0 hu1 (T.Uprime_le 2 ((T.Uprime 2).inv_mem ha)) hcomm
    have hy' : y ∈ win T.U 3 5 := by
      convert hy using 2 <;> norm_num
    have hmc : T.mu 0 u * a⁻¹ * (T.mu 0 u)⁻¹ ∈ T.Uprime 6 := by
      have h := T.mu_conj_mem_Uprime (i := 0) (j := 2) hu0 hu1 ((T.Uprime 2).inv_mem ha)
      rwa [show 2 * (0 : ℤ) + 8 - 2 = 6 by norm_num] at h
    refine ⟨y, hy', T.mu 0 u * a⁻¹ * (T.mu 0 u)⁻¹, hmc, ?_⟩
    simpa only [commutatorElement_def, hnu, inv_inv] using hyeq

theorem lemma36_i' {a b : G} (ha : a ∈ T.U 2) (hb : b ∈ T.Uprime 8) :
    ∃ c ∈ T.Uprime 4, ∃ w ∈ win T.U 5 7, ⁅a, b⁆ = c * w := by
  have hbS : b ∈ (T.refl 10).Uprime 2 := by
    rw [Uprime_refl]
    simpa using hb
  have haS : a ∈ (T.refl 10).U 8 := by
    rw [refl_U]
    simpa using ha
  obtain ⟨w, hw, c, hc, hbc⟩ := lemma36_i (T := T.refl 10) hbS haS
  rw [win_refl] at hw
  rw [Uprime_refl] at hc
  refine ⟨c⁻¹, ?_, w⁻¹, ?_, ?_⟩
  · exact (T.Uprime 4).inv_mem (by simpa using hc)
  · exact (win T.U 5 7).inv_mem (by simpa using hw)
  · have h : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h, hbc]
    group

theorem lemma36_ii {a b : G} (ha : a ∈ T.Uprime 2) (hb : b ∈ T.Uprime 8) :
    ∃ d ∈ T.Uprime 4, ∃ e ∈ T.U 5, ∃ c ∈ T.Uprime 6, ⁅a, b⁆ = d * e * c := by
  obtain ⟨w, hw, c, hc, hwc⟩ := T.lemma36_i ha (T.Uprime_le 8 hb)
  obtain ⟨c', hc', w', hw', hc'w'⟩ := T.lemma36_i' (T.Uprime_le 2 ha) hb
  have hmem36 : ⁅a, b⁆ ∈ win T.U 3 6 := by
    rw [hwc]
    exact (win T.U 3 6).mul_mem
      (T.win_mono (a := 3) (b := 5) (c := 3) (d := 6) (by norm_num) (by norm_num) hw)
      (T.U_le_win (by omega) (by omega) (T.Uprime_le 6 hc))
  have hmem47 : ⁅a, b⁆ ∈ win T.U 4 7 := by
    rw [hc'w']
    exact (win T.U 4 7).mul_mem
      (T.U_le_win (by omega) (by omega) (T.Uprime_le 4 hc'))
      (T.win_mono (by norm_num) (by norm_num) hw')
  have hmem46 : ⁅a, b⁆ ∈ win T.U 4 6 := by
    have hmem : ⁅a, b⁆ ∈ win T.U 3 6 ⊓ win T.U 4 7 := ⟨hmem36, hmem47⟩
    rwa [win_inf_win (T := T) (a := 3) (b := 6) (c := 4) (d := 7) (by norm_num)] at hmem
  have hw'46 : w' ∈ win T.U 4 6 := by
    have h := (win T.U 4 6).mul_mem
      (T.U_le_win (by omega) (by omega) (T.Uprime_le 4 ((T.Uprime 4).inv_mem hc'))) hmem46
    rwa [show c'⁻¹ * ⁅a, b⁆ = w' by rw [hc'w']; group] at h
  have hw'56 : w' ∈ win T.U 5 6 := by
    have hmem : w' ∈ win T.U 4 6 ⊓ win T.U 5 7 := ⟨hw'46, hw'⟩
    rwa [win_inf_win (T := T) (a := 4) (b := 6) (c := 5) (d := 7) (by norm_num)] at hmem
  obtain ⟨e, he, c'', hc'', heq⟩ :=
    T.exists_mul_of_mem_win (a := 5) (c := 5) (b := 6) (by norm_num) (by norm_num)
      (by norm_num) hw'56
  have he5 : e ∈ T.U 5 := by simpa [T.win_self] using he
  have hc''6 : c'' ∈ T.U 6 := by simpa [T.win_self] using hc''
  have hkey : c' * e = w ∧ c'' = c := by
    have h1 : c' * e ∈ win T.U 3 5 :=
      (win T.U 3 5).mul_mem (T.U_le_win (by omega) (by omega) (T.Uprime_le 4 hc'))
        (T.U_le_win (by omega) (by omega) he5)
    have h2 : c'' ∈ win T.U 6 6 := by rw [T.win_self]; exact hc''6
    have h3 : c ∈ win T.U 6 6 := by
      rw [T.win_self]
      exact T.Uprime_le 6 hc
    have heq' : (c' * e) * c'' = w * c := by
      rw [← hwc, hc'w', heq]
      group
    exact T.eq_of_mul_eq_mul (a := 3) (c := 5) (b := 6) (by norm_num) (by norm_num)
      (by norm_num) h1 hw h2 h3 heq'
  refine ⟨c', hc', e, he5, c'', ?_, ?_⟩
  · rw [hkey.2]
    exact hc
  · calc ⁅a, b⁆ = c' * w' := hc'w'
      _ = c' * (e * c'') := by rw [heq]
      _ = c' * e * c'' := by group

theorem lemma37a {v u a b : G} (hv : v ∈ T.U 0) (hv1 : v ≠ 1) (hu : u ∈ T.U 6)
    (hu1 : u ≠ 1) (ha : a ∈ T.Uprime 2) (hb : b ∈ T.Uprime 4)
    (h : ⁅v, u⁆ = a * b) :
    u ∈ T.Uprime 6 ∧ a ≠ 1 ∧ ⁅a⁻¹, T.nu 0 v⁆ = (b * u)⁻¹ := by
  set v' : G := T.nu 0 v with hv'def
  have hv'U : v' ∈ T.U 8 := by
    have h := T.nu_mem (n := 8) hv hv1
    simpa using h
  have hv'1 : v' ≠ 1 := T.nu_ne_one (by norm_num) hv hv1
  set v'' : G := (T.nu 8 v')⁻¹ with hv''def
  have hv''U : v'' ∈ T.U 0 := by
    have h := T.nu_mem (n := 8) hv'U hv'1
    have h' : T.U ((8 : ℤ) + ((8 : ℕ) : ℤ)) = T.U 0 := by
      rw [show (8 : ℤ) + ((8 : ℕ) : ℤ) = 0 + 2 * ((8 : ℕ) : ℤ) * 1 by norm_num,
        U_add_two_mul]
    have h2 : T.nu 8 v' ∈ T.U 0 := by rwa [h'] at h
    exact (T.U 0).inv_mem h2
  set m : G := T.mu 0 v with hmdef
  have hm : m = v''⁻¹ * v' * v := by
    have h := T.mu_eq_nu_nu (n := 8) (by norm_num) hv hv1
    rw [show (0 : ℤ) + ((8 : ℕ) : ℤ) = 8 by norm_num, ← hv'def] at h
    simpa only [hv''def, inv_inv] using h
  set z : G := v'' * (m * u * m⁻¹) * v''⁻¹ with hzdef
  have hz_eq : z = v' * v * u * v⁻¹ * v'⁻¹ := by
    rw [hzdef, hm]
    group
  have hmz : m * u * m⁻¹ ∈ T.U 2 := by
    have h := Moves.conj_mem T (T.moves_mu (n := 8) hv hv1) (j := 6) hu
    rwa [show 2 * (0 : ℤ) + ((8 : ℕ) : ℤ) - 6 = 2 by norm_num] at h
  have hv''norm : v'' ∈ Subgroup.normalizer (win T.U 1 2 : Set G) := by
    have h := (T.le_normalizer_win (a := 1) (b := 2) (by norm_num)).1
    rw [show (1 : ℤ) - 1 = 0 by norm_num] at h
    exact h hv''U
  have hzwin : z ∈ win T.U 1 2 := by
    have hmem : m * u * m⁻¹ ∈ win T.U 1 2 := T.U_le_win (by norm_num) (by norm_num) hmz
    exact (Subgroup.mem_normalizer_iff.mp hv''norm (m * u * m⁻¹)).mp hmem
  have hvu : v * u * v⁻¹ = a * b * u := by
    have h' := h
    simp only [commutatorElement_def] at h'
    calc v * u * v⁻¹ = (v * u * v⁻¹ * u⁻¹) * u := by group
      _ = a * b * u := by rw [h']
  obtain ⟨w, hw, c, hc, hwc⟩ := T.lemma36_i (a := a⁻¹) (b := v')
    ((T.Uprime 2).inv_mem ha) hv'U
  have hdef : ⁅a⁻¹, v'⁆ = a⁻¹ * v' * a * v'⁻¹ := by
    simp only [commutatorElement_def, inv_inv]
  have hv'a : v' * a * v'⁻¹ = a * (w * c) := by
    calc v' * a * v'⁻¹ = a * (a⁻¹ * v' * a * v'⁻¹) := by group
      _ = a * (w * c) := by rw [← hdef, hwc]
  have hv'b : v' * b * v'⁻¹ = b := by
    have hwin : v' ∈ win T.U 0 8 := T.U_le_win (by norm_num) (by norm_num) hv'U
    have hcomm : b * v' = v' * b :=
      T.Uprime_comm_win (j := 4) (by norm_num) (by norm_num) hb hwin
    calc v' * b * v'⁻¹ = b * v' * v'⁻¹ := by rw [← hcomm]
      _ = b := by group
  have hv'u : v' * u * v'⁻¹ = ⁅v', u⁆ * u := by
    simp only [commutatorElement_def]
    group
  have hvu7 : ⁅v', u⁆ ∈ T.U 7 := by
    have h := T.comm 6 8 (by norm_num) (by norm_num) u hu v' hv'U
    have h' : u * v' * u⁻¹ * v'⁻¹ ∈ T.U 7 := by
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun k hk => ?_
      obtain ⟨h1, h2⟩ := hk
      have hk7 : k = 7 := by omega
      rw [hk7]
    have e : ⁅v', u⁆ = (u * v' * u⁻¹ * v'⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (T.U 7).inv_mem h'
  have hcomm7 : u * ⁅v', u⁆ = ⁅v', u⁆ * u := by
    have h := T.comm 6 7 (by norm_num) (by norm_num) u hu ⁅v', u⁆ hvu7
    have hbot : (⨆ k ∈ Set.Ioo (6 : ℤ) 7, T.U k) = ⊥ := by
      rw [eq_bot_iff]
      refine iSup₂_le fun k hk => ?_
      obtain ⟨h1, h2⟩ := hk
      omega
    rw [hbot] at h
    have h1 : ⁅u, ⁅v', u⁆⁆ = 1 := by
      have h' : u * ⁅v', u⁆ * u⁻¹ * ⁅v', u⁆⁻¹ = 1 := by simpa using h
      simpa only [commutatorElement_def] using h'
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcb : c * b = b * c := by
    have hwin : b ∈ win T.U 2 10 :=
      T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hb)
    exact T.Uprime_comm_win (j := 6) (by norm_num) (by norm_num) hc hwin
  have hz_form : z = a * (w * b) * (c * u) * ⁅v', u⁆ := by
    rw [hz_eq]
    calc v' * v * u * v⁻¹ * v'⁻¹ = v' * (v * u * v⁻¹) * v'⁻¹ := by group
      _ = v' * (a * b * u) * v'⁻¹ := by rw [hvu]
      _ = (v' * a * v'⁻¹) * (v' * b * v'⁻¹) * (v' * u * v'⁻¹) := by group
      _ = (a * (w * c)) * b * (⁅v', u⁆ * u) := by rw [hv'a, hv'b, hv'u]
      _ = a * (w * b) * (c * u) * ⁅v', u⁆ := by
        have e1 : (a * (w * c)) * b * (⁅v', u⁆ * u) =
            a * w * (c * b) * (⁅v', u⁆ * u) := by group
        rw [e1, hcb]
        have e2 : a * w * (b * c) * (⁅v', u⁆ * u) = a * w * b * c * (u * ⁅v', u⁆) := by
          rw [← hcomm7]
          group
        rw [e2]
        group
  have hcomp1 : a * (w * b) * (c * u) = z ∧ ⁅v', u⁆ = 1 := by
    have hx1 : a * (w * b) * (c * u) ∈ win T.U 1 6 :=
      (win T.U 1 6).mul_mem ((win T.U 1 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 ha))
        ((win T.U 1 6).mul_mem (T.win_mono (by norm_num) (by norm_num) hw)
          (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hb))))
        ((win T.U 1 6).mul_mem
          (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc))
          (T.U_le_win (by norm_num) (by norm_num) hu))
    refine T.eq_of_mul_eq_mul (a := 1) (c := 6) (b := 7) (by norm_num) (by norm_num)
      (by norm_num) hx1 ?_ ?_ (Subgroup.one_mem _) ?_
    · exact T.win_mono (by norm_num) (by norm_num) hzwin
    · rw [show (6 : ℤ) + 1 = 7 by norm_num, T.win_self]
      exact hvu7
    · rw [hz_form]
      group
  have hcomp2 : a * (w * b) = z ∧ c * u = 1 := by
    have hx2 : a * (w * b) ∈ win T.U 1 5 :=
      (win T.U 1 5).mul_mem
        (T.U_le_win (a := 1) (b := 5) (k := 2) (by norm_num) (by norm_num)
          (T.Uprime_le 2 ha))
        ((win T.U 1 5).mul_mem
          (T.win_mono (a := 3) (b := 5) (c := 1) (d := 5) (by norm_num) (by norm_num) hw)
          (T.U_le_win (a := 1) (b := 5) (k := 4) (by norm_num) (by norm_num)
            (T.Uprime_le 4 hb)))
    have hy2 : c * u ∈ win T.U (5 + 1) 6 := by
      rw [show (5 : ℤ) + 1 = 6 by norm_num, T.win_self]
      exact (T.U 6).mul_mem (T.Uprime_le 6 hc) hu
    refine T.eq_of_mul_eq_mul (a := 1) (c := 5) (b := 6) (by norm_num) (by norm_num)
      (by norm_num) hx2 ?_ hy2 (Subgroup.one_mem _) ?_
    · exact T.win_mono (a := 1) (b := 2) (c := 1) (d := 5)
        (by norm_num) (by norm_num) hzwin
    · rw [hcomp1.1]
      group
  have hcomp3 : a = z ∧ w * b = 1 := by
    have hx3 : a ∈ win T.U 1 2 :=
      T.U_le_win (a := 1) (b := 2) (k := 2) (by norm_num) (by norm_num) (T.Uprime_le 2 ha)
    have hy3 : w * b ∈ win T.U (2 + 1) 5 :=
      (win T.U ((2 : ℤ) + 1) 5).mul_mem
        (T.win_mono (a := 3) (b := 5) (c := (2 : ℤ) + 1) (d := 5)
          (by norm_num) (by norm_num) hw)
        (T.U_le_win (a := (2 : ℤ) + 1) (b := 5) (k := 4) (by norm_num) (by norm_num)
          (T.Uprime_le 4 hb))
    refine T.eq_of_mul_eq_mul (a := 1) (c := 2) (b := 5) (by norm_num) (by norm_num)
      (by norm_num) hx3 hzwin hy3 (Subgroup.one_mem _) ?_
    rw [hcomp2.1]
    group
  have hu6 : u ∈ T.Uprime 6 := by
    have hu_eq : u = c⁻¹ := eq_inv_of_mul_eq_one_right hcomp2.2
    rw [hu_eq]
    exact (T.Uprime 6).inv_mem hc
  have ha1 : a ≠ 1 := by
    intro hae
    have hz_conj : z = (v' * v) * u * (v' * v)⁻¹ := by
      rw [hz_eq]
      group
    have hz1 : z = 1 := by rw [← hcomp3.1, hae]
    have hu1' : u = 1 := by
      have hc := congrArg (fun t => (v' * v)⁻¹ * t * (v' * v)) hz1
      rw [hz_conj] at hc
      have h2 : (v' * v)⁻¹ * ((v' * v) * u * (v' * v)⁻¹) * (v' * v) = u := by group
      rw [h2] at hc
      simpa using hc
    exact hu1 hu1'
  have hbu : b * u = u * b :=
    T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hb (T.Uprime_le 6 hu6)
  have hfinal : ⁅a⁻¹, T.nu 0 v⁆ = (b * u)⁻¹ := by
    have hw1 : w = b⁻¹ := eq_inv_of_mul_eq_one_left hcomp3.2
    have hc1 : c = u⁻¹ := eq_inv_of_mul_eq_one_left hcomp2.2
    calc ⁅a⁻¹, T.nu 0 v⁆ = w * c := by rw [show T.nu 0 v = v' from rfl, hwc]
      _ = b⁻¹ * u⁻¹ := by rw [hw1, hc1]
      _ = (b * u)⁻¹ := by rw [← mul_inv_rev, hbu]
  exact ⟨hu6, ha1, hfinal⟩

theorem lemma37 {v u a b : G} (hv : v ∈ T.Uprime 0) (hu : u ∈ T.U 6)
    (ha : a ∈ T.Uprime 2) (hb : b ∈ T.Uprime 4) (h : ⁅v, u⁆ = a * b) :
    u = 1 ∨ v = 1 := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  right
  by_contra hv1
  have hv0 : v ∈ T.U 0 := T.Uprime_le 0 hv
  obtain ⟨hu6, ha1, hconj⟩ :=
    T.lemma37a (v := v) (u := u) (a := a) (b := b) hv0 hv1 hu hu1 ha hb h
  have hbu : b * u = u * b :=
    T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hb (T.Uprime_le 6 hu6)
  have hconj' : ⁅a⁻¹, T.nu 0 v⁆ = b⁻¹ * u⁻¹ := by
    rw [hconj, mul_inv_rev]
    have hinv : u⁻¹ * b⁻¹ = b⁻¹ * u⁻¹ := by
      have h := congrArg Inv.inv hbu
      rwa [mul_inv_rev, mul_inv_rev] at h
    exact hinv
  have hv'U : T.nu 0 v ∈ T.U 8 := by simpa using T.nu_mem (n := 8) hv0 hv1
  have hv'1 : T.nu 0 v ≠ 1 := T.nu_ne_one (by norm_num) hv0 hv1
  have hmem0 : a⁻¹ ∈ (T.shift 2).U 0 := by
    rw [shift_U]
    simpa using (T.U 2).inv_mem (T.Uprime_le 2 ha)
  have hmem6 : T.nu 0 v ∈ (T.shift 2).U 6 := by
    rw [shift_U]
    simpa using hv'U
  have haS : b⁻¹ ∈ (T.shift 2).Uprime 2 := by
    rw [Uprime_shift]
    simpa using (T.Uprime 4).inv_mem hb
  have hbS : u⁻¹ ∈ (T.shift 2).Uprime 4 := by
    rw [Uprime_shift]
    simpa using (T.Uprime 6).inv_mem hu6
  have hres := lemma37a (T := T.shift 2) (v := a⁻¹) (u := T.nu 0 v)
    (a := b⁻¹) (b := u⁻¹) hmem0 (inv_ne_one.mpr ha1) hmem6 hv'1 haS hbS hconj'
  have h8 : T.nu 0 v ∈ T.Uprime 8 := by
    have h := hres.1
    rw [Uprime_shift] at h
    simpa using h
  exact T.nu_not_mem_Uprime hv hv1 h8

end TitsSystem

end CFSG.GH74.Tits83
