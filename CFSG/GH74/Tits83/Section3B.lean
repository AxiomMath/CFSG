module

public import CFSG.GH74.Tits83.Section3A

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G] {n : ℕ}

namespace TitsSystem

variable (T : TitsSystem G 8)

theorem Vmid_one_comm_Vmid_five {a b : G} (ha : a ∈ T.Vmid 1) (hb : b ∈ T.Vmid 5) :
    a * b = b * a := by
  have haU : a ∈ T.U 1 := T.Vmid_le 1 ha
  have hbU : b ∈ T.U 5 := T.Vmid_le 5 hb
  have haY : a ∈ T.Ybar 1 := ha.1
  have hbY : b ∈ T.Ybar 5 := hb.1
  have hnorm1 : T.U 5 ≤ Subgroup.normalizer (T.Ybar 1 : Set G) := by
    have h := normClosure2_normalized_right (T.U ((1 : ℤ) - 4)) (T.U ((1 : ℤ) + 4))
      (T.Uprime ((1 : ℤ) - 1))
    simpa [Ybar, show (1 : ℤ) - 4 = -3 by norm_num, show (1 : ℤ) + 4 = 5 by norm_num,
      show (1 : ℤ) - 1 = 0 by norm_num] using h
  have hnorm5 : T.U 1 ≤ Subgroup.normalizer (T.Ybar 5 : Set G) := by
    have h := normClosure2_normalized_left (T.U ((5 : ℤ) - 4)) (T.U ((5 : ℤ) + 4))
      (T.Uprime ((5 : ℤ) - 1))
    simpa [Ybar, show (5 : ℤ) - 4 = 1 by norm_num, show (5 : ℤ) + 4 = 9 by norm_num,
      show (5 : ℤ) - 1 = 4 by norm_num] using h
  have hmem1 : ⁅a, b⁆ ∈ T.Ybar 1 := by
    have hconj : b * a⁻¹ * b⁻¹ ∈ T.Ybar 1 :=
      (Subgroup.mem_normalizer_iff.mp (hnorm1 hbU) a⁻¹).mp ((T.Ybar 1).inv_mem haY)
    have h := (T.Ybar 1).mul_mem haY hconj
    simpa [commutatorElement_def, mul_assoc] using h
  have hmem5 : ⁅a, b⁆ ∈ T.Ybar 5 := by
    have hconj : a * b * a⁻¹ ∈ T.Ybar 5 :=
      (Subgroup.mem_normalizer_iff.mp (hnorm5 haU) b).mp hbY
    have h := (T.Ybar 5).mul_mem hconj ((T.Ybar 5).inv_mem hbY)
    simpa [commutatorElement_def, mul_assoc] using h
  have hsub1 : T.Ybar 1 ≤ win T.U 0 2 := by
    intro x hx
    have h := T.Ybar_subset 1 hx
    simp only [show (1 : ℤ) - 1 = 0 by norm_num,
      show (1 : ℤ) + 1 = 2 by norm_num] at h
    obtain ⟨p, hp, c, hc, rfl⟩ := h
    obtain ⟨q, hq, r, hr, rfl⟩ := hp
    exact (win T.U 0 2).mul_mem ((win T.U 0 2).mul_mem
      (T.U_le_win (k := 0) (by norm_num) (by norm_num) (T.Uprime_le 0 hq))
      (T.U_le_win (k := 1) (by norm_num) (by norm_num) hr))
      (T.U_le_win (k := 2) (by norm_num) (by norm_num) (T.Uprime_le 2 hc))
  have hsub5 : T.Ybar 5 ≤ win T.U 4 6 := by
    intro x hx
    have h := T.Ybar_subset 5 hx
    simp only [show (5 : ℤ) - 1 = 4 by norm_num,
      show (5 : ℤ) + 1 = 6 by norm_num] at h
    obtain ⟨p, hp, c, hc, rfl⟩ := h
    obtain ⟨q, hq, r, hr, rfl⟩ := hp
    exact (win T.U 4 6).mul_mem ((win T.U 4 6).mul_mem
      (T.U_le_win (k := 4) (by norm_num) (by norm_num) (T.Uprime_le 4 hq))
      (T.U_le_win (k := 5) (by norm_num) (by norm_num) hr))
      (T.U_le_win (k := 6) (by norm_num) (by norm_num) (T.Uprime_le 6 hc))
  have hbot : win T.U 0 2 ⊓ win T.U 4 6 = ⊥ := by
    rw [T.win_inf_win (a := 0) (b := 2) (c := 4) (d := 6) (by norm_num)]
    exact T.win_eq_bot (by norm_num)
  have hone : ⁅a, b⁆ = 1 := by
    have hmem : ⁅a, b⁆ ∈ win T.U 0 2 ⊓ win T.U 4 6 := ⟨hsub1 hmem1, hsub5 hmem5⟩
    rw [hbot] at hmem
    simpa using hmem
  have h1 : a * b * a⁻¹ = b := mul_inv_eq_one.mp hone
  calc a * b = (a * b * a⁻¹) * a := by group
    _ = b * a := by rw [h1]

theorem centralizer_Vmid_five {u : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hc : u ∈ Subgroup.centralizer (T.Vmid 5 : Set G)) :
    T.mu 1 u ∈ Subgroup.centralizer (T.Vmid 5 : Set G) ∧
      T.nu 1 u ∈ Subgroup.centralizer (T.Vmid 5 : Set G) ∧
      T.nu 9 (T.nu 1 u) ∈ Subgroup.centralizer (T.Vmid 5 : Set G) := by
  have hux : ∀ x ∈ T.Vmid 5, u * x = x * u := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  have hnu_mem : T.nu 1 u ∈ T.U 9 := by
    have h := T.nu_mem hu hu1
    rwa [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num] at h
  have hnu_ne : T.nu 1 u ≠ 1 := T.nu_ne_one (by norm_num) hu hu1
  have hnu_comm : T.nu 1 u ∈ Subgroup.centralizer (T.Vmid 5 : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact (T.lemma212_ii (by norm_num) (i := 1) (j := 5) (by norm_num) hu hu1
      (T.Vmid_le 5 hx) (hux x hx)).1
  have hmu_comm : T.mu 1 u ∈ Subgroup.centralizer (T.Vmid 5 : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact (T.lemma212_ii (by norm_num) (i := 1) (j := 5) (by norm_num) hu hu1
      (T.Vmid_le 5 hx) (hux x hx)).2
  refine ⟨hmu_comm, hnu_comm, ?_⟩
  refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
  have hxcomm : T.nu 1 u * x = x * T.nu 1 u :=
    (Subgroup.mem_centralizer_iff.mp hnu_comm x hx).symm
  exact (T.lemma212_ii' (by norm_num) (i := 9) (j := 5) (by norm_num) hnu_mem hnu_ne
    (T.Vmid_le 5 hx) hxcomm).1

theorem comm_mem_Uprime_mul_Vmid {u y : G} (hu : u ∈ T.U 1) (hy : y ∈ T.Uprime 6) :
    ∃ a ∈ T.Uprime 4, ∃ z ∈ T.Vmid 5, ⁅u, y⁆ = a * z := by
  have hyY : y ∈ T.Ybar 5 := T.Uprime_le_Ybar_right 5 hy
  have hnorm : T.U 1 ≤ Subgroup.normalizer (T.Ybar 5 : Set G) := by
    have h := normClosure2_normalized_left (T.U ((5 : ℤ) - 4)) (T.U ((5 : ℤ) + 4))
      (T.Uprime ((5 : ℤ) - 1))
    simpa [Ybar, show (5 : ℤ) - 4 = 1 by norm_num, show (5 : ℤ) + 4 = 9 by norm_num,
      show (5 : ℤ) - 1 = 4 by norm_num] using h
  have hconj : u * y * u⁻¹ ∈ T.Ybar 5 :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hu) y).mp hyY
  have hmem : ⁅u, y⁆ ∈ T.Ybar 5 := by
    have h := (T.Ybar 5).mul_mem hconj ((T.Ybar 5).inv_mem hyY)
    simpa [commutatorElement_def, mul_assoc] using h
  have hprod : ⁅u, y⁆ ∈ (T.Uprime 4 : Set G) * (T.Vmid 5 : Set G) * (T.Uprime 6 : Set G) := by
    have h := T.Ybar_eq 5
    simp only [show (5 : ℤ) - 1 = 4 by norm_num,
      show (5 : ℤ) + 1 = 6 by norm_num] at h
    change ⁅u, y⁆ ∈ (T.Ybar 5 : Set G) at hmem
    rwa [h] at hmem
  obtain ⟨az, haz, c, hc, heq⟩ := hprod
  obtain ⟨a, ha, z, hz, rfl⟩ := haz
  have hcomm : ⁅u, y⁆ ∈ win T.U 2 5 := by
    have h := T.comm 1 6 (by norm_num) (by norm_num) u hu y (T.Uprime_le 6 hy)
    have he : ⁅u, y⁆ = u * y * u⁻¹ * y⁻¹ := by simp [commutatorElement_def]
    rw [he]
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun k hk => ?_
    have hk' : (1 : ℤ) < k ∧ k < 6 := hk
    exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
  have hleft : a * z ∈ win T.U 2 5 := (win T.U 2 5).mul_mem
    ((T.U_le_win (by norm_num) (by norm_num)) (T.Uprime_le 4 ha))
    ((T.U_le_win (by norm_num) (by norm_num)) (T.Vmid_le 5 hz))
  have hright : c ∈ win T.U 6 6 := by
    rw [T.win_self]
    exact T.Uprime_le 6 hc
  have hcmp : (a * z) * c = ⁅u, y⁆ * 1 := heq.trans (mul_one _).symm
  have hsplit := T.eq_of_mul_eq_mul (a := 2) (c := 5) (b := 6) (by norm_num) (by norm_num)
    (by norm_num) hleft hcomm hright (win T.U 6 6).one_mem hcmp
  exact ⟨a, ha, z, hz, hsplit.1.symm⟩

theorem lemma33_i' {u y : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1) (hy : y ∈ T.Uprime 6) :
    ∃ z ∈ T.Vmid 5, ⁅u, y⁆ = T.mu 1 u * y * (T.mu 1 u)⁻¹ * z := by
  obtain ⟨ψ, hψ, z, hz, huy⟩ := T.comm_mem_Uprime_mul_Vmid hu hy
  have h9 : T.nu 1 u ∈ T.U 9 := by
    have h := T.nu_mem hu hu1
    rwa [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num] at h
  have h1 : T.nu 1 u ≠ 1 := T.nu_ne_one (by norm_num) hu hu1
  have hb17 : T.nu 9 (T.nu 1 u) ∈ T.U 17 := by
    have h := T.nu_mem h9 h1
    rwa [show (9 : ℤ) + (8 : ℕ) = 17 by norm_num] at h
  set w : G := T.nu 1 u with hw
  set wb : G := T.nu 9 (T.nu 1 u) with hwb
  have hw9 : w ∈ T.U 9 := by rw [hw]; exact h9
  have hwne : w ≠ 1 := by rw [hw]; exact h1
  have hwbU1 : wb ∈ T.U 1 := by
    rw [hwb]
    have he : T.U (17 : ℤ) = T.U 1 := by
      have h := U_add_two_mul T 1 1
      rwa [show (1 : ℤ) + 2 * (8 : ℕ) * 1 = 17 by norm_num] at h
    rwa [he] at hb17
  have hwy : w * y * w⁻¹ = y := by
    have hcomm : y * w = w * y :=
      T.Uprime_comm (j := 6) (k := 9) (by norm_num) (by norm_num) hy hw9
    rw [← hcomm]
    group
  have huyy : u * y * u⁻¹ = ψ * z * y := by
    have hc : ⁅u, y⁆ * y = u * y * u⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← hc, huy]
  have hm : T.mu 1 u = wb * w * u := by
    have h := T.mu_eq_nu_nu (by norm_num) hu hu1
    rw [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num, ← hwb, ← hw] at h
    exact h
  set B : G := ⁅ψ⁻¹, w⁆ * (w * z * w⁻¹) * y with hB
  have hX : T.mu 1 u * y * (T.mu 1 u)⁻¹ = wb * (ψ * B) * wb⁻¹ := by
    rw [hm]
    rw [show wb * w * u * y * (wb * w * u)⁻¹ =
        wb * (w * (u * y * u⁻¹) * w⁻¹) * wb⁻¹ by group]
    rw [huyy]
    rw [show w * (ψ * z * y) * w⁻¹ =
        (w * ψ * w⁻¹) * (w * z * w⁻¹) * (w * y * w⁻¹) by group]
    rw [hwy]
    rw [show w * ψ * w⁻¹ = ψ * ⁅ψ⁻¹, w⁆ by
      simp only [commutatorElement_def]; group]
    rw [hB]
    group
  have hmyU : T.mu 1 u * y * (T.mu 1 u)⁻¹ ∈ T.Uprime 4 :=
    T.mu_conj_mem_Uprime (i := 1) (j := 6) hu hu1 hy
  have hXcomm : (T.mu 1 u * y * (T.mu 1 u)⁻¹) * wb =
      wb * (T.mu 1 u * y * (T.mu 1 u)⁻¹) :=
    T.Uprime_comm (j := 4) (k := 1) (by norm_num) (by norm_num) hmyU hwbU1
  have hconjX : wb⁻¹ * (wb * (ψ * B) * wb⁻¹) * wb =
      T.mu 1 u * y * (T.mu 1 u)⁻¹ := by
    rw [← hX]
    rw [mul_assoc, hXcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hpsiX : ψ * B = T.mu 1 u * y * (T.mu 1 u)⁻¹ := by
    calc ψ * B = wb⁻¹ * (wb * (ψ * B) * wb⁻¹) * wb := by group
      _ = T.mu 1 u * y * (T.mu 1 u)⁻¹ := hconjX
  have hpsiInv : ψ⁻¹ ∈ T.U 4 := (T.U 4).inv_mem (T.Uprime_le 4 hψ)
  have hcommψ : ⁅ψ⁻¹, w⁆ ∈ win T.U 5 8 := by
    have h := T.comm 4 9 (by norm_num) (by norm_num) ψ⁻¹ hpsiInv w hw9
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun k hk => ?_
    have hk' : (4 : ℤ) < k ∧ k < 9 := hk
    exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
  have hwzU : w * z * w⁻¹ ∈ win T.U 5 8 := by
    have hzU : z ∈ T.U 5 := T.Vmid_le 5 hz
    have hmem : ⁅z, w⁆ ∈ win T.U 6 8 := by
      have h := T.comm 5 9 (by norm_num) (by norm_num) z hzU w hw9
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun k hk => ?_
      have hk' : (5 : ℤ) < k ∧ k < 9 := hk
      exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
    have hzw : w * z * w⁻¹ = ⁅w, z⁆ * z := by
      simp only [commutatorElement_def]
      group
    rw [hzw]
    refine (win T.U 5 8).mul_mem ?_ ((T.U_le_win (by norm_num) (by norm_num)) hzU)
    have hinv : ⁅w, z⁆ = ⁅z, w⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hinv]
    exact (win T.U 5 8).inv_mem ((T.win_mono (by norm_num) (by norm_num)) hmem)
  have hyWin : y ∈ win T.U 5 8 :=
    (T.U_le_win (k := 6) (by norm_num) (by norm_num)) (T.Uprime_le 6 hy)
  have hBwin : B ∈ win T.U 5 8 := by
    rw [hB]
    exact (win T.U 5 8).mul_mem ((win T.U 5 8).mul_mem hcommψ hwzU) hyWin
  have hpsiWin : ψ ∈ win T.U 4 4 := by
    rw [T.win_self]
    exact T.Uprime_le 4 hψ
  have hmyWin : T.mu 1 u * y * (T.mu 1 u)⁻¹ ∈ win T.U 4 4 := by
    rw [T.win_self]
    exact T.Uprime_le 4 hmyU
  have hcmp : ψ * B = (T.mu 1 u * y * (T.mu 1 u)⁻¹) * 1 := by
    rw [mul_one]
    exact hpsiX
  have hsplit := T.eq_of_mul_eq_mul (a := 4) (c := 4) (b := 8) (by norm_num) (by norm_num)
    (by norm_num) hpsiWin hmyWin hBwin (win T.U 5 8).one_mem hcmp
  have hpsi : ψ = T.mu 1 u * y * (T.mu 1 u)⁻¹ := hsplit.1
  exact ⟨z, hz, by rw [huy, hpsi]⟩

theorem lemma33_ii' (hT : T.Normalized) {u u' : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hc : u ∈ Subgroup.centralizer (T.Vmid 5 : Set G)) (hu' : u' ∈ T.U 1) (hu1' : u' ≠ 1)
    (hc' : u' ∈ Subgroup.centralizer (T.Vmid 5 : Set G)) (h : T.mu 1 u = T.mu 1 u') :
    u = u' := by
  obtain ⟨y, hy, hy1⟩ := T.exists_Uprime (j := 6) hT (by decide : Even (6 : ℤ))
  obtain ⟨z, hz, hzu⟩ := T.lemma33_i' hu hu1 hy
  obtain ⟨z', hz', hzu'⟩ := T.lemma33_i' hu' hu1' hy
  set a : G := T.mu 1 u * y * (T.mu 1 u)⁻¹ with ha
  set a' : G := T.mu 1 u' * y * (T.mu 1 u')⁻¹ with ha'
  have ha'eq : a = a' := by rw [ha, ha', h]
  have haU : a ∈ T.Uprime 4 := by
    rw [ha]
    exact T.mu_conj_mem_Uprime (i := 1) (j := 6) hu hu1 hy
  have haz : a * z = z * a :=
    T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) haU (T.Vmid_le 5 hz)
  have haz' : a * z'⁻¹ = z'⁻¹ * a :=
    T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) haU
      ((T.U 5).inv_mem (T.Vmid_le 5 hz'))
  have hcent : ∀ x ∈ T.Vmid 5, u'⁻¹ * x * u' = x := by
    intro x hx
    have hcomm : x * u' = u' * x := Subgroup.mem_centralizer_iff.mp hc' x hx
    calc u'⁻¹ * x * u' = u'⁻¹ * (x * u') := by group
      _ = u'⁻¹ * (u' * x) := by rw [hcomm]
      _ = x := by group
  have hzz : z * z'⁻¹ ∈ T.Vmid 5 := (T.Vmid 5).mul_mem hz ((T.Vmid 5).inv_mem hz')
  have hgy : ⁅u'⁻¹ * u, y⁆ = z * z'⁻¹ := by
    have h1 : ⁅u'⁻¹ * u, y⁆ = u'⁻¹ * (⁅u, y⁆ * ⁅u', y⁆⁻¹) * u' := by
      simp only [commutatorElement_def]
      group
    have h2 : ⁅u, y⁆ * ⁅u', y⁆⁻¹ = z * z'⁻¹ := by
      have hz' : a * z' = z' * a :=
        T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) haU (T.Vmid_le 5 hz')
      calc ⁅u, y⁆ * ⁅u', y⁆⁻¹ = (a * z) * (a * z')⁻¹ := by rw [hzu, hzu', ← ha'eq]
        _ = a * z * (z'⁻¹ * a⁻¹) := by rw [mul_inv_rev]
        _ = (a * z) * z'⁻¹ * a⁻¹ := by group
        _ = (z * a) * z'⁻¹ * a⁻¹ := by rw [haz]
        _ = z * (a * z'⁻¹) * a⁻¹ := by group
        _ = z * (z'⁻¹ * a) * a⁻¹ := by rw [haz']
        _ = z * z'⁻¹ := by group
    calc ⁅u'⁻¹ * u, y⁆ = u'⁻¹ * (z * z'⁻¹) * u' := by rw [h1, h2]
      _ = z * z'⁻¹ := hcent (z * z'⁻¹) hzz
  have hg : u'⁻¹ * u ∈ T.U 1 := (T.U 1).mul_mem ((T.U 1).inv_mem hu') hu
  by_cases hg1 : u'⁻¹ * u = 1
  · have : u = u' := by
      calc u = u' * (u'⁻¹ * u) := by group
        _ = u' * 1 := by rw [hg1]
        _ = u' := mul_one u'
    exact this
  · have hgU : ⁅u'⁻¹ * u, y⁆ = z * z'⁻¹ := hgy
    obtain ⟨z'', hz'', hzu''⟩ := T.lemma33_i' hg hg1 hy
    have hmV : T.mu 1 (u'⁻¹ * u) * y * (T.mu 1 (u'⁻¹ * u))⁻¹ ∈ T.Vmid 5 := by
      have heq : T.mu 1 (u'⁻¹ * u) * y * (T.mu 1 (u'⁻¹ * u))⁻¹ =
          (z * z'⁻¹) * z''⁻¹ := by
        calc T.mu 1 (u'⁻¹ * u) * y * (T.mu 1 (u'⁻¹ * u))⁻¹
            = (T.mu 1 (u'⁻¹ * u) * y * (T.mu 1 (u'⁻¹ * u))⁻¹ * z'') * z''⁻¹ := by
              group
          _ = ⁅u'⁻¹ * u, y⁆ * z''⁻¹ := by rw [← hzu'']
          _ = (z * z'⁻¹) * z''⁻¹ := by rw [hgU]
      rw [heq]
      exact (T.Vmid 5).mul_mem hzz ((T.Vmid 5).inv_mem hz'')
    have hmU : T.mu 1 (u'⁻¹ * u) * y * (T.mu 1 (u'⁻¹ * u))⁻¹ ∈ T.Uprime 4 :=
      T.mu_conj_mem_Uprime (i := 1) (j := 6) hg hg1 hy
    have hbot : T.U 4 ⊓ T.U 5 = ⊥ :=
      T.U_inf_U (k := 4) (l := 5) (by norm_num) (by norm_num)
    have hone : T.mu 1 (u'⁻¹ * u) * y * (T.mu 1 (u'⁻¹ * u))⁻¹ = 1 := by
      have hmem : T.mu 1 (u'⁻¹ * u) * y * (T.mu 1 (u'⁻¹ * u))⁻¹ ∈
          T.U 4 ⊓ T.U 5 := ⟨T.Uprime_le 4 hmU, T.Vmid_le 5 hmV⟩
      rw [hbot] at hmem
      simpa using hmem
    have hyone : y = 1 := by
      have := congrArg (fun x => (T.mu 1 (u'⁻¹ * u))⁻¹ * x * T.mu 1 (u'⁻¹ * u)) hone
      simpa [mul_assoc] using this
    exact absurd hyone hy1

theorem lemma33_ii'' (hT : T.Normalized) {u : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hc : u ∈ Subgroup.centralizer (T.Vmid 5 : Set G)) :
    T.nu 1 u = T.mu 1 u * u * (T.mu 1 u)⁻¹ ∧ T.nu 9 (T.nu 1 u) = u := by
  obtain ⟨hmuC, hnuC, hnu9C⟩ := T.centralizer_Vmid_five hu hu1 hc
  have hnu9 : T.nu 1 u ∈ T.U 9 := by
    have h := T.nu_mem hu hu1
    rwa [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num] at h
  have hnu9ne : T.nu 1 u ≠ 1 := T.nu_ne_one (by norm_num) hu hu1
  have hmU9 : T.mu 1 u * u * (T.mu 1 u)⁻¹ ∈ T.U 9 :=
    Moves.conj_mem T (T.moves_mu hu hu1) hu
  have hmC9 : T.mu 1 u * u * (T.mu 1 u)⁻¹ ∈
      Subgroup.centralizer (T.Vmid 5 : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hm : x * T.mu 1 u = T.mu 1 u * x :=
      Subgroup.mem_centralizer_iff.mp hmuC x hx
    have hu' : x * u = u * x := Subgroup.mem_centralizer_iff.mp hc x hx
    have hmconj : T.mu 1 u * x * (T.mu 1 u)⁻¹ = x := by
      rw [← hm]
      group
    calc x * (T.mu 1 u * u * (T.mu 1 u)⁻¹)
        = (x * T.mu 1 u) * u * (T.mu 1 u)⁻¹ := by group
      _ = (T.mu 1 u * x) * u * (T.mu 1 u)⁻¹ := by rw [hm]
      _ = T.mu 1 u * (x * u) * (T.mu 1 u)⁻¹ := by group
      _ = T.mu 1 u * (u * x) * (T.mu 1 u)⁻¹ := by rw [hu']
      _ = (T.mu 1 u * u * (T.mu 1 u)⁻¹) * (T.mu 1 u * x * (T.mu 1 u)⁻¹) := by
        group
      _ = (T.mu 1 u * u * (T.mu 1 u)⁻¹) * x := by rw [hmconj]
  have hmne : T.mu 1 u * u * (T.mu 1 u)⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have := congrArg (fun x => (T.mu 1 u)⁻¹ * x * T.mu 1 u) h
    simpa [mul_assoc] using this
  have hT' : (T.refl 10).Normalized := Normalized.refl (T := T) hT (by decide : Even (10 : ℤ))
  have hmu_eq : (T.refl 10).mu 1 (T.nu 1 u) =
      (T.refl 10).mu 1 (T.mu 1 u * u * (T.mu 1 u)⁻¹) := by
    rw [T.mu_refl (by norm_num) 10 1, T.mu_refl (by norm_num) 10 1]
    change T.mu 9 (T.nu 1 u) = T.mu 9 (T.mu 1 u * u * (T.mu 1 u)⁻¹)
    have h1 := (T.mu_nu (by norm_num) hu hu1).1
    rw [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num] at h1
    have h2 := T.mu_conj_self (by norm_num) hu hu1
    rw [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num] at h2
    rw [h1, h2]
  have hnu_eq : T.nu 1 u = T.mu 1 u * u * (T.mu 1 u)⁻¹ := by
    refine lemma33_ii' (T := T.refl 10) hT' (u := T.nu 1 u)
      (u' := T.mu 1 u * u * (T.mu 1 u)⁻¹) ?_ hnu9ne ?_ ?_ hmne ?_ hmu_eq
    · rw [refl_U]
      exact hnu9
    · rw [Vmid_refl]
      exact hnuC
    · rw [refl_U]
      exact hmU9
    · rw [Vmid_refl]
      exact hmC9
  have hnuU17 : T.nu 9 (T.nu 1 u) ∈ T.U 17 := by
    have h := T.nu_mem hnu9 hnu9ne
    rwa [show (9 : ℤ) + (8 : ℕ) = 17 by norm_num] at h
  have hnuU1 : T.nu 9 (T.nu 1 u) ∈ T.U 1 := by
    have he : T.U (17 : ℤ) = T.U 1 := by
      have h := U_add_two_mul T 1 1
      rwa [show (1 : ℤ) + 2 * (8 : ℕ) * 1 = 17 by norm_num] at h
    rwa [he] at hnuU17
  have hnuNe : T.nu 9 (T.nu 1 u) ≠ 1 :=
    T.nu_ne_one (by norm_num) hnu9 hnu9ne
  have hmEq : T.mu 1 (T.nu 9 (T.nu 1 u)) = T.mu 1 u := by
    have h1 := (T.mu_nu (by norm_num) hnu9 hnu9ne).1
    have h2 := (T.mu_nu (by norm_num) hu hu1).1
    have h3 := T.mu_add_two_mul (by norm_num) (1 : ℤ) (1 : ℤ) (T.nu 9 (T.nu 1 u))
    rw [show (9 : ℤ) + (8 : ℕ) = 17 by norm_num] at h1
    rw [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num] at h2
    rw [show (1 : ℤ) + 2 * (8 : ℕ) * 1 = 17 by norm_num] at h3
    rw [← h3, h1, h2]
  have hnu_nu : T.nu 9 (T.nu 1 u) = u :=
    (lemma33_ii' (T := T) (u := u) (u' := T.nu 9 (T.nu 1 u))
      hT hu hu1 hc hnuU1 hnuNe hnu9C hmEq.symm).symm
  exact ⟨hnu_eq, hnu_nu⟩

theorem Vmid_one_comm_U_five (hT : T.Normalized) {u x : G} (hu : u ∈ T.Vmid 1)
    (hx : x ∈ T.U 5) : u * x = x * u := by
  by_cases hu1 : u = 1
  · subst hu1
    simp
  have huU : u ∈ T.U 1 := T.Vmid_le 1 hu
  have huY : u ∈ T.Ybar 1 := hu.1
  have hcV : u ∈ Subgroup.centralizer (T.Vmid 5 : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
    exact (T.Vmid_one_comm_Vmid_five hu hb).symm
  have hii := T.lemma33_ii'' hT huU hu1 hcV
  set u' : G := T.nu 1 u with hu'
  set m : G := T.mu 1 u with hmdef
  set y : G := ⁅u, x⁆ with hy
  set mx : G := m * x * m⁻¹ with hmx
  set z : G := ⁅u⁻¹, mx⁆ with hz
  have hu'U9 : u' ∈ T.U 9 := by
    rw [hu']
    have h := T.nu_mem huU hu1
    rwa [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num] at h
  have hu'ne : u' ≠ 1 := by
    rw [hu']
    exact T.nu_ne_one (by norm_num) huU hu1
  have hm : m = u * u' * u := by
    rw [hmdef, hu']
    have h := T.mu_eq_nu_nu (by norm_num) huU hu1
    rw [show (1 : ℤ) + (8 : ℕ) = 9 by norm_num, ← hu'] at h
    rw [hii.2] at h
    exact h
  have hnorm1 : T.U 5 ≤ Subgroup.normalizer (T.Ybar 1 : Set G) := by
    have h := normClosure2_normalized_right (T.U ((1 : ℤ) - 4)) (T.U ((1 : ℤ) + 4))
      (T.Uprime ((1 : ℤ) - 1))
    simpa [Ybar, show (1 : ℤ) - 4 = -3 by norm_num, show (1 : ℤ) + 4 = 5 by norm_num,
      show (1 : ℤ) - 1 = 0 by norm_num] using h
  have hyY : y ∈ T.Ybar 1 := by
    rw [hy]
    have hconj : x * u⁻¹ * x⁻¹ ∈ T.Ybar 1 :=
      (Subgroup.mem_normalizer_iff.mp (hnorm1 hx) u⁻¹).mp ((T.Ybar 1).inv_mem huY)
    have h := (T.Ybar 1).mul_mem huY hconj
    simpa [commutatorElement_def, mul_assoc] using h
  have hyWin : y ∈ win T.U 2 4 := by
    rw [hy]
    have h := T.comm 1 5 (by norm_num) (by norm_num) u huU x hx
    have he : ⁅u, x⁆ = u * x * u⁻¹ * x⁻¹ := by simp [commutatorElement_def]
    rw [he]
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := hk
    exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
  have hyU2 : y ∈ T.Uprime 2 :=
    T.mem_Uprime_of_mem_Ybar (i := 1) hyY (by simpa using hyWin)
  have hmxU : mx ∈ T.U 5 := by
    rw [hmx, hmdef]
    have h := Moves.conj_mem T (T.moves_mu huU hu1) hx
    rwa [show (2 : ℤ) * 1 + (8 : ℕ) - 5 = 5 by norm_num] at h
  have hzY : z ∈ T.Ybar 1 := by
    rw [hz]
    have hconj : mx * u * mx⁻¹ ∈ T.Ybar 1 :=
      (Subgroup.mem_normalizer_iff.mp (hnorm1 hmxU) u).mp huY
    have h := (T.Ybar 1).mul_mem ((T.Ybar 1).inv_mem huY) hconj
    simpa [commutatorElement_def, mul_assoc] using h
  have hzWin : z ∈ win T.U 2 4 := by
    rw [hz]
    have h := T.comm 1 5 (by norm_num) (by norm_num) u⁻¹ ((T.U 1).inv_mem huU) mx hmxU
    have he : ⁅u⁻¹, mx⁆ = u⁻¹ * mx * (u⁻¹)⁻¹ * mx⁻¹ := by simp [commutatorElement_def]
    rw [he]
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := hk
    exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
  have hzU2 : z ∈ T.Uprime 2 :=
    T.mem_Uprime_of_mem_Ybar (i := 1) hzY (by simpa using hzWin)
  have hyx : y * x = u * x * u⁻¹ := by
    rw [hy]
    simp only [commutatorElement_def]
    group
  have heq : u' * y * u'⁻¹ * (u' * x * u'⁻¹) = z * mx := by
    calc u' * y * u'⁻¹ * (u' * x * u'⁻¹)
        = u' * (y * x) * u'⁻¹ := by group
      _ = u' * (u * x * u⁻¹) * u'⁻¹ := by rw [hyx]
      _ = (u' * u) * x * (u' * u)⁻¹ := by group
      _ = u⁻¹ * (m * x * m⁻¹) * u := by
            rw [hm]
            group
      _ = u⁻¹ * mx * u := by rw [hmx]
      _ = z * mx := by
            rw [hz]
            simp only [commutatorElement_def]
            group
  have hu'xWin : u' * x * u'⁻¹ ∈ win T.U 5 8 := by
    have hcomm : ⁅x, u'⁆ ∈ win T.U 6 8 := by
      have h := T.comm 5 9 (by norm_num) (by norm_num) x hx u' hu'U9
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := hk
      exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
    have hconj : u' * x * u'⁻¹ = ⁅x, u'⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [hconj]
    exact (win T.U 5 8).mul_mem
      ((win T.U 5 8).inv_mem ((T.win_mono (by norm_num) (by norm_num)) hcomm))
      ((T.U_le_win (by norm_num) (by norm_num)) hx)
  have hcommut : ⁅y⁻¹, u'⁆ = y⁻¹ * (u' * y * u'⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hmem : ⁅y⁻¹, u'⁆ ∈ (T.U 2 : Set G) * (win T.U 5 8 : Set G) := by
    have heq' : y⁻¹ * (u' * y * u'⁻¹) =
        (y⁻¹ * z) * (mx * (u' * x * u'⁻¹)⁻¹) := by
      calc y⁻¹ * (u' * y * u'⁻¹)
          = y⁻¹ * (u' * y * u'⁻¹ * (u' * x * u'⁻¹)) * (u' * x * u'⁻¹)⁻¹ := by group
        _ = y⁻¹ * (z * mx) * (u' * x * u'⁻¹)⁻¹ := by rw [heq]
        _ = (y⁻¹ * z) * (mx * (u' * x * u'⁻¹)⁻¹) := by group
    rw [hcommut, heq']
    exact Set.mul_mem_mul ((T.U 2).mul_mem ((T.U 2).inv_mem (T.Uprime_le 2 hyU2))
        (T.Uprime_le 2 hzU2))
      ((win T.U 5 8).mul_mem ((T.U_le_win (by norm_num) (by norm_num)) hmxU)
        ((win T.U 5 8).inv_mem hu'xWin))
  have hmem58 : ⁅y⁻¹, u'⁆ ∈ win T.U 5 8 := by
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    have hleft : a ∈ win T.U 2 2 := by rwa [T.win_self]
    have hright : b ∈ win T.U (2 + 1) 8 :=
      (T.win_mono (by norm_num) (by norm_num)) hb
    have hwin38 : ⁅y⁻¹, u'⁆ ∈ win T.U (2 + 1) 8 := by
      have h := T.comm 2 9 (by norm_num) (by norm_num) y⁻¹
        ((T.U 2).inv_mem (T.Uprime_le 2 hyU2)) u' hu'U9
      have he : ⁅y⁻¹, u'⁆ = y⁻¹ * u' * (y⁻¹)⁻¹ * u'⁻¹ := by
        simp [commutatorElement_def]
      rw [he]
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := hk
      exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
    have h1 : a * b = 1 * ⁅y⁻¹, u'⁆ := by rw [one_mul]; exact hab
    have hsplit := T.eq_of_mul_eq_mul (a := 2) (c := 2) (b := 8) (by norm_num) (by norm_num)
      (by norm_num) (x := a) (x' := 1) (y := b) (y' := ⁅y⁻¹, u'⁆) hleft
      (by rw [T.win_self]; exact (T.U 2).one_mem) hright hwin38 h1
    rw [← hsplit.2]
    exact hb
  by_cases hy1 : y = 1
  · have h1 : ⁅u, x⁆ = 1 := hy.symm.trans hy1
    have hcomm : u * x * u⁻¹ = x := by
      have h := congrArg (fun t => t * x) h1
      simpa [commutatorElement_def, mul_assoc] using h
    calc u * x = (u * x * u⁻¹) * u := by group
      _ = x * u := by rw [hcomm]
  · have h29 : ¬ ⁅y⁻¹, u'⁆ ∈ win T.U 4 8 := by
      have hU2 : y⁻¹ ∈ (T.shift 1).U 1 := by
        rw [shift_U]
        change y⁻¹ ∈ T.U 2
        exact (T.U 2).inv_mem (T.Uprime_le 2 hyU2)
      have hU9 : u' ∈ (T.shift 1).U 8 := by
        rw [shift_U]
        change u' ∈ T.U 9
        exact hu'U9
      have h := lemma29_five (T := T.shift 1) (n := 8) (by norm_num) (u := y⁻¹) (v := u')
        hU2 (inv_ne_one.mpr hy1) hU9 hu'ne
      have e : win (T.shift 1).U 3 (((8 : ℕ) : ℤ) - 1) = win T.U 4 8 := by
        rw [win_shift]
        rw [show (3 : ℤ) + 1 = 4 by norm_num,
          show (((8 : ℕ) : ℤ) - 1) + 1 = 8 by norm_num]
      rwa [e] at h
    exact absurd ((T.win_mono (by norm_num) (by norm_num)) hmem58) h29

theorem Vmid_five_comm_U_one (hT : T.Normalized) {u x : G} (hu : u ∈ T.Vmid 5)
    (hx : x ∈ T.U 1) : u * x = x * u := by
  have hT' : (T.refl 6).Normalized := Normalized.refl (T := T) hT (by decide : Even (6 : ℤ))
  have hu' : u ∈ (T.refl 6).Vmid 1 := by
    rw [Vmid_refl]
    show u ∈ T.Vmid 5
    exact hu
  have hx' : x ∈ (T.refl 6).U 5 := by
    rw [refl_U]
    show x ∈ T.U 1
    exact hx
  exact Vmid_one_comm_U_five (T := T.refl 6) hT' hu' hx'

theorem lemma33_ii (hT : T.Normalized) {u : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1) :
    T.nu 1 u = T.mu 1 u * u * (T.mu 1 u)⁻¹ ∧ T.nu 9 (T.nu 1 u) = u := by
  have hc : u ∈ Subgroup.centralizer (T.Vmid 5 : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
    exact T.Vmid_five_comm_U_one hT hb hu
  exact T.lemma33_ii'' hT hu hu1 hc

theorem nu_odd (hT : T.Normalized) {j : ℤ} (hj : Odd j) {u : G} (hu : u ∈ T.U j) (hu1 : u ≠ 1) :
    T.nu j u = T.mu j u * u * (T.mu j u)⁻¹ ∧ T.nu (j + 8) (T.nu j u) = u := by
  obtain ⟨k, hk⟩ := hj
  have heven : Even (j - 1) := ⟨k, by omega⟩
  have hT' : (T.shift (j - 1)).Normalized := Normalized.shift (T := T) hT heven
  have hu' : u ∈ (T.shift (j - 1)).U 1 := by
    rw [shift_U]
    rw [show (1 : ℤ) + (j - 1) = j by ring]
    exact hu
  have hmain := lemma33_ii (T := T.shift (j - 1)) hT' hu' hu1
  rw [T.nu_shift (by norm_num) (j - 1) 1 u, T.mu_shift (by norm_num) (j - 1) 1 u] at hmain
  rw [T.nu_shift (by norm_num) (j - 1) 9 (T.nu (1 + (j - 1)) u)] at hmain
  rw [show (1 : ℤ) + (j - 1) = j by ring,
    show (9 : ℤ) + (j - 1) = j + 8 by ring] at hmain
  exact hmain

theorem Vmid_five_eq_bot (hT : T.Normalized) : T.Vmid 5 = ⊥ := by
  have hU1W : T.U 1 ≤ Subgroup.normalizer (win T.U 2 8 : Set G) := by
    have h := (T.le_normalizer_win (a := 2) (b := 8) (by norm_num)).1
    simpa using h
  have hU9W : T.U 9 ≤ Subgroup.normalizer (win T.U 2 8 : Set G) := by
    have h := (T.le_normalizer_win (a := 2) (b := 8) (by norm_num)).2
    simpa using h
  have hnormCent : ∀ {X : Subgroup G},
      X ≤ Subgroup.normalizer (win T.U 2 8 : Set G) →
      X ≤ Subgroup.normalizer (Subgroup.centralizer (win T.U 2 8 : Set G) : Set G) := by
    intro X hX
    refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun y hy => ?_
    have himg : (MulAut.conj y).toMonoidHom '' (win T.U 2 8 : Set G) =
        (win T.U 2 8 : Set G) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hX hy) w).mp hw
      · intro hz
        refine ⟨y⁻¹ * z * y, ?_, ?_⟩
        · simpa using (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (win T.U 2 8 : Set G)).inv_mem (hX hy)) z).mp hz
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
    have hmap := Subgroup.map_centralizer_le_centralizer_image (win T.U 2 8 : Set G)
      (MulAut.conj y).toMonoidHom
    rwa [himg] at hmap
  have hYbar5 : T.Ybar 5 ≤ Subgroup.centralizer (win T.U 2 8 : Set G) := by
    have h := normClosure2_le (A := T.U ((5 : ℤ) - 4)) (B := T.U ((5 : ℤ) + 4))
      (X := T.Uprime ((5 : ℤ) - 1)) (Y := Subgroup.centralizer (win T.U 2 8 : Set G))
      (by
        intro x hx
        exact Subgroup.centralizer_le (T.win_mono (by norm_num) (by norm_num)) hx.1)
      (by rw [show (5 : ℤ) - 4 = 1 by norm_num]; exact hnormCent hU1W)
      (by rw [show (5 : ℤ) + 4 = 9 by norm_num]; exact hnormCent hU9W)
    simpa [Ybar, show (5 : ℤ) - 4 = 1 by norm_num, show (5 : ℤ) + 4 = 9 by norm_num,
      show (5 : ℤ) - 1 = 4 by norm_num] using h
  have hV5 : T.Vmid 5 ≤ Subgroup.centralizer (win T.U 1 9 : Set G) := by
    intro x hx
    rw [T.mem_centralizer_win_iff]
    intro k hk1 hk2 y hy
    by_cases hk1' : k = 1
    · subst hk1'
      exact (T.Vmid_five_comm_U_one hT hx hy).symm
    by_cases hk9 : k = 9
    · subst hk9
      have hT' : (T.refl 10).Normalized := Normalized.refl (T := T) hT (by decide : Even (10 : ℤ))
      have hx' : x ∈ (T.refl 10).Vmid 5 := by
        rw [Vmid_refl]
        show x ∈ T.Vmid 5
        exact hx
      have hy' : y ∈ (T.refl 10).U 1 := by
        rw [refl_U]
        show y ∈ T.U 9
        exact hy
      exact (Vmid_five_comm_U_one (T := T.refl 10) hT' hx' hy').symm
    · have hxZ : x ∈ Subgroup.centralizer (win T.U 2 8 : Set G) := hYbar5 hx.1
      have hk2' : 2 ≤ k := by omega
      have hk8 : k ≤ 8 := by omega
      exact Subgroup.mem_centralizer_iff.mp hxZ y (T.U_le_win hk2' hk8 hy)
  have hnuCent : ∀ x ∈ T.Vmid 5, x ≠ 1 →
      T.nu 5 x ∈ Subgroup.centralizer (win T.U 9 17 : Set G) := by
    intro x hx hx1
    have hxU : x ∈ T.U 5 := T.Vmid_le 5 hx
    have hxZ : x ∈ Subgroup.centralizer (win T.U 1 9 : Set G) := hV5 hx
    have hnuEq : T.nu 5 x = T.mu 5 x * x * (T.mu 5 x)⁻¹ :=
      (T.nu_odd hT (by decide : Odd (5 : ℤ)) hxU hx1).1
    have hmoves : T.Moves (T.mu 5 x) (fun j => 2 * 5 + 8 - j) := T.moves_mu hxU hx1
    have hmap : (win T.U 1 9).map (MulAut.conj (T.mu 5 x)).toMonoidHom =
        win T.U 9 17 := by
      have h := Moves.map_win_refl T hmoves 1 9
      rw [show 2 * (5 : ℤ) + 8 - 9 = 9 by norm_num,
        show 2 * (5 : ℤ) + 8 - 1 = 17 by norm_num] at h
      exact h
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hy' : (T.mu 5 x)⁻¹ * y * T.mu 5 x ∈ win T.U 1 9 := by
      have hmem : y ∈ (win T.U 1 9).map (MulAut.conj (T.mu 5 x)).toMonoidHom := by
        rw [hmap]
        exact hy
      obtain ⟨w, hw, hwy⟩ := hmem
      have heq : (T.mu 5 x)⁻¹ * y * T.mu 5 x = w := by
        rw [← hwy]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [heq]
    have hz : ((T.mu 5 x)⁻¹ * y * T.mu 5 x) * x =
        x * ((T.mu 5 x)⁻¹ * y * T.mu 5 x) :=
      Subgroup.mem_centralizer_iff.mp hxZ _ hy'
    calc y * T.nu 5 x = y * (T.mu 5 x * x * (T.mu 5 x)⁻¹) := by rw [hnuEq]
      _ = T.mu 5 x * (((T.mu 5 x)⁻¹ * y * T.mu 5 x) * x) * (T.mu 5 x)⁻¹ := by
        group
      _ = T.mu 5 x * (x * ((T.mu 5 x)⁻¹ * y * T.mu 5 x)) * (T.mu 5 x)⁻¹ := by
        rw [hz]
      _ = (T.mu 5 x * x * (T.mu 5 x)⁻¹) * y := by group
      _ = T.nu 5 x * y := by rw [hnuEq]
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  exact T.lemma31 (i := 5) (T.Vmid_le 5 hx) hx1 (hV5 hx) (hnuCent x hx hx1)

theorem lemma33_i (hT : T.Normalized) {u y : G} (hu : u ∈ T.U 1) (hy : y ∈ T.Uprime 6) :
    ⁅u, y⁆ ∈ T.Uprime 4 := by
  obtain ⟨a, ha, z, hz, h⟩ := T.comm_mem_Uprime_mul_Vmid hu hy
  have hzbot : z = 1 := by
    have hmem : z ∈ (⊥ : Subgroup G) := by
      rw [← T.Vmid_five_eq_bot hT]
      exact hz
    simpa using hmem
  rw [h, hzbot, mul_one]
  exact ha

theorem lemma33_i_eq (hT : T.Normalized) {u y : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hy : y ∈ T.Uprime 6) : ⁅u, y⁆ = T.mu 1 u * y * (T.mu 1 u)⁻¹ := by
  obtain ⟨z, hz, h⟩ := T.lemma33_i' hu hu1 hy
  have hzbot : z = 1 := by
    have hmem : z ∈ (⊥ : Subgroup G) := by
      rw [← T.Vmid_five_eq_bot hT]
      exact hz
    simpa using hmem
  rw [h, hzbot, mul_one]

theorem lemma33_i_mul (hT : T.Normalized) {u u' y : G} (hu : u ∈ T.U 1)
    (hu' : u' ∈ T.U 1) (hy : y ∈ T.Uprime 6) :
    ⁅u * u', y⁆ = ⁅u, y⁆ * ⁅u', y⁆ := by
  have huy : ⁅u, y⁆ ∈ T.Uprime 4 := T.lemma33_i hT hu hy
  have hu'y : ⁅u', y⁆ ∈ T.Uprime 4 := T.lemma33_i hT hu' hy
  have hcomm : u * ⁅u', y⁆ = ⁅u', y⁆ * u :=
    (T.Uprime_comm (j := 4) (k := 1) (by norm_num) (by norm_num) hu'y hu).symm
  have hconj : u * ⁅u', y⁆ * u⁻¹ = ⁅u', y⁆ := by
    rw [hcomm]
    group
  have hmulcomm : ⁅u', y⁆ * ⁅u, y⁆ = ⁅u, y⁆ * ⁅u', y⁆ :=
    T.Uprime_mul_comm (j := 4) hu'y huy
  calc ⁅u * u', y⁆ = u * ⁅u', y⁆ * u⁻¹ * ⁅u, y⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u', y⁆ * ⁅u, y⁆ := by rw [hconj]
    _ = ⁅u, y⁆ * ⁅u', y⁆ := hmulcomm

theorem lemma33_i_inj (hT : T.Normalized) {y : G} (hy : y ∈ T.Uprime 6) (hy1 : y ≠ 1)
    {u u' : G} (hu : u ∈ T.U 1) (hu' : u' ∈ T.U 1) (h : ⁅u, y⁆ = ⁅u', y⁆) : u = u' := by
  by_cases hu'1 : u' = 1
  · have h1 : ⁅u, y⁆ = 1 := by simpa [hu'1] using h
    by_cases hu1 : u = 1
    · rw [hu1, hu'1]
    · have heq := T.lemma33_i_eq hT hu hu1 hy
      rw [h1] at heq
      have hyone : y = 1 := by
        have := congrArg (fun t => (T.mu 1 u)⁻¹ * t * T.mu 1 u) heq.symm
        simpa [mul_assoc] using this
      exact absurd hyone hy1
  · set g : G := u'⁻¹ * u with hgdef
    have hgU : g ∈ T.U 1 := by
      rw [hgdef]
      exact (T.U 1).mul_mem ((T.U 1).inv_mem hu') hu
    have hinv : ⁅u'⁻¹, y⁆ = ⁅u', y⁆⁻¹ := by
      have hmul := T.lemma33_i_mul hT hu' ((T.U 1).inv_mem hu') hy
      have h1 : ⁅u' * u'⁻¹, y⁆ = 1 := by simp [commutatorElement_def]
      rw [hmul] at h1
      exact eq_inv_of_mul_eq_one_right h1
    by_cases hg1 : g = 1
    · rw [hgdef] at hg1
      calc u = u' * (u'⁻¹ * u) := by group
        _ = u' * 1 := by rw [hg1]
        _ = u' := mul_one u'
    · have hgEq : ⁅g, y⁆ = 1 := by
        have hmul := T.lemma33_i_mul hT ((T.U 1).inv_mem hu') hu hy
        rw [hgdef, hmul, hinv, h, inv_mul_cancel]
      have heq := T.lemma33_i_eq hT hgU hg1 hy
      rw [hgEq] at heq
      have hyone : y = 1 := by
        have := congrArg (fun t => (T.mu 1 g)⁻¹ * t * T.mu 1 g) heq.symm
        simpa [mul_assoc] using this
      exact absurd hyone hy1

theorem comm_odd_Uprime (hT : T.Normalized) {j : ℤ} (hj : Odd j) {u y : G} (hu : u ∈ T.U j)
    (hy : y ∈ T.Uprime (j + 5)) :
    ⁅u, y⁆ ∈ T.Uprime (j + 3) ∧ (u ≠ 1 → ⁅u, y⁆ = T.mu j u * y * (T.mu j u)⁻¹) := by
  obtain ⟨k, hk⟩ := hj
  have heven : Even (j - 1) := ⟨k, by omega⟩
  have hT' : (T.shift (j - 1)).Normalized := Normalized.shift (T := T) hT heven
  have hU : u ∈ (T.shift (j - 1)).U 1 := by
    rw [shift_U]
    rw [show (1 : ℤ) + (j - 1) = j by ring]
    exact hu
  have hY : y ∈ (T.shift (j - 1)).Uprime 6 := by
    rw [Uprime_shift]
    rw [show (6 : ℤ) + (j - 1) = j + 5 by ring]
    exact hy
  constructor
  · have hmem := lemma33_i (T := T.shift (j - 1)) hT' hU hY
    rw [Uprime_shift] at hmem
    rw [show (4 : ℤ) + (j - 1) = j + 3 by ring] at hmem
    exact hmem
  · intro hu1
    have heq := lemma33_i_eq (T := T.shift (j - 1)) hT' hU hu1 hY
    rw [T.mu_shift (by norm_num) (j - 1) 1 u] at heq
    rw [show (1 : ℤ) + (j - 1) = j by ring] at heq
    exact heq

theorem comm_odd_Uprime' (hT : T.Normalized) {j : ℤ} (hj : Odd j) {u y : G} (hu : u ∈ T.U j)
    (hy : y ∈ T.Uprime (j - 5)) :
    ⁅u, y⁆ ∈ T.Uprime (j - 3) ∧ (u ≠ 1 → ⁅u, y⁆ = T.mu j u * y * (T.mu j u)⁻¹) := by
  obtain ⟨k, hk⟩ := hj
  have heven : Even (j + 1) := ⟨k + 1, by omega⟩
  have hT' : (T.refl (j + 1)).Normalized := Normalized.refl (T := T) hT heven
  have hU : u ∈ (T.refl (j + 1)).U 1 := by
    rw [refl_U]
    rw [show j + 1 - 1 = j by ring]
    exact hu
  have hY : y ∈ (T.refl (j + 1)).Uprime 6 := by
    rw [Uprime_refl]
    rw [show j + 1 - 6 = j - 5 by ring]
    exact hy
  constructor
  · have hmem := lemma33_i (T := T.refl (j + 1)) hT' hU hY
    rw [Uprime_refl] at hmem
    rw [show j + 1 - 4 = j - 3 by ring] at hmem
    exact hmem
  · intro hu1
    have heq := lemma33_i_eq (T := T.refl (j + 1)) hT' hU hu1 hY
    rw [T.mu_refl (by norm_num) (j + 1) 1] at heq
    rw [show j + 1 - 1 = j by ring] at heq
    exact heq

end TitsSystem

end CFSG.GH74.Tits83
