module

public import CFSG.GH74.Tits83.Section3B
public import CFSG.GH74.Tits83.Section3A2

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace TitsSystem

variable (T : TitsSystem G 8)

private theorem comm_U_zero_one {x y : G} (hx : x ∈ T.U 0) (hy : y ∈ T.U 1) : x * y = y * x := by
  have h := T.comm 0 1 (by norm_num) (by norm_num) x hx y hy
  have hbot : win T.U 1 0 = ⊥ := T.win_eq_bot (by norm_num)
  have hmem : ⁅x, y⁆ ∈ win T.U 1 0 := by
    refine SetLike.le_def.mp (iSup₂_le fun k hk => ?_) h
    have hk' : 0 < k ∧ k < 1 := hk
    exact T.U_le_win (by omega) (by omega)
  rw [hbot] at hmem
  have hone : x * y * x⁻¹ * y⁻¹ = 1 := by simpa [commutatorElement_def] using hmem
  calc
    x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hone, one_mul]

private theorem lemma34_aux (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 3) (hu1 : u ≠ 1)
    (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1) :
    ⁅T.nu 8 v, u⁻¹⁆ = T.mu 8 v * ((T.mu 3 u)⁻¹ * v * T.mu 3 u) * (T.mu 8 v)⁻¹ ∧
      ⁅T.nu 8 v, (T.mu 3 u)⁻¹ * v * T.mu 3 u⁆ =
        T.mu 8 v * ((T.mu 3 u)⁻¹ * v * T.mu 3 u) * (T.mu 8 v)⁻¹ * u⁻¹ *
          (T.mu 8 v * u * (T.mu 8 v)⁻¹) := by
  classical
  have h3 : 3 ≤ (8 : ℕ) := by norm_num
  have hvU : v ∈ T.U 8 := T.Uprime_le 8 hv
  set mU : G := T.mu 3 u with hmU
  set m : G := T.mu 8 v with hm
  set vp : G := T.nu 8 v with hvp
  set w : G := T.nu 16 vp with hw
  set v1 : G := mU⁻¹ * v * mU with hv1def
  set X : G := m * u * m⁻¹ with hX
  set kk : G := X⁻¹ * (w⁻¹ * X * w) with hk
  set A : G := m * v1 * m⁻¹ with hA
  have hmUinv : mU⁻¹ = T.mu 3 u⁻¹ := by
    rw [hmU, T.mu_inv h3 hu hu1]
  have hv1U : v1 ∈ T.Uprime 6 := by
    have h := T.mu_conj_mem_Uprime (i := 3) (j := 8) ((T.U 3).inv_mem hu)
      (inv_ne_one.mpr hu1) hv
    have h' : T.mu 3 u⁻¹ * v * (T.mu 3 u⁻¹)⁻¹ = T.mu 3 u⁻¹ * v * mU := by
      rw [← hmUinv, inv_inv]
    rw [h'] at h
    have hidx : (2 * 3 + 8 - 8 : ℤ) = 6 := by norm_num
    rw [hidx] at h
    rw [hv1def, hmUinv]
    exact h
  have hvm : v * v1 = v1 * v :=
    (T.Uprime_comm (j := 6) (k := 8) (by norm_num) (by norm_num) hv1U hvU).symm
  have hv1eq : v1 = u⁻¹ * v * u * v⁻¹ := by
    have hnormS : (T.shift 2).Normalized := hT.shift (by norm_num)
    have hu' : u⁻¹ ∈ (T.shift 2).U 1 := by
      rw [shift_U]
      simpa using (T.U 3).inv_mem hu
    have hu1' : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
    have hv' : v ∈ (T.shift 2).Uprime 6 := by
      rw [Uprime_shift]
      simpa using hv
    have h33 := (T.shift 2).lemma33_i_eq hnormS hu' hu1' hv'
    have hmuS : (T.shift 2).mu 1 u⁻¹ = mU⁻¹ := by
      rw [T.mu_shift h3 2 1 u⁻¹]
      rw [show (1 : ℤ) + 2 = 3 by norm_num]
      rw [hmU]
      exact T.mu_inv h3 hu hu1
    rw [hmuS] at h33
    rw [hv1def]
    calc
      mU⁻¹ * v * mU = ⁅u⁻¹, v⁆ := by rw [h33]; group
      _ = u⁻¹ * v * u * v⁻¹ := by
        simp only [commutatorElement_def]
        group
  have hvp_mem : vp ∈ T.U 16 := by
    rw [hvp]
    have h := T.nu_mem hvU hv1
    rwa [show (8 : ℤ) + (8 : ℕ) = 16 by norm_num] at h
  have hvp_ne : vp ≠ 1 := by
    rw [hvp]
    exact T.nu_ne_one h3 hvU hv1
  have hw_mem : w ∈ T.U 8 := by
    rw [hw]
    have h := T.nu_mem hvp_mem hvp_ne
    rw [show (16 : ℤ) + (8 : ℕ) = (8 : ℤ) + 2 * ((8 : ℕ) : ℤ) * 1 by norm_num,
      U_add_two_mul T 8 1] at h
    exact h
  have hmu : m = w * vp * v := by
    rw [hm, hw, hvp]
    exact T.mu_eq_nu_nu h3 hvU hv1
  obtain ⟨y, hywin, hyeq⟩ := T.lemma212_iii' (n := 8) h3 (i := 8) (j := 6) (by norm_num)
    (by norm_num) hvU hv1 (T.Uprime_le 6 hv1U) hvm
  have hyeq' : v1⁻¹ * vp * v1 * vp⁻¹ = y * (m * v1 * m⁻¹) := by
    rw [hvp, hm]
    exact hyeq
  have hA2 : A ∈ T.Uprime 2 := by
    have h := T.mu_conj_mem_Uprime (i := 8) (j := 6) hvU hv1 hv1U
    have hidx : (2 * 8 + 8 - 6 : ℤ) = 2 + 16 * 1 := by norm_num
    rw [hidx, T.Uprime_add_two_mul (j := 2) (k := 1)] at h
    rw [hA, hm]
    exact h
  have hAcommV1 : A * v1 = v1 * A :=
    T.Uprime_comm (j := 2) (k := 6) (by norm_num) (by norm_num) hA2 (T.Uprime_le 6 hv1U)
  have hAcommY : A * y = y * A :=
    T.Uprime_comm_win (j := 2) (a := 3) (b := 5) (by norm_num) (by norm_num) hA2 hywin
  have hv1y : v1 * y = y * v1 :=
    T.Uprime_comm_win (j := 6) (a := 3) (b := 5) (by norm_num) (by norm_num) hv1U hywin
  have hstepA : vp * v1 * vp⁻¹ = A * (y * v1) := by
    have h1 : vp * v1 * vp⁻¹ = v1 * (y * A) := by
      calc
        vp * v1 * vp⁻¹ = v1 * (v1⁻¹ * vp * v1 * vp⁻¹) := by group
        _ = v1 * (y * (m * v1 * m⁻¹)) := by rw [hyeq']
        _ = v1 * (y * A) := by rw [hA]
    rw [h1]
    calc
      v1 * (y * A) = (v1 * y) * A := by group
      _ = (y * v1) * A := by rw [hv1y]
      _ = y * (v1 * A) := by group
      _ = y * (A * v1) := by rw [← hAcommV1]
      _ = y * A * v1 := by group
      _ = (A * y) * v1 := by rw [← hAcommY]
      _ = A * (y * v1) := by group
  have hvpv : vp * v = w⁻¹ * m := by
    calc
      vp * v = w⁻¹ * (w * vp * v) := by group
      _ = w⁻¹ * m := by rw [← hmu]
  have hconj : vp * v * u * v⁻¹ * vp⁻¹ = w⁻¹ * X * w := by
    calc
      vp * v * u * v⁻¹ * vp⁻¹ = (vp * v) * u * (vp * v)⁻¹ := by group
      _ = (w⁻¹ * m) * u * (w⁻¹ * m)⁻¹ := by rw [hvpv]
      _ = w⁻¹ * (m * u * m⁻¹) * w := by group
      _ = w⁻¹ * X * w := by rw [hX]
  have hLHS : vp * v1 * vp⁻¹ = (vp * u⁻¹ * vp⁻¹) * (w⁻¹ * X * w) := by
    rw [hv1eq]
    calc
      vp * (u⁻¹ * v * u * v⁻¹) * vp⁻¹ =
          (vp * u⁻¹ * vp⁻¹) * (vp * v * u * v⁻¹ * vp⁻¹) := by group
      _ = (vp * u⁻¹ * vp⁻¹) * (w⁻¹ * X * w) := by rw [hconj]
  have hcommu : vp * u⁻¹ * vp⁻¹ = ⁅vp, u⁻¹⁆ * u⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hXk : w⁻¹ * X * w = X * kk := by
    rw [hk]
    group
  have hEq1 : A * (y * v1) = ⁅vp, u⁻¹⁆ * ((u⁻¹ * X) * kk) := by
    rw [← hstepA, hLHS, hcommu, hXk]
    group
  have hAwin : A ∈ win T.U 1 2 :=
    T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 hA2)
  have hvp0 : vp ∈ T.U 0 := by
    have h : T.U 0 = T.U 16 := by
      have h' := U_add_two_mul T 0 1
      rw [show (0 : ℤ) + 2 * ((8 : ℕ) : ℤ) * 1 = 16 by norm_num] at h'
      exact h'.symm
    rwa [h]
  have hcommuwin : ⁅vp, u⁻¹⁆ ∈ win T.U 1 2 := by
    have h := T.comm 0 3 (by norm_num) (by norm_num) vp hvp0 u⁻¹ ((T.U 3).inv_mem hu)
    refine SetLike.le_def.mp (iSup₂_le fun k hk => ?_) h
    have hk' : (0 : ℤ) < k ∧ k < 3 := hk
    exact T.U_le_win (by omega) (by omega)
  have hyv1win : y * v1 ∈ win T.U 3 7 :=
    (win T.U 3 7).mul_mem (T.win_mono (by norm_num) (by norm_num) hywin)
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hv1U))
  have hX5 : X ∈ T.U 5 := by
    have h := Moves.conj_mem T (T.moves_mu hvU hv1) (j := 3) hu
    have hidx : (2 * 8 + ((8 : ℕ) : ℤ) - 3 : ℤ) = 5 + 2 * ((8 : ℕ) : ℤ) * 1 := by norm_num
    rw [hidx, U_add_two_mul T 5 1] at h
    rw [hX, hm]
    exact h
  have huxwin : u⁻¹ * X ∈ win T.U 3 5 :=
    (win T.U 3 5).mul_mem (T.U_le_win (by norm_num) (by norm_num) ((T.U 3).inv_mem hu))
      (T.U_le_win (by norm_num) (by norm_num) hX5)
  have hkw : kk ∈ win T.U 6 7 := by
    have h := T.comm 5 8 (by norm_num) (by norm_num) X⁻¹ ((T.U 5).inv_mem hX5)
      w⁻¹ ((T.U 8).inv_mem hw_mem)
    have he : X⁻¹ * (w⁻¹ * X * w) = X⁻¹ * w⁻¹ * (X⁻¹)⁻¹ * (w⁻¹)⁻¹ := by group
    rw [hk, he]
    refine SetLike.le_def.mp (iSup₂_le fun k hk' => ?_) h
    have hk'' : (5 : ℤ) < k ∧ k < 8 := hk'
    exact T.U_le_win (by omega) (by omega)
  have hprodR : (u⁻¹ * X) * kk ∈ win T.U 3 7 :=
    (win T.U 3 7).mul_mem (T.win_mono (by norm_num) (by norm_num) huxwin)
      (T.win_mono (by norm_num) (by norm_num) hkw)
  have hcmp1 := T.eq_of_mul_eq_mul (a := 1) (c := 2) (b := 7) (by norm_num) (by norm_num)
    (by norm_num) hAwin hcommuwin hyv1win hprodR hEq1
  have hcmp2 := T.eq_of_mul_eq_mul (a := 3) (c := 5) (b := 7) (by norm_num) (by norm_num)
    (by norm_num) hywin huxwin (T.U_le_win (by norm_num) (by norm_num)
      (T.Uprime_le 6 hv1U)) hkw hcmp1.2
  refine ⟨?_, ?_⟩
  · rw [← hcmp1.1, hA, hv1def]
  · calc
      ⁅vp, v1⁆ = (vp * v1 * vp⁻¹) * v1⁻¹ := by
        simp only [commutatorElement_def]

      _ = (A * (y * v1)) * v1⁻¹ := by rw [hstepA]
      _ = A * y := by group
      _ = A * (u⁻¹ * X) := by rw [hcmp2.1]
      _ = ⁅vp, u⁻¹⁆ * (u⁻¹ * X) := by rw [hcmp1.1]
      _ = m * v1 * m⁻¹ * u⁻¹ * (m * u * m⁻¹) := by
        rw [← hcmp1.1, hA, hX]
        group

theorem lemma34_one (hT : T.Normalized) {x u v : G} (hx : x ∈ T.U 1) (hu : u ∈ T.U 3)
    (hu1 : u ≠ 1) (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1) :
    ⁅x, T.mu 8 v * u * (T.mu 8 v)⁻¹⁆ = ⁅x, u⁆ := by
  classical
  have h3 : 3 ≤ (8 : ℕ) := by norm_num
  have hvU : v ∈ T.U 8 := T.Uprime_le 8 hv
  obtain ⟨hi, hii⟩ := T.lemma34_aux hT hu hu1 hv hv1
  set m : G := T.mu 8 v with hm
  set vp : G := T.nu 8 v with hvp
  set v1 : G := (T.mu 3 u)⁻¹ * v * T.mu 3 u with hv1def
  set X : G := m * u * m⁻¹ with hX
  set A : G := m * v1 * m⁻¹ with hA
  have hv1U : v1 ∈ T.Uprime 6 := by
    have h := T.mu_conj_mem_Uprime (i := 3) (j := 8) ((T.U 3).inv_mem hu)
      (inv_ne_one.mpr hu1) hv
    have hmUinv : T.mu 3 u⁻¹ = (T.mu 3 u)⁻¹ := T.mu_inv h3 hu hu1
    have hidx : (2 * 3 + 8 - 8 : ℤ) = 6 := by norm_num
    rw [hmUinv, hidx] at h
    simpa [hv1def] using h
  have hX5 : X ∈ T.U 5 := by
    have h := Moves.conj_mem T (T.moves_mu hvU hv1) (j := 3) hu
    have hidx : (2 * 8 + ((8 : ℕ) : ℤ) - 3 : ℤ) = 5 + 2 * ((8 : ℕ) : ℤ) * 1 := by norm_num
    rw [hidx, U_add_two_mul T 5 1] at h
    simpa [hX, hm] using h
  have hA2 : A ∈ T.Uprime 2 := by
    have h := T.mu_conj_mem_Uprime (i := 8) (j := 6) hvU hv1 hv1U
    have hidx : (2 * 8 + 8 - 6 : ℤ) = 2 + 16 * 1 := by norm_num
    rw [hidx, T.Uprime_add_two_mul (j := 2) (k := 1)] at h
    simpa [hA, hm] using h
  have hvp_mem : vp ∈ T.U 16 := by
    rw [hvp]
    have h := T.nu_mem hvU hv1
    rwa [show (8 : ℤ) + (8 : ℕ) = 16 by norm_num] at h
  have hvp0 : vp ∈ T.U 0 := by
    have h : T.U 0 = T.U 16 := by
      have h' := U_add_two_mul T 0 1
      rw [show (0 : ℤ) + 2 * ((8 : ℕ) : ℤ) * 1 = 16 by norm_num] at h'
      exact h'.symm
    rwa [h]
  have hii' : ⁅vp, v1⁆ = A * u⁻¹ * X := by
    simpa [hA, hX, hv1def, hm, hvp] using hii
  have hxA : x * A = A * x :=
    (T.Uprime_comm (j := 2) (k := 1) (by norm_num) (by norm_num) hA2 hx).symm
  have hAconj : x * A⁻¹ * x⁻¹ = A⁻¹ := by
    have h := (Commute.inv_right (show Commute x A from hxA)).eq
    rw [h]
    group
  have hAinv : x * A⁻¹ = A⁻¹ * x := by
    calc
      x * A⁻¹ = x * A⁻¹ * x⁻¹ * x := by group
      _ = A⁻¹ * x := by rw [hAconj]
  have hc4 : ⁅x, v1⁆ ∈ T.Uprime 4 :=
    (T.comm_odd_Uprime hT (j := 1) (by norm_num) hx (by simpa using hv1U)).1
  have hxv1 : x * v1 * x⁻¹ = ⁅x, v1⁆ * v1 := by
    simp only [commutatorElement_def]
    group
  have hcv1 : ⁅x, v1⁆ * v1 = v1 * ⁅x, v1⁆ :=
    T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hc4 (T.Uprime_le 6 hv1U)
  have hcvp : ⁅x, v1⁆ * vp = vp * ⁅x, v1⁆ :=
    T.Uprime_comm (j := 4) (k := 0) (by norm_num) (by norm_num) hc4 hvp0
  have hxvp : x * vp * x⁻¹ = vp := by
    have hcomm : vp * x = x * vp := comm_U_zero_one T hvp0 hx
    rw [← hcomm]
    group
  have hmem_vv : ⁅vp, v1⁆ ∈ win T.U 0 8 := by
    rw [hii']
    exact (win T.U 0 8).mul_mem ((win T.U 0 8).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 hA2))
      (T.U_le_win (by norm_num) (by norm_num) ((T.U 3).inv_mem hu)))
      (T.U_le_win (by norm_num) (by norm_num) hX5)
  have hc_vv : ⁅x, v1⁆ * ⁅vp, v1⁆ = ⁅vp, v1⁆ * ⁅x, v1⁆ :=
    T.Uprime_comm_win (j := 4) (a := 0) (b := 8) (by norm_num) (by norm_num) hc4 hmem_vv
  have hcvpinv : ⁅x, v1⁆ * vp⁻¹ = vp⁻¹ * ⁅x, v1⁆ :=
    (Commute.inv_right (show Commute _ _ from hcvp)).eq
  have hcv1inv : ⁅x, v1⁆ * v1⁻¹ = v1⁻¹ * ⁅x, v1⁆ :=
    (Commute.inv_right (show Commute _ _ from hcv1)).eq
  have hcY : ⁅x, v1⁆ * (vp * v1 * vp⁻¹ * v1⁻¹) =
      (vp * v1 * vp⁻¹ * v1⁻¹) * ⁅x, v1⁆ := by
    calc
      ⁅x, v1⁆ * (vp * v1 * vp⁻¹ * v1⁻¹) = ⁅x, v1⁆ * vp * v1 * vp⁻¹ * v1⁻¹ := by group
      _ = vp * ⁅x, v1⁆ * v1 * vp⁻¹ * v1⁻¹ := by rw [hcvp]
      _ = vp * (⁅x, v1⁆ * v1) * vp⁻¹ * v1⁻¹ := by group
      _ = vp * (v1 * ⁅x, v1⁆) * vp⁻¹ * v1⁻¹ := by rw [hcv1]
      _ = vp * v1 * ⁅x, v1⁆ * vp⁻¹ * v1⁻¹ := by group
      _ = vp * v1 * (⁅x, v1⁆ * vp⁻¹) * v1⁻¹ := by group
      _ = vp * v1 * (vp⁻¹ * ⁅x, v1⁆) * v1⁻¹ := by rw [hcvpinv]
      _ = vp * v1 * vp⁻¹ * ⁅x, v1⁆ * v1⁻¹ := by group
      _ = vp * v1 * vp⁻¹ * (⁅x, v1⁆ * v1⁻¹) := by group
      _ = vp * v1 * vp⁻¹ * (v1⁻¹ * ⁅x, v1⁆) := by rw [hcv1inv]
      _ = (vp * v1 * vp⁻¹ * v1⁻¹) * ⁅x, v1⁆ := by group
  have hxcomm : x * ⁅vp, v1⁆ * x⁻¹ = ⁅vp, v1⁆ := by
    have hconj : x * ⁅vp, v1⁆ * x⁻¹ = (x * vp * x⁻¹) * (x * v1 * x⁻¹) *
        (x * vp * x⁻¹)⁻¹ * (x * v1 * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hcx : (x * vp * x⁻¹) * (x * v1 * x⁻¹) * (x * vp * x⁻¹)⁻¹ *
        (x * v1 * x⁻¹)⁻¹ = vp * (⁅x, v1⁆ * v1) * vp⁻¹ * (⁅x, v1⁆ * v1)⁻¹ := by
      rw [hxvp, hxv1]
    have hstep2 : vp * (⁅x, v1⁆ * v1) * vp⁻¹ * (⁅x, v1⁆ * v1)⁻¹ =
        ⁅x, v1⁆ * (vp * v1 * vp⁻¹ * v1⁻¹) * (⁅x, v1⁆)⁻¹ := by
      calc
        vp * (⁅x, v1⁆ * v1) * vp⁻¹ * (⁅x, v1⁆ * v1)⁻¹ =
            (vp * ⁅x, v1⁆) * v1 * vp⁻¹ * v1⁻¹ * (⁅x, v1⁆)⁻¹ := by group
        _ = (⁅x, v1⁆ * vp) * v1 * vp⁻¹ * v1⁻¹ * (⁅x, v1⁆)⁻¹ := by rw [hcvp]
        _ = ⁅x, v1⁆ * (vp * v1 * vp⁻¹ * v1⁻¹) * (⁅x, v1⁆)⁻¹ := by group
    have hfin : ⁅x, v1⁆ * (vp * v1 * vp⁻¹ * v1⁻¹) * (⁅x, v1⁆)⁻¹ =
        vp * v1 * vp⁻¹ * v1⁻¹ := by
      calc
        ⁅x, v1⁆ * (vp * v1 * vp⁻¹ * v1⁻¹) * (⁅x, v1⁆)⁻¹ =
            (⁅x, v1⁆ * (vp * v1 * vp⁻¹ * v1⁻¹)) * (⁅x, v1⁆)⁻¹ := by group
        _ = ((vp * v1 * vp⁻¹ * v1⁻¹) * ⁅x, v1⁆) * (⁅x, v1⁆)⁻¹ := by rw [hcY]
        _ = vp * v1 * vp⁻¹ * v1⁻¹ := by group
    rw [hconj, hcx, hstep2, hfin]
    rfl
  have hxcomm' : x * ⁅vp, v1⁆ = ⁅vp, v1⁆ * x := by
    calc
      x * ⁅vp, v1⁆ = x * ⁅vp, v1⁆ * x⁻¹ * x := by group
      _ = ⁅vp, v1⁆ * x := by rw [hxcomm]
  have hxg : x * (u⁻¹ * X) = (u⁻¹ * X) * x := by
    have hg : u⁻¹ * X = A⁻¹ * ⁅vp, v1⁆ := by
      rw [hii']
      group
    have hconj_g : x * (A⁻¹ * ⁅vp, v1⁆) * x⁻¹ = A⁻¹ * ⁅vp, v1⁆ := by
      calc
        x * (A⁻¹ * ⁅vp, v1⁆) * x⁻¹ =
            (x * A⁻¹ * x⁻¹) * (x * ⁅vp, v1⁆ * x⁻¹) := by group
        _ = A⁻¹ * ⁅vp, v1⁆ := by rw [hAconj, hxcomm]
    rw [hg]
    calc
      x * (A⁻¹ * ⁅vp, v1⁆) = x * (A⁻¹ * ⁅vp, v1⁆) * x⁻¹ * x := by group
      _ = (A⁻¹ * ⁅vp, v1⁆) * x := by rw [hconj_g]
  have hxg_one : ⁅x, u⁻¹ * X⁆ = 1 := by
    rw [commutatorElement_def, hxg]
    group
  have hXg : X = u * (u⁻¹ * X) := by group
  calc
    ⁅x, X⁆ = ⁅x, u * (u⁻¹ * X)⁆ := by
      conv_lhs => rw [hXg]
    _ = ⁅x, u⁆ * (u * ⁅x, u⁻¹ * X⁆ * u⁻¹) := by
      simp only [commutatorElement_def]
      group
    _ = ⁅x, u⁆ := by rw [hxg_one]; group

theorem lemma34_i (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 3) (hu1 : u ≠ 1)
    (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1) :
    ⁅T.nu 8 v, u⁻¹⁆ = T.mu 8 v * ((T.mu 3 u)⁻¹ * v * T.mu 3 u) * (T.mu 8 v)⁻¹ :=
  (T.lemma34_aux hT hu hu1 hv hv1).1

theorem lemma34_ii (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 3) (hu1 : u ≠ 1)
    (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1) :
    ⁅T.nu 8 v, (T.mu 3 u)⁻¹ * v * T.mu 3 u⁆ =
      T.mu 8 v * ((T.mu 3 u)⁻¹ * v * T.mu 3 u) * (T.mu 8 v)⁻¹ * u⁻¹ *
        (T.mu 8 v * u * (T.mu 8 v)⁻¹) :=
  (T.lemma34_aux hT hu hu1 hv hv1).2

theorem comm_one_five_mem (hT : T.Normalized) {x y : G} (hx : x ∈ T.U 1) (hy : y ∈ T.U 5) :
    ⁅x, y⁆ ∈ T.U 2 := by
  classical
  have h3 : 3 ≤ (8 : ℕ) := by norm_num
  obtain ⟨v, hv, hv1⟩ := T.exists_Uprime hT (j := 8) ⟨4, by norm_num⟩
  have hvU : v ∈ T.U 8 := T.Uprime_le 8 hv
  have hu3 : (T.mu 8 v)⁻¹ * y * T.mu 8 v ∈ T.U 3 := by
    have hmoves := T.moves_mu hvU hv1
    have hinv : T.Moves (T.mu 8 v)⁻¹ (fun j => 2 * 8 + ((8 : ℕ) : ℤ) - j) :=
      Moves.inv_refl T hmoves
    have h := Moves.conj_mem T hinv (j := 5) hy
    have hidx : (2 * 8 + ((8 : ℕ) : ℤ) - 5 : ℤ) = 3 + 2 * ((8 : ℕ) : ℤ) * 1 := by norm_num
    rw [hidx, U_add_two_mul T 3 1] at h
    simpa using h
  by_cases hu1 : (T.mu 8 v)⁻¹ * y * T.mu 8 v = 1
  · have hy1 : y = 1 := by
      have h : T.mu 8 v * ((T.mu 8 v)⁻¹ * y * T.mu 8 v) * (T.mu 8 v)⁻¹ = y := by group
      rw [hu1] at h
      have h' : (1 : G) = y := by simpa using h
      exact h'.symm
    rw [hy1]
    simp [commutatorElement_def]
  · have h := T.lemma34_one hT hx hu3 hu1 hv hv1
    have hyform : T.mu 8 v * ((T.mu 8 v)⁻¹ * y * T.mu 8 v) * (T.mu 8 v)⁻¹ = y := by
      group
    rw [hyform] at h
    rw [h]
    have hcomm := T.comm 1 3 (by norm_num) (by norm_num) x hx
      ((T.mu 8 v)⁻¹ * y * T.mu 8 v) hu3
    have hmem : ⁅x, (T.mu 8 v)⁻¹ * y * T.mu 8 v⁆ ∈ win T.U 2 2 := by
      refine SetLike.le_def.mp (iSup₂_le fun k hk => ?_) hcomm
      have hk' : (1 : ℤ) < k ∧ k < 3 := hk
      exact T.U_le_win (by omega) (by omega)
    rwa [T.win_self] at hmem

theorem lemma34_iii (hT : T.Normalized) {x y : G} (hx : x ∈ T.U 1) (hy : y ∈ T.U 5) :
    x * y = y * x := by
  have h2 : ⁅x, y⁆ ∈ T.U 2 := T.comm_one_five_mem hT hx hy
  have hnormR : (T.refl 6).Normalized := hT.refl (⟨3, by norm_num⟩ : Even (6 : ℤ))
  have hx' : y ∈ (T.refl 6).U 1 := by
    rw [refl_U, show (6 : ℤ) - 1 = 5 by norm_num]
    exact hy
  have hy' : x ∈ (T.refl 6).U 5 := by
    rw [refl_U, show (6 : ℤ) - 5 = 1 by norm_num]
    exact hx
  have h4 : ⁅y, x⁆ ∈ (T.refl 6).U 2 := (T.refl 6).comm_one_five_mem hnormR hx' hy'
  rw [refl_U, show (6 : ℤ) - 2 = 4 by norm_num] at h4
  have h4' : ⁅x, y⁆ ∈ T.U 4 := by
    have h := (T.U 4).inv_mem h4
    rwa [show ⁅y, x⁆⁻¹ = ⁅x, y⁆ by
      simp only [commutatorElement_def]
      group] at h
  have hmem : ⁅x, y⁆ ∈ T.U 2 ⊓ T.U 4 := ⟨h2, h4'⟩
  rw [T.U_inf_U (by norm_num) (by norm_num)] at hmem
  exact (commutatorElement_eq_one_iff_commute.mp (by simpa using hmem)).eq

theorem lemma34_iv (hT : T.Normalized) {x y : G} (hx : x ∈ T.U 1) (hy : y ∈ T.U 3) :
    x * y = y * x := by
  rcases eq_or_ne y 1 with rfl | hy1
  · simp
  obtain ⟨v, hv, hv1⟩ := T.exists_Uprime hT (j := 8) ⟨4, by norm_num⟩
  have hvU : v ∈ T.U 8 := T.Uprime_le 8 hv
  have hy5 : T.mu 8 v * y * (T.mu 8 v)⁻¹ ∈ T.U 5 := by
    have h := Moves.conj_mem T (T.moves_mu hvU hv1) (j := 3) hy
    have hidx : (2 * 8 + ((8 : ℕ) : ℤ) - 3 : ℤ) = 5 + 2 * ((8 : ℕ) : ℤ) * 1 := by norm_num
    rw [hidx, U_add_two_mul T 5 1] at h
    exact h
  have hcomm5 : x * (T.mu 8 v * y * (T.mu 8 v)⁻¹) =
      (T.mu 8 v * y * (T.mu 8 v)⁻¹) * x := T.lemma34_iii hT hx hy5
  have h1 : ⁅x, T.mu 8 v * y * (T.mu 8 v)⁻¹⁆ = 1 := by
    rw [commutatorElement_def, hcomm5]
    group
  have h2 := T.lemma34_one hT hx hy hy1 hv hv1
  rw [h1] at h2
  exact (commutatorElement_eq_one_iff_commute.mp h2.symm).eq

theorem comm_odd_add_four (hT : T.Normalized) {j : ℤ} (hj : Odd j) {x y : G}
    (hx : x ∈ T.U j) (hy : y ∈ T.U (j + 4)) : x * y = y * x := by
  have hshift : (T.shift (j - 1)).Normalized := hT.shift (hj.sub_odd odd_one)
  have hx' : x ∈ (T.shift (j - 1)).U 1 := by
    rw [shift_U, show (1 : ℤ) + (j - 1) = j by ring]
    exact hx
  have hy' : y ∈ (T.shift (j - 1)).U 5 := by
    rw [shift_U, show (5 : ℤ) + (j - 1) = j + 4 by ring]
    exact hy
  exact (T.shift (j - 1)).lemma34_iii hshift hx' hy'

theorem comm_odd_add_two (hT : T.Normalized) {j : ℤ} (hj : Odd j) {x y : G}
    (hx : x ∈ T.U j) (hy : y ∈ T.U (j + 2)) : x * y = y * x := by
  have hshift : (T.shift (j - 1)).Normalized := hT.shift (hj.sub_odd odd_one)
  have hx' : x ∈ (T.shift (j - 1)).U 1 := by
    rw [shift_U, show (1 : ℤ) + (j - 1) = j by ring]
    exact hx
  have hy' : y ∈ (T.shift (j - 1)).U 3 := by
    rw [shift_U, show (3 : ℤ) + (j - 1) = j + 2 by ring]
    exact hy
  exact (T.shift (j - 1)).lemma34_iv hshift hx' hy'

theorem comm_one_seven_mem (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 1) (hv : v ∈ T.U 7) :
    ⁅u, v⁆ ∈ win T.U 3 6 := by
  by_cases hu1 : u = 1
  · subst hu1
    simp
  set w := T.nu' 1 u
  have hw : w ∈ T.U 9 := by
    have h := T.nu'_mem hu hu1
    simpa using h
  have hw1 : w ≠ 1 := T.nu'_ne_one (by norm_num : 3 ≤ 8) hu hu1
  have hnu9 : T.nu 9 w = u := by
    have h := (T.mu_nu' (by norm_num : 3 ≤ 8) hu hu1).2
    simpa using h
  have hmu9 : T.mu 9 w = T.mu 1 u := by
    have h := (T.mu_nu' (by norm_num : 3 ≤ 8) hu hu1).1
    simpa using h
  have hv' : v⁻¹ ∈ T.U 7 := (T.U 7).inv_mem hv
  have hcomm : w * v⁻¹ = v⁻¹ * w :=
    (comm_odd_add_two (T := T) hT (j := 7) (by decide) hv' hw).symm
  obtain ⟨y, hy, hprod⟩ := lemma212_iii' (T := T) (by norm_num : 3 ≤ 8) (i := 9) (j := 7)
    (by norm_num) (by norm_num) hw hw1 hv' hcomm
  have hmain : v * u * v⁻¹ * u⁻¹ = y * (T.mu 1 u * v⁻¹ * (T.mu 1 u)⁻¹) := by
    simpa only [inv_inv, hnu9, hmu9] using hprod
  have hmem3 : T.mu 1 u * v⁻¹ * (T.mu 1 u)⁻¹ ∈ T.U 3 := by
    have hm := Moves.conj_mem T (T.moves_mu hu hu1) (j := 7) hv'
    have e : 2 * (1 : ℤ) + (8 : ℕ) - 7 = 3 := by norm_num
    rwa [e] at hm
  have hgoal : v * u * v⁻¹ * u⁻¹ ∈ win T.U 3 6 := by
    rw [hmain]
    exact (win T.U 3 6).mul_mem
      (T.win_mono (a := 4) (b := 6) (c := 3) (d := 6) (by norm_num) (by norm_num) hy)
      (T.U_le_win (a := 3) (b := 6) (k := 3) (by norm_num) (by norm_num) hmem3)
  have hinv := (win T.U 3 6).inv_mem hgoal
  have e : ⁅u, v⁆ = (v * u * v⁻¹ * u⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rwa [e]

theorem lemma35_one (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 1) (hv : v ∈ T.U 7) :
    ⁅u, v⁆ ∈ win T.U 3 5 := by
  have hA : ⁅u, v⁆ ∈ win T.U 3 6 := comm_one_seven_mem T hT hu hv
  have hT' : (T.refl 8).Normalized := Normalized.refl hT (by decide : Even (8 : ℤ))
  have hv' : v ∈ (T.refl 8).U 1 := by
    rw [refl_U]
    simpa using hv
  have hu' : u ∈ (T.refl 8).U 7 := by
    rw [refl_U]
    simpa using hu
  have hB : ⁅v, u⁆ ∈ win T.U 2 5 := by
    have h := comm_one_seven_mem (T := T.refl 8) hT' hv' hu'
    rw [win_refl] at h
    convert h using 2 <;> norm_num
  have hB' : ⁅u, v⁆ ∈ win T.U 2 5 := by
    have hinv := (win T.U 2 5).inv_mem hB
    have e : ⁅u, v⁆ = ⁅v, u⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [e]
  have hinter : ⁅u, v⁆ ∈ win T.U 3 6 ⊓ win T.U 2 5 := ⟨hA, hB'⟩
  rw [T.win_inf_win (a := 3) (b := 6) (c := 2) (d := 5) (by norm_num)] at hinter
  simpa using hinter

theorem lemma35_half (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hv : v ∈ T.U 7) (hv1 : v ≠ 1) :
    ∃ z ∈ T.U 5, ⁅u, v⁆ = T.mu 1 u * v * (T.mu 1 u)⁻¹ * z := by
  obtain ⟨hu'_eq, hnu9u'⟩ := lemma33_ii (T := T) hT hu hu1
  set m := T.mu 1 u with hm
  set u' := T.nu 1 u with hu'_def
  have hu'U : u' ∈ T.U 9 := by
    have h := T.nu_mem hu hu1
    simpa [u'] using h
  have hu'1 : u' ≠ 1 := by
    have h := T.nu_ne_one (by norm_num : 3 ≤ 8) hu hu1
    simpa [u'] using h
  have hmu9 : T.mu 9 u' = m := by
    have h := (T.mu_nu (by norm_num : 3 ≤ 8) (i := 1) hu hu1).1
    exact h
  have hnu9 : T.nu 9 u' = u := by
    have h := hnu9u'
    simpa [u'] using h
  have hnu17 : T.nu ((9 : ℤ) + (8 : ℕ)) u = u' := by
    have hper : T.nu ((9 : ℤ) + (8 : ℕ)) u = T.nu 1 u := by
      have h := T.nu_add_two_mul (by norm_num : 3 ≤ 8) (i := 1) (k := 1) u
      convert h using 2
      norm_num
    rw [hper]
  have hm_eq : m = u * u' * u := by
    have h := T.mu_eq_nu_nu (by norm_num : 3 ≤ 8) (i := 1) hu hu1
    rw [show T.nu ((1 : ℤ) + (8 : ℕ)) u' = u from by simpa [u'] using hnu9u'] at h
    simpa [m] using h
  have hm_eq2 : m = u' * u * u' := by
    have h := T.mu_eq_nu_nu (by norm_num : 3 ≤ 8) (i := 9) hu'U hu'1
    rw [hmu9, hnu9, hnu17] at h
    simpa [m] using h
  have hu'v : u' * v = v * u' :=
    (comm_odd_add_two (T := T) hT (j := 7) (by decide) hv hu'U).symm
  have ha3 : m * v * m⁻¹ ∈ T.U 3 := by
    have h := Moves.conj_mem T (T.moves_mu hu hu1) (j := 7) hv
    have e : 2 * (1 : ℤ) + (8 : ℕ) - 7 = 3 := by norm_num
    rw [e] at h
    simpa [m] using h
  have hconj : u'⁻¹ * (m * v * m⁻¹) * u' = u * v * u⁻¹ := by
    rw [hm_eq2]
    have e : u'⁻¹ * ((u' * u * u') * v * (u' * u * u')⁻¹) * u' =
        u * (u' * v * u'⁻¹) * u⁻¹ := by group
    rw [e]
    have hc : u' * v * u'⁻¹ = v := by
      calc u' * v * u'⁻¹ = v * u' * u'⁻¹ := by rw [hu'v]
        _ = v := by group
    rw [hc]
  have hc5 : T.mu 7 v * u * (T.mu 7 v)⁻¹ ∈ T.U 5 := by
    have h := Moves.conj_mem T (T.moves_mu hv hv1) (j := 1) hu
    have h2 : T.mu 7 v * u * (T.mu 7 v)⁻¹ ∈ T.U (5 + 2 * (8 : ℕ) * 1) := by
      convert h using 2
      norm_num
    rwa [U_add_two_mul T 5 1] at h2
  have hTshift : (T.shift 2).Normalized := Normalized.shift hT (by decide : Even (2 : ℤ))
  have ha_inv : (m * v * m⁻¹)⁻¹ ∈ (T.shift 2).U 1 := by
    rw [shift_U]
    have e : (1 : ℤ) + 2 = 3 := by norm_num
    rw [e]
    exact (T.U 3).inv_mem ha3
  have hu'_inv : u'⁻¹ ∈ (T.shift 2).U 7 := by
    rw [shift_U]
    have e : (7 : ℤ) + 2 = 9 := by norm_num
    rw [e]
    exact (T.U 9).inv_mem hu'U
  have hcwin : ⁅(m * v * m⁻¹)⁻¹, u'⁻¹⁆ ∈ win T.U 5 7 := by
    have h := lemma35_one (T := T.shift 2) hTshift ha_inv hu'_inv
    rw [win_shift] at h
    convert h using 2 <;> norm_num
  have hrepr : u * v * u⁻¹ = (m * v * m⁻¹) * ⁅(m * v * m⁻¹)⁻¹, u'⁻¹⁆ := by
    rw [← hconj]
    simp only [commutatorElement_def]
    group
  have hrepr2 : u * v * u⁻¹ = ⁅u, v⁆ * v := by
    simp only [commutatorElement_def]
    group
  have hmain : (m * v * m⁻¹) * ⁅(m * v * m⁻¹)⁻¹, u'⁻¹⁆ = ⁅u, v⁆ * v := by
    rw [← hrepr, hrepr2]
  have hz_eq : ⁅(m * v * m⁻¹)⁻¹, u'⁻¹⁆ * v⁻¹ = (m * v * m⁻¹)⁻¹ * ⁅u, v⁆ := by
    have h := congrArg (fun t => (m * v * m⁻¹)⁻¹ * t * v⁻¹) hmain
    simpa [mul_assoc] using h
  have hbwin : ⁅u, v⁆ ∈ win T.U 3 5 := lemma35_one (T := T) hT hu hv
  have hz1 : (m * v * m⁻¹)⁻¹ * ⁅u, v⁆ ∈ win T.U 3 5 :=
    (win T.U 3 5).mul_mem
      (T.U_le_win (a := 3) (b := 5) (k := 3) (by norm_num) (by norm_num)
        ((T.U 3).inv_mem ha3)) hbwin
  have hz2 : ⁅(m * v * m⁻¹)⁻¹, u'⁻¹⁆ * v⁻¹ ∈ win T.U 5 7 :=
    (win T.U 5 7).mul_mem hcwin
      (T.U_le_win (a := 5) (b := 7) (k := 7) (by norm_num) (by norm_num)
        ((T.U 7).inv_mem hv))
  have hinter : win T.U 3 5 ⊓ win T.U 5 7 = T.U 5 := by
    rw [T.win_inf_win (a := 3) (b := 5) (c := 5) (d := 7) (by norm_num)]
    rw [show max (3 : ℤ) 5 = 5 by norm_num, show min (5 : ℤ) 7 = 5 by norm_num, T.win_self]
  have hzmem : (m * v * m⁻¹)⁻¹ * ⁅u, v⁆ ∈ win T.U 3 5 ⊓ win T.U 5 7 := by
    refine ⟨hz1, ?_⟩
    rw [← hz_eq]
    exact hz2
  have hzU5 : (m * v * m⁻¹)⁻¹ * ⁅u, v⁆ ∈ T.U 5 := by
    rw [← hinter]
    exact hzmem
  refine ⟨(m * v * m⁻¹)⁻¹ * ⁅u, v⁆, hzU5, ?_⟩
  rw [hm]
  group

theorem lemma35_three (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hv : v ∈ T.U 7) (hv1 : v ≠ 1) :
    ⁅u, v⁆ = T.mu 1 u * v * (T.mu 1 u)⁻¹ * (T.mu 7 v * u * (T.mu 7 v)⁻¹)⁻¹ := by
  obtain ⟨z', hz'U, hz'eq⟩ := lemma35_half (T := T) hT hu hu1 hv hv1
  have hT' : (T.refl 8).Normalized := Normalized.refl hT (by decide : Even (8 : ℤ))
  have hv' : v ∈ (T.refl 8).U 1 := by
    rw [refl_U]
    simpa using hv
  have hu' : u ∈ (T.refl 8).U 7 := by
    rw [refl_U]
    simpa using hu
  obtain ⟨z'', hz''U, hz''eq⟩ := lemma35_half (T := T.refl 8) hT' hv' hv1 hu' hu1
  have hz''U' : z'' ∈ T.U 3 := by
    have h : z'' ∈ (T.refl 8).U 5 := hz''U
    rw [refl_U] at h
    simpa using h
  have hz''eq' : ⁅v, u⁆ = T.mu 7 v * u * (T.mu 7 v)⁻¹ * z'' := by
    have h := hz''eq
    rw [T.mu_refl (by norm_num : 3 ≤ 8) (8 : ℤ) (1 : ℤ) v] at h
    simpa using h
  have ha3 : T.mu 1 u * v * (T.mu 1 u)⁻¹ ∈ T.U 3 := by
    have h := Moves.conj_mem T (T.moves_mu hu hu1) (j := 7) hv
    have e : 2 * (1 : ℤ) + (8 : ℕ) - 7 = 3 := by norm_num
    rw [e] at h
    exact h
  have hc5 : T.mu 7 v * u * (T.mu 7 v)⁻¹ ∈ T.U 5 := by
    have h := Moves.conj_mem T (T.moves_mu hv hv1) (j := 1) hu
    have h2 : T.mu 7 v * u * (T.mu 7 v)⁻¹ ∈ T.U (5 + 2 * (8 : ℕ) * 1) := by
      convert h using 2
      norm_num
    rwa [U_add_two_mul T 5 1] at h2
  have hz''inv : ⁅u, v⁆ = z''⁻¹ * (T.mu 7 v * u * (T.mu 7 v)⁻¹)⁻¹ := by
    have h : ⁅u, v⁆ = ⁅v, u⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h, hz''eq']
    group
  have hcmp : T.mu 1 u * v * (T.mu 1 u)⁻¹ * z' =
      z''⁻¹ * (T.mu 7 v * u * (T.mu 7 v)⁻¹)⁻¹ := by
    rw [← hz'eq, hz''inv]
  have hsplit := T.eq_of_mul_eq_mul (a := 3) (c := 3) (b := 5)
    (by norm_num) (by norm_num) (by norm_num)
    (x := T.mu 1 u * v * (T.mu 1 u)⁻¹) (x' := z''⁻¹)
    (y := z') (y' := (T.mu 7 v * u * (T.mu 7 v)⁻¹)⁻¹)
    (by rw [T.win_self]; exact ha3)
    (by rw [T.win_self]; exact (T.U 3).inv_mem hz''U')
    (T.U_le_win (a := 4) (b := 5) (k := 5) (by norm_num) (by norm_num) hz'U)
    (T.U_le_win (a := 4) (b := 5) (k := 5) (by norm_num) (by norm_num)
      ((T.U 5).inv_mem hc5))
    hcmp
  rw [hz'eq, hsplit.2]

private theorem lemma35_i_one (hT : T.Normalized) {u : G} (hu : u ∈ T.U 1) : u * u = 1 := by
  by_cases hu1 : u = 1
  · subst hu1
    simp
  obtain ⟨v, hv, hv1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot 7)
  set m := T.mu 1 u with hm
  set u' := T.nu 1 u with hu'_def
  set c := T.mu 7 v * u * (T.mu 7 v)⁻¹ with hc_def
  have hu'U : u' ∈ T.U 9 := by
    have h := T.nu_mem hu hu1
    simpa [u'] using h
  have hu'1 : u' ≠ 1 := by
    have h := T.nu_ne_one (by norm_num : 3 ≤ 8) hu hu1
    simpa [u'] using h
  have hm_eq : m = u * u' * u := by
    have h := T.mu_eq_nu_nu (by norm_num : 3 ≤ 8) (i := 1) hu hu1
    rw [show T.nu ((1 : ℤ) + (8 : ℕ)) u' = u from by
      have h2 := (lemma33_ii (T := T) hT hu hu1).2
      simpa [u'] using h2] at h
    simpa [m] using h
  have hu'v : u' * v = v * u' :=
    (comm_odd_add_two (T := T) hT (j := 7) (by decide) hv hu'U).symm
  have ha3 : m * v * m⁻¹ ∈ T.U 3 := by
    have h := Moves.conj_mem T (T.moves_mu hu hu1) (j := 7) hv
    have e : 2 * (1 : ℤ) + (8 : ℕ) - 7 = 3 := by norm_num
    rw [e] at h
    simpa [m] using h
  have hc5 : c ∈ T.U 5 := by
    have h := Moves.conj_mem T (T.moves_mu hv hv1) (j := 1) hu
    have h2 : T.mu 7 v * u * (T.mu 7 v)⁻¹ ∈ T.U (5 + 2 * (8 : ℕ) * 1) := by
      convert h using 2
      norm_num
    rw [U_add_two_mul T 5 1] at h2
    rwa [hc_def]
  have hthree : ⁅u, v⁆ = m * v * m⁻¹ * c⁻¹ := lemma35_three (T := T) hT hu hu1 hv hv1
  have hu_inv : u⁻¹ ∈ T.U 1 := (T.U 1).inv_mem hu
  have hu1_inv : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
  have hthree2 := lemma35_three (T := T) hT hu_inv hu1_inv hv hv1
  have hm_inv : T.mu 1 u⁻¹ = m⁻¹ := by
    have h := T.mu_inv (by norm_num : 3 ≤ 8) hu hu1
    simpa [m] using h
  have hc_inv : T.mu 7 v * u⁻¹ * (T.mu 7 v)⁻¹ = c⁻¹ := by
    rw [hc_def]
    group
  have hthree2' : ⁅u⁻¹, v⁆ = m⁻¹ * v * m * c := by
    have h := hthree2
    rw [hm_inv, hc_inv] at h
    simpa using h
  have hleft : u⁻¹ * v * u = m⁻¹ * v * m * c * v := by
    have e : u⁻¹ * v * u = ⁅u⁻¹, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    rw [e, hthree2']
  have hright : u * v * u⁻¹ = m * v * m⁻¹ * c⁻¹ * v := by
    have e : u * v * u⁻¹ = ⁅u, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    rw [e, hthree]
  have hconj : m * (u⁻¹ * v * u) * m⁻¹ = u * v * u⁻¹ := by
    rw [hm_eq]
    have e : u * u' * u * (u⁻¹ * v * u) * (u * u' * u)⁻¹ =
        u * (u' * v * u'⁻¹) * u⁻¹ := by group
    rw [e]
    have hc : u' * v * u'⁻¹ = v := by
      calc u' * v * u'⁻¹ = v * u' * u'⁻¹ := by rw [hu'v]
        _ = v := by group
    rw [hc]
  have huc : u * c = c * u :=
    comm_odd_add_four (T := T) hT (j := 1) (by decide) hu hc5
  have hu'c : u' * c = c * u' :=
    (comm_odd_add_four (T := T) hT (j := 5) (by decide) hc5 hu'U).symm
  have hmc : m * c = c * m := by
    rw [hm_eq]
    calc u * u' * u * c = u * u' * (u * c) := by group
      _ = u * u' * (c * u) := by rw [huc]
      _ = u * (u' * c) * u := by group
      _ = u * (c * u') * u := by rw [hu'c]
      _ = (u * c) * u' * u := by group
      _ = (c * u) * u' * u := by rw [huc]
      _ = c * (u * u' * u) := by group
  have hleft' : m * (u⁻¹ * v * u) * m⁻¹ = v * c * (m * v * m⁻¹) := by
    rw [hleft]
    have e : m * (m⁻¹ * v * m * c * v) * m⁻¹ = v * (m * c) * v * m⁻¹ := by group
    rw [e, hmc]
    group
  have hEq : m * v * m⁻¹ * c⁻¹ * v = v * c * (m * v * m⁻¹) := by
    rw [← hright, ← hconj, hleft']
  have hav : (m * v * m⁻¹) * v = v * (m * v * m⁻¹) :=
    comm_odd_add_four (T := T) hT (j := 3) (by decide) ha3 hv
  have hac : (m * v * m⁻¹) * c = c * (m * v * m⁻¹) :=
    comm_odd_add_two (T := T) hT (j := 3) (by decide) ha3 hc5
  have hcvinv : c⁻¹ * v = v * c⁻¹ :=
    comm_odd_add_two (T := T) hT (j := 5) (by decide) ((T.U 5).inv_mem hc5) hv
  have hstep1 : m * v * m⁻¹ * c⁻¹ * v = v * (m * v * m⁻¹) * c⁻¹ := by
    calc m * v * m⁻¹ * c⁻¹ * v = (m * v * m⁻¹) * (c⁻¹ * v) := by group
      _ = (m * v * m⁻¹) * (v * c⁻¹) := by rw [hcvinv]
      _ = ((m * v * m⁻¹) * v) * c⁻¹ := by group
      _ = (v * (m * v * m⁻¹)) * c⁻¹ := by rw [hav]
      _ = v * (m * v * m⁻¹) * c⁻¹ := by group
  have hstep2 : v * c * (m * v * m⁻¹) = v * (m * v * m⁻¹) * c := by
    calc v * c * (m * v * m⁻¹) = v * (c * (m * v * m⁻¹)) := by group
      _ = v * ((m * v * m⁻¹) * c) := by rw [← hac]
      _ = v * (m * v * m⁻¹) * c := by group
  have hcancel : c⁻¹ = c := by
    have h : v * (m * v * m⁻¹) * c⁻¹ = v * (m * v * m⁻¹) * c := by
      rw [← hstep1, hEq, hstep2]
    exact mul_left_cancel h
  have hcc : c * c = 1 := by
    have h : c⁻¹ * c = 1 := inv_mul_cancel c
    rwa [hcancel] at h
  have hmm : c * c = T.mu 7 v * (u * u) * (T.mu 7 v)⁻¹ := by
    rw [hc_def]
    group
  have hconj1 : T.mu 7 v * (u * u) * (T.mu 7 v)⁻¹ = 1 := by
    rw [← hmm]
    exact hcc
  have h := congrArg (fun t => (T.mu 7 v)⁻¹ * t * (T.mu 7 v)) hconj1
  simpa [mul_assoc] using h

theorem lemma35_i (hT : T.Normalized) {j : ℤ} (hj : Odd j) {u : G} (hu : u ∈ T.U j) :
    u * u = 1 := by
  obtain ⟨k, hk⟩ := hj
  have hT' : (T.shift (j - 1)).Normalized :=
    Normalized.shift hT (show Even (j - 1) by rw [hk]; exact ⟨k, by ring⟩)
  have hu' : u ∈ (T.shift (j - 1)).U 1 := by
    rw [shift_U]
    convert hu using 1
    ring_nf
  exact lemma35_i_one (T := T.shift (j - 1)) hT' hu'

theorem lemma35_ii (hT : T.Normalized) {j : ℤ} (hj : Odd j) {u : G} (hu : u ∈ T.U j)
    (hu1 : u ≠ 1) : T.mu j u * T.mu j u = 1 := by
  have hj' : Odd (j + 8) := by
    obtain ⟨k, hk⟩ := hj
    exact ⟨k + 4, by push_cast at hk ⊢; omega⟩
  set m := T.mu j u with hm
  set u' := T.nu j u with hu'_def
  have hu'U : u' ∈ T.U (j + 8) := by
    have h := T.nu_mem hu hu1
    simpa [u'] using h
  have hnu : T.nu (j + 8) u' = u := by
    have h := (nu_odd (T := T) hT hj hu hu1).2
    simpa [u'] using h
  have hm_eq : m = u * u' * u := by
    have h := T.mu_eq_nu_nu (by norm_num : 3 ≤ 8) hu hu1
    have hnu' : T.nu (j + (8 : ℕ)) (T.nu j u) = u := by
      simpa [u'] using hnu
    rw [hnu'] at h
    simpa [m, u'] using h
  have hu2 : u * u = 1 := lemma35_i (T := T) hT hj hu
  have hu'2 : u' * u' = 1 := lemma35_i (T := T) hT hj' hu'U
  calc m * m = u * u' * u * (u * u' * u) := by rw [hm_eq]
    _ = u * u' * (u * u) * u' * u := by group
    _ = u * u' * u' * u := by rw [hu2, mul_one]
    _ = u * (u' * u') * u := by group
    _ = u * u := by rw [hu'2, mul_one]
    _ = 1 := hu2

theorem lemma35_iii (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hv : v ∈ T.U 7) (hv1 : v ≠ 1) :
    ⁅u, v⁆ = T.mu 1 u * v * (T.mu 1 u)⁻¹ * (T.mu 7 v * u * (T.mu 7 v)⁻¹) := by
  have hu2 : u * u = 1 := lemma35_i (T := T) hT (by decide : Odd (1 : ℤ)) hu
  have hcc : (T.mu 7 v * u * (T.mu 7 v)⁻¹) * (T.mu 7 v * u * (T.mu 7 v)⁻¹) = 1 := by
    have e : (T.mu 7 v * u * (T.mu 7 v)⁻¹) * (T.mu 7 v * u * (T.mu 7 v)⁻¹) =
        T.mu 7 v * (u * u) * (T.mu 7 v)⁻¹ := by group
    rw [e, hu2]
    group
  have hcinv : (T.mu 7 v * u * (T.mu 7 v)⁻¹)⁻¹ = T.mu 7 v * u * (T.mu 7 v)⁻¹ := by
    calc (T.mu 7 v * u * (T.mu 7 v)⁻¹)⁻¹
        = (T.mu 7 v * u * (T.mu 7 v)⁻¹)⁻¹ * ((T.mu 7 v * u * (T.mu 7 v)⁻¹) *
            (T.mu 7 v * u * (T.mu 7 v)⁻¹)) := by rw [hcc, mul_one]
      _ = T.mu 7 v * u * (T.mu 7 v)⁻¹ := by group
  rw [lemma35_three (T := T) hT hu hu1 hv hv1, hcinv]

theorem Yc_sup_subset :
    ((T.Yc ⊔ T.Uprime 4 : Subgroup G) : Set G) ⊆
      (T.Uprime 2 : Set G) * (win T.U 3 5 : Set G) * (T.Uprime 6 : Set G) := by
  have hYcwin : (T.Yc : Set G) ⊆ (win T.U 2 6 : Set G) := by
    intro y hy
    obtain ⟨ab, hab, c, hc, rfl⟩ := Set.mem_mul.1 (T.Yc_subset hy)
    obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_mul.1 hab
    refine (win T.U 2 6).mul_mem ((win T.U 2 6).mul_mem ?_ ?_)
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc))
    · exact T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 ha)
    · exact T.win_mono (by norm_num) (by norm_num) hw
  have hcent : T.Uprime 4 ≤ Subgroup.centralizer (T.Yc : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (T.Uprime_comm_win (j := 4) (a := 2) (b := 6) (by norm_num) (by norm_num)
      hd (hYcwin hy)).symm
  have hnorm : T.Uprime 4 ≤ Subgroup.normalizer (T.Yc : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (T.Yc : Set G))
  rw [Subgroup.coe_mul_of_right_le_normalizer_left T.Yc (T.Uprime 4) hnorm]
  intro x hx
  obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hx
  obtain ⟨ab, hab, c, hc, rfl⟩ := Set.mem_mul.1 (T.Yc_subset ha)
  obtain ⟨a1, ha1, w, hw, rfl⟩ := Set.mem_mul.1 hab
  have hdc : c * d = d * c := by
    have hmem : c ∈ T.Yc := T.Uprime_six_le_Yc hc
    exact Subgroup.mem_centralizer_iff.1 (hcent hd) c hmem
  have hdw : d * w = w * d :=
    T.Uprime_comm_win (j := 4) (a := 3) (b := 5) (by norm_num) (by norm_num) hd hw
  have hwd : w * d ∈ win T.U 3 5 := by
    have hd4 : d ∈ win T.U 3 5 :=
      T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hd)
    have h : d * w ∈ win T.U 3 5 := (win T.U 3 5).mul_mem hd4 hw
    rwa [hdw] at h
  refine Set.mem_mul.2 ⟨a1 * (w * d), Set.mem_mul.2 ⟨a1, ha1, w * d, hwd, rfl⟩,
    c, hc, ?_⟩
  calc a1 * (w * d) * c = a1 * w * (d * c) := by group
    _ = a1 * w * (c * d) := by rw [hdc.symm]
    _ = a1 * w * c * d := by group

theorem le_normalizer_Yc_sup :
    T.U 0 ≤ Subgroup.normalizer ((T.Yc ⊔ T.Uprime 4 : Subgroup G) : Set G) ∧
      T.U 8 ≤ Subgroup.normalizer ((T.Yc ⊔ T.Uprime 4 : Subgroup G) : Set G) := by
  have hYc := T.le_normalizer_Yc
  have hcent0 : T.U 0 ≤ Subgroup.centralizer (T.Uprime 4 : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact T.Uprime_comm_win (j := 4) (a := 0) (b := 8) (by norm_num) (by norm_num)
      hx (T.U_le_win (by norm_num) (by norm_num) hu)
  have hcent8 : T.U 8 ≤ Subgroup.centralizer (T.Uprime 4 : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact T.Uprime_comm_win (j := 4) (a := 0) (b := 8) (by norm_num) (by norm_num)
      hx (T.U_le_win (by norm_num) (by norm_num) hu)
  have hN0 : T.U 0 ≤ Subgroup.normalizer (T.Uprime 4 : Set G) :=
    hcent0.trans (Subgroup.centralizer_le_normalizer (T.Uprime 4 : Set G))
  have hN8 : T.U 8 ≤ Subgroup.normalizer (T.Uprime 4 : Set G) :=
    hcent8.trans (Subgroup.centralizer_le_normalizer (T.Uprime 4 : Set G))
  exact ⟨CFSG.LieType.Steinberg.le_normalizer_sup hYc.1 hN0,
    CFSG.LieType.Steinberg.le_normalizer_sup hYc.2 hN8⟩

theorem lemma38_one {v x : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1) (hx : x ∈ T.Uprime 2)
    (hx1 : x ≠ 1) :
    ∃ e ∈ T.U 5, ⁅v, x⁆ = T.mu 2 x * v⁻¹ * (T.mu 2 x)⁻¹ * e * (T.mu 8 v * x * (T.mu 8 v)⁻¹) := by
  set mx := T.mu 2 x
  set q := T.mu 8 v * x * (T.mu 8 v)⁻¹
  have hu0' : T.nu' 8 v ∈ T.U (8 + 8) := T.nu'_mem (i := 8) (T.Uprime_le 8 hv) hv1
  have hU16 : T.U 16 = T.U 0 := by simpa using T.periodic 0
  have hu0 : T.nu' 8 v ∈ T.U 0 := by
    rw [← hU16]
    exact hu0'
  have hu01 : T.nu' 8 v ≠ 1 := T.nu'_ne_one (n := 8) (i := 8) (by norm_num) (T.Uprime_le 8 hv) hv1
  have hn16 : T.nu 16 (T.nu' 8 v) = T.nu 0 (T.nu' 8 v) := by
    simpa using T.nu_add_two_mul (n := 8) (by norm_num) (0 : ℤ) (1 : ℤ) (T.nu' 8 v)
  have hν0 : T.nu 0 (T.nu' 8 v) = v := by
    rw [← hn16]
    exact (T.mu_nu' (n := 8) (i := 8) (by norm_num) (T.Uprime_le 8 hv) hv1).2
  have hm16 : T.mu 16 (T.nu' 8 v) = T.mu 0 (T.nu' 8 v) := by
    simpa using T.mu_add_two_mul (n := 8) (by norm_num) (0 : ℤ) (1 : ℤ) (T.nu' 8 v)
  have hm0 : T.mu 0 (T.nu' 8 v) = T.mu 8 v := by
    rw [← hm16]
    exact (T.mu_nu' (n := 8) (i := 8) (by norm_num) (T.Uprime_le 8 hv) hv1).1
  have hxu0 : x * T.nu' 8 v = T.nu' 8 v * x := by
    have hwin : T.nu' 8 v ∈ win T.U 0 0 := by simpa [T.win_self] using hu0
    exact T.Uprime_comm_win (j := 2) (a := 0) (b := 0) (by norm_num) (by norm_num) hx hwin
  have hcomm1 : T.nu' 8 v * x⁻¹ = x⁻¹ * T.nu' 8 v := by
    calc T.nu' 8 v * x⁻¹ = x⁻¹ * (x * T.nu' 8 v) * x⁻¹ := by group
      _ = x⁻¹ * (T.nu' 8 v * x) * x⁻¹ := by rw [hxu0]
      _ = x⁻¹ * T.nu' 8 v := by group
  obtain ⟨y, hy, hyeq⟩ := T.lemma212_iii (n := 8) (by norm_num) (i := 0) (j := 2)
    (by norm_num) (by norm_num) hu0 hu01 ((T.U 2).inv_mem (T.Uprime_le 2 hx)) hcomm1
  have hq22 : T.mu 8 v * x * (T.mu 8 v)⁻¹ ∈ T.U 22 := by
    have h := Moves.conj_mem T (T.moves_mu (n := 8) (T.Uprime_le 8 hv) hv1) (j := 2)
      (T.Uprime_le 2 hx)
    simpa [q] using h
  have hper : T.U 22 = T.U 6 := by
    simpa [show (22 : ℤ) = 6 + 2 * (8 : ℤ) * 1 by norm_num] using (U_add_two_mul T 6 1)
  have hqmem : q ∈ T.U 6 := by
    rw [← hper]
    exact hq22
  have hqwin : q ∈ win T.U 6 6 := by simpa [T.win_self] using hqmem
  have hqnorm : q ∈ Subgroup.normalizer (win T.U 3 5 : Set G) :=
    (T.le_normalizer_win (a := 3) (b := 5) (by norm_num)).2 hqmem
  have hy1 : q * y⁻¹ * q⁻¹ ∈ win T.U 3 5 :=
    (Subgroup.mem_normalizer_iff.mp hqnorm y⁻¹).1 ((win T.U 3 5).inv_mem hy)
  have hA : ⁅v, x⁆ = (q * y⁻¹ * q⁻¹) * q := by
    have hyeq' : ⁅x, v⁆ = y * (T.mu 8 v * x⁻¹ * (T.mu 8 v)⁻¹) := by
      have h := hyeq
      rw [hν0, hm0] at h
      simpa [commutatorElement_def] using h
    have h1 : ⁅x, v⁆ = y * q⁻¹ := by
      rw [hyeq']
      simp only [q]
      group
    calc ⁅v, x⁆ = ⁅x, v⁆⁻¹ := by simp only [commutatorElement_def]; group
      _ = (y * q⁻¹)⁻¹ := by rw [h1]
      _ = q * y⁻¹ := by group
      _ = (q * y⁻¹ * q⁻¹) * q := by group
  have hu1 : T.nu' 2 x ∈ T.U 10 := T.nu'_mem (i := 2) (T.Uprime_le 2 hx) hx1
  have hu11 : T.nu' 2 x ≠ 1 := T.nu'_ne_one (n := 8) (i := 2) (by norm_num) (T.Uprime_le 2 hx) hx1
  have hν10 : T.nu 10 (T.nu' 2 x) = x :=
    (T.mu_nu' (n := 8) (i := 2) (by norm_num) (T.Uprime_le 2 hx) hx1).2
  have hm10 : T.mu 10 (T.nu' 2 x) = mx :=
    (T.mu_nu' (n := 8) (i := 2) (by norm_num) (T.Uprime_le 2 hx) hx1).1
  have hvu1 : v * T.nu' 2 x = T.nu' 2 x * v := by
    have hwin : T.nu' 2 x ∈ win T.U 10 10 := by simpa [T.win_self] using hu1
    exact T.Uprime_comm_win (j := 8) (a := 10) (b := 10) (by norm_num) (by norm_num) hv hwin
  have hcomm2 : T.nu' 2 x * v⁻¹ = v⁻¹ * T.nu' 2 x := by
    calc T.nu' 2 x * v⁻¹ = v⁻¹ * (v * T.nu' 2 x) * v⁻¹ := by group
      _ = v⁻¹ * (T.nu' 2 x * v) * v⁻¹ := by rw [hvu1]
      _ = v⁻¹ * T.nu' 2 x := by group
  obtain ⟨y2, hy2, hy2eq⟩ := T.lemma212_iii' (n := 8) (by norm_num) (i := 10) (j := 8)
    (by norm_num) (by norm_num) hu1 hu11 ((T.U 8).inv_mem (T.Uprime_le 8 hv)) hcomm2
  have hz : mx * v⁻¹ * mx⁻¹ ∈ T.Uprime 4 := by
    have h := T.mu_conj_mem_Uprime (i := 2) (j := 8) (u := x) (x := v)
      (T.Uprime_le 2 hx) hx1 hv
    have h4 : T.mu 2 x * v * (T.mu 2 x)⁻¹ ∈ T.Uprime 4 := h
    simpa [mx, mul_assoc] using (T.Uprime 4).inv_mem h4
  have hB : ⁅v, x⁆ = y2 * (mx * v⁻¹ * mx⁻¹) := by
    have hy2eq' : ⁅v, x⁆ = y2 * (mx * v⁻¹ * mx⁻¹) := by
      have h := hy2eq
      rw [hν10, hm10] at h
      simpa [commutatorElement_def] using h
    exact hy2eq'
  have hwin1 : ⁅v, x⁆ ∈ win T.U 3 6 := by
    rw [hA]
    exact (win T.U 3 6).mul_mem
      (T.win_mono (by norm_num) (by norm_num) hy1)
      (T.U_le_win (by norm_num) (by norm_num) hqmem)
  have hwin2 : ⁅v, x⁆ ∈ win T.U 4 7 := by
    rw [hB]
    exact (win T.U 4 7).mul_mem
      (T.win_mono (by norm_num) (by norm_num) hy2)
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hz))
  have hwin : ⁅v, x⁆ ∈ win T.U 4 6 := by
    have h : ⁅v, x⁆ ∈ win T.U 3 6 ⊓ win T.U 4 7 := ⟨hwin1, hwin2⟩
    rw [T.win_inf_win (a := 3) (b := 6) (c := 4) (d := 7) (by norm_num)] at h
    simpa using h
  have hy2' : y2 ∈ win T.U 4 6 := by
    have hy2eq' : y2 = ⁅v, x⁆ * (mx * v⁻¹ * mx⁻¹)⁻¹ := by
      rw [hB]
      group
    rw [hy2eq']
    exact (win T.U 4 6).mul_mem hwin
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 ((T.Uprime 4).inv_mem hz)))
  have hy256 : y2 ∈ win T.U 5 6 := by
    have h : y2 ∈ win T.U 5 7 ⊓ win T.U 4 6 := ⟨hy2, hy2'⟩
    rw [T.win_inf_win (a := 5) (b := 7) (c := 4) (d := 6) (by norm_num)] at h
    simpa using h
  obtain ⟨e, he', c, hc', hy2e⟩ := T.exists_mul_of_mem_win (a := 5) (c := 5) (b := 6)
    (by norm_num) (by norm_num) (by norm_num) hy256
  have he : e ∈ T.U 5 := by simpa [T.win_self] using he'
  have hc : c ∈ T.U 6 := by simpa [T.win_self] using hc'
  have hcz : c * (mx * v⁻¹ * mx⁻¹) = (mx * v⁻¹ * mx⁻¹) * c := by
    have hwin : c ∈ win T.U 6 6 := by simpa [T.win_self] using hc
    exact (T.Uprime_comm_win (j := 4) (a := 6) (b := 6) (by norm_num) (by norm_num)
      hz hwin).symm
  have hcomp : (e * (mx * v⁻¹ * mx⁻¹)) * c = (q * y⁻¹ * q⁻¹) * q := by
    calc (e * (mx * v⁻¹ * mx⁻¹)) * c = e * ((mx * v⁻¹ * mx⁻¹) * c) := by group
      _ = e * (c * (mx * v⁻¹ * mx⁻¹)) := by rw [hcz.symm]
      _ = (e * c) * (mx * v⁻¹ * mx⁻¹) := by group
      _ = y2 * (mx * v⁻¹ * mx⁻¹) := by rw [← hy2e]
      _ = ⁅v, x⁆ := hB.symm
      _ = (q * y⁻¹ * q⁻¹) * q := hA
  have hez : e * (mx * v⁻¹ * mx⁻¹) ∈ win T.U 3 5 :=
    (win T.U 3 5).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) he)
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hz))
  have hc6 : c ∈ win T.U 6 6 := by simpa [T.win_self] using hc
  have hq6 : q ∈ win T.U 6 6 := hqwin
  have hsplit := T.eq_of_mul_eq_mul (a := 3) (c := 5) (b := 6) (by norm_num) (by norm_num)
    (by norm_num) hez hy1 hc6 hq6 hcomp
  refine ⟨e, he, ?_⟩
  have hze : e * (mx * v⁻¹ * mx⁻¹) = (mx * v⁻¹ * mx⁻¹) * e :=
    (T.Uprime_comm_win (j := 4) (a := 5) (b := 5) (x := mx * v⁻¹ * mx⁻¹) (y := e)
      (by norm_num) (by norm_num) hz (by simpa [T.win_self] using he)).symm
  have hfinal : ⁅v, x⁆ = ((mx * v⁻¹ * mx⁻¹) * e) * q := by
    calc ⁅v, x⁆ = (q * y⁻¹ * q⁻¹) * q := hA
      _ = (e * (mx * v⁻¹ * mx⁻¹)) * q := by rw [hsplit.1]
      _ = ((mx * v⁻¹ * mx⁻¹) * e) * q := by rw [hze]
  simpa [q] using hfinal

theorem lemma38_i {v x : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1) (hx : x ∈ T.Uprime 2)
    (h : ⁅v, x⁆ ∈ (T.Uprime 4 : Set G) * (T.Uprime 6 : Set G)) : x = 1 := by
  obtain ⟨d, hd, c, hc, hdc⟩ := Set.mem_mul.1 h
  have hcd : c * d = d * c := by
    have hwin : c ∈ win T.U 6 6 := by
      simpa [T.win_self] using T.Uprime_le 6 hc
    exact (T.Uprime_comm_win (j := 4) (a := 6) (b := 6) (by norm_num) (by norm_num)
      hd hwin).symm
  have hv0 : v ∈ (T.refl 8).Uprime 0 := by
    rw [T.Uprime_refl]
    norm_num
    exact hv
  have hx0 : x ∈ (T.refl 8).U 6 := by
    rw [refl_U]
    norm_num
    exact T.Uprime_le 2 hx
  have ha0 : c ∈ (T.refl 8).Uprime 2 := by
    rw [T.Uprime_refl]
    norm_num
    exact hc
  have hb0 : d ∈ (T.refl 8).Uprime 4 := by
    rw [T.Uprime_refl]
    norm_num
    exact hd
  rcases TitsSystem.lemma37 (T := T.refl 8) hv0 hx0 ha0 hb0 (hdc.symm.trans hcd.symm) with h1 | h1
  · exact h1
  · exact absurd h1 hv1

theorem lemma38_i_inj {v x x' d d' e c c' : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1)
    (hx : x ∈ T.Uprime 2) (hx' : x' ∈ T.Uprime 2) (hd : d ∈ T.Uprime 4) (hd' : d' ∈ T.Uprime 4)
    (he : e ∈ T.U 5) (hc : c ∈ T.Uprime 6) (hc' : c' ∈ T.Uprime 6)
    (h : ⁅v, x⁆ = d * e * c) (h' : ⁅v, x'⁆ = d' * e * c') : x = x' := by
  have hg : x'⁻¹ * x ∈ T.Uprime 2 :=
    (T.Uprime 2).mul_mem ((T.Uprime 2).inv_mem hx') hx
  have hwin : ⁅v, x⁆ ∈ win T.U 4 6 := by
    rw [h]
    exact (win T.U 4 6).mul_mem ((win T.U 4 6).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hd))
      (T.U_le_win (by norm_num) (by norm_num) he))
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc))
  have hwin' : ⁅v, x'⁆ ∈ win T.U 4 6 := by
    rw [h']
    exact (win T.U 4 6).mul_mem ((win T.U 4 6).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hd'))
      (T.U_le_win (by norm_num) (by norm_num) he))
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc'))
  have hcx : x' * ⁅v, x⁆ = ⁅v, x⁆ * x' :=
    T.Uprime_comm_win (j := 2) (a := 4) (b := 6) (by norm_num) (by norm_num) hx' hwin
  have hcx' : x' * ⁅v, x'⁆ = ⁅v, x'⁆ * x' :=
    T.Uprime_comm_win (j := 2) (a := 4) (b := 6) (by norm_num) (by norm_num) hx' hwin'
  have hinv : ⁅v, x'⁻¹⁆ = ⁅v, x'⁆⁻¹ := by
    have h1 : v * x' * v⁻¹ = ⁅v, x'⁆ * x' := by
      simp only [commutatorElement_def]
      group
    have h2 : v * x'⁻¹ * v⁻¹ = x'⁻¹ * ⁅v, x'⁆⁻¹ := by
      have := congrArg Inv.inv h1
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
    have h3 : x'⁻¹ * ⁅v, x'⁆⁻¹ = ⁅v, x'⁆⁻¹ * x'⁻¹ := by
      have := congrArg Inv.inv hcx'
      simpa only [mul_inv_rev, inv_inv] using this.symm
    simp only [commutatorElement_def]
    rw [h2, h3]
    group
  have hxconj : x'⁻¹ * ⁅v, x⁆ * x' = ⁅v, x⁆ := by
    calc x'⁻¹ * ⁅v, x⁆ * x' = x'⁻¹ * (⁅v, x⁆ * x') := by group
      _ = x'⁻¹ * (x' * ⁅v, x⁆) := by rw [← hcx]
      _ = ⁅v, x⁆ := by group
  have hvg : ⁅v, x'⁻¹ * x⁆ = ⁅v, x'⁆⁻¹ * ⁅v, x⁆ := by
    rw [commutatorElement_def]
    calc v * (x'⁻¹ * x) * v⁻¹ * (x'⁻¹ * x)⁻¹
        = ⁅v, x'⁻¹⁆ * (x'⁻¹ * ⁅v, x⁆ * x') := by
          simp only [commutatorElement_def]
          group
      _ = ⁅v, x'⁆⁻¹ * ⁅v, x⁆ := by rw [hinv, hxconj]
  have hcen4 : T.Uprime 4 ≤ Subgroup.centralizer (win T.U 3 6 : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (T.Uprime_comm_win (j := 4) (a := 3) (b := 6) (by norm_num) (by norm_num)
      ha hb).symm
  have hdd' : d'⁻¹ * d ∈ T.Uprime 4 := (T.Uprime 4).mul_mem ((T.Uprime 4).inv_mem hd') hd
  have hew : e ∈ win T.U 3 6 := T.U_le_win (by norm_num) (by norm_num) he
  have hc'w : c' ∈ win T.U 3 6 :=
    T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc')
  have hcw : c ∈ win T.U 3 6 :=
    T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc)
  have he_comm : e * (d'⁻¹ * d) = (d'⁻¹ * d) * e :=
    Subgroup.mem_centralizer_iff.1 (hcen4 hdd') e hew
  have hc'_comm : c' * (d'⁻¹ * d) = (d'⁻¹ * d) * c' :=
    Subgroup.mem_centralizer_iff.1 (hcen4 hdd') c' hc'w
  have hc_comm : c * (d'⁻¹ * d) = (d'⁻¹ * d) * c :=
    Subgroup.mem_centralizer_iff.1 (hcen4 hdd') c hcw
  have hmem : ⁅v, x'⁻¹ * x⁆ ∈ (T.Uprime 4 : Set G) * (T.Uprime 6 : Set G) := by
    rw [hvg]
    have hx'inv : ⁅v, x'⁆⁻¹ = c'⁻¹ * e⁻¹ * d'⁻¹ := by
      rw [h']
      group
    rw [hx'inv, h]
    have hcc' : c'⁻¹ * c ∈ T.Uprime 6 := (T.Uprime 6).mul_mem ((T.Uprime 6).inv_mem hc') hc
    refine Set.mem_mul.2 ⟨d'⁻¹ * d, hdd', c'⁻¹ * c, hcc', ?_⟩
    have he_mid : e⁻¹ * (d'⁻¹ * d) * e = d'⁻¹ * d := by
      calc e⁻¹ * (d'⁻¹ * d) * e = e⁻¹ * ((d'⁻¹ * d) * e) := by group
        _ = e⁻¹ * (e * (d'⁻¹ * d)) := by rw [← he_comm]
        _ = d'⁻¹ * d := by group
    have hc'_mid : c'⁻¹ * (d'⁻¹ * d) = (d'⁻¹ * d) * c'⁻¹ := by
      calc c'⁻¹ * (d'⁻¹ * d) = c'⁻¹ * ((d'⁻¹ * d) * c') * c'⁻¹ := by group
        _ = c'⁻¹ * (c' * (d'⁻¹ * d)) * c'⁻¹ := by rw [← hc'_comm]
        _ = (d'⁻¹ * d) * c'⁻¹ := by group
    calc (d'⁻¹ * d) * (c'⁻¹ * c)
        = (d'⁻¹ * d) * c'⁻¹ * c := by group
      _ = c'⁻¹ * (d'⁻¹ * d) * c := by rw [← hc'_mid]
      _ = c'⁻¹ * (e⁻¹ * (d'⁻¹ * d) * e) * c := by
          rw [he_mid]
      _ = c'⁻¹ * e⁻¹ * d'⁻¹ * (d * e * c) := by group
  have h : x'⁻¹ * x = 1 := T.lemma38_i hv hv1 hg hmem
  exact (inv_mul_eq_one.mp h).symm

theorem lemma38_mem (hT : T.Normalized) {v u : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1)
    (hu : u ∈ T.U 3) (hu1 : u ≠ 1) :
    (T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v ∈ T.Uprime 2 ∧
      (T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v ≠ 1 := by
  obtain ⟨hmem6, hform⟩ := T.comm_odd_Uprime (hT := hT) (j := 3)
    (show Odd (3 : ℤ) from ⟨1, by norm_num⟩) hu hv
  have hne6 : ⁅u, v⁆ ≠ 1 := by
    intro h1
    have hconj : (1 : G) = T.mu 3 u * v * (T.mu 3 u)⁻¹ := by
      rw [← hform hu1, h1]
    have hv1' : v = 1 := by
      calc v = (T.mu 3 u)⁻¹ * (T.mu 3 u * v * (T.mu 3 u)⁻¹) * T.mu 3 u := by group
        _ = (T.mu 3 u)⁻¹ * (1 : G) * T.mu 3 u := by rw [← hconj]
        _ = 1 := by group
    exact hv1 hv1'
  have hmoves : T.Moves (T.mu 8 v)⁻¹ (fun j => 24 - j) :=
    Moves.inv_refl T (T.moves_mu (n := 8) (T.Uprime_le 8 hv) hv1)
  have hmem18 : (T.mu 8 v)⁻¹ * ⁅u, v⁆ * (T.mu 8 v)⁻¹⁻¹ ∈ T.Uprime 18 := by
    have h := Moves.conj_mem_Uprime_refl T hmoves hmem6
    simpa using h
  have hU : T.Uprime (18 : ℤ) = T.Uprime 2 := by
    rw [show (18 : ℤ) = 2 + 16 * 1 by norm_num, T.Uprime_add_two_mul 2 1]
  refine ⟨?_, ?_⟩
  · rw [hU] at hmem18
    simpa using hmem18
  · intro h1
    apply hne6
    calc ⁅u, v⁆ = T.mu 8 v * ((T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v) * (T.mu 8 v)⁻¹ := by group
      _ = T.mu 8 v * (1 : G) * (T.mu 8 v)⁻¹ := by rw [h1]
      _ = 1 := by group

private theorem lemma38_ii_iii_aux (hT : T.Normalized) {v u u' : G}
    (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1) (hu : u ∈ T.U 3) (hu1 : u ≠ 1)
    (hu' : u' = (T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v) :
    (⁅v, u'⁆ = T.mu 2 u' * v⁻¹ * (T.mu 2 u')⁻¹ * (T.mu 8 v * u * (T.mu 8 v)⁻¹) *
      (T.mu 8 v * u' * (T.mu 8 v)⁻¹)) ∧
    (⁅(T.nu 8 v)⁻¹, T.mu 8 v * u * (T.mu 8 v)⁻¹⁆ =
      u' * u * (T.mu 2 u' * v⁻¹ * (T.mu 2 u')⁻¹)) := by
  set m := T.mu 8 v
  set m' := T.mu 2 u'
  set vp := T.nu' 8 v with hvp
  set vpp := (T.nu 8 v)⁻¹ with hvpp
  have hm : m = vpp⁻¹ * v * vp := by
    have h1 : vpp⁻¹ = T.nu 8 v := by simp [vpp]
    rw [show m = T.mu 8 v from rfl, h1]
    rfl
  have hu'2 : u' ∈ T.Uprime 2 := by
    rw [hu']
    exact (T.lemma38_mem hT hv hv1 hu hu1).1
  have hu'1 : u' ≠ 1 := by
    rw [hu']
    exact (T.lemma38_mem hT hv hv1 hu hu1).2
  have hvpp0 : vpp ∈ T.U 0 := by
    have hU : T.U ((8 : ℤ) + ↑(8 : ℕ)) = T.U 0 := by simpa using (U_add_two_mul T 0 1)
    have h : T.nu 8 v ∈ T.U 0 := by
      have := T.nu_mem (i := 8) (T.Uprime_le 8 hv) hv1
      rwa [hU] at this
    simpa [vpp] using (T.U 0).inv_mem h
  have hvp0 : vp ∈ T.U 0 := by
    have h := T.nu'_mem (i := 8) (T.Uprime_le 8 hv) hv1
    have hU : T.U ((8 : ℤ) + ↑(8 : ℕ)) = T.U 0 := by simpa using (U_add_two_mul T 0 1)
    rwa [hU] at h
  have hv8 : v ∈ T.U 8 := T.Uprime_le 8 hv
  set W : Subgroup G := T.Yc ⊔ T.Uprime 4
  have hN0 : T.U 0 ≤ Subgroup.normalizer (W : Set G) := T.le_normalizer_Yc_sup.1
  have hN8 : T.U 8 ≤ Subgroup.normalizer (W : Set G) := T.le_normalizer_Yc_sup.2
  have hu'2W : u' ∈ W := Subgroup.mem_sup_left (T.Uprime_two_le_Yc hu'2)
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := by
    have h1 : vpp⁻¹ ∈ Subgroup.normalizer (W : Set G) := hN0 ((T.U 0).inv_mem hvpp0)
    have h2 : v ∈ Subgroup.normalizer (W : Set G) := hN8 hv8
    have h3 : vp ∈ Subgroup.normalizer (W : Set G) := hN0 hvp0
    rw [hm]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have hm'N : m⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normalizer (W : Set G)).inv_mem hmN
  obtain ⟨e, he, hve⟩ := T.lemma38_one hv hv1 hu'2 hu'1
  have hA' : m' * v⁻¹ * m'⁻¹ ∈ T.Uprime 4 := by
    have h := T.mu_conj_mem_Uprime (i := 2) (j := 8) (u := u') (x := v)
      (T.Uprime_le 2 hu'2) hu'1 hv
    have h4 : T.mu 2 u' * v * (T.mu 2 u')⁻¹ ∈ T.Uprime 4 := h
    simpa [m', mul_assoc] using (T.Uprime 4).inv_mem h4
  have hmu'6 : m * u' * m⁻¹ ∈ T.Uprime 6 := by
    have h := T.mu_conj_mem_Uprime (i := 8) (j := 2) (u := v) (x := u')
      (T.Uprime_le 8 hv) hv1 hu'2
    have h22 : T.mu 8 v * u' * (T.mu 8 v)⁻¹ ∈ T.Uprime 22 := by simpa using h
    have hU22 : T.Uprime (22 : ℤ) = T.Uprime 6 := by
      simpa using (T.Uprime_add_two_mul 6 1)
    rw [hU22] at h22
    simpa [m] using h22
  have hve' : ⁅v, u'⁆ = m' * v⁻¹ * m'⁻¹ * e * (m * u' * m⁻¹) := hve
  have hveW : ⁅v, u'⁆ ∈ W := by
    have hvu' : v * u' * v⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hN8 hv8) u').1 hu'2W
    have : (v * u' * v⁻¹) * u'⁻¹ ∈ W := W.mul_mem hvu' (W.inv_mem hu'2W)
    simpa only [commutatorElement_def] using this
  have heW : e ∈ W := by
    have h1 : (m' * v⁻¹ * m'⁻¹)⁻¹ ∈ W := W.inv_mem (Subgroup.mem_sup_right hA')
    have h2 : (m * u' * m⁻¹)⁻¹ ∈ W :=
      W.inv_mem (Subgroup.mem_sup_left (T.Uprime_six_le_Yc hmu'6))
    have h3 : (m' * v⁻¹ * m'⁻¹)⁻¹ * ⁅v, u'⁆ * (m * u' * m⁻¹)⁻¹ ∈ W :=
      W.mul_mem (W.mul_mem h1 hveW) h2
    have heq : e = (m' * v⁻¹ * m'⁻¹)⁻¹ * ⁅v, u'⁆ * (m * u' * m⁻¹)⁻¹ := by
      rw [hve']
      group
    rwa [heq]
  set y := m⁻¹ * e * m
  have hy3 : y ∈ T.U 3 := by
    have hmm : T.Moves m⁻¹ (fun j => 2 * (8 : ℤ) + 8 - j) :=
      Moves.inv_refl T (T.moves_mu (n := 8) (T.Uprime_le 8 hv) hv1)
    have hmem19 : m⁻¹ * e * (m⁻¹)⁻¹ ∈ T.U 19 := by
      have h := Moves.conj_mem T hmm he
      simpa using h
    have hU19 : T.U (19 : ℤ) = T.U 3 := by
      simpa using (U_add_two_mul T 3 1)
    rw [hU19] at hmem19
    simpa [y] using hmem19
  have hyW : y ∈ W := by
    have h := (Subgroup.mem_normalizer_iff.mp hm'N e).1 heW
    simpa [y] using h
  have hzW : ⁅vp, y⁆ ∈ W := by
    have hvy : vp * y * vp⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hN0 hvp0) y).1 hyW
    have : (vp * y * vp⁻¹) * y⁻¹ ∈ W := W.mul_mem hvy (W.inv_mem hyW)
    simpa only [commutatorElement_def] using this
  have hz12 : ⁅vp, y⁆ ∈ win T.U 1 2 := by
    have h := T.comm (i := 0) (j := 3) (by norm_num) (by norm_num) vp hvp0 y hy3
    have h' : vp * y * vp⁻¹ * y⁻¹ ∈ win T.U 1 2 := by
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := hk
      exact T.U_le_win (by omega) (by omega)
    simpa only [commutatorElement_def] using h'
  set z := ⁅vp, y⁆
  have hz2 : z ∈ T.Uprime 2 := by
    obtain ⟨ab, hab, cc, hcc, hzabc⟩ := Set.mem_mul.1 (T.Yc_sup_subset hzW)
    obtain ⟨a, ha, w, hw, habw⟩ := Set.mem_mul.1 hab
    have hz_eq : z = a * w * cc := by
      rw [← hzabc, ← habw]
    have hcomp : z * 1 = a * (w * cc) := by
      rw [hz_eq]
      group
    have hsplit := T.eq_of_mul_eq_mul (a := 1) (c := 2) (b := 6) (by norm_num) (by norm_num)
      (by norm_num) hz12
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 ha))
      (by exact one_mem _)
      ((win T.U 3 6).mul_mem (T.win_mono (by norm_num) (by norm_num) hw)
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hcc)))
      hcomp
    rw [hsplit.1]
    exact ha
  have hz1 : z ≠ 1 := by
    intro hz0
    have hvy6 : ⁅v, y⁆ ∈ T.Uprime 6 := by
      have h := T.comm_odd_Uprime (hT := hT) (j := 3)
        (show Odd (3 : ℤ) from ⟨1, by norm_num⟩) hy3 hv
      simpa [commutatorElement_def, mul_assoc] using (T.Uprime 6).inv_mem h.1
    have hveq : ⁅vpp, e⁆ = ⁅v, y⁆ * y * e⁻¹ := by
      have h1 : ⁅vpp, e⁆ = (vpp * m) * y * (vpp * m)⁻¹ * e⁻¹ := by
        rw [show e = m * y * m⁻¹ by simp only [y]; group]
        simp only [commutatorElement_def]
        group
      have h2 : vpp * m = v * vp := by rw [hm]; group
      rw [h2] at h1
      have h3 : (v * vp) * y * (v * vp)⁻¹ = v * (z * y) * v⁻¹ := by
        rw [show v * vp * y * (v * vp)⁻¹ = v * (vp * y * vp⁻¹) * v⁻¹ by group]
        simp only [z, commutatorElement_def]
        group
      rw [h3] at h1
      have h4 : v * (z * y) * v⁻¹ = ⁅v, z⁆ * z * (⁅v, y⁆ * y) := by
        simp only [commutatorElement_def]
        group
      rw [h4] at h1
      rw [hz0] at h1
      simpa using h1
    have hve14 : ⁅vpp, e⁆ ∈ win T.U 1 4 := by
      have h := T.comm (i := 0) (j := 5) (by norm_num) (by norm_num) vpp hvpp0 e he
      have h' : vpp * e * vpp⁻¹ * e⁻¹ ∈ win T.U 1 4 := by
        refine SetLike.le_def.mp ?_ h
        refine iSup₂_le fun k hk => ?_
        obtain ⟨hk1, hk2⟩ := hk
        exact T.U_le_win (by omega) (by omega)
      simpa only [commutatorElement_def] using h'
    have hcomp : ⁅vpp, e⁆ * 1 = (y * e⁻¹) * ⁅v, y⁆ := by
      rw [hveq]
      have hcomm1 : ⁅v, y⁆ * y = y * ⁅v, y⁆ :=
        T.Uprime_comm_win (j := 6) (a := 3) (b := 3) (by norm_num) (by norm_num)
          hvy6 (by simpa [T.win_self] using hy3)
      have hcomm2 : ⁅v, y⁆ * e⁻¹ = e⁻¹ * ⁅v, y⁆ :=
        T.Uprime_comm_win (j := 6) (a := 5) (b := 5) (by norm_num) (by norm_num)
          hvy6 (by simpa [T.win_self] using he)
      calc (⁅v, y⁆ * y) * e⁻¹ * 1 = (y * ⁅v, y⁆) * e⁻¹ := by rw [hcomm1]; group
        _ = y * (⁅v, y⁆ * e⁻¹) := by group
        _ = y * (e⁻¹ * ⁅v, y⁆) := by rw [hcomm2]
        _ = (y * e⁻¹) * ⁅v, y⁆ := by group
    have hsplit := T.eq_of_mul_eq_mul (a := 1) (c := 5) (b := 6) (by norm_num) (by norm_num)
      (by norm_num) (T.win_mono (by norm_num) (by norm_num) hve14)
      (T.win_mono (by norm_num) (by norm_num)
        ((win T.U 3 5).mul_mem (T.U_le_win (by norm_num) (by norm_num) hy3)
          (T.U_le_win (by norm_num) (by norm_num) ((T.U 5).inv_mem he))))
      (by exact one_mem _)
      (by simpa [T.win_self] using T.Uprime_le 6 hvy6)
      hcomp
    have hye14 : y * e⁻¹ ∈ win T.U 1 4 := by
      rw [← hsplit.1]
      exact hve14
    have hye34 : y * e⁻¹ ∈ win T.U 3 4 := by
      have h : y * e⁻¹ ∈ win T.U 1 4 ⊓ win T.U 3 5 := by
        exact ⟨hye14, (win T.U 3 5).mul_mem
          (T.U_le_win (by norm_num) (by norm_num) hy3)
          (T.U_le_win (by norm_num) (by norm_num) ((T.U 5).inv_mem he))⟩
      rw [T.win_inf_win (a := 1) (b := 4) (c := 3) (d := 5) (by norm_num)] at h
      simpa using h
    have he4 : e⁻¹ ∈ T.U 4 := by
      have h : e⁻¹ ∈ win T.U 3 4 ⊓ win T.U 4 5 := by
        refine ⟨?_, ?_⟩
        · have h' : y⁻¹ * (y * e⁻¹) ∈ win T.U 3 4 :=
            (win T.U 3 4).mul_mem
              (T.U_le_win (by norm_num) (by norm_num) ((T.U 3).inv_mem hy3)) hye34
          simpa using h'
        · exact T.U_le_win (by norm_num) (by norm_num) ((T.U 5).inv_mem he)
      rw [T.win_inf_win (a := 3) (b := 4) (c := 4) (d := 5) (by norm_num)] at h
      simpa [T.win_self] using h
    have he1 : e = 1 := by
      have hbot : T.U 4 ⊓ T.U 5 = ⊥ := T.U_inf_U (by norm_num) (by norm_num)
      have hmem : e ∈ T.U 4 ⊓ T.U 5 := ⟨by simpa using (T.U 4).inv_mem he4, he⟩
      rw [hbot] at hmem
      simpa using hmem
    apply hu'1
    apply T.lemma38_i hv hv1 hu'2
    refine Set.mem_mul.2 ⟨m' * v⁻¹ * m'⁻¹, hA', m * u' * m⁻¹, hmu'6, ?_⟩
    rw [hve']
    rw [he1]
    group
  obtain ⟨ez, hez, hve_z⟩ := T.lemma38_one hv hv1 hz2 hz1
  have hAz : T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ ∈ T.Uprime 4 := by
    have h := T.mu_conj_mem_Uprime (i := 2) (j := 8) (u := z) (x := v)
      (T.Uprime_le 2 hz2) hz1 hv
    have h4 : T.mu 2 z * v * (T.mu 2 z)⁻¹ ∈ T.Uprime 4 := by simpa using h
    simpa [mul_assoc] using (T.Uprime 4).inv_mem h4
  have hmz6 : m * z * m⁻¹ ∈ T.Uprime 6 := by
    have h := T.mu_conj_mem_Uprime (i := 8) (j := 2) (u := v) (x := z)
      (T.Uprime_le 8 hv) hv1 hz2
    have h22 : T.mu 8 v * z * (T.mu 8 v)⁻¹ ∈ T.Uprime 22 := by simpa using h
    have hU22 : T.Uprime (22 : ℤ) = T.Uprime 6 := by
      simpa using (T.Uprime_add_two_mul 6 1)
    rw [hU22] at h22
    simpa [m] using h22
  have hveqz : ⁅v, z⁆ =
      T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹) := hve_z
  have hvy6 : ⁅v, y⁆ ∈ T.Uprime 6 := by
    have h := T.comm_odd_Uprime (hT := hT) (j := 3)
      (show Odd (3 : ℤ) from ⟨1, by norm_num⟩) hy3 hv
    simpa [commutatorElement_def, mul_assoc] using (T.Uprime 6).inv_mem h.1
  have hzy : Commute z y :=
    T.Uprime_comm_win (j := 2) (a := 3) (b := 3) (by norm_num) (by norm_num)
      hz2 (by simpa [T.win_self] using hy3)
  have hzA : Commute z (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹) :=
    T.Uprime_comm_win (j := 2) (a := 4) (b := 4) (by norm_num) (by norm_num)
      hz2 (by simpa [T.win_self] using T.Uprime_le 4 hAz)
  have hze : Commute z ez :=
    T.Uprime_comm_win (j := 2) (a := 5) (b := 5) (by norm_num) (by norm_num)
      hz2 (by simpa [T.win_self] using hez)
  have hzm : Commute z (m * z * m⁻¹) :=
    T.Uprime_comm_win (j := 2) (a := 6) (b := 6) (by norm_num) (by norm_num)
      hz2 (by simpa [T.win_self] using T.Uprime_le 6 hmz6)
  have hzvy : Commute z ⁅v, y⁆ :=
    T.Uprime_comm_win (j := 2) (a := 6) (b := 6) (by norm_num) (by norm_num)
      hz2 (by simpa [T.win_self] using T.Uprime_le 6 hvy6)
  have hyA : Commute y (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹) :=
    (T.Uprime_comm_win (j := 4) (a := 3) (b := 3) (by norm_num) (by norm_num)
      hAz (by simpa [T.win_self] using hy3)).symm
  have hye : Commute y ez :=
    T.comm_odd_add_two (hT := hT) (j := 3)
      (show Odd (3 : ℤ) from ⟨1, by norm_num⟩) hy3 (by simpa using hez)
  have hyzm : Commute y (m * z * m⁻¹) :=
    (T.Uprime_comm_win (j := 6) (a := 3) (b := 3) (by norm_num) (by norm_num)
      hmz6 (by simpa [T.win_self] using hy3)).symm
  have hyvy : Commute y ⁅v, y⁆ :=
    (T.Uprime_comm_win (j := 6) (a := 3) (b := 3) (by norm_num) (by norm_num)
      hvy6 (by simpa [T.win_self] using hy3)).symm
  have hem : Commute e⁻¹ (m * z * m⁻¹) :=
    (T.Uprime_comm_win (j := 6) (a := 5) (b := 5) (by norm_num) (by norm_num)
      hmz6 (by simpa [T.win_self] using (T.U 5).inv_mem he)).symm
  have hevy : Commute e⁻¹ ⁅v, y⁆ :=
    (T.Uprime_comm_win (j := 6) (a := 5) (b := 5) (by norm_num) (by norm_num)
      hvy6 (by simpa [T.win_self] using (T.U 5).inv_mem he)).symm
  have hzP : Commute z (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) :=
    ((hzA.mul_right hze).mul_right hzm)
  have hyP : Commute y ((T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) * ⁅v, y⁆) :=
    (((hyA.mul_right hye).mul_right hyzm).mul_right hyvy)
  have heP : Commute e⁻¹ ((m * z * m⁻¹) * ⁅v, y⁆) :=
    hem.mul_right hevy
  have hveq2 : ⁅vpp, e⁆ = (vpp * m) * y * (vpp * m)⁻¹ * e⁻¹ := by
    rw [show e = m * y * m⁻¹ by simp only [y]; group]
    simp only [commutatorElement_def]
    group
  have h2 : vpp * m = v * vp := by rw [hm]; group
  have h3 : (v * vp) * y * (v * vp)⁻¹ = v * (z * y) * v⁻¹ := by
    rw [show v * vp * y * (v * vp)⁻¹ = v * (vp * y * vp⁻¹) * v⁻¹ by group]
    simp only [z, commutatorElement_def]
    group
  have h4 : v * (z * y) * v⁻¹ = ⁅v, z⁆ * z * (⁅v, y⁆ * y) := by
    simp only [commutatorElement_def]
    group
  have hprod : ⁅vpp, e⁆ = z * y * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹) * (ez * e⁻¹) *
      ((m * z * m⁻¹) * ⁅v, y⁆) := by
    rw [hveq2, h2, h3, h4, hveqz]
    have hP : (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) * z =
        z * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) := hzP.eq.symm
    have hY : T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹) *
          (⁅v, y⁆ * y) =
        y * ((T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) * ⁅v, y⁆) := by
      rw [show T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹) * (⁅v, y⁆ * y) =
        (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹) * ⁅v, y⁆) * y by group]
      exact hyP.eq.symm
    have hE : ((m * z * m⁻¹) * ⁅v, y⁆) * e⁻¹ = e⁻¹ * ((m * z * m⁻¹) * ⁅v, y⁆) :=
      heP.eq.symm
    rw [hP]
    calc (z * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹))) * (⁅v, y⁆ * y) * e⁻¹
        = z * ((T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) * (⁅v, y⁆ * y)) *
            e⁻¹ := by group
      _ = z * (y * ((T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) * ⁅v, y⁆)) *
            e⁻¹ := by rw [hY]
      _ = z * y * ((T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez * (m * z * m⁻¹)) * ⁅v, y⁆) *
            e⁻¹ := by group
      _ = z * y * ((T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez) * ((m * z * m⁻¹) * ⁅v, y⁆)) *
            e⁻¹ := by group
      _ = (z * y * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez)) *
            (((m * z * m⁻¹) * ⁅v, y⁆) * e⁻¹) := by group
      _ = (z * y * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹ * ez)) *
            (e⁻¹ * ((m * z * m⁻¹) * ⁅v, y⁆)) := by rw [hE]
      _ = z * y * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹) * (ez * e⁻¹) *
            ((m * z * m⁻¹) * ⁅v, y⁆) := by group
  have hve14 : ⁅vpp, e⁆ ∈ win T.U 1 4 := by
    have h := T.comm (i := 0) (j := 5) (by norm_num) (by norm_num) vpp hvpp0 e he
    have h' : vpp * e * vpp⁻¹ * e⁻¹ ∈ win T.U 1 4 := by
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := hk
      exact T.U_le_win (by omega) (by omega)
    simpa only [commutatorElement_def] using h'
  have hcomp2 : ⁅vpp, e⁆ * 1 =
      (z * y * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹)) *
        ((ez * e⁻¹) * ((m * z * m⁻¹) * ⁅v, y⁆)) := by
    rw [hprod]
    group
  have hsplit2 := T.eq_of_mul_eq_mul (a := 1) (c := 4) (b := 6) (by norm_num) (by norm_num)
    (by norm_num) hve14
    ((win T.U 1 4).mul_mem ((win T.U 1 4).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 2 hz2))
      (T.U_le_win (by norm_num) (by norm_num) hy3))
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hAz)))
    (by exact one_mem _)
    ((win T.U 5 6).mul_mem
      ((win T.U 5 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) hez)
        (T.U_le_win (by norm_num) (by norm_num) ((T.U 5).inv_mem he)))
      ((win T.U 5 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hmz6))
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hvy6))))
    hcomp2
  have hsplit3 : ez * e⁻¹ = 1 ∧ (m * z * m⁻¹) * ⁅v, y⁆ = 1 := by
    have hcomp3 : (ez * e⁻¹) * ((m * z * m⁻¹) * ⁅v, y⁆) = (1 : G) * 1 := by
      simpa using hsplit2.2.symm
    exact T.eq_of_mul_eq_mul (a := 5) (c := 5) (b := 6) (by norm_num) (by norm_num)
      (by norm_num)
      ((win T.U 5 5).mul_mem (T.U_le_win (by norm_num) (by norm_num) hez)
        (T.U_le_win (by norm_num) (by norm_num) ((T.U 5).inv_mem he)))
      (by simpa [T.win_self] using one_mem (T.U 5))
      ((win T.U 6 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hmz6))
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hvy6)))
      (by simpa [T.win_self] using one_mem (T.U 6))
      (by simpa using hcomp3)
  have heze : ez = e := by
    calc ez = ez * e⁻¹ * e := by group
      _ = 1 * e := by rw [hsplit3.1]
      _ = e := by group
  have hz_eq : z = u' := by
    refine T.lemma38_i_inj (v := v) (x := z) (x' := u')
      (d := T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹) (d' := m' * v⁻¹ * m'⁻¹)
      (e := e) (c := m * z * m⁻¹) (c' := m * u' * m⁻¹)
      hv hv1 hz2 hu'2 hAz hA' he hmz6 hmu'6 ?_ ?_
    · rw [hveqz, heze]
    · exact hve'
  have hzmu : (m * z * m⁻¹) = ⁅y, v⁆ := by
    calc m * z * m⁻¹ = (m * z * m⁻¹) * (⁅v, y⁆ * ⁅v, y⁆⁻¹) := by group
      _ = ((m * z * m⁻¹) * ⁅v, y⁆) * ⁅v, y⁆⁻¹ := by group
      _ = 1 * ⁅v, y⁆⁻¹ := by rw [hsplit3.2]
      _ = ⁅y, v⁆ := by
          simp only [commutatorElement_def]
          group
  have hmu'eq : (m * u' * m⁻¹) = ⁅u, v⁆ := by
    rw [hu']
    group
  have hyu : y = u := by
    have hv8' : v ∈ (T.shift 2).Uprime 6 := by
      rw [T.Uprime_shift]
      norm_num
      exact hv
    have hy1 : y ∈ (T.shift 2).U 1 := by
      rw [shift_U]
      norm_num
      exact hy3
    have hu1' : u ∈ (T.shift 2).U 1 := by
      rw [shift_U]
      norm_num
      exact hu
    have hcomm : ⁅y, v⁆ = ⁅u, v⁆ := by
      rw [← hzmu, ← hmu'eq, hz_eq]
    exact TitsSystem.lemma33_i_inj (T := T.shift 2) (hT := hT.shift (by norm_num))
      hv8' hv1 hy1 hu1' hcomm
  have he_eq : e = m * u * m⁻¹ := by
    have hey : e = m * y * m⁻¹ := by
      simp only [y]
      group
    rw [hey, hyu]
  refine ⟨?_, ?_⟩
  · rw [hve', he_eq]
  · rw [← he_eq]
    have h1 : ⁅vpp, e⁆ = z * y * (T.mu 2 z * v⁻¹ * (T.mu 2 z)⁻¹) := by
      rw [hprod, hsplit3.1, hsplit3.2]
      group
    rw [h1, hz_eq, hyu]

theorem lemma38_ii (hT : T.Normalized) {v u u' : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1)
    (hu : u ∈ T.U 3) (hu1 : u ≠ 1) (hu' : u' = (T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v) :
    ⁅v, u'⁆ = T.mu 2 u' * v⁻¹ * (T.mu 2 u')⁻¹ * (T.mu 8 v * u * (T.mu 8 v)⁻¹) *
      (T.mu 8 v * u' * (T.mu 8 v)⁻¹) :=
  (lemma38_ii_iii_aux T hT hv hv1 hu hu1 hu').1

theorem lemma38_iii (hT : T.Normalized) {v u u' : G} (hv : v ∈ T.Uprime 8) (hv1 : v ≠ 1)
    (hu : u ∈ T.U 3) (hu1 : u ≠ 1) (hu' : u' = (T.mu 8 v)⁻¹ * ⁅u, v⁆ * T.mu 8 v) :
    ⁅(T.nu 8 v)⁻¹, T.mu 8 v * u * (T.mu 8 v)⁻¹⁆ =
      u' * u * (T.mu 2 u' * v⁻¹ * (T.mu 2 u')⁻¹) :=
  (lemma38_ii_iii_aux T hT hv hv1 hu hu1 hu').2

end TitsSystem

end CFSG.GH74.Tits83
