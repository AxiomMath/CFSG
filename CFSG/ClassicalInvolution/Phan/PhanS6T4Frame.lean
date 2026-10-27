module

public import CFSG.ClassicalInvolution.Phan.PhanS6T1Lin
public import CFSG.ClassicalInvolution.Phan.PhanS6T3Octa

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

variable {K : Type} [Field K] (M : Model K)

structure Frame where
  a : Vec K
  b : Vec K
  f : Vec K
  z : Vec K
  r : Vec K
  bf_aa : bf M a a = 0
  bf_ab : bf M a b = 0
  bf_bb : bf M b b = 0
  f_a : bf M f a = 0
  f_b : bf M f b = 0
  f_A : bf M f (tauV M a) = 0
  f_B : bf M f (tauV M b) = 0
  z_a : bf M z a = 0
  z_b : bf M z b = 0
  z_A : bf M z (tauV M a) = 0
  z_B : bf M z (tauV M b) = 0
  r_a : bf M r a = 0
  r_b : bf M r b = 0
  r_A : bf M r (tauV M a) = 0
  r_B : bf M r (tauV M b) = 0
  bf_ff : bf M f f = 0
  bf_fz : bf M f z = 0
  bf_fr : bf M f r = 1
  bf_zr : bf M z r = 0
  bf_rr : bf M r r = 0
  tau_f : tauV M f = f
  tau_z : tauV M z = z
  tau_r : tauV M r = r

variable {M}

namespace Frame

variable (F : Frame M)

@[expose] def gd : Gd M where
  na := her M F.a F.a
  nb := her M F.b F.b
  h := her M F.a F.b
  ζ := bf M F.z F.z
  hna := tau_her_self M F.a
  hnb := tau_her_self M F.b
  hζ := by rw [← bf_tauV, F.tau_z]

@[expose] def Φ (x : Co K) : Vec K :=
  x.xa • F.a + x.xb • F.b + x.xA • tauV M F.a + x.xB • tauV M F.b + x.xf • F.f + x.xz • F.z +
    x.xr • F.r

theorem bf_Φ (x y : Co K) : bf M (F.Φ x) (F.Φ y) = F.gd.bfc x y := by
  have e_aa : bf M F.a F.a = 0 := F.bf_aa
  have e_ab : bf M F.a F.b = 0 := F.bf_ab
  have e_aA_ : bf M F.a (tauV M F.a) = her M F.a F.a := rfl
  have e_aB_ : bf M F.a (tauV M F.b) = her M F.a F.b := rfl
  have e_af : bf M F.a F.f = 0 := by rw [bf_comm]; exact F.f_a
  have e_az : bf M F.a F.z = 0 := by rw [bf_comm]; exact F.z_a
  have e_ar : bf M F.a F.r = 0 := by rw [bf_comm]; exact F.r_a
  have e_ba : bf M F.b F.a = 0 := by rw [bf_comm]; exact F.bf_ab
  have e_bb : bf M F.b F.b = 0 := F.bf_bb
  have e_bA_ : bf M F.b (tauV M F.a) = M.τ (her M F.a F.b) := her_conj_symm M F.a F.b
  have e_bB_ : bf M F.b (tauV M F.b) = her M F.b F.b := rfl
  have e_bf : bf M F.b F.f = 0 := by rw [bf_comm]; exact F.f_b
  have e_bz : bf M F.b F.z = 0 := by rw [bf_comm]; exact F.z_b
  have e_br : bf M F.b F.r = 0 := by rw [bf_comm]; exact F.r_b
  have e_A_a : bf M (tauV M F.a) F.a = her M F.a F.a := by rw [bf_comm]; rfl
  have e_A_b : bf M (tauV M F.a) F.b = M.τ (her M F.a F.b) := by
    rw [bf_comm]
    exact her_conj_symm M F.a F.b
  have e_A_A_ : bf M (tauV M F.a) (tauV M F.a) = 0 := by rw [bf_tauV, F.bf_aa, map_zero]
  have e_A_B_ : bf M (tauV M F.a) (tauV M F.b) = 0 := by rw [bf_tauV, F.bf_ab, map_zero]
  have e_A_f : bf M (tauV M F.a) F.f = 0 := by rw [bf_comm]; exact F.f_A
  have e_A_z : bf M (tauV M F.a) F.z = 0 := by rw [bf_comm]; exact F.z_A
  have e_A_r : bf M (tauV M F.a) F.r = 0 := by rw [bf_comm]; exact F.r_A
  have e_B_a : bf M (tauV M F.b) F.a = her M F.a F.b := by rw [bf_comm]; rfl
  have e_B_b : bf M (tauV M F.b) F.b = her M F.b F.b := by rw [bf_comm]; rfl
  have e_B_A_ : bf M (tauV M F.b) (tauV M F.a) = 0 := by rw [bf_tauV, bf_comm, F.bf_ab, map_zero]
  have e_B_B_ : bf M (tauV M F.b) (tauV M F.b) = 0 := by rw [bf_tauV, F.bf_bb, map_zero]
  have e_B_f : bf M (tauV M F.b) F.f = 0 := by rw [bf_comm]; exact F.f_B
  have e_B_z : bf M (tauV M F.b) F.z = 0 := by rw [bf_comm]; exact F.z_B
  have e_B_r : bf M (tauV M F.b) F.r = 0 := by rw [bf_comm]; exact F.r_B
  have e_fa : bf M F.f F.a = 0 := F.f_a
  have e_fb : bf M F.f F.b = 0 := F.f_b
  have e_fA_ : bf M F.f (tauV M F.a) = 0 := F.f_A
  have e_fB_ : bf M F.f (tauV M F.b) = 0 := F.f_B
  have e_ff : bf M F.f F.f = 0 := F.bf_ff
  have e_fz : bf M F.f F.z = 0 := F.bf_fz
  have e_fr : bf M F.f F.r = 1 := F.bf_fr
  have e_za : bf M F.z F.a = 0 := F.z_a
  have e_zb : bf M F.z F.b = 0 := F.z_b
  have e_zA_ : bf M F.z (tauV M F.a) = 0 := F.z_A
  have e_zB_ : bf M F.z (tauV M F.b) = 0 := F.z_B
  have e_zf : bf M F.z F.f = 0 := by rw [bf_comm]; exact F.bf_fz
  have e_zr : bf M F.z F.r = 0 := F.bf_zr
  have e_ra : bf M F.r F.a = 0 := F.r_a
  have e_rb : bf M F.r F.b = 0 := F.r_b
  have e_rA_ : bf M F.r (tauV M F.a) = 0 := F.r_A
  have e_rB_ : bf M F.r (tauV M F.b) = 0 := F.r_B
  have e_rf : bf M F.r F.f = 1 := by rw [bf_comm]; exact F.bf_fr
  have e_rz : bf M F.r F.z = 0 := by rw [bf_comm]; exact F.bf_zr
  have e_rr : bf M F.r F.r = 0 := F.bf_rr
  simp only [Φ, bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, e_aa, e_ab, e_aA_, e_aB_,
    e_af, e_az, e_ar, e_ba, e_bb, e_bA_, e_bB_, e_bf, e_bz, e_br, e_A_a, e_A_b, e_A_A_, e_A_B_,
    e_A_f, e_A_z, e_A_r, e_B_a, e_B_b, e_B_A_, e_B_B_, e_B_f, e_B_z, e_B_r, e_fa, e_fb, e_fA_,
    e_fB_, e_ff, e_fz, e_fr, e_za, e_zb, e_zA_, e_zB_, e_zf, e_zr, e_ra, e_rb, e_rA_, e_rB_,
    e_rf, e_rz, e_rr, gd, Gd.bfc]
  ring

theorem tauV_Φ (x : Co K) : tauV M (F.Φ x) = F.Φ (Co.cj M x) := by
  simp only [Φ, Co.cj, tauV_add, tauV_smul, tauV_tauV, F.tau_f, F.tau_z, F.tau_r]
  abel

theorem her_Φ (x y : Co K) : her M (F.Φ x) (F.Φ y) = F.gd.herc x y := by
  rw [her, tauV_Φ, bf_Φ]
  rfl

theorem gram_Φ (x y : Co K) : gram M (F.Φ x) (F.Φ y) = F.gd.gramc x y := by
  simp only [gram, Gd.gramc, her_Φ]

theorem det3_Φ (x y z : Co K) : det3 M (F.Φ x) (F.Φ y) (F.Φ z) = F.gd.det3c x y z := by
  simp only [det3, Gd.det3c, her_Φ]

theorem Φ_va : F.Φ va = F.a := by
  simp [Φ, va]

theorem Φ_vb : F.Φ vb = F.b := by
  simp [Φ, vb]

theorem Φ_vc (α β : K) : F.Φ (vc α β) = α • F.a + β • F.b + F.r := by
  simp [Φ, vc]

theorem isFF_Φ {x : Co K} (h : F.gd.Ffc x) : IsFF M (F.Φ x) :=
  ⟨by rw [bf_Φ]; exact h.1, by rw [her_Φ]; exact h.2⟩

theorem col_Φ {x y : Co K} (h : F.gd.Colc x y) : Col M (F.Φ x) (F.Φ y) :=
  ⟨by rw [bf_Φ]; exact h.1, by rw [gram_Φ]; exact h.2⟩

theorem geom_Φ {x y z : Co K} (h : F.gd.Geomc x y z) : Geom M (F.Φ x) (F.Φ y) (F.Φ z) :=
  ⟨col_Φ F h.1, col_Φ F h.2.1, col_Φ F h.2.2.1, Or.inl (by rw [det3_Φ]; exact h.2.2.2)⟩

end Frame

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
