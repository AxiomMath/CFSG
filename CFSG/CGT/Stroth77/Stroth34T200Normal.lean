module

public import CFSG.CGT.Stroth77.Stroth34T200R0

public section

namespace CFSG.CGT.Stroth77

open Stroth34T200

namespace Stroth34T200

variable {m : ℕ}

theorem c_zsmul_eq_zero_iff (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] = 0 ↔ (2 : ℤ) ^ m ∣ l := by
  rw [t200_zsmul_vec, t200_vec_eq_zero_iff]
  simp

theorem c_zsmul_eq_iff (l l' : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] = l' • Torus.ofInt _ ![1, 0, 0] ↔
      (2 : ℤ) ^ m ∣ l - l' := by
  rw [t200_zsmul_vec, t200_zsmul_vec, t200_vec_eq_iff]
  simp only [mul_one, mul_zero, sub_zero, dvd_zero, and_true]
  exact dvd_sub_comm

theorem dvd_of_four_mul_zsmul_w {l : ℤ}
    (h : (4 * l) • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 1, 1] = 0) : (2 : ℤ) ^ m ∣ l := by
  rw [t200_zsmul_vec, t200_vec_eq_zero_iff] at h
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h
  exact ⟨k, mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) (by linear_combination hk)⟩

theorem a_eq_ofInt : (Torus.a : Torus (StrothTypeIndex.t200 m).k) = Torus.ofInt _ ![0, 1, 0] := by
  show gen _ 1 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem b_eq_ofInt : (Torus.b : Torus (StrothTypeIndex.t200 m).k) = Torus.ofInt _ ![0, 0, 1] := by
  show gen _ 2 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

end Stroth34T200

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (StrothTypeIndex.t200 m))

theorem t200_c_eq : (dD.c : G) = dD.ofT (Torus.ofInt _ ![1, 0, 0]) := by
  rw [← c_eq_ofInt]; rfl

theorem t200_a_eq : (dD.a : G) = dD.ofT (Torus.ofInt _ ![0, 1, 0]) := by
  rw [← a_eq_ofInt]; rfl

theorem t200_b_eq : (dD.b : G) = dD.ofT (Torus.ofInt _ ![0, 0, 1]) := by
  rw [← b_eq_ofInt]; rfl

theorem t200_c_pow_eq (j : ℕ) :
    (dD.c : G) ^ j = dD.ofT ((j : ℤ) • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) := by
  rw [dD.ofT_zsmul, zpow_natCast, ← t200_c_eq]

theorem t200_c_inv_eq :
    (dD.c : G)⁻¹ = dD.ofT ((-1 : ℤ) • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) := by
  rw [dD.ofT_zsmul, zpow_neg_one, ← t200_c_eq]

theorem t200_c_pow_inv_mul_pow_eq (p M : ℕ) :
    ((dD.c : G) ^ p)⁻¹ * (dD.c : G) ^ M =
      dD.ofT ((-(p : ℤ) + M) • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t200_c_eq, zpow_neg, zpow_natCast,
    zpow_natCast]

theorem t200_a_mul_pow_eq (j : ℕ) :
    (dD.a : G) * (dD.a : G) ^ j =
      dD.ofT ((1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0]) := by
  rw [add_zsmul, dD.ofT_add, one_zsmul, dD.ofT_zsmul, ← t200_a_eq, zpow_natCast]

theorem t200_a_inv_mul_pow_eq (j : ℕ) :
    (dD.a : G)⁻¹ * (dD.a : G) ^ j =
      dD.ofT ((-1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t200_a_eq, zpow_natCast, zpow_neg_one]

theorem t200_b_mul_pow_eq (j : ℕ) :
    (dD.b : G) * (dD.b : G) ^ j =
      dD.ofT ((1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, 1]) := by
  rw [add_zsmul, dD.ofT_add, one_zsmul, dD.ofT_zsmul, ← t200_b_eq, zpow_natCast]

theorem t200_b_inv_mul_pow_eq (j : ℕ) :
    (dD.b : G)⁻¹ * (dD.b : G) ^ j =
      dD.ofT ((-1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, 1]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t200_b_eq, zpow_natCast, zpow_neg_one]

theorem t200_cab_pow_eq (p : ℕ) :
    ((dD.c : G) * dD.a * dD.b) ^ p =
      dD.ofT ((p : ℤ) • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 1, 1]) := by
  have h : Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 1, 1] =
      Torus.ofInt _ ![1, 0, 0] + Torus.ofInt _ ![0, 1, 0] + Torus.ofInt _ ![0, 0, 1] := by
    rw [t200_add_vec, t200_add_vec]; norm_num
  rw [dD.ofT_zsmul, zpow_natCast, h, dD.ofT_add, dD.ofT_add, ← t200_c_eq, ← t200_a_eq,
    ← t200_b_eq]

theorem t200_a_pow_inv_eq (p : ℕ) :
    ((dD.a : G) ^ p)⁻¹ =
      dD.ofT ((p : ℤ) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0]) := by
  have h : Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0] =
      (-1 : ℤ) • Torus.ofInt _ ![0, 1, 0] := by
    rw [t200_zsmul_vec]; norm_num
  rw [h, smul_smul, dD.ofT_zsmul, ← t200_a_eq, mul_neg_one, zpow_neg, zpow_natCast]

end StrothWeakTypeData

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t200 m)}

theorem t200_crdT_eq_of_proj_eq (hS : Local.Setting (F.S : Subgroup G) D) {d : G} (hd : d ∈ D)
    (hp : hS.proj dD.ρ d = d) :
    ∃ l : ℤ, crdT dD.e d = l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] := by
  have hρd : dD.ρ⁻¹ * d * dD.ρ ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hd
  have h1 := hS.proj_eq_of_mem (hS.D_le_R hρd)
  rw [hp] at h1
  obtain ⟨l, hl⟩ := fix_ρ_c (crdT dD.e d) (by
    rw [← crdT_conj dD.e dD.ρ_mem dD.ρ_conj hd, ← h1])
  exact ⟨l, by rw [hl, c_eq_ofInt]⟩

theorem normal200_one (hS : Local.Setting (F.S : Subgroup G) D) : Normal200 hS dD 1 1 0 where
  mem := one_mem _
  proj := proj_rho_one hS
  comm := by rw [mul_one, one_mul]
  scalar v := by rw [one_zsmul]; exact dD.thetaT_of_mem _ (one_mem D) v
  ruv := by rw [zero_zsmul, show (1 : G)⁻¹ * dD.uv * 1 * dD.uv⁻¹ = 1 by group, crdT_one]
  rt := by rw [zero_zsmul, show (1 : G)⁻¹ * dD.t * 1 * dD.t⁻¹ = 1 by group, crdT_one]

end StrothFrame.IsD

namespace Normal200

open StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t200 m)} {hS : Local.Setting (F.S : Subgroup G) D}

theorem mul_c {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (μ : ℤ) :
    Normal200 hS dD (e * dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]))
      y (p - 4 * μ) := by
  set d := dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) with hd_def
  have hd : d ∈ D := dD.ofT_mem _
  have hdN : d ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hd
  have hcd : crdT dD.e d = μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] :=
    dD.crdT_ofT _
  have heN := hS.R_le_normalizer hn.mem.1
  have hρd : dD.ρ⁻¹ * d * dD.ρ = d := by
    refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hd) hd ?_
    rw [crdT_conj dD.e dD.ρ_mem dD.ρ_conj hd, hcd, map_zsmul, ← c_eq_ofInt, φρ_c]
  have hud : dD.u * d = d * dD.u := by
    have h1 : dD.u⁻¹ * d * dD.u = d := by
      refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp dD.u_mem _).mp hd) hd ?_
      rw [crdT_conj dD.e dD.u_mem dD.u_conj hd, hcd, map_zsmul, ← c_eq_ofInt, φu_c]
    calc dD.u * d = dD.u * (dD.u⁻¹ * d * dD.u) := by rw [h1]
      _ = d * dD.u := by group
  have huv := dD.crdT_cocycle_mul hdN hn.mem.2.1 (dD.crdT_cocycle_of_mem_uv hd).1
  have ht := dD.crdT_cocycle_mul hdN hn.mem.2.2 (dD.crdT_cocycle_of_mem_t hd).1
  refine ⟨mul_mem hn.mem (D_le_R1 hS hd), ?_, ?_, fun v => ?_, ?_, ?_⟩
  · rw [hS.proj_mul dD.ρ_mem hn.mem.1 (hS.D_le_R hd), hn.proj,
      hS.proj_eq_of_mem (by rw [hρd]; exact hS.D_le_R hd), hρd]
  · rw [← mul_assoc, hn.comm, mul_assoc, hud, ← mul_assoc]
  · rw [dD.thetaT_congr _ (mul_mem heN hdN) rfl, dD.thetaT_mul heN hdN, dD.thetaT_of_mem hdN hd,
      hn.scalar]
  · rw [huv.2, dD.thetaT_of_mem hdN hd, hn.ruv, (dD.crdT_cocycle_of_mem_uv hd).2, hcd, φuv_c_sub,
      ← add_zsmul]
    congr 1; ring
  · rw [ht.2, dD.thetaT_of_mem hdN hd, hn.rt, (dD.crdT_cocycle_of_mem_t hd).2, hcd, φt_c_sub,
      ← add_zsmul]
    congr 1; ring

theorem mul {e f : G} {y p y' p' : ℤ} (he : Normal200 hS dD e y p)
    (hf : Normal200 hS dD f y' p') : Normal200 hS dD (e * f) (y * y') (y' * p + p') := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  refine ⟨mul_mem he.mem hf.mem, ?_, ?_, fun v => ?_, ?_, ?_⟩
  · rw [hS.proj_mul dD.ρ_mem he.mem.1 hf.mem.1, he.proj, hf.proj]
  · rw [← mul_assoc, he.comm, mul_assoc, hf.comm, mul_assoc]
  · rw [dD.thetaT_congr _ (mul_mem heN hfN) rfl, dD.thetaT_mul heN hfN, he.scalar, map_zsmul,
      hf.scalar, smul_smul]
  · rw [(dD.crdT_cocycle_mul hfN he.mem.2.1 hf.mem.2.1).2, he.ruv, map_zsmul, hf.scalar,
      smul_smul, hf.ruv, ← add_zsmul, mul_comm y' p]
  · rw [(dD.crdT_cocycle_mul hfN he.mem.2.2 hf.mem.2.2).2, he.rt, map_zsmul, hf.scalar,
      smul_smul, hf.rt, ← add_zsmul, mul_comm y' p]

theorem mem_of_dvd (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p)
    (hp : (4 : ℤ) ∣ p) : e ∈ D := by
  obtain ⟨μ, rfl⟩ := hp
  exact h.mem_of_cocycle_cob hS hn.mem.1 hn.mem.2.1 hn.mem.2.2
    (μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) (by rw [hn.ruv, cob_uv])
    (by rw [hn.rt, cob_t])

theorem mul_inv_mem (h : F.IsD D dD) {e f : G} {y p y' p' : ℤ} (he : Normal200 hS dD e y p)
    (hf : Normal200 hS dD f y' p') (hp : (4 : ℤ) ∣ p - p') : e * f⁻¹ ∈ D := by
  obtain ⟨μ, hμ⟩ := hp
  refine h.mul_inv_mem_of_cocycle_cob hS he.mem hf.mem
    (μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) ?_ ?_
  · rw [he.ruv, hf.ruv, cob_uv, ← add_zsmul]
    congr 1; linear_combination hμ
  · rw [he.rt, hf.rt, cob_t, ← add_zsmul]
    congr 1; linear_combination hμ

theorem scalar_dvd {e f : G} {y p y' p' : ℤ} (he : Normal200 hS dD e y p)
    (hf : Normal200 hS dD f y' p') (hef : e * f⁻¹ ∈ D) : (2 : ℤ) ^ (m + 2) ∣ y - y' := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  have hdN : e * f⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hef
  refine dvd_sub_of_zsmul_eq (a := 0) (c := 0) ?_
  rw [← he.scalar, ← hf.scalar, dD.thetaT_congr heN (mul_mem hdN hfN) (by group),
    dD.thetaT_mul hdN hfN, dD.thetaT_of_mem hdN hef]

theorem mul_inv_mem_of_scalar {e f : G} {y p y' p' : ℤ} (he : Normal200 hS dD e y p)
    (hf : Normal200 hS dD f y' p') (hy : (2 : ℤ) ^ (m + 2) ∣ y - y') : e * f⁻¹ ∈ D := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S he.mem.1) (inv_mem (hS.R_le_S hf.mem.1)))
    (mul_mem heN (inv_mem hfN)) fun v => ?_
  rw [dD.thetaT_mul heN (inv_mem hfN), he.scalar, zsmul_congr hy, ← hf.scalar,
    dD.thetaT_inv_thetaT]

theorem dvd_of_mul_inv_mem {e f : G} {y p y' p' : ℤ} (he : Normal200 hS dD e y p)
    (hf : Normal200 hS dD f y' p') (hef : e * f⁻¹ ∈ D) : (4 : ℤ) ∣ p - p' := by
  have hfN := hS.R_le_normalizer hf.mem.1
  have hp : hS.proj dD.ρ (e * f⁻¹) = e * f⁻¹ := by
    rw [hS.proj_mul dD.ρ_mem he.mem.1 (inv_mem hf.mem.1), he.proj, proj_rho_inv hS hf.mem.1,
      hf.proj]
  obtain ⟨l, hl⟩ := t200_crdT_eq_of_proj_eq hS hef hp
  have key := (dD.crdT_cocycle_mul hfN (dD.crdT_cocycle_of_mem_uv hef).1 hf.mem.2.1).2
  rw [show e * f⁻¹ * f = e by group, he.ruv, (dD.crdT_cocycle_of_mem_uv hef).2, hl, φuv_c_sub,
    map_zsmul, hf.scalar, smul_smul, hf.ruv, ← add_zsmul] at key
  obtain ⟨k, hk⟩ := dvd_sub_of_zsmul_eq key
  exact ⟨2 ^ m * k - l * y', by linear_combination hk⟩

theorem dvd_of_mem {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (he : e ∈ D) :
    (4 : ℤ) ∣ p := by
  have := hn.dvd_of_mul_inv_mem (normal200_one hS) (by simpa using he)
  simpa using this

theorem scalar_dvd_of_mem {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (he : e ∈ D) :
    (2 : ℤ) ^ (m + 2) ∣ y - 1 :=
  hn.scalar_dvd (normal200_one hS) (by simpa using he)

theorem mem_of_scalar {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - 1) : e ∈ D := by
  simpa using hn.mul_inv_mem_of_scalar (normal200_one hS) hy

theorem eq (h : F.IsD D dD) {e f : G} {y p y' p' : ℤ} (he : Normal200 hS dD e y p)
    (hf : Normal200 hS dD f y' p') (hp : (2 : ℤ) ^ (m + 2) ∣ p - p') : e = f := by
  have hef : e * f⁻¹ ∈ D := he.mul_inv_mem h hf (dvd_trans ⟨2 ^ m, by ring⟩ hp)
  have hfN := hS.R_le_normalizer hf.mem.1
  have hpr : hS.proj dD.ρ (e * f⁻¹) = e * f⁻¹ := by
    rw [hS.proj_mul dD.ρ_mem he.mem.1 (inv_mem hf.mem.1), he.proj, proj_rho_inv hS hf.mem.1,
      hf.proj]
  obtain ⟨l, hl⟩ := t200_crdT_eq_of_proj_eq hS hef hpr
  have key := (dD.crdT_cocycle_mul hfN (dD.crdT_cocycle_of_mem_uv hef).1 hf.mem.2.1).2
  rw [show e * f⁻¹ * f = e by group, he.ruv, hf.ruv, zsmul_congr hp] at key
  have k0 : dD.thetaT hfN (crdT dD.e ((e * f⁻¹)⁻¹ * dD.uv * (e * f⁻¹) * dD.uv⁻¹)) = 0 :=
    (add_left_inj _).mp (by rw [zero_add]; exact key.symm)
  have h0 : crdT dD.e ((e * f⁻¹)⁻¹ * dD.uv * (e * f⁻¹) * dD.uv⁻¹) = 0 := by
    have := congrArg (dD.thetaT (inv_mem hfN)) k0
    rwa [dD.thetaT_inv_thetaT, map_zero] at this
  rw [(dD.crdT_cocycle_of_mem_uv hef).2, hl, φuv_c_sub] at h0
  have hl0 : l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] = 0 := by
    rw [c_zsmul_eq_zero_iff]
    exact dvd_neg.mp (dvd_of_four_mul_zsmul_w
      (by rw [show (4 * -l : ℤ) = -4 * l by ring]; exact h0))
  have h1 : e * f⁻¹ = 1 := crdT_inj dD.e hef (one_mem D) (by rw [hl, hl0, crdT_one])
  exact mul_inv_eq_one.mp h1

theorem eq_ofT (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {μ : ℤ}
    (hμ : (2 : ℤ) ^ (m + 2) ∣ p + 4 * μ) :
    e = dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) := by
  have h1 := (normal200_one hS (dD := dD)).mul_c μ
  rw [one_mul] at h1
  exact hn.eq h h1 (by rw [zero_sub, sub_neg_eq_add]; exact hμ)

theorem c_conj_eq {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ m ∣ y - l) :
    e⁻¹ * (dD.c : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have hc : (dD.c : G) ∈ D := (dD.c).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp hc) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN hc, dD.crdT_ofT, dD.t200_c_eq, dD.crdT_ofT, hn.scalar,
    (c_zsmul_eq_iff y l).mpr hy]

theorem a_conj_eq {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - l) :
    e⁻¹ * (dD.a : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have ha : (dD.a : G) ∈ D := (dD.a).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp ha) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN ha, dD.crdT_ofT, dD.t200_a_eq, dD.crdT_ofT, hn.scalar, zsmul_congr hy]

theorem b_conj_eq {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - l) :
    e⁻¹ * (dD.b : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, 1]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have hb : (dD.b : G) ∈ D := (dD.b).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp hb) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN hb, dD.crdT_ofT, dD.t200_b_eq, dD.crdT_ofT, hn.scalar, zsmul_congr hy]

theorem uv_conj_eq {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {q : ℕ}
    (hq : (2 : ℤ) ^ (m + 2) ∣ p - q) :
    e⁻¹ * dD.uv * e = ((dD.c : G) * dD.a * dD.b) ^ q * dD.uv := by
  have key : e⁻¹ * dD.uv * e * dD.uv⁻¹ = ((dD.c : G) * dD.a * dD.b) ^ q := by
    rw [dD.t200_cab_pow_eq]
    exact crdT_inj dD.e hn.mem.2.1 (dD.ofT_mem _) (by rw [hn.ruv, dD.crdT_ofT, zsmul_congr hq])
  rw [← key]; group

theorem t_conj_eq {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {q : ℕ}
    (hq : (2 : ℤ) ^ (m + 2) ∣ p - q) :
    e⁻¹ * dD.t * e = ((dD.a : G) ^ q)⁻¹ * dD.t := by
  have key : e⁻¹ * dD.t * e * dD.t⁻¹ = ((dD.a : G) ^ q)⁻¹ := by
    rw [dD.t200_a_pow_inv_eq]
    exact crdT_inj dD.e hn.mem.2.2 (dD.ofT_mem _) (by rw [hn.rt, dD.crdT_ofT, zsmul_congr hq])
  rw [← key]; group

theorem u_conj_eq {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) : e⁻¹ * dD.u * e = dD.u := by
  rw [mul_assoc, hn.comm]; group

theorem sq_eq (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {μ : ℤ}
    (hμ : (2 : ℤ) ^ (m + 2) ∣ (y + 1) * p + 4 * μ) :
    e * e = dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) :=
  (hn.mul hn).eq_ofT h (by convert hμ using 1; ring)

end Normal200

end CFSG.CGT.Stroth77
