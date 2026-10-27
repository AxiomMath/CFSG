module

public import CFSG.CGT.Stroth77.Stroth34Layer
public import CFSG.CGT.Stroth77.Stroth34T201Facts
public import CFSG.CGT.Stroth77.Stroth34Defs

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Stroth34T201

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)}

theorem t201_proj_mul_inv_mem (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e : G} (he : e ∈ hS.R1 dD.uv dD.t) : hS.proj dD.ρ e * e⁻¹ ∈ D :=
  h.proj_rho_mul_inv_mem hS (fun _ _ h1 h2 h3 => t201_rho_triv hm _ _ h1 h2 h3) he

theorem t201_comm_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    {e : G} (he : e ∈ hS.R1 dD.uv dD.t) :
    (∀ x, dD.thetaT (hS.R_le_normalizer he.1) ((StrothTypeIndex.t201 m).action.φuv x) =
      (StrothTypeIndex.t201 m).action.φuv (dD.thetaT (hS.R_le_normalizer he.1) x)) ∧
    (∀ x, dD.thetaT (hS.R_le_normalizer he.1) ((StrothTypeIndex.t201 m).action.φt x) =
      (StrothTypeIndex.t201 m).action.φt (dD.thetaT (hS.R_le_normalizer he.1) x)) ∧
    (∀ x, dD.thetaT (hS.R_le_normalizer he.1) ((StrothTypeIndex.t201 m).action.φρ x) =
      (StrothTypeIndex.t201 m).action.φρ (dD.thetaT (hS.R_le_normalizer he.1) x)) := by
  have heN := hS.R_le_normalizer he.1
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have := dD.thetaT_comm_of_conj_mem heN dD.uv_mem he.2.1 x
    rwa [dD.thetaT_uv, dD.thetaT_uv] at this
  · have := dD.thetaT_comm_of_conj_mem heN dD.t_mem he.2.2 x
    rwa [dD.thetaT_t, dD.thetaT_t] at this
  · exact thetaT_comm_rho hS he.1 (h.t201_proj_mul_inv_mem hS hm he) x

theorem t201_D_le_R1 (hS : Local.Setting (F.S : Subgroup G) D) : D ≤ hS.R1 dD.uv dD.t :=
  fun d hd =>
    ⟨hS.D_le_R hd, (dD.crdT_cocycle_of_mem_uv hd).1, (dD.crdT_cocycle_of_mem_t hd).1⟩

theorem t201_conj_u_mem_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : dD.u⁻¹ * e * dD.u ∈ hS.R1 dD.uv dD.t :=
  ⟨h.conj_u_mem_R hS he.1, (cocycle_conj_u hS he.2.1 he.2.2).1,
    (cocycle_conj_u hS he.2.1 he.2.2).2.1⟩

theorem t201_conj_u_mul_inv_mem_of_scalar (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    {g : G} (hg : g ∈ hS.R) {y : ℤ} (hy : ∀ v, dD.thetaT (hS.R_le_normalizer hg) v = y • v) :
    dD.u⁻¹ * g * dD.u * g⁻¹ ∈ D := by
  have huS : dD.u ∈ (F.S : Subgroup G) := h.u_eq ▸ F.u_mem_S
  have := dD.conj_mem_of_thetaT_comm hS huS (hS.R_le_S hg) dD.u_mem (hS.R_le_normalizer hg)
    (fun x => by rw [hy, hy, map_zsmul])
  exact this

theorem t201_scalar_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    {e : G} (he : e ∈ hS.R1 dD.uv dD.t) (hue : dD.u⁻¹ * e * dD.u * e⁻¹ ∈ D) :
    ∃ y : ℤ, ∀ v, dD.thetaT (hS.R_le_normalizer he.1) v = y • v := by
  obtain ⟨huv, ht, hρ⟩ := h.t201_comm_R1 hS hm he
  exact t201_scalar hm _ huv ht (fun x => thetaT_comm_u hS he.1 hue x) hρ

theorem t201_thetaT_u_inv (x : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT (inv_mem dD.u_mem) x = (StrothTypeIndex.t201 m).action.φu x := by
  rw [dD.thetaT_congr (inv_mem dD.u_mem) dD.u_mem (inv_eq_of_mul_eq_one_right dD.u_sq),
    dD.thetaT_u]

theorem t201_comm_u_scalar (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    {e : G} (he : e ∈ hS.R1 dD.uv dD.t) (hue : dD.u⁻¹ * e * dD.u * e⁻¹ ∉ D) :
    e⁻¹ * (dD.u⁻¹ * e * dD.u) ∈ hS.R1 dD.uv dD.t ∧
      ∀ v, dD.thetaT (hS.R_le_normalizer
        (mul_mem (inv_mem he) (h.t201_conj_u_mem_R1 hS he)).1) v = (1 + 2 ^ (m + 1) : ℤ) • v := by
  have hg : e⁻¹ * (dD.u⁻¹ * e * dD.u) ∈ hS.R1 dD.uv dD.t :=
    mul_mem (inv_mem he) (h.t201_conj_u_mem_R1 hS he)
  refine ⟨hg, ?_⟩
  have heN := hS.R_le_normalizer he.1
  obtain ⟨huv, ht, hρ⟩ := h.t201_comm_R1 hS hm he
  have hcN : dD.u⁻¹ * e * dD.u ∈ Subgroup.normalizer (D : Set G) :=
    mul_mem (mul_mem (inv_mem dD.u_mem) heN) dD.u_mem
  have hconj : ∀ x, dD.thetaT hcN x = (StrothTypeIndex.t201 m).action.φu
      (dD.thetaT heN ((StrothTypeIndex.t201 m).action.φu x)) := fun x => by
    rw [dD.thetaT_congr hcN (mul_mem (mul_mem (inv_mem dD.u_mem) heN) dD.u_mem) rfl,
      dD.thetaT_conj heN dD.u_mem, dD.thetaT_u, t201_thetaT_u_inv]
  rcases t201_uconj hm (dD.thetaT heN) huv ht hρ (fun x hx => by
      have := congrArg (dD.thetaT (inv_mem heN)) hx
      rwa [dD.thetaT_inv_thetaT, map_zero] at this) with hθ | hθ
  · exfalso
    refine hue (dD.mem_of_thetaT_id hS ?_ (mul_mem hcN (inv_mem heN)) fun x => ?_)
    · have huS : dD.u ∈ (F.S : Subgroup G) := h.u_eq ▸ F.u_mem_S
      exact mul_mem (mul_mem (mul_mem (inv_mem huS) (hS.R_le_S he.1)) huS)
        (inv_mem (hS.R_le_S he.1))
    · rw [dD.thetaT_mul hcN (inv_mem heN), hconj, hθ, dD.thetaT_inv_thetaT]
  · intro v
    rw [dD.thetaT_congr _ (mul_mem (inv_mem heN) hcN) rfl, dD.thetaT_mul (inv_mem heN) hcN,
      hconj, hθ, dD.thetaT_thetaT_inv]

end StrothFrame.IsD

structure Normal201 {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    (hS : Local.Setting (F.S : Subgroup G) D) (dD : StrothWeakTypeData D (StrothTypeIndex.t201 m))
    (e : G) (y p : ℤ) : Prop where
  mem : e ∈ hS.R1 dD.uv dD.t
  proj : hS.proj dD.ρ e = e
  comm : dD.u * e = e * dD.u
  scalar : ∀ v, dD.thetaT (hS.R_le_normalizer mem.1) v = y • v
  ruv : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) =
    p • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 1, 1]
  rt : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) = p • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, -1, 0]

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)}

theorem exists_normal201 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) (hug : dD.u⁻¹ * g * dD.u * g⁻¹ ∈ D) :
    ∃ d ∈ D, ∃ y p : ℤ, Normal201 hS dD (g * d) y (2 * p) := by
  obtain ⟨d, hd, hp, hu⟩ := h.exists_normalized hS fix_ρ_c φu_c hm hfus hg.1
    (h.t201_proj_mul_inv_mem hS hm hg) hug
  have hmem : g * d ∈ hS.R1 dD.uv dD.t := mul_mem hg (t201_D_le_R1 hS hd)
  obtain ⟨y, hy⟩ := h.t201_scalar_R1 hS hm hmem (by
    rw [show dD.u⁻¹ * (g * d) * dD.u = dD.u⁻¹ * (dD.u * (g * d)) by rw [hu]; group]
    simpa using one_mem D)
  obtain ⟨n1, n2, n3, -⟩ := h.cocycle_normalized hS hmem hp hu
  obtain ⟨p, hp1, hp2⟩ := t201_normal_form _ _ n3 n1 n2
  exact ⟨d, hd, y, p, hmem, hp, hu, hy, hp1, hp2⟩

end StrothFrame.IsD

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (StrothTypeIndex.t201 m))

theorem t201_c_eq : (dD.c : G) = dD.ofT (Torus.ofInt _ ![1, 0, 0]) := by
  rw [← c_eq_ofInt]; rfl

theorem t201_a_eq : (dD.a : G) = dD.ofT (Torus.ofInt _ ![0, 1, 0]) := by
  rw [← a_eq_ofInt]; rfl

theorem t201_b_eq : (dD.b : G) = dD.ofT (Torus.ofInt _ ![0, 0, 1]) := by
  rw [← b_eq_ofInt]; rfl

theorem t201_c_inv_eq :
    (dD.c : G)⁻¹ = dD.ofT ((-1 : ℤ) • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) := by
  rw [dD.ofT_zsmul, zpow_neg_one, ← t201_c_eq]

theorem t201_a_mul_pow_eq (j : ℕ) :
    (dD.a : G) * (dD.a : G) ^ j =
      dD.ofT ((1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]) := by
  rw [add_zsmul, dD.ofT_add, one_zsmul, dD.ofT_zsmul, ← t201_a_eq, zpow_natCast]

theorem t201_a_inv_mul_pow_eq (j : ℕ) :
    (dD.a : G)⁻¹ * (dD.a : G) ^ j =
      dD.ofT ((-1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t201_a_eq, zpow_natCast, zpow_neg_one]

theorem t201_b_mul_pow_eq (j : ℕ) :
    (dD.b : G) * (dD.b : G) ^ j =
      dD.ofT ((1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 0, 1]) := by
  rw [add_zsmul, dD.ofT_add, one_zsmul, dD.ofT_zsmul, ← t201_b_eq, zpow_natCast]

theorem t201_b_inv_mul_pow_eq (j : ℕ) :
    (dD.b : G)⁻¹ * (dD.b : G) ^ j =
      dD.ofT ((-1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 0, 1]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t201_b_eq, zpow_natCast, zpow_neg_one]

theorem t201_cab_pow_eq (p : ℕ) :
    ((dD.c : G) * dD.a * dD.b) ^ p =
      dD.ofT ((p : ℤ) • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 1, 1]) := by
  have h : Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 1, 1] =
      Torus.ofInt _ ![1, 0, 0] + Torus.ofInt _ ![0, 1, 0] + Torus.ofInt _ ![0, 0, 1] := by
    rw [t201_add_vec, t201_add_vec]; norm_num
  rw [dD.ofT_zsmul, zpow_natCast, h, dD.ofT_add, dD.ofT_add, ← t201_c_eq, ← t201_a_eq,
    ← t201_b_eq]

theorem t201_a_pow_inv_eq (p : ℕ) :
    ((dD.a : G) ^ p)⁻¹ =
      dD.ofT ((p : ℤ) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, -1, 0]) := by
  have h : Torus.ofInt (StrothTypeIndex.t201 m).k ![0, -1, 0] =
      (-1 : ℤ) • Torus.ofInt _ ![0, 1, 0] := by
    rw [t201_zsmul_vec]; norm_num
  rw [h, smul_smul, dD.ofT_zsmul, ← t201_a_eq, mul_neg_one, zpow_neg, zpow_natCast]

end StrothWeakTypeData

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)}

theorem t201_crdT_eq_of_proj_eq (hS : Local.Setting (F.S : Subgroup G) D) {d : G} (hd : d ∈ D)
    (hp : hS.proj dD.ρ d = d) :
    ∃ l : ℤ, crdT dD.e d = l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] := by
  have hρd : dD.ρ⁻¹ * d * dD.ρ ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hd
  have h1 := hS.proj_eq_of_mem (hS.D_le_R hρd)
  rw [hp] at h1
  obtain ⟨l, hl⟩ := fix_ρ_c (crdT dD.e d) (by
    rw [← crdT_conj dD.e dD.ρ_mem dD.ρ_conj hd, ← h1])
  exact ⟨l, by rw [hl, c_eq_ofInt]⟩

theorem normal201_one (hS : Local.Setting (F.S : Subgroup G) D) : Normal201 hS dD 1 1 0 where
  mem := one_mem _
  proj := proj_rho_one hS
  comm := by rw [mul_one, one_mul]
  scalar v := by rw [one_zsmul]; exact dD.thetaT_of_mem _ (one_mem D) v
  ruv := by rw [zero_zsmul, show (1 : G)⁻¹ * dD.uv * 1 * dD.uv⁻¹ = 1 by group, crdT_one]
  rt := by rw [zero_zsmul, show (1 : G)⁻¹ * dD.t * 1 * dD.t⁻¹ = 1 by group, crdT_one]

end StrothFrame.IsD

namespace Normal201

open StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)} {hS : Local.Setting (F.S : Subgroup G) D}

theorem mul_c {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) (μ : ℤ) :
    Normal201 hS dD (e * dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]))
      y (p - 4 * μ) := by
  set d := dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) with hd_def
  have hd : d ∈ D := dD.ofT_mem _
  have hdN : d ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hd
  have hcd : crdT dD.e d = μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] :=
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
  refine ⟨mul_mem hn.mem (t201_D_le_R1 hS hd), ?_, ?_, fun v => ?_, ?_, ?_⟩
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

theorem mul {e f : G} {y p y' p' : ℤ} (he : Normal201 hS dD e y p)
    (hf : Normal201 hS dD f y' p') : Normal201 hS dD (e * f) (y * y') (y' * p + p') := by
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

theorem mem_of_dvd (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p)
    (hp : (4 : ℤ) ∣ p) : e ∈ D := by
  obtain ⟨μ, rfl⟩ := hp
  exact h.mem_of_cocycle_cob hS hn.mem.1 hn.mem.2.1 hn.mem.2.2
    (μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) (by rw [hn.ruv, cob_uv])
    (by rw [hn.rt, cob_t])

theorem mul_inv_mem (h : F.IsD D dD) {e f : G} {y p y' p' : ℤ} (he : Normal201 hS dD e y p)
    (hf : Normal201 hS dD f y' p') (hp : (4 : ℤ) ∣ p - p') : e * f⁻¹ ∈ D := by
  obtain ⟨μ, hμ⟩ := hp
  refine h.mul_inv_mem_of_cocycle_cob hS he.mem hf.mem
    (μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) ?_ ?_
  · rw [he.ruv, hf.ruv, cob_uv, ← add_zsmul]
    congr 1; linear_combination hμ
  · rw [he.rt, hf.rt, cob_t, ← add_zsmul]
    congr 1; linear_combination hμ

theorem scalar_dvd {e f : G} {y p y' p' : ℤ} (he : Normal201 hS dD e y p)
    (hf : Normal201 hS dD f y' p') (hef : e * f⁻¹ ∈ D) : (2 : ℤ) ^ (m + 2) ∣ y - y' := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  have hdN : e * f⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hef
  refine dvd_sub_of_zsmul_eq (a := 0) (c := 0) ?_
  rw [← he.scalar, ← hf.scalar, dD.thetaT_congr heN (mul_mem hdN hfN) (by group),
    dD.thetaT_mul hdN hfN, dD.thetaT_of_mem hdN hef]

theorem mul_inv_mem_of_scalar {e f : G} {y p y' p' : ℤ} (he : Normal201 hS dD e y p)
    (hf : Normal201 hS dD f y' p') (hy : (2 : ℤ) ^ (m + 2) ∣ y - y') : e * f⁻¹ ∈ D := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S he.mem.1) (inv_mem (hS.R_le_S hf.mem.1)))
    (mul_mem heN (inv_mem hfN)) fun v => ?_
  rw [dD.thetaT_mul heN (inv_mem hfN), he.scalar, zsmul_congr hy, ← hf.scalar,
    dD.thetaT_inv_thetaT]

theorem scalar_dvd_of_mem {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) (he : e ∈ D) :
    (2 : ℤ) ^ (m + 2) ∣ y - 1 :=
  hn.scalar_dvd (normal201_one hS) (by simpa using he)

theorem mem_of_scalar {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - 1) : e ∈ D := by
  simpa using hn.mul_inv_mem_of_scalar (normal201_one hS) hy

theorem eq (h : F.IsD D dD) {e f : G} {y p y' p' : ℤ} (he : Normal201 hS dD e y p)
    (hf : Normal201 hS dD f y' p') (hp : (2 : ℤ) ^ (m + 2) ∣ p - p') : e = f := by
  have hef : e * f⁻¹ ∈ D := he.mul_inv_mem h hf (dvd_trans ⟨2 ^ m, by ring⟩ hp)
  have hfN := hS.R_le_normalizer hf.mem.1
  have hpr : hS.proj dD.ρ (e * f⁻¹) = e * f⁻¹ := by
    rw [hS.proj_mul dD.ρ_mem he.mem.1 (inv_mem hf.mem.1), he.proj, proj_rho_inv hS hf.mem.1,
      hf.proj]
  obtain ⟨l, hl⟩ := t201_crdT_eq_of_proj_eq hS hef hpr
  have key := (dD.crdT_cocycle_mul hfN (dD.crdT_cocycle_of_mem_uv hef).1 hf.mem.2.1).2
  rw [show e * f⁻¹ * f = e by group, he.ruv, hf.ruv, zsmul_congr hp] at key
  have k0 : dD.thetaT hfN (crdT dD.e ((e * f⁻¹)⁻¹ * dD.uv * (e * f⁻¹) * dD.uv⁻¹)) = 0 :=
    (add_left_inj _).mp (by rw [zero_add]; exact key.symm)
  have h0 : crdT dD.e ((e * f⁻¹)⁻¹ * dD.uv * (e * f⁻¹) * dD.uv⁻¹) = 0 := by
    have := congrArg (dD.thetaT (inv_mem hfN)) k0
    rwa [dD.thetaT_inv_thetaT, map_zero] at this
  rw [(dD.crdT_cocycle_of_mem_uv hef).2, hl, φuv_c_sub] at h0
  have hl0 : l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] = 0 := by
    rw [c_zsmul_eq_zero_iff]
    exact dvd_neg.mp (dvd_of_four_mul_zsmul_w
      (by rw [show (4 * -l : ℤ) = -4 * l by ring]; exact h0))
  have h1 : e * f⁻¹ = 1 := crdT_inj dD.e hef (one_mem D) (by rw [hl, hl0, crdT_one])
  exact mul_inv_eq_one.mp h1

theorem eq_ofT (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {μ : ℤ}
    (hμ : (2 : ℤ) ^ (m + 2) ∣ p + 4 * μ) :
    e = dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) := by
  have h1 := (normal201_one hS (dD := dD)).mul_c μ
  rw [one_mul] at h1
  exact hn.eq h h1 (by rw [zero_sub, sub_neg_eq_add]; exact hμ)

theorem renorm {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {p' : ℤ} (h : (4 : ℤ) ∣ p - p') :
    ∃ d ∈ D, Normal201 hS dD (e * d) y p' := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨_, dD.ofT_mem (μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]), ?_⟩
  have := hn.mul_c μ
  rwa [show p - 4 * μ = p' by linear_combination hμ] at this

theorem c_conj_eq {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ m ∣ y - l) :
    e⁻¹ * (dD.c : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have hc : (dD.c : G) ∈ D := (dD.c).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp hc) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN hc, dD.crdT_ofT, dD.t201_c_eq, dD.crdT_ofT, hn.scalar,
    (c_zsmul_eq_iff y l).mpr hy]

theorem a_conj_eq {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - l) :
    e⁻¹ * (dD.a : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have ha : (dD.a : G) ∈ D := (dD.a).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp ha) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN ha, dD.crdT_ofT, dD.t201_a_eq, dD.crdT_ofT, hn.scalar, zsmul_congr hy]

theorem b_conj_eq {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - l) :
    e⁻¹ * (dD.b : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 0, 1]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have hb : (dD.b : G) ∈ D := (dD.b).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp hb) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN hb, dD.crdT_ofT, dD.t201_b_eq, dD.crdT_ofT, hn.scalar, zsmul_congr hy]

theorem uv_conj_eq {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {q : ℕ}
    (hq : (2 : ℤ) ^ (m + 2) ∣ p - q) :
    e⁻¹ * dD.uv * e = ((dD.c : G) * dD.a * dD.b) ^ q * dD.uv := by
  have key : e⁻¹ * dD.uv * e * dD.uv⁻¹ = ((dD.c : G) * dD.a * dD.b) ^ q := by
    rw [dD.t201_cab_pow_eq]
    exact crdT_inj dD.e hn.mem.2.1 (dD.ofT_mem _) (by rw [hn.ruv, dD.crdT_ofT, zsmul_congr hq])
  rw [← key]; group

theorem t_conj_eq {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {q : ℕ}
    (hq : (2 : ℤ) ^ (m + 2) ∣ p - q) :
    e⁻¹ * dD.t * e = ((dD.a : G) ^ q)⁻¹ * dD.t := by
  have key : e⁻¹ * dD.t * e * dD.t⁻¹ = ((dD.a : G) ^ q)⁻¹ := by
    rw [dD.t201_a_pow_inv_eq]
    exact crdT_inj dD.e hn.mem.2.2 (dD.ofT_mem _) (by rw [hn.rt, dD.crdT_ofT, zsmul_congr hq])
  rw [← key]; group

theorem u_conj_eq {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) : e⁻¹ * dD.u * e = dD.u := by
  rw [mul_assoc, hn.comm]; group

theorem sq_eq (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) {μ : ℤ}
    (hμ : (2 : ℤ) ^ (m + 2) ∣ (y + 1) * p + 4 * μ) :
    e * e = dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) :=
  (hn.mul hn).eq_ofT h (by convert hμ using 1; ring)

theorem rel34i (h : F.IsD D dD) {e : G} {y : ℤ} (hn : Normal201 hS dD e y 2)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ (m + 1))) : Rel34i dD e (2 ^ (m + 1)) := by
  obtain ⟨k, hk⟩ := hy
  have hy' : (2 : ℤ) ^ (m + 2) ∣ y - (1 + ((2 ^ (m + 1) : ℕ) : ℤ)) :=
    ⟨k, by push_cast; exact hk⟩
  have hq : (2 : ℤ) ^ (m + 2) ∣ 2 - ((2 : ℕ) : ℤ) := by norm_num
  refine ⟨?_, ?_, ?_, ?_, hn.uv_conj_eq hq, hn.t_conj_eq hq, hn.u_conj_eq⟩
  · rw [hn.c_conj_eq (l := 1) ⟨4 * k + 2, by linear_combination hk⟩, one_zsmul, ← dD.t201_c_eq]
  · rw [hn.a_conj_eq hy', dD.t201_a_mul_pow_eq]
  · rw [hn.b_conj_eq hy', dD.t201_b_mul_pow_eq]
  · rw [hn.sq_eq h (μ := -1) ⟨1 + 2 * k, by linear_combination 2 * hk⟩, dD.t201_c_inv_eq]

theorem rel34inv {e : G} {y : ℤ} (hn : Normal201 hS dD e y 2) (j : ℕ)
    (hj : (2 : ℤ) ^ m ∣ j) (hy : (2 : ℤ) ^ (m + 2) ∣ y - (-1 + j)) (hs : e * e = 1) :
    Rel34inv dD e j 1 2 := by
  have hc : (2 : ℤ) ^ m ∣ y - (-1) := by
    have h1 : (2 : ℤ) ^ m ∣ y - (-1 + j) := dvd_trans (pow_dvd_pow 2 (by omega)) hy
    have := dvd_add h1 hj
    rwa [show y - (-1 + (j : ℤ)) + j = y - (-1) by ring] at this
  have hq : (2 : ℤ) ^ (m + 2) ∣ 2 - ((2 : ℕ) : ℤ) := by norm_num
  refine ⟨?_, ?_, ?_, hs, hn.uv_conj_eq hq, hn.t_conj_eq hq, hn.u_conj_eq⟩
  · rw [hn.c_conj_eq hc, dD.t201_c_inv_eq]
  · rw [hn.a_conj_eq hy, dD.t201_a_inv_mul_pow_eq]
  · rw [hn.b_conj_eq hy, dD.t201_b_inv_mul_pow_eq]

end Normal201

end CFSG.CGT.Stroth77
