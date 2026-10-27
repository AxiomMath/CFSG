module

public import CFSG.CGT.Stroth77.Stroth34Layer
public import CFSG.CGT.Stroth77.Stroth34T200H1
public import CFSG.CGT.Stroth77.Stroth34T200Facts
public import CFSG.CGT.Stroth77.Stroth34Arith

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Stroth34T200

namespace Stroth34T200

variable {m : ℕ}

theorem zsmul_congr {y y' : ℤ} (h : (2 : ℤ) ^ (m + 2) ∣ y - y')
    (x : Torus (StrothTypeIndex.t200 m).k) : y • x = y' • x := by
  obtain ⟨a, b, c, rfl⟩ := t200_exists_vec x
  rw [t200_zsmul_vec, t200_zsmul_vec, t200_vec_eq_iff]
  obtain ⟨k, hk⟩ := h
  refine ⟨⟨-(k * 4) * a, ?_⟩, ⟨-k * b, ?_⟩, ⟨-k * c, ?_⟩⟩
  · rw [pow_add] at hk; linear_combination (-a) * hk
  · linear_combination (-b) * hk
  · linear_combination (-c) * hk

theorem φuv_c_sub (l : ℤ) :
    (StrothTypeIndex.t200 m).action.φuv (l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) -
        l • Torus.ofInt _ ![1, 0, 0] = (-4 * l) • Torus.ofInt _ ![1, 1, 1] := by
  rw [t200_zsmul_vec, t200_φuv_vec, t200_sub_vec, t200_zsmul_vec, t200_vec_eq_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

theorem φt_c_sub (l : ℤ) :
    (StrothTypeIndex.t200 m).action.φt (l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) -
        l • Torus.ofInt _ ![1, 0, 0] = (-4 * l) • Torus.ofInt _ ![0, -1, 0] := by
  rw [t200_zsmul_vec, t200_φt_vec, t200_sub_vec, t200_zsmul_vec, t200_vec_eq_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

theorem c_eq_ofInt : (Torus.c : Torus (StrothTypeIndex.t200 m).k) = Torus.ofInt _ ![1, 0, 0] := by
  show gen _ 0 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem φρ_c : (StrothTypeIndex.t200 m).action.φρ (Torus.c : Torus (StrothTypeIndex.t200 m).k) =
    Torus.c := by
  rw [c_eq_ofInt, t200_φρ_vec, t200_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φu_c : (StrothTypeIndex.t200 m).action.φu (Torus.c : Torus (StrothTypeIndex.t200 m).k) =
    Torus.c := by
  rw [c_eq_ofInt, t200_φu_vec]

theorem fix_ρ_c (x : Torus (StrothTypeIndex.t200 m).k)
    (h : (StrothTypeIndex.t200 m).action.φρ x = x) : ∃ l : ℤ, x = l • Torus.c := by
  obtain ⟨l, hl⟩ := t200_fix_ρ x h
  exact ⟨l, by rw [hl, c_eq_ofInt]⟩

theorem dvd_sub_of_zsmul_eq {y y' a c : ℤ}
    (h : y • Torus.ofInt (StrothTypeIndex.t200 m).k ![a, 1, c] = y' • Torus.ofInt _ ![a, 1, c]) :
    (2 : ℤ) ^ (m + 2) ∣ y - y' := by
  rw [t200_zsmul_vec, t200_zsmul_vec, t200_vec_eq_iff] at h
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h
  exact ⟨-k, by linear_combination -hk⟩

theorem cob_uv (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] -
        (StrothTypeIndex.t200 m).action.φuv (l • Torus.ofInt _ ![1, 0, 0]) =
      (4 * l) • Torus.ofInt _ ![1, 1, 1] := by
  rw [t200_zsmul_vec, t200_φuv_vec, t200_sub_vec, t200_zsmul_vec, t200_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem cob_t (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] -
        (StrothTypeIndex.t200 m).action.φt (l • Torus.ofInt _ ![1, 0, 0]) =
      (4 * l) • Torus.ofInt _ ![0, -1, 0] := by
  rw [t200_zsmul_vec, t200_φt_vec, t200_sub_vec, t200_zsmul_vec, t200_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem dvd_mul_self_sub_one_of_one_add {y : ℤ}
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ (m + 1))) : (2 : ℤ) ^ (m + 2) ∣ y * y - 1 := by
  obtain ⟨k, hk⟩ := hy
  exact ⟨(1 + 2 * k) * (1 + 2 ^ m + 2 ^ (m + 1) * k), by
    rw [show y = 1 + 2 ^ (m + 1) + 2 ^ (m + 2) * k by linear_combination hk]; ring⟩

end Stroth34T200

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t200 m)}

theorem t200_proj_mul_inv_mem (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : hS.proj dD.ρ e * e⁻¹ ∈ D :=
  h.proj_rho_mul_inv_mem hS (fun _ _ h1 h2 h3 => t200_rho_triv _ _ h1 h2 h3) he

theorem t200_conj_u_mul_inv_mem (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e : G} (he : e ∈ hS.R1 dD.uv dD.t) : dD.u⁻¹ * e * dD.u * e⁻¹ ∈ D :=
  h.conj_u_mul_inv_mem hS (fun _ _ h1 h2 h3 => t200_u_triv hm _ _ h1 h2 h3) he

theorem t200_scalar_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    {e : G} (he : e ∈ hS.R1 dD.uv dD.t) :
    ∃ y : ℤ, ∀ v, dD.thetaT (hS.R_le_normalizer he.1) v = y • v := by
  obtain ⟨heR, huv, ht⟩ := he
  have heN := hS.R_le_normalizer heR
  refine t200_scalar _ (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · have := dD.thetaT_comm_of_conj_mem heN dD.uv_mem huv x
    rwa [dD.thetaT_uv, dD.thetaT_uv] at this
  · have := dD.thetaT_comm_of_conj_mem heN dD.t_mem ht x
    rwa [dD.thetaT_t, dD.thetaT_t] at this
  · exact thetaT_comm_u hS heR (h.t200_conj_u_mul_inv_mem hS hm ⟨heR, huv, ht⟩) x
  · exact thetaT_comm_rho hS heR (h.t200_proj_mul_inv_mem hS ⟨heR, huv, ht⟩) x

theorem D_le_R1 (hS : Local.Setting (F.S : Subgroup G) D) : D ≤ hS.R1 dD.uv dD.t := fun d hd =>
  ⟨hS.D_le_R hd, (dD.crdT_cocycle_of_mem_uv hd).1, (dD.crdT_cocycle_of_mem_t hd).1⟩

theorem t200_conj_mem_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    {g e : G} (hg : g ∈ hS.R) (he : e ∈ hS.R1 dD.uv dD.t) :
    g⁻¹ * e * g ∈ hS.R1 dD.uv dD.t := by
  obtain ⟨y, hy⟩ := h.t200_scalar_R1 hS hm he
  have hgN := hS.R_le_normalizer hg
  have heN := hS.R_le_normalizer he.1
  have hcR : g⁻¹ * e * g ∈ hS.R := mul_mem (mul_mem (inv_mem hg) he.1) hg
  have hcN := hS.R_le_normalizer hcR
  have h1 : ∀ v, dD.thetaT hcN v = dD.thetaT heN v := fun v => by
    rw [dD.thetaT_congr hcN (mul_mem (mul_mem (inv_mem hgN) heN) hgN) rfl, dD.thetaT_conj heN hgN]
    simp only [hy]
    rw [map_zsmul, dD.thetaT_thetaT_inv]
  have h2 : g⁻¹ * e * g * e⁻¹ ∈ D := by
    refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S hcR) (inv_mem (hS.R_le_S he.1)))
      (mul_mem hcN (inv_mem heN)) fun v => ?_
    rw [dD.thetaT_mul hcN (inv_mem heN), h1, dD.thetaT_inv_thetaT]
  have := mul_mem (D_le_R1 hS h2) he
  simpa using this

theorem t200_R_le_normalizer_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) : hS.R ≤ Subgroup.normalizer ((hS.R1 dD.uv dD.t : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro e
  refine ⟨fun he => h.t200_conj_mem_R1 hS hm hg he, fun he => ?_⟩
  have := h.t200_conj_mem_R1 hS hm (inv_mem hg) he
  rwa [show g⁻¹⁻¹ * (g⁻¹ * e * g) * g⁻¹ = e by group] at this

end StrothFrame.IsD

structure Normal200 {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    (hS : Local.Setting (F.S : Subgroup G) D) (dD : StrothWeakTypeData D (StrothTypeIndex.t200 m))
    (e : G) (y p : ℤ) : Prop where
  mem : e ∈ hS.R1 dD.uv dD.t
  proj : hS.proj dD.ρ e = e
  comm : dD.u * e = e * dD.u
  scalar : ∀ v, dD.thetaT (hS.R_le_normalizer mem.1) v = y • v
  ruv : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) =
    p • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 1, 1]
  rt : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) = p • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0]

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t200 m)}

theorem exists_normal200 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) : ∃ d ∈ D, ∃ y p : ℤ, Normal200 hS dD (g * d) y p := by
  obtain ⟨d, hd, hp, hu⟩ := h.exists_normalized hS fix_ρ_c φu_c hm hfus hg.1
    (h.t200_proj_mul_inv_mem hS hg) (h.t200_conj_u_mul_inv_mem hS hm hg)
  have hmem : g * d ∈ hS.R1 dD.uv dD.t := mul_mem hg (D_le_R1 hS hd)
  obtain ⟨y, hy⟩ := h.t200_scalar_R1 hS hm hmem
  obtain ⟨n1, n2, n3, -⟩ := h.cocycle_normalized hS hmem hp hu
  obtain ⟨p, hp1, hp2⟩ := t200_normal_form _ _ n3 n1 n2
  exact ⟨d, hd, y, p, hmem, hp, hu, hy, hp1, hp2⟩

theorem normal200_sq_of_one_add (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (heD : e ∉ D)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ (m + 1))) :
    e * e ∈ D ∧
      (∃ l : ℤ, crdT dD.e (e * e) = l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) ∧
      (4 : ℤ) ∣ p - 2 := by
  have heR := hn.mem.1
  have heN := hS.R_le_normalizer heR
  have hsq : e * e ∈ D := by
    refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S heR) (hS.R_le_S heR)) (mul_mem heN heN)
      fun v => ?_
    rw [dD.thetaT_mul heN heN, hn.scalar, hn.scalar, smul_smul,
      zsmul_congr (dvd_mul_self_sub_one_of_one_add hy), one_zsmul]
  obtain ⟨s1, s2, -⟩ := sq_normalized hS hn.mem hn.proj hsq
  obtain ⟨l, hl⟩ := fix_ρ_c _ s1
  rw [c_eq_ofInt] at hl
  refine ⟨hsq, ⟨l, hl⟩, ?_⟩
  rw [hl, hn.ruv, hn.scalar, smul_smul, φuv_c_sub, ← add_zsmul] at s2
  have h1 := dvd_sub_of_zsmul_eq s2
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k, hk⟩ := hy
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, p = 2 * Y :=
    ⟨_, mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      (show 2 * p = 2 * (2 * (-(2 * 2 ^ m' * k1) - 2 * 2 ^ m' * k * p - l - 2 ^ m' * p)) by
        linear_combination (-1 : ℤ) * hk1 - p * hk)⟩
  rcases Int.even_or_odd Y with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
  ·
    exfalso
    refine heD (h.mem_of_cocycle_cob hS heR hn.mem.2.1 hn.mem.2.2
      (μ • Torus.ofInt (StrothTypeIndex.t200 (m' + 1)).k ![1, 0, 0]) ?_ ?_)
    · rw [hn.ruv, cob_uv, hY, hμ]; congr 1; ring
    · rw [hn.rt, cob_t, hY, hμ]; congr 1; ring
  · exact ⟨μ, by rw [hY, hμ]; ring⟩

theorem t200_false_of_conj (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G)) (hx2 : x * x = 1)
    {φ : Torus (StrothTypeIndex.t200 m).k →+ Torus (StrothTypeIndex.t200 m).k}
    (hφ : ∀ v, dD.thetaT hxN v = φ v)
    (hexp : ∀ w, φ w = w → (2 ^ (m + 1) : ℤ) • w = 0)
    (htw : ∀ y : ℤ, (y = -1 ∨ y = -1 + 2 ^ (m + 1)) →
      ∃ v, y • φ v = v ∧ (2 ^ (m + 1) : ℤ) • v ≠ 0)
    (r₁ : Torus (StrothTypeIndex.t200 m).k)
    (hr : ∀ {e : G} {y p : ℤ}, Normal200 hS dD e y p →
      e⁻¹ * x * e * x⁻¹ ∈ D ∧ crdT dD.e (e⁻¹ * x * e * x⁻¹) = p • r₁)
    (hnoinv : ∀ q : ℤ, (4 : ℤ) ∣ q - 2 → ∀ (l : ℤ) (d : Torus (StrothTypeIndex.t200 m).k),
      (1 + 2 ^ (m + 1) : ℤ) • d + φ d + l • Torus.ofInt _ ![1, 0, 0] + q • r₁ ≠ 0)
    {f : G} (hfR : f ∈ hS.R) (hg : f⁻¹ * x * f * x⁻¹ ∈ hS.R1 dD.uv dD.t)
    (hgD : f⁻¹ * x * f * x⁻¹ ∉ D) : False := by
  set g := f⁻¹ * x * f * x⁻¹ with hgdef
  have hfN := hS.R_le_normalizer hfR
  have hgN := hS.R_le_normalizer hg.1
  have hxf : f⁻¹ * x * f = g * x := by rw [hgdef]; group
  have hgx1 : g * x * (g * x) = 1 := by
    rw [← hxf]
    calc f⁻¹ * x * f * (f⁻¹ * x * f) = f⁻¹ * (x * x) * f := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨y, hy⟩ := h.t200_scalar_R1 hS hm hg
  have hφφ : ∀ v, φ (φ v) = v := fun v => by
    rw [← hφ, ← hφ, ← dD.thetaT_mul hxN hxN]
    exact dD.thetaT_of_mem _ (by rw [hx2]; exact one_mem _) v
  have hy2 : (2 : ℤ) ^ (m + 2) ∣ y ^ 2 - 1 := by
    have hgxN : g * x ∈ Subgroup.normalizer (D : Set G) := mul_mem hgN hxN
    have key := dD.thetaT_of_mem (mul_mem hgxN hgxN) (by rw [hgx1]; exact one_mem D)
      (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0])
    rw [dD.thetaT_mul hgxN hgxN, dD.thetaT_mul hgN hxN, dD.thetaT_mul hgN hxN, hy, hφ, hy, hφ,
      map_zsmul, hφφ, smul_smul] at key
    rw [sq]
    exact dvd_sub_of_zsmul_eq (y' := 1) (by rwa [one_zsmul])
  rcases Stroth34Arith.sq_cases' hy2 with h1 | h1 | h1 | h1
  ·
    exact hgD (dD.mem_of_thetaT_id hS (hS.R_le_S hg.1) hgN fun v => by
      rw [hy, zsmul_congr h1, one_zsmul])
  ·
    obtain ⟨v, hv, hv0⟩ := htw (-1) (Or.inl rfl)
    exact dD.false_of_twist_fix hfN hxN hφ hgN hxf (fun v => by
      rw [hy]; exact zsmul_congr (by rwa [sub_neg_eq_add]) v) hexp hv hv0
  ·
    obtain ⟨d, hd, y', p, hn⟩ := h.exists_normal200 hS hm hfus hg
    have heN := hS.R_le_normalizer hn.mem.1
    have hy' : (2 : ℤ) ^ (m + 2) ∣ y' - (1 + 2 ^ (m + 1)) := by
      have e1 : y' • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0] =
          y • Torus.ofInt _ ![0, 1, 0] := by
        rw [← hn.scalar, dD.thetaT_congr heN (mul_mem hgN (Subgroup.le_normalizer hd)) rfl,
          dD.thetaT_mul hgN (Subgroup.le_normalizer hd), dD.thetaT_of_mem _ hd, hy]
      have := dvd_add (dvd_sub_of_zsmul_eq e1) h1
      rwa [sub_add_sub_cancel] at this
    have heD : g * d ∉ D := fun h' => hgD (by simpa using mul_mem h' (inv_mem hd))
    obtain ⟨hsq, ⟨l, hl⟩, hp4⟩ := h.normal200_sq_of_one_add hS hm hn heD hy'
    have key := (dD.crdT_sq_coset heN hxN hx2 hφ (hr hn).1 hsq (inv_mem hd)).2
    rw [show g * d * d⁻¹ * x = g * x by group, hgx1, crdT_one, hl, hn.scalar, (hr hn).2] at key
    apply hnoinv p hp4 l (crdT dD.e d⁻¹)
    rw [zsmul_congr (dvd_sub_comm.mp hy') (crdT dD.e d⁻¹), key]
    abel
  ·
    obtain ⟨v, hv, hv0⟩ := htw (-1 + 2 ^ (m + 1)) (Or.inr rfl)
    exact dD.false_of_twist_fix hfN hxN hφ hgN hxf (fun v => by rw [hy]; exact zsmul_congr h1 v)
      hexp hv hv0

theorem t200_R1_eq_R (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) :
    hS.R1 dD.uv dD.t = hS.R := by
  refine le_antisymm (fun e he => he.1) fun f hfR => ?_
  by_contra hf
  have hlt : hS.R1 dD.uv dD.t < hS.R :=
    lt_of_le_of_ne (fun e he => he.1) fun heq => hf (by rw [heq]; exact hfR)
  obtain ⟨f, hfR, hfR1, huv, ht⟩ :=
    h.exists_mem_R_conj_mem_R1 hS (h.t200_R_le_normalizer_R1 hS hm) hlt
  by_cases huvD : f⁻¹ * dD.uv * f * dD.uv⁻¹ ∈ D
  · by_cases htD : f⁻¹ * dD.t * f * dD.t⁻¹ ∈ D
    · exact hfR1 ⟨hfR, huvD, htD⟩
    · exact h.t200_false_of_conj hS hm hfus dD.t_mem dD.t_sq dD.thetaT_t t200_fix_t_exp
        (fun _ hy => t200_twist_fix_t hm hy) _ (fun hn => ⟨hn.mem.2.2, hn.rt⟩)
        (fun _ hq l d => t200_noInv_t hm hq l d) hfR ht htD
  · exact h.t200_false_of_conj hS hm hfus dD.uv_mem dD.uv_sq dD.thetaT_uv t200_fix_uv_exp
      (fun _ hy => t200_twist_fix_uv hm hy) _ (fun hn => ⟨hn.mem.2.1, hn.ruv⟩)
      (fun _ hq l d => t200_noInv_uv hm hq l d) hfR huv huvD

end StrothFrame.IsD

end CFSG.CGT.Stroth77
