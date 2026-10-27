module

public import CFSG.CGT.Stroth77.AmbientSplit

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

theorem two_pow_dvd_of_dvd_two_mul {t n : ℕ} (h : 2 ^ (t + 1) ∣ 2 * n) : 2 ^ t ∣ n := by
  have hsplit : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
  rw [hsplit] at h
  exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp h

theorem zmod_two_mul_eq_zero_iff {k : ℕ} (hk : 1 ≤ k) (x : ZMod (2 ^ k)) :
    2 * x = 0 ↔ x = 0 ∨ x = ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  rw [show t + 1 - 1 = t from by omega]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  ·
    have h2z : (2 : ZMod (2 ^ 1)) = 0 := by simpa using ZMod.natCast_self 2
    have hx : ∀ y : ZMod (2 ^ 1), y = 0 ∨ y = ((1 : ℕ) : ZMod (2 ^ 1)) := by
      intro y
      obtain ⟨n, hnlt, hny⟩ : ∃ n : ℕ, n < 2 ∧ ((n : ℕ) : ZMod (2 ^ 1)) = y :=
        ⟨y.val, ZMod.val_lt y, ZMod.natCast_zmod_val y⟩
      interval_cases n
      · left; exact hny.symm
      · right; exact hny.symm
    rw [show (2 ^ 0 : ℕ) = 1 from rfl, h2z, zero_mul]
    exact ⟨fun _ => hx x, fun _ => rfl⟩
  ·
    haveI : NeZero (2 ^ (t + 1)) := ⟨by positivity⟩
    constructor
    · intro h
      have hv : (2 * x).val = 0 := by rw [h]; exact ZMod.val_zero
      rw [ZMod.val_mul] at hv
      have h2v : (2 : ZMod (2 ^ (t + 1))).val = 2 := by
        rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt]
        have h1 : 1 < 2 ^ t := by
          calc 1 < 2 ^ 1 := by norm_num
            _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
        calc 2 = 2 * 1 := by ring
          _ < 2 * 2 ^ t := by nlinarith
          _ = 2 ^ (t + 1) := by ring
      rw [h2v] at hv
      have hxlt : x.val < 2 ^ (t + 1) := ZMod.val_lt x
      have hsplit : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
      have hdvd : 2 ^ (t + 1) ∣ 2 * x.val := Nat.dvd_of_mod_eq_zero hv
      have hdvd' : 2 ^ t ∣ x.val := two_pow_dvd_of_dvd_two_mul hdvd
      obtain ⟨c, hc⟩ := hdvd'
      have hc2 : c < 2 := by
        have hlt : x.val < 2 * 2 ^ t := by
          calc x.val < 2 ^ (t + 1) := hxlt
            _ = 2 * 2 ^ t := hsplit
        nlinarith [Nat.one_le_two_pow (n := t)]
      interval_cases c
      · left
        have hzero : x.val = 0 := by rw [hc]; ring
        rw [← ZMod.natCast_zmod_val x, hzero]
        simp
      · right
        have hone : x.val = 2 ^ t := by rw [hc]; ring
        rw [← ZMod.natCast_zmod_val x, hone]
    · rintro (rfl | rfl)
      · simp
      · have h2 : (2 : ZMod (2 ^ (t + 1))) * ((2 ^ t : ℕ) : ZMod (2 ^ (t + 1))) =
            ((2 * 2 ^ t : ℕ) : ZMod (2 ^ (t + 1))) := by push_cast; ring
        rw [h2, show 2 * 2 ^ t = 2 ^ (t + 1) from by ring]
        exact ZMod.natCast_self _

namespace StrothTypeData

variable {B : Subgroup S} {τ : StrothTypeIndex}

@[expose] noncomputable def ec (D : StrothTypeData B τ) (x : B) : Torus τ.k :=
  D.e (Additive.ofMul x)

theorem ec_injective (D : StrothTypeData B τ) : Function.Injective D.ec := by
  intro x y h
  exact Additive.ofMul.injective (D.e.injective h)

@[simp]
theorem ec_mul (D : StrothTypeData B τ) (x y : B) : D.ec (x * y) = D.ec x + D.ec y := by
  simp [ec, ofMul_mul, map_add]

@[simp]
theorem ec_one (D : StrothTypeData B τ) : D.ec 1 = 0 := by
  simp [ec]

@[simp]
theorem ec_inv (D : StrothTypeData B τ) (x : B) : D.ec x⁻¹ = -D.ec x := by
  simp [ec, ofMul_inv]

@[simp]
theorem ec_zpow (D : StrothTypeData B τ) (x : B) (n : ℤ) : D.ec (x ^ n) = n • D.ec x := by
  simp [ec, ofMul_zpow]

theorem ec_eq_zero_iff (D : StrothTypeData B τ) {x : B} : D.ec x = 0 ↔ x = 1 := by
  constructor
  · intro h
    have h1 : x = 1 := D.ec_injective (by rw [h, D.ec_one])
    exact h1
  · rintro rfl
    exact D.ec_one

@[simp]
theorem ec_c (D : StrothTypeData B τ) : D.ec D.c = Torus.c := by
  simp [ec, StrothTypeData.c, Torus.c]

@[simp]
theorem ec_a (D : StrothTypeData B τ) : D.ec D.a = Torus.a := by
  simp [ec, StrothTypeData.a, Torus.a]

@[simp]
theorem ec_b (D : StrothTypeData B τ) : D.ec D.b = Torus.b := by
  simp [ec, StrothTypeData.b, Torus.b]

end StrothTypeData

theorem matAct_zsmul_gens {k : Fin 3 → ℕ} (M : IntMat) (hM : Compat k M) (i j l : ℤ) :
    matAct k M hM (i • gen k 0 + j • gen k 1 + l • gen k 2) =
      (M 0 0 * i + M 0 1 * j + M 0 2 * l) • gen k 0 +
      (M 1 0 * i + M 1 1 * j + M 1 2 * l) • gen k 1 +
      (M 2 0 * i + M 2 1 * j + M 2 2 * l) • gen k 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, matAct_gen_eq, matAct_gen_eq,
    matAct_gen_eq]
  funext t
  fin_cases t <;> simp [gen, Pi.single_apply, zsmul_eq_mul, add_mul, mul_add] <;> ring


theorem conjBy_val {H : Subgroup S} {g : S} (hg : g ∈ Subgroup.normalizer H) (x : H) :
    (conjBy hg x : S) = g⁻¹ * (x : S) * g := rfl

theorem conjBy_mul {H : Subgroup S} {g : S} (hg : g ∈ Subgroup.normalizer H) (x y : H) :
    conjBy hg (x * y) = conjBy hg x * conjBy hg y := by
  apply Subtype.ext
  simp only [conjBy_val, Subgroup.coe_mul]
  group

theorem conjBy_one {H : Subgroup S} {g : S} (hg : g ∈ Subgroup.normalizer H) :
    conjBy hg (1 : H) = 1 := by
  apply Subtype.ext
  simp only [conjBy_val, Subgroup.coe_one]
  group

theorem conjBy_inclusion {g : S} (hBC : B ≤ C) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : B) :
    conjBy hgC (Subgroup.inclusion hBC x) = Subgroup.inclusion hBC (conjBy hgB x) := by
  apply Subtype.ext
  rfl

noncomputable abbrev Φuv (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k :=
  (StrothTypeIndex.action (StrothTypeIndex.t100 m)).φuv

noncomputable abbrev Φt (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k :=
  (StrothTypeIndex.action (StrothTypeIndex.t100 m)).φt

noncomputable abbrev Φu (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k :=
  (StrothTypeIndex.action (StrothTypeIndex.t100 m)).φu

noncomputable abbrev Φρ (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k :=
  (StrothTypeIndex.action (StrothTypeIndex.t100 m)).φρ

theorem Φuv_eq (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φuv D = matAct (Type100.k m) Type100.uvM (Type100.compat_uv m) := rfl

theorem Φt_eq (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φt D = matAct (Type100.k m) Type100.tM (Type100.compat_t m) := rfl

theorem Φu_eq (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φu D = matAct (Type100.k m) Type100.uM (Type100.compat_u m) := rfl

theorem Φρ_eq (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φρ D = matAct (Type100.k m) Type100.ρM (Type100.compat_rho m) := rfl

theorem ec_conj_u (D : StrothTypeData B (StrothTypeIndex.t100 m)) (x : B) :
    D.ec (conjBy D.u_mem x) = Φu D (D.ec x) :=
  D.u_conj x

theorem ec_conj_t (D : StrothTypeData B (StrothTypeIndex.t100 m)) (x : B) :
    D.ec (conjBy D.t_mem x) = Φt D (D.ec x) :=
  D.t_conj x

theorem ec_conj_ρ (D : StrothTypeData B (StrothTypeIndex.t100 m)) (x : B) :
    D.ec (conjBy D.ρ_mem x) = Φρ D (D.ec x) :=
  D.ρ_conj x

theorem ec_conj_uv (D : StrothTypeData B (StrothTypeIndex.t100 m)) (x : B) :
    D.ec (conjBy D.uv_mem x) = Φuv D (D.ec x) :=
  D.uv_conj x

section Cocycle

theorem exists_conj_eq (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (g : S)
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) :
    ∃ b : B, conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b := by
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  have hyC : (conjBy hgC (⟨d, hdC⟩ : C) : S) ∈ C := (conjBy hgC _).2
  have hyB : (conjBy hgC (⟨d, hdC⟩ : C) : S) ∉ B := by
    intro hmem
    exact hdB ((Subgroup.mem_normalizer_iff''.mp hgB d).mpr hmem)
  rcases mem_or_exists_mul_of_index_two hdC hdB hindex hyC with hB | ⟨b, hbB, hb⟩
  · exact (hyB hB).elim
  · exact ⟨⟨b, hbB⟩, Subtype.ext hb⟩

noncomputable def bU (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem)

noncomputable def bT (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.t (hL D.t_mem_L) D.t_mem)

noncomputable def bR (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.ρ (hL D.ρ_mem_L) D.ρ_mem)

noncomputable def bUV (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.uv (hL D.uv_mem_L) D.uv_mem)

theorem conj_eq_bU (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bU D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem)

theorem conj_eq_bT (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bT D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.t (hL D.t_mem_L) D.t_mem)

theorem conj_eq_bR (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bR D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.ρ (hL D.ρ_mem_L) D.ρ_mem)

theorem conj_eq_bUV (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bUV D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.uv (hL D.uv_mem_L) D.uv_mem)

theorem mul_comm_C (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (x y : C) : x * y = y * x :=
  comm_of_le_centralizer D hBC hC hrel x y

theorem dC_sq (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C) {d : S}
    (hdC : d ∈ C) (hd2 : d * d = (D.c : S)) :
    (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ = Subgroup.inclusion hBC D.c :=
  Subtype.ext hd2

theorem conj_dC_mul {g : S} (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b) (β : B) :
    conjBy hgC (⟨d, hdC⟩ * Subgroup.inclusion hBC β) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (b * conjBy hgB β) := by
  rw [conjBy_mul, hb, conjBy_inclusion, mul_assoc, ← map_mul]

theorem sq_rel (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S)) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {b β : B} (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    (hβ : conjBy hgB D.c = D.c * β) :
    (2 : ℤ) • D.ec b = D.ec β := by
  letI : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := fun x y => mul_comm_C D hBC hC hrel x y }
  have hsq : (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ * Subgroup.inclusion hBC (b * b) =
      Subgroup.inclusion hBC (conjBy hgB D.c) := by
    calc (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ * Subgroup.inclusion hBC (b * b)
        = ((⟨d, hdC⟩ : C) * Subgroup.inclusion hBC b) *
            (⟨d, hdC⟩ * Subgroup.inclusion hBC b) := by
          rw [map_mul]
          ac_rfl
      _ = conjBy hgC (⟨d, hdC⟩ : C) * conjBy hgC (⟨d, hdC⟩ : C) := by rw [hb]
      _ = conjBy hgC ((⟨d, hdC⟩ : C) * ⟨d, hdC⟩) := (conjBy_mul hgC _ _).symm
      _ = conjBy hgC (Subgroup.inclusion hBC D.c) := by rw [dC_sq D hBC hdC hd2]
      _ = Subgroup.inclusion hBC (conjBy hgB D.c) := conjBy_inclusion hBC hgC hgB D.c
  have hBB : D.c * (b * b) = conjBy hgB D.c := by
    apply Subgroup.inclusion_injective hBC
    rw [map_mul]
    rw [show Subgroup.inclusion hBC D.c = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ from
      (dC_sq D hBC hdC hd2).symm]
    exact hsq
  have h1 : D.ec (D.c * (b * b)) = D.ec (D.c * β) := by rw [hBB, hβ]
  rw [D.ec_mul, D.ec_mul, D.ec_mul] at h1
  rw [two_zsmul]
  exact add_left_cancel h1

theorem inv_rel (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    (hg2 : g * g = 1)
    (φ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (hφ : ∀ x : B, D.ec (conjBy hgB x) = φ (D.ec x)) :
    D.ec b + φ (D.ec b) = 0 := by
  have h2 : conjBy hgC (conjBy hgC (⟨d, hdC⟩ : C)) = ⟨d, hdC⟩ := by
    apply Subtype.ext
    show g⁻¹ * (g⁻¹ * (d : S) * g) * g = d
    calc g⁻¹ * (g⁻¹ * (d : S) * g) * g = (g * g)⁻¹ * (d : S) * (g * g) := by group
      _ = d := by rw [hg2]; group
  rw [hb, conj_dC_mul hBC hdC hgC hgB hb] at h2
  have h3 : Subgroup.inclusion hBC (b * conjBy hgB b) = 1 := by
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) h2
    simpa [mul_assoc] using h4
  have h4 : b * conjBy hgB b = 1 := by
    have h3' : Subgroup.inclusion hBC (b * conjBy hgB b) = Subgroup.inclusion hBC (1 : B) := by
      simpa using h3
    have := Subgroup.inclusion_injective hBC h3'
    simpa using this
  have h5 := congrArg D.ec h4
  rw [D.ec_mul, D.ec_one, hφ] at h5
  exact h5

theorem inv_rel_three (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    (hg3 : g * g * g = 1)
    (φ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (hφ : ∀ x : B, D.ec (conjBy hgB x) = φ (D.ec x)) :
    D.ec b + φ (D.ec b) + φ (φ (D.ec b)) = 0 := by
  have h2 : conjBy hgC (conjBy hgC (conjBy hgC (⟨d, hdC⟩ : C))) = ⟨d, hdC⟩ := by
    apply Subtype.ext
    show g⁻¹ * (g⁻¹ * (g⁻¹ * (d : S) * g) * g) * g = d
    calc g⁻¹ * (g⁻¹ * (g⁻¹ * (d : S) * g) * g) * g
        = (g * g * g)⁻¹ * (d : S) * (g * g * g) := by group
      _ = d := by rw [hg3]; group
  rw [hb] at h2
  rw [conj_dC_mul hBC hdC hgC hgB hb] at h2
  rw [conj_dC_mul hBC hdC hgC hgB hb] at h2
  rw [conjBy_mul] at h2
  have h3 : Subgroup.inclusion hBC (b * (conjBy hgB b * conjBy hgB (conjBy hgB b))) = 1 := by
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) h2
    simpa [mul_assoc] using h4
  have h4 : b * (conjBy hgB b * conjBy hgB (conjBy hgB b)) = 1 := by
    have h3' : Subgroup.inclusion hBC (b * (conjBy hgB b * conjBy hgB (conjBy hgB b))) =
        Subgroup.inclusion hBC (1 : B) := by
      simpa using h3
    have := Subgroup.inclusion_injective hBC h3'
    simpa using this
  have h5 := congrArg D.ec h4
  simp only [D.ec_mul, D.ec_one, hφ] at h5
  simpa [add_assoc] using h5

theorem rel_uv_comm_u (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C)
    (hLu : D.u ∈ Subgroup.normalizer C) (hLuv : D.uv ∈ Subgroup.normalizer C)
    {bU bUV : B}
    (hbU : conjBy hLu (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hbUV : conjBy hLuv (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bUV) :
    D.ec bU + Φu D (D.ec bUV) = D.ec bUV + Φuv D (D.ec bU) := by
  have h1 : conjBy hLu (conjBy hLuv (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bU * conjBy D.u_mem bUV) := by
    rw [hbUV, conj_dC_mul hBC hdC hLu D.u_mem hbU]
  have h2 : conjBy hLuv (conjBy hLu (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bUV * conjBy D.uv_mem bU) := by
    rw [hbU, conj_dC_mul hBC hdC hLuv D.uv_mem hbUV]
  have heq : conjBy hLu (conjBy hLuv (⟨d, hdC⟩ : C)) =
      conjBy hLuv (conjBy hLu (⟨d, hdC⟩ : C)) := by
    apply Subtype.ext
    show D.u⁻¹ * (D.uv⁻¹ * (d : S) * D.uv) * D.u =
      D.uv⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.uv
    calc D.u⁻¹ * (D.uv⁻¹ * (d : S) * D.uv) * D.u
        = (D.uv * D.u)⁻¹ * (d : S) * (D.uv * D.u) := by group
      _ = (D.u * D.uv)⁻¹ * (d : S) * (D.u * D.uv) := by rw [D.uv_comm_u]
      _ = D.uv⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.uv := by group
  rw [h1, h2] at heq
  have h3 : bU * conjBy D.u_mem bUV = bUV * conjBy D.uv_mem bU := by
    apply Subgroup.inclusion_injective hBC
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) heq
    simpa [mul_assoc] using h4
  have h5 := congrArg D.ec h3
  simpa [D.ec_mul, ec_conj_u, ec_conj_uv] using h5

theorem rel_uv_rho (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C)
    (hLt : D.t ∈ Subgroup.normalizer C) (hLr : D.ρ ∈ Subgroup.normalizer C)
    (hLuv : D.uv ∈ Subgroup.normalizer C) {bT bR bUV : B}
    (hbT : conjBy hLt (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bT)
    (hbR : conjBy hLr (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR)
    (hbUV : conjBy hLuv (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bUV) :
    D.ec bR + Φρ D (D.ec bUV) = D.ec bT + Φt D (D.ec bR) := by
  have h1 : conjBy hLr (conjBy hLuv (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bR * conjBy D.ρ_mem bUV) := by
    rw [hbUV, conj_dC_mul hBC hdC hLr D.ρ_mem hbR]
  have h2 : conjBy hLt (conjBy hLr (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bT * conjBy D.t_mem bR) := by
    rw [hbR, conj_dC_mul hBC hdC hLt D.t_mem hbT]
  have heq : conjBy hLr (conjBy hLuv (⟨d, hdC⟩ : C)) =
      conjBy hLt (conjBy hLr (⟨d, hdC⟩ : C)) := by
    apply Subtype.ext
    show D.ρ⁻¹ * (D.uv⁻¹ * (d : S) * D.uv) * D.ρ =
      D.t⁻¹ * (D.ρ⁻¹ * (d : S) * D.ρ) * D.t
    calc D.ρ⁻¹ * (D.uv⁻¹ * (d : S) * D.uv) * D.ρ
        = (D.uv * D.ρ)⁻¹ * (d : S) * (D.uv * D.ρ) := by group
      _ = (D.ρ * D.t)⁻¹ * (d : S) * (D.ρ * D.t) := by rw [D.uv_rho]
      _ = D.t⁻¹ * (D.ρ⁻¹ * (d : S) * D.ρ) * D.t := by group
  rw [h1, h2] at heq
  have h3 : bR * conjBy D.ρ_mem bUV = bT * conjBy D.t_mem bR := by
    apply Subgroup.inclusion_injective hBC
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) heq
    simpa [mul_assoc] using h4
  have h5 := congrArg D.ec h3
  simpa [D.ec_mul, ec_conj_t, ec_conj_ρ] using h5

theorem rel_u_rho (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C)
    (hLu : D.u ∈ Subgroup.normalizer C) (hLr : D.ρ ∈ Subgroup.normalizer C)
    {bU bR : B}
    (hbU : conjBy hLu (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hbR : conjBy hLr (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR) :
    D.ec bR + Φρ D (D.ec bU) + Φρ D (Φu D (D.ec bR)) +
      Φρ D (Φu D (Φρ D (D.ec bU))) = 0 := by
  have hX2 : conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bR * conjBy D.ρ_mem bU) := by
    rw [hbU, conj_dC_mul hBC hdC hLr D.ρ_mem hbR]
  have hX3 : conjBy hLu (conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C))) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU)) := by
    rw [hX2, conj_dC_mul hBC hdC hLu D.u_mem hbU]
  have hX4 : conjBy hLr (conjBy hLu (conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C)))) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC
        (bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU))) := by
    rw [hX3, conj_dC_mul hBC hdC hLr D.ρ_mem hbR]
  have hfin : conjBy hLr (conjBy hLu (conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C)))) =
      ⟨d, hdC⟩ := by
    apply Subtype.ext
    show D.ρ⁻¹ * (D.u⁻¹ * (D.ρ⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.ρ) * D.u) * D.ρ = d
    calc D.ρ⁻¹ * (D.u⁻¹ * (D.ρ⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.ρ) * D.u) * D.ρ
        = (D.u * D.ρ * D.u * D.ρ)⁻¹ * (d : S) * (D.u * D.ρ * D.u * D.ρ) := by group
      _ = d := by rw [D.u_rho]; group
  rw [hX4] at hfin
  have hβ : Subgroup.inclusion hBC
      (bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU))) = 1 := by
    have h5 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) hfin
    simpa [mul_assoc] using h5
  have h6 : bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU)) = 1 := by
    have hβ' : Subgroup.inclusion hBC
        (bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU))) =
        Subgroup.inclusion hBC (1 : B) := by
      simpa using hβ
    have := Subgroup.inclusion_injective hBC hβ'
    simpa using this
  have h7 := congrArg D.ec h6
  rw [D.ec_mul, D.ec_one, ec_conj_ρ, D.ec_mul, ec_conj_u, D.ec_mul, ec_conj_ρ] at h7
  simp only [map_add] at h7 ⊢
  linear_combination h7


noncomputable abbrev Φuv0 (m : ℕ) : Torus (Type100.k m) →+ Torus (Type100.k m) :=
  matAct (Type100.k m) Type100.uvM (Type100.compat_uv m)

noncomputable abbrev Φt0 (m : ℕ) : Torus (Type100.k m) →+ Torus (Type100.k m) :=
  matAct (Type100.k m) Type100.tM (Type100.compat_t m)

noncomputable abbrev Φu0 (m : ℕ) : Torus (Type100.k m) →+ Torus (Type100.k m) :=
  matAct (Type100.k m) Type100.uM (Type100.compat_u m)

noncomputable abbrev Φρ0 (m : ℕ) : Torus (Type100.k m) →+ Torus (Type100.k m) :=
  matAct (Type100.k m) Type100.ρM (Type100.compat_rho m)

theorem Φuv_eq_zero (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φuv D = Φuv0 m := rfl

theorem Φt_eq_zero (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φt D = Φt0 m := rfl

theorem Φu_eq_zero (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φu D = Φu0 m := rfl

theorem Φρ_eq_zero (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Φρ D = Φρ0 m := rfl

theorem gens_coord_zero {k : Fin 3 → ℕ} {i j l i' j' l' : ℤ}
    (h : i • gen k 0 + j • gen k 1 + l • gen k 2 = i' • gen k 0 + j' • gen k 1 + l' • gen k 2) :
    (i : ZMod (2 ^ k 0)) = (i' : ZMod (2 ^ k 0)) := by
  have := congrFun h 0
  simpa [gen, Pi.single_apply, zsmul_eq_mul] using this

theorem gens_coord_one {k : Fin 3 → ℕ} {i j l i' j' l' : ℤ}
    (h : i • gen k 0 + j • gen k 1 + l • gen k 2 = i' • gen k 0 + j' • gen k 1 + l' • gen k 2) :
    (j : ZMod (2 ^ k 1)) = (j' : ZMod (2 ^ k 1)) := by
  have := congrFun h 1
  simpa [gen, Pi.single_apply, zsmul_eq_mul] using this

theorem zsmul_gens {k : Fin 3 → ℕ} (n i j l : ℤ) :
    n • (i • gen k 0 + j • gen k 1 + l • gen k 2) =
      (n * i) • gen k 0 + (n * j) • gen k 1 + (n * l) • gen k 2 := by
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]

theorem gens_add {k : Fin 3 → ℕ} (a b c a' b' c' : ℤ) :
    (a • gen k 0 + b • gen k 1 + c • gen k 2) + (a' • gen k 0 + b' • gen k 1 + c' • gen k 2) =
      (a + a') • gen k 0 + (b + b') • gen k 1 + (c + c') • gen k 2 := by
  rw [add_smul, add_smul, add_smul]
  abel

theorem gens_coord_zero_of_eq_zero {k : Fin 3 → ℕ} {i j l : ℤ}
    (h : i • gen k 0 + j • gen k 1 + l • gen k 2 = (0 : Torus k)) :
    (i : ZMod (2 ^ k 0)) = 0 := by
  have := congrFun h 0
  simpa [gen, Pi.single_apply, zsmul_eq_mul] using this

theorem gens_coord_one_of_eq_zero {k : Fin 3 → ℕ} {i j l : ℤ}
    (h : i • gen k 0 + j • gen k 1 + l • gen k 2 = (0 : Torus k)) :
    (j : ZMod (2 ^ k 1)) = 0 := by
  have := congrFun h 1
  simpa [gen, Pi.single_apply, zsmul_eq_mul] using this

theorem gens_coord_two_of_eq_zero {k : Fin 3 → ℕ} {i j l : ℤ}
    (h : i • gen k 0 + j • gen k 1 + l • gen k 2 = (0 : Torus k)) :
    (l : ZMod (2 ^ k 2)) = 0 := by
  have := congrFun h 2
  simpa [gen, Pi.single_apply, zsmul_eq_mul] using this

theorem gens_coord_two {k : Fin 3 → ℕ} {i j l i' j' l' : ℤ}
    (h : i • gen k 0 + j • gen k 1 + l • gen k 2 = i' • gen k 0 + j' • gen k 1 + l' • gen k 2) :
    (l : ZMod (2 ^ k 2)) = (l' : ZMod (2 ^ k 2)) := by
  have := congrFun h 2
  simpa [gen, Pi.single_apply, zsmul_eq_mul] using this

theorem gens_apply_zero {k : Fin 3 → ℕ} (a b c : ℤ) :
    (a • gen k 0 + b • gen k 1 + c • gen k 2 : Torus k) 0 = (a : ZMod (2 ^ k 0)) := by
  simp [gen, Pi.single_apply, zsmul_eq_mul]

theorem gens_apply_one {k : Fin 3 → ℕ} (a b c : ℤ) :
    (a • gen k 0 + b • gen k 1 + c • gen k 2 : Torus k) 1 = (b : ZMod (2 ^ k 1)) := by
  simp [gen, Pi.single_apply, zsmul_eq_mul]

theorem gens_apply_two {k : Fin 3 → ℕ} (a b c : ℤ) :
    (a • gen k 0 + b • gen k 1 + c • gen k 2 : Torus k) 2 = (c : ZMod (2 ^ k 2)) := by
  simp [gen, Pi.single_apply, zsmul_eq_mul]

theorem k100_zero (m : ℕ) : Type100.k m 0 = m := by
  simp only [Type100.k, Matrix.cons_val_zero]

theorem k100_one (m : ℕ) : Type100.k m 1 = m + 1 := by
  simp only [Type100.k, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]

theorem k100_two (m : ℕ) : Type100.k m 2 = m + 1 := by
  simp only [Type100.k, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem form_bu {m : ℕ} (hm : 1 ≤ m) {x : Torus (Type100.k m)}
    (h2 : (2 : ℤ) • x = 0) (hφ : x + Φu0 m x = 0) :
    ∃ ε δ : ℕ, ε ≤ 1 ∧ δ ≤ 1 ∧
      x = ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type100.k m) 0 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 1 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 2 := by
  classical
  obtain ⟨i, j, l, hx⟩ := torus_eq_zsmul_gens (Type100.k m) x
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_zero_of_eq_zero h
    rw [k100_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 1))) * (j : ZMod (2 ^ (m + 1))) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k100_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 1))) * (l : ZMod (2 ^ (m + 1))) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_two_of_eq_zero h
    rw [k100_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hφ1 : (j : ZMod (2 ^ (m + 1))) + (l : ZMod (2 ^ (m + 1))) = 0 := by
    have h := hφ
    rw [hx, Φu0, matAct_zsmul_gens, gens_add] at h
    have h10 : Type100.uM 1 0 = 0 := by decide
    have h11 : Type100.uM 1 1 = 0 := by decide
    have h12 : Type100.uM 1 2 = 1 := by decide
    rw [h10, h11, h12] at h
    simp only [zero_mul, mul_one, one_mul, add_zero, zero_add] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k100_one] at h'
    rw [Int.cast_add] at h'
    exact h'
  have hjl : (l : ZMod (2 ^ (m + 1))) = (j : ZMod (2 ^ (m + 1))) := by
    have h1 : (l : ZMod (2 ^ (m + 1))) = -(j : ZMod (2 ^ (m + 1))) := by linear_combination hφ1
    have h3 : -(j : ZMod (2 ^ (m + 1))) = (j : ZMod (2 ^ (m + 1))) := by
      linear_combination -h2j
    rw [h1, h3]
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℕ, ε ≤ 1 ∧
      (i : ZMod (2 ^ m)) = (((ε : ℤ) * 2 ^ (m - 1) : ℤ) : ZMod (2 ^ m)) := by
    rcases (zmod_two_mul_eq_zero_iff hm (i : ZMod (2 ^ m))).1 h2i with h | h
    · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
    · exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : ℕ, δ ≤ 1 ∧
      (j : ZMod (2 ^ (m + 1))) = (((δ : ℤ) * 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 1) (j : ZMod (2 ^ (m + 1)))).1 h2j
      with h | h
    · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
    · exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  have hl : (l : ZMod (2 ^ (m + 1))) = (((δ : ℤ) * 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) := by
    rw [hjl, hδ]
  refine ⟨ε, δ, hε1, hδ1, ?_⟩
  rw [hx]
  funext t
  fin_cases t
  · show (i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 +
      l • gen (Type100.k m) 2 : Torus (Type100.k m)) 0 =
      (((ε : ℤ) * 2 ^ (m - 1)) • gen (Type100.k m) 0 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 1 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 2 : Torus (Type100.k m)) 0
    rw [gens_apply_zero, gens_apply_zero]
    exact hε
  · show (i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 +
      l • gen (Type100.k m) 2 : Torus (Type100.k m)) 1 =
      (((ε : ℤ) * 2 ^ (m - 1)) • gen (Type100.k m) 0 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 1 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 2 : Torus (Type100.k m)) 1
    rw [gens_apply_one, gens_apply_one]
    exact hδ
  · show (i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 +
      l • gen (Type100.k m) 2 : Torus (Type100.k m)) 2 =
      (((ε : ℤ) * 2 ^ (m - 1)) • gen (Type100.k m) 0 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 1 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 2 : Torus (Type100.k m)) 2
    rw [gens_apply_two, gens_apply_two]
    exact hl

theorem gens_eq_of_coord {k : Fin 3 → ℕ} {a b c a' b' c' : ℤ}
    (h0 : (a : ZMod (2 ^ k 0)) = (a' : ZMod (2 ^ k 0)))
    (h1 : (b : ZMod (2 ^ k 1)) = (b' : ZMod (2 ^ k 1)))
    (h2 : (c : ZMod (2 ^ k 2)) = (c' : ZMod (2 ^ k 2))) :
    a • gen k 0 + b • gen k 1 + c • gen k 2 = a' • gen k 0 + b' • gen k 1 + c' • gen k 2 := by
  funext t
  fin_cases t
  · show (a • gen k 0 + b • gen k 1 + c • gen k 2 : Torus k) 0 =
      (a' • gen k 0 + b' • gen k 1 + c' • gen k 2 : Torus k) 0
    rw [gens_apply_zero, gens_apply_zero]; exact h0
  · show (a • gen k 0 + b • gen k 1 + c • gen k 2 : Torus k) 1 =
      (a' • gen k 0 + b' • gen k 1 + c' • gen k 2 : Torus k) 1
    rw [gens_apply_one, gens_apply_one]; exact h1
  · show (a • gen k 0 + b • gen k 1 + c • gen k 2 : Torus k) 2 =
      (a' • gen k 0 + b' • gen k 1 + c' • gen k 2 : Torus k) 2
    rw [gens_apply_two, gens_apply_two]; exact h2

theorem dvd_of_dvd_two_mul {k : ℕ} {n : ℤ} (h : ((2 : ℤ) ^ (k + 1)) ∣ 2 * n) :
    ((2 : ℤ) ^ k) ∣ n := by
  have hsplit : ((2 : ℤ) ^ (k + 1)) = 2 * (2 : ℤ) ^ k := by rw [pow_succ]; ring
  rw [hsplit] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by linarith⟩

theorem dvd_two_mul_of_two_mul_cast_eq_zero {k : ℕ} {n : ℤ}
    (h : (2 : ZMod (2 ^ k)) * (n : ZMod (2 ^ k)) = 0) : ((2 : ℤ) ^ k) ∣ 2 * n := by
  have h' : ((2 * n : ℤ) : ZMod (2 ^ k)) = 0 := by push_cast; exact h
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * n) (2 ^ k)).1 h'
  simpa using this

theorem dvd_of_cast_mul_eq_zero {k : ℕ} {c n : ℤ}
    (h : (c : ZMod (2 ^ k)) * (n : ZMod (2 ^ k)) = 0) : ((2 : ℤ) ^ k) ∣ c * n := by
  have h' : ((c * n : ℤ) : ZMod (2 ^ k)) = 0 := by push_cast; exact h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (c * n) (2 ^ k)).1 h'

@[expose]
noncomputable def xU (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : Torus (StrothTypeIndex.t100 m).k :=
  D.ec (bU D hBC hrel hdC hdB hL)

@[expose]
noncomputable def yT (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : Torus (StrothTypeIndex.t100 m).k :=
  D.ec (bT D hBC hrel hdC hdB hL)

@[expose]
noncomputable def zR (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : Torus (StrothTypeIndex.t100 m).k :=
  D.ec (bR D hBC hrel hdC hdB hL)

@[expose]
noncomputable def wUV (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : Torus (StrothTypeIndex.t100 m).k :=
  D.ec (bUV D hBC hrel hdC hdB hL)

theorem t100_u_c' (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.u_mem D.c) = Torus.c := by
  show D.e (Additive.ofMul (conjBy D.u_mem D.c)) = Torus.c
  simpa only [one_zsmul] using D.t100_u_c

theorem t100_t_c' (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.t_mem D.c) = Torus.c + (2 : ℤ) • Torus.a := by
  show D.e (Additive.ofMul (conjBy D.t_mem D.c)) = Torus.c + (2 : ℤ) • Torus.a
  simpa only [one_zsmul] using D.t100_t_c

theorem t100_rho_c' (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.ρ_mem D.c) = Torus.c := by
  show D.e (Additive.ofMul (conjBy D.ρ_mem D.c)) = Torus.c
  simpa only [one_zsmul] using D.t100_rho_c

theorem t100_uv_c' (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.uv_mem D.c) =
      (-3 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b := by
  show D.e (Additive.ofMul (conjBy D.uv_mem D.c)) =
    (-3 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b
  simpa only [Int.reduceNeg] using D.t100_uv_c

theorem sq_bU (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • xU D hBC hrel hdC hdB hL = 0 := by
  have hβ : conjBy D.u_mem D.c = D.c * (D.c⁻¹ * conjBy D.u_mem D.c) := by group
  have h := sq_rel (D := D) (hBC := hBC) (hC := hC) (hrel := hrel) (d := d) (hdC := hdC)
    (hd2 := hd2) (g := D.u) (hgC := hL D.u_mem_L) (hgB := D.u_mem)
    (b := bU D hBC hrel hdC hdB hL) (β := D.c⁻¹ * conjBy D.u_mem D.c)
    (hb := conj_eq_bU (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL)) (hβ := hβ)
  rw [← xU] at h
  rw [h]
  rw [D.ec_mul, D.ec_inv, D.ec_c, t100_u_c' D, neg_add_cancel]

theorem sq_bT (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • yT D hBC hrel hdC hdB hL = (2 : ℤ) • Torus.a := by
  have hβ : conjBy D.t_mem D.c = D.c * (D.c⁻¹ * conjBy D.t_mem D.c) := by group
  have h := sq_rel (D := D) (hBC := hBC) (hC := hC) (hrel := hrel) (d := d) (hdC := hdC)
    (hd2 := hd2) (g := D.t) (hgC := hL D.t_mem_L) (hgB := D.t_mem)
    (b := bT D hBC hrel hdC hdB hL) (β := D.c⁻¹ * conjBy D.t_mem D.c)
    (hb := conj_eq_bT (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL)) (hβ := hβ)
  rw [← yT] at h
  rw [h]
  rw [D.ec_mul, D.ec_inv, D.ec_c, t100_t_c' D]
  abel

theorem sq_bR (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • zR D hBC hrel hdC hdB hL = 0 := by
  have hβ : conjBy D.ρ_mem D.c = D.c * (D.c⁻¹ * conjBy D.ρ_mem D.c) := by group
  have h := sq_rel (D := D) (hBC := hBC) (hC := hC) (hrel := hrel) (d := d) (hdC := hdC)
    (hd2 := hd2) (g := D.ρ) (hgC := hL D.ρ_mem_L) (hgB := D.ρ_mem)
    (b := bR D hBC hrel hdC hdB hL) (β := D.c⁻¹ * conjBy D.ρ_mem D.c)
    (hb := conj_eq_bR (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL)) (hβ := hβ)
  rw [← zR] at h
  rw [h]
  rw [D.ec_mul, D.ec_inv, D.ec_c, t100_rho_c' D, neg_add_cancel]

theorem sq_bUV (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • wUV D hBC hrel hdC hdB hL =
      (-4 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b := by
  have hβ : conjBy D.uv_mem D.c = D.c * (D.c⁻¹ * conjBy D.uv_mem D.c) := by group
  have h := sq_rel (D := D) (hBC := hBC) (hC := hC) (hrel := hrel) (d := d) (hdC := hdC)
    (hd2 := hd2) (g := D.uv) (hgC := hL D.uv_mem_L) (hgB := D.uv_mem)
    (b := bUV D hBC hrel hdC hdB hL) (β := D.c⁻¹ * conjBy D.uv_mem D.c)
    (hb := conj_eq_bUV (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL)) (hβ := hβ)
  rw [← wUV] at h
  rw [h]
  rw [D.ec_mul, D.ec_inv, D.ec_c, t100_uv_c' D]
  module

theorem phi_bU (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    xU D hBC hrel hdC hdB hL + Φu D (xU D hBC hrel hdC hdB hL) = 0 :=
  inv_rel (D := D) (hBC := hBC) (hdC := hdC) (g := D.u) (hgC := hL D.u_mem_L)
    (hgB := D.u_mem) (b := bU D hBC hrel hdC hdB hL)
    (hb := conj_eq_bU (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL)) (hg2 := D.u_sq) (φ := Φu0 m) (hφ := ec_conj_u D)

theorem phi_bT (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    yT D hBC hrel hdC hdB hL + Φt D (yT D hBC hrel hdC hdB hL) = 0 :=
  inv_rel (D := D) (hBC := hBC) (hdC := hdC) (g := D.t) (hgC := hL D.t_mem_L)
    (hgB := D.t_mem) (b := bT D hBC hrel hdC hdB hL)
    (hb := conj_eq_bT (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL)) (hg2 := D.t_sq) (φ := Φt0 m) (hφ := ec_conj_t D)

theorem phi_bR (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    zR D hBC hrel hdC hdB hL + Φρ D (zR D hBC hrel hdC hdB hL) +
      Φρ D (Φρ D (zR D hBC hrel hdC hdB hL)) = 0 :=
  inv_rel_three (D := D) (hBC := hBC) (hdC := hdC) (g := D.ρ) (hgC := hL D.ρ_mem_L)
    (hgB := D.ρ_mem) (b := bR D hBC hrel hdC hdB hL)
    (hb := conj_eq_bR (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL)) (hg3 := D.rho_cube) (φ := Φρ0 m) (hφ := ec_conj_ρ D)

theorem rel_bU_bUV (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    xU D hBC hrel hdC hdB hL + Φu D (wUV D hBC hrel hdC hdB hL) =
      wUV D hBC hrel hdC hdB hL + Φuv D (xU D hBC hrel hdC hdB hL) :=
  rel_uv_comm_u (D := D) (hBC := hBC) (hdC := hdC) (hLu := hL D.u_mem_L)
    (hLuv := hL D.uv_mem_L)
    (hbU := conj_eq_bU (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL))
    (hbUV := conj_eq_bUV (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL))

theorem rel_bR_bUV (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    zR D hBC hrel hdC hdB hL + Φρ D (wUV D hBC hrel hdC hdB hL) =
      yT D hBC hrel hdC hdB hL + Φt D (zR D hBC hrel hdC hdB hL) :=
  rel_uv_rho (D := D) (hBC := hBC) (hdC := hdC) (hLt := hL D.t_mem_L)
    (hLr := hL D.ρ_mem_L) (hLuv := hL D.uv_mem_L)
    (hbT := conj_eq_bT (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL))
    (hbR := conj_eq_bR (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL))
    (hbUV := conj_eq_bUV (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL))

theorem rel_bU_bR (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) :
    zR D hBC hrel hdC hdB hL + Φρ D (xU D hBC hrel hdC hdB hL) +
      Φρ D (Φu D (zR D hBC hrel hdC hdB hL)) +
      Φρ D (Φu D (Φρ D (xU D hBC hrel hdC hdB hL))) = 0 :=
  rel_u_rho (D := D) (hBC := hBC) (hdC := hdC) (hLu := hL D.u_mem_L)
    (hLr := hL D.ρ_mem_L)
    (hbU := conj_eq_bU (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL))
    (hbR := conj_eq_bR (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL))

theorem two_pow_cast (m : ℕ) :
    ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) = (2 : ZMod (2 ^ (m + 1))) ^ m := by
  push_cast
  ring

theorem form_bt {m : ℕ} (hm : 1 ≤ m) {y : Torus (Type100.k m)}
    (h2 : (2 : ℤ) • y = (2 : ℤ) • gen (Type100.k m) 1) (hφ : y + Φt0 m y = 0) :
    ∃ α q : ℕ, α ≤ 1 ∧ q ≤ 1 ∧
      y = (0 : ℤ) • gen (Type100.k m) 0 + ((1 : ℤ) + (α : ℤ) * 2 ^ m) • gen (Type100.k m) 1 +
        ((q : ℤ) * 2 ^ m) • gen (Type100.k m) 2 := by
  classical
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (Type100.k m) y
  have h2' : (2 * i) • gen (Type100.k m) 0 + (2 * j) • gen (Type100.k m) 1 +
      (2 * l) • gen (Type100.k m) 2 =
      (0 : ℤ) • gen (Type100.k m) 0 + (2 : ℤ) • gen (Type100.k m) 1 +
        (0 : ℤ) • gen (Type100.k m) 2 := by
    rw [← zsmul_gens, ← hy, h2]
    simp
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h' := gens_coord_zero h2'
    rw [k100_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 1))) * (j : ZMod (2 ^ (m + 1))) = 2 := by
    have h' := gens_coord_one h2'
    rw [k100_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 1))) * (l : ZMod (2 ^ (m + 1))) = 0 := by
    have h' := gens_coord_two h2'
    rw [k100_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hφ1 : (j : ZMod (2 ^ (m + 1))) +
      ((2 * i + -1 * j + -2 * l : ℤ) : ZMod (2 ^ (m + 1))) = 0 := by
    have h := hφ
    rw [hy, Φt0, matAct_zsmul_gens, gens_add] at h
    have ht10 : Type100.tM 1 0 = 2 := by decide
    have ht11 : Type100.tM 1 1 = -1 := by decide
    have ht12 : Type100.tM 1 2 = -2 := by decide
    rw [ht10, ht11, ht12] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k100_one] at h'
    rw [Int.cast_add] at h'
    exact h'
  have hsub : ((2 * i - 2 * l : ℤ) : ZMod (2 ^ (m + 1))) = 0 := by
    have he : (2 * i - 2 * l : ℤ) = j + (2 * i + -1 * j + -2 * l) := by ring
    rw [he, Int.cast_add]
    exact hφ1
  have hzero : (2 : ZMod (2 ^ (m + 1))) * (i : ZMod (2 ^ (m + 1))) = 0 := by
    have h1 : (2 : ZMod (2 ^ (m + 1))) * (i : ZMod (2 ^ (m + 1))) -
        2 * (l : ZMod (2 ^ (m + 1))) = 0 := by
      have h := hsub
      rw [Int.cast_sub, Int.cast_mul, Int.cast_mul] at h
      norm_num at h
      exact h
    have h2'' : (2 : ZMod (2 ^ (m + 1))) * (l : ZMod (2 ^ (m + 1))) = 0 := h2l
    linear_combination h1 + h2''
  have hdvd : ((2 : ℤ) ^ m) ∣ i :=
    dvd_of_dvd_two_mul (k := m) (dvd_two_mul_of_two_mul_cast_eq_zero hzero)
  have hi : (i : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  have hmeq : m + 1 - 1 = m := by omega
  obtain ⟨α, hα1, hα⟩ : ∃ α : ℕ, α ≤ 1 ∧
      (j : ZMod (2 ^ (m + 1))) = 1 + (α : ZMod (2 ^ (m + 1))) *
        ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    have h2j' : (2 : ZMod (2 ^ (m + 1))) * ((j : ZMod (2 ^ (m + 1))) - 1) = 0 := by
      linear_combination h2j
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 1)
      ((j : ZMod (2 ^ (m + 1))) - 1)).1 h2j' with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  obtain ⟨q, hq1, hq⟩ : ∃ q : ℕ, q ≤ 1 ∧
      (l : ZMod (2 ^ (m + 1))) = (q : ZMod (2 ^ (m + 1))) * ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 1) (l : ZMod (2 ^ (m + 1)))).1 h2l
      with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have h1 : (((1 : ℤ) + (α : ℤ) * 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) =
      1 + (α : ZMod (2 ^ (m + 1))) * ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    push_cast
    ring
  have h2q : (((q : ℤ) * 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) =
      (q : ZMod (2 ^ (m + 1))) * ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    push_cast
    ring
  refine ⟨α, q, hα1, hq1, ?_⟩
  rw [hy]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k100_zero, Int.cast_zero]
    exact hi
  · rw [k100_one, h1]
    exact hα
  · rw [k100_two, h2q]
    exact hq

theorem form_br {m : ℕ} (hm : 1 ≤ m) {z : Torus (Type100.k m)}
    (h2 : (2 : ℤ) • z = 0)
    (hφ : z + Φρ0 m z + Φρ0 m (Φρ0 m z) = 0) :
    ∃ θ ζ : ℕ, ζ ≤ 1 ∧ θ ≤ 1 ∧
      z = (0 : ℤ) • gen (Type100.k m) 0 + ((ζ : ℤ) * 2 ^ m) • gen (Type100.k m) 1 +
        ((θ : ℤ) * 2 ^ m) • gen (Type100.k m) 2 := by
  classical
  obtain ⟨i, j, l, hz⟩ := torus_eq_zsmul_gens (Type100.k m) z
  have h2' : (2 * i) • gen (Type100.k m) 0 + (2 * j) • gen (Type100.k m) 1 +
      (2 * l) • gen (Type100.k m) 2 = (0 : Torus (Type100.k m)) := by
    rw [← zsmul_gens, ← hz, h2]
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h' := gens_coord_zero_of_eq_zero h2'
    rw [k100_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 1))) * (j : ZMod (2 ^ (m + 1))) = 0 := by
    have h' := gens_coord_one_of_eq_zero h2'
    rw [k100_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 1))) * (l : ZMod (2 ^ (m + 1))) = 0 := by
    have h' := gens_coord_two_of_eq_zero h2'
    rw [k100_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hj0 : (j : ZMod (2 ^ m)) = 0 := by
    have hd : ((2 : ℤ) ^ m) ∣ j :=
      dvd_of_dvd_two_mul (k := m) (dvd_two_mul_of_two_mul_cast_eq_zero h2j)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have hl0 : (l : ZMod (2 ^ m)) = 0 := by
    have hd : ((2 : ℤ) ^ m) ∣ l :=
      dvd_of_dvd_two_mul (k := m) (dvd_two_mul_of_two_mul_cast_eq_zero h2l)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have hφ1 : ((3 * i - 2 * j - 2 * l : ℤ) : ZMod (2 ^ m)) = 0 := by
    have h := hφ
    rw [hz] at h
    simp only [Φρ0, matAct_zsmul_gens] at h
    rw [gens_add, gens_add] at h
    have hr00 : Type100.ρM 0 0 = 1 := by decide
    have hr01 : Type100.ρM 0 1 = 0 := by decide
    have hr02 : Type100.ρM 0 2 = -2 := by decide
    have hr10 : Type100.ρM 1 0 = 0 := by decide
    have hr11 : Type100.ρM 1 1 = 0 := by decide
    have hr12 : Type100.ρM 1 2 = -1 := by decide
    have hr20 : Type100.ρM 2 0 = 0 := by decide
    have hr21 : Type100.ρM 2 1 = 1 := by decide
    have hr22 : Type100.ρM 2 2 = -1 := by decide
    rw [hr00, hr01, hr02, hr10, hr11, hr12, hr20, hr21, hr22] at h
    have hsimp : (i + (1 * i + 0 * j + -2 * l) +
        (1 * (1 * i + 0 * j + -2 * l) + 0 * (0 * i + 0 * j + -1 * l) +
          -2 * (0 * i + 1 * j + -1 * l)) : ℤ) = 3 * i - 2 * j - 2 * l := by ring
    rw [hsimp] at h
    exact gens_coord_zero_of_eq_zero h
  have h3i : (3 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h := hφ1
    rw [Int.cast_sub, Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_mul] at h
    norm_num at h
    linear_combination h + 2 * hj0 + 2 * hl0
  have hdvd3 : ((2 : ℤ) ^ m) ∣ 3 * i := by
    have h3i' : ((3 : ℤ) : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
      rw [Int.cast_ofNat]
      exact h3i
    exact dvd_of_cast_mul_eq_zero h3i'
  have hcop : IsCoprime ((2 : ℤ) ^ m) (3 : ℤ) :=
    ((show Odd (3 : ℤ) by norm_num).isCoprime_two).symm.pow_left
  have hi : (i : ZMod (2 ^ m)) = 0 := by
    have hd : ((2 : ℤ) ^ m) ∣ i :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hdvd3 (Int.isCoprime_iff_gcd_eq_one.mp hcop)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have hmeq : m + 1 - 1 = m := by omega
  obtain ⟨ζ, hζ1, hζ⟩ : ∃ ζ : ℕ, ζ ≤ 1 ∧
      (j : ZMod (2 ^ (m + 1))) = (ζ : ZMod (2 ^ (m + 1))) *
        ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 1) (j : ZMod (2 ^ (m + 1)))).1 h2j
      with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  obtain ⟨θ, hθ1, hθ⟩ : ∃ θ : ℕ, θ ≤ 1 ∧
      (l : ZMod (2 ^ (m + 1))) = (θ : ZMod (2 ^ (m + 1))) *
        ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 1) (l : ZMod (2 ^ (m + 1)))).1 h2l
      with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have h2q : (((ζ : ℤ) * 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) =
      (ζ : ZMod (2 ^ (m + 1))) * ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    push_cast
    ring
  have h3q : (((θ : ℤ) * 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) =
      (θ : ZMod (2 ^ (m + 1))) * ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
    push_cast
    ring
  refine ⟨θ, ζ, hζ1, hθ1, ?_⟩
  rw [hz]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k100_zero, Int.cast_zero]
    exact hi
  · rw [k100_one, h2q]
    exact hζ
  · rw [k100_two, h3q]
    exact hθ

theorem Φρ_three (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (x : Torus (StrothTypeIndex.t100 m).k) : Φρ D (Φρ D (Φρ D x)) = x := by
  have h := (StrothTypeIndex.action (StrothTypeIndex.t100 m)).rels.rho_cube
  have h' := DFunLike.congr_fun h x
  simpa [AddMonoidHom.comp_apply] using h'

theorem form_xU (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ ε δ : ℕ, ε ≤ 1 ∧ δ ≤ 1 ∧
      xU D hBC hrel hdC hdB hL = ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type100.k m) 0 +
        ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 1 + ((δ : ℤ) * 2 ^ m) • gen (Type100.k m) 2 :=
  form_bu hm (sq_bU D hBC hC hrel hdC hdB hd2 hL) (phi_bU D hBC hrel hdC hdB hL)

theorem form_yT (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ α q : ℕ, α ≤ 1 ∧ q ≤ 1 ∧
      yT D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type100.k m) 0 +
        ((1 : ℤ) + (α : ℤ) * 2 ^ m) • gen (Type100.k m) 1 +
        ((q : ℤ) * 2 ^ m) • gen (Type100.k m) 2 :=
  form_bt hm (sq_bT D hBC hC hrel hdC hdB hd2 hL) (phi_bT D hBC hrel hdC hdB hL)

theorem form_zR (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ θ η : ℕ, η ≤ 1 ∧ θ ≤ 1 ∧
      zR D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type100.k m) 0 +
        ((η : ℤ) * 2 ^ m) • gen (Type100.k m) 1 + ((θ : ℤ) * 2 ^ m) • gen (Type100.k m) 2 :=
  form_br hm (sq_bR D hBC hC hrel hdC hdB hd2 hL) (phi_bR D hBC hrel hdC hdB hL)

end Cocycle





end CFSG.CGT.Stroth77
