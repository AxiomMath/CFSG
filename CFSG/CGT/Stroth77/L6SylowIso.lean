module

public import CFSG.CGT.Stroth77.L6SylowIsoModel
public import CFSG.CGT.Stroth77.TypePredicates
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.CGT.Stroth77

open CFSG.CGT.Foote81L6.Bridge

section TorusD

variable {S : Type} [Group S] {D : Subgroup S} {m : ℕ} (e : Additive D ≃+ Torus (Type201.k m))

theorem torus_eq_zsmul_gens201 {k : Fin 3 → ℕ} (y : Torus k) :
    ∃ i j l : ℤ, y = i • gen k 0 + j • gen k 1 + l • gen k 2 := by
  classical
  choose i hi using fun r : Fin 3 => ZMod.intCast_surjective (y r)
  refine ⟨i 0, i 1, i 2, ?_⟩
  funext r
  fin_cases r <;> simp [gen, Pi.single_apply, hi, zsmul_eq_mul]

theorem e_mul201 (x y : D) : e (.ofMul (x * y)) = e (.ofMul x) + e (.ofMul y) := by
  rw [ofMul_mul, map_add]

theorem e_zpow201 (x : D) (k : ℤ) : e (.ofMul (x ^ k)) = k • e (.ofMul x) := by
  rw [ofMul_zpow, map_zsmul]

theorem e_pow201 (x : D) (k : ℕ) : e (.ofMul (x ^ k)) = k • e (.ofMul x) := by
  rw [ofMul_pow, map_nsmul]

theorem eq_of_e_eq201 {x y : D} (h : e (.ofMul x) = e (.ofMul y)) : x = y :=
  Additive.ofMul.injective (e.injective h)

variable {c a b : D} (hc : e (.ofMul c) = Torus.c) (ha : e (.ofMul a) = Torus.a)
  (hb : e (.ofMul b) = Torus.b)
include hc ha hb

theorem e_word201 (i j l : ℤ) :
    e (.ofMul (c ^ i * a ^ j * b ^ l)) = i • Torus.c + j • Torus.a + l • Torus.b := by
  rw [e_mul201, e_mul201, e_zpow201, e_zpow201, e_zpow201, hc, ha, hb]

theorem mem_closure_cab201 (x : D) :
    (x : S) ∈ Subgroup.closure ({(c : S), (a : S), (b : S)} : Set S) := by
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens201 (e (.ofMul x))
  have hx : x = c ^ i * a ^ j * b ^ l :=
    eq_of_e_eq201 e (by rw [hy, e_word201 e hc ha hb])
  set K := Subgroup.closure ({(c : S), (a : S), (b : S)} : Set S)
  rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow,
    Subgroup.coe_zpow]
  exact K.mul_mem (K.mul_mem (K.zpow_mem (Subgroup.subset_closure (by simp)) _)
    (K.zpow_mem (Subgroup.subset_closure (by simp)) _)) (K.zpow_mem (Subgroup.subset_closure
      (by simp)) _)

theorem ab_pow_ne_one201 : ((a : S) * b) ^ 2 ^ (m + 1) ≠ 1 := by
  intro h
  have h' : (a * b) ^ 2 ^ (m + 1) = 1 := Subtype.ext (by simpa using h)
  have he := congrArg (fun x : D => e (.ofMul x)) h'
  simp only [e_pow201, e_mul201, ha, hb, ofMul_one, map_zero] at he
  have h1 := congrFun he 1
  simp only [Pi.smul_apply, Pi.add_apply, Torus.a, Torus.b, gen, Pi.zero_apply] at h1
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide), add_zero, nsmul_eq_mul, mul_one] at h1
  have hk : Type201.k m 1 = m + 2 := rfl
  rw [hk] at h1
  rw [ZMod.natCast_eq_zero_iff, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h1
  omega

end TorusD

section Relations

variable {S : Type} [Group S] {D : Subgroup S} {m : ℕ} (e : Additive D ≃+ Torus (Type201.k m))
  {c a b : D} (hc : e (.ofMul c) = Torus.c) (ha : e (.ofMul a) = Torus.a)
  (hb : e (.ofMul b) = Torus.b)

include hc ha hb in
theorem conj_eq_word201 {g : S} (hg : g ∈ Subgroup.normalizer D) {φ : Torus (Type201.k m) →+
    Torus (Type201.k m)} (hconj : ∀ x : D, e (.ofMul (conjBy hg x)) = φ (e (.ofMul x)))
    {x : D} {v : Torus (Type201.k m)} (hx : e (.ofMul x) = v) {i j l : ℤ}
    (hφ : φ v = i • Torus.c + j • Torus.a + l • Torus.b) :
    g⁻¹ * (x : S) * g = (c : S) ^ i * (a : S) ^ j * (b : S) ^ l := by
  have h : conjBy hg x = c ^ i * a ^ j * b ^ l :=
    eq_of_e_eq201 e (by rw [hconj, hx, hφ, e_word201 e hc ha hb])
  have h' := congrArg Subtype.val h
  rw [show ((conjBy hg x : D) : S) = g⁻¹ * x * g from rfl] at h'
  simpa using h'

include hc ha hb in
theorem rel201_of_type201 {uv t u f : S} (huv : uv ∈ Subgroup.normalizer D)
    (ht : t ∈ Subgroup.normalizer D) (hu : u ∈ Subgroup.normalizer D)
    (huv_conj : ∀ x : D, e (.ofMul (conjBy huv x)) = (Type201.action m).φuv (e (.ofMul x)))
    (ht_conj : ∀ x : D, e (.ofMul (conjBy ht x)) = (Type201.action m).φt (e (.ofMul x)))
    (hu_conj : ∀ x : D, e (.ofMul (conjBy hu x)) = (Type201.action m).φu (e (.ofMul x)))
    (huv2 : uv * uv = 1) (ht2 : t * t = 1) (hu2 : u * u = 1) (huvt : uv * t = t * uv)
    (huvu : uv * u = u * uv) (htu : t * u = u * uv * t)
    (hf2 : f * f = 1) (hfc : f⁻¹ * c * f = (c : S)⁻¹)
    (hfa : f⁻¹ * a * f = (a : S)⁻¹ * (a : S) ^ 2 ^ (m + 1))
    (hfb : f⁻¹ * b * f = (b : S)⁻¹ * (b : S) ^ 2 ^ (m + 1))
    (hfuv : f⁻¹ * uv * f = ((c : S) * a * b) ^ 2 * uv) (hft : f⁻¹ * t * f = (a : S)⁻¹ ^ 2 * t)
    (hfu : f⁻¹ * u * f = u) :
    Rel201 m (c : S) (a : S) (b : S) uv t u f := by
  have hD : ∀ {x y : D}, e (.ofMul x) = e (.ofMul y) → (x : S) = y := fun h =>
    congrArg Subtype.val (eq_of_e_eq201 e h)
  have hpow0 : ∀ (k : Fin 3), (2 ^ Type201.k m k) • gen (Type201.k m) k = 0 := by
    intro k
    funext r
    by_cases hr : r = k
    · subst hr
      simp [gen]
    · simp [gen, Pi.single_eq_of_ne hr]
  intro p hp
  simp only [eqns201, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only
  · rw [← Subgroup.coe_pow, ← Subgroup.coe_one]
    exact hD (by rw [e_pow201, hc, ofMul_one, map_zero]; exact hpow0 0)
  · rw [← Subgroup.coe_pow, ← Subgroup.coe_one]
    exact hD (by rw [e_pow201, ha, ofMul_one, map_zero]; exact hpow0 1)
  · rw [← Subgroup.coe_pow, ← Subgroup.coe_one]
    exact hD (by rw [e_pow201, hb, ofMul_one, map_zero]; exact hpow0 2)
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    exact hD (by rw [e_mul201, e_mul201, add_comm])
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    exact hD (by rw [e_mul201, e_mul201, add_comm])
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    exact hD (by rw [e_mul201, e_mul201, add_comm])
  · exact conj_eq_word201 e hc ha hb huv huv_conj hc (Type201.uv_c m)
  · have h := conj_eq_word201 e hc ha hb huv huv_conj ha (Type201.uv_a m)
    rw [show ((2 : ℤ) * 2 ^ m + 2) = ((2 * 2 ^ m + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast] at h
    simpa using h
  · have h := conj_eq_word201 e hc ha hb huv huv_conj hb (Type201.uv_b m)
    rw [show ((4 : ℤ) * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) =
      ((4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at h
    simpa using h
  · have h := conj_eq_word201 e hc ha hb ht ht_conj hc (i := 1) (j := 4) (l := 0)
      ((Type201.t_c m).trans (by simp))
    simpa using h
  · have h := conj_eq_word201 e hc ha hb ht ht_conj ha (i := 0) (j := 2 * 2 ^ m - 1) (l := 0)
      ((Type201.t_a m).trans (by simp))
    simpa using h
  · exact conj_eq_word201 e hc ha hb ht ht_conj hb (Type201.t_b m)
  · have h := conj_eq_word201 e hc ha hb hu hu_conj hc (i := 1) (j := 0) (l := 0)
      ((Type201.u_c m).trans (by simp))
    simpa using h
  · have h := conj_eq_word201 e hc ha hb hu hu_conj ha (i := 0) (j := 0) (l := 1)
      ((Type201.u_a m).trans (by simp))
    simpa using h
  · have h := conj_eq_word201 e hc ha hb hu hu_conj hb (i := 0) (j := 1) (l := 0)
      ((Type201.u_b m).trans (by simp))
    simpa using h
  · exact hfc
  · exact hfa
  · exact hfb
  · exact huv2
  · exact ht2
  · exact hu2
  · exact huvt
  · exact huvu
  · exact htu
  · exact hf2
  · exact hfuv
  · exact hft
  · exact hfu

include hc ha hb in
theorem closure_eq_top_of_type201 {uv t u f : S}
    (hgen : D ⊔ Subgroup.closure {uv, t, u, f} = ⊤) :
    Subgroup.closure ({(c : S), (a : S), (b : S), uv, t, u, f} : Set S) = ⊤ := by
  set K := Subgroup.closure ({(c : S), (a : S), (b : S), uv, t, u, f} : Set S)
  have hcab : Subgroup.closure ({(c : S), (a : S), (b : S)} : Set S) ≤ K :=
    Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢; tauto)
  have hD : D ≤ K := fun x hx => hcab (mem_closure_cab201 e hc ha hb ⟨x, hx⟩)
  have hW : Subgroup.closure ({uv, t, u, f} : Set S) ≤ K :=
    Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢; tauto)
  rw [eq_top_iff, ← hgen]
  exact sup_le hD hW

end Relations

theorem nonempty_mulEquiv_sModel_of_type201 {S : Type} [Group S] [Finite S] {D : Subgroup S}
    {m : ℕ} (hm : 1 ≤ m) (e : Additive D ≃+ Torus (Type201.k m)) {c a b : D}
    (hc : e (.ofMul c) = Torus.c) (ha : e (.ofMul a) = Torus.a) (hb : e (.ofMul b) = Torus.b)
    {uv t u f : S} (huv : uv ∈ Subgroup.normalizer D) (ht : t ∈ Subgroup.normalizer D)
    (hu : u ∈ Subgroup.normalizer D)
    (huv_conj : ∀ x : D, e (.ofMul (conjBy huv x)) = (Type201.action m).φuv (e (.ofMul x)))
    (ht_conj : ∀ x : D, e (.ofMul (conjBy ht x)) = (Type201.action m).φt (e (.ofMul x)))
    (hu_conj : ∀ x : D, e (.ofMul (conjBy hu x)) = (Type201.action m).φu (e (.ofMul x)))
    (huv2 : uv * uv = 1) (ht2 : t * t = 1) (hu2 : u * u = 1) (huvt : uv * t = t * uv)
    (huvu : uv * u = u * uv) (htu : t * u = u * uv * t)
    (hf2 : f * f = 1) (hfc : f⁻¹ * c * f = (c : S)⁻¹)
    (hfa : f⁻¹ * a * f = (a : S)⁻¹ * (a : S) ^ 2 ^ (m + 1))
    (hfb : f⁻¹ * b * f = (b : S)⁻¹ * (b : S) ^ 2 ^ (m + 1))
    (hfuv : f⁻¹ * uv * f = ((c : S) * a * b) ^ 2 * uv) (hft : f⁻¹ * t * f = (a : S)⁻¹ ^ 2 * t)
    (hfu : f⁻¹ * u * f = u) (hgen : D ⊔ Subgroup.closure {uv, t, u, f} = ⊤) :
    Nonempty (S ≃* CFSG.CGT.Foote81L6.Bridge.SModel (m + 2)) := by
  have hrel := rel201_of_type201 e hc ha hb huv ht hu huv_conj ht_conj hu_conj huv2 ht2 hu2 huvt
    huvu htu hf2 hfc hfa hfb hfuv hft hfu
  have hgenS := closure_eq_top_of_type201 e hc ha hb hgen
  obtain ⟨hGfin, hGcard⟩ := G201.card_le m
  have hrelM := L6Model.rel_sModel hm
  let ψ := G201.lift hrelM
  have hψ : Function.Surjective ψ := G201.lift_surjective hrelM (L6Model.closure_sModel_eq_top hm)
  have hcardM : Nat.card (SModel (m + 2)) = 2 ^ (3 * m + 8) := by
    rw [card_SModel (by omega)]
    ring_nf
  have hψbij : Function.Bijective ψ := hψ.bijective_of_nat_card_le (by rw [hcardM]; exact hGcard)
  let φ := G201.lift hrel
  have hφ : Function.Surjective φ := G201.lift_surjective hrel hgenS
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hK
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent (SModel (m + 2)) := (IsPGroup.of_card hcardM).isNilpotent
    have hK' : φ.ker.map ψ ≠ ⊥ := by
      intro h
      apply hK
      rw [eq_bot_iff]
      intro g hg
      have : ψ g ∈ φ.ker.map ψ := ⟨g, hg, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact hψbij.1 (this.trans (map_one ψ).symm)
    haveI : (φ.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hK'
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    obtain ⟨hxK, hxZ⟩ := Subgroup.mem_inf.1 hx
    rw [center_SModel (by omega), mem_zpowers_of_mul_self_eq_one (zS_mul_zS _)] at hxZ
    have hxz : x = zS (m + 2) := by
      rcases hxZ with h | h
      · exact absurd (Subtype.ext h) hx1
      · exact h
    obtain ⟨g, hg, hgx⟩ := hxK
    have hab : ψ ((PresentedGroup.of Gen201.a * PresentedGroup.of Gen201.b) ^ 2 ^ (m + 1)) =
        zS (m + 2) := by
      obtain ⟨-, h2, h3, -⟩ := G201.lift_of hrelM
      rw [map_pow, map_mul, h2, h3, ← map_mul, ← map_pow]
      exact L6Model.mk_ab_pow
    have hg' : g = (PresentedGroup.of Gen201.a * PresentedGroup.of Gen201.b) ^ 2 ^ (m + 1) :=
      hψbij.1 (hgx.trans (hxz.trans hab.symm))
    have hg1 : φ g = 1 := hg
    rw [hg', map_pow, map_mul] at hg1
    obtain ⟨-, h2, h3, -⟩ := G201.lift_of hrel
    rw [h2, h3] at hg1
    exact ab_pow_ne_one201 e hc ha hb hg1
  exact ⟨(MulEquiv.ofBijective φ ⟨hφinj, hφ⟩).symm.trans (MulEquiv.ofBijective ψ hψbij)⟩

end CFSG.CGT.Stroth77
