module

public import CFSG.CGT.Stroth77.Section225FrameTorus
public import CFSG.CGT.Stroth77.Section224A
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Stroth77.Extension22FourProof
public import CFSG.CGT.Stroth77.QuotOmegaOne
public import CFSG.CGT.Stroth77.Stroth31Proof
public import CFSG.Foundations
public import CFSG.GH74.Defs

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}

omit [Finite G] in
theorem mem_S_of_mem_R {x : G} (hx : x ∈ 𝓡[S, D]) : x ∈ S :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1

omit [Finite G] in
theorem mem_normalizer_of_mem_R {x : G} (hx : x ∈ 𝓡[S, D]) :
    x ∈ Subgroup.normalizer (D : Set G) :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2

omit [Finite G] in
theorem mem_centralizer_of_mem_R {x : G} (hx : x ∈ 𝓡[S, D]) :
    x ∈ Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) :=
  (Subgroup.mem_inf.mp hx).2

omit [Finite G] in
theorem comm_of_mem (dD : StrothWeakTypeData D τ) {a b : G} (ha : a ∈ D) (hb : b ∈ D) :
    a * b = b * a :=
  congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

variable {dD : StrothWeakTypeData D τ}

omit [Finite G] in
theorem D_le_R (dD : StrothWeakTypeData D τ) (hDS : D ≤ S) : D ≤ 𝓡[S, D] := fun _ hx =>
  Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hDS hx, Subgroup.le_normalizer hx⟩,
    Subgroup.mem_centralizer_iff.mpr fun _ hy =>
      comm_of_mem dD (CFSG.GroupTheory.HuppertProduct.mho_le D 2 hy) hx⟩

theorem mem_mhoOne_iff (dD : StrothWeakTypeData D τ) {x : G} :
    x ∈ mhoOne D ↔ ∃ d ∈ D, d * d = x := by
  rw [mhoOne, mem_mho_iff_exists_pow_of_comm (fun a ha b hb => comm_of_mem dD ha hb)]
  simp [pow_two]

theorem one_le_of_two_le (hk : ∀ i, 2 ≤ τ.k i) : ∀ i, 1 ≤ τ.k i :=
  fun i => le_trans (by norm_num) (hk i)

@[expose] noncomputable def barD (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i) (d : D) :
    Fin 3 → ZMod 2 :=
  torusBar τ.k (one_le_of_two_le hk) (dD.e (Additive.ofMul d))

omit [Finite G] in
theorem barD_mul (hk : ∀ i, 2 ≤ τ.k i) (d d' : D) :
    barD dD hk (d * d') = barD dD hk d + barD dD hk d' := by
  rw [barD, barD, barD, ofMul_mul, map_add, map_add]

omit [Finite G] in
theorem barD_one (hk : ∀ i, 2 ≤ τ.k i) : barD dD hk 1 = 0 := by
  rw [barD, ofMul_one, map_zero, map_zero]

omit [Finite G] in
theorem barD_add_self (hk : ∀ i, 2 ≤ τ.k i) (d : D) : barD dD hk d + barD dD hk d = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

omit [Finite G] in
theorem barD_inv (hk : ∀ i, 2 ≤ τ.k i) (d : D) : barD dD hk d⁻¹ = barD dD hk d := by
  have h := barD_mul (dD := dD) hk d⁻¹ d
  rw [inv_mul_cancel, barD_one] at h
  calc barD dD hk d⁻¹ = barD dD hk d⁻¹ + (barD dD hk d + barD dD hk d) := by
        rw [barD_add_self, add_zero]
    _ = (barD dD hk d⁻¹ + barD dD hk d) + barD dD hk d := by abel
    _ = barD dD hk d := by rw [← h, zero_add]

omit [Finite G] in
theorem barD_surjective (hk : ∀ i, 2 ≤ τ.k i) : Function.Surjective (barD dD hk) := by
  intro w
  refine ⟨Additive.toMul (dD.e.symm (fun i => ((w i).val : ZMod (2 ^ τ.k i)))), ?_⟩
  funext i
  rw [barD, ofMul_toMul, AddEquiv.apply_symm_apply, torusBar_apply]
  have hd : 2 ∣ 2 ^ τ.k i := dvd_pow_self 2 (by have := hk i; omega)
  rw [ZMod.cast_natCast hd, ZMod.natCast_zmod_val]

theorem barD_eq_zero_iff (hk : ∀ i, 2 ≤ τ.k i) (d : D) :
    barD dD hk d = 0 ↔ (d : G) ∈ mhoOne D := by
  constructor
  · intro h
    have hw : ∀ i, ∃ w : ZMod (2 ^ τ.k i), dD.e (Additive.ofMul d) i = 2 * w := by
      intro i
      have hi := congrFun h i
      rw [barD, torusBar_apply, Pi.zero_apply] at hi
      obtain ⟨z, hz⟩ := ZMod.intCast_surjective (dD.e (Additive.ofMul d) i)
      rw [← hz, ZMod.cast_intCast (dvd_pow_self 2 (by have := hk i; omega)),
        ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
      obtain ⟨z', rfl⟩ := hi
      exact ⟨(z' : ZMod (2 ^ τ.k i)), by rw [← hz]; push_cast; ring⟩
    choose w hw using hw
    have hd : Additive.ofMul d = (2 : ℤ) • dD.e.symm w := by
      apply dD.e.injective
      rw [map_zsmul, AddEquiv.apply_symm_apply]
      funext i
      rw [hw i, Pi.smul_apply, two_zsmul, two_mul]
    rw [mem_mhoOne_iff dD]
    refine ⟨((Additive.toMul (dD.e.symm w) : D) : G), (Additive.toMul _ : D).2, ?_⟩
    have h2 : d = Additive.toMul (dD.e.symm w) * Additive.toMul (dD.e.symm w) := by
      apply Additive.ofMul.injective
      rw [hd, ofMul_mul, ofMul_toMul, two_zsmul]
    rw [h2]
    rfl
  · intro h
    obtain ⟨f, hfD, hf⟩ := (mem_mhoOne_iff dD).mp h
    have hd : d = ⟨f, hfD⟩ * ⟨f, hfD⟩ := Subtype.ext hf.symm
    rw [hd, barD_mul, barD_add_self]

omit [Finite G] in
theorem barD_eq_zero_of_pow (hk : ∀ i, 2 ≤ τ.k i) {w : D} {j : ℕ} (hw : w ^ (2 ^ j) = 1)
    {i : Fin 3} (hi : j + 1 ≤ τ.k i) : barD dD hk w i = 0 := by
  have h4 : ((2 ^ j : ℕ) : ℤ) • dD.e (Additive.ofMul w) = 0 := by
    rw [← map_zsmul, show ((2 ^ j : ℕ) : ℤ) • Additive.ofMul w = Additive.ofMul (w ^ (2 ^ j)) by
      rw [ofMul_pow]; norm_cast, hw, ofMul_one, map_zero]
  have h4i := congrFun h4 i
  rw [Pi.smul_apply, Pi.zero_apply] at h4i
  rw [barD, torusBar_apply]
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (dD.e (Additive.ofMul w) i)
  rw [← hz] at h4i ⊢
  rw [ZMod.cast_intCast (dvd_pow_self 2 (by omega)), ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [zsmul_eq_mul, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at h4i
  obtain ⟨n, hn⟩ : ∃ n, τ.k i = n + j + 1 := ⟨τ.k i - j - 1, by omega⟩
  rw [hn] at h4i
  push_cast at h4i
  obtain ⟨t, ht⟩ := h4i
  have h44 : (2 : ℤ) ^ j * z = 2 ^ j * (2 * (2 ^ n * t)) := by
    rw [ht]; ring
  exact ⟨2 ^ n * t, mul_left_cancel₀ (by positivity) h44⟩

omit [Finite G] in
theorem barD_c (hk : ∀ i, 2 ≤ τ.k i) : barD dD hk dD.c = ![1, 0, 0] := by
  funext i
  rw [barD, StrothWeakTypeData.e_c, torusBar_apply]
  fin_cases i
  · show ZMod.cast ((gen τ.k 0) 0) = (1 : ZMod 2)
    rw [gen, Pi.single_eq_same]
    exact ZMod.cast_one (dvd_pow_self 2 (by have := hk 0; omega))
  · show ZMod.cast ((gen τ.k 0) 1) = (0 : ZMod 2)
    rw [gen, Pi.single_eq_of_ne (by decide)]
    exact ZMod.cast_zero
  · show ZMod.cast ((gen τ.k 0) 2) = (0 : ZMod 2)
    rw [gen, Pi.single_eq_of_ne (by decide)]
    exact ZMod.cast_zero

theorem omegaIn_one_le_mhoOne (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i) :
    omegaIn 1 D ≤ mhoOne D := by
  intro w hw
  obtain ⟨hwD, hw2⟩ := (mem_omegaIn_iff_of_comm (fun a ha b hb => comm_of_mem dD ha hb)).mp hw
  have hv : (2 : ℤ) • dD.e (Additive.ofMul (⟨w, hwD⟩ : D)) = 0 := by
    rw [← map_zsmul, two_zsmul, ← ofMul_mul,
      show (⟨w, hwD⟩ : D) * ⟨w, hwD⟩ = 1 from Subtype.ext (by simpa [pow_two] using hw2),
      ofMul_one, map_zero]
  obtain ⟨ε, hε⟩ := exists_torusHalf_eq τ.k (one_le_of_two_le hk) hv
  have h0 : barD dD hk ⟨w, hwD⟩ = 0 := by
    rw [barD, ← hε]
    exact torusBar_torusHalf _ _ hk ε
  exact (barD_eq_zero_iff hk _).mp h0

theorem commutator_mem_omegaIn_one (dD : StrothWeakTypeData D τ) {x d : G} (hx : x ∈ 𝓡[S, D])
    (hd : d ∈ D) :
    x * d * x⁻¹ * d⁻¹ ∈ omegaIn 1 D := by
  have hxN := mem_normalizer_of_mem_R hx
  have hxd : x * d * x⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hxN d).mp hd
  have hd2 : d * d ∈ mhoOne D := by
    simpa [pow_two] using CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := D) (n := 2) hd
  have hc := Subgroup.mem_centralizer_iff.mp (mem_centralizer_of_mem_R hx) _ hd2
  have hxdd : (x * d * x⁻¹) * (x * d * x⁻¹) = d * d := by
    calc (x * d * x⁻¹) * (x * d * x⁻¹) = x * (d * d) * x⁻¹ := by group
      _ = (d * d) * x * x⁻¹ := by rw [← hc]
      _ = d * d := by group
  refine mem_omegaIn_one_of_mul_self (D.mul_mem hxd (D.inv_mem hd)) ?_
  have hcomm := comm_of_mem dD hxd (D.inv_mem hd)
  calc (x * d * x⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) =
        (x * d * x⁻¹) * ((x * d * x⁻¹) * d⁻¹) * d⁻¹ := by
        rw [mul_assoc (x * d * x⁻¹) d⁻¹, ← mul_assoc d⁻¹, ← hcomm]; group
    _ = ((x * d * x⁻¹) * (x * d * x⁻¹)) * (d * d)⁻¹ := by group
    _ = 1 := by rw [hxdd, mul_inv_cancel]

theorem commute_of_mem_omegaIn_one (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i) {x w : G}
    (hx : x ∈ 𝓡[S, D]) (hw : w ∈ omegaIn 1 D) : x * w * x⁻¹ = w := by
  have hc := Subgroup.mem_centralizer_iff.mp (mem_centralizer_of_mem_R hx) _
    (omegaIn_one_le_mhoOne dD hk hw)
  calc x * w * x⁻¹ = w * x * x⁻¹ := by rw [← hc]
    _ = w := by group

@[expose] noncomputable def devHom (dD : StrothWeakTypeData D τ) (x : G) (hx : x ∈ 𝓡[S, D]) :
    Additive D →+ Torus τ.k where
  toFun d := dD.e (Additive.ofMul ⟨x * ((Additive.toMul d : D) : G) * x⁻¹ *
    ((Additive.toMul d : D) : G)⁻¹,
    omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx (Additive.toMul d).2)⟩)
  map_zero' := by
    have : (⟨x * ((Additive.toMul (0 : Additive D) : D) : G) * x⁻¹ *
        ((Additive.toMul (0 : Additive D) : D) : G)⁻¹, omegaIn_le 1 D
        (commutator_mem_omegaIn_one dD hx (Additive.toMul (0 : Additive D)).2)⟩ : D) =
        1 := Subtype.ext (by simp)
    rw [this, ofMul_one, map_zero]
  map_add' a b := by
    rw [← map_add, ← ofMul_mul]
    congr 2
    apply Subtype.ext
    simp only [toMul_add, Subgroup.coe_mul, _root_.mul_inv_rev]
    have hxN := mem_normalizer_of_mem_R hx
    set p := ((Additive.toMul a : D) : G)
    set q := ((Additive.toMul b : D) : G)
    have hp : p ∈ D := (Additive.toMul a : D).2
    have hq : q ∈ D := (Additive.toMul b : D).2
    have hxq : x * q * x⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hxN q).mp hq
    have h1 : (x * q * x⁻¹) * p⁻¹ = p⁻¹ * (x * q * x⁻¹) := comm_of_mem dD hxq (D.inv_mem hp)
    have h2 : q⁻¹ * p⁻¹ = p⁻¹ * q⁻¹ := comm_of_mem dD (D.inv_mem hq) (D.inv_mem hp)
    calc x * (p * q) * x⁻¹ * (q⁻¹ * p⁻¹) = (x * p * x⁻¹) * ((x * q * x⁻¹) * (q⁻¹ * p⁻¹)) := by
          group
      _ = (x * p * x⁻¹) * ((x * q * x⁻¹) * (p⁻¹ * q⁻¹)) := by rw [h2]
      _ = (x * p * x⁻¹) * (((x * q * x⁻¹) * p⁻¹) * q⁻¹) := by group
      _ = (x * p * x⁻¹) * ((p⁻¹ * (x * q * x⁻¹)) * q⁻¹) := by rw [h1]
      _ = x * p * x⁻¹ * p⁻¹ * (x * q * x⁻¹ * q⁻¹) := by group

theorem devHom_apply (x : G) (hx : x ∈ 𝓡[S, D]) (d : D) :
    devHom dD x hx (Additive.ofMul d) = dD.e (Additive.ofMul ⟨x * d * x⁻¹ * (d : G)⁻¹,
      omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx d.2)⟩) := rfl

theorem two_zsmul_devHom (x : G) (hx : x ∈ 𝓡[S, D]) (d : D) :
    (2 : ℤ) • devHom dD x hx (Additive.ofMul d) = 0 := by
  rw [devHom_apply, ← map_zsmul, two_zsmul, ← ofMul_mul]
  have hmem := commutator_mem_omegaIn_one dD hx d.2
  have h := ((mem_omegaIn_iff_of_comm (fun a ha b hb => comm_of_mem dD ha hb)).mp hmem).2
  have : (⟨x * (d : G) * x⁻¹ * (d : G)⁻¹, omegaIn_le 1 D hmem⟩ : D) *
      ⟨x * (d : G) * x⁻¹ * (d : G)⁻¹, omegaIn_le 1 D hmem⟩ = 1 :=
    Subtype.ext (by simpa [pow_two] using h)
  rw [this, ofMul_one, map_zero]

theorem devHom_mul (hk : ∀ i, 2 ≤ τ.k i) {x y : G} (hx : x ∈ 𝓡[S, D]) (hy : y ∈ 𝓡[S, D]) :
    devHom dD (x * y) (mul_mem hx hy) = devHom dD x hx + devHom dD y hy := by
  refine AddMonoidHom.ext fun d => ?_
  obtain ⟨d, rfl⟩ : ∃ d' : D, Additive.ofMul d' = d := ⟨Additive.toMul d, rfl⟩
  rw [AddMonoidHom.add_apply, devHom_apply, devHom_apply, devHom_apply, ← map_add, ← ofMul_mul]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  set e := y * (d : G) * y⁻¹ * (d : G)⁻¹
  have heΩ : e ∈ omegaIn 1 D := commutator_mem_omegaIn_one dD hy d.2
  have hxe := commute_of_mem_omegaIn_one dD hk hx heΩ
  have heq : y * (d : G) * y⁻¹ = e * d := by simp only [e]; group
  have hxd : x * (d : G) * x⁻¹ * (d : G)⁻¹ ∈ D :=
    omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx d.2)
  have hcomm := comm_of_mem dD (omegaIn_le 1 D heΩ) hxd
  calc x * y * (d : G) * (x * y)⁻¹ * (d : G)⁻¹
      = x * (y * (d : G) * y⁻¹) * x⁻¹ * (d : G)⁻¹ := by group
    _ = (x * e * x⁻¹) * (x * (d : G) * x⁻¹ * (d : G)⁻¹) := by rw [heq]; group
    _ = e * (x * (d : G) * x⁻¹ * (d : G)⁻¹) := by rw [hxe]
    _ = (x * (d : G) * x⁻¹ * (d : G)⁻¹) * e := hcomm

theorem devHom_eq_zero_iff (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)
    {x : G} (hx : x ∈ 𝓡[S, D]) : devHom dD x hx = 0 ↔ x ∈ D := by
  constructor
  · intro h
    rw [← hcent]
    refine Subgroup.mem_inf.mpr ⟨mem_S_of_mem_R hx, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    have h1 := congrArg (fun φ : Additive D →+ Torus τ.k => φ (Additive.ofMul ⟨d, hd⟩)) h
    simp only [AddMonoidHom.zero_apply] at h1
    rw [devHom_apply] at h1
    have h2 := dD.e.injective (h1.trans (map_zero dD.e).symm)
    have h3 := congrArg (fun a : Additive D => ((Additive.toMul a : D) : G)) h2
    simp only [toMul_ofMul, toMul_zero, Subgroup.coe_one] at h3
    calc d * x = (x * d * x⁻¹ * d⁻¹)⁻¹ * (x * d) := by group
      _ = x * d := by rw [h3, inv_one, one_mul]
  · intro h
    refine AddMonoidHom.ext fun d => ?_
    obtain ⟨d, rfl⟩ : ∃ d' : D, Additive.ofMul d' = d := ⟨Additive.toMul d, rfl⟩
    rw [AddMonoidHom.zero_apply, devHom_apply]
    have hc := comm_of_mem dD h d.2
    have : (⟨x * (d : G) * x⁻¹ * (d : G)⁻¹, omegaIn_le 1 D
        (commutator_mem_omegaIn_one dD hx d.2)⟩ : D) = 1 :=
      Subtype.ext (by simp only [Subgroup.coe_one]; rw [hc]; group)
    rw [this, ofMul_one, map_zero]

theorem mul_self_mem_of_mem_R (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x : G} (hx : x ∈ 𝓡[S, D]) :
    x * x ∈ D := by
  rw [← hcent]
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mem_S_of_mem_R hx) (mem_S_of_mem_R hx),
    Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
  set e := x * d * x⁻¹ * d⁻¹
  have heΩ : e ∈ omegaIn 1 D := commutator_mem_omegaIn_one dD hx hd
  have hxe := commute_of_mem_omegaIn_one dD hk hx heΩ
  have he2 : e * e = 1 := by
    have := ((mem_omegaIn_iff_of_comm (fun a ha b hb => comm_of_mem dD ha hb)).mp heΩ).2
    simpa [pow_two] using this
  have h1 : x * d * x⁻¹ = e * d := by simp only [e]; group
  have h2 : (x * x) * d * (x * x)⁻¹ = d := by
    calc (x * x) * d * (x * x)⁻¹ = x * (x * d * x⁻¹) * x⁻¹ := by group
      _ = x * (e * d) * x⁻¹ := by rw [h1]
      _ = (x * e * x⁻¹) * (x * d * x⁻¹) := by group
      _ = e * (e * d) := by rw [hxe, h1]
      _ = d := by rw [← mul_assoc, he2, one_mul]
  calc d * (x * x) = (x * x) * ((x * x)⁻¹ * d * (x * x)) := by group
    _ = (x * x) * d := by
      rw [show (x * x)⁻¹ * d * (x * x) = d by
        calc (x * x)⁻¹ * d * (x * x) = (x * x)⁻¹ * ((x * x) * d * (x * x)⁻¹) * (x * x) := by
              rw [h2]
          _ = d := by group]

@[expose] noncomputable def genD (dD : StrothWeakTypeData D τ) (j : Fin 3) : D :=
  Additive.toMul (dD.e.symm (gen τ.k j))

@[expose] noncomputable def devMat (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i) (x : G)
    (hx : x ∈ 𝓡[S, D]) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j =>
    (exists_torusHalf_eq τ.k (one_le_of_two_le hk)
      (two_zsmul_devHom (dD := dD) x hx (genD dD j))).choose i

theorem torusHalf_devMat_col (hk : ∀ i, 2 ≤ τ.k i) (x : G) (hx : x ∈ 𝓡[S, D]) (j : Fin 3) :
    torusHalf τ.k (fun i => devMat dD hk x hx i j) =
      devHom dD x hx (Additive.ofMul (genD dD j)) :=
  (exists_torusHalf_eq τ.k (one_le_of_two_le hk)
    (two_zsmul_devHom (dD := dD) x hx (genD dD j))).choose_spec

theorem zsmul_eq_cast_smul (z : ℤ) (w : Fin 3 → ZMod 2) : z • w = (z : ZMod 2) • w := by
  funext i
  simp [zsmul_eq_mul]

theorem mulVec_eq_sum_smul_col (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (w : Fin 3 → ZMod 2) :
    M *ᵥ w = ∑ j, w j • fun i => M i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem devHom_eq_torusHalf (hk : ∀ i, 2 ≤ τ.k i) (x : G) (hx : x ∈ 𝓡[S, D]) (d : D) :
    devHom dD x hx (Additive.ofMul d) = torusHalf τ.k (devMat dD hk x hx *ᵥ barD dD hk d) := by
  set v := dD.e (Additive.ofMul d) with hv
  have hz : ∀ j, ∃ z : ℤ, (z : ZMod (2 ^ τ.k j)) = v j := fun j => ZMod.intCast_surjective _
  choose z hz using hz
  have hvsum : v = ∑ j, z j • gen τ.k j := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [gen, hz i]
    · intro j _ hji
      simp [gen, Pi.single_eq_of_ne' hji]
    · simp
  have hd : Additive.ofMul d = dD.e.symm v := by rw [hv, AddEquiv.symm_apply_apply]
  have hbar : barD dD hk d = fun j => ((z j : ℤ) : ZMod 2) := by
    funext j
    rw [barD, ← hv, torusBar_apply, ← hz j,
      ZMod.cast_intCast (dvd_pow_self 2 (by have := hk j; omega))]
  set f : Torus τ.k →+ Torus τ.k := (devHom dD x hx).comp dD.e.symm.toAddMonoidHom with hfdef
  have hf : ∀ w, devHom dD x hx (dD.e.symm w) = f w := fun w => rfl
  rw [hd, hf, hvsum, map_sum, hbar, mulVec_eq_sum_smul_col, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg : dD.e.symm (gen τ.k j) = Additive.ofMul (genD dD j) := by
    rw [genD, ofMul_toMul]
  rw [map_zsmul, ← hf, hg, ← torusHalf_devMat_col hk x hx j, ← map_zsmul, zsmul_eq_cast_smul]

theorem devMat_val_eq (hk : ∀ i, 2 ≤ τ.k i) (x : G) (hx : x ∈ 𝓡[S, D]) (d : D) :
    dD.e (Additive.ofMul ⟨x * d * x⁻¹ * (d : G)⁻¹,
        omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx d.2)⟩) =
      torusHalf τ.k (devMat dD hk x hx *ᵥ barD dD hk d) := by
  rw [← devHom_eq_torusHalf, devHom_apply]

omit [Finite G] in
theorem matrix_eq_of_mulVec_barD (hk : ∀ i, 2 ≤ τ.k i)
    {M N : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ d : D, M *ᵥ barD dD hk d = N *ᵥ barD dD hk d) : M = N := by
  have h' : ∀ w, M *ᵥ w = N *ᵥ w := fun w => by
    obtain ⟨d, rfl⟩ := barD_surjective (dD := dD) hk w
    exact h d
  ext i j
  have := congrFun (h' (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem devMat_mul (hk : ∀ i, 2 ≤ τ.k i) {x y : G} (hx : x ∈ 𝓡[S, D]) (hy : y ∈ 𝓡[S, D]) :
    devMat dD hk (x * y) (mul_mem hx hy) = devMat dD hk x hx + devMat dD hk y hy := by
  refine matrix_eq_of_mulVec_barD (dD := dD) hk fun d => ?_
  apply torusHalf_injective τ.k (one_le_of_two_le hk)
  rw [← devHom_eq_torusHalf, Matrix.add_mulVec, map_add, ← devHom_eq_torusHalf,
    ← devHom_eq_torusHalf, devHom_mul hk hx hy, AddMonoidHom.add_apply]

theorem devMat_eq_zero_iff (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x : G} (hx : x ∈ 𝓡[S, D]) :
    devMat dD hk x hx = 0 ↔ x ∈ D := by
  rw [← devHom_eq_zero_iff hcent hx]
  constructor
  · intro h
    refine AddMonoidHom.ext fun d => ?_
    obtain ⟨d, rfl⟩ : ∃ d' : D, Additive.ofMul d' = d := ⟨Additive.toMul d, rfl⟩
    rw [AddMonoidHom.zero_apply, devHom_eq_torusHalf hk, h, Matrix.zero_mulVec, map_zero]
  · intro h
    refine matrix_eq_of_mulVec_barD (dD := dD) hk fun d => ?_
    apply torusHalf_injective τ.k (one_le_of_two_le hk)
    rw [← devHom_eq_torusHalf, Matrix.zero_mulVec, map_zero, h, AddMonoidHom.zero_apply]

theorem devMat_congr (hk : ∀ i, 2 ≤ τ.k i) {x x' : G} (h : x = x') (hx : x ∈ 𝓡[S, D])
    (hx' : x' ∈ 𝓡[S, D]) : devMat dD hk x hx = devMat dD hk x' hx' := by
  subst h; rfl

theorem devMat_one (hk : ∀ i, 2 ≤ τ.k i) (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) :
    devMat (S := S) dD hk 1 (one_mem _) = (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  (devMat_eq_zero_iff hk hcent _).mpr D.one_mem

theorem eq_of_add_eq_zero_two {f g : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : f + g = 0) :
    g = f := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.zero_apply] at h'
  exact (eq_neg_of_add_eq_zero_right h').trans (CharTwo.neg_eq _)

theorem matrix_add_self (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : f + f = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

theorem devMat_inv (hk : ∀ i, 2 ≤ τ.k i) (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)
    {x : G} (hx : x ∈ 𝓡[S, D]) :
    devMat dD hk x⁻¹ (inv_mem hx) = devMat dD hk x hx := by
  have h := devMat_mul (dD := dD) hk hx (inv_mem hx)
  rw [devMat_congr hk (mul_inv_cancel x) _ (one_mem _), devMat_one hk hcent] at h
  exact eq_of_add_eq_zero_two h.symm

theorem inv_mul_mem_of_devMat_eq (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x y : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D]) (h : devMat dD hk x hx = devMat dD hk y hy) : x⁻¹ * y ∈ D := by
  rw [← devMat_eq_zero_iff (dD := dD) hk hcent (mul_mem (inv_mem hx) hy),
    devMat_mul hk (inv_mem hx) hy, devMat_inv hk hcent hx, h, matrix_add_self]

theorem commutator_mem_D (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x y : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D]) : x * y * x⁻¹ * y⁻¹ ∈ D := by
  have hxy : x * y ∈ 𝓡[S, D] := mul_mem hx hy
  have hyx : y * x ∈ 𝓡[S, D] := mul_mem hy hx
  have h := inv_mul_mem_of_devMat_eq (dD := dD) hk hcent hyx hxy (by
    rw [devMat_mul hk hy hx, devMat_mul hk hx hy, add_comm])
  have hconj : x * y * x⁻¹ * y⁻¹ = (y * x) * ((y * x)⁻¹ * (x * y)) * (y * x)⁻¹ := by group
  rw [hconj]
  exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_R hyx) _).mp h

theorem devMat_mul_eq_of_conj (hk : ∀ i, 2 ≤ τ.k i) {x y l : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D]) (hl : l ∈ Subgroup.normalizer (D : Set G)) {M : IntMat}
    {hM : Compat τ.k M}
    (hmat : ∀ d : D,
      dD.e (Additive.ofMul (conjBy hl d)) = matAct τ.k M hM (dD.e (Additive.ofMul d)))
    {A₁ A₂ : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hA₁ : ∀ v, torusBar τ.k (one_le_of_two_le hk) (matAct τ.k M hM v) =
      A₁ *ᵥ torusBar τ.k (one_le_of_two_le hk) v)
    (hA₂ : ∀ ε, matAct τ.k M hM (torusHalf τ.k ε) = torusHalf τ.k (A₂ *ᵥ ε))
    (hyx : ∀ d ∈ D, y * (l⁻¹ * d * l) * y⁻¹ * (l⁻¹ * d * l)⁻¹ =
      l⁻¹ * (x * d * x⁻¹ * d⁻¹) * l) :
    devMat dD hk y hy * A₁ = A₂ * devMat dD hk x hx := by
  refine matrix_eq_of_mulVec_barD (dD := dD) hk fun d => ?_
  apply torusHalf_injective τ.k (one_le_of_two_le hk)
  have hbar : barD dD hk (conjBy hl d) = A₁ *ᵥ barD dD hk d := by
    rw [barD, hmat, hA₁]
    rfl
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hbar, ← devMat_val_eq, ← hA₂,
    ← devMat_val_eq, ← hmat]
  congr 2
  apply Subtype.ext
  simp only [conjBy]
  exact hyx d d.2

theorem barD_conj_of_mem (hk : ∀ i, 2 ≤ τ.k i) {y : G} (hy : y ∈ 𝓡[S, D]) (d : D) :
    barD dD hk ⟨y * d * y⁻¹,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_R hy) (d : G)).mp d.2⟩ =
      barD dD hk d := by
  have hφ : (⟨y * d * y⁻¹,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_R hy) (d : G)).mp d.2⟩ : D) =
      ⟨y * d * y⁻¹ * (d : G)⁻¹, omegaIn_le 1 D (commutator_mem_omegaIn_one dD hy d.2)⟩ * d :=
    Subtype.ext (by simp)
  rw [hφ, barD_mul]
  have h0 : barD dD hk ⟨y * d * y⁻¹ * (d : G)⁻¹, omegaIn_le 1 D
      (commutator_mem_omegaIn_one dD hy d.2)⟩ = 0 := by
    rw [barD, devMat_val_eq hk y hy d]
    exact torusBar_torusHalf _ _ hk _
  rw [h0, zero_add]

@[expose] noncomputable def sqBar (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) (x : G) (hx : x ∈ 𝓡[S, D]) :
    Fin 3 → ZMod 2 :=
  barD dD hk ⟨x * x, mul_self_mem_of_mem_R dD hk hcent hx⟩

variable (hk : ∀ i, 2 ≤ τ.k i) (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)

theorem sqBar_congr {x x' : G} (h : x = x') (hx : x ∈ 𝓡[S, D]) (hx' : x' ∈ 𝓡[S, D]) :
    sqBar dD hk hcent x hx = sqBar dD hk hcent x' hx' := by
  subst h; rfl

theorem devMat_mulVec_sqBar {x : G} (hx : x ∈ 𝓡[S, D]) :
    devMat dD hk x hx *ᵥ sqBar dD hk hcent x hx = 0 := by
  apply torusHalf_injective τ.k (one_le_of_two_le hk)
  rw [sqBar, ← devMat_val_eq, map_zero]
  have h1 : (⟨x * (x * x) * x⁻¹ * (x * x)⁻¹, omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx
      (mul_self_mem_of_mem_R dD hk hcent hx))⟩ : D) = 1 :=
    Subtype.ext (by simp only [Subgroup.coe_one]; group)
  rw [h1, ofMul_one, map_zero]

theorem sqBar_mul {x y : G} (hx : x ∈ 𝓡[S, D]) (hy : y ∈ 𝓡[S, D]) :
    sqBar dD hk hcent (x * y) (mul_mem hx hy) =
      sqBar dD hk hcent x hx + sqBar dD hk hcent y hy +
        barD dD hk ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ := by
  set w : D := ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩
  set x2 : D := ⟨x * x, mul_self_mem_of_mem_R dD hk hcent hx⟩
  set y2 : D := ⟨y * y, mul_self_mem_of_mem_R dD hk hcent hy⟩
  have hc : (⟨(x * y) * (x * y), mul_self_mem_of_mem_R dD hk hcent (mul_mem hx hy)⟩ : D) =
      w * ⟨y * x2 * y⁻¹, (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_R hy)
        (x2 : G)).mp x2.2⟩ * y2 :=
    Subtype.ext (by simp [w, x2, y2]; group)
  rw [sqBar, hc, barD_mul, barD_mul, barD_conj_of_mem hk hy x2, sqBar, sqBar]
  abel

theorem sqBar_mul_D (hDS : D ≤ S) {x d : G} (hx : x ∈ 𝓡[S, D]) (hd : d ∈ D) :
    sqBar dD hk hcent (x * d) (mul_mem hx (D_le_R dD hDS hd)) = sqBar dD hk hcent x hx := by
  rw [sqBar_mul hk hcent hx (D_le_R dD hDS hd)]
  have h1 : sqBar dD hk hcent d (D_le_R dD hDS hd) = 0 := by
    rw [sqBar, show (⟨d * d, mul_self_mem_of_mem_R dD hk hcent (D_le_R dD hDS hd)⟩ : D) =
      ⟨d, hd⟩ * ⟨d, hd⟩ from rfl, barD_mul, barD_add_self]
  have h2 : barD dD hk ⟨x * d * x⁻¹ * d⁻¹, commutator_mem_D dD hk hcent hx
      (D_le_R dD hDS hd)⟩ = 0 := by
    have := devMat_val_eq (dD := dD) hk x hx ⟨d, hd⟩
    rw [barD]
    convert torusBar_torusHalf _ (one_le_of_two_le hk) hk _ using 2
    exact this
  rw [h1, h2, add_zero, add_zero]

theorem sqBar_eq_of_devMat_eq (hDS : D ≤ S) {x y : G} (hx : x ∈ 𝓡[S, D]) (hy : y ∈ 𝓡[S, D])
    (h : devMat dD hk x hx = devMat dD hk y hy) :
    sqBar dD hk hcent x hx = sqBar dD hk hcent y hy := by
  have hd := inv_mul_mem_of_devMat_eq hk hcent hx hy h
  rw [← sqBar_mul_D hk hcent hDS hx hd]
  exact sqBar_congr hk hcent (by group) _ _

theorem sqBar_conj {x l : G} (hx : x ∈ 𝓡[S, D]) (hl : l ∈ Subgroup.normalizer (D : Set G))
    (hlx : l⁻¹ * x * l ∈ 𝓡[S, D]) {M : IntMat} {hM : Compat τ.k M}
    (hmat : ∀ d : D,
      dD.e (Additive.ofMul (conjBy hl d)) = matAct τ.k M hM (dD.e (Additive.ofMul d)))
    {A₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hA₁ : ∀ v, torusBar τ.k (one_le_of_two_le hk) (matAct τ.k M hM v) =
      A₁ *ᵥ torusBar τ.k (one_le_of_two_le hk) v) :
    sqBar dD hk hcent (l⁻¹ * x * l) hlx = A₁ *ᵥ sqBar dD hk hcent x hx := by
  have h : (⟨(l⁻¹ * x * l) * (l⁻¹ * x * l), mul_self_mem_of_mem_R dD hk hcent hlx⟩ : D) =
      conjBy hl ⟨x * x, mul_self_mem_of_mem_R dD hk hcent hx⟩ :=
    Subtype.ext (by simp [conjBy]; group)
  rw [sqBar, h, barD, hmat, hA₁]
  rfl

end DeviationGeneric

end CFSG.CGT.Stroth77
