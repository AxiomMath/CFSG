module

public import CFSG.CGT.Stroth77.Section42CoreSplit

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core

namespace Stroth42Core

theorem zmod_even_iff_cast {m : ℕ} (hm : 1 ≤ m) (x : ZMod (2 ^ m)) :
    Even x ↔ ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) x = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [even_intCast_iff hm, map_intCast, ZMod.intCast_eq_zero_iff_even]

theorem zmod_even_add_iff {m : ℕ} (hm : 1 ≤ m) (x y : ZMod (2 ^ m)) :
    Even (x + y) ↔ (Even x ↔ Even y) := by
  rw [zmod_even_iff_cast hm, zmod_even_iff_cast hm, zmod_even_iff_cast hm, map_add]
  generalize ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) x = a
  generalize ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) y = b
  revert a b
  decide

theorem zmod_not_even_one {m : ℕ} (hm : 1 ≤ m) : ¬ Even (1 : ZMod (2 ^ m)) := by
  rw [zmod_even_iff_cast hm, map_one]
  decide

end Stroth42Core

theorem compat_diagonal {k : Fin 3 → ℕ} (d : Fin 3 → ℤ) : Compat k (Matrix.diagonal d) := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

@[expose] def torusDiag (k : Fin 3 → ℕ) (d : Fin 3 → ℤ) : Torus k →+ Torus k :=
  matAct k (Matrix.diagonal d) (compat_diagonal d)

theorem torusDiag_ofInt {k : Fin 3 → ℕ} (d x : Fin 3 → ℤ) :
    torusDiag k d (Torus.ofInt k x) = Torus.ofInt k (fun i => d i * x i) := by
  rw [torusDiag, matAct_ofInt]
  congr 1
  funext i
  simp [Matrix.mulVec_diagonal]

theorem torusDiag_gen {k : Fin 3 → ℕ} (d : Fin 3 → ℤ) (j : Fin 3) :
    torusDiag k d (gen k j) = d j • gen k j := by
  rw [torusDiag, matAct_gen_eq]
  fin_cases j <;> simp [Matrix.diagonal_apply]

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem ofTorus_zsmul (z : ℤ) (v : Torus τ.k) : dD.ofTorus (z • v) = dD.ofTorus v ^ z := by
  rcases z with z | z
  · rw [Int.ofNat_eq_coe, natCast_zsmul, ofTorus_nsmul, zpow_natCast]
  · rw [Int.negSucc_eq, neg_zsmul, ofTorus_neg, zpow_neg]
    congr 1
    rw [← Int.natCast_succ, natCast_zsmul, ofTorus_nsmul, zpow_natCast]

theorem ofTorus_ofInt (x : Fin 3 → ℤ) :
    dD.ofTorus (Torus.ofInt τ.k x) = (dD.c : G) ^ x 0 * (dD.a : G) ^ x 1 * (dD.b : G) ^ x 2 := by
  rw [Torus.ofInt_eq_zsmul_gens, ofTorus_add, ofTorus_add, ofTorus_zsmul, ofTorus_zsmul,
    ofTorus_zsmul, ← c_eq, ← a_eq, ← b_eq]

theorem conj_ofTorus_of_gens {g : G} {φ : Torus τ.k →+ Torus τ.k}
    (hc : g⁻¹ * (dD.c : G) * g = dD.ofTorus (φ Torus.c))
    (ha : g⁻¹ * (dD.a : G) * g = dD.ofTorus (φ Torus.a))
    (hb : g⁻¹ * (dD.b : G) * g = dD.ofTorus (φ Torus.b)) (v : Torus τ.k) :
    g⁻¹ * dD.ofTorus v * g = dD.ofTorus (φ v) := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [Torus.ofInt_eq_zsmul_gens, ofTorus_add, ofTorus_add, ofTorus_zsmul, ofTorus_zsmul,
    ofTorus_zsmul, ← c_eq, ← a_eq, ← b_eq, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    ofTorus_add, ofTorus_add, ofTorus_zsmul, ofTorus_zsmul, ofTorus_zsmul, ← hc, ← ha, ← hb]
  simp only [← MulAut.conj_inv_apply, map_mul, map_zpow]

structure EAction (e : G) where
  φe : Torus τ.k →+ Torus τ.k
  wuv : Torus τ.k
  wt : Torus τ.k
  ve : Torus τ.k
  conj_ofTorus : ∀ v, e⁻¹ * dD.ofTorus v * e = dD.ofTorus (φe v)
  conj_uv : e⁻¹ * dD.uv * e = dD.ofTorus wuv * dD.uv
  conj_t : e⁻¹ * dD.t * e = dD.ofTorus wt * dD.t
  conj_u : e⁻¹ * dD.u * e = dD.u
  mul_self : e * e = dD.ofTorus ve

namespace EAction

variable {dD} {e : G} (hE : dD.EAction e)

@[expose] def twist (i j : Bool) : Torus τ.k :=
  (if i then hE.wuv else 0) + τ.action.d8Act i false false (if j then hE.wt else 0)

theorem conj_mul (x y : G) : e⁻¹ * (x * y) * e = e⁻¹ * x * e * (e⁻¹ * y * e) := by group

theorem ofTorus_mul_ofTorus_mul (v w : Torus τ.k) (x : G) :
    dD.ofTorus v * (dD.ofTorus w * x) = dD.ofTorus (v + w) * x := by
  rw [← mul_assoc, ← dD.ofTorus_add]

theorem conj_d8 (i j l : Bool) :
    e⁻¹ * dD.d8 i j l * e = dD.ofTorus (hE.twist i j) * dD.d8 i j l := by
  have h1 : e⁻¹ * (1 : G) * e = 1 := by group
  cases i <;> cases j <;> cases l <;>
    simp only [d8, twist, Bool.false_eq_true, ↓reduceIte, conj_mul, h1, hE.conj_uv, hE.conj_t,
      hE.conj_u, one_mul, mul_one, inv_mul_cancel, add_zero, zero_add, map_zero, ofTorus_zero,
      SigmaFourAction.d8Act, AddMonoidHom.comp_apply, AddMonoidHom.id_apply] <;>
    (try simp only [mul_assoc, dD.uv_mul_ofTorus_mul, dD.uv_mul_ofTorus, ofTorus_mul_ofTorus_mul])

theorem conj_nf (v : Torus τ.k) (i j l : Bool) :
    e⁻¹ * (dD.ofTorus v * dD.d8 i j l) * e =
      dD.ofTorus (hE.φe v + hE.twist i j) * dD.d8 i j l := by
  rw [conj_mul, hE.conj_ofTorus, hE.conj_d8, ← mul_assoc, ← dD.ofTorus_add]

theorem ofTorus_mul_e (v : Torus τ.k) :
    dD.ofTorus v * e = e * dD.ofTorus (hE.φe v) := by
  rw [← hE.conj_ofTorus]
  group

theorem conj_inv_ofTorus (v : Torus τ.k) :
    e * dD.ofTorus v * e⁻¹ = dD.ofTorus (hE.φe v) := by
  have h2 : dD.ofTorus hE.ve * dD.ofTorus v * (dD.ofTorus hE.ve)⁻¹ = dD.ofTorus v := by
    rw [← dD.ofTorus_neg, ← dD.ofTorus_add, ← dD.ofTorus_add, add_comm hE.ve v,
      add_neg_cancel_right]
  calc e * dD.ofTorus v * e⁻¹ = e⁻¹ * ((e * e) * dD.ofTorus v * (e * e)⁻¹) * e := by group
    _ = e⁻¹ * dD.ofTorus v * e := by rw [hE.mul_self, h2]
    _ = dD.ofTorus (hE.φe v) := hE.conj_ofTorus v

theorem e_mul_ofTorus (v : Torus τ.k) : e * dD.ofTorus v = dD.ofTorus (hE.φe v) * e := by
  rw [← hE.conj_inv_ofTorus]
  group

theorem conj_inv_nf (v : Torus τ.k) (i j l : Bool) :
    e * (dD.ofTorus v * dD.d8 i j l) * e⁻¹ =
      dD.ofTorus (hE.φe (hE.ve + v - τ.action.d8Act i j l hE.ve) + hE.twist i j) *
        dD.d8 i j l := by
  have h2 : dD.ofTorus hE.ve * (dD.ofTorus v * dD.d8 i j l) * (dD.ofTorus hE.ve)⁻¹ =
      dD.ofTorus (hE.ve + v - τ.action.d8Act i j l hE.ve) * dD.d8 i j l := by
    rw [← dD.ofTorus_neg, mul_assoc, mul_assoc, dD.d8_mul_ofTorus, ofTorus_mul_ofTorus_mul,
      ofTorus_mul_ofTorus_mul, map_neg, ← sub_eq_add_neg]
  calc e * (dD.ofTorus v * dD.d8 i j l) * e⁻¹ =
      e⁻¹ * ((e * e) * (dD.ofTorus v * dD.d8 i j l) * (e * e)⁻¹) * e := by group
    _ = e⁻¹ * (dD.ofTorus (hE.ve + v - τ.action.d8Act i j l hE.ve) * dD.d8 i j l) * e := by
      rw [hE.mul_self, h2]
    _ = _ := hE.conj_nf _ i j l

include hE in
theorem mem_normalizer :
    e ∈ Subgroup.normalizer
      ((D ⊔ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
    rw [hE.conj_nf]
    exact dD.nf_mem _ i j l
  · intro hy
    obtain ⟨v, i, j, l, hv⟩ := dD.mem_sup_iff.mp hy
    have : y = e * (dD.ofTorus v * dD.d8 i j l) * e⁻¹ := by rw [← hv]; group
    rw [this, hE.conj_inv_nf]
    exact dD.nf_mem _ i j l

theorem zpow_two_mul (q : ℤ) : e ^ (2 * q) = dD.ofTorus (q • hE.ve) := by
  rw [ofTorus_zsmul, ← hE.mul_self, zpow_mul, zpow_two]

include hE in
theorem mem_sup_zpowers_iff {y : G} :
    y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e ↔
      ∃ (v : Torus τ.k) (i j l k : Bool), y = dD.ofTorus v * dD.d8 i j l * bpow e k := by
  have hle : Subgroup.zpowers e ≤ Subgroup.normalizer
      ((D ⊔ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).mpr hE.mem_normalizer
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle, Set.mem_mul]
  constructor
  · rintro ⟨s, hs, z, hz, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hs
    have hn : n = 2 * (n / 2) + n % 2 := by omega
    have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have hsplit : e ^ n = dD.ofTorus ((n / 2) • hE.ve) * bpow e (decide (n % 2 = 1)) := by
      conv_lhs => rw [hn]
      rw [zpow_add, hE.zpow_two_mul]
      rcases hr with h | h <;> simp [h, bpow]
    rw [hsplit, ← mul_assoc, mul_assoc (dD.ofTorus v), dD.d8_mul_ofTorus, ← mul_assoc,
      ← dD.ofTorus_add]
    exact ⟨_, i, j, l, _, rfl⟩
  · rintro ⟨v, i, j, l, k, rfl⟩
    refine ⟨_, dD.nf_mem v i j l, bpow e k, ?_, rfl⟩
    cases k
    · exact one_mem _
    · exact Subgroup.mem_zpowers e

include hE in
theorem nfe_mem (v : Torus τ.k) (i j l k : Bool) :
    dD.ofTorus v * dD.d8 i j l * bpow e k ∈
      D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
  hE.mem_sup_zpowers_iff.mpr ⟨v, i, j, l, k, rfl⟩

@[expose] def eStep (v : Torus τ.k) (i j l k : Bool) : Torus τ.k :=
  hE.φe v + hE.φe (hE.ve - τ.action.d8Act i j l hE.ve) + hE.twist i j +
    (if k then τ.action.d8Act i j l hE.ve else 0)

theorem conj_inv_d8 (i j l : Bool) :
    e * dD.d8 i j l * e⁻¹ =
      dD.ofTorus (hE.φe (hE.ve - τ.action.d8Act i j l hE.ve) + hE.twist i j) * dD.d8 i j l := by
  have h := hE.conj_inv_nf 0 i j l
  rwa [ofTorus_zero, one_mul, add_zero] at h

theorem e_mul_d8 (i j l : Bool) :
    e * dD.d8 i j l =
      dD.ofTorus (hE.φe (hE.ve - τ.action.d8Act i j l hE.ve) + hE.twist i j) * dD.d8 i j l * e := by
  rw [← hE.conj_inv_d8]
  group

theorem e_mul_nfe (v : Torus τ.k) (i j l k : Bool) :
    e * (dD.ofTorus v * dD.d8 i j l * bpow e k) =
      dD.ofTorus (hE.eStep v i j l k) * dD.d8 i j l * bpow e (!k) := by
  have hsplit : e * (dD.ofTorus v * dD.d8 i j l * bpow e k) =
      (e * dD.ofTorus v * e⁻¹) * (e * dD.d8 i j l * e⁻¹) * (e * bpow e k) := by group
  rw [hsplit, hE.conj_inv_ofTorus, hE.conj_inv_d8,
    ← mul_assoc (dD.ofTorus _) (dD.ofTorus _) (dD.d8 i j l), ← dD.ofTorus_add]
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one, Bool.not_false, eStep, add_zero,
      add_assoc]
  · simp only [bpow, ↓reduceIte, Bool.not_true, Bool.false_eq_true, mul_one, eStep]
    rw [hE.mul_self, mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]
    simp only [add_assoc]

theorem ofTorus_mul_nfe (w v : Torus τ.k) (i j l k : Bool) :
    dD.ofTorus w * (dD.ofTorus v * dD.d8 i j l * bpow e k) =
      dD.ofTorus (w + v) * dD.d8 i j l * bpow e k := by
  rw [← mul_assoc, ← mul_assoc, ← dD.ofTorus_add]

theorem uv_mul_nfe (v : Torus τ.k) (i j l k : Bool) :
    dD.uv * (dD.ofTorus v * dD.d8 i j l * bpow e k) =
      dD.ofTorus (τ.action.φuv v) * dD.d8 (!i) j l * bpow e k := by
  rw [← mul_assoc, ← mul_assoc, dD.uv_mul_ofTorus, mul_assoc _ dD.uv, dD.uv_mul_d8]

theorem t_mul_nfe (v : Torus τ.k) (i j l k : Bool) :
    dD.t * (dD.ofTorus v * dD.d8 i j l * bpow e k) =
      dD.ofTorus (τ.action.φt v) * dD.d8 i (!j) l * bpow e k := by
  rw [← mul_assoc, ← mul_assoc, dD.t_mul_ofTorus, mul_assoc _ dD.t, dD.t_mul_d8]

theorem u_mul_nfe (v : Torus τ.k) (i j l k : Bool) :
    dD.u * (dD.ofTorus v * dD.d8 i j l * bpow e k) =
      dD.ofTorus (τ.action.φu v) * dD.d8 (xor i j) j (!l) * bpow e k := by
  rw [← mul_assoc, ← mul_assoc, dD.u_mul_ofTorus, mul_assoc _ dD.u, dD.u_mul_d8]

theorem e_inv_eq : e⁻¹ = dD.ofTorus (-hE.ve) * e := by
  rw [dD.ofTorus_neg, ← hE.mul_self]
  group

theorem even_eStep_iff (hk0 : 1 ≤ τ.k 0)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (hve : Even (hE.ve 0)) (v : Torus τ.k) (i j l k : Bool) :
    Even ((hE.eStep v i j l k) 0) ↔ Even (v 0) := by
  have hdv : Even ((τ.action.d8Act i j l hE.ve) 0) := (hP i j l _).mpr hve
  have h1 : Even ((hE.φe (hE.ve - τ.action.d8Act i j l hE.ve)) 0) := by
    rw [hPe, Pi.sub_apply, sub_eq_add_neg]
    exact (zmod_even_add_iff hk0 _ _).mpr ⟨fun _ => hdv.neg, fun _ => hve⟩
  have h2 : Even ((hE.twist i j) 0) := by
    simp only [twist, Pi.add_apply]
    refine (zmod_even_add_iff hk0 _ _).mpr ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [hP]
      cases j
      · exact ⟨0, by simp⟩
      · exact hwt
    · cases i
      · exact ⟨0, by simp⟩
      · exact hwuv
  have h3 : Even ((if k then τ.action.d8Act i j l hE.ve else 0) 0) := by
    cases k
    · exact ⟨0, by simp⟩
    · exact hdv
  simp only [eStep, Pi.add_apply]
  rw [zmod_even_add_iff hk0, zmod_even_add_iff hk0, zmod_even_add_iff hk0, hPe]
  tauto

theorem mem_S₁e_iff (hk0 : 1 ≤ τ.k 0)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (hve : Even (hE.ve 0)) {y : G} :
    y ∈ Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} : Set G) ↔
      ∃ (v : Torus τ.k) (i j l k : Bool), Even (v 0) ∧
        y = dD.ofTorus v * dD.d8 i j l * bpow e k := by
  have hPuv : ∀ v : Torus τ.k, Even ((τ.action.φuv v) 0) ↔ Even (v 0) := fun v => by
    simpa [SigmaFourAction.d8Act] using hP true false false v
  have hPt : ∀ v : Torus τ.k, Even ((τ.action.φt v) 0) ↔ Even (v 0) := fun v => by
    simpa [SigmaFourAction.d8Act] using hP false true false v
  have hPu : ∀ v : Torus τ.k, Even ((τ.action.φu v) 0) ↔ Even (v 0) := fun v => by
    simpa [SigmaFourAction.d8Act] using hP false false true v
  have hev : ∀ w : Torus τ.k, Even (w 0) → ∀ v : Torus τ.k, (Even ((w + v) 0) ↔ Even (v 0)) :=
    fun w hw v => by
      rw [Pi.add_apply, zmod_even_add_iff hk0]
      tauto
  have hc2 : (dD.c : G) ^ 2 = dD.ofTorus (Torus.c + Torus.c) := by
    rw [ofTorus_add, ← c_eq, sq]
  have hc2e : Even ((Torus.c + Torus.c : Torus τ.k) 0) := ⟨Torus.c 0, rfl⟩
  have hae : Even ((Torus.a : Torus τ.k) 0) := ⟨0, by simp [gen]⟩
  have hbe : Even ((Torus.b : Torus τ.k) 0) := ⟨0, by simp [gen]⟩
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction_left with
    | one =>
      exact ⟨0, false, false, false, false, ⟨0, by simp⟩, by
        simp [d8, bpow, ofTorus_zero]⟩
    | mul_left x hx y _ ih =>
      obtain ⟨v, i, j, l, k, hv, rfl⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hc2, ofTorus_mul_nfe]
        exact ⟨_, i, j, l, k, (hev _ hc2e v).mpr hv, rfl⟩
      · rw [a_eq, ofTorus_mul_nfe]
        exact ⟨_, i, j, l, k, (hev _ hae v).mpr hv, rfl⟩
      · rw [b_eq, ofTorus_mul_nfe]
        exact ⟨_, i, j, l, k, (hev _ hbe v).mpr hv, rfl⟩
      · rw [uv_mul_nfe]
        exact ⟨_, _, j, l, k, (hPuv v).mpr hv, rfl⟩
      · rw [t_mul_nfe]
        exact ⟨_, i, _, l, k, (hPt v).mpr hv, rfl⟩
      · rw [u_mul_nfe]
        exact ⟨_, _, j, _, k, (hPu v).mpr hv, rfl⟩
      · rw [hE.e_mul_nfe]
        exact ⟨_, i, j, l, _, (hE.even_eStep_iff hk0 hP hPe hwuv hwt hve v i j l k).mpr hv, rfl⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨v, i, j, l, k, hv, rfl⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hc2, ← dD.ofTorus_neg, ofTorus_mul_nfe]
        exact ⟨_, i, j, l, k, (hev _ (by simpa using hc2e.neg) v).mpr hv, rfl⟩
      · rw [a_eq, ← dD.ofTorus_neg, ofTorus_mul_nfe]
        exact ⟨_, i, j, l, k, (hev _ (by simpa using hae.neg) v).mpr hv, rfl⟩
      · rw [b_eq, ← dD.ofTorus_neg, ofTorus_mul_nfe]
        exact ⟨_, i, j, l, k, (hev _ (by simpa using hbe.neg) v).mpr hv, rfl⟩
      · rw [dD.uv_inv, uv_mul_nfe]
        exact ⟨_, _, j, l, k, (hPuv v).mpr hv, rfl⟩
      · rw [dD.t_inv, t_mul_nfe]
        exact ⟨_, i, _, l, k, (hPt v).mpr hv, rfl⟩
      · rw [dD.u_inv, u_mul_nfe]
        exact ⟨_, _, j, _, k, (hPu v).mpr hv, rfl⟩
      · rw [hE.e_inv_eq, mul_assoc, hE.e_mul_nfe, ofTorus_mul_nfe]
        refine ⟨_, i, j, l, _, ?_, rfl⟩
        rw [hev _ (by simpa using hve.neg)]
        exact (hE.even_eStep_iff hk0 hP hPe hwuv hwt hve v i j l k).mpr hv
  · rintro ⟨v, i, j, l, k, hv, rfl⟩
    have hgen : ∀ x ∈ ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} : Set G),
        x ∈ Subgroup.closure
          ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} : Set G) :=
      fun x hx => Subgroup.subset_closure hx
    have hS₁ : Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G) ≤
        Subgroup.closure
          ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgen _ (by simp)
    refine mul_mem (hS₁ ((dD.mem_S₁_iff hk0 hP).mpr ⟨v, i, j, l, hv, rfl⟩)) ?_
    cases k
    · exact one_mem _
    · exact hgen e (by simp)

@[expose] def cMul (hcu : τ.action.φu Torus.c = Torus.c) : dD.EAction ((dD.c : G) * e) where
  φe := hE.φe
  wuv := hE.φe (τ.action.φuv Torus.c - Torus.c) + hE.wuv
  wt := hE.φe (τ.action.φt Torus.c - Torus.c) + hE.wt
  ve := Torus.c + hE.φe Torus.c + hE.ve
  conj_ofTorus v := by
    have h : ((dD.c : G) * e)⁻¹ * dD.ofTorus v * ((dD.c : G) * e) =
        e⁻¹ * ((dD.c : G)⁻¹ * dD.ofTorus v * (dD.c : G)) * e := by group
    rw [h, c_eq, ← dD.ofTorus_neg, ← dD.ofTorus_add, ← dD.ofTorus_add, neg_add_cancel_comm,
      hE.conj_ofTorus]
  conj_uv := by
    have h : ((dD.c : G) * e)⁻¹ * dD.uv * ((dD.c : G) * e) =
        e⁻¹ * ((dD.c : G)⁻¹ * (dD.uv * (dD.c : G))) * e := by group
    have h1 : (dD.c : G)⁻¹ * (dD.uv * (dD.c : G)) =
        dD.ofTorus (τ.action.φuv Torus.c - Torus.c) * dD.d8 true false false := by
      rw [c_eq, dD.uv_mul_ofTorus, ← dD.ofTorus_neg, ← mul_assoc, ← dD.ofTorus_add,
        neg_add_eq_sub, dD.d8_tff]
    rw [h, h1, hE.conj_nf, dD.d8_tff]
    congr 2
    simp only [twist, ↓reduceIte, Bool.false_eq_true, map_zero, add_zero]
  conj_t := by
    have h : ((dD.c : G) * e)⁻¹ * dD.t * ((dD.c : G) * e) =
        e⁻¹ * ((dD.c : G)⁻¹ * (dD.t * (dD.c : G))) * e := by group
    have h1 : (dD.c : G)⁻¹ * (dD.t * (dD.c : G)) =
        dD.ofTorus (τ.action.φt Torus.c - Torus.c) * dD.d8 false true false := by
      rw [c_eq, dD.t_mul_ofTorus, ← dD.ofTorus_neg, ← mul_assoc, ← dD.ofTorus_add,
        neg_add_eq_sub, dD.d8_ftf]
    rw [h, h1, hE.conj_nf, dD.d8_ftf]
    congr 2
    simp only [twist, ↓reduceIte, Bool.false_eq_true, zero_add,
      SigmaFourAction.d8Act, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  conj_u := by
    have h : ((dD.c : G) * e)⁻¹ * dD.u * ((dD.c : G) * e) =
        e⁻¹ * ((dD.c : G)⁻¹ * (dD.u * (dD.c : G))) * e := by group
    have h1 : (dD.c : G)⁻¹ * (dD.u * (dD.c : G)) = dD.u := by
      rw [c_eq, dD.u_mul_ofTorus, hcu, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h, h1, hE.conj_u]
  mul_self := by
    have h : (dD.c : G) * e * ((dD.c : G) * e) = (dD.c : G) * (e * (dD.c : G) * e⁻¹) * (e * e) := by
      group
    rw [h, c_eq, hE.conj_inv_ofTorus, hE.mul_self, ← dD.ofTorus_add, ← dD.ofTorus_add]

theorem mem_S₂_iff (hk0 : 1 ≤ τ.k 0)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (hve : Even (hE.ve 0)) (hcu : τ.action.φu Torus.c = Torus.c) {y : G} :
    y ∈ Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, (dD.c : G) * e} : Set G) ↔
      ∃ (v : Torus τ.k) (i j l k : Bool), Even (v 0 + (if k then 1 else 0)) ∧
        y = dD.ofTorus v * dD.d8 i j l * bpow e k := by
  have hc1 : ((Torus.c : Torus τ.k) 0) = 1 := by simp [gen]
  have hco : ¬ Even ((Torus.c : Torus τ.k) 0) := by rw [hc1]; exact zmod_not_even_one hk0
  have hdiff : ∀ φ : Torus τ.k →+ Torus τ.k, (∀ v, Even ((φ v) 0) ↔ Even (v 0)) →
      Even ((φ Torus.c - Torus.c : Torus τ.k) 0) := by
    intro φ hφ
    rw [Pi.sub_apply, sub_eq_add_neg, zmod_even_add_iff hk0]
    constructor
    · intro h; exact absurd ((hφ _).mp h) hco
    · intro h; exact absurd (by simpa using h.neg) hco
  have hPuv : ∀ v : Torus τ.k, Even ((τ.action.φuv v) 0) ↔ Even (v 0) := fun v => by
    simpa [SigmaFourAction.d8Act] using hP true false false v
  have hPt : ∀ v : Torus τ.k, Even ((τ.action.φt v) 0) ↔ Even (v 0) := fun v => by
    simpa [SigmaFourAction.d8Act] using hP false true false v
  have hE' := hE.cMul hcu
  have hwuv' : Even ((hE.cMul hcu).wuv 0) := by
    show Even ((hE.φe (τ.action.φuv Torus.c - Torus.c) + hE.wuv) 0)
    rw [Pi.add_apply]
    exact ((hPe _).mpr (hdiff _ hPuv)).add hwuv
  have hwt' : Even ((hE.cMul hcu).wt 0) := by
    show Even ((hE.φe (τ.action.φt Torus.c - Torus.c) + hE.wt) 0)
    rw [Pi.add_apply]
    exact ((hPe _).mpr (hdiff _ hPt)).add hwt
  have hve' : Even ((hE.cMul hcu).ve 0) := by
    show Even ((Torus.c + hE.φe Torus.c + hE.ve : Torus τ.k) 0)
    rw [Pi.add_apply, Pi.add_apply]
    refine Even.add ?_ hve
    rw [zmod_even_add_iff hk0, hPe]
  rw [(hE.cMul hcu).mem_S₁e_iff hk0 hP hPe hwuv' hwt' hve']
  have hconv : ∀ (v : Torus τ.k) (i j l k : Bool),
      dD.ofTorus v * dD.d8 i j l * bpow ((dD.c : G) * e) k =
        dD.ofTorus (v + if k then τ.action.d8Act i j l Torus.c else 0) * dD.d8 i j l *
          bpow e k := by
    intro v i j l k
    cases k
    · simp [bpow]
    · simp only [bpow, ↓reduceIte]
      rw [c_eq, ← mul_assoc, mul_assoc (dD.ofTorus v), dD.d8_mul_ofTorus, ← mul_assoc,
        ← dD.ofTorus_add]
  have hodd : ∀ i j l, ¬ Even ((τ.action.d8Act i j l Torus.c) 0) := fun i j l h =>
    hco ((hP i j l _).mp h)
  have hpar : ∀ (v : Torus τ.k) (i j l k : Bool),
      Even ((v + if k then τ.action.d8Act i j l Torus.c else 0) 0 + (if k then 1 else 0)) ↔
        Even (v 0) := by
    intro v i j l k
    cases k
    · simp
    · simp only [↓reduceIte, Pi.add_apply]
      rw [add_assoc, zmod_even_add_iff hk0, zmod_even_add_iff hk0]
      have := hodd i j l
      have h1 := zmod_not_even_one hk0 (m := τ.k 0)
      tauto
  constructor
  · rintro ⟨v, i, j, l, k, hv, rfl⟩
    exact ⟨_, i, j, l, k, (hpar v i j l k).mpr hv, hconv v i j l k⟩
  · rintro ⟨v, i, j, l, k, hv, rfl⟩
    refine ⟨v - (if k then τ.action.d8Act i j l Torus.c else 0), i, j, l, k, ?_, ?_⟩
    · rw [← hpar _ i j l k, sub_add_cancel]
      exact hv
    · rw [hconv, sub_add_cancel]

theorem e_not_mem (hφe : ∀ i j l, (∀ v, hE.φe v = τ.action.d8Act i j l v) → False) :
    e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  intro h
  obtain ⟨w, a, b, c, hw⟩ := dD.mem_sup_iff.mp h
  apply hφe (xor a (c && b)) b c
  intro v
  apply dD.ofTorus_inj
  rw [← hE.conj_ofTorus, hw]
  have h1 : (dD.d8 a b c)⁻¹ * dD.ofTorus v =
      dD.ofTorus (τ.action.d8Act (xor a (c && b)) b c v) * (dD.d8 a b c)⁻¹ := by
    rw [dD.d8_inv, dD.d8_mul_ofTorus]
  have h2 : (dD.ofTorus w)⁻¹ * dD.ofTorus v * dD.ofTorus w = dD.ofTorus v := by
    rw [← dD.ofTorus_neg, ← dD.ofTorus_add, ← dD.ofTorus_add, add_comm (-w) v, add_assoc,
      neg_add_cancel, add_zero]
  calc (dD.ofTorus w * dD.d8 a b c)⁻¹ * dD.ofTorus v * (dD.ofTorus w * dD.d8 a b c)
      = (dD.d8 a b c)⁻¹ * ((dD.ofTorus w)⁻¹ * dD.ofTorus v * dD.ofTorus w) * dD.d8 a b c := by
        group
    _ = (dD.d8 a b c)⁻¹ * dD.ofTorus v * dD.d8 a b c := by rw [h2]
    _ = dD.ofTorus (τ.action.d8Act (xor a (c && b)) b c v) * (dD.d8 a b c)⁻¹ * dD.d8 a b c := by
        rw [h1]
    _ = _ := by group

theorem nfe_inj
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    (hφe : ∀ i j l, (∀ v, hE.φe v = τ.action.d8Act i j l v) → False)
    {v v' : Torus τ.k} {i j l i' j' l' k k' : Bool}
    (h : dD.ofTorus v * dD.d8 i j l * bpow e k = dD.ofTorus v' * dD.d8 i' j' l' * bpow e k') :
    v = v' ∧ i = i' ∧ j = j' ∧ l = l' ∧ k = k' := by
  have hne : ∀ (v v' : Torus τ.k) (i j l i' j' l' : Bool),
      dD.ofTorus v * dD.d8 i j l * e ≠ dD.ofTorus v' * dD.d8 i' j' l' := by
    intro v v' i j l i' j' l' h'
    apply hE.e_not_mem hφe
    have : e = (dD.ofTorus v * dD.d8 i j l)⁻¹ * (dD.ofTorus v' * dD.d8 i' j' l') := by
      rw [← h']; group
    rw [this]
    exact mul_mem (inv_mem (dD.nf_mem v i j l)) (dD.nf_mem v' i' j' l')
  cases k <;> cases k'
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    obtain ⟨h1, h2, h3, h4⟩ := dD.nf_inj hF h
    exact ⟨h1, h2, h3, h4, rfl⟩
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    exact absurd h.symm (hne _ _ _ _ _ _ _ _)
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    exact absurd h (hne _ _ _ _ _ _ _ _)
  · simp only [bpow, ↓reduceIte] at h
    obtain ⟨h1, h2, h3, h4⟩ := dD.nf_inj hF (mul_right_cancel h)
    exact ⟨h1, h2, h3, h4, rfl⟩

theorem relIndex_S (hφe : ∀ i j l, (∀ v, hE.φe v = τ.action.d8Act i j l v) → False) :
    (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨e, Subgroup.mem_sup_right (Subgroup.mem_zpowers e), fun y hy => ?_⟩
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  have hS := dD.nf_mem v i j l
  have hnot := hE.e_not_mem hφe
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
    refine Or.inr ⟨hS, fun h => hnot ?_⟩
    have := mul_mem (inv_mem hS) h
    rwa [inv_mul_cancel_left] at this
  · simp only [bpow, ↓reduceIte]
    refine Or.inl ⟨?_, fun h => hnot ?_⟩
    · rw [mul_assoc, hE.mul_self, mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]
      exact dD.nf_mem _ i j l
    · have := mul_mem (inv_mem hS) h
      rwa [inv_mul_cancel_left] at this

theorem nfe_mul_c (v : Torus τ.k) (i j l k : Bool) :
    dD.ofTorus v * dD.d8 i j l * bpow e k * (dD.c : G) =
      dD.ofTorus (v + τ.action.d8Act i j l (if k then hE.φe Torus.c else Torus.c)) *
        dD.d8 i j l * bpow e k := by
  rw [c_eq]
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]
  · simp only [bpow, ↓reduceIte]
    rw [mul_assoc _ e, hE.e_mul_ofTorus, ← mul_assoc, mul_assoc (dD.ofTorus v),
      dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]

theorem odd_d8Act_c (hk0 : 1 ≤ τ.k 0)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (i j l k : Bool) :
    ¬ Even ((τ.action.d8Act i j l (if k then hE.φe Torus.c else Torus.c)) 0) := by
  have hc : ¬ Even ((Torus.c : Torus τ.k) 0) := by
    rw [show ((Torus.c : Torus τ.k) 0) = 1 by simp [gen]]
    exact zmod_not_even_one hk0
  rw [hP]
  cases k
  · exact hc
  · simp only [↓reduceIte]; rw [hPe]; exact hc

theorem relIndex_S₁e (hk0 : 1 ≤ τ.k 0)
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    (hφe : ∀ i j l, (∀ v, hE.φe v = τ.action.d8Act i j l v) → False)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (hve : Even (hE.ve 0)) :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 := by
  have hS₁ := fun y => hE.mem_S₁e_iff (y := y) hk0 hP hPe hwuv hwt hve
  have hnot : ∀ (v : Torus τ.k) (i j l k : Bool), ¬ Even (v 0) →
      dD.ofTorus v * dD.d8 i j l * bpow e k ∉
        Subgroup.closure ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} :
          Set G) := by
    intro v i j l k hv h
    obtain ⟨v', i', j', l', k', hv', he'⟩ := (hS₁ _).mp h
    obtain ⟨rfl, -⟩ := hE.nfe_inj hF hφe he'
    exact hv hv'
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨dD.c, Subgroup.mem_sup_left (Subgroup.mem_sup_left dD.c.2), fun y hy => ?_⟩
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  rw [hE.nfe_mul_c]
  have hodd := hE.odd_d8Act_c hk0 hP hPe i j l k
  by_cases hv : Even (v 0)
  · have h2 : ¬ Even ((v + τ.action.d8Act i j l (if k then hE.φe Torus.c else Torus.c)) 0) := by
      rw [Pi.add_apply, zmod_even_add_iff hk0]
      tauto
    exact Or.inr ⟨(hS₁ _).mpr ⟨v, i, j, l, k, hv, rfl⟩, hnot _ i j l k h2⟩
  · have h2 : Even ((v + τ.action.d8Act i j l (if k then hE.φe Torus.c else Torus.c)) 0) := by
      rw [Pi.add_apply, zmod_even_add_iff hk0]
      tauto
    exact Or.inl ⟨(hS₁ _).mpr ⟨_, i, j, l, k, h2, rfl⟩, hnot v i j l k hv⟩

theorem c_not_mem_S₁e (hk0 : 1 ≤ τ.k 0)
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    (hφe : ∀ i j l, (∀ v, hE.φe v = τ.action.d8Act i j l v) → False)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (hve : Even (hE.ve 0)) :
    (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} := by
  intro h
  obtain ⟨v, i, j, l, k, hv, he'⟩ := (hE.mem_S₁e_iff hk0 hP hPe hwuv hwt hve).mp h
  have h1 : (dD.c : G) = dD.ofTorus Torus.c * dD.d8 false false false * bpow e false := by
    simp [d8, bpow, c_eq]
  rw [h1] at he'
  obtain ⟨rfl, -⟩ := hE.nfe_inj hF hφe he'
  exact (show ¬ Even ((Torus.c : Torus τ.k) 0) by
    rw [show ((Torus.c : Torus τ.k) 0) = 1 by simp [gen]]; exact zmod_not_even_one hk0) hv

theorem relIndex_S₂ (hk0 : 1 ≤ τ.k 0)
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    (hφe : ∀ i j l, (∀ v, hE.φe v = τ.action.d8Act i j l v) → False)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (hve : Even (hE.ve 0)) (hcu : τ.action.φu Torus.c = Torus.c) :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      (dD.c : G) * e}).relIndex
        (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 := by
  have hS₂ := fun y => hE.mem_S₂_iff (y := y) hk0 hP hPe hwuv hwt hve hcu
  have hnot : ∀ (v : Torus τ.k) (i j l k : Bool), ¬ Even (v 0 + (if k then 1 else 0)) →
      dD.ofTorus v * dD.d8 i j l * bpow e k ∉
        Subgroup.closure ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
          (dD.c : G) * e} : Set G) := by
    intro v i j l k hv h
    obtain ⟨v', i', j', l', k', hv', he'⟩ := (hS₂ _).mp h
    obtain ⟨rfl, -, -, -, rfl⟩ := hE.nfe_inj hF hφe he'
    exact hv hv'
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨dD.c, Subgroup.mem_sup_left (Subgroup.mem_sup_left dD.c.2), fun y hy => ?_⟩
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  rw [hE.nfe_mul_c]
  have hodd := hE.odd_d8Act_c hk0 hP hPe i j l k
  by_cases hv : Even (v 0 + (if k then 1 else 0))
  · have h2 : ¬ Even ((v + τ.action.d8Act i j l (if k then hE.φe Torus.c else Torus.c)) 0 +
        (if k then 1 else 0)) := by
      rw [Pi.add_apply, add_right_comm, zmod_even_add_iff hk0]
      tauto
    exact Or.inr ⟨(hS₂ _).mpr ⟨v, i, j, l, k, hv, rfl⟩, hnot _ i j l k h2⟩
  · have h2 : Even ((v + τ.action.d8Act i j l (if k then hE.φe Torus.c else Torus.c)) 0 +
        (if k then 1 else 0)) := by
      rw [Pi.add_apply, add_right_comm, zmod_even_add_iff hk0]
      tauto
    exact Or.inl ⟨(hS₂ _).mpr ⟨_, i, j, l, k, h2, rfl⟩, hnot v i j l k hv⟩

theorem nf_not_mem_S₂ (hk0 : 1 ≤ τ.k 0)
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    (hφe : ∀ i j l, (∀ v, hE.φe v = τ.action.d8Act i j l v) → False)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (hve : Even (hE.ve 0)) (hcu : τ.action.φu Torus.c = Torus.c)
    {v : Torus τ.k} (hv : ¬ Even (v 0)) (i j l : Bool) :
    dD.ofTorus v * dD.d8 i j l ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
        (dD.c : G) * e} := by
  intro h
  obtain ⟨v', i', j', l', k', hv', he'⟩ := (hE.mem_S₂_iff hk0 hP hPe hwuv hwt hve hcu).mp h
  have h1 : dD.ofTorus v * dD.d8 i j l = dD.ofTorus v * dD.d8 i j l * bpow e false := by
    simp [bpow]
  rw [h1] at he'
  obtain ⟨rfl, -, -, -, rfl⟩ := hE.nfe_inj hF hφe he'
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hv'
  exact hv hv'

@[expose] def sqE (v : Torus τ.k) (i j l : Bool) : Torus τ.k :=
  v + τ.action.d8Act i j l (hE.φe (hE.ve + v - τ.action.d8Act i j l hE.ve) + hE.twist i j) +
    τ.action.d8Act (l && j) false false hE.ve

theorem nfe_e_mul_self (v : Torus τ.k) (i j l : Bool) :
    dD.ofTorus v * dD.d8 i j l * e * (dD.ofTorus v * dD.d8 i j l * e) =
      dD.ofTorus (hE.sqE v i j l) * dD.d8 (l && j) false false := by
  have h1 : dD.ofTorus v * dD.d8 i j l * e * (dD.ofTorus v * dD.d8 i j l * e) =
      dD.ofTorus v * dD.d8 i j l * (e * (dD.ofTorus v * dD.d8 i j l) * e⁻¹) * (e * e) := by group
  rw [h1, hE.conj_inv_nf, nf_mul_nf, hE.mul_self, mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc,
    ← dD.ofTorus_add]
  have hb : xor i (xor i (l && j)) = (l && j) := by cases i <;> simp
  rw [hb, Bool.xor_self, Bool.xor_self]
  rfl

include hE in
theorem mul_self_mem_or :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * y ∈ D ∨ y * y * dD.uv ∈ D := by
  intro y hy
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
    exact dD.mul_self_mem_or _ (dD.nf_mem v i j l)
  · simp only [bpow, ↓reduceIte]
    rw [hE.nfe_e_mul_self]
    cases l && j
    · left
      rw [d8_fff, mul_one]
      exact dD.ofTorus_mem _
    · right
      rw [d8_tff, mul_assoc, dD.uv_sq, mul_one]
      exact dD.ofTorus_mem _

theorem even_sqE_iff (hk0 : 1 ≤ τ.k 0)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0))
    (hPe : ∀ v, Even ((hE.φe v) 0) ↔ Even (v 0)) (hwuv : Even (hE.wuv 0))
    (hwt : Even (hE.wt 0)) (v : Torus τ.k) (i j l : Bool) :
    Even ((hE.sqE v i j l) 0) ↔ Even (hE.ve 0) := by
  have htw : Even ((hE.twist i j) 0) := by
    simp only [twist, Pi.add_apply]
    refine (zmod_even_add_iff hk0 _ _).mpr ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [hP]
      cases j
      · exact ⟨0, by simp⟩
      · exact hwt
    · cases i
      · exact ⟨0, by simp⟩
      · exact hwuv
  simp only [sqE, Pi.add_apply]
  rw [zmod_even_add_iff hk0, zmod_even_add_iff hk0, hP, hP, Pi.add_apply,
    zmod_even_add_iff hk0, hPe, Pi.sub_apply, Pi.add_apply, sub_eq_add_neg,
    zmod_even_add_iff hk0, zmod_even_add_iff hk0]
  have hn : ∀ x : ZMod (2 ^ τ.k 0), Even (-x) ↔ Even x := fun x =>
    ⟨fun h => by simpa using h.neg, fun h => h.neg⟩
  rw [hn, hP]
  tauto

end EAction

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

@[expose] def t100EAction (φe : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (ve : Torus (StrothTypeIndex.t100 m).k)
    (hφe : ∀ v, e⁻¹ * dD.ofTorus v * e = dD.ofTorus (φe v))
    (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (he : e * e = dD.ofTorus ve) : dD.EAction e where
  φe := φe
  wuv := Torus.ofInt _ ![2, 1, 1]
  wt := Torus.ofInt _ ![0, -1, 0]
  ve := ve
  conj_ofTorus := hφe
  conj_uv := by
    rw [heuv, ofTorus_ofInt]
    simp
  conj_t := by
    rw [het, ofTorus_ofInt]
    simp
  conj_u := hue
  mul_self := he

section Twist

variable {dD} (hE : dD.EAction e) (hwuv : hE.wuv = Torus.ofInt _ ![2, 1, 1])
  (hwt : hE.wt = Torus.ofInt _ ![0, -1, 0])

include hwuv hwt

theorem twist_ff : hE.twist false false = 0 := by
  simp [EAction.twist, SigmaFourAction.d8Act]

theorem twist_ft : hE.twist false true = Torus.ofInt _ ![0, -1, 0] := by
  simp [EAction.twist, SigmaFourAction.d8Act, hwt]

theorem twist_tf : hE.twist true false = Torus.ofInt _ ![2, 1, 1] := by
  simp [EAction.twist, SigmaFourAction.d8Act, hwuv]

theorem twist_tt : hE.twist true true = Torus.ofInt _ ![0, 0, -1] := by
  simp only [EAction.twist, ↓reduceIte, SigmaFourAction.d8Act, Bool.false_eq_true,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, hwuv, hwt, Stroth42Core.t100_φuv,
    ← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> simp

end Twist

@[expose] def iiAction (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = dD.c)
    (hae : e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m)
    (hbe : e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m)
    (he : e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) : dD.EAction e :=
  dD.t100EAction (torusDiag _ ![1, 1 + 2 ^ m, 1 + 2 ^ m]) (Torus.ofInt _ ![-1 + 2 ^ (m - 1), 0, 0])
    (dD.conj_ofTorus_of_gens
      (by rw [hce, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
      (by
        rw [hae, torusDiag_gen, ofTorus_zsmul, ← a_eq,
          show (![1, 1 + 2 ^ m, 1 + 2 ^ m] : Fin 3 → ℤ) 1 = 1 + 2 ^ m from rfl,
          zpow_add, zpow_one, show ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast])
      (by
        rw [hbe, torusDiag_gen, ofTorus_zsmul, ← b_eq,
          show (![1, 1 + 2 ^ m, 1 + 2 ^ m] : Fin 3 → ℤ) 2 = 1 + 2 ^ m from rfl,
          zpow_add, zpow_one, show ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast]))
    heuv het hue
    (by
      rw [he, ofTorus_ofInt]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, zpow_zero, mul_one]
      rw [zpow_add, zpow_neg_one, show ((2 : ℤ) ^ (m - 1)) = ((2 ^ (m - 1) : ℕ) : ℤ) by
        push_cast; rfl, zpow_natCast])

@[expose] def iiiAction (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) : dD.EAction e :=
  dD.t100EAction (torusDiag _ ![-1, -1, -1]) 0
    (dD.conj_ofTorus_of_gens
      (by rw [hce, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
      (by rw [hae, torusDiag_gen, ofTorus_zsmul, ← a_eq]; simp)
      (by rw [hbe, torusDiag_gen, ofTorus_zsmul, ← b_eq]; simp))
    heuv het hue (by rw [he, ofTorus_zero])

@[expose] def ivAction (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m)
    (he : e * e = (dD.c : G) ^ 2 ^ (m - 1)) : dD.EAction e :=
  dD.t100EAction (torusDiag _ ![-1, -1 + 2 ^ m, -1 + 2 ^ m]) (Torus.ofInt _ ![2 ^ (m - 1), 0, 0])
    (dD.conj_ofTorus_of_gens
      (by rw [hce, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
      (by
        rw [hae, torusDiag_gen, ofTorus_zsmul, ← a_eq,
          show (![-1, -1 + 2 ^ m, -1 + 2 ^ m] : Fin 3 → ℤ) 1 = -1 + 2 ^ m from rfl,
          zpow_add, zpow_neg_one, show ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast])
      (by
        rw [hbe, torusDiag_gen, ofTorus_zsmul, ← b_eq,
          show (![-1, -1 + 2 ^ m, -1 + 2 ^ m] : Fin 3 → ℤ) 2 = -1 + 2 ^ m from rfl,
          zpow_add, zpow_neg_one, show ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast]))
    heuv het hue
    (by
      rw [he, ofTorus_ofInt]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, zpow_zero, mul_one]
      rw [show ((2 : ℤ) ^ (m - 1)) = ((2 ^ (m - 1) : ℕ) : ℤ) by push_cast; rfl, zpow_natCast])

theorem t100_faithful_om (hm : 1 ≤ m) (i j l : Bool)
    (hc : (StrothTypeIndex.t100 m).action.d8Act i j l (Stroth42Core.om100 m ![1, 0, 0]) =
      Stroth42Core.om100 m ![1, 0, 0])
    (ha : (StrothTypeIndex.t100 m).action.d8Act i j l (Stroth42Core.om100 m ![0, 1, 0]) =
      Stroth42Core.om100 m ![0, 1, 0]) :
    i = false ∧ j = false ∧ l = false := by
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Stroth42Core.t100_φuv_om hm,
      Stroth42Core.t100_φt_om hm, Stroth42Core.t100_φu_om, Stroth42Core.om100_eq_iff hm] at hc ha <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | exact absurd hc (by decide)
    | exact absurd ha (by decide)

theorem t100_not_word (hm : 1 ≤ m) (φ : Torus (StrothTypeIndex.t100 m).k →+
      Torus (StrothTypeIndex.t100 m).k)
    (hc : φ (Stroth42Core.om100 m ![1, 0, 0]) = Stroth42Core.om100 m ![1, 0, 0])
    (ha : φ (Stroth42Core.om100 m ![0, 1, 0]) = Stroth42Core.om100 m ![0, 1, 0])
    {w : Torus (StrothTypeIndex.t100 m).k} (hw : φ w ≠ w) (i j l : Bool)
    (h : ∀ v, φ v = (StrothTypeIndex.t100 m).action.d8Act i j l v) : False := by
  obtain ⟨rfl, rfl, rfl⟩ := t100_faithful_om hm i j l (by rw [← h, hc]) (by rw [← h, ha])
  apply hw
  rw [h]
  simp [SigmaFourAction.d8Act]

theorem torusDiag_om100 (hm : 1 ≤ m) (d : Fin 3 → ℤ) (hd : ∀ i, d i % 2 = 1) (ε : Fin 3 → ℤ) :
    torusDiag _ d (Stroth42Core.om100 m ε) = Stroth42Core.om100 m ε := by
  rw [Stroth42Core.om100, torusDiag_ofInt]
  rw [show (fun i => d i * (ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1))) =
    fun i => (d i * ε i) * 2 ^ ((StrothTypeIndex.t100 m).k i - 1) by funext i; ring]
  exact (Stroth42Core.om100_eq_iff hm _ _).mpr fun i => by
    have := hd i
    simp only [Int.ModEq, Int.mul_emod, this, one_mul, Int.emod_emod_of_dvd, Int.emod_emod]

theorem even_torusDiag_iff (hm : 1 ≤ m) (d : Fin 3 → ℤ) (hd : d 0 % 2 = 1)
    (v : Torus (StrothTypeIndex.t100 m).k) :
    Even ((torusDiag _ d v) 0) ↔ Even (v 0) := by
  have hk : 1 ≤ (StrothTypeIndex.t100 m).k 0 := hm
  refine Stroth42Core.even_matAct_zero_iff hk _ _ ?_ ?_ ?_ v
  · rw [Matrix.diagonal_apply_eq, Int.odd_iff]; exact hd
  · rw [Matrix.diagonal_apply_ne _ (by decide)]; exact ⟨0, rfl⟩
  · rw [Matrix.diagonal_apply_ne _ (by decide)]; exact ⟨0, rfl⟩

theorem EAction.t100_comm_c₁ (hE : dD.EAction e) (hm : 1 ≤ m)
    (hφ : hE.φe (Stroth42Core.om100 m ![1, 0, 0]) = Stroth42Core.om100 m ![1, 0, 0])
    {v : Torus (StrothTypeIndex.t100 m).k} {i j l k : Bool}
    (h : dD.ofTorus v * dD.d8 i j l * Stroth42Core.bpow e k * (dD.c : G) ^ 2 ^ (m - 1) =
      (dD.c : G) ^ 2 ^ (m - 1) * (dD.ofTorus v * dD.d8 i j l * Stroth42Core.bpow e k)) :
    i = false ∧ j = false := by
  rw [dD.t100_c_pow] at h
  have hb : Stroth42Core.bpow e k * dD.ofTorus (Stroth42Core.om100 m ![1, 0, 0]) =
      dD.ofTorus (Stroth42Core.om100 m ![1, 0, 0]) * Stroth42Core.bpow e k := by
    cases k
    · simp [Stroth42Core.bpow]
    · simp only [Stroth42Core.bpow, ↓reduceIte]
      rw [hE.e_mul_ofTorus, hφ]
  rw [mul_assoc _ (Stroth42Core.bpow e k), hb, ← mul_assoc, ← mul_assoc] at h
  have h' := mul_right_cancel h
  rw [← dD.t100_c_pow] at h'
  exact dD.t100_comm_z hm h'

theorem torusDiag_om100_of_odd (hm : 1 ≤ m) {d : Fin 3 → ℤ} (h0 : d 0 % 2 = 1)
    (h1 : d 1 % 2 = 1) (h2 : d 2 % 2 = 1) (ε : Fin 3 → ℤ) :
    torusDiag _ d (Stroth42Core.om100 m ε) = Stroth42Core.om100 m ε :=
  torusDiag_om100 hm d (fun i => by fin_cases i <;> assumption) ε

theorem one_add_two_pow_emod_two (hm : 1 ≤ m) : (1 + 2 ^ m : ℤ) % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]; omega

theorem neg_one_add_two_pow_emod_two (hm : 1 ≤ m) : (-1 + 2 ^ m : ℤ) % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]; omega

theorem t100_pow_ne_c₁_of_sq_uv (hm : 1 ≤ m) {y : G} {W : Torus (StrothTypeIndex.t100 m).k}
    (h : y * y = dD.ofTorus W * dD.d8 true false false) {n : ℕ} (hn : 1 ≤ n) :
    y ^ 2 ^ n ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro hz
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [pow_one, sq, h] at hz
    have hnot := dD.d8_not_mem (Stroth42Core.t100_faithful hm) (i := true) (j := false)
      (l := false) (by decide) W
    rw [hz] at hnot
    exact hnot (pow_mem dD.c.2 _)
  · obtain ⟨w, rfl⟩ := Torus.exists_ofInt W
    have h4 : y * y * (y * y) = dD.ofTorus (Torus.ofInt (StrothTypeIndex.t100 m).k
        ![-2 * w 0 + 2 * w 1 + 2 * w 2, -2 * w 0 + 2 * w 1 + 2 * w 2,
          -2 * w 0 + 2 * w 1 + 2 * w 2]) := by
      rw [h, dD.nf_mul_self_of_false _ (by rfl)]
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, Stroth42Core.t100_φuv, ← Torus.ofInt_add]
      congr 2
      funext i
      fin_cases i <;> simp <;> ring
    rw [Stroth42Core.pow_two_pow_eq_mul_self _ hn] at hz
    exact dD.t100_pow_ne_c₁ hm h4 (Or.inl rfl) (by omega : 1 ≤ n - 1) hz

theorem t100_pow_ne_c₁_of_two_mul (hm : 1 ≤ m) {y : G} {w : Fin 3 → ℤ}
    (hsq : y * y = dD.ofTorus (Torus.ofInt _ w)) (hw : w 0 = 2 * w 1) {n : ℕ} (hn : 1 ≤ n) :
    y ^ 2 ^ n ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro h
  rw [dD.pow_two_pow_of_mul_self hsq hn, dD.t100_c_pow, om100_c, ← natCast_zsmul,
    ← Torus.ofInt_zsmul] at h
  obtain ⟨h0, h1, -⟩ := (Stroth42Core.t100_ofInt_eq_iff _ _).mp (dD.ofTorus_inj h)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h0 h1
  rw [hw] at h0
  refine Stroth42Core.not_dvd_pow_pred_sub hm h0 ?_
  have h2 : (2 : ℤ) ^ (m + 1) ∣ 2 * (0 - ((2 ^ (n - 1) : ℕ) : ℤ) * w 1) :=
    dvd_mul_of_dvd_right h1 2
  have : (2 : ℤ) * (0 - ((2 ^ (n - 1) : ℕ) : ℤ) * w 1) =
      0 - ((2 ^ (n - 1) : ℕ) : ℤ) * (2 * w 1) := by ring
  rwa [this] at h2

theorem t100_φu_zero (v : Torus (StrothTypeIndex.t100 m).k) :
    ((StrothTypeIndex.t100 m).action.φu v) 0 = v 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [Stroth42Core.t100_φu]
  rfl

theorem t100_cover_CSz (hm : 1 ≤ m) {X : Subgroup G}
    (hX : ∀ y ∈ X, y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (hab : IsMulCommutative X) {x₁ : G} (hx₁ : x₁ ∈ X)
    (hx₁S : x₁ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) (hx₁D : x₁ ∉ D) :
    ∀ y ∈ X, y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      ∃ w : Bool × ZMod (2 ^ m) × ZMod (2 ^ (m + 1)),
        dD.ofTorus (Torus.ofInt _ ![(w.2.1.val : ℤ), (w.2.2.val : ℤ), (w.2.2.val : ℤ)]) *
          (if w.1 then x₁ else 1) = y := by
  obtain ⟨v₀, hv₀⟩ := dD.t100_mem_CSz_of_not_mem hm (hX x₁ hx₁ hx₁S) hx₁D
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
  have hfix : ∀ d ∈ X, d ∈ D → ∃ (p : ZMod (2 ^ m)) (q : ZMod (2 ^ (m + 1))),
      d = dD.ofTorus (Torus.ofInt _ ![(p.val : ℤ), (q.val : ℤ), (q.val : ℤ)]) := by
    intro d hd hdD
    obtain ⟨v, rfl⟩ := dD.exists_ofTorus hdD
    have hc := hcomm _ hd _ hx₁
    rw [hv₀] at hc
    have hfv := (dD.nf_commute_iff v₀ v false false true).mp hc.symm
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] at hfv
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    rw [Stroth42Core.t100_φu, Stroth42Core.t100_ofInt_eq_iff] at hfv
    obtain ⟨-, h1, -⟩ := hfv
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    refine ⟨((x 0 : ℤ) : ZMod (2 ^ m)), ((x 1 : ℤ) : ZMod (2 ^ (m + 1))), ?_⟩
    congr 1
    rw [Stroth42Core.t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast]
    have hm' : ((2 ^ m : ℕ) : ℤ) = 2 ^ m := by push_cast; rfl
    have hm'' : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 ^ (m + 1) := by push_cast; rfl
    rw [hm', hm'']
    refine ⟨⟨-(x 0 / 2 ^ m), by rw [Int.emod_def]; ring⟩, ⟨-(x 1 / 2 ^ (m + 1)), by
      rw [Int.emod_def]; ring⟩, ?_⟩
    obtain ⟨c, hc⟩ := h1
    exact ⟨c - x 1 / 2 ^ (m + 1), by rw [Int.emod_def]; linear_combination hc⟩
  intro y hy hyS
  by_cases hyD : y ∈ D
  · obtain ⟨p, q, hd⟩ := hfix y hy hyD
    exact ⟨(false, p, q), by simp [hd]⟩
  · obtain ⟨v, hv⟩ := dD.t100_mem_CSz_of_not_mem hm (hX y hy hyS) hyD
    have hmem : y * x₁⁻¹ ∈ D := by
      rw [hv, hv₀]
      exact dD.nf_u_mul_inv_mem v₀ v
    obtain ⟨p, q, hd⟩ := hfix (y * x₁⁻¹) (mul_mem hy (inv_mem hx₁)) hmem
    refine ⟨(true, p, q), ?_⟩
    simp only [if_true]
    rw [← hd, inv_mul_cancel_right]

theorem EAction.t100_h9_of (hE : dD.EAction e) (hm : 2 ≤ m)
    (hφ : hE.φe (Stroth42Core.om100 m ![1, 0, 0]) = Stroth42Core.om100 m ![1, 0, 0])
    (hnot : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    {P₀ P₁ : Type} [Finite P₀] [Finite P₁]
    (g₀ : P₀ → Torus (StrothTypeIndex.t100 m).k) (g₁ : P₁ → Torus (StrothTypeIndex.t100 m).k)
    (hg₀ : ∀ w, hE.φe w = w → ∃ p, g₀ p = w)
    (hg₁ : ∀ w, (StrothTypeIndex.t100 m).action.φu (hE.φe w) = w → ∃ p, g₁ p = w)
    (hP₀ : 2 * Nat.card P₀ < 2 ^ (m + (m + 1) + (m + 1)))
    (hP₁ : 2 * Nat.card P₁ < 2 ^ (m + (m + 1) + (m + 1))) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D := by
  intro X hX hab hcard
  have hm1 : 1 ≤ m := by omega
  have hDcard : Nat.card D = 2 ^ (m + (m + 1) + (m + 1)) := dD.card
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hXS : ∀ y ∈ X, y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} :=
    fun y hy hyS => Subgroup.mem_inf.mpr ⟨hyS, (Subgroup.mem_inf.mp (hX hy)).2⟩
  have hnfX : ∀ y ∈ X, ∃ (v : Torus (StrothTypeIndex.t100 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * Stroth42Core.bpow e k := by
    intro y hy
    obtain ⟨hyS', hyC⟩ := Subgroup.mem_inf.mp (hX hy)
    obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS'
    rw [Subgroup.mem_centralizer_iff] at hyC
    obtain ⟨rfl, rfl⟩ := EAction.t100_comm_c₁ dD hE hm1 hφ (hyC _ (Set.mem_singleton _)).symm
    exact ⟨v, l, k, rfl⟩
  have hk1 : ∀ (v : Torus (StrothTypeIndex.t100 m).k) (l : Bool),
      dD.ofTorus v * dD.d8 false false l * Stroth42Core.bpow e true ∉
        D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
    intro v l h
    apply hnot
    have : e = (dD.ofTorus v * dD.d8 false false l)⁻¹ *
        (dD.ofTorus v * dD.d8 false false l * Stroth42Core.bpow e true) := by
      simp only [Stroth42Core.bpow, ↓reduceIte]; group
    rw [this]
    exact mul_mem (inv_mem (dD.nf_mem v false false l)) h
  by_cases hD : ∃ x ∈ X, x ∉ D
  · exfalso
    by_cases hA : ∃ x₁ ∈ X, x₁ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ∧ x₁ ∉ D
    ·
      obtain ⟨x₁, hx₁, hx₁S, hx₁D⟩ := hA
      have hcov₁ := dD.t100_cover_CSz hm1 hXS hab hx₁ hx₁S hx₁D
      haveI : NeZero (2 ^ m) := ⟨by positivity⟩
      haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
      by_cases hB : ∃ x₀ ∈ X, x₀ ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}
      · obtain ⟨x₀, hx₀, hx₀S⟩ := hB
        let f : Bool × (Bool × ZMod (2 ^ m) × ZMod (2 ^ (m + 1))) → G := fun w =>
          dD.ofTorus (Torus.ofInt _ ![(w.2.2.1.val : ℤ), (w.2.2.2.val : ℤ),
            (w.2.2.2.val : ℤ)]) * (if w.2.1 then x₁ else 1) * (if w.1 then x₀ else 1)
        have hcov : ∀ y ∈ X, ∃ w, f w = y := by
          intro y hy
          by_cases hyS : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}
          · obtain ⟨w, hw⟩ := hcov₁ y hy hyS
            exact ⟨(false, w), by simp only [f, Bool.false_eq_true, ↓reduceIte, mul_one]; exact hw⟩
          ·
            have hyx : y * x₀⁻¹ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
              obtain ⟨v, l, k, rfl⟩ := hnfX y hy
              obtain ⟨v', l', k', rfl⟩ := hnfX x₀ hx₀
              cases k
              · exact absurd (by simpa [Stroth42Core.bpow] using dD.nf_mem v false false l) hyS
              cases k'
              · exact absurd (by simpa [Stroth42Core.bpow] using dD.nf_mem v' false false l')
                  hx₀S
              simp only [Stroth42Core.bpow, ↓reduceIte]
              have : dD.ofTorus v * dD.d8 false false l * e *
                  (dD.ofTorus v' * dD.d8 false false l' * e)⁻¹ =
                  dD.ofTorus v * dD.d8 false false l * (dD.ofTorus v' * dD.d8 false false l')⁻¹ :=
                by group
              rw [this]
              exact mul_mem (dD.nf_mem v false false l) (inv_mem (dD.nf_mem v' false false l'))
            obtain ⟨w, hw⟩ := hcov₁ (y * x₀⁻¹) (mul_mem hy (inv_mem hx₀)) hyx
            refine ⟨(true, w), ?_⟩
            simp only [f, if_true]
            rw [hw, inv_mul_cancel_right]
        have hle := Stroth42Core.natCard_le_of_subset_range f hcov
        rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_zmod,
          Nat.card_zmod] at hle
        have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
        rw [h2, show 2 * (2 * (2 ^ m * 2 ^ (m + 1))) = 2 ^ (m + m + 3) by ring] at hle
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
        omega
      · simp only [not_exists, not_and, not_not] at hB
        let f : Bool × ZMod (2 ^ m) × ZMod (2 ^ (m + 1)) → G := fun w =>
          dD.ofTorus (Torus.ofInt _ ![(w.2.1.val : ℤ), (w.2.2.val : ℤ), (w.2.2.val : ℤ)]) *
            (if w.1 then x₁ else 1)
        have hle := Stroth42Core.natCard_le_of_subset_range f (fun y hy => hcov₁ y hy (hB y hy))
        rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hle
        have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
        rw [h2, show 2 * (2 ^ m * 2 ^ (m + 1)) = 2 ^ (m + m + 2) by ring] at hle
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
        omega
    ·
      simp only [not_exists, not_and, not_not] at hA
      obtain ⟨x₀, hx₀, hx₀D⟩ := hD
      have hx₀S : x₀ ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := fun h => hx₀D (hA x₀ hx₀ h)
      obtain ⟨v₀, l₀, k₀, hv₀⟩ := hnfX x₀ hx₀
      cases k₀
      · exact hx₀S (by rw [hv₀]; simpa [Stroth42Core.bpow] using dD.nf_mem v₀ false false l₀)
      have hfix : ∀ d ∈ X, d ∈ D → ∃ w : Torus (StrothTypeIndex.t100 m).k,
          d = dD.ofTorus w ∧ (StrothTypeIndex.t100 m).action.d8Act false false l₀ (hE.φe w) = w := by
        intro d hd hdD
        obtain ⟨w, rfl⟩ := dD.exists_ofTorus hdD
        refine ⟨w, rfl, ?_⟩
        have hc := hcomm _ hd _ hx₀
        rw [hv₀] at hc
        simp only [Stroth42Core.bpow, ↓reduceIte] at hc
        have h1 : dD.ofTorus v₀ * dD.d8 false false l₀ * e * dD.ofTorus w =
            dD.ofTorus (v₀ + (StrothTypeIndex.t100 m).action.d8Act false false l₀ (hE.φe w)) *
              dD.d8 false false l₀ * e := by
          rw [mul_assoc _ e, hE.e_mul_ofTorus, ← mul_assoc, mul_assoc (dD.ofTorus v₀),
            dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]
        have h2 : dD.ofTorus w * (dD.ofTorus v₀ * dD.d8 false false l₀ * e) =
            dD.ofTorus (w + v₀) * dD.d8 false false l₀ * e := by
          rw [← mul_assoc, ← mul_assoc, ← dD.ofTorus_add]
        rw [h1, h2] at hc
        have hc' := dD.ofTorus_inj (mul_right_cancel (mul_right_cancel hc))
        rw [add_comm w v₀] at hc'
        exact (add_left_cancel hc').symm
      have hcovD : ∀ y ∈ X, y ∈ D ∨ (y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ∧
          y * x₀⁻¹ ∈ D) := by
        intro y hy
        by_cases hyS : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}
        · exact Or.inl (hA y hy hyS)
        · refine Or.inr ⟨hyS, hA _ (mul_mem hy (inv_mem hx₀)) ?_⟩
          obtain ⟨v, l, k, rfl⟩ := hnfX y hy
          cases k
          · exact absurd (by simpa [Stroth42Core.bpow] using dD.nf_mem v false false l) hyS
          rw [hv₀]
          simp only [Stroth42Core.bpow, ↓reduceIte]
          have : dD.ofTorus v * dD.d8 false false l * e *
              (dD.ofTorus v₀ * dD.d8 false false l₀ * e)⁻¹ =
              dD.ofTorus v * dD.d8 false false l * (dD.ofTorus v₀ * dD.d8 false false l₀)⁻¹ := by
            group
          rw [this]
          exact mul_mem (dD.nf_mem v false false l) (inv_mem (dD.nf_mem v₀ false false l₀))
      cases l₀
      ·
        let f : Bool × P₀ → G := fun w => dD.ofTorus (g₀ w.2) * (if w.1 then x₀ else 1)
        have hcov : ∀ y ∈ X, ∃ w, f w = y := by
          intro y hy
          rcases hcovD y hy with hyD | ⟨-, hyx⟩
          · obtain ⟨w, rfl, hw⟩ := hfix y hy hyD
            simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
              AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hw
            obtain ⟨p, hp⟩ := hg₀ w hw
            exact ⟨(false, p), by simp [f, hp]⟩
          · obtain ⟨w, hw', hw⟩ := hfix _ (mul_mem hy (inv_mem hx₀)) hyx
            simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
              AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hw
            obtain ⟨p, hp⟩ := hg₀ w hw
            refine ⟨(true, p), ?_⟩
            simp only [f, if_true, hp]
            rw [← hw', inv_mul_cancel_right]
        have hle := Stroth42Core.natCard_le_of_subset_range f hcov
        rw [hcard, hDcard, Nat.card_prod] at hle
        have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
        rw [h2] at hle
        omega
      ·
        let f : Bool × P₁ → G := fun w => dD.ofTorus (g₁ w.2) * (if w.1 then x₀ else 1)
        have hcov : ∀ y ∈ X, ∃ w, f w = y := by
          intro y hy
          rcases hcovD y hy with hyD | ⟨-, hyx⟩
          · obtain ⟨w, rfl, hw⟩ := hfix y hy hyD
            simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
              AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hw
            obtain ⟨p, hp⟩ := hg₁ w hw
            exact ⟨(false, p), by simp [f, hp]⟩
          · obtain ⟨w, hw', hw⟩ := hfix _ (mul_mem hy (inv_mem hx₀)) hyx
            simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
              AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hw
            obtain ⟨p, hp⟩ := hg₁ w hw
            refine ⟨(true, p), ?_⟩
            simp only [f, if_true, hp]
            rw [← hw', inv_mul_cancel_right]
        have hle := Stroth42Core.natCard_le_of_subset_range f hcov
        rw [hcard, hDcard, Nat.card_prod] at hle
        have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
        rw [h2] at hle
        omega
  · simp only [not_exists, not_and, not_not] at hD
    haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge (fun x hx => hD x hx) hcard.ge

section III

variable (hm : 1 ≤ m)
  (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
  (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
  (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
  (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)

theorem iiiAction_φe :
    (dD.iiiAction heuv het hue hce hae hbe he).φe = torusDiag _ ![-1, -1, -1] := rfl

theorem iiiAction_wuv :
    (dD.iiiAction heuv het hue hce hae hbe he).wuv = Torus.ofInt _ ![2, 1, 1] := rfl

theorem iiiAction_wt :
    (dD.iiiAction heuv het hue hce hae hbe he).wt = Torus.ofInt _ ![0, -1, 0] := rfl

theorem iiiAction_ve : (dD.iiiAction heuv het hue hce hae hbe he).ve = 0 := rfl

theorem iiiAction_φe_apply (v : Torus (StrothTypeIndex.t100 m).k) :
    (dD.iiiAction heuv het hue hce hae hbe he).φe v = -v := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [iiiAction_φe, torusDiag_ofInt, ← Torus.ofInt_neg]
  congr 1
  funext i
  fin_cases i <;> simp

include hm in
theorem iii_parity_e (v : Torus (StrothTypeIndex.t100 m).k) :
    Even (((dD.iiiAction heuv het hue hce hae hbe he).φe v) 0) ↔ Even (v 0) :=
  even_torusDiag_iff hm _ (by decide) v

theorem t100_φu_c : (StrothTypeIndex.t100 m).action.φu Torus.c = Torus.c := by
  have h := Type100.u_c m
  rw [one_smul] at h
  exact h

include hm heuv het hue hce hae hbe he in
theorem iii_mem_S₁e_iff {y : G} :
    y ∈ Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} : Set G) ↔
      ∃ (v : Torus (StrothTypeIndex.t100 m).k) (i j l k : Bool), Even (v 0) ∧
        y = dD.ofTorus v * dD.d8 i j l * Stroth42Core.bpow e k :=
  (dD.iiiAction heuv het hue hce hae hbe he).mem_S₁e_iff hm (Stroth42Core.t100_parity hm)
    (dD.iii_parity_e hm heuv het hue hce hae hbe he)
    ⟨1, by rw [iiiAction_wuv, Torus.ofInt_apply]; push_cast; norm_num⟩
    ⟨0, by rw [iiiAction_wt, Torus.ofInt_apply]; simp⟩ ⟨0, by rw [iiiAction_ve]; simp⟩

include hm heuv het hue hce hae hbe he in
theorem iii_mem_S₂_iff {y : G} :
    y ∈ Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, (dD.c : G) * e} : Set G) ↔
      ∃ (v : Torus (StrothTypeIndex.t100 m).k) (i j l k : Bool),
        Even (v 0 + (if k then 1 else 0)) ∧
        y = dD.ofTorus v * dD.d8 i j l * Stroth42Core.bpow e k :=
  (dD.iiiAction heuv het hue hce hae hbe he).mem_S₂_iff hm (Stroth42Core.t100_parity hm)
    (dD.iii_parity_e hm heuv het hue hce hae hbe he)
    ⟨1, by rw [iiiAction_wuv, Torus.ofInt_apply]; push_cast; norm_num⟩
    ⟨0, by rw [iiiAction_wt, Torus.ofInt_apply]; simp⟩ ⟨0, by rw [iiiAction_ve]; simp⟩
    (t100_φu_c (m := m))

end III

theorem iii_not_word (hm : 2 ≤ m) (i j l : Bool)
    (h : ∀ v, torusDiag (StrothTypeIndex.t100 m).k ![-1, -1, -1] v =
      (StrothTypeIndex.t100 m).action.d8Act i j l v) : False := by
  refine t100_not_word (by omega) _ (torusDiag_om100 (by omega) _ (by decide) _)
    (torusDiag_om100 (by omega) _ (by decide) _) (w := Torus.c) ?_ i j l h
  rw [torusDiag_gen]
  intro hc
  have hc' : Torus.ofInt (StrothTypeIndex.t100 m).k ![-1, 0, 0] = Torus.ofInt _ ![1, 0, 0] := by
    rw [show Torus.ofInt (StrothTypeIndex.t100 m).k ![-1, 0, 0] = (-1 : ℤ) • Torus.c by
      rw [Torus.ofInt_eq_zsmul_gens]; simp,
      show Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] = Torus.c by
      rw [Torus.ofInt_eq_zsmul_gens]; simp]
    simpa using hc
  obtain ⟨h0, -, -⟩ := (Stroth42Core.t100_ofInt_eq_iff _ _).mp hc'
  have h2 : (2 : ℤ) ^ m ∣ 2 := by simpa using h0
  have h4 : (4 : ℤ) ≤ 2 ^ m := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have := Int.le_of_dvd (by norm_num) h2
  omega

section IIIh

variable (hm : 2 ≤ m)
  (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
  (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
  (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
  (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)

include hm heuv het hue hce hae hbe he

theorem iii_h1 :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      e}).relIndex (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 :=
  (dD.iiiAction heuv het hue hce hae hbe he).relIndex_S₁e (by show 1 ≤ m; omega)
    (Stroth42Core.t100_faithful (by omega)) (iii_not_word hm)
    (Stroth42Core.t100_parity (by omega)) (dD.iii_parity_e (by omega) heuv het hue hce hae hbe he)
    ⟨1, by rw [iiiAction_wuv, Torus.ofInt_apply]; push_cast; norm_num⟩
    ⟨0, by rw [iiiAction_wt, Torus.ofInt_apply]; simp⟩ ⟨0, by rw [iiiAction_ve]; simp⟩

theorem iii_h2 :
    (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} :=
  (dD.iiiAction heuv het hue hce hae hbe he).c_not_mem_S₁e (by show 1 ≤ m; omega)
    (Stroth42Core.t100_faithful (by omega)) (iii_not_word hm)
    (Stroth42Core.t100_parity (by omega)) (dD.iii_parity_e (by omega) heuv het hue hce hae hbe he)
    ⟨1, by rw [iiiAction_wuv, Torus.ofInt_apply]; push_cast; norm_num⟩
    ⟨0, by rw [iiiAction_wt, Torus.ofInt_apply]; simp⟩ ⟨0, by rw [iiiAction_ve]; simp⟩

theorem iii_h1' :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      (dD.c : G) * e}).relIndex
        (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 :=
  (dD.iiiAction heuv het hue hce hae hbe he).relIndex_S₂ (by show 1 ≤ m; omega)
    (Stroth42Core.t100_faithful (by omega)) (iii_not_word hm)
    (Stroth42Core.t100_parity (by omega)) (dD.iii_parity_e (by omega) heuv het hue hce hae hbe he)
    ⟨1, by rw [iiiAction_wuv, Torus.ofInt_apply]; push_cast; norm_num⟩
    ⟨0, by rw [iiiAction_wt, Torus.ofInt_apply]; simp⟩ ⟨0, by rw [iiiAction_ve]; simp⟩
    (t100_φu_c (m := m))

theorem iii_h2' :
    (dD.c : G) * dD.a * dD.uv ∉ Subgroup.closure
      {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, (dD.c : G) * e} := by
  have h : (dD.c : G) * dD.a * dD.uv =
      dD.ofTorus (Torus.c + Torus.a) * dD.d8 true false false := by
    rw [d8_tff, ofTorus_add, ← c_eq, ← a_eq]
  rw [h]
  refine (dD.iiiAction heuv het hue hce hae hbe he).nf_not_mem_S₂ (by show 1 ≤ m; omega)
    (Stroth42Core.t100_faithful (by omega)) (iii_not_word hm)
    (Stroth42Core.t100_parity (by omega)) (dD.iii_parity_e (by omega) heuv het hue hce hae hbe he)
    ⟨1, by rw [iiiAction_wuv, Torus.ofInt_apply]; push_cast; norm_num⟩
    ⟨0, by rw [iiiAction_wt, Torus.ofInt_apply]; simp⟩ ⟨0, by rw [iiiAction_ve]; simp⟩
    (t100_φu_c (m := m)) ?_ true false false
  rw [show ((Torus.c + Torus.a : Torus (StrothTypeIndex.t100 m).k) 0) = 1 by simp [gen]]
  exact Stroth42Core.zmod_not_even_one (by show 1 ≤ m; omega)

theorem iii_sqE (v : Torus (StrothTypeIndex.t100 m).k) (i j l : Bool) :
    (dD.iiiAction heuv het hue hce hae hbe he).sqE v i j l =
      v + (StrothTypeIndex.t100 m).action.d8Act i j l
        (-v + (dD.iiiAction heuv het hue hce hae hbe he).twist i j) := by
  rw [EAction.sqE, iiiAction_ve, iiiAction_φe_apply]
  simp

theorem iii_h4 :
    ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ (m - 1) ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hcomm hpow
  have hm1 : 1 ≤ m := by omega
  set hE := dD.iiiAction heuv het hue hce hae hbe he with hEdef
  obtain ⟨v, i, j, l, k, hv, rfl⟩ := (dD.iii_mem_S₁e_iff hm1 heuv het hue hce hae hbe he).mp hy
  have hφ : hE.φe (Stroth42Core.om100 m ![1, 0, 0]) = Stroth42Core.om100 m ![1, 0, 0] :=
    torusDiag_om100_of_odd hm1 (by decide) (by decide) (by decide) _
  obtain ⟨rfl, rfl⟩ := EAction.t100_comm_c₁ dD hE hm1 hφ hcomm
  cases k
  ·
    simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hcomm hpow
    refine dD.t100_h4 hm _ ?_ hcomm hpow
    exact (dD.mem_S₁_iff hm1 (Stroth42Core.t100_parity hm1)).mpr ⟨v, false, false, l, hv, rfl⟩
  ·
    simp only [Stroth42Core.bpow, ↓reduceIte] at hpow
    have hsq := hE.nfe_e_mul_self v false false l
    rw [Bool.and_false, d8_fff, mul_one, dD.iii_sqE hm heuv het hue hce hae hbe he,
      twist_ff hE rfl rfl, add_zero] at hsq
    rw [dD.pow_two_pow_of_mul_self hsq (by omega : 1 ≤ m - 1), dD.t100_c_pow] at hpow
    have h0 := congrFun (dD.ofTorus_inj hpow) 0
    have hc0 : ((v + (StrothTypeIndex.t100 m).action.d8Act false false l (-v)) 0) = 0 := by
      cases l
      · simp [SigmaFourAction.d8Act]
      · simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
          AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
        rw [Pi.add_apply, t100_φu_zero, Pi.neg_apply, add_neg_cancel]
    rw [Pi.smul_apply, hc0, smul_zero, Stroth42Core.om100, Torus.ofInt_apply] at h0
    have h1 : ((((![1, 0, 0] : Fin 3 → ℤ) 0) * 2 ^ ((StrothTypeIndex.t100 m).k 0 - 1) : ℤ) :
        ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) ≠ 0 := by
      simp only [Matrix.cons_val_zero, one_mul]
      push_cast
      exact two_pow_pred_ne_zero hm1
    exact h1 h0.symm

theorem iii_h8 :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ (m - 1) ≠ 1 := by
  intro y hy hy1 n hn hz
  have hm1 : 1 ≤ m := by omega
  set hE := dD.iiiAction heuv het hue hce hae hbe he with hEdef
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  have hodd : ¬ Even (v 0) := fun hv => hy1
    ((dD.iii_mem_S₁e_iff hm1 heuv het hue hce hae hbe he).mpr ⟨v, i, j, l, k, hv, rfl⟩)
  cases k
  ·
    simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hy1 hz ⊢
    refine dD.t100_h8 hm _ (dD.nf_mem v i j l) (fun h => ?_) n hn hz
    apply hy1
    have hle : Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G) ≤
        Subgroup.closure
          ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} : Set G) :=
      Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢; tauto)
    exact hle h
  · exfalso
    simp only [Stroth42Core.bpow, ↓reduceIte] at hz
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    have hx0 : x 0 % 2 = 1 := by
      rw [Torus.ofInt_apply,
        Stroth42Core.even_intCast_iff (show 1 ≤ (StrothTypeIndex.t100 m).k 0 from hm1),
        Int.not_even_iff] at hodd
      exact hodd
    have hsq := hE.nfe_e_mul_self (Torus.ofInt _ x) i j l
    rw [dD.iii_sqE hm heuv het hue hce hae hbe he] at hsq
    have h1 : (dD.d8 (false && false) false false : G) = 1 := dD.d8_fff
    have h2 : (dD.d8 (false && true) false false : G) = 1 := dD.d8_fff
    have h3 : (dD.d8 (true && false) false false : G) = 1 := dD.d8_fff
    cases i <;> cases j <;> cases l
    ·
      rw [twist_ff hE rfl rfl, add_zero, h1, mul_one] at hsq
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, add_neg_cancel, ofTorus_zero] at hsq
      rw [Stroth42Core.pow_two_pow_eq_mul_self _ hn, hsq, one_pow, dD.t100_c_pow] at hz
      have hz' := dD.ofTorus_inj (hz.symm.trans dD.ofTorus_zero.symm)
      rw [← om100_zero, om100_eq_iff hm1] at hz'
      exact absurd hz' (by decide)
    ·
      rw [twist_ff hE rfl rfl, add_zero, h3, mul_one] at hsq
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, map_neg, Stroth42Core.t100_φu, ← Torus.ofInt_neg,
        ← Torus.ofInt_add] at hsq
      rw [dD.pow_two_pow_of_mul_self hsq hn, dD.t100_c_pow, om100_c, ← natCast_zsmul,
        ← Torus.ofInt_zsmul] at hz
      obtain ⟨h0, -, -⟩ := (Stroth42Core.t100_ofInt_eq_iff _ _).mp (dD.ofTorus_inj hz)
      simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, Matrix.cons_val_zero,
        add_neg_cancel, mul_zero, sub_zero] at h0
      have hlt : (2 : ℤ) ^ (m - 1) < 2 ^ m := pow_lt_pow_right₀ (by norm_num) (by omega)
      have hpos : (0 : ℤ) < 2 ^ (m - 1) := by positivity
      exact absurd (Int.le_of_dvd hpos h0) (not_le.mpr hlt)
    ·
      rw [twist_ft hE rfl rfl, h2, mul_one] at hsq
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, ← Torus.ofInt_neg, ← Torus.ofInt_add, Stroth42Core.t100_φt] at hsq
      refine dD.t100_pow_ne_c₁_of_odd hm1 hsq ?_ hn hz
      simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      omega
    ·
      exact dD.t100_pow_ne_c₁_of_sq_uv hm1 hsq hn hz
    ·
      rw [twist_tf hE rfl rfl, h1, mul_one] at hsq
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, ← Torus.ofInt_neg, ← Torus.ofInt_add,
        Stroth42Core.t100_φuv] at hsq
      refine dD.t100_pow_ne_c₁_of_odd hm1 hsq ?_ hn hz
      simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      omega
    ·
      rw [twist_tf hE rfl rfl, h3, mul_one] at hsq
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, ← Torus.ofInt_neg, ← Torus.ofInt_add, Stroth42Core.t100_φuv,
        Stroth42Core.t100_φu] at hsq
      by_cases hpar : (x 1 + x 2) % 2 = 0
      · refine dD.t100_pow_ne_c₁_of_odd hm1 hsq ?_ hn hz
        simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        omega
      · refine dD.t100_pow_ne_c₁_of_two_mul hm1 hsq ?_ hn hz
        simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        ring
    ·
      rw [twist_tt hE rfl rfl, h2, mul_one] at hsq
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, ← Torus.ofInt_neg, ← Torus.ofInt_add, Stroth42Core.t100_φuv,
        Stroth42Core.t100_φt] at hsq
      refine dD.t100_pow_ne_c₁ hm1 hsq (Or.inl ?_) hn hz
      simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    ·
      exact dD.t100_pow_ne_c₁_of_sq_uv hm1 hsq hn hz

theorem iii_h9 :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D := by
  have hm1 : 1 ≤ m := by omega
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
  set hE := dD.iiiAction heuv het hue hce hae hbe he with hEdef
  refine EAction.t100_h9_of dD hE hm
    (torusDiag_om100_of_odd hm1 (by decide) (by decide) (by decide) _)
    (hE.e_not_mem (iii_not_word hm))
    (fun p : Bool × Bool × Bool =>
      Stroth42Core.om100 m ![(p.1.toNat : ℤ), p.2.1.toNat, p.2.2.toNat])
    (fun p : ZMod (2 ^ m) × ZMod (2 ^ (m + 1)) =>
      Torus.ofInt (StrothTypeIndex.t100 m).k ![(p.1.val : ℤ), -(p.2.val : ℤ), (p.2.val : ℤ)])
    ?_ ?_ ?_ ?_
  ·
    intro w hw
    rw [iiiAction_φe_apply] at hw
    have h2 : (2 : ℤ) • w = 0 := by
      rw [two_zsmul]
      nth_rewrite 1 [← hw]
      exact neg_add_cancel w
    obtain ⟨ε, hε, rfl⟩ := (Torus.two_zsmul_eq_zero_iff (Stroth42Core.t100_one_le_k hm1) w).mp h2
    refine ⟨(decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1)), ?_⟩
    rw [Stroth42Core.om100]
    congr 1
    funext i
    fin_cases i <;> simp [Stroth42Core.bool_toNat_cast_eq (hε _)]
  ·
    intro w hw
    rw [iiiAction_φe_apply, map_neg] at hw
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
    rw [Stroth42Core.t100_φu, ← Torus.ofInt_neg, Stroth42Core.t100_ofInt_eq_iff] at hw
    obtain ⟨-, h1, -⟩ := hw
    simp only [Pi.neg_apply, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h1
    refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((x 2 : ℤ) : ZMod (2 ^ (m + 1)))), ?_⟩
    rw [Stroth42Core.t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast]
    have hm' : ((2 ^ m : ℕ) : ℤ) = 2 ^ m := by push_cast; rfl
    have hm'' : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 ^ (m + 1) := by push_cast; rfl
    rw [hm', hm'']
    refine ⟨⟨x 0 / 2 ^ m, by rw [Int.emod_def]; ring⟩, ?_, ⟨x 2 / 2 ^ (m + 1), by
      rw [Int.emod_def]; ring⟩⟩
    obtain ⟨c, hc⟩ := h1
    exact ⟨c - x 2 / 2 ^ (m + 1), by rw [Int.emod_def]; linear_combination hc⟩
  · have hc : Nat.card (Bool × Bool × Bool) = 8 := by simp [Nat.card_eq_fintype_card]
    rw [hc]
    have h8 : (2 : ℕ) ^ 8 ≤ 2 ^ (m + (m + 1) + (m + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
      show 2 * (2 ^ m * 2 ^ (m + 1)) = 2 ^ (m + m + 2) by ring]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end IIIh

section IIh

variable (hm : 2 ≤ m)
  (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
  (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
  (hce : e⁻¹ * (dD.c : G) * e = dD.c)
  (hae : e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m)
  (hbe : e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m)
  (he : e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))

theorem iiAction_φe :
    (dD.iiAction heuv het hue hce hae hbe he).φe = torusDiag _ ![1, 1 + 2 ^ m, 1 + 2 ^ m] := rfl

theorem iiAction_wuv :
    (dD.iiAction heuv het hue hce hae hbe he).wuv = Torus.ofInt _ ![2, 1, 1] := rfl

theorem iiAction_wt :
    (dD.iiAction heuv het hue hce hae hbe he).wt = Torus.ofInt _ ![0, -1, 0] := rfl

theorem iiAction_ve :
    (dD.iiAction heuv het hue hce hae hbe he).ve = Torus.ofInt _ ![-1 + 2 ^ (m - 1), 0, 0] := rfl

theorem ii_not_word (hm : 2 ≤ m) (i j l : Bool)
    (h : ∀ v, torusDiag (StrothTypeIndex.t100 m).k ![1, 1 + 2 ^ m, 1 + 2 ^ m] v =
      (StrothTypeIndex.t100 m).action.d8Act i j l v) : False := by
  have hm1 : 1 ≤ m := by omega
  refine t100_not_word hm1 _
    (torusDiag_om100_of_odd hm1 (by norm_num) (one_add_two_pow_emod_two hm1)
      (one_add_two_pow_emod_two hm1) _)
    (torusDiag_om100_of_odd hm1 (by norm_num) (one_add_two_pow_emod_two hm1)
      (one_add_two_pow_emod_two hm1) _) (w := Torus.a) ?_ i j l h
  rw [torusDiag_gen]
  intro ha
  have ha' : Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1 + 2 ^ m, 0] =
      Torus.ofInt _ ![0, 1, 0] := by
    rw [show Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1 + 2 ^ m, 0] =
      (1 + 2 ^ m : ℤ) • Torus.a by rw [Torus.ofInt_eq_zsmul_gens]; simp,
      show Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0] = Torus.a by
      rw [Torus.ofInt_eq_zsmul_gens]; simp]
    simpa using ha
  obtain ⟨-, h1, -⟩ := (Stroth42Core.t100_ofInt_eq_iff _ _).mp ha'
  have h2 : (2 : ℤ) ^ (m + 1) ∣ 2 ^ m := by
    have h := h1.neg_right
    have h' : -((![0, 1, 0] : Fin 3 → ℤ) 1 - (![0, 1 + 2 ^ m, 0] : Fin 3 → ℤ) 1) = 2 ^ m := by
      show -(1 - (1 + 2 ^ m) : ℤ) = 2 ^ m
      ring
    rwa [h'] at h
  have hlt : (2 : ℤ) ^ m < 2 ^ (m + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℤ) < 2 ^ m := by positivity
  exact absurd (Int.le_of_dvd hpos h2) (not_le.mpr hlt)

include hm heuv het hue hce hae hbe he

theorem ii_h1 :
    (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 :=
  (dD.iiAction heuv het hue hce hae hbe he).relIndex_S (ii_not_word hm)

theorem ii_h2 : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
  (dD.iiAction heuv het hue hce hae hbe he).e_not_mem (ii_not_word hm)

theorem ii_h4 :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ m ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hcomm hpow
  have hm1 : 1 ≤ m := by omega
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨rfl, rfl⟩ := dD.t100_comm_z hm1 hcomm
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hsq := dD.nf_mul_self_of_false (Torus.ofInt _ x) (i := false) (j := false) (l := l)
    (Bool.and_false l)
  rw [dD.pow_two_pow_of_mul_self hsq hm1, dD.t100_c_pow, om100_c] at hpow
  have hu : (StrothTypeIndex.t100 m).action.d8Act false false l (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0, if l then x 2 else x 1, if l then x 1 else x 2] := by
    cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Stroth42Core.t100_φu]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hu, ← Torus.ofInt_add, ← natCast_zsmul, ← Torus.ofInt_zsmul] at hpow
  obtain ⟨h0, -, -⟩ := (Stroth42Core.t100_ofInt_eq_iff _ _).mp (dD.ofTorus_inj hpow)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at h0
  push_cast at h0
  have h2 : (2 : ℤ) ^ (m - 1) * (x 0 + x 0) = 2 ^ m * x 0 := by
    rw [show (2 : ℤ) ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]
    ring
  rw [h2] at h0
  have h' : (2 : ℤ) ^ m ∣ 2 ^ (m - 1) := by
    have := dvd_add h0 (dvd_mul_right ((2 : ℤ) ^ m) (x 0))
    simpa using this
  have hlt : (2 : ℤ) ^ (m - 1) < 2 ^ m := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℤ) < 2 ^ (m - 1) := by positivity
  exact absurd (Int.le_of_dvd hpos h') (not_le.mpr hlt)

theorem ii_odd_sqE (v : Torus (StrothTypeIndex.t100 m).k) (i j l : Bool) :
    ¬ Even (((dD.iiAction heuv het hue hce hae hbe he).sqE v i j l) 0) := by
  have hm1 : 1 ≤ m := by omega
  have hk : 1 ≤ (StrothTypeIndex.t100 m).k 0 := hm1
  rw [EAction.even_sqE_iff _ hk (Stroth42Core.t100_parity hm1)
    (fun w => even_torusDiag_iff hm1 _ (by norm_num) w)
    ⟨1, by rw [iiAction_wuv, Torus.ofInt_apply]; push_cast; norm_num⟩
    ⟨0, by rw [iiAction_wt, Torus.ofInt_apply]; simp⟩, iiAction_ve, Torus.ofInt_apply,
    Stroth42Core.even_intCast_iff hk, Int.not_even_iff]
  simp only [Matrix.cons_val_zero]
  obtain ⟨k, hk'⟩ : ∃ k, m - 1 = k + 1 := ⟨m - 2, by omega⟩
  rw [hk', pow_succ]
  omega

theorem ii_h6' :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → y * y ≠ 1 := by
  intro y hy hyS hyy
  have hm1 : 1 ≤ m := by omega
  set hE := dD.iiAction heuv het hue hce hae hbe he with hEdef
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  cases k
  · exact hyS (by simpa [Stroth42Core.bpow] using dD.nf_mem v i j l)
  simp only [Stroth42Core.bpow, ↓reduceIte] at hyy
  rw [hE.nfe_e_mul_self] at hyy
  cases hlj : (l && j)
  · rw [hlj, d8_fff, mul_one, ofTorus_eq_one_iff] at hyy
    have hodd := dD.ii_odd_sqE hm heuv het hue hce hae hbe he v i j l
    rw [hyy] at hodd
    exact hodd ⟨0, by simp⟩
  · rw [hlj] at hyy
    have hnot := dD.d8_not_mem (Stroth42Core.t100_faithful hm1) (i := true) (j := false)
      (l := false) (by decide) (hE.sqE v i j l)
    rw [hyy] at hnot
    exact hnot (one_mem _)

theorem ii_h7 :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16 := by
  intro E hE hinv
  refine dD.t100_h7 hm E (fun x hx => ?_) hinv
  obtain ⟨hxS', hxC⟩ := Subgroup.mem_inf.mp (hE hx)
  refine Subgroup.mem_inf.mpr ⟨?_, hxC⟩
  by_contra hxS
  exact dD.ii_h6' hm heuv het hue hce hae hbe he x hxS' hxS (hinv x hx)

theorem ii_h8 :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ m ≠ 1 := by
  intro y hy hyS n hn hz
  have hm1 : 1 ≤ m := by omega
  set hE := dD.iiAction heuv het hue hce hae hbe he with hEdef
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  cases k
  · exact absurd (by simpa [Stroth42Core.bpow] using dD.nf_mem v i j l) hyS
  simp only [Stroth42Core.bpow, ↓reduceIte] at hz ⊢
  have hsq := hE.nfe_e_mul_self v i j l
  cases hlj : (l && j)
  · rw [hlj, d8_fff, mul_one] at hsq
    intro h1
    rw [dD.pow_two_pow_of_mul_self hsq hm1, ofTorus_eq_one_iff] at h1
    have h0 := congrFun h1 0
    have hodd := dD.ii_odd_sqE hm heuv het hue hce hae hbe he v i j l
    rw [Stroth42Core.zmod_not_even_iff_odd (show 1 ≤ (StrothTypeIndex.t100 m).k 0 from hm1)]
      at hodd
    obtain ⟨r, hr⟩ := hodd
    rw [Pi.smul_apply, hr, Pi.zero_apply, nsmul_eq_mul] at h0
    push_cast at h0
    have h2 := two_mul_two_pow_pred (n := (StrothTypeIndex.t100 m).k 0)
    have h3 := two_pow_pred_ne_zero (n := (StrothTypeIndex.t100 m).k 0) hm1
    apply h3
    calc (2 : ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) ^ ((StrothTypeIndex.t100 m).k 0 - 1)
        = 2 ^ ((StrothTypeIndex.t100 m).k 0 - 1) * (2 * r + 1) -
          (2 * 2 ^ ((StrothTypeIndex.t100 m).k 0 - 1)) * r := by ring
      _ = 0 := by
        rw [h2, zero_mul, sub_zero]
        exact h0
  · rw [hlj] at hsq
    exact absurd hz (dD.t100_pow_ne_c₁_of_sq_uv hm1 hsq hn)

theorem ii_h9 :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D := by
  have hm1 : 1 ≤ m := by omega
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
  set hE := dD.iiAction heuv het hue hce hae hbe he with hEdef
  have hm' : ((2 ^ m : ℕ) : ℤ) = 2 ^ m := by push_cast; rfl
  have hm'' : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 ^ (m + 1) := by push_cast; rfl
  have h2m : (2 : ℤ) ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
  refine EAction.t100_h9_of dD hE hm
    (torusDiag_om100_of_odd hm1 (by norm_num) (one_add_two_pow_emod_two hm1)
      (one_add_two_pow_emod_two hm1) _)
    (dD.ii_h2 hm heuv het hue hce hae hbe he)
    (fun p : ZMod (2 ^ m) × ZMod (2 ^ m) × ZMod (2 ^ m) =>
      Torus.ofInt (StrothTypeIndex.t100 m).k
        ![(p.1.val : ℤ), 2 * (p.2.1.val : ℤ), 2 * (p.2.2.val : ℤ)])
    (fun p : ZMod (2 ^ m) × ZMod (2 ^ (m + 1)) =>
      Torus.ofInt (StrothTypeIndex.t100 m).k
        ![(p.1.val : ℤ), (1 + 2 ^ m) * (p.2.val : ℤ), (p.2.val : ℤ)])
    ?_ ?_ ?_ ?_
  ·
    intro w hw
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
    rw [iiAction_φe, torusDiag_ofInt, Stroth42Core.t100_ofInt_eq_iff] at hw
    obtain ⟨-, h1, h2⟩ := hw
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h1 h2
    have he1 : (2 : ℤ) ∣ x 1 := by
      have : (2 : ℤ) ^ m * 2 ∣ 2 ^ m * (-(x 1)) := by
        rw [← h2m]; convert h1 using 1; ring
      exact (dvd_neg).mp ((mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp this)
    have he2 : (2 : ℤ) ∣ x 2 := by
      have : (2 : ℤ) ^ m * 2 ∣ 2 ^ m * (-(x 2)) := by
        rw [← h2m]; convert h2 using 1; ring
      exact (dvd_neg).mp ((mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp this)
    obtain ⟨y1, hy1⟩ := he1
    obtain ⟨y2, hy2⟩ := he2
    refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((y1 : ℤ) : ZMod (2 ^ m)), ((y2 : ℤ) : ZMod (2 ^ m))),
      ?_⟩
    rw [Stroth42Core.t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast, hm']
    refine ⟨⟨x 0 / 2 ^ m, by rw [Int.emod_def]; ring⟩, ⟨y1 / 2 ^ m, ?_⟩, ⟨y2 / 2 ^ m, ?_⟩⟩
    · rw [hy1, Int.emod_def, h2m]; ring
    · rw [hy2, Int.emod_def, h2m]; ring
  ·
    intro w hw
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
    rw [iiAction_φe, torusDiag_ofInt, Stroth42Core.t100_φu,
      Stroth42Core.t100_ofInt_eq_iff] at hw
    obtain ⟨-, h1, -⟩ := hw
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h1
    refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((x 2 : ℤ) : ZMod (2 ^ (m + 1)))), ?_⟩
    rw [Stroth42Core.t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast, hm', hm'']
    obtain ⟨c, hc⟩ := h1
    refine ⟨⟨x 0 / 2 ^ m, by rw [Int.emod_def]; ring⟩, ⟨c + (1 + 2 ^ m) * (x 2 / 2 ^ (m + 1)),
      by rw [Int.emod_def]; linear_combination hc⟩, ⟨x 2 / 2 ^ (m + 1), by
        rw [Int.emod_def]; ring⟩⟩
  · rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod,
      show 2 * (2 ^ m * (2 ^ m * 2 ^ m)) = 2 ^ (m + m + m + 1) by ring]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
      show 2 * (2 ^ m * 2 ^ (m + 1)) = 2 ^ (m + m + 2) by ring]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end IIh

end StrothWeakTypeData

end CFSG.CGT.Stroth77
