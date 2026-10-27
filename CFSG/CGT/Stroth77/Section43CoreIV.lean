module

public import CFSG.CGT.Stroth77.Section43CoreE

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

section IV

variable (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
  (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
  (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
  (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m)
  (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m)
  (he : e * e = (dD.c : G) ^ 2 ^ (m - 1))

theorem ivAction_φe :
    (dD.ivAction heuv het hue hce hae hbe he).φe =
      torusDiag _ ![-1, -1 + 2 ^ m, -1 + 2 ^ m] := rfl

theorem ivAction_wuv :
    (dD.ivAction heuv het hue hce hae hbe he).wuv = Torus.ofInt _ ![2, 1, 1] := rfl

theorem ivAction_wt :
    (dD.ivAction heuv het hue hce hae hbe he).wt = Torus.ofInt _ ![0, -1, 0] := rfl

theorem ivAction_ve :
    (dD.ivAction heuv het hue hce hae hbe he).ve = Torus.ofInt _ ![2 ^ (m - 1), 0, 0] := rfl

theorem iv_sqE_ne_zero (hm : 2 ≤ m) (x : Fin 3 → ℤ) (i j l : Bool) (hlj : (l && j) = false) :
    (dD.ivAction heuv het hue hce hae hbe he).sqE (Torus.ofInt _ x) i j l ≠ 0 := by
  intro h0
  have hwuv := dD.ivAction_wuv heuv het hue hce hae hbe he
  have hwt := dD.ivAction_wt heuv het hue hce hae hbe he
  simp only [EAction.sqE, ivAction_φe, ivAction_ve] at h0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hQ : (0 : ℤ) < 2 ^ m' := by positivity
  have e0 : m' + 2 - 1 = m' + 1 := rfl
  have e1 : (2 : ℤ) ^ (m' + 2) = 4 * 2 ^ m' := by ring
  have e2 : (2 : ℤ) ^ (m' + 2 + 1) = 8 * 2 ^ m' := by ring
  have e3 : (2 : ℤ) ^ (m' + 1) = 2 * 2 ^ m' := by ring
  cases i <;> cases j <;> cases l <;> simp only [Bool.and_true, Bool.and_false,
      Bool.true_eq_false, Bool.false_eq_true] at hlj <;>
    simp only [twist_ff _ hwuv hwt, twist_ft _ hwuv hwt, twist_tf _ hwuv hwt,
      twist_tt _ hwuv hwt, SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      Bool.and_false, Bool.and_true, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t100_φuv,
      t100_φt, t100_φu, ← Torus.ofInt_add, ← Torus.ofInt_sub, torusDiag_ofInt, add_zero,
      zero_add, map_zero, t100_ofInt_eq_zero_iff] at h0 <;>
    obtain ⟨d0, d1, d2⟩ := h0 <;>
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, e0, e1, e2, e3] at d0 d1 d2 <;>
    generalize (2 : ℤ) ^ m' = Q at hQ d0 d1 d2
  ·
    obtain ⟨k, hk⟩ := d0
    have h : 2 * Q * (1 - 2 * k) = 0 := by linear_combination hk
    rcases mul_eq_zero.mp h with h | h <;> omega
  ·
    obtain ⟨k, hk⟩ := d0
    have h : 2 * Q * (1 - 2 * k) = 0 := by linear_combination hk
    rcases mul_eq_zero.mp h with h | h <;> omega
  ·
    obtain ⟨k, hk⟩ := d2
    obtain ⟨j, hj⟩ := d0
    have hx : 2 * x 2 = 2 * (2 * Q * (2 * k + x 2)) := by linear_combination hk
    have hx' := mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) hx
    have h' : 2 * Q * (1 + 2 * (2 * k + x 2) - 8 * (Q * (2 * k + x 2))) = 2 * Q * (2 * j) := by
      linear_combination hj - (2 - 8 * Q) * hx'
    have h'' := mul_left_cancel₀ (by omega : (2 * Q : ℤ) ≠ 0) h'
    omega
  ·
    obtain ⟨k, hk⟩ := d1
    have h : 2 * (4 * (Q * k) - 24 * (Q * Q) - 4 * (Q * x 2) - 2 * (Q * x 1) - 2 * Q + x 2 -
        x 0) + 1 = 0 := by linear_combination (-1 : ℤ) * hk
    omega
  ·
    obtain ⟨k1, hk1⟩ := d1
    obtain ⟨k2, hk2⟩ := d2
    have h12 : 4 * Q * (x 1 - x 2) = 4 * Q * (2 * (k1 - k2)) := by linear_combination hk1 - hk2
    have hx := mul_left_cancel₀ (by omega : (4 * Q : ℤ) ≠ 0) h12
    have hp : 2 * (24 * (Q * Q) + 2 * (Q * x 2) + 4 * (Q * x 1) + 2 * Q + x 0 - 4 * (Q * k1)) =
        x 1 + x 2 + 1 := by linear_combination hk1
    omega
  ·
    obtain ⟨k, hk⟩ := d1
    obtain ⟨j, hj⟩ := d0
    have hx : 2 * x 1 = 2 * (2 * Q * (2 * k + x 1)) := by linear_combination hk
    have hx' := mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) hx
    have h' : 2 * Q * (1 + 2 * (2 * k + x 1) - 8 * (Q * (2 * k + x 1))) = 2 * Q * (2 * j) := by
      linear_combination hj - (2 - 8 * Q) * hx'
    have h'' := mul_left_cancel₀ (by omega : (2 * Q : ℤ) ≠ 0) h'
    omega

end IV

theorem iv_not_word (hm : 2 ≤ m) (i j l : Bool)
    (h : ∀ v, torusDiag (StrothTypeIndex.t100 m).k ![-1, -1 + 2 ^ m, -1 + 2 ^ m] v =
      (StrothTypeIndex.t100 m).action.d8Act i j l v) : False := by
  have hm1 : 1 ≤ m := by omega
  refine t100_not_word hm1 _
    (torusDiag_om100_of_odd hm1 (by norm_num) (neg_one_add_two_pow_emod_two hm1)
      (neg_one_add_two_pow_emod_two hm1) _)
    (torusDiag_om100_of_odd hm1 (by norm_num) (neg_one_add_two_pow_emod_two hm1)
      (neg_one_add_two_pow_emod_two hm1) _) (w := Torus.c) ?_ i j l h
  rw [torusDiag_gen]
  intro hc
  have hc' : Torus.ofInt (StrothTypeIndex.t100 m).k ![-1, 0, 0] = Torus.ofInt _ ![1, 0, 0] := by
    rw [show Torus.ofInt (StrothTypeIndex.t100 m).k ![-1, 0, 0] = (-1 : ℤ) • Torus.c by
      rw [Torus.ofInt_eq_zsmul_gens]; simp,
      show Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] = Torus.c by
      rw [Torus.ofInt_eq_zsmul_gens]; simp]
    simpa using hc
  obtain ⟨h0, -, -⟩ := (t100_ofInt_eq_iff _ _).mp hc'
  have h2 : (2 : ℤ) ^ m ∣ 2 := by simpa using h0
  have h4 : (4 : ℤ) ≤ 2 ^ m := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have := Int.le_of_dvd (by norm_num) h2
  omega

theorem iv_hc₂ (hm : 2 ≤ m) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * y := by
  intro y hy hc
  obtain ⟨v, l, rfl⟩ := dD.t100_mem_CSz (by omega) (Subgroup.mem_inf.mpr ⟨hy,
    Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hc.symm⟩)
  rw [show (dD.c : G) ^ 2 ^ (m - 2) = dD.ofTorus ((2 ^ (m - 2)) • Torus.c) by
    rw [ofTorus_nsmul, ← c_eq]]
  refine (dD.nf_commute_iff v _ false false l).mpr ?_
  cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, map_nsmul, t100_φu_c]

private theorem two_pow_succ_dvd_two_mul (hm : 2 ≤ m) {x : ℤ}
    (h : (2 : ℤ) ^ (m + 1) ∣ x - (-1 + 2 ^ m) * x) : (2 : ℤ) ^ (m + 1) ∣ 2 * x := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hcop : IsCoprime ((2 : ℤ) ^ (n + 2 + 1)) (1 - 2 * 2 ^ n) :=
    (show IsCoprime (2 : ℤ) (1 - 2 * 2 ^ n) from ⟨2 ^ n, 1, by ring⟩).pow_left
  refine hcop.dvd_of_dvd_mul_right ?_
  convert h using 1
  ring

section IVh

variable (hm : 2 ≤ m)
  (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
  (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
  (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
  (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m)
  (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m)
  (he : e * e = (dD.c : G) ^ 2 ^ (m - 1))

include hm heuv het hue hce hae hbe he

theorem iv_h1 :
    (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 :=
  (dD.ivAction heuv het hue hce hae hbe he).relIndex_S (iv_not_word hm)

theorem iv_h2 : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
  (dD.ivAction heuv het hue hce hae hbe he).e_not_mem (iv_not_word hm)

theorem iv_h6' :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → y * y ≠ 1 := by
  intro y hy hyS hyy
  obtain ⟨v, i, j, l, k, rfl⟩ :=
    (dD.ivAction heuv het hue hce hae hbe he).mem_sup_zpowers_iff.mp hy
  cases k
  · apply hyS
    simpa [bpow] using dD.nf_mem v i j l
  · simp only [bpow, ↓reduceIte] at hyy
    rw [(dD.ivAction heuv het hue hce hae hbe he).nfe_e_mul_self] at hyy
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    cases hlj : (l && j)
    · rw [hlj, d8_fff, mul_one, ofTorus_eq_one_iff] at hyy
      exact dD.iv_sqE_ne_zero heuv het hue hce hae hbe he hm x i j l hlj hyy
    · rw [hlj, d8_tff] at hyy
      have hnot := dD.d8_not_mem (t100_faithful (by omega)) (i := true) (j := false)
        (l := false) (by decide)
        ((dD.ivAction heuv het hue hce hae hbe he).sqE (Torus.ofInt _ x) i j l)
      rw [d8_tff, hyy] at hnot
      exact hnot (one_mem _)

theorem iv_h7 :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16 := by
  intro E hE hinv
  refine dD.t100_h7 hm E (fun y hy => ?_) hinv
  obtain ⟨hyS', hyC⟩ := Subgroup.mem_inf.mp (hE hy)
  refine Subgroup.mem_inf.mpr ⟨?_, hyC⟩
  by_contra hyS
  exact dD.iv_h6' hm heuv het hue hce hae hbe he y hyS' hyS (hinv y hy)

theorem iv_h9 :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D := by
  have hm1 : 1 ≤ m := by omega
  haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
  have hpow : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine EAction.t100_h9_of dD (dD.ivAction heuv het hue hce hae hbe he) hm
    (torusDiag_om100_of_odd hm1 (by norm_num) (neg_one_add_two_pow_emod_two hm1)
      (neg_one_add_two_pow_emod_two hm1) _)
    (dD.iv_h2 hm heuv het hue hce hae hbe he) (P₀ := Bool × Bool × Bool)
    (P₁ := Bool × ZMod (2 ^ (m + 1)))
    (fun p => om100 m ![(p.1.toNat : ℤ), p.2.1.toNat, p.2.2.toNat])
    (fun p => Torus.ofInt _
      ![(p.1.toNat : ℤ) * 2 ^ (m - 1), (-1 + 2 ^ m) * (p.2.val : ℤ), (p.2.val : ℤ)])
    ?_ ?_ ?_ ?_
  ·
    intro w hw
    have h2w : (2 : ℤ) • w = 0 := by
      obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
      rw [dD.ivAction_φe heuv het hue hce hae hbe he, torusDiag_ofInt, t100_ofInt_eq_iff] at hw
      obtain ⟨h0, h1, h2⟩ := hw
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
      rw [← Torus.ofInt_zsmul, t100_ofInt_eq_zero_iff]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact ⟨by convert h0 using 1; ring, two_pow_succ_dvd_two_mul hm h1,
        two_pow_succ_dvd_two_mul hm h2⟩
    obtain ⟨ε, hε, rfl⟩ := (Torus.two_zsmul_eq_zero_iff (t100_one_le_k hm1) w).mp h2w
    refine ⟨(decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1)), ?_⟩
    show om100 m _ = om100 m ε
    congr 1
    funext i
    fin_cases i <;> simp [bool_toNat_cast_eq (hε _)]
  ·
    intro w hw
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
    rw [dD.ivAction_φe heuv het hue hce hae hbe he, torusDiag_ofInt, t100_φu,
      t100_ofInt_eq_iff] at hw
    obtain ⟨h0, h1, -⟩ := hw
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1
    obtain ⟨c, hc⟩ := h0
    have hj : x 0 = 2 ^ (m - 1) * c :=
      mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
        (by rw [← mul_assoc, ← hpow]; linear_combination hc)
    refine ⟨(decide (c % 2 = 1), ((x 2 : ℤ) : ZMod (2 ^ (m + 1)))), ?_⟩
    rw [t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast,
      bool_toNat_cast_eq (Int.emod_two_eq_zero_or_one c)]
    have hm'' : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 ^ (m + 1) := by push_cast; rfl
    rw [hm'']
    have h2 : (2 : ℤ) ^ (m + 1) ∣ x 2 - x 2 % 2 ^ (m + 1) :=
      ⟨x 2 / 2 ^ (m + 1), by rw [Int.emod_def]; ring⟩
    refine ⟨⟨c / 2, by rw [hj, hpow, Int.emod_def]; ring⟩, ?_, h2⟩
    have := dvd_add h1 (dvd_mul_of_dvd_right h2 (-1 + 2 ^ m))
    convert this using 1
    ring
  · rw [show Nat.card (Bool × Bool × Bool) = 8 by simp [Nat.card_eq_fintype_card]]
    calc 2 * 8 = 2 ^ 4 := by norm_num
      _ < 2 ^ (m + (m + 1) + (m + 1)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [Nat.card_prod, Nat.card_zmod, show Nat.card Bool = 2 by simp [Nat.card_eq_fintype_card]]
    calc 2 * (2 * 2 ^ (m + 1)) = 2 ^ (m + 3) := by ring
      _ < 2 ^ (m + (m + 1) + (m + 1)) := Nat.pow_lt_pow_right (by norm_num) (by omega)

end IVh

end StrothWeakTypeData

end CFSG.CGT.Stroth77
