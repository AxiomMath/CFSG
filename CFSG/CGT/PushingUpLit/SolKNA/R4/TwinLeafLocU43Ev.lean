module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Arith
public import CFSG.GH74.GLS.C3.Layer1.St1EndNU43Mat

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 (hud P43)
open CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat (hud_bar isPrimeFormGram_one4 coe_scalar_smul barF)
open Matrix

abbrev C1 : Matrix (Fin 4) (Fin 4) F9 := ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)

abbrev UU : Type := primeFormUnitary hud C1

abbrev Gt : Type := UU ⋊[primeFormFieldU hud isPrimeFormGram_one4] (F9 ≃+* F9)

theorem hud_bar9 (x : F9) : hud.bar x = bar9 x := hud_bar x

theorem map_hud_bar (M : Matrix (Fin 4) (Fin 4) F9) : M.map hud.bar = M.map bar9 :=
  Matrix.ext fun i j => hud_bar9 _

theorem barRE_mul_self : barRE * barRE = 1 := by
  refine RingEquiv.ext fun x => ?_
  change bar9 (bar9 x) = x
  exact bar9_bar9 x

theorem barRE_ne_one : barRE ≠ 1 := by
  intro h
  have := congrArg (fun φ : F9 ≃+* F9 => φ ⟨0, 1⟩) h
  revert this
  decide

theorem barRE_pow_two : barRE ^ 2 = 1 := by
  rw [pow_two, barRE_mul_self]

theorem barRE_pow_mod (n : ℕ) : barRE ^ n = barRE ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, barRE_pow_two, one_pow, mul_one]

theorem barRE_pow_eq_one_iff {n : ℕ} (hn : n < 2) : barRE ^ n = 1 ↔ n = 0 := by
  constructor
  · intro h
    by_contra h0
    have : n = 1 := by omega
    subst this
    exact barRE_ne_one (by simpa using h)
  · rintro rfl
    rfl

theorem barRE_pow_inj {m n : ℕ} (hm : m < 2) (hn : n < 2) (h : barRE ^ m = barRE ^ n) : m = n := by
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · rfl
  · exact absurd (by simpa using h.symm) barRE_ne_one
  · exact absurd (by simpa using h) barRE_ne_one
  · rfl

@[expose] def glOf (z : Array ℕ) (h : rawValid z = true) : GL (Fin 4) F9 :=
  ⟨matC z, ((matC z).map bar9)ᵀ, mul_eq_one_comm.mpr ((rawValid_iff z).1 h).2.2.2,
    ((rawValid_iff z).1 h).2.2.2⟩

theorem glOf_val (z : Array ℕ) (h : rawValid z = true) :
    ((glOf z h : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = matC z := rfl

theorem glOf_mem (z : Array ℕ) (h : rawValid z = true) : glOf z h ∈ primeFormUnitary hud C1 := by
  rw [mem_primeFormUnitary]
  change ((matC z).map hud.bar)ᵀ * C1 * matC z = C1
  rw [map_hud_bar, show C1 = 1 from Units.val_one, Matrix.mul_one]
  exact ((rawValid_iff z).1 h).2.2.2

@[expose] noncomputable def unitOf (z : Array ℕ) : UU :=
  if h : rawValid z = true then ⟨glOf z h, glOf_mem z h⟩ else 1

theorem unitOf_val {z : Array ℕ} (h : rawValid z = true) :
    ((unitOf z : UU) : GL (Fin 4) F9) = glOf z h := by
  unfold unitOf
  rw [dif_pos h]

theorem unitOf_mat {z : Array ℕ} (h : rawValid z = true) :
    (((unitOf z : UU) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = matC z := by
  rw [unitOf_val h]
  rfl

@[expose] noncomputable def decG (z : Array ℕ) : Gt := ⟨unitOf z, barRE ^ z[16]!⟩

@[expose] noncomputable def ev (z : Array ℕ) : MulAut P43 :=
  primeFormPsi hud isPrimeFormGram_one4 (decG z)

theorem coe_glAut_pow (x : ℕ) (hx : x < 2) (g : GL (Fin 4) F9) :
    ((glAut (barRE ^ x) g : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      if x = 1 then ((g : Matrix (Fin 4) (Fin 4) F9)).map bar9 else (g : Matrix (Fin 4) (Fin 4) F9) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · simp only [pow_zero, if_neg (by norm_num : ¬ ((0 : ℕ) = 1)), coe_glAut]
    exact Matrix.ext fun i j => rfl
  · simp only [pow_one, if_true, coe_glAut]
    rfl

theorem decG_left (z : Array ℕ) : (decG z).left = unitOf z := rfl

theorem decG_right (z : Array ℕ) : (decG z).right = barRE ^ z[16]! := rfl

theorem decG_mulRaw {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true) :
    decG (mulRaw x y) = decG x * decG y := by
  have hxy := rawValid_mulRaw hx hy
  have hx2 : x[16]! < 2 := ((rawValid_iff x).1 hx).2.2.1
  have hy2 : y[16]! < 2 := ((rawValid_iff y).1 hy).2.2.1
  have hx9 := ((rawValid_iff x).1 hx).2.1
  have hy9 := ((rawValid_iff y).1 hy).2.1
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, decG_left, decG_left, decG_right, decG_left]
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, unitOf_mat hxy, unitOf_mat hx, coe_primeFormFieldU,
      coe_glAut_pow _ hx2, unitOf_mat hy, matC_mulRaw hx9 hy9]
  · rw [SemidirectProduct.mul_right, decG_right, decG_right, decG_right, mulRaw_getElem_16,
      ← barRE_pow_mod, pow_add]

theorem ev_mulRaw {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true) :
    ev (mulRaw x y) = ev x * ev y := by
  unfold ev
  rw [decG_mulRaw hx hy, map_mul]

theorem rawValid_scal {c : ℕ} (hc : c = 3 ∨ c = 6 ∨ c = 1 ∨ c = 2) : rawValid (scal c) = true := by
  rcases hc with rfl | rfl | rfl | rfl <;> decide +kernel

theorem hud_norm9 (x : F9) : hud.norm x = x * bar9 x := by
  unfold UnitaryFieldData.norm
  rw [hud_bar9]

theorem norm_uncode9_aux : ∀ c : Fin 9, ((c : ℕ) = 3 ∨ (c : ℕ) = 6 ∨ (c : ℕ) = 1 ∨ (c : ℕ) = 2) ↔
    uncode9 c * bar9 (uncode9 c) = 1 := by decide

theorem uncode9_ne_zero_aux : ∀ c : Fin 9, (c : ℕ) ≠ 0 → uncode9 c ≠ 0 := by decide

theorem ev_scal {c : ℕ} (hc : c = 3 ∨ c = 6 ∨ c = 1 ∨ c = 2) : ev (scal c) = 1 := by
  have hv := rawValid_scal hc
  have hc9 : c < 9 := by omega
  have hc0 : c ≠ 0 := by omega
  have hn : uncode9 c ≠ 0 := uncode9_ne_zero_aux ⟨c, hc9⟩ hc0
  have hno : uncode9 c * bar9 (uncode9 c) = 1 := (norm_uncode9_aux ⟨c, hc9⟩).1 hc
  unfold ev
  refine (primeFormPsi_eq_one_iff hud isPrimeFormGram_one4 (by norm_num) _).2 ⟨?_, Units.mk0 _ hn,
    ?_, ?_⟩
  · rw [decG_right, scal_getElem_16, pow_zero]
    rfl
  · rw [Units.val_mk0, hud_norm9]
    exact hno
  · refine Units.ext ?_
    rw [decG_left, unitOf_mat hv, matC_scal hc9, coe_scalar_smul, Units.val_mk0]

theorem isZ_of_ev_eq_one {z : Array ℕ} (hz : rawValid z = true) (h : ev z = 1) : isZ z = true := by
  obtain ⟨hs, h9, h2, hu⟩ := (rawValid_iff z).1 hz
  unfold ev at h
  obtain ⟨hr, c, hno, hl⟩ :=
    (primeFormPsi_eq_one_iff hud isPrimeFormGram_one4 (by norm_num) _).1 h
  rw [decG_right] at hr
  have h16 : z[16]! = 0 := (barRE_pow_eq_one_iff h2).1 hr
  have hmat : matC z = (c : F9) • (1 : Matrix (Fin 4) (Fin 4) F9) := by
    have := congrArg (fun g : GL (Fin 4) F9 => (g : Matrix (Fin 4) (Fin 4) F9)) hl
    simp only [decG_left, unitOf_mat hz, coe_scalar_smul] at this
    exact this
  have hc00 : uncode9 z[0]! = (c : F9) := by
    have := congrFun (congrFun hmat 0) 0
    simpa [matC] using this
  have hnorm : (c : F9) * bar9 (c : F9) = 1 := by rw [← hud_norm9]; exact hno
  have hz0 : z[0]! < 9 := h9 0 (by norm_num)
  have hcc : z[0]! = 3 ∨ z[0]! = 6 ∨ z[0]! = 1 ∨ z[0]! = 2 :=
    (norm_uncode9_aux ⟨z[0]!, hz0⟩).2 (by rw [hc00]; exact hnorm)
  have hzs : z = scal z[0]! := by
    refine arr17_ext hs (size_scal _) h9 (fun k hk => scal_lt hz0 hk) ?_ ?_
    · rw [hmat, matC_scal hz0, hc00]
    · rw [h16, scal_getElem_16]
  unfold isZ
  rw [hzs]
  rcases hcc with h3 | h3 | h3 | h3 <;> rw [h3] <;> simp

theorem isZ_cases {z : Array ℕ} (h : isZ z = true) :
    ∃ c, (c = 3 ∨ c = 6 ∨ c = 1 ∨ c = 2) ∧ z = scal c := by
  unfold isZ at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact ⟨3, by simp, h⟩
  · exact ⟨6, by simp, h⟩
  · exact ⟨1, by simp, h⟩
  · exact ⟨2, by simp, h⟩

theorem ev_eq_one_iff {z : Array ℕ} (hz : rawValid z = true) : ev z = 1 ↔ isZ z = true :=
  ⟨isZ_of_ev_eq_one hz, fun h => by
    obtain ⟨c, hc, rfl⟩ := isZ_cases h
    exact ev_scal hc⟩

theorem smul_one_map_bar9 (c : F9) :
    ((c • (1 : Matrix (Fin 4) (Fin 4) F9)).map bar9) = bar9 c • (1 : Matrix (Fin 4) (Fin 4) F9) := by
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, hij, bar9_zero]

theorem exists_scalar_of_ev_eq {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true)
    (h : ev x = ev y) :
    ∃ c : F9, c * bar9 c = 1 ∧ y[16]! = x[16]! ∧ matC y = c • matC x := by
  have hx2 : x[16]! < 2 := ((rawValid_iff x).1 hx).2.2.1
  have hy2 : y[16]! < 2 := ((rawValid_iff y).1 hy).2.2.1
  have h1 : primeFormPsi hud isPrimeFormGram_one4 ((decG x)⁻¹ * decG y) = 1 := by
    rw [map_mul, map_inv]
    change (ev x)⁻¹ * ev y = 1
    rw [h, inv_mul_cancel]
  obtain ⟨hr, c, hno, hl⟩ :=
    (primeFormPsi_eq_one_iff hud isPrimeFormGram_one4 (by norm_num) _).1 h1
  rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right] at hr
  have hrr : (decG x).right = (decG y).right := inv_mul_eq_one.1 hr
  rw [decG_right, decG_right] at hrr
  have h16 : y[16]! = x[16]! := (barRE_pow_inj hx2 hy2 hrr).symm
  have hxy : decG y = decG x * ((decG x)⁻¹ * decG y) := (mul_inv_cancel_left _ _).symm
  have hL : (decG y).left = (decG x).left *
      (primeFormFieldU hud isPrimeFormGram_one4 (decG x).right) ((decG x)⁻¹ * decG y).left := by
    have := congrArg SemidirectProduct.left hxy
    rw [SemidirectProduct.mul_left] at this
    exact this
  have hLm : matC y = matC x * ((glAut (barRE ^ x[16]!) ((((decG x)⁻¹ * decG y).left : UU) :
      GL (Fin 4) F9)) : Matrix (Fin 4) (Fin 4) F9) := by
    have := congrArg (fun u : UU => (((u : UU) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)) hL
    simp only [decG_left, unitOf_mat hy, Subgroup.coe_mul, Units.val_mul, coe_primeFormFieldU,
      decG_right, unitOf_mat hx] at this
    exact this
  rw [hl, coe_glAut_pow _ hx2, coe_scalar_smul] at hLm
  rcases (by omega : x[16]! = 0 ∨ x[16]! = 1) with h0 | h0
  · refine ⟨c, ?_, h16, ?_⟩
    · rw [← hud_norm9]; exact hno
    · rw [hLm, if_neg (by omega), Matrix.mul_smul, Matrix.mul_one]
  · refine ⟨bar9 c, ?_, h16, ?_⟩
    · rw [bar9_bar9, mul_comm, ← hud_norm9]; exact hno
    · rw [hLm, if_pos h0, smul_one_map_bar9, Matrix.mul_smul, Matrix.mul_one]

theorem uncode9_surj_aux : ∀ c : F9, ∃ d : Fin 9, uncode9 d = c := by decide

theorem mC_cases_aux : ∀ u : Fin 9, (u : ℕ) ≠ 0 →
    (mC u = 3 ∨ mC u = 6 ∨ mC u = 1 ∨ mC u = 2) := by decide

theorem mC_firstNZ_cases {z : Array ℕ} (hz : rawValid z = true) :
    mC (firstNZ z) = 3 ∨ mC (firstNZ z) = 6 ∨ mC (firstNZ z) = 1 ∨ mC (firstNZ z) = 2 := by
  have h9 := ((rawValid_iff z).1 hz).2.1
  exact mC_cases_aux ⟨firstNZ z, firstNZ_lt h9⟩ (firstNZ_ne_zero hz)

theorem normalize_eq_mulRaw' {z : Array ℕ} (hz : rawValid z = true) :
    normalize z = mulRaw (scal (mC (firstNZ z))) z := by
  obtain ⟨-, h9, h2, -⟩ := (rawValid_iff z).1 hz
  exact normalize_eq_mulRaw h9 h2

theorem ev_normalize {z : Array ℕ} (hz : rawValid z = true) : ev (normalize z) = ev z := by
  rw [normalize_eq_mulRaw' hz, ev_mulRaw (rawValid_scal (mC_firstNZ_cases hz)) hz,
    ev_scal (mC_firstNZ_cases hz), one_mul]

theorem normalize_eq_of_ev_eq {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true)
    (h : ev x = ev y) : normalize x = normalize y := by
  obtain ⟨c, hno, h16, hm⟩ := exists_scalar_of_ev_eq hx hy h
  obtain ⟨d, hd⟩ := uncode9_surj_aux c
  have hd9 : (d : ℕ) < 9 := d.2
  have hdd : ((d : ℕ) = 3 ∨ (d : ℕ) = 6 ∨ (d : ℕ) = 1 ∨ (d : ℕ) = 2) :=
    (norm_uncode9_aux d).2 (by rw [hd]; exact hno)
  obtain ⟨hxs, hx9, hx2, -⟩ := (rawValid_iff x).1 hx
  obtain ⟨hys, hy9, hy2, -⟩ := (rawValid_iff y).1 hy
  have hk : ∀ k < 16, y[k]! = mulC d x[k]! := by
    intro k hk
    have h1 := congrFun (congrFun hm ⟨k / 4, by omega⟩) ⟨k % 4, by omega⟩
    have e : 4 * (k / 4) + k % 4 = k := by omega
    simp only [matC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, e] at h1
    rw [← hd, ← uncode9_mulC hd9 (hx9 k hk)] at h1
    exact uncode9_inj (hy9 k hk) (mulC_lt _ _) h1
  have hcc : (d : ℕ) = 1 ∨ (d : ℕ) = 2 ∨ (d : ℕ) = 3 ∨ (d : ℕ) = 6 := by omega
  exact (normalize_eq_of_mulC hx hy hcc h16 hk).symm

theorem eqZ_iff_ev {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true) :
    eqZ x y = true ↔ ev x = ev y := by
  unfold eqZ
  rw [beq_iff_eq]
  constructor
  · intro h
    rw [← ev_normalize hx, ← ev_normalize hy, h]
  · intro h
    exact normalize_eq_of_ev_eq hx hy h

theorem eqZ_ev {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true)
    (h : eqZ x y = true) : ev x = ev y := (eqZ_iff_ev hx hy).1 h

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
