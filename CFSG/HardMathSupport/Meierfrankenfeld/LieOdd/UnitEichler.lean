module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {K : Type} [Field K] {p f : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

section Form

variable (h : UnitaryFieldData p f K) (G : Matrix ι ι K)

@[expose] noncomputable def hf (x y : ι → K) : K := gramForm h G x y

theorem hf_add_left (x x' y : ι → K) : hf h G (x + x') y = hf h G x y + hf h G x' y := by
  simp [hf]

theorem hf_add_right (x y y' : ι → K) : hf h G x (y + y') = hf h G x y + hf h G x y' := by
  simp [hf]

theorem hf_smul_left (c : K) (x y : ι → K) : hf h G (c • x) y = h.bar c * hf h G x y := by
  simp [hf]

theorem hf_smul_right (c : K) (x y : ι → K) : hf h G x (c • y) = c * hf h G x y := by
  simp [hf]

theorem hf_neg_left (x y : ι → K) : hf h G (-x) y = -hf h G x y := by
  simp [hf]

theorem hf_neg_right (x y : ι → K) : hf h G x (-y) = -hf h G x y := by
  simp [hf]

theorem hf_sub_left (x x' y : ι → K) : hf h G (x - x') y = hf h G x y - hf h G x' y := by
  simp [hf]

theorem hf_sub_right (x y y' : ι → K) : hf h G x (y - y') = hf h G x y - hf h G x y' := by
  simp [hf]

theorem hf_zero_left (y : ι → K) : hf h G 0 y = 0 := by simp [hf]

theorem hf_zero_right (x : ι → K) : hf h G x 0 = 0 := by simp [hf]

theorem map_hf (hG : (G.map h.bar)ᵀ = G) (x y : ι → K) : h.bar (hf h G x y) = hf h G y x :=
  (gramForm_isSymm h hG).1 x y

theorem hf_self_bar (hG : (G.map h.bar)ᵀ = G) (x : ι → K) : h.bar (hf h G x x) = hf h G x x :=
  map_hf h G hG x x

theorem eq_zero_of_hf_eq_zero (hdet : G.det ≠ 0) {x : ι → K} (hx : ∀ y, hf h G x y = 0) :
    x = 0 :=
  (gramForm_separatingLeft h hdet) x hx

end Form

section Eichler

variable (h : UnitaryFieldData p f K) (G : Matrix ι ι K)

@[expose] def IsQ (v u : ι → K) (c : K) : Prop :=
  hf h G v v = 0 ∧ hf h G v u = 0 ∧ c + h.bar c = -hf h G u u

@[expose] noncomputable def eM (v u : ι → K) (c : K) : Matrix ι ι K :=
  1 + vecMulVec u ((fun i => h.bar (v i)) ᵥ* G) - vecMulVec v ((fun i => h.bar (u i)) ᵥ* G) +
    c • vecMulVec v ((fun i => h.bar (v i)) ᵥ* G)

theorem eM_mulVec (v u : ι → K) (c : K) (w : ι → K) :
    eM h G v u c *ᵥ w = w + hf h G v w • u - hf h G u w • v + (c * hf h G v w) • v := by
  have e : ∀ x : ι → K, ((fun i => h.bar (x i)) ᵥ* G) ⬝ᵥ w = hf h G x w := fun x => by
    rw [← Matrix.dotProduct_mulVec]; rfl
  simp only [eM, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, e, mul_smul]

theorem hf_comm_zero (hG : (G.map h.bar)ᵀ = G) {v u : ι → K} (hu : hf h G v u = 0) :
    hf h G u v = 0 := by
  rw [← map_hf h G hG v u, hu, map_zero]

theorem eM_isom (hG : (G.map h.bar)ᵀ = G) {v u : ι → K} {c : K} (hq : IsQ h G v u c)
    (x y : ι → K) : hf h G (eM h G v u c *ᵥ x) (eM h G v u c *ᵥ y) = hf h G x y := by
  obtain ⟨hv, hu, hc⟩ := hq
  have huv := hf_comm_zero h G hG hu
  rw [eM_mulVec, eM_mulVec]
  simp only [hf_add_left, hf_add_right, hf_sub_left, hf_sub_right, hf_smul_left, hf_smul_right,
    map_mul, map_hf h G hG, hv, hu, huv, mul_zero, add_zero, sub_zero]
  linear_combination (hf h G x v * hf h G v y) * hc

theorem eM_zero (v : ι → K) : eM h G v 0 0 = 1 := by
  refine Matrix.ext_iff_mulVec.2 fun w => ?_
  rw [eM_mulVec, Matrix.one_mulVec]
  simp [hf_zero_left]

theorem eM_mul (hG : (G.map h.bar)ᵀ = G) {v u u' : ι → K} {c c' : K} (hv : hf h G v v = 0)
    (hu : hf h G v u = 0) (hu' : hf h G v u' = 0) :
    eM h G v u c * eM h G v u' c' = eM h G v (u + u') (c + c' - hf h G u u') := by
  have huv := hf_comm_zero h G hG hu
  have hu'v := hf_comm_zero h G hG hu'
  refine Matrix.ext_iff_mulVec.2 fun w => ?_
  rw [← Matrix.mulVec_mulVec, eM_mulVec, eM_mulVec, eM_mulVec]
  simp only [hf_add_left, hf_add_right, hf_sub_left, hf_sub_right, hf_smul_right, hu, hu', hv,
    huv, hu'v, mul_zero, add_zero, sub_zero, smul_add, smul_sub]
  module

theorem eM_congr {v u u' : ι → K} {c c' : K} (h1 : u = u') (h2 : c = c') :
    eM h G v u c = eM h G v u' c' := by
  subst h1; subst h2; rfl

theorem IsQ.neg (hG : (G.map h.bar)ᵀ = G) {v u : ι → K} {c : K} (hq : IsQ h G v u c) :
    IsQ h G v (-u) (h.bar c) := by
  obtain ⟨hv, hu, hc⟩ := hq
  refine ⟨hv, by rw [hf_neg_right, hu, neg_zero], ?_⟩
  rw [hf_neg_left, hf_neg_right, neg_neg, UnitaryFieldData.bar_bar]
  linear_combination hc

@[expose] noncomputable def Tgl (hG : (G.map h.bar)ᵀ = G) {v u : ι → K} {c : K}
    (hq : IsQ h G v u c) : GL ι K where
  val := eM h G v u c
  inv := eM h G v (-u) (h.bar c)
  val_inv := by
    have hq' := hq.neg h G hG
    rw [eM_mul h G hG hq.1 hq.2.1 hq'.2.1]
    have e2 : c + h.bar c - hf h G u (-u) = 0 := by
      rw [hf_neg_right]; linear_combination hq.2.2
    rw [add_neg_cancel, e2]
    exact eM_zero h G v
  inv_val := by
    have hq' := hq.neg h G hG
    rw [eM_mul h G hG hq.1 hq'.2.1 hq.2.1]
    have e2 : h.bar c + c - hf h G (-u) u = 0 := by
      rw [hf_neg_left]; linear_combination hq.2.2
    rw [neg_add_cancel, e2]
    exact eM_zero h G v

theorem det_one_add_of_pow_three {N : Matrix ι ι K} (hN : N ^ 3 = 0) : (1 + N).det = 1 := by
  have hnil : IsNilpotent (-N) := ⟨3, by rw [neg_pow, hN, mul_zero]⟩
  have h1 : (-N).charpoly = Polynomial.X ^ Fintype.card ι :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil).eq_zero
  have h2 := Matrix.eval_charpoly (-N) 1
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h2
  rw [← h2.symm, sub_neg_eq_add]

theorem det_eM (hG : (G.map h.bar)ᵀ = G) {v u : ι → K} {c : K} (hq : IsQ h G v u c) :
    (eM h G v u c).det = 1 := by
  obtain ⟨hv, hu, hc⟩ := hq
  have huv := hf_comm_zero h G hG hu
  have hN : (eM h G v u c - 1) ^ 3 = 0 := by
    have key : ∀ w, (eM h G v u c - 1) *ᵥ w =
        hf h G v w • u - hf h G u w • v + (c * hf h G v w) • v := by
      intro w
      rw [Matrix.sub_mulVec, eM_mulVec, Matrix.one_mulVec]
      abel
    refine Matrix.ext_iff_mulVec.2 fun w => ?_
    rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key, key, key]
    simp only [hf_add_right, hf_sub_right, hf_smul_right, hu, hv, huv, mul_zero, add_zero, sub_zero,
      zero_sub, smul_neg, smul_smul, Matrix.zero_mulVec]
    simp
  have := det_one_add_of_pow_three (N := eM h G v u c - 1) hN
  rwa [add_sub_cancel] at this

theorem unitary_of_isom (A : Matrix ι ι K) (hA : ∀ x y, hf h G (A *ᵥ x) (A *ᵥ y) = hf h G x y) :
    (A.map h.bar)ᵀ * G * A = G :=
  (gramForm_isometry_iff h G A).1 hA

theorem Tgl_mem (hG : (G.map h.bar)ᵀ = G) {v u : ι → K} {c : K} (hq : IsQ h G v u c) :
    Tgl h G hG hq ∈ gramSU h G :=
  ⟨unitary_of_isom h G _ (eM_isom h G hG hq), det_eM h G hG hq⟩

theorem IsQ.mul {v u u' : ι → K} {c c' : K} (hG : (G.map h.bar)ᵀ = G) (hq : IsQ h G v u c)
    (hq' : IsQ h G v u' c') : IsQ h G v (u + u') (c + c' - hf h G u u') := by
  obtain ⟨hv, hu, hc⟩ := hq
  obtain ⟨-, hu', hc'⟩ := hq'
  refine ⟨hv, by rw [hf_add_right, hu, hu', add_zero], ?_⟩
  rw [map_sub, map_add, map_hf h G hG u u', hf_add_left, hf_add_right, hf_add_right]
  linear_combination hc + hc'

end Eichler

section Group

variable (h : UnitaryFieldData p f K) (G : Matrix ι ι K)

@[expose] def smat (g : ↥(gramSU h G)) : Matrix ι ι K := ((g : GL ι K) : Matrix ι ι K)

theorem smat_mul (g g' : ↥(gramSU h G)) : smat h G (g * g') = smat h G g * smat h G g' := rfl

theorem smat_one : smat h G (1 : ↥(gramSU h G)) = 1 := rfl

theorem smat_injective : Function.Injective (smat h G) :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem SU_ext_mulVec {g g' : ↥(gramSU h G)} (H : ∀ w, smat h G g *ᵥ w = smat h G g' *ᵥ w) :
    g = g' :=
  smat_injective h G (Matrix.ext_iff_mulVec.2 H)

theorem scalar_val (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) =
      (c : K) • (1 : Matrix ι ι K) := by
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem mk_ne_one_of_fixed_su {m : ℕ} (g : ↥(gramSU h G)) (hg : g ≠ 1) {w₀ : ι → K}
    (hw₀ : w₀ ≠ 0) (hfix : smat h G g *ᵥ w₀ = w₀) :
    (QuotientGroup.mk g : ↥(gramSU h G) ⧸ normOneScalars h (gramSU h G) m) ≠ 1 := by
  intro hmk
  rw [QuotientGroup.eq_one_iff, mem_normOneScalars] at hmk
  obtain ⟨c, -, -, hc⟩ := hmk
  have hs : smat h G g = (c : K) • (1 : Matrix ι ι K) := by
    have := scalar_val (ι := ι) (K := K) c
    rw [← hc] at this
    exact this
  rw [hs, Matrix.smul_mulVec, Matrix.one_mulVec] at hfix
  have hc1 : (c : K) = 1 := by
    have h0 : ((c : K) - 1) • w₀ = 0 := by rw [sub_smul, hfix, one_smul, sub_self]
    have := (smul_eq_zero.1 h0).resolve_right hw₀
    linear_combination this
  apply hg
  refine SU_ext_mulVec h G fun w => ?_
  rw [hs, hc1, one_smul, smat_one]


variable (hG : (G.map h.bar)ᵀ = G)

include hG

@[expose] noncomputable def Tsu {v u : ι → K} {c : K} (hq : IsQ h G v u c) : ↥(gramSU h G) :=
  ⟨Tgl h G hG hq, Tgl_mem h G hG hq⟩

theorem smat_Tsu {v u : ι → K} {c : K} (hq : IsQ h G v u c) :
    smat h G (Tsu h G hG hq) = eM h G v u c := rfl

theorem Tsu_mulVec {v u : ι → K} {c : K} (hq : IsQ h G v u c) (w : ι → K) :
    smat h G (Tsu h G hG hq) *ᵥ w = w + hf h G v w • u - hf h G u w • v + (c * hf h G v w) • v :=
  eM_mulVec h G v u c w

theorem Tsu_congr {v u u' : ι → K} {c c' : K} (hq : IsQ h G v u c) (hq' : IsQ h G v u' c')
    (h1 : u = u') (h2 : c = c') : Tsu h G hG hq = Tsu h G hG hq' := by
  subst h1; subst h2; rfl

theorem Tsu_mul {v u u' : ι → K} {c c' : K} (hq : IsQ h G v u c) (hq' : IsQ h G v u' c') :
    Tsu h G hG hq * Tsu h G hG hq' = Tsu h G hG (hq.mul h G hG hq') :=
  smat_injective h G (eM_mul h G hG hq.1 hq.2.1 hq'.2.1)

omit hG in
theorem IsQ.zero {v : ι → K} (hv : hf h G v v = 0) : IsQ h G v 0 0 :=
  ⟨hv, hf_zero_right h G v, by simp [hf_zero_left]⟩

theorem Tsu_zero {v : ι → K} (hv : hf h G v v = 0) : Tsu h G hG (IsQ.zero h G hv) = 1 :=
  smat_injective h G (eM_zero h G v)

omit hG in
theorem IsQ.central {v : ι → K} (hv : hf h G v v = 0) {d : K} (hd : d + h.bar d = 0) :
    IsQ h G v 0 d :=
  ⟨hv, hf_zero_right h G v, by rw [hf_zero_left]; simpa using hd⟩

omit hG in
theorem IsQ.addCentral {v u : ι → K} {c d : K} (hq : IsQ h G v u c) (hd : d + h.bar d = 0) :
    IsQ h G v u (c + d) := by
  obtain ⟨hv, hu, hc⟩ := hq
  refine ⟨hv, hu, ?_⟩
  rw [map_add]
  linear_combination hc + hd

theorem Tsu_mul_central {v u : ι → K} {c d : K} (hq : IsQ h G v u c) (hd : d + h.bar d = 0) :
    Tsu h G hG hq * Tsu h G hG (IsQ.central h G hq.1 hd) =
      Tsu h G hG (hq.addCentral h G hd) := by
  rw [Tsu_mul]
  refine Tsu_congr h G hG _ _ (add_zero u) ?_
  rw [hf_zero_right]; ring

theorem central_mul_Tsu {v u : ι → K} {c d : K} (hq : IsQ h G v u c) (hd : d + h.bar d = 0) :
    Tsu h G hG (IsQ.central h G hq.1 hd) * Tsu h G hG hq =
      Tsu h G hG (hq.addCentral h G hd) := by
  rw [Tsu_mul]
  refine Tsu_congr h G hG _ _ (zero_add u) ?_
  rw [hf_zero_left]; ring

omit hG in
theorem smat_pow (g : ↥(gramSU h G)) (k : ℕ) : smat h G (g ^ k) = smat h G g ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, smat_mul, ih, pow_succ]

theorem eM_pow {v u : ι → K} {c : K} (hq : IsQ h G v u c) (k : ℕ) :
    eM h G v u c ^ k =
      eM h G v ((k : K) • u) ((k : K) * c - (k.choose 2 : K) * hf h G u u) := by
  induction k with
  | zero =>
    rw [pow_zero, ← eM_zero h G v]
    exact eM_congr h G (by simp) (by simp)
  | succ k ih =>
    rw [pow_succ, ih, eM_mul h G hG hq.1 (by rw [hf_smul_right, hq.2.1, mul_zero]) hq.2.1]
    refine eM_congr h G (by rw [Nat.cast_succ, add_smul, one_smul]) ?_
    rw [hf_smul_left, map_natCast, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    ring

theorem Tsu_pow_char [hp : Fact p.Prime] (hp2 : p ≠ 2) {v u : ι → K} {c : K}
    (hq : IsQ h G v u c) : Tsu h G hG hq ^ p = 1 := by
  have hK : CharP K p := h.charP
  have hc2 : (p.choose 2 : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K p]
    exact hp.out.dvd_choose_self (by norm_num) (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
  refine smat_injective h G ?_
  rw [smat_pow, smat_Tsu, eM_pow h G hG hq, smat_one, ← eM_zero h G v]
  exact eM_congr h G (by simp [CharP.cast_eq_zero]) (by simp [CharP.cast_eq_zero, hc2])

@[expose] noncomputable def cc (u : ι → K) : K := -(2⁻¹ * hf h G u u)

theorem IsQ.can (h2 : (2 : K) ≠ 0) {v u : ι → K} (hv : hf h G v v = 0) (hu : hf h G v u = 0) :
    IsQ h G v u (cc h G u) := by
  refine ⟨hv, hu, ?_⟩
  have hb : h.bar (cc h G u) = cc h G u := by
    rw [cc, map_neg, map_mul, hf_self_bar h G hG, map_inv₀, map_ofNat]
  rw [hb]
  unfold cc
  have := mul_inv_cancel₀ h2
  linear_combination (-hf h G u u) * this

@[expose] noncomputable def Tcan (h2 : (2 : K) ≠ 0) {v : ι → K} (hv : hf h G v v = 0)
    {u : ι → K} (hu : hf h G v u = 0) : ↥(gramSU h G) :=
  Tsu h G hG (IsQ.can h G hG h2 hv hu)

@[expose] noncomputable def Zel {v : ι → K} (hv : hf h G v v = 0) {d : K}
    (hd : d + h.bar d = 0) : ↥(gramSU h G) :=
  Tsu h G hG (IsQ.central h G hv hd)

@[expose] noncomputable def Psi (u u' : ι → K) : K := hf h G u' u - hf h G u u'

theorem Psi_trace (u u' : ι → K) : Psi h G u u' + h.bar (Psi h G u u') = 0 := by
  rw [Psi, map_sub, map_hf h G hG, map_hf h G hG]; ring

theorem Tcan_comm (h2 : (2 : K) ≠ 0) {v : ι → K} (hv : hf h G v v = 0) {a b : ι → K}
    (ha : hf h G v a = 0) (hb : hf h G v b = 0) :
    Tcan h G hG h2 hv ha * Tcan h G hG h2 hv hb =
      Tcan h G hG h2 hv hb * Tcan h G hG h2 hv ha * Zel h G hG hv (Psi_trace h G hG a b) := by
  unfold Tcan Zel
  rw [Tsu_mul, Tsu_mul, Tsu_mul_central h G hG _ (Psi_trace h G hG a b)]
  refine Tsu_congr h G hG _ _ (add_comm a b) ?_
  simp only [cc, Psi]
  ring

theorem Tcan_comm_zero (h2 : (2 : K) ≠ 0) {v : ι → K} (hv : hf h G v v = 0) {a b : ι → K}
    (ha : hf h G v a = 0) (hb : hf h G v b = 0) (hab : Psi h G a b = 0) :
    Tcan h G hG h2 hv ha * Tcan h G hG h2 hv hb = Tcan h G hG h2 hv hb * Tcan h G hG h2 hv ha := by
  have hz : Zel h G hG hv (Psi_trace h G hG a b) = 1 := by
    unfold Zel
    rw [← Tsu_zero h G hG hv]
    exact Tsu_congr h G hG _ _ rfl hab
  rw [Tcan_comm h G hG h2 hv ha hb, hz, mul_one]

theorem Tcan_pow_char [hp : Fact p.Prime] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) {v : ι → K}
    (hv : hf h G v v = 0) {u : ι → K} (hu : hf h G v u = 0) :
    Tcan h G hG h2 hv hu ^ p = 1 :=
  Tsu_pow_char h G hG hp2 _

theorem Zel_pow_char [hp : Fact p.Prime] (hp2 : p ≠ 2) {v : ι → K} (hv : hf h G v v = 0) {d : K}
    (hd : d + h.bar d = 0) : Zel h G hG hv hd ^ p = 1 :=
  Tsu_pow_char h G hG hp2 _

theorem Zel_comm_Tcan (h2 : (2 : K) ≠ 0) {v : ι → K} (hv : hf h G v v = 0) {d : K}
    (hd : d + h.bar d = 0) {u : ι → K} (hu : hf h G v u = 0) :
    Tcan h G hG h2 hv hu * Zel h G hG hv hd = Zel h G hG hv hd * Tcan h G hG h2 hv hu := by
  unfold Tcan Zel
  rw [Tsu_mul_central h G hG (IsQ.can h G hG h2 hv hu) hd,
    central_mul_Tsu h G hG (IsQ.can h G hG h2 hv hu) hd]

theorem Zel_ne_one (hdet : G.det ≠ 0) {v : ι → K} (hv : hf h G v v = 0) (hv0 : v ≠ 0) {d : K}
    (hd : d + h.bar d = 0) (hd0 : d ≠ 0) : Zel h G hG hv hd ≠ 1 := by
  intro hz
  obtain ⟨w, hw⟩ : ∃ w, hf h G v w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (eq_zero_of_hf_eq_zero h G hdet (x := v) hcon)
  have e := congrArg (fun g => smat h G g *ᵥ w) hz
  simp only [Zel, Tsu_mulVec, smat_one, Matrix.one_mulVec, hf_zero_left, smul_zero, add_zero,
    zero_smul, sub_zero] at e
  have e' : (d * hf h G v w) • v = 0 := by simpa using e
  rcases smul_eq_zero.1 e' with h4 | h4
  · exact mul_ne_zero hd0 hw h4
  · exact hv0 h4

theorem heisCfg_Tcan [hp : Fact p.Prime] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hdet : G.det ≠ 0)
    {v : ι → K} (hv : hf h G v v = 0) (hv0 : v ≠ 0) {m : ℕ} (a b : Fin m → ι → K)
    (ha : ∀ i, hf h G v (a i) = 0) (hb : ∀ i, hf h G v (b i) = 0) {ι₀ : K}
    (hι : ι₀ + h.bar ι₀ = 0) (hι0 : ι₀ ≠ 0) (haa : ∀ i j, Psi h G (a i) (a j) = 0)
    (hbb : ∀ i j, i ≠ j → Psi h G (b i) (b j) = 0)
    (hab : ∀ i j, i ≠ j → Psi h G (a i) (b j) = 0) (hii : ∀ i, Psi h G (a i) (b i) = ι₀) :
    HeisCfg p m (fun i => Tcan h G hG h2 hv (ha i)) (fun i => Tcan h G hG h2 hv (hb i))
      (Zel h G hG hv hι) where
  xp i := Tcan_pow_char h G hG hp2 h2 hv (ha i)
  zp := Zel_pow_char h G hG hp2 hv hι
  zx i := Zel_comm_Tcan h G hG h2 hv hι (ha i)
  zy i := Zel_comm_Tcan h G hG h2 hv hι (hb i)
  yx i := by
    have hz : Zel h G hG hv (Psi_trace h G hG (a i) (b i)) = Zel h G hG hv hι := by
      unfold Zel; exact Tsu_congr h G hG _ _ rfl (hii i)
    have e := Tcan_comm h G hG h2 hv (ha i) (hb i)
    rw [hz] at e
    rw [mul_assoc, e]
    group
  xx i j := Tcan_comm_zero h G hG h2 hv (ha i) (ha j) (haa i j)
  yy i j hij := Tcan_comm_zero h G hG h2 hv (hb i) (hb j) (hbb i j hij)
  xy i j hij := Tcan_comm_zero h G hG h2 hv (ha i) (hb j) (hab i j hij)
  z1 := Zel_ne_one h G hG hdet hv hv0 hι hι0

theorem heisCfg_Tcan_proj [hp : Fact p.Prime] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    (hdet : G.det ≠ 0) (m' : ℕ) {v : ι → K} (hv : hf h G v v = 0) (hv0 : v ≠ 0) {m : ℕ}
    (a b : Fin m → ι → K) (ha : ∀ i, hf h G v (a i) = 0) (hb : ∀ i, hf h G v (b i) = 0)
    {ι₀ : K} (hι : ι₀ + h.bar ι₀ = 0) (hι0 : ι₀ ≠ 0) (haa : ∀ i j, Psi h G (a i) (a j) = 0)
    (hbb : ∀ i j, i ≠ j → Psi h G (b i) (b j) = 0)
    (hab : ∀ i j, i ≠ j → Psi h G (a i) (b j) = 0) (hii : ∀ i, Psi h G (a i) (b i) = ι₀) :
    HeisCfg p m
      (fun i => (QuotientGroup.mk (Tcan h G hG h2 hv (ha i)) :
        ↥(gramSU h G) ⧸ normOneScalars h (gramSU h G) m'))
      (fun i => (QuotientGroup.mk (Tcan h G hG h2 hv (hb i)) :
        ↥(gramSU h G) ⧸ normOneScalars h (gramSU h G) m'))
      (QuotientGroup.mk (Zel h G hG hv hι)) := by
  have hH := heisCfg_Tcan h G hG hp2 h2 hdet hv hv0 a b ha hb hι hι0 haa hbb hab hii
  have hfix : smat h G (Zel h G hG hv hι) *ᵥ v = v := by
    unfold Zel
    rw [Tsu_mulVec]
    simp [hv, hf_zero_left]
  exact hH.map (QuotientGroup.mk' (normOneScalars h (gramSU h G) m'))
    (mk_ne_one_of_fixed_su h G _ hH.z1 hv0 hfix)

end Group

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
