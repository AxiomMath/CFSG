module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3L2Centralizer
public import CFSG.ClassicalGroups.UnitaryFlag.SU3AutLineStabilizer
import CFSG.ClassicalGroups.UnitaryFlag.SU3L2AutInv
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

variable {m : ℕ} {K : Type} [Field K]

theorem field_part_fixes_bar_fixed (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {B : unitaryIsom3 h} {δ : K ≃+* K}
    (hαL : ∀ x ∈ L, (suConj h B * suField h δ) x = x)
    {t : K} (ht : h.bar t = t) : δ t = t := by
  obtain ⟨k, hkL, hktrace⟩ := exists_mem_trace_eq h hv hL ht
  have hαk : (suConj h B * suField h δ) k = k := hαL k hkL
  have hBinvB : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmat : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map δ) *
        ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 := congrArg (fun x : unitarySU 2 m K 3 =>
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hαk
    rw [coe_suConj_mul_suField_apply] at h1
    simpa [Units.val_mul, coe_glAut] using h1
  have htr : Matrix.trace (((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map δ) =
      Matrix.trace ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h2 := congrArg Matrix.trace hmat
    rw [Matrix.trace_mul_comm (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map δ))
      ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)] at h2
    rw [← mul_assoc, hBinvB, one_mul] at h2
    exact h2
  have hmap : Matrix.trace (((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map δ) =
      δ (Matrix.trace ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    simp [Matrix.trace, map_sum]
  rw [hmap, hktrace, map_add, map_one] at htr
  exact add_left_cancel htr

theorem eq_one_or_eq_barEquiv_of_forall_bar_fixed (h : UnitaryFieldData 2 m K) {δ : K ≃+* K}
    (hδ : ∀ t : K, h.bar t = t → δ t = t) : δ = 1 ∨ δ = h.barEquiv := by
  have : CharP K 2 := h.charP
  have hsub : ∀ y z : K, y - z = y + z := fun y z => CharTwo.sub_eq_add y z
  have hroot : ∀ x : K, δ x = x ∨ δ x = h.bar x := by
    intro x
    have h1 : δ (x + h.bar x) = x + h.bar x :=
      hδ _ (by rw [map_add, UnitaryFieldData.bar_bar, add_comm])
    have h2 : δ (x * h.bar x) = x * h.bar x :=
      hδ _ (by rw [map_mul, UnitaryFieldData.bar_bar, mul_comm])
    have h0 : x ^ 2 + (x + h.bar x) * x + x * h.bar x = 0 := by
      have e : x ^ 2 + (x + h.bar x) * x + x * h.bar x =
          (x ^ 2 + x ^ 2) + (x * h.bar x + x * h.bar x) := by ring
      rw [e, CharTwo.add_self_eq_zero (x ^ 2),
        CharTwo.add_self_eq_zero (x * h.bar x), zero_add]
    have h0' := congrArg δ h0
    simp only [map_add, map_mul, map_pow, map_zero, h1, h2] at h0'
    have h3 : (δ x - x) * (δ x - h.bar x) = 0 := by
      rw [hsub (δ x) x, hsub (δ x) (h.bar x)]
      have e : (δ x + x) * (δ x + h.bar x) =
          (δ x) ^ 2 + (x + h.bar x) * δ x + x * h.bar x := by ring
      rw [e]
      exact h0'
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact Or.inl (sub_eq_zero.mp h4)
    · exact Or.inr (sub_eq_zero.mp h4)
  by_cases h1 : ∀ x : K, δ x = x
  · exact Or.inl (RingEquiv.ext h1)
  · obtain ⟨x, hx⟩ := not_forall.mp h1
    by_cases h2 : ∀ y : K, δ y = h.bar y
    · exact Or.inr (RingEquiv.ext fun y => by rw [h2 y, UnitaryFieldData.barEquiv_apply])
    · obtain ⟨y, hy⟩ := not_forall.mp h2
      have hxS : δ x = h.bar x := (hroot x).resolve_left hx
      have hyS : δ y = y := (hroot y).resolve_right hy
      rcases hroot (x + y) with hxy | hxy
      · rw [map_add, hxS, hyS] at hxy
        exact absurd (hxS.trans (add_right_cancel hxy)) hx
      · rw [map_add, hxS, hyS, map_add] at hxy
        exact absurd (hyS.trans (add_left_cancel hxy)) hy

theorem coe_mul_comm_of_suConj_eq_self (h : UnitaryFieldData 2 m K)
    {B : unitaryIsom3 h} {t : unitarySU 2 m K 3} (htB : suConj h B t = t) :
    ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : (B : GL (Fin 3) K) * (t : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹ =
      (t : GL (Fin 3) K) := by
    simpa [coe_suConj] using congrArg (fun x : unitarySU 2 m K 3 =>
      ((x : GL (Fin 3) K))) htB
  have h2 := congrArg (fun x : GL (Fin 3) K => x * (B : GL (Fin 3) K)) h1
  have h3 : (B : GL (Fin 3) K) * (t : GL (Fin 3) K) =
      (t : GL (Fin 3) K) * (B : GL (Fin 3) K) := by simpa [mul_assoc] using h2
  simpa only [Units.val_mul] using congrArg (fun x : GL (Fin 3) K =>
    (x : Matrix (Fin 3) (Fin 3) K)) h3

theorem exists_eq_smul_of_suConj_eq_self_of_hermTransvection (h : UnitaryFieldData 2 m K)
    {B : unitaryIsom3 h} {a x : Fin 3 → K} {t : unitarySU 2 m K 3}
    (ht : Matrix.mulVecLin ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      hermTransvection (stdHermForm h 3) a 1)
    (hx : stdHermForm h 3 a x = 1) (htB : suConj h B t = t) :
    ∃ c : K, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a = c • a := by
  have : CharP K 2 := h.charP
  let Bm : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  let tm : Matrix (Fin 3) (Fin 3) K := ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hmatM : Bm * tm = tm * Bm := by
    simpa [Bm, tm] using coe_mul_comm_of_suConj_eq_self h htB
  have htx : tm *ᵥ x = x + a := by
    have h1 : tm *ᵥ x = hermTransvection (stdHermForm h 3) a 1 x := by
      rw [← Matrix.mulVecLin_apply, show Matrix.mulVecLin tm = _ from ht]
    rw [h1, hermTransvection_apply, one_mul, hx, one_smul]
  have hstep : tm *ᵥ (Bm *ᵥ x) = Bm *ᵥ (tm *ᵥ x) := by
    calc tm *ᵥ (Bm *ᵥ x) = (tm * Bm) *ᵥ x := Matrix.mulVec_mulVec x _ _
      _ = (Bm * tm) *ᵥ x := by rw [hmatM]
      _ = Bm *ᵥ (tm *ᵥ x) := (Matrix.mulVec_mulVec x _ _).symm
  have hsub_a : subOne t (Bm *ᵥ x) = (stdHermForm h 3 a (Bm *ᵥ x)) • a := by
    rw [subOne_apply h, CharTwo.sub_eq_add, unitarySU_smul_def h, Matrix.mulVecLin_apply,
      ← Matrix.mulVecLin_apply, show Matrix.mulVecLin tm = _ from ht, hermTransvection_apply,
      one_mul]
    rw [add_assoc, add_comm ((stdHermForm h 3 a (Bm *ᵥ x)) • a) (Bm *ᵥ x),
      ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hBa : Bm *ᵥ a = subOne t (Bm *ᵥ x) := by
    have ha_eq : a = tm *ᵥ x + x := by
      rw [htx, add_assoc, add_comm a x, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [ha_eq, Matrix.mulVec_add, ← hstep, subOne_apply h, CharTwo.sub_eq_add,
      unitarySU_smul_def h, Matrix.mulVecLin_apply]
  exact ⟨_, hBa.trans hsub_a⟩


theorem exists_smul_mulVec_of_forall_mem_suConj (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {B : unitaryIsom3 h} (hBL : ∀ x ∈ L, suConj h B x = x) :
    ∃ c : K, c ≠ 0 ∧ ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v := by
  have : CharP K 2 := h.charP
  have hvne : v ≠ 0 := fun h0 => hv (by rw [h0]; simp)
  obtain ⟨c, hcne, hc⟩ :=
    exists_smul_of_suConj_mul_suField_fixes_torus (h := h) (T := L) (v := v) hvne
      (fun b hb => (hL b).mp hb)
      (fun w hw => exists_eq_smul_of_forall_mem_mulVec_eq h hv hL hw)
      (B := B) (δ := 1) (fun b hb => by simpa using hBL b hb)
  exact ⟨c, hcne, by simpa using hc⟩

theorem exists_eigenvalue_of_forall_mem_suConj (h : UnitaryFieldData 2 m K)
    {v e f : Fin 3 → K}
    (hee : stdHermForm h 3 e e = 0) (hff : stdHermForm h 3 f f = 0)
    (hef : stdHermForm h 3 e f = 1) (hev : stdHermForm h 3 e v = 0)
    (hfv : stdHermForm h 3 f v = 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {B : unitaryIsom3 h} (hBL : ∀ x ∈ L, suConj h B x = x) :
    ∃ lam : K, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ e = lam • e ∧
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f = lam • f := by
  have : CharP K 2 := h.charP
  have h1 : (1 : K) ∈ h.traceZero := mem_traceZero_of_bar_eq h (map_one h.bar)
  obtain ⟨ge, hge⟩ := exists_mem_unitarySU_hermTransvection h hee h1
  obtain ⟨gf, hgf⟩ := exists_mem_unitarySU_hermTransvection h hff h1
  have hgeL : ge ∈ L := by
    refine (hL ge).mpr ?_
    rw [← Matrix.mulVecLin_apply, hge, hermTransvection_apply, one_mul, hev]
    simp
  have hgfL : gf ∈ L := by
    refine (hL gf).mpr ?_
    rw [← Matrix.mulVecLin_apply, hgf, hermTransvection_apply, one_mul, hfv]
    simp
  obtain ⟨lam, hBe⟩ := exists_eq_smul_of_suConj_eq_self_of_hermTransvection h
    (a := e) (x := f) (t := ge) hge hef (hBL ge hgeL)
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    rw [hef, map_one] at h'
    exact h'.symm
  obtain ⟨lam', hBf⟩ := exists_eq_smul_of_suConj_eq_self_of_hermTransvection h
    (a := f) (x := e) (t := gf) hgf hfe (hBL gf hgfL)
  have hge_f : ((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f = f + e := by
    rw [← Matrix.mulVecLin_apply, hge, hermTransvection_apply, one_mul, hef]
    simp
  have hcommGe := coe_mul_comm_of_suConj_eq_self h (hBL ge hgeL)
  have h1' : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f) =
      ((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f) := by
    calc ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f)
        = (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ f :=
          Matrix.mulVec_mulVec f _ _
      _ = (((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ f := by rw [hcommGe]
      _ = ((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f) :=
          (Matrix.mulVec_mulVec f _ _).symm
  have hcompare : lam • e = lam' • e := by
    have h := h1'
    rw [hge_f, Matrix.mulVec_add, hBe, hBf, Matrix.mulVec_smul, hge_f, smul_add] at h
    exact add_left_cancel h
  have he0 : e ≠ 0 := by intro h0; rw [h0] at hef; simp at hef
  have hlam : lam = lam' := by
    by_contra hne
    apply he0
    funext i
    have h := congrArg (fun z : Fin 3 → K => z i) hcompare
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have h' : (lam - lam') * e i = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  exact ⟨lam, hBe, by rw [hBf, hlam]⟩

theorem exists_scalar_pow_of_suConj_pow_eq_one (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {B : unitaryIsom3 h} {k : ℕ} (hk : suConj h B ^ 2 ^ k = 1) :
    ∃ c' : Kˣ, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 2 ^ k =
      Matrix.scalar (Fin 3) (c' : K) := by
  have hq : 2 < 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  have hBpow : suConj h (B ^ 2 ^ k) = 1 := by rw [map_pow, hk]
  have hpsuPow : psuConj h (B ^ 2 ^ k) = 1 := by
    have h := congrArg (suDescend h hq) hBpow
    rwa [suDescend_suConj, map_one] at h
  obtain ⟨-, c', -, hc'⟩ :=
    eq_one_of_psuConj_mul_psuField_eq_one (B ^ 2 ^ k) 1 (by rw [map_one, mul_one, hpsuPow])
  refine ⟨c', ?_⟩
  have hc'mat : (((B ^ 2 ^ k : unitaryIsom3 h) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (c' : K) := by
    rw [hc', GeneralLinearGroup.coe_scalar]
  simpa [Subgroup.coe_pow] using hc'mat

theorem eq_eigenvalue_of_pow_eq_scalar (h : UnitaryFieldData 2 m K)
    {B : unitaryIsom3 h} {e v : Fin 3 → K} {lam c c' : K} (he : e ≠ 0) (hv : v ≠ 0)
    {k : ℕ} (hBe : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ e = lam • e)
    (hBv : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v)
    (hpow : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 2 ^ k =
      Matrix.scalar (Fin 3) c') : lam = c := by
  have : CharP K 2 := h.charP
  let Bm : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hBe' : Bm *ᵥ e = lam • e := hBe
  have hBv' : Bm *ᵥ v = c • v := hBv
  have hpow' : Bm ^ 2 ^ k = Matrix.scalar (Fin 3) c' := hpow
  have hpow_e : ∀ r : ℕ, (Bm ^ r) *ᵥ e = (lam ^ r) • e := by
    intro r
    induction r with
    | zero => rw [pow_zero, Matrix.one_mulVec, pow_zero, one_smul]
    | succ r ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hBe', Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have hpow_v : ∀ r : ℕ, (Bm ^ r) *ᵥ v = (c ^ r) • v := by
    intro r
    induction r with
    | zero => rw [pow_zero, Matrix.one_mulVec, pow_zero, one_smul]
    | succ r ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hBv', Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have hpe : (Bm ^ 2 ^ k) *ᵥ e = c' • e := by
    rw [hpow', Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
  have hpv : (Bm ^ 2 ^ k) *ᵥ v = c' • v := by
    rw [hpow', Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
  have hlam_pow : lam ^ 2 ^ k = c' := by
    have h1 : (lam ^ 2 ^ k) • e = c' • e := by rw [← hpow_e (2 ^ k), hpe]
    by_contra hne
    apply he
    funext i
    have h := congrArg (fun z : Fin 3 → K => z i) h1
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have h' : (lam ^ 2 ^ k - c') * e i = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hc_pow : c ^ 2 ^ k = c' := by
    have h1 : (c ^ 2 ^ k) • v = c' • v := by rw [← hpow_v (2 ^ k), hpv]
    by_contra hne
    apply hv
    funext i
    have h := congrArg (fun z : Fin 3 → K => z i) h1
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have h' : (c ^ 2 ^ k - c') * v i = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hinj : Function.Injective (fun x : K => x ^ 2 ^ k) := by
    intro x y hxy
    exact iterateFrobenius_inj K 2 k (by simpa only [iterateFrobenius_def] using hxy)
  exact hinj (hlam_pow.trans hc_pow.symm)

theorem eq_scalar_of_mulVec_eq_smul_of_hyperbolicPair (h : UnitaryFieldData 2 m K)
    {v e f : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0)
    (hee : stdHermForm h 3 e e = 0) (hff : stdHermForm h 3 f f = 0)
    (hef : stdHermForm h 3 e f = 1) (hev : stdHermForm h 3 e v = 0)
    (hfv : stdHermForm h 3 f v = 0) {B : unitaryIsom3 h} {c : K}
    (hBe : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ e = c • e)
    (hBf : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f = c • f)
    (hBv : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v) :
    ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  let Bm : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hBe' : Bm *ᵥ e = c • e := hBe
  have hBf' : Bm *ᵥ f = c • f := hBf
  have hBv' : Bm *ᵥ v = c • v := hBv
  have hspan := span_range_hyperbolic_eq_top h hv hee hff hef hev hfv
  have hlin : Matrix.toLin' Bm = c • LinearMap.id := by
    apply LinearMap.ext_on_range (v := ![e, f, v]) hspan
    intro i
    fin_cases i
    · simpa [Matrix.toLin'_apply] using hBe'
    · simpa [Matrix.toLin'_apply] using hBf'
    · simpa [Matrix.toLin'_apply] using hBv'
  have hscalar : Matrix.toLin' (Matrix.scalar (Fin 3) c) = c • LinearMap.id := by
    rw [← LinearMap.toMatrix'_algebraMap (n := Fin 3) c, Matrix.toLin'_toMatrix',
      Module.algebraMap_end_eq_smul_id]
  exact Matrix.toLin'.injective (hlin.trans hscalar.symm)

theorem suConj_eq_one_of_forall_mem_of_pow_eq_one (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {B : unitaryIsom3 h} (hBL : ∀ x ∈ L, suConj h B x = x) {k : ℕ}
    (hk : suConj h B ^ 2 ^ k = 1) : suConj h B = 1 := by
  have : CharP K 2 := h.charP
  have hq : 2 < 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  let Bm : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  obtain ⟨e, f, hee, hff, hef, hev, hfv⟩ := exists_hyperbolic_pair_of_nonisotropic h hv
  obtain ⟨c0, hc0ne, hcv0⟩ := exists_smul_mulVec_of_forall_mem_suConj h hv hL hBL
  obtain ⟨lam, hBe0, hBf0⟩ :=
    exists_eigenvalue_of_forall_mem_suConj h hee hff hef hev hfv hL hBL
  have hcv : Bm *ᵥ v = c0 • v := hcv0
  have hBe : Bm *ᵥ e = lam • e := hBe0
  have hBf : Bm *ᵥ f = lam • f := hBf0
  obtain ⟨c', hpow0⟩ := exists_scalar_pow_of_suConj_pow_eq_one h hm hk
  have hpow : Bm ^ 2 ^ k = Matrix.scalar (Fin 3) (c' : K) := hpow0
  have he0 : e ≠ 0 := by intro h0; rw [h0] at hef; simp at hef
  have hvne : v ≠ 0 := fun h0 => hv (by rw [h0]; simp)
  have hlam : lam = c0 := eq_eigenvalue_of_pow_eq_scalar h he0 hvne hBe hcv hpow
  have hBe' : Bm *ᵥ e = c0 • e := by rw [hBe, hlam]
  have hBf' : Bm *ᵥ f = c0 • f := by rw [hBf, hlam]
  have hBm_scalar : Bm = Matrix.scalar (Fin 3) c0 :=
    eq_scalar_of_mulVec_eq_smul_of_hyperbolicPair h hv hee hff hef hev hfv hBe' hBf' hcv
  have hBGL : (B : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c0 hc0ne) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    simpa [Bm] using hBm_scalar
  have hpsu : psuConj h B = 1 := psuConj_eq_one_of_coe_eq_scalar hBGL
  apply eq_of_suDescend_eq h hq
  rw [suDescend_suConj, hpsu, map_one]

theorem exists_suConj_eq_inv_mul_mul_suField (h : UnitaryFieldData 2 m K)
    (hq : 2 < 2 ^ m) (B B' : unitaryIsom3 h) (δ : K ≃+* K) :
    ∃ B'' : unitaryIsom3 h,
      (suConj h B * suField h δ)⁻¹ * (suConj h B' * suField h δ) = suConj h B'' := by
  refine ⟨⟨glAut δ⁻¹ (B⁻¹ * B'),
    glAut_mem_unitaryIsom3 δ⁻¹ (mul_mem (inv_mem B.2) B'.2)⟩, ?_⟩
  apply eq_of_suDescend_eq h hq
  conv_rhs => rw [suDescend_suConj]
  conv_lhs => simp only [map_mul, map_inv, suDescend_suConj, suDescend_suField]
  have hF : (psuField h δ)⁻¹ = psuField h δ⁻¹ := by rw [← map_inv]
  have hXY : (psuConj h B)⁻¹ * psuConj h B' = psuConj h (B⁻¹ * B') := by
    rw [← map_inv, ← map_mul]
  rw [_root_.mul_inv_rev]
  calc (psuField h δ)⁻¹ * (psuConj h B)⁻¹ * (psuConj h B' * psuField h δ)
      = (psuField h δ)⁻¹ * ((psuConj h B)⁻¹ * psuConj h B') * psuField h δ := by group
    _ = psuField h δ⁻¹ * psuConj h (B⁻¹ * B') * psuField h δ := by rw [hF, hXY]
    _ = psuConj h ⟨glAut δ⁻¹ (B⁻¹ * B'),
          glAut_mem_unitaryIsom3 δ⁻¹ (mul_mem (inv_mem B.2) B'.2)⟩ := by
        have hδ' : psuField h δ = (psuField h δ⁻¹)⁻¹ := by rw [← hF, inv_inv]
        rw [hδ', psuField_mul_psuConj_mul_inv]
        rfl

theorem eq_one_or_exists_suConj_mul_suField_barEquiv_of_forall_mem (h : UnitaryFieldData 2 m K)
    (hm : 2 ≤ m) {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0)
    {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {A : Subgroup (MulAut (unitarySU 2 m K 3))} (hA : IsPGroup 2 A)
    (hAL : ∀ α ∈ A, ∀ x ∈ L, α x = x) {α : MulAut (unitarySU 2 m K 3)} (hαA : α ∈ A) :
    α = 1 ∨ ∃ B : unitaryIsom3 h, α = suConj h B * suField h h.barEquiv := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 < 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  obtain ⟨B, δ, hα⟩ := exists_suConj_mul_suField h hq α
  have hαL : ∀ x ∈ L, (suConj h B * suField h δ) x = x := by
    intro x hx
    rw [← hα]
    exact hAL α hαA x hx
  have hδbar : ∀ t : K, h.bar t = t → δ t = t :=
    fun t ht => field_part_fixes_bar_fixed h hv hL hαL ht
  rcases eq_one_or_eq_barEquiv_of_forall_bar_fixed h hδbar with hδ1 | hδbar
  · left
    have hαpow : ∃ k : ℕ, α ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨α, hαA⟩
      refine ⟨k, ?_⟩
      have hord : orderOf α = 2 ^ k := by
        rw [Subgroup.orderOf_coe (⟨α, hαA⟩ : A), hk]
      rw [← hord]
      exact pow_orderOf_eq_one α
    obtain ⟨k, hk⟩ := hαpow
    have hBL : ∀ x ∈ L, suConj h B x = x := by
      intro x hx
      have := hαL x hx
      simpa [hδ1, map_one, mul_one] using this
    have hk' : suConj h B ^ 2 ^ k = 1 := by
      simpa [hα, hδ1, map_one, mul_one] using hk
    rw [hα, hδ1, map_one, mul_one]
    exact suConj_eq_one_of_forall_mem_of_pow_eq_one h hm hv hL hBL hk'
  · exact Or.inr ⟨B, by rw [hα, hδbar]⟩

theorem eq_of_ne_one_of_isPGroup (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {A : Subgroup (MulAut (unitarySU 2 m K 3))} (hA : IsPGroup 2 A)
    (hAL : ∀ α ∈ A, ∀ x ∈ L, α x = x) {α β : MulAut (unitarySU 2 m K 3)}
    (hαA : α ∈ A) (hβA : β ∈ A) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) : α = β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 < 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  obtain ⟨Bα, hαbar⟩ :=
    (eq_one_or_exists_suConj_mul_suField_barEquiv_of_forall_mem h hm hv hL hA hAL
      hαA).resolve_left hα1
  obtain ⟨Bβ, hβbar⟩ :=
    (eq_one_or_exists_suConj_mul_suField_barEquiv_of_forall_mem h hm hv hL hA hAL
      hβA).resolve_left hβ1
  obtain ⟨B'', hB''⟩ :=
    exists_suConj_eq_inv_mul_mul_suField h hq Bα Bβ h.barEquiv
  have hmemA : α⁻¹ * β ∈ A := A.mul_mem (A.inv_mem hαA) hβA
  have hαinvx : ∀ x ∈ L, α⁻¹ x = x := by
    intro x hx
    have h := MulAut.inv_apply_self (unitarySU 2 m K 3) α x
    rwa [hAL α hαA x hx] at h
  have hmul : α⁻¹ * β = suConj h B'' := by
    rw [hαbar, hβbar]
    exact hB''
  have hfix : ∀ x ∈ L, suConj h B'' x = x := by
    intro x hx
    have h1 : (α⁻¹ * β) x = x := by
      rw [MulAut.mul_apply]
      rw [hAL β hβA x hx]
      exact hαinvx x hx
    rwa [hmul] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨α⁻¹ * β, hmemA⟩
  have hk' : suConj h B'' ^ 2 ^ k = 1 := by
    have hord : orderOf (α⁻¹ * β) = 2 ^ k := by
      rw [Subgroup.orderOf_coe (⟨α⁻¹ * β, hmemA⟩ : A), hk]
    have hpow : (α⁻¹ * β) ^ 2 ^ k = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one (α⁻¹ * β)
    rwa [← hmul]
  have hone := suConj_eq_one_of_forall_mem_of_pow_eq_one h hm hv hL hfix hk'
  have hαβ : α⁻¹ * β = 1 := by rw [hmul, hone]
  exact eq_of_inv_mul_eq_one hαβ

theorem card_le_two_and_apply_eq_inv_of_forall_mem (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {μ : K} (hμ : μ ^ (2 ^ m + 1) = 1) {g : unitarySU 2 m K 3}
    (hgv : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = (μ ^ 2)⁻¹ • v)
    (hgw : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = μ • w)
    {A : Subgroup (MulAut (unitarySU 2 m K 3))} (hA : IsPGroup 2 A)
    (hAL : ∀ α ∈ A, ∀ x ∈ L, α x = x) :
    Nat.card A ≤ 2 ∧ ∀ α ∈ A, α ≠ 1 → α g = g⁻¹ := by
  classical
  have hunique : ∀ α ∈ A, ∀ β ∈ A, α ≠ 1 → β ≠ 1 → α = β := by
    intro α hαA β hβA hα1 hβ1
    exact eq_of_ne_one_of_isPGroup h hm hv hL hA hAL hαA hβA hα1 hβ1
  have hcard : Nat.card A ≤ 2 := by
    let f : A → Bool := fun x => if (x : MulAut (unitarySU 2 m K 3)) = 1 then true else false
    have hf : Function.Injective f := by
      intro x y hxy
      change (if (x : MulAut (unitarySU 2 m K 3)) = 1 then true else false) =
        (if (y : MulAut (unitarySU 2 m K 3)) = 1 then true else false) at hxy
      by_cases hx : (x : MulAut (unitarySU 2 m K 3)) = 1
      · have hy : (y : MulAut (unitarySU 2 m K 3)) = 1 := by
          by_contra hy
          simp [hx, hy] at hxy
        exact Subtype.ext (hx.trans hy.symm)
      · have hy : (y : MulAut (unitarySU 2 m K 3)) ≠ 1 := by
          intro hy
          simp [hx, hy] at hxy
        exact Subtype.ext (hunique x.val x.2 y.val y.2 hx hy)
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  refine ⟨hcard, ?_⟩
  intro α hαA hα1
  obtain ⟨B, hαbar⟩ :=
    (eq_one_or_exists_suConj_mul_suField_barEquiv_of_forall_mem h hm hv hL hA hAL
      hαA).resolve_left hα1
  have hBL : ∀ x ∈ L, (suConj h B * suField h h.barEquiv) x = x := by
    intro x hx
    rw [← hαbar]
    exact hAL α hαA x hx
  rw [hαbar]
  exact suConj_mul_suField_barEquiv_apply_eq_inv h hv hL hBL hμ hgv hgw

end CFSG.ClassicalGroups.UnitaryFlag

end
