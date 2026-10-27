module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Native
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Bfs
public import CFSG.Sporadic.He.FpSpec
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
public import CFSG.Certificates.Kernel.Orders.HN.Checks.K
public import CFSG.Certificates.Kernel.Spor.VOrbSound
public import CFSG.Sporadic.HN.F5PackedSpec
public import CFSG.Sporadic.Th.CertificateChunks
public import Certificates.Data.Kernel.SporSch.HNXPrim

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native CFSG.KS.Ord
open Finset
open scoped Matrix

theorem dot_lt (d : Nat) (r v : Array Nat) : dot 5 d r v < 5 := Nat.mod_lt _ (by norm_num)

theorem nat_eq_of_cast {a b : Nat} (ha : a < 5) (hb : b < 5) (h : (a : ZMod 5) = (b : ZMod 5)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

theorem mulM_eq_idM {d : Nat} {X Y : Array (Array Nat)} (h : toMat 5 d (mulM 5 d X Y) = 1) :
    mulM 5 d X Y = idM d := by
  have hij : ∀ i j : Fin d, dot 5 d X[i.val]! (col d Y j.val) = if i.val = j.val then 1 else 0 := by
    intro i j
    have e := congrFun (congrFun h i) j
    rw [toMat_apply, Matrix.one_apply] at e
    unfold mulM at e
    rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt] at e
    refine nat_eq_of_cast (dot_lt _ _ _) (by split <;> omega) ?_
    rw [e]
    by_cases hh : i = j
    · simp [hh]
    · have : i.val ≠ j.val := fun e => hh (Fin.ext e)
      simp [hh, this]
  unfold mulM idM
  congr 1
  funext i
  congr 1
  funext j
  exact hij i j

theorem toMat_rows {R : Array (Array Nat)} {W : Nat}
    (hR : ∀ i < 133, ∀ j < 133, (R[i]!)[j]! = ent13 W i j) :
    toMat 5 133 R = ordMat 5 133 13 1729 W := by
  ext i j
  rw [toMat_apply, hR i i.isLt j j.isLt]
  rfl

theorem powM_idM {R : Array (Array Nat)} {W : Nat}
    (hR : ∀ i < 133, ∀ j < 133, (R[i]!)[j]! = ent13 W i j) {e : Nat}
    (he : ordMat 5 133 13 1729 W ^ (e + 1) = 1) : (powM 5 133 R (e + 1) == idM 133) = true := by
  have h : powM 5 133 R (e + 1) = idM 133 := by
    change mulM 5 133 (powM 5 133 R e) R = idM 133
    apply mulM_eq_idM
    have := toMat_powM 5 133 R (e + 1)
    change toMat 5 133 (mulM 5 133 (powM 5 133 R e) R) = _ at this
    rw [this, toMat_rows hR, he]
  rw [h]
  exact beq_self_eq_true _

theorem canon_of_validHN {W : Nat} (h : validHN W = true) : Canon 5 133 13 W :=
  validM_canon CFSG.KD.OrdHN.consts h

theorem mm_sound {a b : Nat} (ha : Canon 5 133 13 a) (hb : Canon 5 133 13 b) :
    Canon 5 133 13 (CFSG.KC.LL.HN.mm a b) ∧
      ordMat 5 133 13 1729 (CFSG.KC.LL.HN.mm a b) =
        ordMat 5 133 13 1729 a * ordMat 5 133 13 1729 b :=
  mulR_sound CFSG.KD.OrdHN.consts ha hb

theorem one_ord : ordMat 5 133 13 1729 CFSG.KD.OrdHN.ONE = 1 := (one_sound CFSG.KD.OrdHN.consts).2

theorem sq_one {W : Nat} (hv : validHN W = true)
    (h : Nat.beq (CFSG.KC.LL.HN.mm W W) CFSG.KD.OrdHN.ONE = true) :
    ordMat 5 133 13 1729 W ^ (1 + 1) = 1 := by
  have hc := canon_of_validHN hv
  rw [pow_two, ← (mm_sound hc hc).2, Nat.eq_of_beq_eq_true h, one_ord]

theorem cube_one {W : Nat} (hv : validHN W = true)
    (h : Nat.beq (CFSG.KC.LL.HN.mm (CFSG.KC.LL.HN.mm W W) W) CFSG.KD.OrdHN.ONE = true) :
    ordMat 5 133 13 1729 W ^ (2 + 1) = 1 := by
  have hc := canon_of_validHN hv
  have h2 := mm_sound hc hc
  rw [pow_succ, pow_two, ← h2.2, ← (mm_sound h2.1 hc).2, Nat.eq_of_beq_eq_true h, one_ord]

theorem matrixChecks_of {D : F5Data} {W1 W2 : Nat} (hd : D.d = 133)
    (hexp : D.expA = 2 ∧ D.expB = 3)
    (hrA : ∀ i < 133, ∀ j < 133, (D.rowsA[i]!)[j]! = ent13 W1 i j)
    (hrB : ∀ i < 133, ∀ j < 133, (D.rowsB[i]!)[j]! = ent13 W2 i j)
    (hA : ordMat 5 133 13 1729 W1 ^ (1 + 1) = 1) (hB : ordMat 5 133 13 1729 W2 ^ (2 + 1) = 1) :
    matrixChecks D = true := by
  unfold matrixChecks
  rw [hd, hexp.1, hexp.2]
  have e1 := powM_idM hrA hA
  have e2 := powM_idM hrB hB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨by norm_num, by norm_num⟩, by norm_num⟩, by norm_num⟩, e1⟩, e2⟩

theorem mat_comm {d : Nat} {A B : Matrix (Fin d) (Fin d) (ZMod 5)} (h : A * B = 1) : B * A = 1 :=
  mul_eq_one_comm.1 h

theorem basis_of {D : F5Data} {O : VOrbit} (hd : D.d = 133) (hQs : D.Q.size = 133)
    {X G : Nat → Nat → Nat}
    (hX : ∀ t < 133, ∀ i < 133, (bytesToNats O.keys[D.Q[t]!]!)[i]! = X t i)
    (hG5 : ∀ k < 133, ∀ l < 133, G k l < 5)
    (hXG : ∀ r < 133, ∀ l < 133, (∑ k ∈ range 133, X r k * G k l) % 5 = if r = l then 1 else 0) :
    basisCheck D O = true := by
  unfold basisCheck
  dsimp only
  rw [hd]
  generalize hM : colsMat 133 (D.Q.map fun q => bytesToNats O.keys[q]!) = M
  have hMe : ∀ i < 133, ∀ t < 133, (M[i]!)[t]! = X t i := by
    intro i hi t ht
    rw [← hM]
    unfold colsMat
    rw [getElem!_ofFn _ hi, getElem!_ofFn _ ht]
    rw [getElem!_pos (D.Q.map fun q => bytesToNats O.keys[q]!) t (by simp [hQs]; omega),
      Array.getElem_map, ← getElem!_pos D.Q t (by omega)]
    exact hX t ht i hi
  let XM : Matrix (Fin 133) (Fin 133) (ZMod 5) := Matrix.of fun r k => ((X r.val k.val : Nat) : ZMod 5)
  let GM : Matrix (Fin 133) (Fin 133) (ZMod 5) := Matrix.of fun k l => ((G k.val l.val : Nat) : ZMod 5)
  have hXGm : XM * GM = 1 := by
    ext r l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e := congrArg (fun n : Nat => (n : ZMod 5)) (hXG r.val r.isLt l.val l.isLt)
    simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul] at e
    rw [← Fin.sum_univ_eq_sum_range (fun k => ((X r.val k : Nat) : ZMod 5) * ((G k l.val : Nat) : ZMod 5))] at e
    simp only [XM, GM, Matrix.of_apply]
    rw [e]
    by_cases hrl : r = l
    · simp [hrl]
    · have : r.val ≠ l.val := fun e => hrl (Fin.ext e)
      simp [hrl, this]
  have hGX : GM * XM = 1 := mat_comm hXGm
  have hGXe : ∀ i < 133, ∀ j < 133, ∑ k ∈ range 133,
      ((X k i : Nat) : ZMod 5) * ((G j k : Nat) : ZMod 5) = if i = j then 1 else 0 := by
    intro i hi j hj
    have e := congrFun (congrFun hGX ⟨j, hj⟩) ⟨i, hi⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [XM, GM, Matrix.of_apply] at e
    rw [Fin.sum_univ_eq_sum_range (fun k => ((G j k : Nat) : ZMod 5) * ((X k i : Nat) : ZMod 5))] at e
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, e]
    by_cases hij : i = j
    · subst hij; simp
    · have h1 : (⟨j, hj⟩ : Fin 133) ≠ ⟨i, hi⟩ := fun e => hij (congrArg Fin.val e).symm
      simp [hij, h1]
  have hinv := LyM.invM_spec (p := 5) (d := 133) Nat.prime_five (X := M) (y := fun k j => G j k)
    (fun i hi j hj => hG5 j hj i hi) (fun i hi j hj => by
      rw [Finset.sum_congr rfl fun k hk => by rw [hMe i hi k (Finset.mem_range.1 hk)]]
      exact hGXe i hi j hj)
  rw [hinv]
  have h : mulM 5 133 M (Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j =>
      G j.val i.val) = idM 133 := by
    apply mulM_eq_idM
    rw [toMat_mulM]
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [toMat_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => (((M[i.val]!)[k]! : Nat) : ZMod 5) *
      (((Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j => G j.val i.val)[k]!)[j.val]! :
        ZMod 5))]
    have hs : ∑ k ∈ range 133, (((M[i.val]!)[k]! : Nat) : ZMod 5) *
        ((((Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j => G j.val i.val)[k]!)[j.val]! :
          Nat) : ZMod 5) = ∑ k ∈ range 133, ((X k i.val : Nat) : ZMod 5) * ((G j.val k : Nat) : ZMod 5) :=
      Finset.sum_congr rfl fun k hk => by
        rw [hMe i.val i.isLt k (Finset.mem_range.1 hk), getElem!_ofFn _ (Finset.mem_range.1 hk),
          getElem!_ofFn _ j.isLt]
    rw [hs, hGXe i.val i.isLt j.val j.isLt]
    by_cases hij : i = j
    · simp [hij]
    · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [hij, this]
  rw [h]
  exact beq_self_eq_true _

theorem bind_facts {T : Nat → Nat} {P : PackedOrbitData} (hP : hnxBindK T P = true) :
    P.dimension = 133 ∧ P.vectors.values.length = 1140000 ∧ P.alpha.values.length = 1140000 ∧
    P.beta.values.length = 1140000 ∧ P.alpha.valid = true ∧ P.beta.valid = true ∧
    P.parents.valid = true ∧ P.labels.valid = true ∧
    ∀ i < 1140000, P.vectors.values[i]! = xv T i ∧ P.alpha.values[i]! = qv T 0 i ∧
      P.beta.values[i]! = qv T 1 i ∧
      (0 < i → P.parents.values[i]! = (pp T i - 1) / 2 ∧
        P.labels.values[i]! = (pp T i - 1) % 2 + 1) := by
  unfold hnxBindK at hP
  obtain ⟨hs, hP⟩ := (CFSG.KS.bAnd_iff _ _).1 hP
  obtain ⟨hv, hP⟩ := (CFSG.KS.bAnd_iff _ _).1 hP
  obtain ⟨ha, hP⟩ := (CFSG.KS.bAnd_iff _ _).1 hP
  obtain ⟨hb, hP⟩ := (CFSG.KS.bAnd_iff _ _).1 hP
  obtain ⟨hp, hl⟩ := (CFSG.KS.bAnd_iff _ _).1 hP
  unfold hnxShapeK at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨hd, sv⟩, sa⟩, sb⟩, sp⟩, sl⟩ := hs
  have wv := walk_get sv hv
  have wa := walk_get sa ha
  have wb := walk_get sb hb
  have wp := walk_get sp hp
  have wl := walk_get sl hl
  refine ⟨hd, (shape_spec sv).2.2, (shape_spec sa).2.2, (shape_spec sb).2.2, (shape_spec sa).1,
    (shape_spec sb).1, (shape_spec sp).1, (shape_spec sl).1, fun i hi => ⟨?_, ?_, ?_, fun h0 => ?_⟩⟩
  · exact Nat.eq_of_beq_eq_true (wv i hi)
  · exact Nat.eq_of_beq_eq_true (wa i hi)
  · exact Nat.eq_of_beq_eq_true (wb i hi)
  · have hne : Nat.beq i (nat_lit 0) = false := by
      cases i with
      | zero => omega
      | succ i => rfl
    have e1 := wp i hi
    have e2 := wl i hi
    unfold parAt at e1
    unfold labAt at e2
    rw [hne] at e1 e2
    have f1 := Nat.eq_of_beq_eq_true e1
    have f2 := Nat.eq_of_beq_eq_true e2
    constructor
    · rw [f1]
      change (fldW (getRec T 464 i) 441 22 - 1) >>> 1 = (pp T i - 1) / 2
      rw [Nat.shiftRight_eq_div_pow]
      rfl
    · rw [f2]
      change ((fldW (getRec T 464 i) 441 22 - 1) &&& 1) + 1 = (pp T i - 1) % 2 + 1
      rw [Nat.and_one_is_mod]
      rfl

theorem qv_lt (T : Nat → Nat) (s i : Nat) : qv T s i < 2 ^ 21 := by
  unfold qv
  rw [fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem pp_lt (T : Nat → Nat) (i : Nat) : pp T i < 2 ^ 22 := by
  unfold pp
  rw [fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem orbit_facts {T : Nat → Nat} {P : PackedOrbitData} (hP : hnxBindK T P = true) :
    P.toOrbit.keys.size = 1140000 ∧ P.toOrbit.alpha.size = 1140000 ∧
    P.toOrbit.beta.size = 1140000 ∧
    ∀ i < 1140000, P.toOrbit.keys[i]! = orbitVector 133 (xv T i) ∧
      ap P.toOrbit.alpha i = qv T 0 i ∧ ap P.toOrbit.beta i = qv T 1 i ∧
      (0 < i → ap P.toOrbit.par i = (pp T i - 1) / 2 ∧
        ap P.toOrbit.lab i = (pp T i - 1) % 2 + 1) := by
  obtain ⟨hd, lv, la, lb, va, vb, vp, vl, hf⟩ := bind_facts hP
  refine ⟨by rw [toOrbit_keys_size, lv], by rw [toOrbit_alpha_size, la],
    by rw [toOrbit_beta_size, lb], fun i hi => ?_⟩
  obtain ⟨f1, f2, f3, f4⟩ := hf i hi
  have q0 := qv_lt T 0 i
  have q1 := qv_lt T 1 i
  refine ⟨?_, ?_, ?_, fun h0 => ?_⟩
  · rw [toOrbit_keys_get P (by omega), f1, hd]
  · rw [toOrbit_ap_alpha P va i (by rw [f2]; omega), f2]
  · rw [toOrbit_ap_beta P vb i (by rw [f3]; omega), f3]
  · obtain ⟨g1, g2⟩ := f4 h0
    have := pp_lt T i
    refine ⟨?_, ?_⟩
    · rw [toOrbit_ap_par P vp i (by rw [g1]; omega), g1]
    · rw [toOrbit_ap_lab P vl i (by rw [g2]; omega), g2]

structure GF (T : Nat → Nat) (W1 W2 : Nat) : Prop where
  q_lt : ∀ i < 1140000, ∀ s < 2, qv T s i < 1140000
  imgA : ∀ i < 1140000, ∀ l < 133,
    xe T (qv T 0 i) l = (∑ k ∈ range 133, xe T i k * ent13 W1 l k) % 5
  imgB : ∀ i < 1140000, ∀ l < 133,
    xe T (qv T 1 i) l = (∑ k ∈ range 133, xe T i k * ent13 W2 l k) % 5
  canon : ∀ i < 1140000, ∀ j < 133, xe T i j < 5
  inj : ∀ i < 1140000, ∀ j < 1140000, xv T i = xv T j → i = j
  pp0 : pp T 0 = 0
  mono : ∀ i, 0 < i → i < 1140000 → pp T (i - 1) < pp T i ∧ pp T i ≤ 2 * i
  edge : ∀ i < 1140000, ∀ s < 2, pp T (qv T s i) ≤ 2 * i + s + 1
  first : ∀ t, 0 < t → t < 1140000 → ∃ i < 1140000, ∃ s < 2, qv T s i = t ∧ pp T t = 2 * i + s + 1
  A2 : ordMat 5 133 13 1729 W1 ^ (1 + 1) = 1
  B3 : ordMat 5 133 13 1729 W2 ^ (2 + 1) = 1

@[expose] noncomputable def xvec (T : Nat → Nat) (i : Nat) : Fin 133 → ZMod 5 :=
  fun j => ((xe T i j.val : Nat) : ZMod 5)

theorem xvec_img {T : Nat → Nat} {W t i : Nat}
    (h : ∀ l < 133, xe T t l = (∑ k ∈ range 133, xe T i k * ent13 W l k) % 5) :
    xvec T t = ordMat 5 133 13 1729 W *ᵥ xvec T i := by
  funext l
  change _ = ∑ k : Fin 133, ordMat 5 133 13 1729 W l k * xvec T i k
  rw [xvec, h l.val l.isLt, ZMod.natCast_mod, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun k => ((xe T i k * ent13 W l.val k : Nat) : ZMod 5))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, mul_comm]
  rfl

theorem xv_eq_of_xvec {T : Nat → Nat} {a b : Nat} (ha : ∀ j < 133, xe T a j < 5)
    (hb : ∀ j < 133, xe T b j < 5) (h : xvec T a = xvec T b) : xv T a = xv T b := by
  refine eq_of_fields (xv_lt T a) (xv_lt T b) fun j hj => ?_
  exact nat_eq_of_cast (ha j hj) (hb j hj) (congrFun h ⟨j, hj⟩)

section GF

variable {T : Nat → Nat} {W1 W2 : Nat} (hg : GF T W1 W2)
include hg

theorem GF.vecA {i : Nat} (hi : i < 1140000) :
    xvec T (qv T 0 i) = ordMat 5 133 13 1729 W1 *ᵥ xvec T i := xvec_img (hg.imgA i hi)

theorem GF.vecB {i : Nat} (hi : i < 1140000) :
    xvec T (qv T 1 i) = ordMat 5 133 13 1729 W2 *ᵥ xvec T i := xvec_img (hg.imgB i hi)

theorem GF.inv0 {i : Nat} (hi : i < 1140000) : qv T 0 (qv T 0 i) = i := by
  have h1 := hg.q_lt i hi 0 (by norm_num)
  have h2 := hg.q_lt _ h1 0 (by norm_num)
  refine hg.inj _ h2 _ hi (xv_eq_of_xvec (hg.canon _ h2) (hg.canon _ hi) ?_)
  rw [hg.vecA h1, hg.vecA hi, Matrix.mulVec_mulVec, ← pow_two, hg.A2, Matrix.one_mulVec]

theorem GF.inv1 {i : Nat} (hi : i < 1140000) : qv T 1 (qv T 1 (qv T 1 i)) = i := by
  have h1 := hg.q_lt i hi 1 (by norm_num)
  have h2 := hg.q_lt _ h1 1 (by norm_num)
  have h3 := hg.q_lt _ h2 1 (by norm_num)
  refine hg.inj _ h3 _ hi (xv_eq_of_xvec (hg.canon _ h3) (hg.canon _ hi) ?_)
  have e : ordMat 5 133 13 1729 W2 * ordMat 5 133 13 1729 W2 * ordMat 5 133 13 1729 W2 = 1 := by
    rw [← pow_two, ← pow_succ]
    exact hg.B3
  rw [hg.vecB h2, hg.vecB h1, hg.vecB hi, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e,
    Matrix.one_mulVec]

end GF

theorem toVecB_orbitVector (x : Nat) :
    CFSG.Sporadic.F5.toVecB 133 (orbitVector 133 x) = fun j => ((x / 2 ^ (3 * j.val) % 8 : Nat) : ZMod 5) := by
  funext j
  unfold CFSG.Sporadic.F5.toVecB
  rw [orbitVector_get 133 x j.isLt]

theorem toMatR_rows {R : Array (Array Nat)} {W : Nat}
    (hR : ∀ i < 133, ∀ j < 133, (R[i]!)[j]! = ent13 W i j) :
    CFSG.Sporadic.F5.toMatR 133 133 R = ordMat 5 133 13 1729 W := by
  ext i j
  unfold CFSG.Sporadic.F5.toMatR
  rw [Matrix.of_apply, hR i i.isLt j j.isLt]
  rfl

theorem mulW_orbit {R : Array (Array Nat)} {W : Nat}
    (hR : ∀ i < 133, ∀ j < 133, (R[i]!)[j]! = ent13 W i j) {T : Nat → Nat} {i t : Nat}
    (hi : ∀ j < 133, xe T i j < 5) (ht : ∀ j < 133, xe T t j < 5)
    (h : ∀ l < 133, xe T t l = (∑ k ∈ range 133, xe T i k * ent13 W l k) % 5) :
    mulW 133 133 (frTable 133 133 R) (orbitVector 133 (xv T i)) = orbitVector 133 (xv T t) := by
  have hci : canonB 133 (orbitVector 133 (xv T i)) = true := canonB_orbitVector hi
  have hct : canonB 133 (orbitVector 133 (xv T t)) = true := canonB_orbitVector ht
  refine CFSG.Sporadic.F5.eq_of_toVecB_eq (CFSG.Sporadic.F5.canonB_mulW _ _ _ _) hct ?_
  rw [CFSG.Sporadic.F5.toVecB_mulW (by norm_num) (by norm_num) R hci, toMatR_rows hR,
    toVecB_orbitVector, toVecB_orbitVector]
  exact (xvec_img h).symm

theorem bytesToNats_get_gen (v : ByteArray) {j : Nat} (hj : j < v.size) :
    (bytesToNats v)[j]! = (v.get! j).toNat := by
  obtain ⟨a⟩ := v
  have hj' : j < a.size := hj
  unfold bytesToNats
  rw [getElem!_pos _ j (by simpa using hj'), Array.getElem_map]
  change a[j].toNat = (a[j]!).toNat
  rw [getElem!_pos a j hj']

theorem bytesToNats_orbitVector (x : Nat) {j : Nat} (hj : j < 133) :
    (bytesToNats (orbitVector 133 x))[j]! = x / 2 ^ (3 * j) % 8 := by
  rw [bytesToNats_get_gen _ (by rw [orbitVector_size]; exact hj), orbitVector_get 133 x hj]

theorem nodup_keys {T : Nat → Nat} {P : PackedOrbitData} (hP : hnxBindK T P = true)
    (hinj : ∀ i < 1140000, ∀ j < 1140000, xv T i = xv T j → i = j) :
    (P.vectors.values.map (orbitVector P.dimension)).Nodup := by
  obtain ⟨hd, lv, -, -, -, -, -, -, hf⟩ := bind_facts hP
  rw [List.nodup_iff_injective_get]
  intro a b hab
  have ha : a.val < 1140000 := by have := a.isLt; simp [lv] at this; exact this
  have hb : b.val < 1140000 := by have := b.isLt; simp [lv] at this; exact this
  simp only [List.get_eq_getElem, List.getElem_map] at hab
  have ea : P.vectors.values[a.val]'(by omega) = xv T a.val := by
    rw [← (hf a.val ha).1]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : a.val < P.vectors.values.length)]
  have eb : P.vectors.values[b.val]'(by omega) = xv T b.val := by
    rw [← (hf b.val hb).1]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : b.val < P.vectors.values.length)]
  simp only [ea, eb, hd] at hab
  exact Fin.ext (hinj _ ha _ hb (orbitVector_inj (xv_lt T _) (xv_lt T _) hab))

theorem arr_get_toList (A : Array Nat) (t : Nat) : A[t]! = A.toList[t]! := by
  cases A
  simp [List.getElem!_eq_getElem?_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem checkAt_of {D : F5Data} {T : Nat → Nat} {W1 W2 : Nat} {P : PackedOrbitData}
    (hg : GF T W1 W2) (hP : hnxBindK T P = true) (hd : D.d = 133)
    (hrA : ∀ i < 133, ∀ j < 133, (D.rowsA[i]!)[j]! = ent13 W1 i j)
    (hrB : ∀ i < 133, ∀ j < 133, (D.rowsB[i]!)[j]! = ent13 W2 i j) {k : Nat}
    (hk : k < 1140000) :
    f5OrbitCheckAt D.d (D.tabA ()) (D.tabB ()) P.toOrbit k = true := by
  obtain ⟨hks, -, -, hf⟩ := orbit_facts hP
  obtain ⟨-, lv, -⟩ := bind_facts hP
  obtain ⟨ek, ea, eb, et⟩ := hf k hk
  have hq0 := hg.q_lt k hk 0 (by norm_num)
  have hq1 := hg.q_lt k hk 1 (by norm_num)
  have hTA : D.tabA () = frTable 133 133 D.rowsA := by rw [← hd]; rfl
  have hTB : D.tabB () = frTable 133 133 D.rowsB := by rw [← hd]; rfl
  unfold f5OrbitCheckAt
  dsimp only
  rw [hd, hTA, hTB, hks, ea, eb, ek, (hf _ hq0).1, (hf _ hq1).1,
    mulW_orbit hrA (hg.canon k hk) (hg.canon _ hq0) (hg.imgA k hk),
    mulW_orbit hrB (hg.canon k hk) (hg.canon _ hq1) (hg.imgB k hk),
    ← ek, toOrbit_index P (nodup_keys hP hg.inj) (by omega)]
  have c1 : canonB 133 P.toOrbit.keys[k]! = true := by
    rw [ek]; exact canonB_orbitVector (hg.canon k hk)
  rw [c1, beq_self_eq_true k, decide_eq_true hq0, beq_self_eq_true, decide_eq_true hq1,
    beq_self_eq_true, Bool.true_and, Bool.true_and, Bool.true_and, Bool.true_and, Bool.true_and,
    Bool.true_and]
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · rw [h0]; rfl
  · obtain ⟨i, hi, s, hs, hqs, hpp⟩ := hg.first k h0 hk
    obtain ⟨epar, elb⟩ := et h0
    have hmk := (hg.mono k h0 hk).2
    have hpar : (pp T k - 1) / 2 = i := by omega
    rw [epar, hpar, elb, (hf i hi).2.1, (hf i hi).2.2.1, decide_eq_true (by omega : i < k)]
    have hk0 : (k == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    rw [hk0, Bool.false_or, Bool.true_and]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · have e1 : (pp T k - 1) % 2 + 1 = 1 := by omega
      rw [e1, hqs]
      simp
    · have e1 : (pp T k - 1) % 2 + 1 = 2 := by omega
      rw [e1, hqs]
      simp

theorem native_goal {D : F5Data} {T : Nat → Nat} {W1 W2 : Nat} {P : PackedOrbitData}
    {Q : List Nat} {G : Nat → Nat → Nat}
    (hg : GF T W1 W2) (hP : hnxBindK T P = true) (hO : D.orbit () = P.toOrbit)
    (hd : D.d = 133) (hn : D.n = 1140000) (hexp : D.expA = 2 ∧ D.expB = 3)
    (hrA : ∀ i < 133, ∀ j < 133, (D.rowsA[i]!)[j]! = ent13 W1 i j)
    (hrB : ∀ i < 133, ∀ j < 133, (D.rowsB[i]!)[j]! = ent13 W2 i j)
    (hroot : D.v0 = orbitVector 133 (xv T 0))
    (hQ : D.Q.toList = Q) (hQl : Q.length = 133) (hQn : ∀ q ∈ Q, q < 1140000)
    (hG5 : ∀ k < 133, ∀ l < 133, G k l < 5)
    (hXG : ∀ r < 133, ∀ l < 133,
      (∑ k ∈ range 133, xe T (Q[r]!) k * G k l) % 5 = if r = l then 1 else 0) :
    (matrixChecks D && orbitChecks D (D.orbit ()) 3 &&
      bfsOrderOK D.n (D.orbit ()).alpha (D.orbit ()).beta) = true := by
  obtain ⟨hks, has, hbs, hf⟩ := orbit_facts hP
  have hmat := matrixChecks_of hd hexp hrA hrB hg.A2 hg.B3
  have hQs : D.Q.size = 133 := by rw [← Array.length_toList, hQ, hQl]
  have hQget : ∀ t, D.Q[t]! = Q[t]! := fun t => by rw [arr_get_toList, hQ]
  have hQlt : ∀ t < 133, Q[t]! < 1140000 := fun t ht => by
    apply hQn
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  rw [hO, hn]
  have hf5 : f5OrbitOK D.d (D.tabA ()) (D.tabB ()) D.v0 P.toOrbit 3 = true := by
    unfold f5OrbitOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by rw [hks]; norm_num, by rw [hks]; norm_num⟩, ?_⟩, ?_⟩
    · rw [(hf 0 (by norm_num)).1, hroot]
      exact beq_self_eq_true _
    · refine CFSG.Sporadic.Th.parAll_eq_true_of fun k hk => ?_
      rw [hks] at hk
      exact checkAt_of hg hP hd hrA hrB hk
  have hiA : invOK 1140000 P.toOrbit.alpha (invT 1140000 P.toOrbit.alpha) = true :=
    (CFSG.KS.VO.invT_get (f := ap P.toOrbit.alpha) (g := ap P.toOrbit.alpha) (by norm_num)
      fun x hx => ⟨rfl, by rw [(hf x hx).2.1]; exact hg.q_lt x hx 0 (by norm_num), by
        rw [(hf x hx).2.1, (hf _ (hg.q_lt x hx 0 (by norm_num))).2.1]; exact hg.inv0 hx⟩).1
  have hiB : invOK 1140000 P.toOrbit.beta (invT 1140000 P.toOrbit.beta) = true :=
    (CFSG.KS.VO.invT_get (f := ap P.toOrbit.beta)
      (g := fun y => ap P.toOrbit.beta (ap P.toOrbit.beta y)) (by norm_num)
      fun x hx => ⟨rfl, by rw [(hf x hx).2.2.1]; exact hg.q_lt x hx 1 (by norm_num), by
        have h1 := hg.q_lt x hx 1 (by norm_num)
        have h2 := hg.q_lt _ h1 1 (by norm_num)
        rw [(hf x hx).2.2.1, (hf _ h1).2.2.1, (hf _ h2).2.2.1]; exact hg.inv1 hx⟩).1
  have hall : D.Q.all (· < 1140000) = true := by
    rw [Array.all_eq_true]
    intro t ht
    rw [hQs] at ht
    have := hQlt t ht
    rw [← hQget t, getElem!_pos D.Q t (by omega)] at this
    exact decide_eq_true this
  have hbasis : basisCheck D P.toOrbit = true := by
    refine basis_of (X := fun t i => xe T (Q[t]!) i) hd hQs (fun t ht i hi => ?_) hG5 hXG
    rw [hQget t, (hf _ (hQlt t ht)).1, bytesToNats_orbitVector _ hi]
    rfl
  have hbfs : bfsOrderOK 1140000 P.toOrbit.alpha P.toOrbit.beta = true := by
    refine bfsOrderOK_of (pp := pp T) (by norm_num) hg.pp0 hg.mono (fun i hi => ?_)
      (fun i hi => ?_) (fun t ht0 ht => ?_)
    · rw [(hf i hi).2.1, (hf i hi).2.2.1]
      exact ⟨hg.q_lt i hi 0 (by norm_num), hg.q_lt i hi 1 (by norm_num)⟩
    · rw [(hf i hi).2.1, (hf i hi).2.2.1]
      exact ⟨hg.edge i hi 0 (by norm_num), hg.edge i hi 1 (by norm_num)⟩
    · obtain ⟨i, hi, s, hs, hqs, hpp⟩ := hg.first t ht0 ht
      refine ⟨i, hi, ?_⟩
      rw [(hf i hi).2.1, (hf i hi).2.2.1]
      rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
      · exact Or.inl ⟨by omega, hqs⟩
      · exact Or.inr ⟨by omega, hqs⟩
  have hdq : decide (D.d ≤ D.Q.size) = true := by rw [hd, hQs]; decide
  have hn30 : decide (1140000 < 2 ^ 30) = true := by decide
  unfold orbitChecks
  rw [hn]
  simp only [hmat, hf5, hks, has, hbs, hiA, hiB, hdq, hn30, hall, hbasis, hbfs, beq_self_eq_true,
    Bool.and_true]

end CFSG.KS.SporSch.HNXP

end
