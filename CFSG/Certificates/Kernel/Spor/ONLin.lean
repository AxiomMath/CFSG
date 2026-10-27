module

public import CFSG.Certificates.Kernel.Spor.ONVecLib
public import CFSG.F3.Spec

public section

namespace CFSG.KS.ONLin

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native
open Matrix

@[expose] noncomputable def vz (X : Nat) : Fin 154 → ZMod 3 := fun t => (vOf X).val t.val

@[expose] def Orbit (n : Nat) (key : Nat → Nat) : Prop :=
  (∀ i < n, canon (key i) = true) ∧ ∀ i < n, ∀ j < n, key i = key j → i = j

@[expose] def Lin (n : Nat) (key : Nat → Nat) (f : Nat → Nat) : Prop :=
  ∃ M : Matrix (Fin 154) (Fin 154) (ZMod 3), ∀ i < n, f i < n ∧ vz (key (f i)) = M *ᵥ vz (key i)

@[expose] def Spans (n : Nat) (key : Nat → Nat) (P : Nat → Nat) : Prop :=
  (∀ t < 154, P t < n) ∧
    ∀ k : Fin 154, ∃ c : Fin 154 → ZMod 3, Pi.single k 1 = ∑ t : Fin 154, c t • vz (key (P t.val))

variable {n : Nat} {key : Nat → Nat}

theorem Lin.id : Lin n key fun x => x := ⟨1, fun i hi => ⟨hi, by rw [Matrix.one_mulVec]⟩⟩

theorem Lin.comp {f g : Nat → Nat} (hf : Lin n key f) (hg : Lin n key g) :
    Lin n key fun x => f (g x) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M * N, fun i hi => ⟨(hM _ (hN i hi).1).1, ?_⟩⟩
  rw [(hM _ (hN i hi).1).2, (hN i hi).2, Matrix.mulVec_mulVec]

theorem Lin.congr {f g : Nat → Nat} (hf : Lin n key f) (h : ∀ i < n, f i = g i) : Lin n key g := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun i hi => by rw [← h i hi]; exact hM i hi⟩

theorem wf_vOf {X : Nat} (h : canon X = true) : (vOf X).wf = true := by
  unfold V.wf
  rw [beq_iff_eq]
  exact (canon_bits h).1

theorem bits_of_val {a : V} (ha : a.wf = true) (j : Nat) :
    a.p.testBit j = decide (a.val j = 1) ∧ a.m.testBit j = decide (a.val j = 2) := by
  have hn := V.not_both ha j
  rw [V.val_eq_bitVal]
  cases hp : a.p.testBit j <;> cases hm : a.m.testBit j <;> simp_all [bitVal] <;> decide

theorem vz_inj {X Y : Nat} (hX : canon X = true) (hY : canon Y = true) (h : vz X = vz Y) : X = Y := by
  have hbX := canon_bits hX
  have hbY := canon_bits hY
  have hval : ∀ j, (vOf X).val j = (vOf Y).val j := by
    intro j
    by_cases hj : j < 154
    · exact congrFun h ⟨j, hj⟩
    · have hx : (vP X).testBit j = false ∧ (vM X).testBit j = false :=
        ⟨Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbX.2.1 (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbX.2.2 (Nat.pow_le_pow_right (by omega) (by omega)))⟩
      have hy : (vP Y).testBit j = false ∧ (vM Y).testBit j = false :=
        ⟨Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbY.2.1 (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbY.2.2 (Nat.pow_le_pow_right (by omega) (by omega)))⟩
      rw [V.val_eq_bitVal, V.val_eq_bitVal]
      exact congrArg₂ bitVal (hx.1.trans hy.1.symm) (hx.2.trans hy.2.symm)
  have hp : vP X = vP Y := Nat.eq_of_testBit_eq fun j => by
    have a := (bits_of_val (wf_vOf hX) j).1
    have b := (bits_of_val (wf_vOf hY) j).1
    change (vOf X).p.testBit j = (vOf Y).p.testBit j
    rw [a, b, hval j]
  have hm : vM X = vM Y := Nat.eq_of_testBit_eq fun j => by
    have a := (bits_of_val (wf_vOf hX) j).2
    have b := (bits_of_val (wf_vOf hY) j).2
    change (vOf X).m.testBit j = (vOf Y).m.testBit j
    rw [a, b, hval j]
  rw [← vmk_vP_vM X, ← vmk_vP_vM Y, hp, hm]

theorem Orbit.eq_of_vz (hO : Orbit n key) {i j : Nat} (hi : i < n) (hj : j < n)
    (h : vz (key i) = vz (key j)) : i = j :=
  hO.2 i hi j hj (vz_inj (hO.1 i hi) (hO.1 j hj) h)

@[expose] noncomputable def colMat (L : List Nat) : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  Matrix.of fun k j => (vOf (L.getD j.val 0)).val k.val

theorem vz_mv {L : List Nat} (hlen : L.length = 154) (hL : ∀ j < 154, canon (L.getD j 0) = true)
    {X : Nat} (hX : canon X = true) : vz (mv L X) = colMat L *ᵥ vz X := by
  funext k
  have hY : ∀ j : Nat, (L.map vOf).toArray[j]!.wf = true := by
    intro j
    by_cases hj : j < L.length
    · rw [map_vOf_get hj]
      exact wf_vOf (hL j (by omega))
    · rw [getElem!_neg _ j (by simpa using hj)]
      rfl
  unfold vz
  rw [vOf_mv (by rw [hlen]; exact hL) X, V.val_comb _ _ _ hY (wf_vOf hX), hlen,
    ← Fin.sum_univ_eq_sum_range (fun j => (vOf X).val j * ((L.map vOf).toArray[j]!).val k.val)]
  unfold Matrix.mulVec dotProduct colMat
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_vOf_get (by rw [hlen]; exact j.isLt)]
  exact mul_comm _ _

theorem lin_of_mv (hO : Orbit n key) {L : List Nat} (hlen : L.length = 154)
    (hL : ∀ j < 154, canon (L.getD j 0) = true) {f : Nat → Nat}
    (hf : ∀ i < n, f i < n ∧ key (f i) = mv L (key i)) : Lin n key f :=
  ⟨colMat L, fun i hi => ⟨(hf i hi).1, by rw [(hf i hi).2, vz_mv hlen hL (hO.1 i hi)]⟩⟩

theorem mat_eq_of_span {P : Nat → Nat} (hS : Spans n key P) {M N : Matrix (Fin 154) (Fin 154) (ZMod 3)}
    (h : ∀ t : Fin 154, M *ᵥ vz (key (P t.val)) = N *ᵥ vz (key (P t.val))) : M = N := by
  have hv : ∀ k : Fin 154, M *ᵥ Pi.single k 1 = N *ᵥ Pi.single k 1 := by
    intro k
    obtain ⟨c, hc⟩ := hS.2 k
    rw [hc, Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, h t]
  ext i k
  have := congrFun (hv k) i
  simpa [Matrix.mulVec_single] using this

theorem Lin.eq_of_span (hO : Orbit n key) {P : Nat → Nat} (hS : Spans n key P) {f g : Nat → Nat}
    (hf : Lin n key f) (hg : Lin n key g) (h : ∀ t < 154, f (P t) = g (P t)) :
    ∀ i < n, f i = g i := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  have e : M = N := mat_eq_of_span hS fun t => by
    have hp := hS.1 t.val t.isLt
    rw [← (hM _ hp).2, ← (hN _ hp).2, h t.val t.isLt]
  intro i hi
  refine hO.eq_of_vz (hM i hi).1 (hN i hi).1 ?_
  rw [(hM i hi).2, (hN i hi).2, e]

theorem Lin.inv {P : Nat → Nat} (hS : Spans n key P) {f g : Nat → Nat}
    (hf : Lin n key f) (hfg : ∀ x < n, g x < n ∧ g (f x) = x) : Lin n key g := by
  obtain ⟨M, hM⟩ := hf
  have hsurj : ∀ y < n, f (g y) = y := by
    intro y hy
    obtain ⟨x, hx, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n)
      (t := Finset.range n) (fun x _ => f x)
      (fun x hx => Finset.mem_range.2 (hM x (Finset.mem_range.1 hx)).1)
      (fun a b ha hb hab => by
        rw [← (hfg a (Finset.mem_range.1 ha)).2, ← (hfg b (Finset.mem_range.1 hb)).2, hab])
      le_rfl y (Finset.mem_range.2 hy)
    rw [e, (hfg x (Finset.mem_range.1 hx)).2]
  have hon : Function.Surjective M.mulVec := by
    intro v
    have hsp : ∀ k : Fin 154, ∃ w, M *ᵥ w = Pi.single k 1 := by
      intro k
      obtain ⟨c, hc⟩ := hS.2 k
      refine ⟨∑ t : Fin 154, c t • vz (key (g (P t.val))), ?_⟩
      rw [hc, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hp := hS.1 t.val t.isLt
      rw [Matrix.mulVec_smul, ← (hM _ (hfg _ hp).1).2, hsurj _ hp]
    choose w hw using hsp
    refine ⟨∑ k : Fin 154, v k • w k, ?_⟩
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hw]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hu : IsUnit M := (Matrix.mulVec_surjective_iff_isUnit).1 hon
  refine ⟨M⁻¹, fun y hy => ⟨(hfg y hy).1, ?_⟩⟩
  have e : M *ᵥ vz (key (g y)) = vz (key y) := by
    rw [← (hM _ (hfg y hy).1).2, hsurj y hy]
  rw [← e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).1 hu),
    Matrix.one_mulVec]

end CFSG.KS.ONLin

end
