module

public import Certificates.Data.Kernel.Co2Cls
public import CFSG.Certificates.Kernel.Co2Syl.Sound
public import CFSG.Certificates.Kernel.BabyMonster.Q23Sound

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2Cls

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KLie.CT
  CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def genMonN (n : Nat) (G : Nat → Nat) :
    Submonoid (Matrix (Fin 22) (Fin 22) (ZMod 2)) :=
  Submonoid.closure (Set.range fun j : Fin n => MatP 22 (G j))

theorem genN_mem {n : Nat} (G : Nat → Nat) {j : Nat} (hj : j < n) : MatP 22 (G j) ∈ genMonN n G :=
  Submonoid.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem genMonN_five (G : Nat → Nat) : genMonN 5 G = genMon G := rfl

section Tree

variable {CF G : Nat → Nat} {NG X0 N : Nat}

theorem recC_spec {k : Nat} (h : recC CF G NG X0 N k = true) :
    sortK CF N k (sOf (recAt CF k)) = true ∧ (k = 0 → elemAt CF k = X0) ∧
    (k ≠ 0 → tOf (recAt CF k) 0 < k ∧ tOf (recAt CF k) 1 < NG ∧
      mulV (elemAt CF k) (G (tOf (recAt CF k) 1)) =
        mulV (G (tOf (recAt CF k) 1)) (elemAt CF (tOf (recAt CF k) 0))) := by
  unfold recC at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  rw [bIf_eq'] at h
  refine ⟨hs, fun h0 => ?_, fun h0 => ?_⟩
  · subst h0
    rw [iteT (Nat.beq_refl 0)] at h
    exact Nat.eq_of_beq_eq_true h
  · rw [iteF (by rw [beq_false h0]; exact Bool.false_ne_true)] at h
    simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
    exact ⟨blt_iff.1 h.1, blt_iff.1 h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem tree_conj (hok : ∀ k < N, recC CF G NG X0 N k = true) :
    ∀ k < N, ∃ g ∈ genMonN NG G, g * MatP 22 X0 = MatP 22 (elemAt CF k) * g := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  obtain ⟨-, h0, h1⟩ := recC_spec (hok k hk)
  rcases Nat.eq_zero_or_pos k with e | e
  · exact ⟨1, (genMonN NG G).one_mem, by rw [h0 e, one_mul, mul_one]⟩
  · obtain ⟨hp, hj, he⟩ := h1 (by omega)
    obtain ⟨g, hg, hgx⟩ := ih _ hp (by omega)
    refine ⟨MatP 22 (G (tOf (recAt CF k) 1)) * g, (genMonN NG G).mul_mem (genN_mem G hj) hg, ?_⟩
    have e2 := congrArg (MatP 22) he
    rw [MatP_mulV, MatP_mulV] at e2
    rw [mul_assoc, hgx, ← mul_assoc, ← e2, mul_assoc]

theorem tree_inj (hok : ∀ k < N, recC CF G NG X0 N k = true) :
    ∀ a < N, ∀ b < N, MatP 22 (elemAt CF a) = MatP 22 (elemAt CF b) → a = b := by
  have hs : ∀ i < N, sOf (recAt CF i) < N := by
    intro i hi
    have h := (recC_spec (hok i hi)).1
    unfold sortK at h
    rw [andK_eq, Bool.and_eq_true] at h
    exact blt_iff.1 h.1
  have hlt : ∀ i, i + 1 < N →
      elemAt CF (sOf (recAt CF i)) < elemAt CF (sOf (recAt CF (i + 1))) := by
    intro i hi
    have h := (recC_spec (hok i (by omega))).1
    unfold sortK at h
    rw [andK_eq, Bool.and_eq_true, implK_eq, blt_iff.2 hi, iteT rfl] at h
    exact blt_iff.1 h.2
  intro a ha b hb e
  exact sorted_inj (σ := fun i => sOf (recAt CF i)) (f := elemAt CF) hs hlt a ha b hb
    (MatP_inj' (elemAt_lt CF a) (elemAt_lt CF b) e)

theorem tree_card (hok : ∀ k < N, recC CF G NG X0 N k = true) :
    N ≤ Nat.card {y : Matrix (Fin 22) (Fin 22) (ZMod 2) //
      ∃ g ∈ genMonN NG G, g * MatP 22 X0 = y * g} := by
  have hinj : Function.Injective (fun k : Fin N => (⟨MatP 22 (elemAt CF k), tree_conj hok k k.2⟩ :
      {y : Matrix (Fin 22) (Fin 22) (ZMod 2) // ∃ g ∈ genMonN NG G, g * MatP 22 X0 = y * g})) :=
    fun a b e => Fin.ext (tree_inj hok a a.2 b b.2 (congrArg Subtype.val e))
  simpa using Nat.card_le_card_of_injective _ hinj

end Tree

section Orbit

variable {O IX H : Nat → Nat} {h m : Nat}

theorem orbK_spec {a : Nat} (hc : orbK O IX H h m a = true) :
    ∀ l < h, oixOf (IX a) l < m ∧ mulV (O (oixOf (IX a) l)) (H l) = mulV (H l) (O a) := by
  unfold orbK at hc
  rw [letB_eq, letB_eq] at hc
  intro l hl
  have e := recAll (p := fun l => oEdge O H m (O a) l (oixOf (IX a) l)) h hc l hl
  unfold oEdge at e
  rw [andK_eq, Bool.and_eq_true] at e
  exact ⟨blt_iff.1 e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem orb_sound (hm : 0 < m) (hc : ∀ a < m, orbK O IX H h m a = true) :
    ∀ g ∈ genMonN h H, ∃ b < m, MatP 22 (O b) * g = g * MatP 22 (O 0) := by
  intro g hg
  induction hg using Submonoid.closure_induction_left with
  | one => exact ⟨0, hm, by rw [mul_one, one_mul]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨b, hb, hby⟩ := ih
    obtain ⟨hc', he⟩ := orbK_spec (hc b hb) j j.2
    refine ⟨_, hc', ?_⟩
    have e2 := congrArg (MatP 22) he
    rw [MatP_mulV, MatP_mulV] at e2
    rw [← mul_assoc, e2, mul_assoc, hby, ← mul_assoc]

end Orbit

theorem MatP_powK (W : Nat) : ∀ e, MatP 22 (powK W e) = MatP 22 W ^ e
  | 0 => by
    change MatP 22 IDP = _
    rw [MatP_IDP, pow_zero]
  | e + 1 => by
    change MatP 22 (mulV (powK W e) W) = _
    rw [MatP_mulV, MatP_powK W e, pow_succ]

theorem MatP_ne_one {W : Nat} (hW : W < 2 ^ 484) (h : Nat.beq W IDP = false) : MatP 22 W ≠ 1 := by
  intro e
  rw [← MatP_IDP] at e
  rw [MatP_inj' hW IDP_lt e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem ordK_sound {W p : Nat} (hW : W < 2 ^ 484) (hp : p.Prime) (h : ordK W p = true) :
    orderOf (MatP 22 W) = p := by
  unfold ordK at h
  rw [andK_eq, Bool.and_eq_true, notK_eq, Bool.not_eq_true'] at h
  have h1 : MatP 22 W ^ p = 1 := by
    rw [← MatP_powK, Nat.eq_of_beq_eq_true h.1, MatP_IDP]
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime h1 (MatP_ne_one hW h.2)

theorem oddW_sound {Y W p : Nat} (hW : W < 2 ^ 484) (hp : p.Prime) (h : oddW Y W p = true) :
    orderOf (MatP 22 W) = p ∧ MatP 22 W * MatP 22 Y = MatP 22 Y * MatP 22 W := by
  unfold oddW at h
  rw [andK_eq, Bool.and_eq_true] at h
  exact ⟨ordK_sound hW hp h.1, commK_sound h.2⟩

theorem pairW_sound {Y U V : Nat} (hU : U < 2 ^ 484) (hV : V < 2 ^ 484) (h : pairW Y U V = true) :
    orderOf (MatP 22 U) = 3 ∧ orderOf (MatP 22 V) = 3 ∧
    MatP 22 U * MatP 22 Y = MatP 22 Y * MatP 22 U ∧
    MatP 22 V * MatP 22 Y = MatP 22 Y * MatP 22 V ∧
    MatP 22 U * MatP 22 V = MatP 22 V * MatP 22 U ∧
    MatP 22 V ≠ MatP 22 U ∧ MatP 22 V ≠ MatP 22 U * MatP 22 U := by
  unfold pairW at h
  simp only [andK_eq, Bool.and_eq_true, notK_eq, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨o1, c1⟩ := oddW_sound hU Nat.prime_three h1
  obtain ⟨o2, c2⟩ := oddW_sound hV Nat.prime_three h2
  refine ⟨o1, o2, c1, c2, commK_sound h3, fun e => ?_, fun e => ?_⟩
  · rw [MatP_inj' hV hU e, Nat.beq_refl] at h4
    exact Bool.noConfusion h4
  · rw [← MatP_mulV] at e
    rw [MatP_inj' hV (mulV_lt U U) e, Nat.beq_refl] at h5
    exact Bool.noConfusion h5

theorem MatP_xor (A B : Nat) : MatP 22 (A ^^^ B) = MatP 22 A + MatP 22 B := by
  ext i j
  rw [Matrix.add_apply, MatP_apply, MatP_apply, MatP_apply, Nat.testBit_xor]
  cases A.testBit (i.val * 22 + j.val) <;> cases B.testBit (i.val * 22 + j.val) <;> decide

@[expose] noncomputable def fld22 (T i : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 22) i)) (nat_lit 4194303)

theorem fld22_lt (T i : Nat) : fld22 T i < 2 ^ 22 := by
  unfold fld22
  change (T >>> (22 * i)) &&& (2 ^ 22 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem testBit_fld22 (T i j : Nat) (hj : j < 22) :
    (fld22 T i).testBit j = T.testBit (i * 22 + j) := by
  unfold fld22
  change ((T >>> (22 * i)) &&& (2 ^ 22 - 1)).testBit j = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and,
    Nat.testBit_shiftRight, Nat.mul_comm 22 i, Nat.add_comm]

theorem fld22_shr (R l : Nat) : fld22 (R >>> 22) l = fld22 R (l + 1) := by
  unfold fld22
  change ((R >>> 22) >>> (22 * l)) &&& _ = (R >>> (22 * (l + 1))) &&& _
  rw [← Nat.shiftRight_add]
  congr 2
  omega

@[expose] noncomputable def matL (U : Nat) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.of fun i j => if (fld22 U i).testBit j then 1 else 0

theorem MatP_eq_matL (U : Nat) : MatP 22 U = matL U := by
  ext i j
  rw [MatP_apply, matL, Matrix.of_apply, testBit_fld22 _ _ _ j.isLt]

@[expose] noncomputable def eLoopL (fromK : Bool) (k n R i st : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ st => st)
    (fun _ ih R i st => CFSG.KC.BM.forceB (CFSG.KC.BM.eBody fromK k i (Nat.land R (nat_lit 4194303)) st)
      (fun st' => ih (Nat.shiftRight R (nat_lit 22)) (Nat.succ i) st')) n R i st

theorem eLoopL_eq (fromK : Bool) (k : Nat) : ∀ (n R i st : Nat),
    eLoopL fromK k n R i st =
      (List.range n).foldl (fun st l => CFSG.KC.BM.eBody fromK k (i + l) (fld22 R l) st) st
  | 0, _, _, _ => rfl
  | n + 1, R, i, st => by
    have e : eLoopL fromK k (n + 1) R i st =
        eLoopL fromK k n (R >>> 22) (i + 1) (CFSG.KC.BM.eBody fromK k i (fld22 R 0) st) := by
      change CFSG.KC.BM.forceB _ _ = _
      rw [CFSG.KC.BM.forceB_q]
      rfl
    rw [e, eLoopL_eq fromK k n]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, Nat.add_zero]
    congr 1
    funext st' l
    have e2 : i + 1 + l = i + (l + 1) := by omega
    rw [fld22_shr, e2]

theorem ech22L_fold {fromK : Bool} {Q k : Nat} (h : ech22L fromK Q k = true) :
    (List.range 22).foldl (fun st i => CFSG.KC.BM.eBody fromK k i (fld22 Q i) st)
      (Nat.shiftLeft 1 40) ≠ 0 := by
  have e : ech22L fromK Q k = Nat.blt 0 (eLoopL fromK k 22 Q 0 (Nat.shiftLeft 1 40)) := rfl
  rw [e, eLoopL_eq, Nat.blt_eq] at h
  simp only [Nat.zero_add] at h
  omega

theorem rankL_sound {M P Q k : Nat} (hk : k ≤ 22) (h : rankL M P Q k = true) :
    (MatP 22 M).rank = k := by
  unfold rankL at h
  rw [andK_eq, andK_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hQ, hEQ, hEP⟩ := h
  have hmat : matL Q = matL P * matL M := by
    rw [← MatP_eq_matL, ← MatP_eq_matL, ← MatP_eq_matL, ← Nat.eq_of_beq_eq_true hQ, MatP_mulV]
  rw [MatP_eq_matL]
  have hfQ : (List.range 22).foldl (fun st i => if Nat.blt i k then CFSG.KC.BM.echStep (fld22 Q i) st
      else if Nat.beq (fld22 Q i) 0 then st else 0) (Nat.shiftLeft 1 40) ≠ 0 := by
    have hf : (fun st i => CFSG.KC.BM.eBody false k i (fld22 Q i) st) = (fun st i =>
        if Nat.blt i k then CFSG.KC.BM.echStep (fld22 Q i) st
        else if Nat.beq (fld22 Q i) 0 then st else 0) := by
      funext st i
      unfold CFSG.KC.BM.eBody
      cases Nat.blt i k <;> cases Nat.beq (fld22 Q i) 0 <;> rfl
    have := ech22L_fold hEQ
    rw [hf] at this
    exact this
  have hfP : (List.range 22).foldl (fun st i => if Nat.ble k i then CFSG.KC.BM.echStep (fld22 P i) st
      else if true then st else 0) (Nat.shiftLeft 1 40) ≠ 0 := by
    have hf : (fun st i => CFSG.KC.BM.eBody true k i (fld22 P i) st) = (fun st i =>
        if Nat.ble k i then CFSG.KC.BM.echStep (fld22 P i) st else if true then st else 0) := by
      funext st i
      unfold CFSG.KC.BM.eBody
      cases Nat.ble k i <;> rfl
    have := ech22L_fold hEP
    rw [hf] at this
    exact this
  obtain ⟨A1, B1, C1, -⟩ := CFSG.KC.BM.SL.ech_fold (fun i => Nat.blt i k) (fun _ r => Nat.beq r 0)
    (fld22 Q) (Nat.shiftLeft 1 40) 22 hfQ
  obtain ⟨A2, -, C2, -⟩ := CFSG.KC.BM.SL.ech_fold (fun i => Nat.ble k i) (fun _ _ => true)
    (fld22 P) (Nat.shiftLeft 1 40) 22 hfP
  have hp1 : ∀ i : Fin 22, i.val < k → Nat.blt i.val k = true := fun i hi => by
    rw [Nat.blt_eq]
    exact hi
  have hp2 : ∀ i : Fin 22, ¬ i.val < k → Nat.ble k i.val = true := fun i hi => by
    rw [Nat.ble_eq]
    omega
  have hli1 : LinearIndependent (ZMod 2)
      ((matL Q).submatrix (fun i : {i : Fin 22 // i.val < k} => i.val) id).row :=
    CFSG.KC.BM.linIndep_rows22 (fun i : {i : Fin 22 // i.val < k} => fld22 Q i.val)
      (fun i => A1 _ i.val.isLt (hp1 _ i.property)) (fun i => fld22_lt _ _)
      (CFSG.KC.BM.log2_inj_of hp1 C1)
  have hli2 : LinearIndependent (ZMod 2)
      ((matL P).submatrix (fun i : {i : Fin 22 // ¬ i.val < k} => i.val) id).row :=
    CFSG.KC.BM.linIndep_rows22 (fun i : {i : Fin 22 // ¬ i.val < k} => fld22 P i.val)
      (fun i => A2 _ i.val.isLt (hp2 _ i.property)) (fun i => fld22_lt _ _)
      (CFSG.KC.BM.log2_inj_of hp2 C2)
  have hz : (matL P).submatrix (fun i : {i : Fin 22 // ¬ i.val < k} => i.val) id * matL M =
      0 := by
    ext i j
    have e1 : ((matL P).submatrix (fun i : {i : Fin 22 // ¬ i.val < k} => i.val) id *
        matL M) i j = (matL P * matL M) i.val j := by
      simp [Matrix.mul_apply]
    have hb := B1 i.val.val i.val.isLt (by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact i.property)
    have h0 : fld22 Q i.val.val = 0 := Nat.eq_of_beq_eq_true hb
    rw [e1, ← hmat, Matrix.zero_apply]
    simp [matL, h0]
  have hlo : k ≤ (matL M).rank := by
    have h1 := LinearIndependent.rank_matrix hli1
    rw [Fintype.card_fin_lt_of_le hk] at h1
    calc k = _ := h1.symm
      _ ≤ (matL Q).rank := Matrix.rank_submatrix_le _ _ _
      _ ≤ (matL M).rank := by
        rw [hmat]
        exact Matrix.rank_mul_le_right _ _
  have hhi := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
  rw [LinearIndependent.rank_matrix hli2, Fintype.card_subtype_compl,
    Fintype.card_fin_lt_of_le hk, Fintype.card_fin] at hhi
  omega

end CFSG.KC.Co2Cls

end
