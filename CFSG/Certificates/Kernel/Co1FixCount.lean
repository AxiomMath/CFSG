
module

public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.Sporadic.Co1.Module.InvSpec

public section

namespace CFSG.KC.Co1Fix

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative Matrix

@[expose] noncomputable def vecOf (x : Nat) : Fin 24 → ZMod 2 := toVecD 24 x

theorem bit_eq' (X i : Nat) : bit X i = X.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff, Nat.beq_eq,
    decide_eq_true_iff]

private theorem blt_iff' {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

private theorem andB_iff {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [CFSG.KLie.CT.andB]

private theorem beq_iff' {a b : Nat} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

private theorem lenL_eq' : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq' L)

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem pw2_eq' (w : Nat) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem addZ : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

theorem add_self' (x : Fin 24 → ZMod 2) : x + x = 0 := by
  funext j
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this (x j)

theorem eq_of_add' {x y : Fin 24 → ZMod 2} (h : x + y = 0) : x = y :=
  funext fun j => addZ _ _ (congrFun h j)

theorem zero_smul' (x : Fin 24 → ZMod 2) : (0 : ZMod 2) • x = 0 := by
  funext j
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_mul]

theorem smul_zero' (a : ZMod 2) : a • (0 : Fin 24 → ZMod 2) = 0 := by
  funext j
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero]

theorem one_smul' (x : Fin 24 → ZMod 2) : (1 : ZMod 2) • x = x := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, one_mul]

@[expose] noncomputable def lowR (v : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 24
    (fun k ih => nIf(bit v (Nat.sub (Nat.sub 24 1) k), Nat.sub (Nat.sub 24 1) k, ih)) n

theorem lowR_spec (v : Nat) : ∀ n ≤ 24, lowR v n < 24 → v.testBit (lowR v n) = true ∧
    24 - n ≤ lowR v n ∧ ∀ j, 24 - n ≤ j → j < lowR v n → v.testBit j = false
  | 0, _, h => absurd h (Nat.lt_irrefl 24)
  | n + 1, hn, h => by
    have e : lowR v (n + 1) = Bool.rec (motive := fun _ => Nat) (lowR v n) (23 - n)
        (v.testBit (23 - n)) := by
      change Bool.rec (motive := fun _ => Nat) (lowR v n) (Nat.sub (Nat.sub 24 1) n)
        (bit v (Nat.sub (Nat.sub 24 1) n)) = _
      rw [bit_eq']
      rfl
    cases hb : v.testBit (23 - n)
    · have e' : lowR v (n + 1) = lowR v n := by rw [e, hb]
      rw [e'] at h ⊢
      obtain ⟨h1, h2, h3⟩ := lowR_spec v n (by omega) h
      refine ⟨h1, by omega, fun j hj1 hj2 => ?_⟩
      by_cases hj : j = 23 - n
      · rw [hj]
        exact hb
      · exact h3 j (by omega) hj2
    · have e' : lowR v (n + 1) = 23 - n := by rw [e, hb]
      rw [e']
      exact ⟨hb, by omega, fun j hj1 hj2 => by omega⟩

theorem lowK_spec {v : Nat} (h : lowK 24 v < 24) :
    v.testBit (lowK 24 v) = true ∧ ∀ j < lowK 24 v, v.testBit j = false := by
  obtain ⟨h1, -, h3⟩ := lowR_spec v 24 le_rfl h
  exact ⟨h1, fun j hj => h3 j (by omega) hj⟩

theorem pivK_spec : ∀ (L : List Nat) (acc : Nat), pivK 24 L acc = true →
    (∀ v ∈ L, lowK 24 v < 24 ∧ acc.testBit (lowK 24 v) = false) ∧ (L.map (lowK 24)).Nodup
  | [], _, _ => ⟨fun v hv => absurd hv List.not_mem_nil, List.nodup_nil⟩
  | v :: L, acc, h => by
    change CFSG.KC.M1F2.strictB (lowK 24 v) (fun p => CFSG.KLie.CT.andB (Nat.blt p 24)
      (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (bit acc p)) (pivK 24 L (Nat.lor acc (pw2 p))))) = true at h
    rw [strictB_eq'] at h
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    obtain ⟨h2, h3⟩ := andB_iff.1 h2
    have hp : lowK 24 v < 24 := blt_iff'.1 h1
    have hacc : acc.testBit (lowK 24 v) = false := by
      rw [← bit_eq']
      cases e : bit acc (lowK 24 v)
      · rfl
      · rw [e] at h2
        exact absurd h2 Bool.false_ne_true
    obtain ⟨ih1, ih2⟩ := pivK_spec L _ h3
    have hor : ∀ j, (Nat.lor acc (pw2 (lowK 24 v))).testBit j =
        (acc.testBit j || decide (j = lowK 24 v)) := fun j => by
      change (acc ||| pw2 (lowK 24 v)).testBit j = _
      rw [Nat.testBit_or, pw2_eq', Nat.testBit_two_pow]
      by_cases hj : j = lowK 24 v <;> simp [hj, eq_comm]
    refine ⟨fun w hw => ?_, ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨hp, hacc⟩
      · obtain ⟨a, b⟩ := ih1 w hw
        rw [hor] at b
        exact ⟨a, (Bool.or_eq_false_iff.1 b).1⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih2⟩
      obtain ⟨w, hw, e⟩ := List.mem_map.1 hm
      have b := (ih1 w hw).2
      rw [hor, e] at b
      simp at b

@[expose] noncomputable def comb (L : List Nat) (n : Nat) (c : Fin n → ZMod 2) : Fin 24 → ZMod 2 :=
  ∑ i, c i • vecOf (L.getD i 0)

theorem comb_add (L : List Nat) (n : Nat) (c c' : Fin n → ZMod 2) :
    comb L n (c + c') = comb L n c + comb L n c' := by
  funext j
  simp only [comb, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib]

theorem comb_zero (L : List Nat) (n : Nat) : comb L n 0 = 0 := by
  unfold comb
  exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, zero_smul']

theorem piv_indep {L : List Nat} {n : Nat} (hn : n ≤ L.length) (hlow : ∀ v ∈ L, lowK 24 v < 24)
    (hnd : (L.map (lowK 24)).Nodup) (c : Fin n → ZMod 2) (hc : comb L n c = 0) : c = 0 := by
  classical
  have hget : ∀ i : Fin n, L.getD i 0 ∈ L := fun i => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hinj : ∀ i j : Fin n, lowK 24 (L.getD i 0) = lowK 24 (L.getD j 0) → i = j := by
    intro i j e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    have := List.nodup_iff_injective_getElem.1 hnd (a₁ := ⟨i.val, by simp; omega⟩)
      (a₂ := ⟨j.val, by simp; omega⟩) (by simpa using e)
    exact Fin.ext (Fin.mk.inj this)
  by_contra hne
  have hS : (Finset.univ.filter fun i => c i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun i : Fin n => lowK 24 (L.getD i 0)) hS
  have hci : c i ≠ 0 := by simpa using hi
  have hli := lowK_spec (hlow _ (hget i))
  have hcoord := congrFun hc ⟨lowK 24 (L.getD i 0), hlow _ (hget i)⟩
  unfold comb at hcoord
  rw [Finset.sum_apply, Finset.sum_eq_single i] at hcoord
  · have hb1 : vecOf (L.getD i 0) ⟨lowK 24 (L.getD i 0), hlow _ (hget i)⟩ = 1 := by
      simp only [vecOf, toVecD_apply, hli.1, ↓reduceIte]
    rw [Pi.smul_apply, hb1, smul_eq_mul, mul_one] at hcoord
    exact hci hcoord
  · intro j _ hj
    by_cases hcj : c j = 0
    · rw [Pi.smul_apply, hcj, smul_eq_mul, zero_mul]
    · have hjm := hmin j (by simpa using hcj)
      have hne' : lowK 24 (L.getD j 0) ≠ lowK 24 (L.getD i 0) := fun e => hj (hinj j i e)
      have hlt : lowK 24 (L.getD i 0) < lowK 24 (L.getD j 0) := lt_of_le_of_ne hjm (Ne.symm hne')
      have hb := (lowK_spec (hlow _ (hget j))).2 _ hlt
      have hb0 : vecOf (L.getD j 0) ⟨lowK 24 (L.getD i 0), hlow _ (hget i)⟩ = 0 := by
        simp only [vecOf, toVecD_apply, hb, Bool.false_eq_true, ↓reduceIte]
      rw [Pi.smul_apply, hb0, smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem comb_injective {L : List Nat} {n : Nat} (hn : n ≤ L.length) (hlow : ∀ v ∈ L, lowK 24 v < 24)
    (hnd : (L.map (lowK 24)).Nodup) : Function.Injective (comb L n) := fun c c' e => by
  have h := piv_indep hn hlow hnd (c + c') (by rw [comb_add, e, add_self'])
  funext i
  exact addZ _ _ (congrFun h i)

theorem comb_act (N : Matrix (Fin 24) (Fin 24) (ZMod 2)) (L : List Nat) (n : Nat)
    (c : Fin n → ZMod 2) : comb L n c ᵥ* N + comb L n c =
      ∑ i, c i • (vecOf (L.getD i 0) ᵥ* N + vecOf (L.getD i 0)) := by
  unfold comb
  rw [Matrix.sum_vecMul]
  funext j
  simp only [Pi.add_apply, Finset.sum_apply, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]

theorem dotK_eq (x y : Nat) : ∀ d, dotK d x y =
    (List.range d).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) false
  | 0 => rfl
  | d + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← dotK_eq x y d]
    change Bool.rec (motive := fun _ => Bool) (dotK d x y) (CFSG.KLie.CT.notB (dotK d x y))
      (CFSG.KLie.CT.andB (bit x d) (bit y d)) = _
    rw [bit_eq', bit_eq']
    cases x.testBit d <;> cases y.testBit d <;> cases dotK d x y <;> rfl

theorem dotK_dotN (x y : Nat) : dotK 24 x y = dotN x y := by
  unfold dotN
  exact dotK_eq x y 24

theorem qCountK_cons (Qt f : Nat) (F : List Nat) (acc : Nat) :
    qCountK 24 Qt (f :: F) acc = qCountK 24 Qt F acc + qCountK 24 Qt F (acc ^^^ f) := by
  change CFSG.KC.Loop.strictN (qCountK 24 Qt F acc) (fun a => CFSG.KC.Loop.strictN
    (qCountK 24 Qt F (Nat.xor acc f)) fun b => Nat.add a b) = _
  rw [strictN_eq', strictN_eq']
  rfl

@[expose] def spanL : List Nat → Nat → List Nat
  | [], a => [a]
  | f :: G, a => spanL G a ++ spanL G (a ^^^ f)

theorem qCountK_append (Qt : Nat) : ∀ (G F : List Nat) (acc : Nat),
    qCountK 24 Qt (G ++ F) acc = ((spanL G acc).map (qCountK 24 Qt F)).sum
  | [], F, acc => by simp [spanL]
  | f :: G, F, acc => by
    rw [List.cons_append, qCountK_cons, qCountK_append Qt G F, qCountK_append Qt G F, spanL,
      List.map_append, List.sum_append]

theorem comb_cons (v : Nat) (L : List Nat) (n : Nat) (c : Fin (n + 1) → ZMod 2) :
    comb (v :: L) (n + 1) c = c 0 • vecOf v + comb L n (fun i => c i.succ) :=
  Fin.sum_univ_succ (fun i : Fin (n + 1) => c i • vecOf ((v :: L).getD i 0))

theorem qCountK_eq {Qt : Nat} {q : (Fin 24 → ZMod 2) → ZMod 2}
    (hq : ∀ x < 2 ^ 24, q (vecOf x) = if dotK 24 x (vecK 24 Qt x) = true then 1 else 0) :
    ∀ (F : List Nat) (n : Nat), F.length = n → (∀ f ∈ F, f < 2 ^ 24) → ∀ acc < 2 ^ 24,
      qCountK 24 Qt F acc =
        (Finset.univ.filter fun c : Fin n → ZMod 2 => q (vecOf acc + comb F n c) = 1).card
  | [], n, hn, _, acc, hacc => by
    subst hn
    have hc : ∀ c : Fin 0 → ZMod 2, comb [] 0 c = 0 := fun c => by simp [comb]
    change Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (dotK 24 acc (vecK 24 Qt acc)) = _
    have hq' := hq acc hacc
    simp only [List.length_nil, hc, add_zero]
    cases e : dotK 24 acc (vecK 24 Qt acc)
    · rw [e] at hq'
      simp only [Bool.false_eq_true, ↓reduceIte] at hq'
      rw [hq']
      simp
    · rw [e] at hq'
      simp only [↓reduceIte] at hq'
      rw [hq']
      simp
  | f :: F, n, hn, hF, acc, hacc => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨F.length, by rw [← hn]; rfl⟩
    have hm : F.length = m := by simpa using hn
    have hf : f < 2 ^ 24 := hF f List.mem_cons_self
    have hF' : ∀ g ∈ F, g < 2 ^ 24 := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    rw [qCountK_cons, qCountK_eq hq F m hm hF' acc hacc,
      qCountK_eq hq F m hm hF' (acc ^^^ f) (Nat.xor_lt_two_pow hacc hf)]
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ZMod 2).sum_comp, Fintype.sum_prod_type]
    have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [hu, Finset.sum_pair (by decide)]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have e : comb (f :: F) (m + 1) ((Fin.consEquiv fun _ => ZMod 2) (0, c)) = comb F m c := by
        rw [comb_cons]
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, zero_smul',
          zero_add]
      rw [e]
    · refine Finset.sum_congr rfl fun c _ => ?_
      have e : vecOf acc + comb (f :: F) (m + 1) ((Fin.consEquiv fun _ => ZMod 2) (1, c)) =
          vecOf (acc ^^^ f) + comb F m c := by
        rw [comb_cons]
        simp only [vecOf, toVecD_xor, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero,
          Fin.cons_succ, one_smul', add_assoc]
      rw [e]

theorem vecMul_eq (M x : Nat) : vecOf x ᵥ* rowsMatrix 24 (unpackR 24 M) = vecOf (vmF 24 M x) := by
  rw [vecOf, vecOf, ← toVecD_vecMulN, CFSG.KC.F2W.vecMulN_unpackR]

theorem mapImg_eq (Mt : Nat) : ∀ Y : List Nat,
    (List.rec (motive := fun _ => List Nat) List.nil
      (fun y _ ih => List.cons (Nat.xor (vecK 24 Mt y) y) ih) Y : List Nat) =
      Y.map fun y => Nat.xor (vmF 24 Mt y) y
  | [] => rfl
  | _ :: Y => congrArg (List.cons _) (mapImg_eq Mt Y)

private theorem listRec_all2 {P Q : Nat → Bool} : ∀ L : List Nat,
    (List.rec (motive := fun _ => Bool) true (fun f _ ih => CFSG.KLie.CT.andB (P f) (CFSG.KLie.CT.andB (Q f) ih)) L : Bool) =
      true → ∀ f ∈ L, P f = true ∧ Q f = true
  | [], _, f, hf => absurd hf List.not_mem_nil
  | g :: L, h, f, hf => by
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    obtain ⟨h2, h3⟩ := andB_iff.1 h2
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨h1, h2⟩
    · exact listRec_all2 L h3 f hf

theorem fixK_spec {Mt Qt k a b : Nat} {F Y : List Nat} (h : fixK 24 Mt Qt F Y k a b = true) :
    F.length = k ∧ Y.length + k = 24 ∧ a = 2 ^ k ∧ (∀ f ∈ F, f < 2 ^ 24 ∧ vmF 24 Mt f = f) ∧
      pivK 24 F 0 = true ∧ pivK 24 (Y.map fun y => Nat.xor (vmF 24 Mt y) y) 0 = true ∧
      qCountK 24 Qt F 0 = b := by
  unfold fixK at h
  obtain ⟨hk, h⟩ := andB_iff.1 h
  obtain ⟨hlen, h⟩ := andB_iff.1 h
  obtain ⟨ha, h⟩ := andB_iff.1 h
  obtain ⟨hF, h⟩ := andB_iff.1 h
  obtain ⟨hpF, h⟩ := andB_iff.1 h
  obtain ⟨-, h⟩ := andB_iff.1 h
  obtain ⟨hpY, hq⟩ := andB_iff.1 h
  rw [lenL_eq'] at hk hlen
  have hF' := listRec_all2 (P := fun f => Nat.blt f (pw2 24)) (Q := fun f => Nat.beq (vecK 24 Mt f) f)
    F hF
  rw [mapImg_eq] at hpY
  refine ⟨beq_iff'.1 hk, beq_iff'.1 hlen, by rw [← pw2_eq']; exact beq_iff'.1 ha,
    fun f hf => ⟨?_, beq_iff'.1 (hF' f hf).2⟩, hpF, hpY, beq_iff'.1 hq⟩
  have := (hF' f hf).1
  rw [blt_iff', pw2_eq'] at this
  exact this

theorem fixed_set {Mt : Nat} {F Y : List Nat} (hFfix : ∀ f ∈ F, vmF 24 Mt f = f)
    (hpF : pivK 24 F 0 = true) (hpY : pivK 24 (Y.map fun y => Nat.xor (vmF 24 Mt y) y) 0 = true)
    (hlen' : F.length + Y.length = 24) :
    {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 Mt) = v} = Set.range (comb F F.length) := by
  obtain ⟨hlowF, hndF⟩ := pivK_spec F 0 hpF
  obtain ⟨hlowZ, hndZ⟩ := pivK_spec _ 0 hpY
  set N := rowsMatrix 24 (unpackR 24 Mt)
  set Z := Y.map fun y => Nat.xor (vmF 24 Mt y) y
  have hlowF' : ∀ v ∈ F, lowK 24 v < 24 := fun v hv => (hlowF v hv).1
  have hlowZ' : ∀ v ∈ Z, lowK 24 v < 24 := fun v hv => (hlowZ v hv).1
  have hZl : Y.length ≤ Z.length := by simp [Z]
  have hFact : ∀ c : Fin F.length → ZMod 2, comb F F.length c ᵥ* N + comb F F.length c = 0 := by
    intro c
    rw [comb_act]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [vecMul_eq, hFfix _ (by rw [List.getD_eq_getElem _ _ i.2]; exact List.getElem_mem _),
      add_self', smul_zero']
  have hYact : ∀ d : Fin Y.length → ZMod 2,
      comb Y Y.length d ᵥ* N + comb Y Y.length d = comb Z Y.length d := by
    intro d
    rw [comb_act]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : Z.getD i 0 = Nat.xor (vmF 24 Mt (Y.getD i 0)) (Y.getD i 0) := by
      simp only [Z]
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ i.2, List.getElem_map]
    rw [vecMul_eq, hz, vecOf, vecOf, vecOf]
    change _ = d i • toVecD 24 (vmF 24 Mt (Y.getD i 0) ^^^ Y.getD i 0)
    rw [toVecD_xor]
  have hact_add : ∀ x y : Fin 24 → ZMod 2, (x + y) ᵥ* N + (x + y) = (x ᵥ* N + x) + (y ᵥ* N + y) :=
    fun x y => by rw [Matrix.add_vecMul, add_add_add_comm]
  let Φ : (Fin F.length → ZMod 2) × (Fin Y.length → ZMod 2) → (Fin 24 → ZMod 2) :=
    fun p => comb F F.length p.1 + comb Y Y.length p.2
  have hΦinj : Function.Injective Φ := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ e
    change comb F F.length c + comb Y Y.length d = comb F F.length c' + comb Y Y.length d' at e
    have e2 : comb F F.length (c + c') + comb Y Y.length (d + d') = 0 := by
      rw [comb_add, comb_add, add_add_add_comm, e, add_self']
    have e3 : (comb F F.length (c + c') + comb Y Y.length (d + d')) ᵥ* N +
        (comb F F.length (c + c') + comb Y Y.length (d + d')) = 0 := by
      rw [e2, Matrix.zero_vecMul, add_zero]
    rw [hact_add, hFact, zero_add, hYact] at e3
    have hd := piv_indep hZl hlowZ' hndZ _ e3
    rw [hd, comb_zero, add_zero] at e2
    have hc := piv_indep le_rfl hlowF' hndF _ e2
    have hc' : c = c' := funext fun i => addZ _ _ (congrFun hc i)
    have hd' : d = d' := funext fun i => addZ _ _ (congrFun hd i)
    rw [hc', hd']
  have hΦ : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hΦinj, ?_⟩
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_add]
    congr 1
  have hset : {v : Fin 24 → ZMod 2 | v ᵥ* N = v} = Set.range (comb F F.length) := by
    ext v
    constructor
    · intro hv
      obtain ⟨⟨c, d⟩, hcd⟩ := hΦ.2 v
      change comb F F.length c + comb Y Y.length d = v at hcd
      have h0 : (comb F F.length c + comb Y Y.length d) ᵥ* N +
          (comb F F.length c + comb Y Y.length d) = 0 := by
        rw [hcd, hv, add_self']
      rw [hact_add, hFact, zero_add, hYact] at h0
      have hd := piv_indep hZl hlowZ' hndZ _ h0
      refine ⟨c, ?_⟩
      rw [← hcd, hd, comb_zero, add_zero]
    · rintro ⟨c, rfl⟩
      exact eq_of_add' (hFact c)
  exact hset

theorem ncard_fix_eq (Mt : Nat) :
    {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 Mt) = v}.ncard =
      fixCount (unpackR 24 Mt) := by
  rw [fixCount]
  refine CFSG.Sporadic.Co1.Module.ncard_eq_countBelow
    (P := fun v => v ᵥ* rowsMatrix 24 (unpackR 24 Mt) = v) (p := isFixedN (unpackR 24 Mt))
    (fun x hx => ?_)
  rw [isFixedN, beq_iff_eq, CFSG.KC.F2W.vecMulN_unpackR]
  change _ ↔ vecOf x ᵥ* rowsMatrix 24 (unpackR 24 Mt) = vecOf x
  rw [vecMul_eq]
  exact ⟨fun h => by rw [h], fun h => toVecD_injective (CFSG.KC.F2W.vmF_lt 24 _ _) hx h⟩

theorem dot_vecMul (Qt x : Nat) : vecOf x ⬝ᵥ (vecOf x ᵥ* rowsMatrix 24 (unpackR 24 Qt)) =
    if dotN x (vmF 24 Qt x) = true then 1 else 0 := by
  rw [vecMul_eq, vecOf, vecOf, CFSG.Sporadic.Co1.Module.toVecD_dotProduct]

theorem ncard_fixQ_eq (Mt Qt : Nat) :
    {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 Mt) = v ∧
      v ⬝ᵥ (v ᵥ* rowsMatrix 24 (unpackR 24 Qt)) = 1}.ncard =
      fixCountQ (unpackR 24 Mt) (unpackR 24 Qt) := by
  rw [fixCountQ]
  refine CFSG.Sporadic.Co1.Module.ncard_eq_countBelow
    (P := fun v => v ᵥ* rowsMatrix 24 (unpackR 24 Mt) = v ∧
      v ⬝ᵥ (v ᵥ* rowsMatrix 24 (unpackR 24 Qt)) = 1)
    (p := fun x => isFixedN (unpackR 24 Mt) x && q0N (unpackR 24 Qt) x) (fun x hx => ?_)
  rw [Bool.and_eq_true, isFixedN, beq_iff_eq, CFSG.KC.F2W.vecMulN_unpackR, q0N,
    CFSG.KC.F2W.vecMulN_unpackR]
  change _ ↔ vecOf x ᵥ* rowsMatrix 24 (unpackR 24 Mt) = vecOf x ∧
    vecOf x ⬝ᵥ (vecOf x ᵥ* rowsMatrix 24 (unpackR 24 Qt)) = 1
  rw [vecMul_eq, dot_vecMul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1], ?_⟩
    rw [h2]
    rfl
  · rintro ⟨h1, h2⟩
    refine ⟨toVecD_injective (CFSG.KC.F2W.vmF_lt 24 _ _) hx h1, ?_⟩
    cases e : dotN x (vmF 24 Qt x)
    · rw [e] at h2
      exact absurd h2 (by decide)
    · rfl

theorem qCount_comb (Qt : Nat) {F : List Nat} (hFlt : ∀ f ∈ F, f < 2 ^ 24) :
    qCountK 24 Qt F 0 = (Finset.univ.filter fun c : Fin F.length → ZMod 2 =>
      comb F F.length c ⬝ᵥ (comb F F.length c ᵥ* rowsMatrix 24 (unpackR 24 Qt)) = 1).card := by
  have hq' : ∀ x < 2 ^ 24, (fun v : Fin 24 → ZMod 2 => v ⬝ᵥ (v ᵥ* rowsMatrix 24 (unpackR 24 Qt)))
      (vecOf x) = if dotK 24 x (vecK 24 Qt x) = true then 1 else 0 := fun x _ => by
    change vecOf x ⬝ᵥ (vecOf x ᵥ* rowsMatrix 24 (unpackR 24 Qt)) =
      if dotK 24 x (vmF 24 Qt x) = true then 1 else 0
    rw [dot_vecMul, dotK_dotN]
  have hcq := qCountK_eq (Qt := Qt) (q := fun v : Fin 24 → ZMod 2 =>
    v ⬝ᵥ (v ᵥ* rowsMatrix 24 (unpackR 24 Qt))) hq' F F.length rfl hFlt 0 (Nat.two_pow_pos 24)
  rw [hcq]
  refine congrArg Finset.card (Finset.filter_congr fun c _ => ?_)
  have h0 : vecOf 0 = 0 := toVecD_zero 24
  rw [h0, zero_add]

theorem fixK_sound_of {Mt Qt k a b : Nat} {F Y : List Nat}
    (h : F.length = k ∧ Y.length + k = 24 ∧ a = 2 ^ k ∧ (∀ f ∈ F, f < 2 ^ 24 ∧ vmF 24 Mt f = f) ∧
      pivK 24 F 0 = true ∧ pivK 24 (Y.map fun y => Nat.xor (vmF 24 Mt y) y) 0 = true ∧
      qCountK 24 Qt F 0 = b) :
    fixCount (unpackR 24 Mt) = a ∧ fixCountQ (unpackR 24 Mt) (unpackR 24 Qt) = b := by
  obtain ⟨hk, hlen', ha, hF', hpF, hpY, hq⟩ := h
  have hFlt : ∀ f ∈ F, f < 2 ^ 24 := fun f hf => (hF' f hf).1
  obtain ⟨hlowF, hndF⟩ := pivK_spec F 0 hpF
  have hinj := comb_injective le_rfl (fun v hv => (hlowF v hv).1) hndF
  have hset := fixed_set (fun f hf => (hF' f hf).2) hpF hpY (by omega)
  refine ⟨?_, ?_⟩
  · rw [← ncard_fix_eq, hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin, hk, ha]
  · have hset2 : {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 Mt) = v ∧
        v ⬝ᵥ (v ᵥ* rowsMatrix 24 (unpackR 24 Qt)) = 1} =
        comb F F.length '' {c | comb F F.length c ⬝ᵥ
          (comb F F.length c ᵥ* rowsMatrix 24 (unpackR 24 Qt)) = 1} := by
      ext v
      constructor
      · rintro ⟨h1, h2⟩
        have hv : v ∈ Set.range (comb F F.length) := hset ▸ h1
        obtain ⟨c, rfl⟩ := hv
        exact ⟨c, h2, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        refine ⟨?_, hc⟩
        have hm : comb F F.length c ∈ Set.range (comb F F.length) := ⟨c, rfl⟩
        rw [← hset] at hm
        exact hm
    rw [← ncard_fixQ_eq, hset2, Set.ncard_image_of_injective _ hinj, ← hq, qCount_comb Qt hFlt,
      ← Set.ncard_coe_finset]
    congr 1
    ext c
    simp

theorem fixK_sound {Mt Qt k a b : Nat} {F Y : List Nat} (h : fixK 24 Mt Qt F Y k a b = true) :
    fixCount (unpackR 24 Mt) = a ∧ fixCountQ (unpackR 24 Mt) (unpackR 24 Qt) = b :=
  fixK_sound_of (fixK_spec h)

end CFSG.KC.Co1Fix

end
