module

public import Certificates.Data.Kernel.LocalQT.BaseS
public import CFSG.Certificates.Kernel.LocalQTRankBProved

public section

namespace CFSG.KC.LQT.BS.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem nthP_eq : ∀ (l : List (Nat × Nat)) (i : Nat), nthP l i = l.getD i (0, 0)
  | [], _ => rfl
  | x :: t, i => by
    change Bool.rec (motive := fun _ => Nat × Nat) (nthP t (Nat.sub i 1)) x (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      have e : Nat.beq (i + 1) 0 = false := rfl
      rw [e]
      dsimp only
      rw [nthP_eq t, List.getD_cons_succ]
      rfl

theorem foldl_slpStepA_size : ∀ (l : List (Nat × Nat)) (arr : Array (Array Nat)),
    (l.foldl slpStepA arr).size = arr.size + l.length
  | [], _ => rfl
  | p :: l, arr => by
    rw [List.foldl_cons, foldl_slpStepA_size l, List.length_cons]
    simp [slpStepA]
    omega

theorem slpTF_rep {n w : Nat} {TF : Nat → Nat} : ∀ (l : List (Nat × Nat)) (arr : Array (Array Nat)),
    (∀ j < arr.size, Rep n w (TF j) arr[j]!) → slpValidAux l arr.size = true →
    (∀ q < l.length, TF (arr.size + q) =
      mulW n w (TF (l.getD q (0, 0)).1) (TF (l.getD q (0, 0)).2)) →
    ∀ j < (l.foldl slpStepA arr).size, Rep n w (TF j) (l.foldl slpStepA arr)[j]!
  | [], _, ha, _, _ => ha
  | p :: l, arr, ha, hv, hT => by
    rw [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hp1, hp2⟩, hv⟩ := hv
    rw [List.foldl_cons]
    have hs : (slpStepA arr p).size = arr.size + 1 := by simp [slpStepA]
    apply slpTF_rep l
    · intro j hj
      rw [hs] at hj
      unfold slpStepA
      rcases Nat.lt_or_ge j arr.size with hjk | hjk
      · rw [getElem!_pos _ j (by simp; omega), Array.getElem_push_lt hjk, ← getElem!_pos arr j hjk]
        exact ha j hjk
      · have e : j = arr.size := by omega
        subst e
        rw [getElem!_pos _ arr.size (by simp), Array.getElem_push_eq]
        have := hT 0 (by simp)
        rw [Nat.add_zero, List.getD_cons_zero] at this
        rw [this]
        exact rep_mul (ha _ hp1) (ha _ hp2)
    · rw [hs]
      exact hv
    · intro q hq
      rw [hs]
      have := hT (q + 1) (by simp; omega)
      rw [show arr.size + (q + 1) = arr.size + 1 + q by omega, List.getD_cons_succ] at this
      exact this

theorem rowsT_go {w RS : Nat} {RT : Nat → Nat} : ∀ (G : List Nat) (t0 : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun g _ ih t => CFSG.KC.Ord.andB (allR 0 RS fun k => Nat.beq (RT (Nat.add (Nat.mul t RS) k)) (rowW w g k))
        (ih (Nat.succ t))) G t0 = true →
    ∀ t < G.length, ∀ k < RS, RT ((t0 + t) * RS + k) = rowW w (G.getD t 0) k
  | [], _, _, t, ht => by simp at ht
  | g :: G, t0, h, t, ht => by
    change CFSG.KC.Ord.andB (allR 0 RS fun k => Nat.beq (RT (Nat.add (Nat.mul t0 RS) k)) (rowW w g k))
      (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun g _ ih t => CFSG.KC.Ord.andB (allR 0 RS fun k => Nat.beq (RT (Nat.add (Nat.mul t RS) k))
          (rowW w g k)) (ih (Nat.succ t))) G (t0 + 1)) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro k hk
    cases t with
    | zero =>
      have := allR_true h.1 k hk
      rw [Nat.zero_add] at this
      rw [Nat.add_zero, List.getD_cons_zero]
      exact P.beq_iff.1 this
    | succ t =>
      rw [List.getD_cons_succ, show t0 + (t + 1) = t0 + 1 + t by omega]
      exact rowsT_go G (t0 + 1) h.2 t (by simpa using ht) k hk

theorem imgR_eq {w RS : Nat} {RT : Nat → Nat} {t x n : Nat} (hRS : n ≤ 64 * RS)
    (hr : ∀ k < RS, RT (t * RS + k) = rowW w x k) {p : Nat} (hp : p < n) :
    imgR w RS RT t p = imgW w x p := by
  have e1 : Nat.shiftRight p 6 = p / 64 := by
    change p >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land p 63 = p % 64 := Nat.and_two_pow_sub_one_eq_mod p 6
  change imgW w (RT (Nat.add (Nat.mul t RS) (Nat.shiftRight p 6))) (Nat.land p 63) = _
  rw [e1, e2]
  change imgW w (RT (t * RS + p / 64)) (p % 64) = _
  rw [hr _ (by omega), imgW_rowW _ _ _ _ (Nat.mod_lt _ (by decide)), Nat.div_add_mod]

theorem imgsR_eq (w RS : Nat) (RT : Nat → Nat) (t : Nat) :
    ∀ l : List Nat, imgsR w RS RT t l = l.map (imgR w RS RT t)
  | [] => rfl
  | x :: l => by
    change letLs (imgR w RS RT t x) (fun y => y :: imgsR w RS RT t l) = _
    rw [letLs_eq, imgsR_eq w RS RT t l, List.map_cons]

theorem imgsR_rep {n w RS : Nat} {RT : Nat → Nat} {t x : Nat} {s : Array Nat} (hRS : n ≤ 64 * RS)
    (hr : ∀ k < RS, RT (t * RS + k) = rowW w x k) (hx : Rep n w x s) {l : List Nat}
    (hl : ∀ y ∈ l, y < n) : imgsR w RS RT t l = applyTab s l := by
  rw [imgsR_eq, applyTab]
  exact List.map_congr_left fun y hy => by rw [imgR_eq hRS hr (hl y hy), (hx.2 y (hl y hy)).2]

theorem decW_go (w x : Nat) : ∀ (m i : Nat),
    Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
      (fun _ ih i => letLs (imgW w x i) fun y => List.cons y (ih (Nat.succ i))) m i =
    (List.range' i m).map (imgW w x)
  | 0, _ => rfl
  | m + 1, i => by
    change letLs (imgW w x i) (fun y => List.cons y (Nat.rec (motive := fun _ => Nat → List Nat)
      (fun _ => []) (fun _ ih i => letLs (imgW w x i) fun y => List.cons y (ih (Nat.succ i))) m
        (i + 1))) = _
    rw [letLs_eq, decW_go w x m (i + 1), List.range'_succ, List.map_cons]

theorem decW_codeK {w : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ w) :
    decW w l.length (codeK w l) = l := by
  rw [decW, decW_go]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
  rw [imgW_codeK l hl i h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

theorem codeK_cons (w x : Nat) (t : List Nat) : codeK w (x :: t) = x + 2 ^ w * codeK w t := by
  change Nat.add x (Nat.shiftLeft (codeK w t) w) = _
  change x + (codeK w t <<< w) = _
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem codeK_mod {w : Nat} : ∀ (l : List Nat) (m : Nat), (∀ x ∈ l, x < 2 ^ w) →
    codeK w l % 2 ^ (w * m) = codeK w (l.take m)
  | [], _, _ => by simp; rfl
  | x :: t, 0, _ => by
    rw [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, List.take_zero]
    rfl
  | x :: t, m + 1, hl => by
    have hx := hl x (List.mem_cons_self ..)
    rw [List.take_succ_cons, codeK_cons, codeK_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * m)),
      Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.add_mul_div_left _ _
        (Nat.two_pow_pos w), Nat.div_eq_of_lt hx, Nat.zero_add,
      codeK_mod t m fun y hy => hl y (List.mem_cons_of_mem _ hy)]

theorem keyC_eq (w nb x : Nat) : keyC w nb x = x % 2 ^ (w * nb) := by
  have e : Nat.shiftLeft 1 (Nat.mul w nb) = 2 ^ (w * nb) := by
    change 1 <<< (w * nb) = 2 ^ (w * nb)
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [keyC, e]
  exact Nat.and_two_pow_sub_one_eq_mod x _

theorem keyC_codeK {w nb : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ w) :
    keyC w nb (codeK w l) = codeK w (l.take nb) := by
  rw [keyC_eq, codeK_mod l nb hl]

theorem letN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.LQT.Syl.letN y k = k y := by
  cases y <;> rfl

theorem findS_go {w nb M : Nat} {E : Nat → Nat} {key : Nat} : ∀ (lg j : Nat), j < M →
    Nat.rec (motive := fun _ => Nat → Nat) (fun j => j)
      (fun b ih j => ih (CFSG.KC.LQT.Syl.letN (Nat.add j (Nat.shiftLeft 1 b)) fun j' =>
        Bool.rec (motive := fun _ => Nat) j j'
          (CFSG.KC.Ord.andB (Nat.blt j' M) (Nat.ble (keyC w nb (E j')) key)))) lg j < M
  | 0, _, hj => hj
  | lg + 1, j, hj => by
    change Nat.rec (motive := fun _ => Nat → Nat) (fun j => j)
      (fun b ih j => ih (CFSG.KC.LQT.Syl.letN (Nat.add j (Nat.shiftLeft 1 b)) fun j' =>
        Bool.rec (motive := fun _ => Nat) j j'
          (CFSG.KC.Ord.andB (Nat.blt j' M) (Nat.ble (keyC w nb (E j')) key)))) lg
      (CFSG.KC.LQT.Syl.letN (Nat.add j (Nat.shiftLeft 1 lg)) fun j' =>
        Bool.rec (motive := fun _ => Nat) j j'
          (CFSG.KC.Ord.andB (Nat.blt j' M) (Nat.ble (keyC w nb (E j')) key))) < M
    apply findS_go lg
    rw [letN_eq]
    cases hc : CFSG.KC.Ord.andB (Nat.blt (Nat.add j (Nat.shiftLeft 1 lg)) M)
        (Nat.ble (keyC w nb (E (Nat.add j (Nat.shiftLeft 1 lg)))) key)
    · exact hj
    · rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at hc
      exact hc.1

theorem memS_spec {w nb M lg : Nat} {E : Nat → Nat} {c : Nat} (hM : 0 < M)
    (h : memS w nb M lg E c = true) : ∃ j < M, E j = c :=
  ⟨_, findS_go lg 0 hM, P.beq_iff.1 h⟩

theorem rangeK_go : ∀ (m i : Nat), Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => List.cons i (ih (Nat.succ i))) m i = List.range' i m
  | 0, _ => rfl
  | m + 1, i => by
    change i :: Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
      (fun _ ih i => List.cons i (ih (Nat.succ i))) m (i + 1) = _
    rw [rangeK_go m (i + 1), List.range'_succ]

theorem rangeK_eq' (m : Nat) : rangeK m = List.range m := by
  rw [rangeK, rangeK_go, List.range_eq_range']

theorem fstT_eq (TF : Nat → Nat) : ∀ qp : List (Nat × Nat), fstT TF qp = qp.map fun p => TF p.1
  | [] => rfl
  | p :: qp => by
    change TF p.1 :: fstT TF qp = _
    rw [fstT_eq TF qp, List.map_cons]

theorem comLoop_trueR {nb : Nat} {app : Nat → List Nat → List Nat} {A : Nat → Array Nat}
    {T0 : List Nat} (hl0 : T0.length = nb) : ∀ (ts : List Nat) (rest : List Nat),
    (∀ t ∈ ts, app t T0 = applyTab (A t) T0) → nb * ts.length ≤ rest.length →
    (∀ q < ts.length, ∀ j < nb, rest.getD (nb * q + j) 0 = img (A (ts.getD q 0)) (T0.getD j 0)) →
    comLoop nb app T0 ts rest = true
  | [], _, _, _, _ => rfl
  | t :: ts, rest, hA, hlen, hc => by
    change CFSG.KC.Ord.andB (eqLW (takeK nb rest) (app t T0)) (comLoop nb app T0 ts (dropK nb rest)) = true
    rw [andB_eq, Bool.and_eq_true, eqLW_iff, takeK_eq, dropK_eq, hA t (List.mem_cons_self ..)]
    simp only [List.length_cons, Nat.mul_succ] at hlen
    refine ⟨?_, comLoop_trueR hl0 ts _ (fun s hs => hA s (List.mem_cons_of_mem _ hs))
      (by rw [List.length_drop]; omega) fun q hq j hj => ?_⟩
    · apply List.ext_getElem (by simp [applyTab, hl0]; omega)
      intro j h1 h2
      have hj : j < nb := by simp at h1; omega
      have e := hc 0 (by simp) j hj
      rw [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
      simp only [applyTab, List.getElem_map, List.getElem_take]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at e
      exact e
    · have e := hc (q + 1) (by simp; omega) j hj
      rw [List.getD_cons_succ, show nb * (q + 1) + j = nb + (nb * q + j) by rw [Nat.mul_succ]; omega]
        at e
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
      exact e

section Loop

variable {n nb : Nat} {G : List (Array Nat)} {Ul : List (List Nat)} {o : List Nat}

@[expose] def BInv (n nb : Nat) (G : List (Array Nat)) (Ul : List (List Nat)) (o : List Nat)
    (S : St) : Prop :=
  S.2.1.size = S.1.size ∧ 0 < S.1.size ∧ S.1[0]! = o ∧ (∀ T ∈ S.1.toList, T ∈ Ul) ∧
  (∀ y, S.2.2.contains y = true ↔ ∃ i < S.1.size, keyNat n nb S.1[i]! = y) ∧
  (∀ i < S.1.size, S.2.2.getD (keyNat n nb S.1[i]!) 0 = i) ∧
  (∀ i < S.1.size, 0 < i → S.2.1[i]! < i ∧ ∃ s ∈ G, S.1[i]! = applyTab s S.1[S.2.1[i]!]!)

theorem body_inv (hclo : ∀ T ∈ Ul, ∀ s ∈ G, applyTab s T ∈ Ul) {S : St}
    (hc : BInv n nb G Ul o S) {i : Nat} (hi : i < S.1.size) {s : Array Nat} (hsG : s ∈ G) :
    BInv n nb G Ul o (bodyB n nb i S.1[i]! S s) ∧
      (∃ new, BW.Pf.Ext S (bodyB n nb i S.1[i]! S s) new) ∧
      (bodyB n nb i S.1[i]! S s).2.2.contains (keyNat n nb (applyTab s S.1[i]!)) = true := by
  obtain ⟨hps, hpos, h0, hU, hmc, hmg, hpar⟩ := hc
  unfold bodyB
  by_cases hf : S.2.2.contains (keyNat n nb (applyTab s S.1[i]!)) = true
  · rw [ite_eq_left hf]
    exact ⟨⟨hps, hpos, h0, hU, hmc, hmg, hpar⟩, ⟨[], by simp [BW.Pf.Ext]⟩, hf⟩
  · rw [ite_eq_right hf]
    generalize hcdef : applyTab s S.1[i]! = c at hf
    have hnotN : ∀ j < S.1.size, keyNat n nb S.1[j]! ≠ keyNat n nb c := fun j hj e =>
      hf ((hmc _).2 ⟨j, hj, e⟩)
    have hext : BW.Pf.Ext S (S.1.push c, S.2.1.push i, S.2.2.insert (keyNat n nb c) S.1.size)
        [c] := by
      simp [BW.Pf.Ext]
    have hgetS : ∀ j < S.1.size, (S.1.push c)[j]! = S.1[j]! := fun j hj => ext_get hext hj
    have hgetN : (S.1.push c)[S.1.size]! = c := by
      rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]
    have hcU : c ∈ Ul := by
      rw [← hcdef]
      exact hclo _ (hU _ (get_mem hi)) s hsG
    refine ⟨⟨by simp [hps], by simp, by rw [hgetS 0 hpos, h0], ?_, ?_, ?_, ?_⟩, ⟨[c], hext⟩, ?_⟩
    · intro T hT
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hT
      rcases hT with hT | rfl
      · exact hU T hT
      · exact hcU
    · intro y
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hmc]
      constructor
      · rintro (rfl | ⟨j, hj, e⟩)
        · exact ⟨S.1.size, by simp, by rw [hgetN]⟩
        · exact ⟨j, by simp; omega, by rw [hgetS j hj, e]⟩
      · rintro ⟨j, hj, e⟩
        simp only [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inr ⟨j, hj, by rw [← hgetS j hj, e]⟩
        · exact Or.inl (by rw [← e, hgetN])
    · intro j hj
      rw [Std.HashMap.getD_insert]
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hgetS j hj, ite_eq_right (by rw [beq_iff_eq]; exact fun e => hnotN j hj e.symm)]
        exact hmg j hj
      · rw [hgetN, ite_eq_left (by rw [beq_iff_eq])]
    · intro j hj hj0
      simp only [Array.size_push] at hj
      have hpget : ∀ k < S.1.size, (S.2.1.push i)[k]! = S.2.1[k]! := by
        intro k hk
        rw [arr_getN, arr_getN, Array.toList_push, getD_append_left (by simp; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨h1, s', hs', h2⟩ := hpar j hj hj0
        rw [hpget j hj, hgetS j hj, hgetS _ (by omega)]
        exact ⟨h1, s', hs', h2⟩
      · have e : (S.2.1.push i)[S.1.size]! = i := by
          rw [arr_getN, Array.toList_push, ← hps]
          rw [show S.2.1.size = S.2.1.toList.length by simp, getD_append_len]
        rw [e, hgetN, hgetS i hi, ← hcdef]
        exact ⟨hi, s, hsG, rfl⟩
    · rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
      exact Or.inl rfl

theorem contains_mono {S S' : St} (hc : BInv n nb G Ul o S) (hc' : BInv n nb G Ul o S')
    {new : List (List Nat)} (he : BW.Pf.Ext S S' new) {y : Nat} (h : S.2.2.contains y = true) :
    S'.2.2.contains y = true := by
  obtain ⟨j, hj, e⟩ := (hc.2.2.2.2.1 y).1 h
  exact (hc'.2.2.2.2.1 y).2 ⟨j, by rw [ext_size he]; omega, by rw [ext_get he hj, e]⟩

theorem fold_inv (hclo : ∀ T ∈ Ul, ∀ s ∈ G, applyTab s T ∈ Ul) {i : Nat} {T : List Nat} :
    ∀ (Gs : List (Array Nat)) (S : St), (∀ s ∈ Gs, s ∈ G) → BInv n nb G Ul o S → i < S.1.size →
    S.1[i]! = T → BInv n nb G Ul o (Gs.foldl (bodyB n nb i T) S) ∧
      (∃ new, BW.Pf.Ext S (Gs.foldl (bodyB n nb i T) S) new) ∧
      ∀ s ∈ Gs, (Gs.foldl (bodyB n nb i T) S).2.2.contains (keyNat n nb (applyTab s T)) = true
  | [], S, _, hc, _, _ => ⟨hc, ⟨[], by simp [BW.Pf.Ext]⟩, fun s hs => by simp at hs⟩
  | s :: Gs, S, hG, hc, hi, hT => by
    rw [List.foldl_cons]
    obtain ⟨hc1, ⟨new1, he1⟩, hk1⟩ := body_inv (o := o) hclo hc hi (hG s (List.mem_cons_self ..))
    rw [hT] at hc1 he1 hk1
    have hi1 : i < (bodyB n nb i T S s).1.size := by rw [ext_size he1]; omega
    have hT1 : (bodyB n nb i T S s).1[i]! = T := by rw [ext_get he1 hi, hT]
    obtain ⟨hc2, ⟨new2, he2⟩, hk2⟩ := fold_inv hclo Gs (bodyB n nb i T S s)
      (fun s hs => hG s (List.mem_cons_of_mem _ hs)) hc1 hi1 hT1
    refine ⟨hc2, ⟨new1 ++ new2, ext_trans he1 he2⟩, fun s' hs' => ?_⟩
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact contains_mono hc1 hc2 he2 hk1
    · exact hk2 s' hs'

theorem toList_nodup {S : St} (hc : BInv n nb G Ul o S) : S.1.toList.Nodup := by
  obtain ⟨-, -, -, -, -, hmg, -⟩ := hc
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i j hi hj e
  simp only [Array.length_toList] at hi hj
  simp only [Array.getElem_toList] at e
  rw [← getElem!_pos S.1 i hi, ← getElem!_pos S.1 j hj] at e
  rw [← hmg i hi, ← hmg j hj, e]

theorem size_le {S : St} (hc : BInv n nb G Ul o S) : S.1.size ≤ Ul.length := by
  have := ((toList_nodup hc).subperm hc.2.2.2.1).length_le
  simpa using this

theorem loop_done (hclo : ∀ T ∈ Ul, ∀ s ∈ G, applyTab s T ∈ Ul) : ∀ (f i : Nat) (S : St),
    BInv n nb G Ul o S → i ≤ S.1.size →
    (∀ i' < i, ∀ s ∈ G, S.2.2.contains (keyNat n nb (applyTab s S.1[i']!)) = true) →
    Ul.length ≤ i + f →
    BInv n nb G Ul o (bfsLoopB n nb G f i S) ∧
      ∀ i' < (bfsLoopB n nb G f i S).1.size, ∀ s ∈ G,
        (bfsLoopB n nb G f i S).2.2.contains
          (keyNat n nb (applyTab s (bfsLoopB n nb G f i S).1[i']!)) = true
  | 0, i, S, hc, hi, hpre, hf => by
    have hs := size_le hc
    have e : bfsLoopB n nb G 0 i S = S := rfl
    rw [e]
    exact ⟨hc, fun i' hi' => hpre i' (by omega)⟩
  | f + 1, i, S, hc, hi, hpre, hf => by
    rw [bfsLoopB_succ]
    by_cases hlt : i < S.1.size
    · rw [ite_eq_left hlt]
      obtain ⟨hc1, ⟨new1, he1⟩, hk1⟩ := fold_inv (o := o) hclo G S (fun s hs => hs) hc hlt rfl
      apply loop_done hclo f (i + 1) _ hc1 (by rw [ext_size he1]; omega) _ (by omega)
      intro i' hi' s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
      · rw [ext_get he1 (by omega)]
        exact contains_mono hc hc1 he1 (hpre i' hi' s hs)
      · rw [ext_get he1 hlt]
        exact hk1 s hs
    · rw [ite_eq_right hlt]
      exact ⟨hc, fun i' hi' => hpre i' (by omega)⟩

theorem keys_nodupB {S : St} (hc : BInv n nb G Ul o S) :
    (S.1.toList.map (keyNat n nb)).Nodup := by
  obtain ⟨-, -, -, -, -, hmg, -⟩ := hc
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i j hi hj e
  simp only [List.length_map, Array.length_toList] at hi hj
  simp only [List.getElem_map, Array.getElem_toList] at e
  rw [← getElem!_pos S.1 i hi, ← getElem!_pos S.1 j hj] at e
  rw [← hmg i hi, ← hmg j hj, e]

end Loop

theorem impB_true {a b : Bool} (h : impB a b = true) (ha : a = true) : b = true := by
  rw [impB_eq, ha] at h
  simpa using h

theorem decW_codeK' {w r : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ w) (hr : l.length = r) :
    decW w r (codeK w l) = l := by
  subst hr
  exact decW_codeK hl

theorem entS_spec {w nb r M lg g : Nat} {app : Nat → List Nat → List Nat} {E PG : Nat → Nat}
    {oC zC j : Nat} (h : entS w nb r M lg g app E PG oC zC j = true) :
    (j + 1 < M → keyC w nb (E j) < keyC w nb (E (j + 1))) ∧
    (∀ t < g, memS w nb M lg E (codeK w (app t (decW w r (E j)))) = true) ∧
    (comW nb app (List.range g) (decW w r (E j)) = true → E j = oC ∨ E j = zC) ∧
    (E j = oC ∨ (Nat.land (PG j) 32767 < M ∧ Nat.land (Nat.shiftRight (PG j) 15) 7 < g ∧
      Nat.shiftRight (PG (Nat.land (PG j) 32767)) 18 < Nat.shiftRight (PG j) 18 ∧
      E j = codeK w (app (Nat.land (Nat.shiftRight (PG j) 15) 7)
        (decW w r (E (Nat.land (PG j) 32767)))))) := by
  rw [entS] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun hj => P.blt_iff.1 (impB_true h1 (P.blt_iff.2 hj)), fun t ht => ?_, fun hc => ?_, ?_⟩
  · rw [rangeK_eq', allL_eq, List.all_eq_true] at h2
    exact h2 t (List.mem_range.2 ht)
  · rw [rangeK_eq'] at h3
    have := impB_true h3 hc
    rw [orB_eq, Bool.or_eq_true, P.beq_iff, P.beq_iff] at this
    exact this
  · rw [orB_eq, Bool.or_eq_true, P.beq_iff, letB_eq, letB_eq] at h4
    rcases h4 with h4 | h4
    · exact Or.inl h4
    · simp only [Bool.and_eq_true, P.blt_iff, P.beq_iff] at h4
      exact Or.inr h4

end CFSG.KC.LQT.BS.Pf

end

public section

namespace CFSG.KC.LQT.BS

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.BS.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem baseS_sound_proved {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat)
    (zn gn gin hn hin k fuel M lg : Nat) (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true) :
    BaseCertS n B (slpTabsA ta.toArray tb.toArray prog) qp zn gn gin hn hin
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  rw [baseSK] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hTF0, hTF1, hKm, hRS, hK2, -, hqpb, hfive, hqinv, hginv, hhinv, hB,
    hrows, hMk, hMf, hmo, hmg, hmh, hnc⟩ := h
  obtain ⟨hzn, hgn, hgin, hhn, hhin⟩ := hfive
  have hnodes : ∀ q < prog.length, TF (2 + q) =
      mulW n w (TF (prog.getD q (0, 0)).1) (TF (prog.getD q (0, 0)).2) := by
    intro q hq
    have hKm' := Nat.le_of_ble_eq_true hKm
    rw [lenA_eq, Nat.add_eq, Nat.mul_eq] at hKm'
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, Nat.mul_zero] at hKm'
        omega
      · exact h0
    have hc : (2 + q) / m < K := by
      rw [Nat.div_lt_iff_lt_mul hm0]
      omega
    have := allR_true (hnd _ hc) ((2 + q) % m) (Nat.mod_lt _ hm0)
    rw [Nat.div_add_mod'] at this
    dsimp only at this
    have h2 : CFSG.KC.Ord.andB (Nat.ble 2 (2 + q)) (Nat.blt (2 + q) (Nat.add (lenA prog) 2)) = true := by
      rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, lenA_eq, Nat.add_eq]
      constructor <;> omega
    have := impB_true this h2
    rw [P.beq_iff, nthP_eq, show Nat.sub (2 + q) 2 = q by rw [Nat.sub_eq]; omega] at this
    exact this
  have hTs : (slpTabsA ta.toArray tb.toArray prog).size = prog.length + 2 := by
    rw [slpTabsA, foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  have hRepT : ∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
      Rep n w (TF j) (slpTabsA ta.toArray tb.toArray prog)[j]! := by
    rw [slpTabsA]
    apply slpTF_rep prog #[ta.toArray, tb.toArray]
    · intro j hj
      rcases j with _ | _ | j
      · rw [P.beq_iff.1 hTF0]
        exact rep_codeK hw hta
      · rw [P.beq_iff.1 hTF1]
        exact rep_codeK hw htb
      · simp at hj
    · exact slpOKK_spec' prog 2 hso
    · intro q hq
      exact hnodes q hq
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT ⊢
  have hNT : Nat.add (lenA prog) 2 = T.size := by rw [hTs, lenA_eq, Nat.add_eq]
  rw [hNT] at hqpb hzn hgn hgin hhn hhin
  rw [P.blt_iff] at hzn hgn hgin hhn hhin
  rw [allA_eq, List.all_eq_true] at hqpb hqinv
  have hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hqpb p hp
    rw [andB_eq, Bool.and_eq_true, P.blt_iff, P.blt_iff] at this
    exact this
  rw [allL_eq, List.all_eq_true] at hB
  have hB' : ∀ b ∈ B, b < n := fun b hb => P.blt_iff.1 (hB b hb)
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = qp.length := by rw [hGidef, List.length_map]
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  have hGrep : ∀ s ∈ G, ∃ c, Rep n w c s := by
    intro s hs
    rw [hGdef, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨TF p.1, hRepT _ (hq1' p hp).1⟩
  have hfor : ∀ l : List (Nat × Nat), (∀ p ∈ l, p.1 < T.size) →
      List.Forall₂ (fun c s => Rep n w c s) (l.map fun p => TF p.1) (l.map fun p => T[p.1]!) := by
    intro l hl
    induction l with
    | nil => exact List.Forall₂.nil
    | cons p l ih =>
      exact List.Forall₂.cons (hRepT _ (hl p (List.mem_cons_self ..)))
        (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
  have hpts : ptsW w B (fstT TF qp) = ptsOf B G := by
    rw [fstT_eq]
    exact ptsW_eq hB' (hfor qp fun p hp => (hq1' p hp).1)
  rw [hpts] at hmo hmg hmh
  have hov : Val n (ptsOf B G).length (ptsOf B G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hGrep s hs
      exact (hc.2 b (hB' b hb)).1
  have hlt2 : ∀ {l : List Nat}, (∀ x ∈ l, x < n) → ∀ x ∈ l, x < 2 ^ w :=
    fun hl x hx => Nat.lt_of_lt_of_le (hl x hx) hw
  have hRS' : n ≤ 64 * RS := Nat.le_of_ble_eq_true hRS
  have hrowsT : ∀ t (ht : t < qp.length), ∀ k' < RS,
      RT (t * RS + k') = rowW w (TF qp[t].1) k' := by
    intro t ht k' hk'
    have := rowsT_go (fstT TF qp) 0 hrows t (by rw [fstT_eq, List.length_map]; exact ht) k' hk'
    rw [Nat.zero_add, fstT_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht] at this
    exact this
  have happ : ∀ t < qp.length, ∀ l : List Nat, (∀ y ∈ l, y < n) →
      imgsR w RS RT t l = applyTab G[t]! l := by
    intro t ht l hl
    rw [hGj t ht]
    exact imgsR_rep hRS' (hrowsT t ht) (hRepT _ (hq1' _ (List.getElem_mem ht)).1) hl
  have hM : 0 < M := by
    rw [P.beq_iff.1 hMk]
    exact Nat.two_pow_pos k
  have hent : ∀ j < M, entS w (lenA B) (lenA (ptsOf B G)) M lg (lenA qp) (imgsR w RS RT) E PG
      (codeK w (ptsOf B G)) (codeK w (imgsW w (TF zn) (ptsOf B G))) j = true := by
    intro j hj
    have hK2' := Nat.le_of_ble_eq_true hK2
    rw [Nat.mul_eq] at hK2'
    have hL0 : 0 < L2 := by
      rcases Nat.eq_zero_or_pos L2 with h0 | h0
      · rw [h0, Nat.mul_zero] at hK2'
        omega
      · exact h0
    have hc : j / L2 < K2 := by
      rw [Nat.div_lt_iff_lt_mul hL0]
      omega
    have := hs _ hc
    rw [setS] at this
    dsimp only at this
    rw [hpts] at this
    have := allR_true this (j % L2) (Nat.mod_lt _ hL0)
    rw [Nat.div_add_mod'] at this
    exact impB_true this (P.blt_iff.2 hj)
  rw [lenA_eq, lenA_eq, lenA_eq] at hent
  have hval : ∀ d, ∀ j < M, Nat.shiftRight (PG j) 18 = d →
      Val n (ptsOf B G).length (decW w (ptsOf B G).length (E j)) ∧
        E j = codeK w (decW w (ptsOf B G).length (E j)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd
      rcases (entS_spec (hent j hj)).2.2.2 with h4 | ⟨hp, ht, hdep, he⟩
      · rw [h4, decW_codeK' (hlt2 hov.2) rfl]
        exact ⟨hov, rfl⟩
      · obtain ⟨hv, -⟩ := ih _ (hd ▸ hdep) _ hp rfl
        rw [he, happ _ ht _ hv.2]
        have hV : Val n (ptsOf B G).length (applyTab G[Nat.land (Nat.shiftRight (PG j) 15) 7]!
            (decW w (ptsOf B G).length (E (Nat.land (PG j) 32767)))) :=
          ⟨by rw [applyTab, List.length_map]; exact hv.1, applyTab_lt
            (hGj _ ht ▸ hRepT _ (hq1' _ (List.getElem_mem ht)).1) hv.2⟩
        rw [decW_codeK' (hlt2 hV.2) hV.1]
        exact ⟨hV, rfl⟩
  have hU : ∀ j < M, Val n (ptsOf B G).length (decW w (ptsOf B G).length (E j)) ∧
      E j = codeK w (decW w (ptsOf B G).length (E j)) := fun j hj => hval _ j hj rfl
  have hstrict : ∀ a b, a < b → b < M → keyC w B.length (E a) < keyC w B.length (E b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact Nat.lt_trans (ih h (by omega)) ((entS_spec (hent b (by omega))).1 hb)
      · exact (entS_spec (hent a (by omega))).1 hb
  have hkeyU : ∀ a < M, ∀ b < M, keyNat n B.length (decW w (ptsOf B G).length (E a)) =
      keyNat n B.length (decW w (ptsOf B G).length (E b)) → a = b := by
    intro a ha b hb e
    rw [keyNat_eq_iff (hU a ha).1 (hU b hb).1] at e
    have e2 : keyC w B.length (E a) = keyC w B.length (E b) := by
      rw [(hU a ha).2, (hU b hb).2, keyC_codeK (hlt2 (hU a ha).1.2),
        keyC_codeK (hlt2 (hU b hb).1.2), e]
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e2 (Nat.ne_of_lt (hstrict a b h hb))
    · exact h
    · exact absurd e2.symm (Nat.ne_of_lt (hstrict b a h ha))
  set Ul := (List.range M).map fun j => decW w (ptsOf B G).length (E j) with hUldef
  have hUl : ∀ {T'}, T' ∈ Ul ↔ ∃ j < M, decW w (ptsOf B G).length (E j) = T' := by
    intro T'
    rw [hUldef, List.mem_map]
    simp only [List.mem_range]
  have hUlv : ∀ T' ∈ Ul, Val n (ptsOf B G).length T' := by
    intro T' hT'
    obtain ⟨j, hj, rfl⟩ := hUl.1 hT'
    exact (hU j hj).1
  have hkey : ∀ T' ∈ Ul, ∀ V ∈ Ul, keyNat n B.length T' = keyNat n B.length V → T' = V := by
    intro T' hT' V hV e
    obtain ⟨a, ha, rfl⟩ := hUl.1 hT'
    obtain ⟨b, hb, rfl⟩ := hUl.1 hV
    rw [hkeyU a ha b hb e]
  have hUlnd : Ul.Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hkeyU a (List.mem_range.1 ha) b (List.mem_range.1 hb)
      (by rw [e])) List.nodup_range
  have hUllen : Ul.length = M := by rw [hUldef, List.length_map, List.length_range]
  have hprod : ∀ j < M, ∀ t < qp.length,
      applyTab G[t]! (decW w (ptsOf B G).length (E j)) ∈ Ul := by
    intro j hj t ht
    obtain ⟨j', hj', e⟩ := memS_spec hM ((entS_spec (hent j hj)).2.1 t ht)
    rw [happ t ht _ (hU j hj).1.2] at e
    have hV : Val n (ptsOf B G).length (applyTab G[t]! (decW w (ptsOf B G).length (E j))) :=
      ⟨by rw [applyTab, List.length_map]; exact (hU j hj).1.1, applyTab_lt
        (hGj _ ht ▸ hRepT _ (hq1' _ (List.getElem_mem ht)).1) (hU j hj).1.2⟩
    refine hUl.2 ⟨j', hj', ?_⟩
    rw [e, decW_codeK' (hlt2 hV.2) hV.1]
  have hclo : ∀ T' ∈ Ul, ∀ s ∈ G, applyTab s T' ∈ Ul := by
    intro T' hT' s hs
    obtain ⟨j, hj, rfl⟩ := hUl.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
    have ht' : t < qp.length := by omega
    rw [← getElem!_pos G t ht]
    exact hprod j hj t ht'
  have hoU : ptsOf B G ∈ Ul := by
    obtain ⟨j, hj, e⟩ := memS_spec hM hmo
    refine hUl.2 ⟨j, hj, ?_⟩
    rw [e, decW_codeK' (hlt2 hov.2) rfl]
  have hS0 : BInv n B.length G Ul (ptsOf B G) (#[ptsOf B G], #[0],
      (∅ : Std.HashMap Nat Nat).insert (keyNat n B.length (ptsOf B G)) 0) := by
    have hget : ∀ i < 1, (#[ptsOf B G] : Array (List Nat))[i]! = ptsOf B G := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rfl
    refine ⟨rfl, by simp, rfl, fun T' hT' => ?_, fun y => ?_, fun i hi => ?_, fun i hi hi0 => ?_⟩
    · simp only [List.mem_singleton] at hT'
      rw [hT']
      exact hoU
    · simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        rfl
    · have hi' : i < 1 := by simpa using hi
      rw [hget i hi']
      simp only [Std.HashMap.getD_insert, beq_self_eq_true, ite_true]
      omega
    · have hi' : i < 1 := by simpa using hi
      omega
  have hMf' := Nat.le_of_ble_eq_true hMf
  obtain ⟨hcf, hdone⟩ := loop_done hclo fuel 0 _ hS0 (Nat.zero_le _)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [hUllen]; omega)
  generalize hSf : bfsLoopB n B.length G fuel 0 (#[ptsOf B G], #[0],
    (∅ : Std.HashMap Nat Nat).insert (keyNat n B.length (ptsOf B G)) 0) = S at hcf hdone
  have hbe : bfsEnumB n B G Gi fuel = (S.1, S.2.1, (List.range S.1.size).foldl (fun acc i =>
      (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, hSf]
  obtain ⟨hps, hpos, h0, hSU, hmc, hmgS, hpar⟩ := hcf
  have hv : ∀ T' ∈ S.1.toList, Val n (ptsOf B G).length T' := fun T' hT' => hUlv T' (hSU T' hT')
  have hfind : ∀ i < S.1.size, ∀ t < qp.length, ∃ k' < S.1.size,
      S.1[k']! = applyTab G[t]! S.1[i]! := by
    intro i hi t ht
    have hs : G[t]! ∈ G := by rw [getElem!_pos G t (by omega)]; exact List.getElem_mem _
    obtain ⟨k', hk', e⟩ := (hmc _).1 (hdone i hi _ hs)
    refine ⟨k', hk', hkey _ (hSU _ (get_mem hk')) _ (hclo _ (hSU _ (get_mem hi)) _ hs) e⟩
  have hreach : ∀ d, ∀ j < M, Nat.shiftRight (PG j) 18 = d →
      decW w (ptsOf B G).length (E j) ∈ S.1.toList := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd
      rcases (entS_spec (hent j hj)).2.2.2 with h4 | ⟨hp, ht, hdep, he⟩
      · rw [h4, decW_codeK' (hlt2 hov.2) rfl, ← h0]
        exact get_mem hpos
      · obtain ⟨i', hi', e⟩ := mem_idx (ih _ (hd ▸ hdep) _ hp rfl)
        obtain ⟨k', hk', e'⟩ := hfind i' hi' _ ht
        have hpU := hU _ hp
        rw [he, happ _ ht _ hpU.1.2, ← e]
        have hV : Val n (ptsOf B G).length (applyTab G[Nat.land (Nat.shiftRight (PG j) 15) 7]!
            S.1[i']!) := by
          rw [e]
          exact ⟨by rw [applyTab, List.length_map]; exact hpU.1.1, applyTab_lt
            (hGj _ ht ▸ hRepT _ (hq1' _ (List.getElem_mem ht)).1) hpU.1.2⟩
        rw [decW_codeK' (hlt2 hV.2) hV.1, ← e']
        exact get_mem hk'
  have hsize : S.1.size = M := by
    apply Nat.le_antisymm
    · have := ((toList_nodup ⟨hps, hpos, h0, hSU, hmc, hmgS, hpar⟩).subperm hSU).length_le
      simp only [Array.length_toList] at this
      omega
    · have := (hUlnd.subperm fun T' hT' => by
        obtain ⟨j, hj, rfl⟩ := hUl.1 hT'
        exact hreach _ j hj rfl).length_le
      simp only [Array.length_toList] at this
      omega
  rw [hbe]
  dsimp only
  have hinvq : ∀ a ∈ qp, ∀ q < n, img T[a.2]! (img T[a.1]! q) = q := fun a ha =>
    rep_inv (hRepT a.1 (hq1' a ha).1) (hRepT a.2 (hq1' a ha).2) hw (P.beq_iff.1 (hqinv a ha))
  have hclget : ∀ i < S.1.size, ∀ j < (G ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * (G.length + Gi.length) + j]! =
      S.2.2.getD (keyNat n B.length (applyTab (G ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    rw [arr_getN, cl_fold, ← List.length_append]
    exact (flatMap_getD (G ++ Gi) _ S.1.size).2 i hi j hj
  have hidx : ∀ i < S.1.size, ∀ {s : Array Nat} {k' : Nat}, k' < S.1.size →
      S.1[k']! = applyTab s S.1[i]! →
      S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0 = k' := by
    intro i _ s k' hk' e
    rw [← e]
    exact hmgS k' hk'
  unfold BaseCertS
  refine ⟨hq1', hzn, hgn, hgin, hhn, hhin, ?_⟩
  have hm1 : (qp.map fun p => (T[p.1]!, T[p.2]!)).map Prod.fst = G := by
    rw [List.map_map, hGdef]
    rfl
  have hm2 : (qp.map fun p => (T[p.1]!, T[p.2]!)).map Prod.snd = Gi := by
    rw [List.map_map, hGidef]
    rfl
  unfold BaseCert
  rw [hm1, hm2]
  refine ⟨?_, rep_inv (hRepT gn hgn) (hRepT gin hgin) hw (P.beq_iff.1 hginv),
    rep_inv (hRepT hn hhn) (hRepT hin hhin) hw (P.beq_iff.1 hhinv), ?_,
    by rw [hsize]; exact P.beq_iff.1 hMk, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq
    rw [List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact hinvq a ha q hq
  · refine ⟨hpos, h0, hps, hpar, keys_nodupB ⟨hps, hpos, h0, hSU, hmc, hmgS, hpar⟩,
      fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · obtain ⟨k', hk', e⟩ := hfind i hi j (by omega)
      rw [hclget i hi j (by simp; omega), getBang_append_left hj, hidx i hi hk' e]
      exact ⟨hk', e⟩
    · have hjq : j < qp.length := by omega
      have hmem : applyTab Gi[j]! S.1[i]! ∈ S.1.toList := by
        apply closed_inv (s := G[j]!) (n := n)
        · intro q hq
          rw [hGj j hjq, hGij j hjq]
          exact hinvq _ (List.getElem_mem _) q hq
        · exact fun U hU => (hv U hU).2
        · intro U hU
          obtain ⟨i', hi', rfl⟩ := mem_idx hU
          obtain ⟨k', hk', e⟩ := hfind i' hi' j hjq
          rw [← e]
          exact get_mem hk'
        · exact get_mem hi
      obtain ⟨k', hk', e⟩ := mem_idx hmem
      rw [Nat.add_assoc, hclget i hi _ (by simp; omega), getBang_append_right hj,
        hidx i hi hk' e]
      exact ⟨hk', e⟩
  · intro T' hT' hcond
    obtain ⟨j, hj, rfl⟩ := hUl.1 (hSU T' hT')
    have hTv := (hU j hj).1
    have hL : (ptsOf B G).length = B.length + B.length * qp.length := by
      simp [ptsOf, List.length_flatMap, hGdef, Function.comp_def, List.map_const',
        List.sum_replicate, Nat.mul_comm]
    have hcw : comW B.length (imgsR w RS RT) (List.range qp.length)
        (decW w (ptsOf B G).length (E j)) = true := by
      rw [comW_eq, takeK_eq, dropK_eq]
      apply comLoop_trueR (A := fun t => G.getD t #[])
        (by rw [List.length_take, hTv.1, hL]; omega)
      · intro t ht
        rw [List.mem_range] at ht
        rw [happ t ht _ (fun x hx => hTv.2 x (List.mem_of_mem_take hx)),
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
          getElem!_pos G t (by omega)]
      · rw [List.length_drop, hTv.1, hL, List.length_range]
        omega
      · intro q hq j' hj'
        rw [List.length_range] at hq
        have hrq : (List.range qp.length).getD q 0 = q := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_range hq, Option.getD_some]
        rw [hrq, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD (l := List.take _ _), List.getElem?_take_of_lt hj',
          ← List.getD_eq_getElem?_getD, show B.length + (B.length * q + j') =
            B.length * (1 + q) + j' by rw [Nat.mul_add, Nat.mul_one]; omega]
        exact hcond q (by rw [hGl]; exact hq) j' hj'
    rcases (entS_spec (hent j hj)).2.2.1 hcw with e | e
    · left
      rw [e, decW_codeK' (hlt2 hov.2) rfl]
    · right
      have hz := hRepT zn hzn
      rw [e, imgsW_rep hz hov.2]
      exact decW_codeK' (hlt2 (applyTab_lt hz hov.2)) (by rw [applyTab, List.length_map])
  · obtain ⟨j, hj, e⟩ := memS_spec hM hmg
    rw [conj_tab (hRepT zn hzn) (hRepT gn hgn) (hRepT gin hgin) hov.2] at e
    have := hreach _ j hj rfl
    rwa [e, decW_codeK' (hlt2 (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact conj_lt (hRepT zn hzn) (hRepT gn hgn) (hRepT gin hgin) (hov.2 y hy)))
      (by rw [List.length_map])] at this
  · obtain ⟨j, hj, e⟩ := memS_spec hM hmh
    rw [conj_tab (hRepT zn hzn) (hRepT hn hhn) (hRepT hin hhin) hov.2] at e
    have := hreach _ j hj rfl
    rwa [e, decW_codeK' (hlt2 (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact conj_lt (hRepT zn hzn) (hRepT hn hhn) (hRepT hin hhin) (hov.2 y hy)))
      (by rw [List.length_map])] at this
  · rw [anyL_eq, List.any_eq_true] at hnc
    obtain ⟨b, hb, hne⟩ := hnc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
    refine ⟨j, hj, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hbn := hB' _ hb
    rw [notB_eq, Bool.not_eq_true', ← Bool.not_eq_true, P.beq_iff,
      conj_rep (hRepT zn hzn) (hRepT hn hhn) (hRepT hin hhin) hbn,
      conj_rep (hRepT zn hzn) (hRepT gn hgn) (hRepT gin hgin) hbn,
      conj_rep (hRepT zn hzn) (hRepT gn hgn) (hRepT gin hgin)
        (conj_lt (hRepT zn hzn) (hRepT hn hhn) (hRepT hin hhin) hbn),
      conj_rep (hRepT zn hzn) (hRepT hn hhn) (hRepT hin hhin)
        (conj_lt (hRepT zn hzn) (hRepT gn hgn) (hRepT gin hgin) hbn)] at hne
    exact hne

end CFSG.KC.LQT.BS

end
