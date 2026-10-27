module

public import Certificates.Data.Kernel.OrbK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound

public section

namespace CFSG.KS.OrbK

open CFSG.KC.OrbK CFSG.AGLEmbedding.R3

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem vcode_nil (p : Nat) : vcode p [] = 0 := rfl

theorem vcode_cons (p x : Nat) (v : List Nat) : vcode p (x :: v) = x + p * vcode p v := rfl

theorem vdec_succ (p n c : Nat) : vdec p (n + 1) c = c % p :: vdec p n (c / p) := rfl

theorem dotK_cons_cons (a x : Nat) (as xs : List Nat) :
    dotK (a :: as) (x :: xs) = a * x + dotK as xs := rfl

theorem mvK_zero (p n : Nat) (v M : List Nat) : mvK p n v 0 M = [] := rfl

theorem mvK_succ (p n : Nat) (v : List Nat) (k : Nat) (M : List Nat) :
    mvK p n v (k + 1) M = dotK M v % p :: mvK p n v k (M.drop n) := rfl

theorem orbKAux_nil (p W n nacts FULL : Nat) (m : NMod) (T len S : Nat) :
    orbKAux p W n nacts FULL m [] T len S = Nat.beq (S ||| 1) FULL := rfl

theorem orbKAux_cons (p W n nacts FULL : Nat) (m : NMod) (j par : Nat) (rest : List (Nat × Nat))
    (T len S : Nat) :
    orbKAux p W n nacts FULL m ((j, par) :: rest) T len S =
      (Nat.blt j nacts && Nat.blt par len &&
        strictB (vcode p (mvK p n (vdec p n ((T >>> (W * par)) % 2 ^ W)) n
          (m.acts.getD j default).mat)) fun c =>
        strictB (T + (c <<< (W * len))) fun T' => strictB (S ||| (1 <<< c)) fun S' =>
        strictB (len + 1) fun len' => orbKAux p W n nacts FULL m rest T' len' S') := rfl

theorem orbKIni_nil (p W n nacts FULL : Nat) (m : NMod) (orb : List (Nat × Nat)) (T len S : Nat) :
    orbKIni p W n nacts FULL m orb [] T len S = orbKAux p W n nacts FULL m orb T len S := rfl

theorem orbKIni_cons (p W n nacts FULL : Nat) (m : NMod) (orb : List (Nat × Nat)) (v : List Nat)
    (vs : List (List Nat)) (T len S : Nat) :
    orbKIni p W n nacts FULL m orb (v :: vs) T len S =
      (vecOK p n v && strictB (vcode p v) fun c =>
        strictB (T + (c <<< (W * len))) fun T' => strictB (S ||| (1 <<< c)) fun S' =>
        strictB (len + 1) fun len' => orbKIni p W n nacts FULL m orb vs T' len' S') := rfl

@[expose] def Valid (p n : Nat) (v : List Nat) : Prop := v.length = n ∧ ∀ x ∈ v, x < p

theorem vdec_vcode (p : Nat) : ∀ (v : List Nat) (n : Nat), Valid p n v → vdec p n (vcode p v) = v
  | [], n, h => by
    rw [← h.1]
    rfl
  | x :: v, n, h => by
    obtain ⟨hl, hx⟩ := h
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨v.length, by simp at hl; omega⟩
    have hxp : x < p := hx x List.mem_cons_self
    have hp : 0 < p := by omega
    have hv : Valid p n v := ⟨by simpa using hl, fun y hy => hx y (List.mem_cons_of_mem _ hy)⟩
    rw [vcode_cons, vdec_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxp, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt hxp, Nat.zero_add, vdec_vcode p v n hv]

theorem vcode_lt (p : Nat) : ∀ (v : List Nat) (n : Nat), Valid p n v → vcode p v < p ^ n
  | [], n, h => by
    rw [← h.1, vcode_nil]
    simp
  | x :: v, n, h => by
    obtain ⟨hl, hx⟩ := h
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨v.length, by simp at hl; omega⟩
    have hxp : x < p := hx x List.mem_cons_self
    have hv : Valid p n v := ⟨by simpa using hl, fun y hy => hx y (List.mem_cons_of_mem _ hy)⟩
    have h1 := vcode_lt p v n hv
    rw [vcode_cons, pow_succ]
    have : p * (vcode p v + 1) ≤ p * p ^ n := Nat.mul_le_mul_left p h1
    nlinarith

theorem vcode_inj {p n : Nat} {v w : List Nat} (hv : Valid p n v) (hw : Valid p n w)
    (h : vcode p v = vcode p w) : v = w := by
  rw [← vdec_vcode p v n hv, ← vdec_vcode p w n hw, h]

theorem vcode_ne_zero {p : Nat} (hp : 0 < p) :
    ∀ v : List Nat, (∃ x ∈ v, x ≠ 0) → vcode p v ≠ 0
  | [], ⟨_, hx, _⟩ => by simp at hx
  | x :: v, ⟨y, hy, hy0⟩ => by
    rw [vcode_cons]
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := vcode_ne_zero hp v ⟨y, hy, hy0⟩
      have : 0 < p * vcode p v := Nat.mul_pos hp (Nat.pos_of_ne_zero this)
      omega

theorem allVecs_valid (p : Nat) : ∀ (n : Nat), ∀ c ∈ allVecs p n, Valid p n c
  | 0, c, hc => by
    simp only [allVecs, List.mem_singleton] at hc
    subst hc
    exact ⟨rfl, by simp⟩
  | n + 1, c, hc => by
    simp only [allVecs, List.mem_flatMap, List.mem_range, List.mem_map] at hc
    obtain ⟨a, ha, c', hc', rfl⟩ := hc
    obtain ⟨hl, hx⟩ := allVecs_valid p n c' hc'
    refine ⟨by simp [hl], fun x hx' => ?_⟩
    rcases List.mem_cons.1 hx' with rfl | hx'
    · exact ha
    · exact hx x hx'

theorem matVecL_valid {p n : Nat} (hp : 0 < p) (M c : List Nat) : Valid p n (matVecL p n M c) := by
  refine ⟨by simp [matVecL], fun x hx => ?_⟩
  simp only [matVecL, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact Nat.mod_lt _ hp

@[expose] def packW (W : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + 2 ^ W * packW W xs

theorem packW_append (W c : Nat) :
    ∀ xs : List Nat, packW W (xs ++ [c]) = packW W xs + c * 2 ^ (W * xs.length)
  | [] => by simp [packW]
  | x :: xs => by
    rw [List.cons_append, packW, packW, packW_append W c xs, List.length_cons, Nat.mul_succ,
      pow_add]
    ring

theorem packW_get (W : Nat) :
    ∀ xs : List Nat, (∀ x ∈ xs, x < 2 ^ W) → ∀ i < xs.length,
      (packW W xs >>> (W * i)) % 2 ^ W = xs.getD i 0
  | [], _, i, hi => by simp at hi
  | x :: xs, hx, i, hi => by
    have hxW : x < 2 ^ W := hx x List.mem_cons_self
    rcases i with _ | i
    · rw [Nat.mul_zero, Nat.shiftRight_zero, packW, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hxW]
      rfl
    · have e : W * (i + 1) = W + W * i := by ring
      rw [e, Nat.shiftRight_add, packW, Nat.shiftRight_eq_div_pow (x + 2 ^ W * packW W xs) W,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt hxW, Nat.zero_add,
        packW_get W xs (fun y hy => hx y (List.mem_cons_of_mem _ hy)) i (by simpa using hi)]
      rfl

@[expose] def Inv (p W n : Nat) (K : List (List Nat)) (T len S : Nat) : Prop :=
  len = K.length ∧ T = packW W (K.map (vcode p)) ∧ (∀ v ∈ K, Valid p n v) ∧
    ∀ c, S.testBit c = true → ∃ v ∈ K, vcode p v = c

theorem inv_nil (p W n : Nat) : Inv p W n [] 0 0 0 :=
  ⟨rfl, rfl, by simp, fun c hc => by simp at hc⟩

theorem inv_push {p W n : Nat} {K : List (List Nat)} {T len S : Nat} (h : Inv p W n K T len S)
    {w : List Nat} (hw : Valid p n w) :
    Inv p W n (K ++ [w]) (T + (vcode p w <<< (W * len))) (len + 1) (S ||| (1 <<< vcode p w)) := by
  obtain ⟨hl, hT, hv, hS⟩ := h
  refine ⟨by simp [hl], ?_, fun v hv' => ?_, fun c hc => ?_⟩
  · rw [List.map_append, List.map_singleton, packW_append, hT, Nat.shiftLeft_eq, hl,
      List.length_map]
  · rcases List.mem_append.1 hv' with hv' | hv'
    · exact hv v hv'
    · rw [List.mem_singleton.1 hv']
      exact hw
  · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_iff] at hc
    rcases hc with hc | rfl
    · obtain ⟨v, hv', rfl⟩ := hS c hc
      exact ⟨v, List.mem_append_left _ hv', rfl⟩
    · exact ⟨w, List.mem_append_right _ List.mem_cons_self, rfl⟩

theorem inv_get {p W n : Nat} {K : List (List Nat)} {T len S : Nat} (h : Inv p W n K T len S)
    (hW : p ^ n ≤ 2 ^ W) {par : Nat} (hpar : par < len) :
    vdec p n ((T >>> (W * par)) % 2 ^ W) = K.getD par [] := by
  obtain ⟨hl, hT, hv, -⟩ := h
  have hpK : par < K.length := hl ▸ hpar
  have hlt : ∀ x ∈ K.map (vcode p), x < 2 ^ W := by
    intro x hx
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hx
    exact Nat.lt_of_lt_of_le (vcode_lt p v n (hv v hv')) hW
  have hget : K.getD par [] = K[par] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpK]
  have hgetc : (K.map (vcode p)).getD par 0 = vcode p K[par] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpK]
  rw [hT, packW_get W _ hlt par (by simpa using hpK), hgetc, hget]
  exact vdec_vcode p _ n (hv _ (List.getElem_mem hpK))

theorem dotK_eq : ∀ (c L : List Nat),
    dotK L c = ∑ i ∈ Finset.range c.length, L.getD i 0 * c.getD i 0
  | [], L => by cases L <;> rfl
  | x :: c, [] => by
    change 0 = _
    simp
  | x :: c, a :: L => by
    rw [dotK_cons_cons, dotK_eq c L, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem mvK_eq (p n : Nat) (v M : List Nat) :
    ∀ k o, mvK p n v k (M.drop o) = (List.range k).map fun r => dotK (M.drop (o + n * r)) v % p
  | 0, o => by simp [mvK_zero]
  | k + 1, o => by
    have e : (M.drop o).drop n = M.drop (o + n) := by
      rw [List.drop_drop] <;> rw [Nat.add_comm]
    rw [mvK_succ, e, mvK_eq p n v M k (o + n), List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro r _
    have e2 : o + n * (r + 1) = o + n + n * r := by ring
    simp only [Function.comp_apply, e2]

theorem mvK_matVecL {p n : Nat} {v : List Nat} (hv : v.length = n) (M : List Nat) :
    mvK p n v n M = matVecL p n M v := by
  have h := mvK_eq p n v M n 0
  rw [List.drop_zero] at h
  rw [h, matVecL]
  apply List.map_congr_left
  intro r _
  rw [foldl_add_range, Nat.zero_add, dotK_eq, hv, Nat.zero_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem orbKAux_sound {p W : Nat} {m : NMod} (hp : 2 ≤ p) (hW : p ^ m.basis.length ≤ 2 ^ W) :
    ∀ (orb : List (Nat × Nat)) (K : List (List Nat)) (T len S : Nat),
      Inv p W m.basis.length K T len S →
      orbKAux p W m.basis.length m.acts.length (2 ^ p ^ m.basis.length - 1) m orb T len S = true →
      m.orbChk p ((allVecs p m.basis.length).filter fun c => !c.all (· == 0)) K orb = true
  | [], K, T, len, S, hI, h => by
    rw [orbKAux_nil] at h
    rw [NMod.orbChk, List.all_eq_true]
    intro c hc
    have hS := Nat.eq_of_beq_eq_true h
    rw [List.mem_filter] at hc
    obtain ⟨hc, hnz⟩ := hc
    have hcv := allVecs_valid p _ c hc
    have hnz' : ∃ x ∈ c, x ≠ 0 := by simpa [List.all_eq_true] using hnz
    have h0 := vcode_ne_zero (p := p) (by omega) c hnz'
    have hlt := vcode_lt p c _ hcv
    have hbit : (S ||| 1).testBit (vcode p c) = true := by
      rw [hS, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact hlt
    have hb1 : Nat.testBit 1 (vcode p c) = false := by
      have e1 : (1 : Nat) = 2 ^ 0 := rfl
      rw [e1, Nat.testBit_two_pow, decide_eq_false_iff_not]
      omega
    rw [Nat.testBit_or, hb1, Bool.or_false] at hbit
    obtain ⟨v, hv, hvc⟩ := hI.2.2.2 _ hbit
    rw [vcode_inj (hI.2.2.1 v hv) hcv hvc] at hv
    simpa using hv
  | (j, par) :: rest, K, T, len, S, hI, h => by
    rw [orbKAux_cons] at h
    simp only [strictB_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hj, hpar⟩, h⟩ := h
    rw [NMod.orbChk]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hj, hI.1 ▸ hpar⟩, ?_⟩
    have hpK : par < K.length := hI.1 ▸ hpar
    have hlen : (K.getD par []).length = m.basis.length := by
      have hget : K.getD par [] = K[par] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpK]
      rw [hget]
      exact (hI.2.2.1 _ (List.getElem_mem hpK)).1
    rw [inv_get hI hW hpar, mvK_matVecL hlen] at h
    exact orbKAux_sound hp hW rest _ _ _ _ (inv_push hI (matVecL_valid (by omega) _ _)) h

theorem orbKIni_sound {p W : Nat} {m : NMod} (hp : 2 ≤ p) (hW : p ^ m.basis.length ≤ 2 ^ W)
    (orb : List (Nat × Nat)) :
    ∀ (vs K : List (List Nat)) (T len S : Nat),
      Inv p W m.basis.length K T len S →
      orbKIni p W m.basis.length m.acts.length (2 ^ p ^ m.basis.length - 1) m orb vs T len S =
        true →
      m.orbChk p ((allVecs p m.basis.length).filter fun c => !c.all (· == 0)) (K ++ vs) orb = true
  | [], K, T, len, S, hI, h => by
    rw [orbKIni_nil] at h
    rw [List.append_nil]
    exact orbKAux_sound hp hW orb K T len S hI h
  | v :: vs, K, T, len, S, hI, h => by
    rw [orbKIni_cons] at h
    simp only [strictB_eq, Bool.and_eq_true] at h
    obtain ⟨hv, h⟩ := h
    unfold vecOK at hv
    simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hv
    have hvv : Valid p m.basis.length v := ⟨Nat.eq_of_beq_eq_true hv.1, hv.2⟩
    have := orbKIni_sound hp hW orb vs _ _ _ _ (inv_push hI hvv) h
    rwa [List.append_assoc, List.singleton_append] at this

theorem orbChk_of_orbK {p W : Nat} {m : NMod} {known : List (List Nat)} {orb : List (Nat × Nat)}
    (h : orbK p W m known orb = true) :
    m.orbChk p ((allVecs p m.basis.length).filter fun c => !c.all (· == 0)) known orb = true := by
  unfold orbK at h
  simp only [Bool.and_eq_true, Nat.ble_eq, strictB_eq] at h
  obtain ⟨⟨hp, hW⟩, h⟩ := h
  have := orbKIni_sound hp hW orb known [] 0 0 0 (inv_nil p W _) h
  rwa [List.nil_append] at this

theorem wfO_of_orbK {p W : Nat} {m : NMod} {orb : List (Nat × Nat)}
    (hm : m.acts.all (fun g => decide (g.mat.length = m.basis.length * m.basis.length)) = true)
    (h : orbK p W m (m.indep.map (·.1)) orb = true) : m.wfO p orb = true := by
  have hp : 2 ≤ p := by
    unfold orbK at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    exact h.1.1
  unfold NMod.wfO
  rw [hm, orbChk_of_orbK h, decide_eq_true hp]
  rfl

end CFSG.KS.OrbK

end
