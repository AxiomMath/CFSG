module

public import Certificates.Data.Kernel.Co1LeafQ
public import CFSG.Certificates.Kernel.Co1LeafPSound
import CFSG.Certificates.Kernel.VecKRegs
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.KC.Co1LeafQ

open CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1BBound CFSG.KC.Co1LeafP

section Lemmas

open CFSG.KC.Co1Leaf (selK crdK strictL)
open CFSG.KLie.CT (andB pw2 bit)

@[expose] noncomputable def lqX (r : ℕ → ℕ) (S n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun s acc => if S.testBit s then r s ^^^ acc else acc) n

theorem lqX_succ (r : ℕ → ℕ) (S n : ℕ) :
    lqX r S (n + 1) = if S.testBit n then r n ^^^ lqX r S n else lqX r S n := rfl

theorem lqX_zero (r : ℕ → ℕ) (S : ℕ) : lqX r S 0 = 0 := rfl

theorem lqX_shift (r : ℕ → ℕ) (S : ℕ) : ∀ n,
    lqX r S (n + 1) = (if S.testBit 0 then r 0 else 0) ^^^ lqX (fun s => r (s + 1)) (S >>> 1) n
  | 0 => by
    rw [lqX_succ]
    cases S.testBit 0 <;> simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte, lqX_zero,
      Nat.xor_zero, Nat.zero_xor]
  | n + 1 => by
    rw [lqX_succ, lqX_shift r S n, lqX_succ, Nat.testBit_shiftRight, Nat.add_comm 1 n]
    cases S.testBit (n + 1) <;> simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
    exact lp_x3 _ _ _

theorem lqX_congr {r r' : ℕ → ℕ} {S : ℕ} : ∀ {n}, (∀ s < n, r s = r' s) → lqX r S n = lqX r' S n
  | 0, _ => rfl
  | n + 1, h => by
    rw [lqX_succ, lqX_succ, lqX_congr fun s hs => h s (by omega), h n (by omega)]

theorem lq_selK_X : ∀ (L : List ℕ) (S : ℕ), selK L S = lqX (fun s => L.getD s 0) S L.length
  | [], _ => rfl
  | x :: L, S => by
    rw [List.length_cons, lqX_shift, List.getD_cons_zero]
    have e : (fun s => (x :: L).getD (s + 1) 0) = fun s => L.getD s 0 := by
      funext s
      rw [List.getD_cons_succ]
    rw [e, ← lq_selK_X L]
    cases hS : S.testBit 0
    · rw [lp_selK_f hS]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
    · rw [lp_selK_t hS]
      simp only [eq_self_iff_true, ↓reduceIte]

theorem lqX_lt {r : ℕ → ℕ} {S : ℕ} : ∀ {n}, (∀ s < n, r s < 2 ^ 24) → lqX r S n < 2 ^ 24
  | 0, _ => Nat.two_pow_pos 24
  | n + 1, h => by
    rw [lqX_succ]
    have := lqX_lt (S := S) (n := n) fun s hs => h s (by omega)
    split_ifs
    · exact lp_xor_lt (h n (by omega)) this
    · exact this

theorem lq_f_X {XB : ℕ → ℕ} {BT : List ℕ} {f : ℕ → ℕ} (hf : Equi XB BT f) {r : ℕ → ℕ} {S : ℕ} :
    ∀ {n}, (∀ s < n, r s < 2 ^ 24) → f (lqX r S n) = lqX (fun s => f (r s)) S n
  | 0, _ => lp_f0 hf
  | n + 1, h => by
    rw [lqX_succ, lqX_succ]
    have hlt := lqX_lt (S := S) (n := n) fun s hs => h s (by omega)
    have ih := lq_f_X hf (S := S) (n := n) fun s hs => h s (by omega)
    split_ifs
    · rw [hf.add _ _ (h n (by omega)) hlt, ih]
    · exact ih

theorem lq_strictLL (y : ℕ) (k : ℕ → List (List ℕ)) : strictLL y k = k y := by
  cases y <;> rfl

theorem lq_imgQ (x : ℕ) : ∀ IM : List (List ℕ), imgQ IM x = IM.map fun L => selK L x
  | [] => rfl
  | L :: IM => by
    rw [List.map_cons, ← lq_imgQ x IM]
    change strictL (selK L x) (fun v => v :: imgQ IM x) = _
    exact lp_strictL _ _

theorem lq_bit (S s : ℕ) : bit S s = S.testBit s := by
  change Nat.beq (Nat.land (Nat.shiftRight S s) 1) 1 = _
  rw [lp_bit0]
  change (S >>> s).testBit 0 = _
  rw [Nat.testBit_shiftRight, Nat.add_zero]

variable {XB : ℕ → ℕ} {BT U : List ℕ}

theorem lq_maskCodes (i S : ℕ) (cs : List ℕ) : ∀ n, sumU BT U (maskCodes i S cs n) =
    lqX (fun s => slotU BT U (32 * i + s)) S n ^^^ sumU BT U cs
  | 0 => (Nat.zero_xor _).symm
  | n + 1 => by
    change sumU BT U (Bool.rec (motive := fun _ => List ℕ) (maskCodes i S cs n)
      ((32 * i + n) :: maskCodes i S cs n) (bit S n)) = _
    rw [lqX_succ, lq_bit]
    cases S.testBit n <;> simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
    · exact lq_maskCodes i S cs n
    · change slotU BT U (32 * i + n) ^^^ sumU BT U (maskCodes i S cs n) = _
      rw [lq_maskCodes i S cs n, Nat.xor_assoc]

theorem lq_candsN_mem {E : List ℕ} {IM : List (List ℕ)} {x : ℕ} (hx : memK XB (selK E x) = true) :
    ∀ n, x < n → imgQ IM x ∈ candsN XB E IM n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    change imgQ IM x ∈ Bool.rec (motive := fun _ => List (List ℕ)) (candsN XB E IM n)
      (imgQ IM n :: candsN XB E IM n) (memK XB (selK E n))
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · cases memK XB (selK E n)
      · exact lq_candsN_mem hx n h
      · exact List.mem_cons_of_mem _ (lq_candsN_mem hx n h)
    · rw [hx]
      exact List.mem_cons_self

theorem lq_candQ_sub {R P : List (List ℕ)} {acc : List (List (List ℕ))} :
    ∀ CL : List (List ℕ), ∀ y ∈ acc, y ∈ candQ XB R P CL acc
  | [], _, hy => hy
  | C :: CL, y, hy => by
    change y ∈ Bool.rec (motive := fun _ => List (List (List ℕ))) (candQ XB R P CL acc)
      ((P ++ [C]) :: candQ XB R P CL acc) (passQ XB R C)
    cases passQ XB R C
    · exact lq_candQ_sub CL y hy
    · exact List.mem_cons_of_mem _ (lq_candQ_sub CL y hy)

theorem lq_candQ_mem {R P : List (List ℕ)} {acc : List (List (List ℕ))} {C : List ℕ}
    (hC : passQ XB R C = true) : ∀ CL : List (List ℕ), C ∈ CL → P ++ [C] ∈ candQ XB R P CL acc
  | [], h => by cases h
  | D :: CL, h => by
    change P ++ [C] ∈ Bool.rec (motive := fun _ => List (List (List ℕ))) (candQ XB R P CL acc)
      ((P ++ [D]) :: candQ XB R P CL acc) (passQ XB R D)
    rcases List.mem_cons.1 h with rfl | h
    · rw [hC]
      exact List.mem_cons_self
    · cases passQ XB R D
      · exact lq_candQ_mem hC CL h
      · exact List.mem_cons_of_mem _ (lq_candQ_mem hC CL h)

theorem lq_stepQ_mem {CL : List (List ℕ)} {T : List (List ℕ)} {C : List ℕ} (hC : C ∈ CL) :
    ∀ (Ps : List (List (List ℕ))) (P : List (List ℕ)), P ∈ Ps →
      passQ XB (prepQ P T) C = true → P ++ [C] ∈ stepQ XB CL T Ps
  | [], _, h, _ => by cases h
  | Q :: Ps, P, hP, hc => by
    change P ++ [C] ∈ candQ XB (prepQ Q T) Q CL (stepQ XB CL T Ps)
    rcases List.mem_cons.1 hP with rfl | hP
    · exact lq_candQ_mem hc CL hC
    · exact lq_candQ_sub CL _ (lq_stepQ_mem hC Ps P hP hc)

theorem lq_passQ {P : List (List ℕ)} {C : List ℕ} : ∀ T : List (List ℕ),
    (∀ t ∈ T, Nat.beq (bitN (memK XB (sumQ P t.tail.tail ^^^ selK C (t.tail.headD 0))))
      (t.headD 2) = true) → passQ XB (prepQ P T) C = true
  | [], _ => rfl
  | t :: T, h => by
    have h1 := h t List.mem_cons_self
    have h2 := lq_passQ T fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    change passQ XB (strictLL (sumQ P t.tail.tail) fun F =>
      (t.headD 2 :: t.tail.headD 0 :: F :: []) :: prepQ P T) C = true
    rw [lq_strictLL]
    change andB (Nat.beq (bitN (memK XB (sumQ P t.tail.tail ^^^ selK C (t.tail.headD 0))))
      (t.headD 2)) (passQ XB (prepQ P T) C) = true
    rw [h1, h2]
    all_goals rfl

theorem lq_fixK {nb i : ℕ} : ∀ cs : List ℕ, fixK nb i cs = true → ∀ c ∈ cs, c / 32 < i ∧ c % 32 < nb
  | [], _, _, hc => by cases hc
  | c :: cs, h, c', hc' => by
    obtain ⟨h1, h⟩ := lp_andB h
    obtain ⟨h2, h3⟩ := lp_andB h
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩
    · exact lq_fixK cs h3 c' hc'

theorem lq_fixQ {nb i : ℕ} : ∀ T : List (List ℕ), fixQ nb i T = true → ∀ t ∈ T,
    ∀ c ∈ t.tail.tail, c / 32 < i ∧ c % 32 < nb
  | [], _, _, ht => by cases ht
  | t :: T, h, t', ht' => by
    obtain ⟨-, h⟩ := lp_andB h
    obtain ⟨h2, h3⟩ := lp_andB h
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact lq_fixK _ h2
    · exact lq_fixQ T h3 t' ht'

theorem lq_convQ_mem {nb i : ℕ} : ∀ (T : List (List ℕ)) (t : List ℕ), t ∈ T →
    (t.headD 2 :: maskCodes i (t.tail.headD 0) t.tail.tail nb) ∈ convQ nb i T
  | [], _, h => by cases h
  | t :: T, t', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lq_convQ_mem T t' h)

theorem lq_levelsQ {IMS : List (List (List ℕ))} : ∀ (Es : List (List ℕ)) (Ms Us : List ℕ)
    (Ts CLs : List (List (List ℕ))) (i : ℕ), levelsQ XB BT U IMS Es Ms Us Ts CLs i = true →
    Es.length = Us.length ∧ Ts.length = Us.length ∧ CLs.length = Us.length ∧ ∀ j < Us.length,
      levelQ XB BT U (i + j) (Es.getD j []) (Ms.getD j 0) (Us.getD j 0) (Ts.getD j [])
        (getLLP IMS (i + j)) (CLs.getD j []) = true
  | [], [], [], [], [], _, _ => ⟨rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], [], [], [], _ :: _, _, h => absurd h Bool.false_ne_true
  | [], [], [], _ :: _, _, _, h => absurd h Bool.false_ne_true
  | [], [], _ :: _, _, _, _, h => absurd h Bool.false_ne_true
  | [], _ :: _, _, _, _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, _, _, _, h => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, [], _, _, _, h => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, _ :: _, [], _, _, h => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => absurd h Bool.false_ne_true
  | E :: Es, m :: Ms, u :: Us, T :: Ts, CL :: CLs, i, h => by
    obtain ⟨h1, h2⟩ := lp_andB h
    obtain ⟨e1, e2, e3, ih⟩ := lq_levelsQ Es Ms Us Ts CLs (i + 1) h2
    refine ⟨by simp [e1], by simp [e2], by simp [e3], fun j hj => ?_⟩
    cases j with
    | zero => exact h1
    | succ j =>
      have e : i + (j + 1) = i + 1 + j := by omega
      rw [e, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ]
      exact ih j (by simpa using hj)

end Lemmas

theorem card_le_of_leafQK {XB : Nat → Nat} {BT : List Nat} {Es : List (List Nat)} {Ms U : List Nat}
    {Ts : List (List (List Nat))} {IMS CLs : List (List (List Nat))} {SL : List Nat} {UIT N : Nat}
    (h : leafQK XB BT Es Ms U Ts IMS CLs SL UIT N = true) {ι : Type} [Fintype ι] (F : ι → Nat → Nat)
    (hF : ∀ i, Equi XB BT (F i)) (hinj : ∀ i j, (∀ x, x < 2 ^ 24 → F i x = F j x) → i = j) :
    Fintype.card ι ≤ N := by
  classical
  obtain ⟨hBT, h⟩ := lp_andB h
  obtain ⟨hlev, h⟩ := lp_andB h
  obtain ⟨hSL, h⟩ := lp_andB h
  obtain ⟨hcSL, h⟩ := lp_andB h
  obtain ⟨hUIT, hN⟩ := lp_andB h
  have hBT' : BT.length < 33 := by rw [← lp_lenL]; exact Nat.le_of_ble_eq_true hBT
  obtain ⟨hEs, hTs, hCLs, hlv⟩ := lq_levelsQ Es Ms U Ts CLs 0 hlev
  have hlq := fun (j : ℕ) (hj : j < U.length) => by
    have := hlv j hj
    rw [Nat.zero_add] at this
    exact lp_andB this
  have hfact := fun (j : ℕ) (hj : j < U.length) => lp_levelOK (hlq j hj).1
  have hfix := fun (j : ℕ) (hj : j < U.length) => (lp_andB (hlq j hj).2).1
  have hCL := fun (j : ℕ) (hj : j < U.length) => lp_eqLL _ _ (lp_andB (hlq j hj).2).2
  have hu24 : ∀ j < U.length, U.getD j 0 < 2 ^ 24 := fun j hj => by
    rw [← (hfact j hj).2.1]
    exact lp_vmF_lt _ _
  have hex : ∀ k j, ∃ a, a < 2 ^ (Es.getD j []).length ∧
      F k (U.getD j 0) = CFSG.KC.Co1Leaf.selK (Es.getD j []) a := by
    intro k j
    by_cases hj : j < U.length
    · obtain ⟨hcrd, he, -, -, -⟩ := hfact j hj
      obtain ⟨a, ha⟩ := lp_e_span hcrd (F k (U.getD j 0))
      refine ⟨a % 2 ^ (Es.getD j []).length, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
      rw [← lp_selK_mod, ← ha, ← lp_f_e (hF k) _ (hu24 j hj), he]
    · have h1 : U.getD j 0 = 0 := List.getD_eq_default _ _ (by omega)
      have h2 : Es.getD j [] = [] := List.getD_eq_default _ _ (by omega)
      refine ⟨0, by rw [h2]; norm_num, ?_⟩
      rw [h1, h2, lp_f0 (hF k)]
      all_goals rfl
  choose a ha using hex
  have hClen : ∀ k j, j < U.length → (imgQ (getLLP IMS j) (a k j)).length = BT.length := by
    intro k j hj
    rw [lq_imgQ, List.length_map, (hfact j hj).2.2.2.2, lp_imgsK, List.length_map]
  have hCget : ∀ k j, j < U.length → ∀ s < BT.length, (imgQ (getLLP IMS j) (a k j)).getD s 0 =
      F k (vmF 24 (BT.getD s 0) (U.getD j 0)) := by
    intro k j hj s hs
    have hs' : s < (imgQ (getLLP IMS j) (a k j)).length := by rw [hClen k j hj]; exact hs
    rw [List.getD_eq_getElem _ _ hs']
    simp only [lq_imgQ, (hfact j hj).2.2.2.2, lp_imgsK, List.map_map, List.getElem_map,
      Function.comp_apply]
    rw [lp_selK_map_vmF, ← (ha k j).2, (hF k).comm s hs _ (hu24 j hj), List.getD_eq_getElem _ _ hs]
  have hslotU : ∀ c, slotU BT U c = vmF 24 (BT.getD (c % 32) 0) (U.getD (c / 32) 0) := by
    intro c
    change vmF 24 (getL 0 BT (c % 32)) (getL 0 U (c / 32)) = _
    rw [lp_getL, lp_getL]
  have hsearch : ∀ k m j0 (Ps : List (List (List ℕ))), j0 + m = U.length →
      (List.range j0).map (fun j => imgQ (getLLP IMS j) (a k j)) ∈ Ps →
      (List.range U.length).map (fun j => imgQ (getLLP IMS j) (a k j)) ∈
        searchQ XB (CLs.drop j0) (Ts.drop j0) Ps := by
    intro k m
    induction m with
    | zero =>
      intro j0 Ps hj hP
      have e : j0 = U.length := by omega
      subst e
      rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      exact hP
    | succ m ih =>
      intro j0 Ps hj hP
      have hj0 : j0 < U.length := by omega
      have hT : Ts.getD j0 [] = Ts[j0]'(by omega) := List.getD_eq_getElem _ _ (by omega)
      have hC' : CLs.getD j0 [] = CLs[j0]'(by omega) := List.getD_eq_getElem _ _ (by omega)
      rw [List.drop_eq_getElem_cons (by omega : j0 < CLs.length),
        List.drop_eq_getElem_cons (by omega : j0 < Ts.length)]
      refine ih (j0 + 1) _ (by omega) ?_
      have e : (List.range (j0 + 1)).map (fun j => imgQ (getLLP IMS j) (a k j)) =
          (List.range j0).map (fun j => imgQ (getLLP IMS j) (a k j)) ++
            [imgQ (getLLP IMS j0) (a k j0)] := by
        rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [e]
      obtain ⟨-, -, hmem, htests, -⟩ := hfact j0 hj0
      refine lq_stepQ_mem ?_ Ps _ hP ?_
      · rw [← hC', hCL j0 hj0]
        refine lq_candsN_mem ?_ _ ?_
        · rw [← (ha k j0).2, (hF k).mem _ (hu24 j0 hj0)]
          exact hmem
        · rw [lp_pw2, lp_lenL]
          exact (ha k j0).1
      · refine lq_passQ _ fun t ht => ?_
        rw [← hT] at ht
        have hb := (lp_testsUK _ htests _ (lq_convQ_mem _ t ht)).2
        have hcs := lq_fixQ _ (hfix j0 hj0) t ht
        have hsumQ : sumQ ((List.range j0).map fun j => imgQ (getLLP IMS j) (a k j)) t.tail.tail =
            F k (sumU BT U t.tail.tail) := by
          generalize t.tail.tail = cs at hcs
          induction cs with
          | nil => exact (lp_f0 (hF k)).symm
          | cons c cs ihc =>
            obtain ⟨hc1, hc2⟩ := hcs c List.mem_cons_self
            have hc2' : c % 32 < BT.length := by rw [← lp_lenL]; exact hc2
            change slotQ _ c ^^^ sumQ _ cs = F k (slotU BT U c ^^^ sumU BT U cs)
            rw [(hF k).add _ _ (lp_slotU_lt c) (lp_sumU_lt cs),
              ihc fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'), hslotU]
            have hlen : c / 32 < ((List.range j0).map fun j => imgQ (getLLP IMS j) (a k j)).length := by
              rw [List.length_map, List.length_range]
              exact hc1
            change getL 0 (getLP ((List.range j0).map fun j => imgQ (getLLP IMS j) (a k j))
              (c / 32)) (c % 32) ^^^ _ = _
            rw [lp_getL, lp_getLP, List.getD_eq_getElem _ _ hlen, List.getElem_map,
              List.getElem_range, hCget k _ (by omega) _ hc2']
        have hsel : CFSG.KC.Co1Leaf.selK (imgQ (getLLP IMS j0) (a k j0)) (t.tail.headD 0) =
            F k (lqX (fun s => slotU BT U (32 * j0 + s)) (t.tail.headD 0) (lenL BT)) := by
          rw [lq_selK_X, lq_f_X (hF k) fun s _ => lp_slotU_lt _, hClen k j0 hj0, ← lp_lenL]
          refine lqX_congr fun s hs => ?_
          rw [lp_lenL] at hs
          rw [hCget k j0 hj0 s hs, hslotU]
          have e1 : (32 * j0 + s) % 32 = s := by omega
          have e2 : (32 * j0 + s) / 32 = j0 := by omega
          rw [e1, e2]
        rw [hsumQ, hsel, ← (hF k).add _ _ (lp_sumU_lt _) (lqX_lt fun s _ => lp_slotU_lt _),
          Nat.xor_comm, ← lq_maskCodes, (hF k).mem _ (lp_sumU_lt _)]
        exact hb
  have hmemS : ∀ k, (List.range U.length).map (fun j => imgQ (getLLP IMS j) (a k j)) ∈
      searchQ XB CLs Ts (List.cons List.nil List.nil) := by
    intro k
    have := hsearch k U.length 0 [[]] (by omega) (by simp)
    rwa [List.drop_zero, List.drop_zero] at this
  have hSLlen : SL.length = 24 := by rw [← lp_lenL]; exact Nat.eq_of_beq_eq_true hSL
  have hginj : Function.Injective fun k =>
      (List.range U.length).map (fun j => imgQ (getLLP IMS j) (a k j)) := by
    intro k k' hkk
    have haj : ∀ j < U.length, imgQ (getLLP IMS j) (a k j) = imgQ (getLLP IMS j) (a k' j) :=
      fun j hj => List.map_inj_left.1 hkk j (List.mem_range.2 hj)
    have hslot : ∀ c, c % 32 < BT.length → F k (slotU BT U c) = F k' (slotU BT U c) := by
      intro c hs
      rw [hslotU]
      by_cases hj : c / 32 < U.length
      · rw [← hCget k _ hj _ hs, ← hCget k' _ hj _ hs, haj _ hj]
      · rw [List.getD_eq_default U 0 (by omega : U.length ≤ c / 32), lp_vmF_zero, lp_f0 (hF k),
          lp_f0 (hF k')]
    have hrows : ∀ r < 24, F k (rowF 24 (packU BT U SL) r) = F k' (rowF 24 (packU BT U SL) r) := by
      intro r hr
      have hr' : r < SL.length := by omega
      rw [lp_rowF_packU hr']
      refine hslot _ ?_
      have hmem : SL.getD r 0 ∈ SL := by
        rw [List.getD_eq_getElem _ _ hr']
        exact List.getElem_mem hr'
      rw [← lp_lenL]
      exact (lp_codesOK _ hcSL _ hmem).2
    refine hinj k k' fun x hx => ?_
    have e1 : CFSG.KC.Co1B.mulWK UIT (packU BT U SL) = CFSG.KC.Co1B.oneK :=
      Nat.eq_of_beq_eq_true hUIT
    have e2 : vmF 24 (CFSG.KC.Co1B.mulWK UIT (packU BT U SL)) x =
        vmF 24 (packU BT U SL) (vmF 24 UIT x) := by
      change vmF 24 (CFSG.KC.F2W.mulW 24 UIT (packU BT U SL)) x = _
      rw [CFSG.KC.F2W.mulW_eq, CFSG.KC.VecK.vmF_mulF]
    have hx' : x = vmF 24 (packU BT U SL) (vmF 24 UIT x) := by
      rw [← e2, e1]
      exact (CFSG.KC.VecK.vmF_idF hx).symm
    rw [hx']
    exact lp_agree (hF k) (hF k') hrows _
  have hlenQ : ∀ L : List (List (List ℕ)), lenQ L = L.length := by
    intro L
    induction L with
    | nil => rfl
    | cons _ L ih => exact congrArg Nat.succ ih
  calc Fintype.card ι = (Finset.univ.image fun k =>
        (List.range U.length).map (fun j => imgQ (getLLP IMS j) (a k j))).card := by
        rw [Finset.card_image_of_injective _ hginj, Finset.card_univ]
    _ ≤ (searchQ XB CLs Ts (List.cons List.nil List.nil)).toFinset.card := by
        refine Finset.card_le_card fun l hl => ?_
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hl
        exact List.mem_toFinset.2 (hmemS k)
    _ ≤ (searchQ XB CLs Ts (List.cons List.nil List.nil)).length := List.toFinset_card_le _
    _ = N := by
        rw [← hlenQ]
        exact Nat.eq_of_beq_eq_true hN

end CFSG.KC.Co1LeafQ

end
