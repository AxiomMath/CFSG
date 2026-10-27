module

public import Certificates.Data.Kernel.B45Nor.Defs
public import CFSG.Quasithin.Background.SmithB45MatIndDefs

public section

namespace CFSG.KC.B45Nor

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.B45Mat.Ind

theorem papK_cons (c : ℕ) (cs : List ℕ) (v : ℕ) :
    papK (c :: cs) v = (if v % 2 = 1 then c else 0) ^^^ papK cs (v / 2) := by
  have e : papK (c :: cs) v =
      (bif Nat.beq (v &&& 1) 1 then c else 0) ^^^ papK cs (v >>> 1) := rfl
  rw [e, Nat.and_one_is_mod, Nat.shiftRight_one]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> rfl

theorem foldl_xor_init (p : ℕ → Bool) (g : ℕ → ℕ) : ∀ (l : List ℕ) (a : ℕ),
    l.foldl (fun acc j => if p j then acc ^^^ g j else acc) a =
      a ^^^ l.foldl (fun acc j => if p j then acc ^^^ g j else acc) 0
  | [], a => by simp
  | j :: l, a => by
    simp only [List.foldl_cons]
    rw [foldl_xor_init p g l, foldl_xor_init p g l (if p j then 0 ^^^ g j else 0)]
    split_ifs <;> simp [Nat.xor_assoc]

theorem papK_eq : ∀ (cs : List ℕ) (v : ℕ), papK cs v = papply cs.length cs v
  | [], _ => rfl
  | c :: cs, v => by
    rw [papK_cons, papK_eq cs]
    unfold papply
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.testBit_add_one, List.getD_cons_succ, List.getD_cons_zero]
    conv_rhs => rw [foldl_xor_init]
    congr 1
    rw [Nat.testBit_zero]
    by_cases h : v % 2 = 1 <;> simp [h]

theorem papK_eq' {d : ℕ} {cs : List ℕ} (h : cs.length = d) (v : ℕ) :
    papK cs v = papply d cs v := by
  rw [papK_eq, h]

theorem wapK_eq {d : ℕ} {cols : Bool → List ℕ} (hc : ∀ b, (cols b).length = d) :
    ∀ (w : List Bool) (v : ℕ), wapK cols w v = wapp d cols w v
  | [], _ => rfl
  | b :: w, v => by
    change papK (cols b) (wapK cols w v) = papply d (cols b) (wapp d cols w v)
    rw [wapK_eq hc w, papK_eq' (hc b)]

theorem sumW_foldl (cols : Bool → List ℕ) (v : ℕ) : ∀ (aW : List (List Bool)) (a : ℕ),
    aW.foldl (fun acc w => acc ^^^ wapK cols w v) a = a ^^^ sumW cols aW v
  | [], a => (Nat.xor_zero a).symm
  | w :: aW, a => by
    rw [List.foldl_cons, sumW_foldl cols v aW]
    change _ = a ^^^ (wapK cols w v ^^^ sumW cols aW v)
    rw [Nat.xor_assoc]

theorem sumW_eq {d : ℕ} {cols : Bool → List ℕ} (hc : ∀ b, (cols b).length = d)
    (aW : List (List Bool)) (v : ℕ) :
    sumW cols aW v = aW.foldl (fun acc w => acc ^^^ wapp d cols w v) 0 := by
  simp only [← wapK_eq hc]
  rw [sumW_foldl, Nat.zero_xor]

theorem aCK_eq {d : ℕ} {cols : Bool → List ℕ} (hc : ∀ b, (cols b).length = d)
    (aW : List (List Bool)) : aCK d cols aW = aColsOf d cols aW := by
  unfold aCK aColsOf
  exact List.map_congr_left fun k _ => sumW_eq hc aW _

theorem getD_map_of_lt {α β : Type} (f : α → β) {l : List α} {k : ℕ} (a : α) (b : β)
    (hk : k < l.length) : (l.map f).getD k b = f (l.getD k a) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem allIx_spec (p : ℕ → ℕ → Bool) : ∀ (xs : List ℕ) (i : ℕ), allIx p xs i = true →
    ∀ j < xs.length, p (i + j) (xs.getD j 0) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | x :: xs, i, h, j, hj => by
    have e : allIx p (x :: xs) i = (p i x && allIx p xs (i + 1)) := rfl
    rw [e, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := allIx_spec p xs (i + 1) h.2 j (by simpa using hj)
      rw [List.getD_cons_succ, ← Nat.add_assoc, Nat.add_right_comm]
      exact this

theorem rowK_testBit : ∀ (cs : List ℕ) (i j : ℕ),
    (rowK cs i).testBit j = (decide (j < cs.length) && (cs.getD j 0).testBit i)
  | [], _, j => by simp [rowK, Nat.zero_testBit]
  | c :: cs, i, j => by
    have e : rowK (c :: cs) i = (c >>> i) % 2 + 2 * rowK cs i := by
      rw [← Nat.and_one_is_mod]
      rfl
    have hb : (c >>> i) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hci : c.testBit i = decide ((c >>> i) % 2 = 1) := by
      rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
    rw [e]
    cases j with
    | zero =>
      rw [Nat.testBit_zero]
      simp only [List.length_cons, Nat.zero_lt_succ, decide_true, List.getD_cons_zero,
        Bool.true_and, hci]
      congr 1
      apply propext
      omega
    | succ j =>
      have : ((c >>> i) % 2 + 2 * rowK cs i) / 2 = rowK cs i := by omega
      rw [Nat.testBit_add_one, this, rowK_testBit cs i j]
      simp

theorem trChk_spec {d : ℕ} {cs hs : List ℕ} (h : trChk cs hs 0 = true) (hc : cs.length = d)
    (hh : hs.length = d) : ∀ i < d, ∀ j < d, (hs.getD i 0).testBit j = (cs.getD j 0).testBit i := by
  intro i hi j hj
  have := allIx_spec _ hs 0 h i (hh ▸ hi)
  rw [Nat.zero_add, Nat.beq_eq] at this
  rw [this, rowK_testBit, hc]
  simp [hj]

theorem fnl_lin_tr {d : ℕ} {C Ct : List ℕ}
    (hb : ∀ i < d, ∀ j < d, (Ct.getD i 0).testBit j = (C.getD j 0).testBit i) (ψ : ℕ)
    (x : Vec d) : fnl d ψ (lin d C x) = fnl d (papply d Ct ψ) x := by
  have hT : ∀ i j : Fin d, toVec d (Ct.getD i.val 0) j = toVec d (C.getD j.val 0) i := by
    intro i j
    simp only [toVec_apply, hb i i.isLt j j.isLt]
  rw [fnl_apply, fnl_apply, toVec_papply]
  simp only [lin_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem fnl_wmap {d : ℕ} {cols ht : Bool → List ℕ} (hh : ∀ b, (ht b).length = d)
    (hb : ∀ b, ∀ i < d, ∀ j < d, ((ht b).getD i 0).testBit j = ((cols b).getD j 0).testBit i) :
    ∀ (w : List Bool) (ψ : ℕ) (x : Vec d),
      fnl d ψ (wmap (fun b => lin d (cols b)) w x) = fnl d (wTK ht w ψ) x
  | [], _, _ => rfl
  | b :: w, ψ, x => by
    rw [wmap_cons, fnl_lin_tr (hb b), ← papK_eq' (hh b), fnl_wmap hh hb w]
    rfl

theorem dotb_wapp {d : ℕ} {cols ht : Bool → List ℕ} (hh : ∀ b, (ht b).length = d)
    (hb : ∀ b, ∀ i < d, ∀ j < d, ((ht b).getD i 0).testBit j = ((cols b).getD j 0).testBit i)
    (w : List Bool) (ψ : ℕ) {k : ℕ} (hk : k < d) :
    dotb d ψ (wapp d cols w (1 <<< k)) = (wTK ht w ψ).testBit k := by
  have h := dotb_cast d ψ (wapp d cols w (1 <<< k))
  rw [toVec_wapp, toVec_one_shiftLeft d k hk, fnl_wmap hh hb, fnl_single, toVec_apply] at h
  revert h
  cases dotb d ψ (wapp d cols w (1 <<< k)) <;> cases (wTK ht w ψ).testBit k <;> simp

theorem papply_aCols {d T : ℕ} {cols : Bool → List ℕ} {aW : List (List Bool)}
    (hc : ∀ b, (cols b).length = d) (hlt : ∀ b, ∀ j < d, (cols b).getD j 0 < 2 ^ d)
    (h0 : sumW cols aW T = 0) : papply d (aColsOf d cols aW) T = 0 := by
  apply toVec_injOn (papply_lt (aColsOf_lt hlt aW) T) (Nat.two_pow_pos d)
  have e : toVec d (sumW cols aW T) = 0 := by rw [h0, toVec_zero]
  rw [sumW_eq hc, toVec_foldl_xor, toVec_zero, zero_add] at e
  rw [toVec_papply, aColsOf_eq, list_sum_apply, List.map_map, toVec_zero, ← e]
  congr 1
  exact List.map_congr_left fun w _ => (toVec_wapp d cols w T).symm

theorem papK_spin {d T c : ℕ} {cols : Bool → List ℕ} (hc : ∀ b, (cols b).length = d)
    (gw : List (List Bool)) :
    papK (gw.map fun w => wapK cols w T) c = xorSelW d cols gw T c := by
  rw [papK_eq, List.length_map]
  unfold papply xorSelW
  refine List.foldl_ext _ _ _ fun acc l hl => ?_
  rw [List.mem_range] at hl
  rw [getD_map_of_lt _ [] 0 hl, wapK_eq hc]

theorem dual_col {d psi k : ℕ} {cols ht : Bool → List ℕ} {dw : List (List Bool)}
    (hh : ∀ b, (ht b).length = d)
    (hb : ∀ b, ∀ i < d, ∀ j < d, ((ht b).getD i 0).testBit j = ((cols b).getD j 0).testBit i)
    (hdw : dw.length = d) (hk : k < d) :
    ofBits d (fun l => (((List.range d).map (rowAt d cols psi dw)).getD l 0).testBit k) =
      rowK (dw.map fun w => wTK ht w psi) k := by
  apply Nat.eq_of_testBit_eq
  intro l
  rw [ofBits_testBit, rowK_testBit, List.length_map, hdw]
  by_cases hl : l < d
  · rw [getD_map_of_lt _ 0 0 (by simpa using hl), getD_map_of_lt _ [] 0 (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_range hl, Option.getD_some]
    unfold rowAt
    rw [ofBits_testBit, dotb_wapp hh hb _ _ hk]
    simp [hl, hk]
  · simp [hl]

theorem nortonFastOK_of_norKP {d T psi : ℕ} {cols ht : Bool → List ℕ}
    {aW gw dw : List (List Bool)} {masks rC minv : List ℕ}
    (h : norKP d cols ht aW T gw masks psi dw rC minv = true)
    (hT : ∀ b, trChk (cols b) (ht b) 0 = true) :
    nortonFastOK d cols aW [(T, gw, masks)] psi dw rC minv = true := by
  unfold norKP at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc0, hc1⟩, hh0⟩, hh1⟩, hb0⟩, hb1⟩, hrC⟩, hmi⟩, hma⟩, hdw⟩, hT0⟩, hTd⟩,
    hA⟩, hAT⟩, hS⟩, hM⟩ := h
  have hc : ∀ b, (cols b).length = d := fun b => by cases b <;> assumption
  have hh : ∀ b, (ht b).length = d := fun b => by cases b <;> assumption
  have hlt : ∀ b, ∀ j < d, (cols b).getD j 0 < 2 ^ d := by
    intro b j hj
    have hb : allIx (fun _ c => Nat.blt c (2 ^ d)) (cols b) 0 = true := by
      cases b <;> assumption
    have := allIx_spec _ _ 0 hb j (by rw [hc b]; exact hj)
    simpa using this
  have htr := fun b => trChk_spec (hT b) (hc b) (hh b)
  have hlenA : (aCK d cols aW).length = d := by simp [aCK]
  have hAk := fun k (hk : k < d) => allIx_spec _ _ 0 hA k (by rw [hlenA]; exact hk)
  unfold nortonFastOK nortonCore
  rw [← aCK_eq hc]
  simp only [List.map_cons, List.map_nil, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
  · intro k hk
    have := hAk k hk
    rw [Bool.and_eq_true, Nat.zero_add] at this
    rw [← papK_eq' hrC]
    simpa [Nat.beq_eq, Bool.or_eq_true] using this.1
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    unfold kerCertOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨hT0, hTd⟩, ?_⟩, hma⟩, ?_⟩
    · rw [aCK_eq hc]
      exact papply_aCols hc hlt hAT
    · intro k hk
      have := allIx_spec _ _ 0 hS k (by rw [List.length_map]; omega)
      rw [Nat.zero_add, Nat.beq_eq, getD_map_of_lt _ 0 0 (by omega), papK_spin hc] at this
      exact this
  · intro k hk
    have := hAk k hk
    rw [Bool.and_eq_true] at this
    exact this.2
  · intro k hk
    have := allIx_spec _ _ 0 hM k (by simpa using hk)
    rw [Nat.zero_add, Nat.beq_eq, getD_map_of_lt _ 0 0 (by simpa using hk),
      List.getD_eq_getElem?_getD, List.getElem?_range hk, Option.getD_some,
      papK_eq' hmi] at this
    rw [beq_iff_eq, dual_col hh htr hdw hk]
    exact this

end CFSG.KC.B45Nor
