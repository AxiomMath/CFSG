module

public import CFSG.Certificates.Kernel.LocalQTPipeEnum

public section

namespace CFSG.KC.LQT.PPEd

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.PPB CFSG.KC.LQT.BW.Pf
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

private theorem allR_get {lo len : Nat} {f : Nat → Bool} (h : allR lo len f = true) :
    ∀ j < len, f (lo + j) = true := by
  induction len with
  | zero => intro j hj; omega
  | succ m ih =>
    have e : allR lo (m + 1) f = CFSG.KC.Ord.andB (f (Nat.add lo m)) (allR lo m f) := rfl
    rw [e, andB_iff] at h
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h.2 j hj
    · exact h.1

private theorem allR_blocks {K L N : Nat} {f : Nat → Bool} (hKL : K * L = N)
    (h : ∀ c < K, allR (c * L) L f = true) : ∀ i < N, f i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; omega
    · exact h0
  have hc : i / L < K := by
    rw [Nat.div_lt_iff_lt_mul hL]; omega
  have := allR_get (h _ hc) (i % L) (Nat.mod_lt _ hL)
  rwa [Nat.div_add_mod'] at this

private theorem getD_push_lt {A : Array (Array Nat)} {x : Array Nat} {i : Nat} (hi : i < A.size) :
    (A.push x).getD i #[] = A.getD i #[] := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hi,
    Array.getElem?_eq_getElem hi]

private theorem getD_push_size (A : Array (Array Nat)) (x : Array Nat) :
    (A.push x).getD A.size #[] = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_eq]
  rfl

private def pushStep (F : Nat → Array Nat → Array Nat) (par : Array Nat)
    (acc : Array (Array Nat)) (i : Nat) : Array (Array Nat) :=
  acc.push (F i (acc.getD (par.getD i 0) #[]))

private theorem foldPush (F : Nat → Array Nat → Array Nat) (par : Array Nat) (base : Array Nat) :
    ∀ m, (∀ j, 0 < j → j ≤ m → par.getD j 0 < j) →
    ((List.range' 1 m).foldl (pushStep F par) #[base]).size = m + 1 ∧
    ((List.range' 1 m).foldl (pushStep F par) #[base]).getD 0 #[] = base ∧
    ∀ i, 0 < i → i ≤ m → ((List.range' 1 m).foldl (pushStep F par) #[base]).getD i #[] =
      F i (((List.range' 1 m).foldl (pushStep F par) #[base]).getD (par.getD i 0) #[])
  | 0, _ => by
    refine ⟨rfl, rfl, fun i h1 h2 => by omega⟩
  | m + 1, hp => by
    have ih := foldPush F par base m (fun j hj hjm => hp j hj (by omega))
    obtain ⟨ih1, ih2, ih3⟩ := ih
    set A := (List.range' 1 m).foldl (pushStep F par) #[base] with hA
    have e : (List.range' 1 (m + 1)).foldl (pushStep F par) #[base] =
        A.push (F (m + 1) (A.getD (par.getD (m + 1) 0) #[])) := by
      rw [List.range'_concat, List.foldl_append, ← hA]
      simp only [List.foldl_cons, List.foldl_nil, pushStep, Nat.one_mul]
      rw [Nat.add_comm]
    rw [e]
    have hpm := hp (m + 1) (by omega) le_rfl
    set X := F (m + 1) (A.getD (par.getD (m + 1) 0) #[]) with hX
    have hsz : (A.push X).getD (m + 1) #[] = X := by
      have := getD_push_size A X
      rwa [ih1] at this
    refine ⟨by simp [ih1], ?_, ?_⟩
    · rw [getD_push_lt (by omega), ih2]
    · intro i hi him
      have hpi := hp i hi him
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · rw [getD_push_lt (by omega), getD_push_lt (by omega), ih3 i hi (by omega)]
      · have hi' : i = m + 1 := by omega
        rw [hi', hsz, getD_push_lt (by omega)]

private theorem treeTabs_spec {n N : Nat} (ta tb par gen : Array Nat) (hN : 0 < N)
    (hv : treeValid N par gen) :
    (treeTabs n N ta tb par gen).size = N ∧
    (treeTabs n N ta tb par gen).getD 0 #[] = Array.range n ∧
    ∀ i, 0 < i → i < N → (treeTabs n N ta tb par gen).getD i #[] =
      compArr (if gen.getD i 0 = 0 then ta else tb)
        ((treeTabs n N ta tb par gen).getD (par.getD i 0) #[]) := by
  have e : treeTabs n N ta tb par gen = (List.range' 1 (N - 1)).foldl
      (pushStep (fun i x => compArr (if gen.getD i 0 = 0 then ta else tb) x) par)
      #[Array.range n] := rfl
  have h := foldPush (fun i x => compArr (if gen.getD i 0 = 0 then ta else tb) x) par
    (Array.range n) (N - 1) (fun j hj hjm => (hv.2.2 j (by omega) hj).1)
  rw [← e] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, h2, fun i hi hiN => h3 i hi (by omega)⟩

private theorem treeInvTabs_spec {n N : Nat} (tai tbi par gen : Array Nat) (hN : 0 < N)
    (hv : treeValid N par gen) :
    (treeInvTabs n N tai tbi par gen).size = N ∧
    (treeInvTabs n N tai tbi par gen).getD 0 #[] = Array.range n ∧
    ∀ i, 0 < i → i < N → (treeInvTabs n N tai tbi par gen).getD i #[] =
      compArr ((treeInvTabs n N tai tbi par gen).getD (par.getD i 0) #[])
        (if gen.getD i 0 = 0 then tai else tbi) := by
  have e : treeInvTabs n N tai tbi par gen = (List.range' 1 (N - 1)).foldl
      (pushStep (fun i x => compArr x (if gen.getD i 0 = 0 then tai else tbi)) par)
      #[Array.range n] := rfl
  have h := foldPush (fun i x => compArr x (if gen.getD i 0 = 0 then tai else tbi)) par
    (Array.range n) (N - 1) (fun j hj hjm => (hv.2.2 j (by omega) hj).1)
  rw [← e] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, h2, fun i hi hiN => h3 i hi (by omega)⟩

private theorem rep_range {n w : Nat} (hw : n ≤ 2 ^ w) : Rep n w (oneW n w) (Array.range n) := by
  refine ⟨by simp, fun i hi => ?_⟩
  have e : img (Array.range n) i = i := by
    rw [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
    simp
  rw [e]
  refine ⟨hi, ?_⟩
  rw [oneW, imgW_ofFnW (fun j hj => by omega) hi]

private theorem beq_false' {x y : Nat} (h : x ≠ y) : Nat.beq x y = false :=
  Bool.eq_false_iff.2 fun e => h (beq_iff.1 e)

private theorem tree_rep {n w W N : Nat} (hw : n ≤ 2 ^ w)
    {ta tb par gen : Array Nat} {ca cb PK GK : Nat} (RF : Nat → Nat)
    (hca : Rep n w ca ta) (hcb : Rep n w cb tb)
    (hPK : ∀ i < N, imgW W PK i = par.getD i 0) (hGK : ∀ i < N, imgW W GK i = gen.getD i 0)
    (hv : treeValid N par gen) (hrt : ∀ i < N, rtAt n w W ca cb PK GK RF i = true) :
    ∀ i < N, Rep n w (RF i) ((treeTabs n N ta tb par gen).getD i #[]) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hN : 0 < N := by omega
  obtain ⟨-, T0, Tk⟩ := treeTabs_spec (n := n) ta tb par gen hN hv
  have h := hrt i hi
  unfold rtAt at h
  by_cases h0 : i = 0
  · subst h0
    change Nat.beq (RF 0) (oneW n w) = true at h
    rw [T0, beq_iff.1 h]
    exact rep_range hw
  · rw [beq_false' h0] at h
    change Nat.beq (RF i) (mulW n w (Bool.rec (motive := fun _ => Nat) cb ca
      (Nat.beq (imgW W GK i) 0)) (RF (imgW W PK i))) = true at h
    have hp := (hv.2.2 i hi (by omega)).1
    rw [hPK i hi, hGK i hi] at h
    rw [Tk i (by omega) hi, beq_iff.1 h]
    by_cases hg : gen.getD i 0 = 0
    · rw [hg]
      change Rep n w (mulW n w ca (RF (par.getD i 0))) _
      simp only [if_true]
      exact rep_mul hca (ih _ hp (by omega))
    · rw [beq_false' hg]
      change Rep n w (mulW n w cb (RF (par.getD i 0))) _
      simp only [if_neg hg]
      exact rep_mul hcb (ih _ hp (by omega))

private def Tab (n : Nat) (t : Array Nat) : Prop := t.size = n ∧ ∀ q < n, img t q < n

private theorem tab_range (n : Nat) : Tab n (Array.range n) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simpa using hi

private theorem img_range {n i : Nat} (hi : i < n) : img (Array.range n) i = i := by
  rw [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simp

private theorem tab_comp {n : Nat} {s t : Array Nat} (hs : Tab n s) (ht : Tab n t) :
    Tab n (compArr s t) ∧ ∀ q < n, img (compArr s t) q = img s (img t q) := by
  have key : ∀ q < n, img (compArr s t) q = img s (img t q) := fun q hq =>
    img_compArr hs.1 ht.1 ht.2 hq
  refine ⟨⟨by simp [compArr, ht.1], fun q hq => ?_⟩, key⟩
  rw [key q hq]
  exact hs.2 _ (ht.2 q hq)

private theorem step_inv {n : Nat} {g gi Up Tp : Array Nat} (hg : Tab n g) (hgi : Tab n gi)
    (hU : Tab n Up) (hT : Tab n Tp) (hgg : ∀ q < n, img gi (img g q) = q)
    (ih : ∀ q < n, img Up (img Tp q) = q) :
    Tab n (compArr Up gi) ∧ Tab n (compArr g Tp) ∧
      ∀ q < n, img (compArr Up gi) (img (compArr g Tp) q) = q := by
  obtain ⟨h1, k1⟩ := tab_comp hU hgi
  obtain ⟨h2, k2⟩ := tab_comp hg hT
  refine ⟨h1, h2, fun q hq => ?_⟩
  rw [k2 q hq, k1 _ (hg.2 _ (hT.2 q hq)), hgg _ (hT.2 q hq), ih q hq]

private theorem inv_tabs {n N : Nat} {ta tb tai tbi par gen : Array Nat}
    (hta : Tab n ta) (htb : Tab n tb) (htai : Tab n tai) (htbi : Tab n tbi)
    (hinv : ∀ q < n, img tai (img ta q) = q ∧ img tbi (img tb q) = q)
    (hv : treeValid N par gen) :
    ∀ i < N, Tab n ((treeTabs n N ta tb par gen).getD i #[]) ∧
      Tab n ((treeInvTabs n N tai tbi par gen).getD i #[]) ∧
      ∀ q < n, img ((treeInvTabs n N tai tbi par gen).getD i #[])
        (img ((treeTabs n N ta tb par gen).getD i #[]) q) = q := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hN : 0 < N := by omega
  obtain ⟨-, T0, Tk⟩ := treeTabs_spec (n := n) ta tb par gen hN hv
  obtain ⟨-, U0, Uk⟩ := treeInvTabs_spec (n := n) tai tbi par gen hN hv
  by_cases h0 : i = 0
  · subst h0
    rw [T0, U0]
    exact ⟨tab_range n, tab_range n, fun q hq => by rw [img_range hq, img_range hq]⟩
  · have hp := (hv.2.2 i hi (by omega)).1
    obtain ⟨ih1, ih2, ih3⟩ := ih _ hp (by omega)
    rw [Tk i (by omega) hi, Uk i (by omega) hi]
    by_cases hg : gen.getD i 0 = 0
    · simp only [if_pos hg]
      exact (fun h => ⟨h.2.1, h.1, h.2.2⟩) (step_inv hta htai ih2 ih1 (fun q hq => (hinv q hq).1) ih3)
    · simp only [if_neg hg]
      exact (fun h => ⟨h.2.1, h.1, h.2.2⟩) (step_inv htb htbi ih2 ih1 (fun q hq => (hinv q hq).2) ih3)

private theorem testBit_invW (w s p : Nat) : ∀ m,
    (invW m w s).testBit p =
      (List.range m).any fun k => decide (w * imgW w s k ≤ p) && k.testBit (p - w * imgW w s k)
  | 0 => by
    have e : invW 0 w s = 0 := rfl
    rw [e]
    simp
  | m + 1 => by
    have e : invW (m + 1) w s = invW m w s ||| (m <<< (w * imgW w s m)) := rfl
    rw [e, Nat.testBit_or, testBit_invW w s p m, List.range_succ, List.any_append,
      Nat.testBit_shiftLeft]
    simp

private theorem imgW_invW {n w : Nat} (hw : n ≤ 2 ^ w) {c : Nat}
    (hinj : ∀ i < n, ∀ j < n, imgW w c i = imgW w c j → i = j) {i : Nat} (hi : i < n) :
    imgW w (invW n w c) (imgW w c i) = i := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_imgW, testBit_invW]
  have hk : ∀ k < n, k < 2 ^ w := fun k hk => by omega
  by_cases hq : q < w
  · simp only [hq, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨k, hkn, hle, hb⟩
      have hlt : w * imgW w c i + q - w * imgW w c k < w := by
        apply Nat.lt_of_not_le
        intro hc
        rw [testBit_lt (hk k hkn) hc] at hb
        exact absurd hb (by decide)
      have hck : imgW w c k = imgW w c i := by
        rcases Nat.lt_trichotomy (imgW w c k) (imgW w c i) with h | h | h
        · have : w * (imgW w c k + 1) ≤ w * imgW w c i := Nat.mul_le_mul_left _ h
          rw [Nat.mul_succ] at this
          omega
        · exact h
        · have : w * (imgW w c i + 1) ≤ w * imgW w c k := Nat.mul_le_mul_left _ h
          rw [Nat.mul_succ] at this
          omega
      have hki := hinj k hkn i hi hck
      subst hki
      have e : w * imgW w c k + q - w * imgW w c k = q := by omega
      rwa [e] at hb
    · intro hb
      refine ⟨i, hi, by omega, ?_⟩
      have e : w * imgW w c i + q - w * imgW w c i = q := by omega
      rwa [e]
  · rw [testBit_lt (j := q) (hk i hi) (by omega)]
    simp [hq]

private theorem tab_surj {n : Nat} {T : Array Nat} (hT : Tab n T) {U : Array Nat}
    (hl : ∀ q < n, img U (img T q) = q) : ∀ y < n, ∃ q < n, img T q = y := by
  let f : Fin n → Fin n := fun q => ⟨img T q, hT.2 q q.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : img T a = img T b := congrArg Fin.val hab
    have h2 := congrArg (img U) h1
    rw [hl a a.2, hl b b.2] at h2
    exact Fin.ext h2
  have hs := Finite.injective_iff_surjective.1 hf
  intro y hy
  obtain ⟨q, hq⟩ := hs ⟨y, hy⟩
  exact ⟨q, q.2, congrArg Fin.val hq⟩

private theorem invW_img {n w : Nat} (hw : n ≤ 2 ^ w) {c : Nat} {T U : Array Nat}
    (hc : Rep n w c T) (hT : Tab n T) (hl : ∀ q < n, img U (img T q) = q) :
    ∀ y < n, imgW w (invW n w c) y = img U y := by
  have hinj : ∀ i < n, ∀ j < n, imgW w c i = imgW w c j → i = j := by
    intro i hi j hj h
    rw [(hc.2 i hi).2, (hc.2 j hj).2] at h
    have h2 := congrArg (img U) h
    rwa [hl i hi, hl j hj] at h2
  intro y hy
  obtain ⟨q, hq, rfl⟩ := tab_surj hT hl y hy
  rw [← (hc.2 q hq).2, imgW_invW hw hinj hq, (hc.2 q hq).2, hl q hq]

private theorem foldl_other (f : List Nat → Nat) :
    ∀ (l : List (List Nat)) (m : Std.HashMap Nat Nat) (c key : Nat), key ∉ l.map f →
    ((l.foldl (fun (st : Std.HashMap Nat Nat × Nat) T => (st.1.insert (f T) st.2, st.2 + 1))
      (m, c)).1)[key]? = m[key]?
  | [], m, c, key, _ => rfl
  | T :: l, m, c, key, h => by
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, foldl_other f l _ _ key h.2, Std.HashMap.getElem?_insert]
    have : (f T == key) = false := by simpa using Ne.symm h.1
    rw [this]
    rfl

private theorem foldl_get (f : List Nat → Nat) :
    ∀ (l : List (List Nat)) (m : Std.HashMap Nat Nat) (c : Nat), (l.map f).Nodup →
    ∀ k (hk : k < l.length),
    ((l.foldl (fun (st : Std.HashMap Nat Nat × Nat) T => (st.1.insert (f T) st.2, st.2 + 1))
      (m, c)).1)[f l[k]]? = some (c + k)
  | [], _, _, _, k, hk => by simp at hk
  | T :: l, m, c, hnd, k, hk => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases k with _ | k
    · rw [List.getElem_cons_zero, foldl_other f l _ _ _ hnd.1, Std.HashMap.getElem?_insert_self]
      rfl
    · rw [List.getElem_cons_succ, foldl_get f l _ (c + 1) hnd.2 k (by simpa using hk)]
      congr 1
      omega

private theorem memR_of_mem {n : Nat} {P : List Nat} {Ts : Array (List Nat)} {E : Array Nat}
    (hnd : (Ts.toList.map (keyNat n n)).Nodup) (hm : P.map (img E) ∈ Ts.toList) :
    memR n P Ts (keyMap n Ts) E = true := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 hm
  have hl := foldl_get (keyNat n n) Ts.toList ∅ 0 hnd k hk
  rw [hke] at hl
  have e : keyMap n Ts = ((Ts.toList.foldl (fun (st : Std.HashMap Nat Nat × Nat) T =>
      (st.1.insert (keyNat n n T) st.2, st.2 + 1)) (∅, 0)).1) := by
    rw [keyMap, Array.foldl_toList]
  simp only [memR]
  rw [e, hl]
  simp only [Nat.zero_add]
  have : Ts.getD k [] = P.map (img E) := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hk, ← hke]
    rfl
  simp [this]

private def Cl (n w : Nat) (Ts : List (List Nat)) (x : Nat) : Prop :=
  ∀ T ∈ Ts, (∀ y ∈ T, y < n) → T.map (imgW w x) ∈ Ts

private theorem imgW_mulW {n w : Nat} (x g : Nat) {y : Nat} (hy : y < n) :
    imgW w (mulW n w x g) y = imgW w x (imgW w g y) := by
  rw [mulW, imgW_ofFnW (fun j _ => imgW_lt _ _ _) hy]

private theorem cl_one {n w : Nat} (hw : n ≤ 2 ^ w) (Ts : List (List Nat)) :
    Cl n w Ts (oneW n w) := by
  intro T hT hlt
  have : T.map (imgW w (oneW n w)) = T := by
    rw [List.map_congr_left (g := id) (fun y hy => by
      rw [oneW, imgW_ofFnW (fun j hj => by omega) (hlt y hy)]; rfl), List.map_id]
  rwa [this]

private theorem cl_mul {n w : Nat} (Ts : List (List Nat)) {x g : Nat} (hx : Cl n w Ts x)
    (hgl : ∀ y < n, imgW w g y < n) (hg : Cl n w Ts g) : Cl n w Ts (mulW n w x g) := by
  intro T hT hlt
  have e : T.map (imgW w (mulW n w x g)) = (T.map (imgW w g)).map (imgW w x) := by
    rw [List.map_map]
    exact List.map_congr_left fun y hy => imgW_mulW x g (hlt y hy)
  rw [e]
  exact hx _ (hg T hT hlt) (fun y hy => by
    rw [List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hgl z (hlt z hz))

private structure ClInv (n w : Nat) (Ts : List (List Nat)) (st : SetK × List Nat) : Prop where
  elems : ∀ y ∈ st.1.elems, Cl n w Ts y
  front : ∀ y ∈ st.2, Cl n w Ts y

private theorem clInv_addK {n w : Nat} {Ts : List (List Nat)} {st : SetK × List Nat} {y : Nat}
    (h : ClInv n w Ts st) (hy : Cl n w Ts y) : ClInv n w Ts (addK st y) := by
  cases hm : memT st.1.t y
  · rw [addK_of_not_mem hm]
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact h.elems z hz
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact h.front z hz
  · rw [addK_of_mem hm]
    exact h

private theorem clInv_inner {n w : Nat} {Ts : List (List Nat)} {x : Nat} (hx : Cl n w Ts x)
    {G : List Nat} (hG : ∀ g ∈ G, (∀ y < n, imgW w g y < n) ∧ Cl n w Ts g) :
    ∀ (gs : List Nat), (∀ g ∈ gs, g ∈ G) → ∀ st, ClInv n w Ts st →
      ClInv n w Ts (gs.foldl (fun st g => addK st (mulW n w x g)) st)
  | [], _, st, h => h
  | g :: gs, hgs, st, h => by
    rw [List.foldl_cons]
    exact clInv_inner hx hG gs (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _
      (clInv_addK h (cl_mul Ts hx (hG g (hgs g (List.mem_cons_self ..))).1
        (hG g (hgs g (List.mem_cons_self ..))).2))

private theorem clInv_outer {n w : Nat} {Ts : List (List Nat)} {G : List Nat}
    (hG : ∀ g ∈ G, (∀ y < n, imgW w g y < n) ∧ Cl n w Ts g) :
    ∀ (xs : List Nat), (∀ x ∈ xs, Cl n w Ts x) → ∀ st, ClInv n w Ts st →
      ClInv n w Ts (xs.foldl (fun st x => G.foldl (fun st g => addK st (mulW n w x g)) st) st)
  | [], _, st, h => h
  | x :: xs, hxs, st, h => by
    rw [List.foldl_cons]
    exact clInv_outer hG xs (fun x' hx' => hxs x' (List.mem_cons_of_mem _ hx')) _
      (clInv_inner (hxs x (List.mem_cons_self ..)) hG G (fun g hg => hg) st h)

private noncomputable def stP (mf : Nat → Nat → Nat) (o : Nat) (G : List Nat) (d : Nat) : SetK × List Nat :=
  Nat.rec (motive := fun _ => SetK × List Nat) (Prod.mk (SetK.mk (NT.nd NT.lf o NT.lf) 1 [o]) [o])
    (fun _ st => roundG mf G st.1 st.2) d

private theorem clInv_stP {n w : Nat} (hw : n ≤ 2 ^ w) {Ts : List (List Nat)} {G : List Nat}
    (hG : ∀ g ∈ G, (∀ y < n, imgW w g y < n) ∧ Cl n w Ts g) :
    ∀ d, ClInv n w Ts (stP (mulW n w) (oneW n w) G d)
  | 0 => ⟨fun y hy => by
      have : y = oneW n w := by simpa [stP] using hy
      subst this; exact cl_one hw Ts,
    fun y hy => by
      have : y = oneW n w := by simpa [stP] using hy
      subst this; exact cl_one hw Ts⟩
  | d + 1 => by
    have ih := clInv_stP hw hG d
    have e : stP (mulW n w) (oneW n w) G (d + 1) =
        roundG (mulW n w) G (stP (mulW n w) (oneW n w) G d).1
          (stP (mulW n w) (oneW n w) G d).2 := rfl
    rw [e, roundG_eq]
    exact clInv_outer hG _ ih.front _ ⟨ih.elems, fun y hy => by simp at hy⟩

private theorem cl_bfsG {n w : Nat} (hw : n ≤ 2 ^ w) {Ts : List (List Nat)} {G : List Nat}
    (hG : ∀ g ∈ G, (∀ y < n, imgW w g y < n) ∧ Cl n w Ts g) (d : Nat) :
    ∀ y ∈ (bfsG (mulW n w) (oneW n w) G d).elems, Cl n w Ts y :=
  (clInv_stP hw hG d).elems

private theorem gcodes_eq (R : List Nat) (qp : List (Nat × Nat)) :
    (List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (nodeK R p.1) ih) qp :
      List Nat) = qp.map fun p => nodeK R p.1 := by
  induction qp with
  | nil => rfl
  | cons p t ih =>
    change nodeK R p.1 :: _ = _
    rw [ih, List.map_cons]

private theorem rl_mem {n w : Nat} (hw : n ≤ 2 ^ w) (a b : Array (Array Nat))
    (prog qp : List (Nat × Nat)) (k fuel d : Nat) (RL : List Nat)
    (hen : enumK n w (chunksK a) (chunksK b) prog qp k fuel d RL = true)
    {Ts : Array (List Nat)} {par cl : Array Nat}
    (hBE : BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) Ts par cl) :
    (∀ y ∈ ptsOf (List.range n)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!), y < n) ∧
    ∀ x ∈ RL, (ptsOf (List.range n)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)).map
        (imgW w x) ∈ Ts.toList := by
  unfold enumK at hen
  simp only [andB_eq, Bool.and_eq_true] at hen
  obtain ⟨hta, htb, hso, her⟩ := hen
  unfold enumR at her
  simp only [andB_eq, Bool.and_eq_true, allBs_cons, allBs_nil, Bool.and_true] at her
  obtain ⟨hq1, hq2, hcl, hsz, hfu, heq⟩ := her
  rw [gcodes_eq] at heq
  have hRL := (eqL_iff _ _).1 heq
  set R := slpW n w (codeK w (chunksK a)) (codeK w (chunksK b)) prog with hR
  have hs := slpW_rep hw hta htb hso
  have e1 : (chunksK a).toArray = Array.flatten a := by rw [chunksK_eq, Array.toArray_toList]
  have e2 : (chunksK b).toArray = Array.flatten b := by rw [chunksK_eq, Array.toArray_toList]
  rw [e1, e2] at hs
  obtain ⟨hlen, hrep⟩ := hs
  set slpT := slpTabsA (Array.flatten a) (Array.flatten b) prog with hslp
  rw [allA_eq, List.all_eq_true] at hq1
  obtain ⟨hpos, hT0, -, -, -, hBcl, -⟩ := hBE
  have hqa : ∀ p ∈ qp, p.1 < slpT.size := by
    intro p hp
    have := hq1 p hp
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, lenA_eq] at this
    rw [← hlen, lenA_eq]
    exact this.1
  have hGen : ∀ g ∈ qp.map (fun p => nodeK R p.1),
      (∀ y < n, imgW w g y < n) ∧ Cl n w Ts.toList g := by
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    have hrp := hrep p.1 (hqa p hp)
    refine ⟨fun y hy => ?_, ?_⟩
    · rw [(hrp.2 y hy).2]
      exact (hrp.2 y hy).1
    · intro T hT hlt
      obtain ⟨i, hi, rfl⟩ := mem_idx hT
      obtain ⟨j, hj', hjp⟩ := List.mem_iff_getElem.1 hp
      have hc := hBcl i hi j (by simpa using hj')
      have hG : (qp.map fun p => slpT[p.1]!)[j]! = slpT[p.1]! := by
        rw [getElem!_pos _ j (by simpa using hj'), List.getElem_map, hjp]
      rw [hG] at hc
      have e : Ts[i]!.map (imgW w (nodeK R p.1)) = applyTab slpT[p.1]! Ts[i]! := by
        rw [applyTab]
        exact List.map_congr_left fun y hy => (hrp.2 y (hlt y hy)).2
      rw [e, ← hc.2]
      exact get_mem hc.1
  have hP : ∀ y ∈ ptsOf (List.range n) (qp.map fun p => slpT[p.1]!), y < n := by
    intro y hy
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hy
    rcases hy with hy | ⟨s, hs, hy⟩
    · exact List.mem_range.1 hy
    · rw [List.mem_map] at hs hy
      obtain ⟨p, hp, rfl⟩ := hs
      obtain ⟨b0, hb0, rfl⟩ := hy
      exact (hrep p.1 (hqa p hp)).2 b0 (List.mem_range.1 hb0) |>.1
  refine ⟨hP, fun x hx => ?_⟩
  rw [← hRL] at hx
  have hCl := cl_bfsG hw hGen d x hx
  have hP' := hP
  rw [← hT0] at hP' ⊢
  exact hCl _ (get_mem hpos) hP'

private theorem treeOf_spec (RL : List Nat) :
    OrdN (treeOf RL) ∧ ∀ y, memN (treeOf RL) y ↔ y ∈ RL := by
  induction RL with
  | nil => exact ⟨trivial, fun y => by simp [treeOf, memN]⟩
  | cons x t ih =>
    have e : treeOf (x :: t) = insT (treeOf t) x := rfl
    rw [e]
    refine ⟨ord_insT x ih.1, fun y => ?_⟩
    rw [mem_insT, ih.2 y, List.mem_cons]

private theorem mem_of_memT (RL : List Nat) {x : Nat} (h : memT (treeOf RL) x = true) : x ∈ RL := by
  have := treeOf_spec RL
  rw [memT_iff this.1, this.2] at h
  exact h

private theorem entry_mem {n w N : Nat} (hw : n ≤ 2 ^ w) {c : Nat} {g : Array Nat}
    (hc : Rep n w c g) (hg : Tab n g) {RF : Nat → Nat} {T U : Array (Array Nat)}
    (hRF : ∀ j < N, Rep n w (RF j) (T.getD j #[]))
    (hT : ∀ j < N, Tab n (T.getD j #[]))
    (hU : ∀ j < N, Tab n (U.getD j #[]))
    (hinvT : ∀ j < N, ∀ q < n, img (U.getD j #[]) (img (T.getD j #[]) q) = q)
    {i j : Nat} (hi : i < N) (hj : j < N)
    {RL : List Nat} {P : List Nat} (hP : ∀ q ∈ P, q < n) {Ts : Array (List Nat)}
    (hmem : ∀ x ∈ RL, P.map (imgW w x) ∈ Ts.toList)
    (hnd : (Ts.toList.map (keyNat n n)).Nodup)
    (hm : memT (treeOf RL) (mulW n w (invW n w (RF j)) (mulW n w c (RF i))) = true) :
    memR n P Ts (keyMap n Ts) (compArr (U.getD j #[]) (compArr g (T.getD i #[]))) = true := by
  apply memR_of_mem hnd
  have h1 := hmem _ (mem_of_memT RL hm)
  convert h1 using 1
  apply List.map_congr_left
  intro q hq
  have hqn := hP q hq
  have hinvj := invW_img hw (hRF j hj) (hT j hj) (hinvT j hj)
  obtain ⟨hgT, kgT⟩ := tab_comp hg (hT i hi)
  obtain ⟨hE, kE⟩ := tab_comp (hU j hj) hgT
  rw [kE q hqn, kgT q hqn, imgW_mulW _ _ hqn, imgW_mulW _ _ hqn, (hRF i hi).2 q hqn |>.2,
    (hc.2 _ ((hT i hi).2 q hqn)).2]
  rw [hinvj _ (hg.2 _ ((hT i hi).2 q hqn))]

private theorem tabs_of_invK {n w : Nat} {ta tb tai tbi : List Nat}
    (h : invK n w ta tb tai tbi = true) :
    tabL n ta = true ∧ tabL n tb = true ∧ tabL n tai = true ∧ tabL n tbi = true := by
  unfold invK at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

private theorem tab_of_rep {n w c : Nat} {t : Array Nat} (h : Rep n w c t) : Tab n t :=
  ⟨h.1, fun q hq => (h.2 q hq).1⟩

private theorem imgW_chunks {N W : Nat} (hW : N ≤ 2 ^ W) {c : Array (Array Nat)}
    (h : tabL N (chunksK c) = true) {K : Nat} (hK : Nat.beq (codeK W (chunksK c)) K = true)
    {i : Nat} (hi : i < N) :
    imgW W K i = (Array.flatten c).getD i 0 ∧ (Array.flatten c).getD i 0 < N := by
  have hr := rep_chunksK hW h
  rw [← Nat.eq_of_beq_eq_true hK]
  exact ⟨(hr.2 i hi).2, (hr.2 i hi).1⟩

theorem edge_sound_aux {n w W N : Nat} (hw : n ≤ 2 ^ w) (hW : N ≤ 2 ^ W)
    (a b ai bi Aa Ab ps gs : Array (Array Nat)) (prog qp : List (Nat × Nat)) (k fuel d : Nat)
    (RL : List Nat) (RF : Nat → Nat) (AK BK PK GK K L : Nat)
    (hinv : invK n w (chunksK a) (chunksK b) (chunksK ai) (chunksK bi) = true)
    (htree : treeK N (chunksK ps) (chunksK gs) = true)
    (hpt : tabL N (chunksK ps) = true) (hgt : tabL N (chunksK gs) = true)
    (hat : tabL N (chunksK Aa) = true) (hbt : tabL N (chunksK Ab) = true)
    (hen : enumK n w (chunksK a) (chunksK b) prog qp k fuel d RL = true)
    (hAK : Nat.beq (codeK W (chunksK Aa)) AK = true) (hBK : Nat.beq (codeK W (chunksK Ab)) BK = true)
    (hPK : Nat.beq (codeK W (chunksK ps)) PK = true) (hGK : Nat.beq (codeK W (chunksK gs)) GK = true)
    (hKL : K * L = N)
    (he : ∀ c < K, edgeChunk n w W N (codeK w (chunksK a)) (codeK w (chunksK b)) AK BK PK GK RF
      (treeOf RL) (c * L) L = true)
    (Ts : Array (List Nat)) (par cl : Array Nat)
    (hBE : BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) Ts par cl) :
    edgeOK n N (ptsOf (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!))
      Ts (keyMap n Ts)
      (Array.flatten a) (Array.flatten b) (Array.flatten Aa) (Array.flatten Ab)
      (treeTabs n N (Array.flatten a) (Array.flatten b) (Array.flatten ps) (Array.flatten gs))
      (treeInvTabs n N (Array.flatten ai) (Array.flatten bi) (Array.flatten ps)
        (Array.flatten gs)) = true := by
  obtain ⟨hta, htb, htai, htbi⟩ := tabs_of_invK hinv
  have hiv := inv_sound hw a b ai bi hinv
  have hv := tree_sound N ps gs htree
  have hca := rep_chunksK hw hta
  have hcb := rep_chunksK hw htb
  have hrt := allR_blocks (f := fun i => CFSG.KC.Ord.andB (rtAt n w W (codeK w (chunksK a))
    (codeK w (chunksK b)) PK GK RF i) (edgeAt n w W N (codeK w (chunksK a))
    (codeK w (chunksK b)) AK BK RF (treeOf RL) i)) hKL (fun c hc => he c hc)
  have hrt1 : ∀ i < N, rtAt n w W (codeK w (chunksK a)) (codeK w (chunksK b)) PK GK RF i = true :=
    fun i hi => (andB_iff.1 (hrt i hi)).1
  have hed : ∀ i < N, edgeAt n w W N (codeK w (chunksK a)) (codeK w (chunksK b)) AK BK RF
      (treeOf RL) i = true := fun i hi => (andB_iff.1 (hrt i hi)).2
  have hPKi : ∀ i < N, imgW W PK i = (Array.flatten ps).getD i 0 :=
    fun i hi => (imgW_chunks hW hpt hPK hi).1
  have hGKi : ∀ i < N, imgW W GK i = (Array.flatten gs).getD i 0 :=
    fun i hi => (imgW_chunks hW hgt hGK hi).1
  have hRF := tree_rep hw RF hca hcb hPKi hGKi hv hrt1
  have hN : ∀ i < N, 0 < N := fun i hi => by omega
  obtain ⟨hiv1, hiv2, hiv3, hiv4, hiv5⟩ := hiv
  have hTa : Tab n (Array.flatten a) := tab_of_rep hca
  have hTb : Tab n (Array.flatten b) := tab_of_rep hcb
  have hTai : Tab n (Array.flatten ai) := tab_of_rep (rep_chunksK hw htai)
  have hTbi : Tab n (Array.flatten bi) := tab_of_rep (rep_chunksK hw htbi)
  have hits := inv_tabs hTa hTb hTai hTbi hiv5 hv
  have hnd : (Ts.toList.map (keyNat n n)).Nodup := by
    have := hBE.2.2.2.2.1
    rwa [List.length_range] at this
  obtain ⟨hP, hmem⟩ := rl_mem hw a b prog qp k fuel d RL hen hBE
  have hT := fun j (hj : j < N) => (hits j hj).1
  have hU := fun j (hj : j < N) => (hits j hj).2.1
  have hinvT := fun j (hj : j < N) => (hits j hj).2.2
  simp only [edgeOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro i hi
  have hE := hed i hi
  simp only [edgeAt, letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq] at hE
  obtain ⟨-, -, hm1, hm2⟩ := hE
  obtain ⟨hAi, hAlt⟩ := imgW_chunks hW hat hAK hi
  obtain ⟨hBi, hBlt⟩ := imgW_chunks hW hbt hBK hi
  rw [hAi] at hm1
  rw [hBi] at hm2
  exact ⟨⟨⟨hAlt, hBlt⟩, entry_mem hw hca hTa hRF hT hU hinvT hi hAlt hP hmem hnd hm1⟩,
    entry_mem hw hcb hTb hRF hT hU hinvT hi hBlt hP hmem hnd hm2⟩

theorem edge_sound_of_enum {n w W N : Nat} (hw : n ≤ 2 ^ w) (hW : N ≤ 2 ^ W)
    (a b ai bi Aa Ab ps gs : Array (Array Nat)) (prog qp : List (Nat × Nat)) (k fuel d : Nat)
    (RL : List Nat) (RF : Nat → Nat) (AK BK PK GK K L : Nat)
    (hinv : invK n w (chunksK a) (chunksK b) (chunksK ai) (chunksK bi) = true)
    (htree : treeK N (chunksK ps) (chunksK gs) = true)
    (hpt : tabL N (chunksK ps) = true) (hgt : tabL N (chunksK gs) = true)
    (hat : tabL N (chunksK Aa) = true) (hbt : tabL N (chunksK Ab) = true)
    (hen : enumK n w (chunksK a) (chunksK b) prog qp k fuel d RL = true)
    (hAK : Nat.beq (codeK W (chunksK Aa)) AK = true) (hBK : Nat.beq (codeK W (chunksK Ab)) BK = true)
    (hPK : Nat.beq (codeK W (chunksK ps)) PK = true) (hGK : Nat.beq (codeK W (chunksK gs)) GK = true)
    (hKL : K * L = N)
    (he : ∀ c < K, edgeChunk n w W N (codeK w (chunksK a)) (codeK w (chunksK b)) AK BK PK GK RF
      (treeOf RL) (c * L) L = true)
    (hBE : BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!)
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).2.2) :
    edgeOK n N (ptsOf (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!))
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1
      (keyMap n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1)
      (Array.flatten a) (Array.flatten b) (Array.flatten Aa) (Array.flatten Ab)
      (treeTabs n N (Array.flatten a) (Array.flatten b) (Array.flatten ps) (Array.flatten gs))
      (treeInvTabs n N (Array.flatten ai) (Array.flatten bi) (Array.flatten ps)
        (Array.flatten gs)) = true :=
  edge_sound_aux hw hW a b ai bi Aa Ab ps gs prog qp k fuel d RL RF AK BK PK GK K L hinv htree hpt
    hgt hat hbt hen hAK hBK hPK hGK hKL he _ _ _ hBE

theorem edge_sound {n w W N : Nat} (hw : n ≤ 2 ^ w) (hW : N ≤ 2 ^ W)
    (a b ai bi Aa Ab ps gs : Array (Array Nat)) (prog qp : List (Nat × Nat)) (k fuel d : Nat)
    (RL : List Nat) (RF : Nat → Nat) (AK BK PK GK K L : Nat)
    (hinv : invK n w (chunksK a) (chunksK b) (chunksK ai) (chunksK bi) = true)
    (htree : treeK N (chunksK ps) (chunksK gs) = true)
    (hpt : tabL N (chunksK ps) = true) (hgt : tabL N (chunksK gs) = true)
    (hat : tabL N (chunksK Aa) = true) (hbt : tabL N (chunksK Ab) = true)
    (hen : enumK n w (chunksK a) (chunksK b) prog qp k fuel d RL = true)
    (hAK : Nat.beq (codeK W (chunksK Aa)) AK = true) (hBK : Nat.beq (codeK W (chunksK Ab)) BK = true)
    (hPK : Nat.beq (codeK W (chunksK ps)) PK = true) (hGK : Nat.beq (codeK W (chunksK gs)) GK = true)
    (hKL : K * L = N)
    (he : ∀ c < K, edgeChunk n w W N (codeK w (chunksK a)) (codeK w (chunksK b)) AK BK PK GK RF
      (treeOf RL) (c * L) L = true) :
    edgeOK n N (ptsOf (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!))
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1
      (keyMap n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1)
      (Array.flatten a) (Array.flatten b) (Array.flatten Aa) (Array.flatten Ab)
      (treeTabs n N (Array.flatten a) (Array.flatten b) (Array.flatten ps) (Array.flatten gs))
      (treeInvTabs n N (Array.flatten ai) (Array.flatten bi) (Array.flatten ps)
        (Array.flatten gs)) = true :=
  edge_sound_of_enum hw hW a b ai bi Aa Ab ps gs prog qp k fuel d RL RF AK BK PK GK K L hinv htree
    hpt hgt hat hbt hen hAK hBK hPK hGK hKL he (CFSG.KC.LQT.PPE.enum_sound hw a b prog qp k fuel d RL hen).2.1

end CFSG.KC.LQT.PPEd

end