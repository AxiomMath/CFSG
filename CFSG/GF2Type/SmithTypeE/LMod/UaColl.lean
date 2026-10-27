module

public import CFSG.GF2Type.SmithTypeE.LMod.UaAct
public import Certificates.Certificate38607

public section

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open CFSG.SmithE (applyCols)

theorem collCheck_holds : chkColl = true :=
  Certificates.certificate38607

theorem collAux_uco_size : uco.size = 49 := by decide

theorem collAux_pow_mem (j : ℕ) (hj : j < 9) : 2 ^ j ∈ uco.toList := by
  have h : ∀ i < 9, 2 ^ i ∈ uco.toList := by decide
  exact h j hj

theorem collAux_ptTab_mem {c : ℕ} (h : collPtTab[c]! = true) : c ∈ uco.toList := by
  have hsz : collPtTab.size = 512 := by simp [collPtTab]
  by_cases hc : c < 512
  · rw [getElem!_pos collPtTab c (by show c < collPtTab.size; rw [hsz]; exact hc)] at h
    have h2 : c ∈ uco := by simpa [collPtTab] using h
    exact Array.mem_toList_iff.2 h2
  · rw [getElem!_neg collPtTab c (by show ¬ (c < collPtTab.size); rw [hsz]; exact hc)] at h
    exact absurd h (by decide)

theorem collAux_hP_mem {cols : Array ℕ} (hP : ∀ k < 49, collPtTab[applyCols cols uco[k]!]! = true) :
    ∀ q ∈ uco.toList, collPtTab[applyCols cols q]! = true := by
  intro q hq
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  have hk49 : k < 49 := by rw [collAux_uco_size] at hk; exact hk
  have h1 := hP k hk49
  rw [getElem!_pos uco k hk] at h1
  exact h1

theorem collAux_mem_newPts {j q : ℕ} :
    q ∈ collNewPts j ↔ q ∈ uco.toList ∧ 2 ^ j ≤ q ∧ q < 2 ^ (j + 1) := by
  unfold collNewPts
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]

theorem collAux_size_extract {cols : Array ℕ} {k : ℕ} (hk : k ≤ cols.size) :
    (cols.extract 0 k).size = k := by
  rw [Array.size_extract]; omega

theorem collAux_extract_get {cols : Array ℕ} {k m : ℕ} (hk : k ≤ cols.size) (hm : m < k) :
    (cols.extract 0 k)[m]! = cols[m]! := by
  have h1 : m < (cols.extract 0 k).size := by rw [Array.size_extract]; omega
  have h2 : m < cols.size := by omega
  rw [getElem!_pos (cols.extract 0 k) m h1, getElem!_pos cols m h2]
  simp

theorem collAux_take_push {cols : Array ℕ} {j : ℕ} (hj : j < cols.size) :
    (cols.extract 0 j).push cols[j]! = cols.extract 0 (j + 1) := by
  rw [getElem!_pos cols j hj, Array.push_extract_getElem hj]
  simp

theorem collAux_foldl_stable (F : ℕ → ℕ → ℕ) (n : ℕ) (hF : ∀ m, n ≤ m → ∀ acc, F acc m = acc)
    (d : ℕ) : (List.range (n + d)).foldl F 0 = (List.range n).foldl F 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      hF (n + d) (by omega), ih]

theorem collAux_applyCols_stable (X : Array ℕ) {n a : ℕ} (ha : a < 2 ^ n) (d : ℕ) :
    (List.range (n + d)).foldl (fun acc m => if a.testBit m then acc ^^^ X[m]! else acc) 0 =
      (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ X[m]! else acc) 0 := by
  refine collAux_foldl_stable (fun acc m => if a.testBit m then acc ^^^ X[m]! else acc) n
    (fun m hm acc => ?_) d
  have h0 : a.testBit m = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hm))
  simp [h0]

theorem collAux_foldl_congr (X Y : Array ℕ) {a : ℕ} (n : ℕ) (h : ∀ m < n, X[m]! = Y[m]!) :
    (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ X[m]! else acc) 0 =
      (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ Y[m]! else acc) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun m hm => h m (by omega))
    have hn := h n (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih', hn]

theorem collAux_take_applyCols {cols : Array ℕ} {k a : ℕ} (hk : k ≤ cols.size) (ha : a < 2 ^ k) :
    applyCols (cols.extract 0 k) a = applyCols cols a := by
  have hsz : (cols.extract 0 k).size = k := collAux_size_extract hk
  unfold applyCols
  rw [hsz, collAux_foldl_congr (cols.extract 0 k) cols k (fun m hm => collAux_extract_get hk hm)]
  obtain ⟨d, hd⟩ : ∃ d, cols.size = k + d := ⟨cols.size - k, by omega⟩
  rw [hd, collAux_applyCols_stable cols ha d]

theorem collAux_invol {cols : Array ℕ} (hs : cols.size = 9)
    (hinv : ∀ m < 9, applyCols cols cols[m]! = 2 ^ m) :
    ∀ n, n ≤ 9 → ∀ a, a < 2 ^ n → applyCols cols (applyCols cols a) = a := by
  intro n
  induction n with
  | zero =>
    intro _ a ha
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    rw [applyCols_zero, applyCols_zero]
  | succ n ih =>
    intro hn a ha
    have hn9 : n < 9 := by omega
    by_cases hlt : a < 2 ^ n
    · exact ih (by omega) a hlt
    · have hle : 2 ^ n ≤ a := Nat.not_lt.1 hlt
      have hbt : (a ^^^ 2 ^ n) < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rw [Nat.testBit_xor]
        rcases Nat.eq_or_lt_of_le hi with h | h
        · subst h
          simp [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hle ha, Nat.testBit_two_pow_self]
        · have hai : a < 2 ^ i := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) h)
          simp [Nat.testBit_lt_two_pow hai, Nat.testBit_two_pow, Nat.ne_of_lt h]
      have hab : a = (a ^^^ 2 ^ n) ^^^ 2 ^ n := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      obtain ⟨b, hb, rfl⟩ : ∃ b, b < 2 ^ n ∧ a = b ^^^ 2 ^ n := ⟨a ^^^ 2 ^ n, hbt, hab⟩
      rw [applyCols_xor, applyCols_pow (cols := cols) (m := n) (by omega), applyCols_xor,
        ih (by omega) b hb, hinv n hn9]

theorem collAux_not_span {cols : Array ℕ} (hs : cols.size = 9)
    (hinv : ∀ m < 9, applyCols cols cols[m]! = 2 ^ m) {j : ℕ} (hj : j < 9) :
    collInSpan (cols.extract 0 j) cols[j]! = false := by
  have hsz : (cols.extract 0 j).size = j := collAux_size_extract (by omega)
  unfold collInSpan
  rw [hsz, Bool.eq_false_iff]
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨s, hsmem, hse⟩ := h
  rw [List.mem_range] at hsmem
  have hse' : applyCols (cols.extract 0 j) s = cols[j]! := beq_iff_eq.1 hse
  have h1 : applyCols cols s = applyCols cols (2 ^ j) := by
    rw [← collAux_take_applyCols (cols := cols) (by omega) hsmem, hse',
      applyCols_pow (cols := cols) (m := j) (by omega)]
  have h2 : applyCols cols (applyCols cols s) = s := collAux_invol hs hinv j (by omega) s hsmem
  have h3 : applyCols cols (applyCols cols (2 ^ j)) = 2 ^ j := by
    rw [applyCols_pow (cols := cols) (m := j) (by omega), hinv j hj]
  rw [h1, h3] at h2
  rw [h2] at hsmem
  exact absurd hsmem (Nat.lt_irrefl s)

theorem collAux_search {cols : Array ℕ} (hs : cols.size = 9)
    (hP : ∀ q ∈ uco.toList, collPtTab[applyCols cols q]! = true)
    (hinv : ∀ m < 9, applyCols cols cols[m]! = 2 ^ m) :
    ∀ n j, j + n = 9 → cols ∈ collGo n (cols.extract 0 j) := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have hj9 : j = 9 := by omega
    subst hj9
    have h9 : cols.extract 0 9 = cols := Array.extract_eq_self_of_le (by omega)
    rw [collGo, h9]
    exact List.mem_singleton_self cols
  | succ n ih =>
    intro j hj
    have hj9 : j < 9 := by omega
    have hjs : j < cols.size := by omega
    have hsz : (cols.extract 0 j).size = j := collAux_size_extract (by omega)
    have hpush : (cols.extract 0 j).push cols[j]! = cols.extract 0 (j + 1) := collAux_take_push hjs
    have hpu : cols[j]! ∈ uco.toList := by
      rw [← applyCols_pow (cols := cols) (m := j) hjs]
      exact collAux_ptTab_mem (hP (2 ^ j) (collAux_pow_mem j hj9))
    have hns : collInSpan (cols.extract 0 j) cols[j]! = false := collAux_not_span hs hinv hj9
    have hall : (collNewPts (cols.extract 0 j).size).all
        (fun q => collPtTab[applyCols ((cols.extract 0 j).push cols[j]!) q]!) = true := by
      rw [List.all_eq_true]
      intro q hq
      show collPtTab[applyCols ((cols.extract 0 j).push cols[j]!) q]! = true
      rw [hsz] at hq
      obtain ⟨hqu, _, hq2⟩ := collAux_mem_newPts.1 hq
      rw [hpush, collAux_take_applyCols (cols := cols) (by omega) hq2]
      exact hP q hqu
    have hpred : ((collNewPts (cols.extract 0 j).size).all
        (fun q => collPtTab[applyCols ((cols.extract 0 j).push cols[j]!) q]!) &&
          !collInSpan (cols.extract 0 j) cols[j]!) = true := by
      rw [Bool.and_eq_true]
      exact ⟨hall, by simp [hns]⟩
    rw [collGo]
    rw [List.mem_flatMap]
    refine ⟨cols[j]!, List.mem_filter.2 ⟨hpu, hpred⟩, ?_⟩
    show cols ∈ collGo n ((cols.extract 0 j).push cols[j]!)
    rw [hpush]
    exact ih (j + 1) (by omega)

theorem mem_collL {cols : Array ℕ} (hs : cols.size = 9)
    (hP : ∀ k < 49, collPtTab[applyCols cols uco[k]!]! = true)
    (hinv : ∀ m < 9, applyCols cols cols[m]! = 2 ^ m) (hne : ∃ m < 9, cols[m]! ≠ 2 ^ m) :
    cols ∈ collL := by
  have hleaf : cols ∈ collGo 9 #[] := by
    have h := collAux_search hs (collAux_hP_mem hP) hinv 9 0 (by norm_num)
    have h0 : cols.extract 0 0 = #[] := Array.extract_zero
    rw [h0] at h
    exact h
  have hB : collInvB cols = true := by
    unfold collInvB
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true]
      intro m hm
      rw [List.mem_range] at hm
      have hm' := hinv m hm
      simpa using hm'
    · rw [List.any_eq_true]
      obtain ⟨m, hm, hne'⟩ := hne
      exact ⟨m, List.mem_range.2 hm, by simpa using hne'⟩
  unfold collL
  rw [Array.mem_toArray, List.mem_filter]
  exact ⟨hleaf, hB⟩

section Reading

attribute [local irreducible] collL collFixTab collCommTab collFixList collCommList collGo collLeaves

theorem collAux_card_filter (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ((Finset.range n).filter p).card = ((List.range n).filter fun v => decide (p v)).length := by
  simp only [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card]

theorem collAux_arr_map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (xs : Array α)
    {i : Nat} (h : i < xs.size) : (xs.map f)[i]! = f xs[i]! := by
  have h' : i < (xs.map f).size := by simpa using h
  rw [getElem!_pos (xs.map f) i h', Array.getElem_map, getElem!_pos xs i h]

theorem collAux_range_map_get {α : Type} [Inhabited α] (f : ℕ → α) {n a : ℕ} (h : a < n) :
    ((List.range n).map f)[a]! = f a := by
  have h' : a < ((List.range n).map f).length := by simpa using h
  rw [getElem!_pos ((List.range n).map f) a h', List.getElem_map, List.getElem_range]

theorem collAux_ofFn_get {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) {v : ℕ} (hv : v < n) :
    (Array.ofFn f)[v]! = f ⟨v, hv⟩ := by
  have h' : v < (Array.ofFn f).size := by simpa using hv
  rw [getElem!_pos (Array.ofFn f) v h', Array.getElem_ofFn]

theorem collAux_colsFix_get {a : Nat} (ha : a < collL.size) :
    collFixTab[a]! = Array.ofFn (n := 512) fun w : Fin 512 => applyCols collL[a]! w.val == w.val := by
  unfold collFixTab
  exact collAux_arr_map_get _ collL ha

theorem collAux_colsFix_apply {a v : Nat} (ha : a < collL.size) (hv : v < 512) :
    (collFixTab[a]!)[v]! = decide (applyCols collL[a]! v = v) := by
  rw [collAux_colsFix_get ha, collAux_ofFn_get (α := Bool) _ hv]
  exact Bool.beq_eq_decide_eq (applyCols collL[a]! v) v

theorem collAux_fixList {a : Nat} (ha : a < collL.size) :
    collFixList[a]! = (List.range 512).filter fun v => decide (applyCols collL[a]! v = v) := by
  unfold collFixList
  rw [List.getElem!_toArray, collAux_range_map_get (α := List ℕ) _ ha]
  exact List.filter_congr fun v hv => collAux_colsFix_apply ha (List.mem_range.mp hv)

theorem collAux_fixCount_eq {a : Nat} (ha : a < collL.size) :
    collFixCount a = ((List.range 512).filter fun v => decide (applyCols collL[a]! v = v)).length := by
  unfold collFixCount
  rw [collAux_fixList ha]

theorem collAux_commTab_row {a : Nat} (ha : a < collL.size) :
    collCommTab[a]! = collL.map fun B => collComm collL[a]! B := by
  unfold collCommTab
  exact collAux_arr_map_get _ collL ha

theorem collAux_commTab_apply {a b : Nat} (ha : a < collL.size) (hb : b < collL.size) :
    (collCommTab[a]!)[b]! = collComm collL[a]! collL[b]! := by
  rw [collAux_commTab_row ha]
  exact collAux_arr_map_get _ collL hb

theorem collAux_commList {a : Nat} (ha : a < collL.size) :
    collCommList[a]! = (List.range collL.size).filter fun m => (collCommTab[a]!)[m]! := by
  unfold collCommList
  rw [List.getElem!_toArray, collAux_range_map_get (α := List ℕ) _ ha]

theorem collAux_toList : collL.toList = (List.range collL.size).map fun m => collL[m]! := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  have hn : n < collL.size := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [getElem!_pos collL n hn]

theorem collAux_chk_fst {a : Nat} (ha : a < collL.size) :
    collFixCount a ≤ 64 := by
  have h := collCheck_holds
  unfold chkColl at h
  rw [Bool.and_eq_true] at h
  have h1 := List.all_eq_true.mp h.1 a (List.mem_range.mpr ha)
  rw [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1.2

theorem collAux_chk_snd {a b c : Nat} (ha : a < collL.size)
    (hb : b ∈ collCommList[a]!) (hc : c ∈ collCommList[a]!)
    (hguard : ((collCommTab[b]!)[c]! && collL[a]! != collL[b]! && collL[c]! != collL[a]! &&
      collL[c]! != collL[b]! && collMul collL[a]! collL[b]! != collL[c]!) = true) :
    collFix3 a b c ≤ 16 ∧ collComm3 a b c ≤ 23 := by
  have h := collCheck_holds
  unfold chkColl at h
  rw [Bool.and_eq_true] at h
  have h2 := List.all_eq_true.mp h.2 a (List.mem_range.mpr ha)
  have h3 := List.all_eq_true.mp h2 b hb
  have h4 := List.all_eq_true.mp h3 c hc
  rw [hguard] at h4
  simpa using h4

theorem collAux_fix3_eq {a b c : Nat} (ha : a < collL.size) (hb : b < collL.size)
    (hc : c < collL.size) :
    collFix3 a b c = ((List.range 512).filter fun v =>
      decide (applyCols collL[a]! v = v ∧ applyCols collL[b]! v = v ∧
        applyCols collL[c]! v = v)).length := by
  unfold collFix3
  rw [collAux_fixList ha, List.countP_eq_length_filter, List.filter_filter]
  refine congrArg List.length (List.filter_congr fun v hv => ?_)
  have hv' : v < 512 := List.mem_range.mp hv
  rw [collAux_colsFix_apply hb hv', collAux_colsFix_apply hc hv']
  by_cases p1 : applyCols collL[a]! v = v <;> by_cases p2 : applyCols collL[b]! v = v <;>
    by_cases p3 : applyCols collL[c]! v = v <;> simp [p1, p2, p3]

theorem collAux_bool3 (x y z : Bool) : ((y && z) && x) = ((x && y) && z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem collAux_toList_len (P : Array ℕ → Bool) :
    (collL.toList.filter P).length = ((List.range collL.size).filter fun m => P collL[m]!).length := by
  rw [collAux_toList, List.filter_map, List.length_map]
  try rfl

theorem collAux_comm3_eq {a b c : Nat} (ha : a < collL.size) (hb : b < collL.size)
    (hc : c < collL.size) :
    collComm3 a b c = (collL.toList.filter fun M => collComm collL[a]! M && collComm collL[b]! M &&
      collComm collL[c]! M).length := by
  rw [collAux_toList_len]
  unfold collComm3
  rw [collAux_commList ha, List.countP_eq_length_filter, List.filter_filter]
  refine congrArg List.length (List.filter_congr fun m hm => ?_)
  have hm' : m < collL.size := List.mem_range.mp hm
  try dsimp only
  rw [collAux_commTab_apply ha hm', collAux_commTab_apply hb hm', collAux_commTab_apply hc hm']
  exact collAux_bool3 _ _ _

theorem fix_le {A : Array ℕ} (hA : A ∈ collL) :
    ((Finset.range 512).filter fun v => applyCols A v = v).card ≤ 64 := by
  obtain ⟨a, ha, hAa⟩ := Array.mem_iff_getElem.mp hA
  have eA : collL[a]! = A := by rw [getElem!_pos collL a ha]; exact hAa
  subst eA
  rw [collAux_card_filter, ← collAux_fixCount_eq ha]
  exact collAux_chk_fst ha

theorem triple_bound {A B C : Array ℕ} (hA : A ∈ collL)
    (hB : B ∈ collL) (hC : C ∈ collL) (hAB : collComm A B = true) (hAC : collComm A C = true)
    (hBC : collComm B C = true) (h1 : A ≠ B) (h2 : C ≠ A) (h3 : C ≠ B) (h4 : collMul A B ≠ C) :
    ((Finset.range 512).filter fun v => applyCols A v = v ∧ applyCols B v = v ∧
        applyCols C v = v).card ≤ 16 ∧
      (collL.toList.filter fun M => collComm A M && collComm B M && collComm C M).length ≤ 23 := by
  obtain ⟨a, ha, hAa⟩ := Array.mem_iff_getElem.mp hA
  obtain ⟨b, hb, hBb⟩ := Array.mem_iff_getElem.mp hB
  obtain ⟨c, hc, hCc⟩ := Array.mem_iff_getElem.mp hC
  have eA : collL[a]! = A := by rw [getElem!_pos collL a ha]; exact hAa
  have eB : collL[b]! = B := by rw [getElem!_pos collL b hb]; exact hBb
  have eC : collL[c]! = C := by rw [getElem!_pos collL c hc]; exact hCc
  subst eA eB eC
  have tAB : (collCommTab[a]!)[b]! = true := by rw [collAux_commTab_apply ha hb]; exact hAB
  have tAC : (collCommTab[a]!)[c]! = true := by rw [collAux_commTab_apply ha hc]; exact hAC
  have tBC : (collCommTab[b]!)[c]! = true := by rw [collAux_commTab_apply hb hc]; exact hBC
  have mB : b ∈ collCommList[a]! := by
    rw [collAux_commList ha, List.mem_filter, List.mem_range]; exact ⟨hb, tAB⟩
  have mC : c ∈ collCommList[a]! := by
    rw [collAux_commList ha, List.mem_filter, List.mem_range]; exact ⟨hc, tAC⟩
  have hguard : ((collCommTab[b]!)[c]! && collL[a]! != collL[b]! && collL[c]! != collL[a]! &&
      collL[c]! != collL[b]! && collMul collL[a]! collL[b]! != collL[c]!) = true := by
    simp [tBC, h1, h2, h3, h4]
  obtain ⟨hf, hcm⟩ := collAux_chk_snd ha mB mC hguard
  refine ⟨?_, ?_⟩
  · rw [collAux_card_filter, ← collAux_fix3_eq ha hb hc]
    exact hf
  · rw [← collAux_comm3_eq ha hb hc]
    exact hcm

end Reading

end CFSG.GF2Type.SmithTypeE.LMod
