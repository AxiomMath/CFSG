module

public import Certificates.Data.Kernel.S75Gen4.Check
public import CFSG.Certificates.Kernel.S5Ext.Sound
public import CFSG.Certificates.Kernel.S5Ext.Group
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bGen4Lift

public section

namespace CFSG.KD.S75Gen4

open CFSG.KD.S5Ext Equiv Equiv.Perm CFSG.OddStandard.Solomon75.AhatData
open CFSG.Certificates.Kernel.S5K (cat_complete)

theorem pt_eq (P x : Nat) : pt P x = (P >>> (4 * x)) &&& 15 := rfl

theorem lP_eq (n TAB i : Nat) : lP n TAB i = (TAB >>> (4 * n * i)) &&& (2 ^ (4 * n) - 1) := by
  change (TAB >>> (4 * n * i)) &&& ((1 <<< (4 * n)) - 1) = _
  rw [Nat.one_shiftLeft]

theorem lP_lt (n TAB i : Nat) : lP n TAB i < 2 ^ (4 * n) := by
  rw [lP_eq]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem testBit_pt (P x r : Nat) :
    (pt P x).testBit r = (P.testBit (4 * x + r) && decide (r < 4)) := by
  rw [pt_eq, Nat.testBit_and, Nat.testBit_shiftRight, (by decide : (15 : Nat) = 2 ^ 4 - 1),
    Nat.testBit_two_pow_sub_one]

theorem eq_of_pt {n P Q : Nat} (hP : P < 2 ^ (4 * n)) (hQ : Q < 2 ^ (4 * n))
    (h : ∀ x, x < n → pt P x = pt Q x) : P = Q := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 4 * n
  · have e := congrArg (Nat.testBit · (j % 4)) (h (j / 4) (by omega))
    simp only [testBit_pt] at e
    rwa [Nat.div_add_mod j 4, decide_eq_true (Nat.mod_lt j (by decide)), Bool.and_true,
      Bool.and_true] at e
  · have hle : 2 ^ (4 * n) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hP hle),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hQ hle)]

theorem comp_spec {n P Q R : Nat} (h : compB n P Q R = true) :
    ∀ x, x < n → pt R x = pt P (pt Q x) := fun x hx =>
  Nat.eq_of_beq_eq_true (recAnd (G := fun x => Nat.beq (pt R x) (pt P (pt Q x))) n h x hx)

theorem mp_spec {n TAB MP lo m : Nat} (h : mpB n TAB MP lo m = true) :
    ∀ t, t < m → ∀ c, c < 128 →
      compB n (lP n TAB (lo + t)) (lP n TAB c) (lP n TAB (lM MP (lo + t) c)) = true := by
  unfold mpB at h
  generalize (128 : Nat) = M at h ⊢
  intro t ht c hc
  exact recAnd _ (recAnd _ h t ht) c hc

theorem mp_all {n TAB MP : Nat} (h0 : mpB n TAB MP 0 32 = true) (h1 : mpB n TAB MP 32 32 = true)
    (h2 : mpB n TAB MP 64 32 = true) (h3 : mpB n TAB MP 96 32 = true) :
    ∀ g, g < 128 → ∀ c, c < 128 →
      compB n (lP n TAB g) (lP n TAB c) (lP n TAB (lM MP g c)) = true := by
  intro g hg c hc
  rcases Nat.lt_or_ge g 64 with hg64 | hg64
  · rcases Nat.lt_or_ge g 32 with hg32 | hg32
    · have e := mp_spec h0 g hg32 c hc
      rwa [Nat.zero_add] at e
    · have e := mp_spec h1 (g - 32) (by omega) c hc
      rwa [Nat.add_sub_cancel' hg32] at e
  · rcases Nat.lt_or_ge g 96 with hg96 | hg96
    · have e := mp_spec h2 (g - 64) (by omega) c hc
      rwa [Nat.add_sub_cancel' hg64] at e
    · have e := mp_spec h3 (g - 96) (by omega) c hc
      rwa [Nat.add_sub_cancel' hg96] at e

theorem lanes_inj {n TAB : Nat} (h : lanesB n TAB = true) :
    ∀ i j, i < 128 → j < 128 → lP n TAB i = lP n TAB j → i = j := by
  unfold lanesB at h
  generalize hA : (126 : Nat) = A at h
  generalize hB : (127 : Nat) = B at h
  rw [Bool.and_eq_true] at h
  have h1 := recAnd A h.1
  have h2 := recAnd B h.2
  have mono : ∀ d i, 1 ≤ i → i + d + 1 < 128 → lP n TAB i < lP n TAB (i + d + 1) := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have e := h1 k (by omega)
      rw [Nat.blt_eq] at e
      exact e
    | succ d ih =>
      intro i hi hd
      have e1 := ih i hi (by omega)
      obtain ⟨k, hk⟩ : ∃ k, i + d + 1 = k + 1 := ⟨i + d, rfl⟩
      have e := h1 k (by omega)
      rw [Nat.blt_eq] at e
      rw [hk] at e1
      have e2 : i + (d + 1) + 1 = k + 1 + 1 := by omega
      rw [e2]
      exact Nat.lt_trans e1 e
  have ne0 : ∀ i, 1 ≤ i → i < 128 → lP n TAB i ≠ lP n TAB 0 := by
    intro i hi hi'
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have e := h2 k (by omega)
    intro e'
    change Bool.not (Nat.beq (lP n TAB (k + 1)) (lP n TAB 0)) = true at e
    rw [e', Nat.beq_refl] at e
    exact absurd e (by decide)
  have lt_of : ∀ i j, i < j → j < 128 → lP n TAB i ≠ lP n TAB j := by
    intro i j hij hj e
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ne0 j (by omega) hj e.symm
    · have := mono (j - i - 1) i hi (by omega)
      rw [(by omega : i + (j - i - 1) + 1 = j)] at this
      rw [e] at this
      exact Nat.lt_irrefl _ this
  intro i j hi hj e
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd e (lt_of i j hij hj)
  · exact hij
  · exact absurd e.symm (lt_of j i hij hi)

@[expose] noncomputable def swLoop (n TAB : Nat) (SW : List (List (Nat × Nat))) (GI : List Nat) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih k => Bool.and (Bool.and (Nat.blt g 128) (Nat.beq (lP n TAB g) (swC n (SW.getD k []))))
      (ih (Nat.succ k))) GI

theorem swLoop_spec {n TAB : Nat} {SW : List (List (Nat × Nat))} :
    ∀ (GI : List Nat) (k : Nat), swLoop n TAB SW GI k = true → ∀ j, j < GI.length →
      GI.getD j 0 < 128 ∧ lP n TAB (GI.getD j 0) = swC n (SW.getD (k + j) [])
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | g :: GI, k, h, j, hj => by
    have h' : Bool.and (Bool.and (Nat.blt g 128) (Nat.beq (lP n TAB g) (swC n (SW.getD k []))))
        (swLoop n TAB SW GI (k + 1)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    cases j with
    | zero => exact ⟨h'.1.1, h'.1.2⟩
    | succ j =>
      have e := swLoop_spec GI (k + 1) h'.2 j (by simp only [List.length_cons] at hj; omega)
      rw [(by omega : k + 1 + j = k + (j + 1))] at e
      exact e

theorem sw_spec {n TAB : Nat} {GI : List Nat} {SW : List (List (Nat × Nat))}
    (h : swB n TAB GI SW = true) : GI.length = SW.length ∧ ∀ j, j < GI.length →
      GI.getD j 0 < 128 ∧ lP n TAB (GI.getD j 0) = swC n (SW.getD j []) := by
  have h' : Bool.and (Nat.beq (lenL GI) SW.length) (swLoop n TAB SW GI 0) = true := h
  rw [Bool.and_eq_true, Nat.beq_eq, lenL_eq] at h'
  refine ⟨h'.1, fun j hj => ?_⟩
  have e := swLoop_spec GI 0 h'.2 j hj
  rwa [Nat.zero_add] at e

theorem treeG_inv {MP : Nat} {GI : List Nat} {Q : Nat → Prop}
    (hs : ∀ p g, Q p → g ∈ GI → Q (lM MP p g)) :
    ∀ (l : List (Nat × Nat × Nat)) (seen : Nat), (treeG MP GI l seen).1 = true →
      (∀ v, tb seen v = true → Q v) → ∀ v, tb (treeG MP GI l seen).2 v = true → Q v
  | [], _, _, hS => hS
  | (e, p, g) :: l, seen, h, hS => by
    have h' : Bool.and (Bool.and (Bool.and (tb seen p) (inL g GI)) (Nat.beq e (lM MP p g)))
        (treeG MP GI l (seen ||| (1 <<< e))).1 = true := h
    have hE : (treeG MP GI ((e, p, g) :: l) seen).2 = (treeG MP GI l (seen ||| (1 <<< e))).2 := rfl
    rw [hE]
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    obtain ⟨⟨⟨hp, hg⟩, he⟩, hrest⟩ := h'
    refine treeG_inv hs l _ hrest ?_
    intro v hv
    rcases tb_or.mp hv with hv | hv
    · exact hS v hv
    · rw [tb_single] at hv
      rw [hv, he]
      exact hs p g (hS p hp) (inL_sound hg)

theorem tb_FULL {v : Nat} (hv : v < 128) : tb FULL v = true := by
  rw [tb_iff, FULL_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hv

theorem tb_one {v : Nat} (h : tb 1 v = true) : v = 0 := by
  rw [(by decide : (1 : Nat) = 1 <<< 0)] at h
  exact tb_single.mp h

theorem lI_lt (INVP g : Nat) : lI INVP g < 128 := by
  unfold lI
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem inv_spec {MP INVP : Nat} (h : invB2 MP INVP = true) :
    ∀ g, g < 128 → lM MP g (lI INVP g) = 0 := by
  unfold invB2 at h
  generalize (128 : Nat) = M at h ⊢
  intro g hg
  exact Nat.eq_of_beq_eq_true (recAnd M h g hg)

theorem suppC_eq (P : Nat) :
    ∀ m, suppC m P = ∑ i ∈ Finset.range m, (if pt P i = i then 0 else 1)
  | 0 => rfl
  | m + 1 => by
    rw [Finset.sum_range_succ, ← suppC_eq P m]
    change Bool.rec (motive := fun _ => Nat) (Nat.succ (suppC m P)) (suppC m P)
      (Nat.beq (pt P m) m) = _
    cases hb : Nat.beq (pt P m) m
    · have h : pt P m ≠ m := fun e => by
        rw [e, Nat.beq_refl] at hb
        exact Bool.noConfusion hb
      rw [if_neg h]
    · rw [if_pos (Nat.eq_of_beq_eq_true hb)]
      rfl

theorem genRecsB_at {n TAB MP CATP : Nat} :
    ∀ (rs : List (List Nat × List (Nat × Nat × Nat) × Nat)) (k0 : Nat),
      genRecsB n TAB MP CATP k0 rs = true → ∀ k, k0 ≤ k → k < k0 + rs.length →
      ∃ r : List Nat × List (Nat × Nat × Nat) × Nat, genRecB n TAB MP (lC CATP k) r = true
  | [], k0, _, k, h1, h2 => by
    simp only [List.length_nil, Nat.add_zero] at h2
    omega
  | r :: rs, k0, h, k, h1, h2 => by
    have h' : Bool.and (genRecB n TAB MP (lC CATP k0) r) (genRecsB n TAB MP CATP (k0 + 1) rs) =
        true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · subst e
      exact ⟨r, h'.1⟩
    · simp only [List.length_cons] at h2
      exact genRecsB_at rs (k0 + 1) h'.2 k hlt (by omega)

theorem genRec_spec {n TAB MP C : Nat} {r : List Nat × List (Nat × Nat × Nat) × Nat}
    (h : genRecB n TAB MP C r = true) :
    r.1.length < 5 ∧ (∀ a ∈ r.1, tb C a = true) ∧ (treeG MP r.1 r.2.1 1).1 = true ∧
      (treeG MP r.1 r.2.1 1).2 = C ∧
      (r.1.length = 4 → tb C r.2.2 = true ∧ lM MP r.2.2 r.2.2 = 0 ∧
        suppC n (lP n TAB r.2.2) = 4) := by
  unfold genRecB at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨hlen, has⟩, ⟨hd1, hd2⟩, hfour⟩ := h
  rw [lenL_eq] at hlen
  refine ⟨hlen, asOK_sound _ has, hd1, hd2, fun h4 => ?_⟩
  have hb : Nat.beq (lenL r.1) 4 = true := by rw [lenL_eq, h4, Nat.beq_refl]
  rw [hb] at hfour
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hfour
  exact ⟨hfour.1.1, hfour.1.2, hfour.2.2⟩

theorem getD_mem {α : Type} {l : List α} {i : ℕ} {d : α} (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem exists_getD {α : Type} {l : List α} {a : α} (d : α) (h : a ∈ l) :
    ∃ i, i < l.length ∧ l.getD i d = a := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨i, hi, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]⟩

@[expose] def RepP (n TAB i : ℕ) (σ : Perm (Fin n)) : Prop :=
  ∀ x : Fin n, pt (lP n TAB i) x.val = (σ x).val

section Perm

variable {n : ℕ} [NeZero n] {TAB : ℕ}

theorem RepP.unique {i : ℕ} {σ τ : Perm (Fin n)} (h1 : RepP n TAB i σ) (h2 : RepP n TAB i τ) :
    σ = τ :=
  Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))

theorem RepP.lane_eq {i j : ℕ} {σ : Perm (Fin n)} (h1 : RepP n TAB i σ) (h2 : RepP n TAB j σ) :
    lP n TAB i = lP n TAB j :=
  eq_of_pt (lP_lt n TAB i) (lP_lt n TAB j) fun x hx => (h1 ⟨x, hx⟩).trans (h2 ⟨x, hx⟩).symm

theorem suppC_card {i : ℕ} {σ : Perm (Fin n)} (h : RepP n TAB i σ) :
    suppC n (lP n TAB i) = σ.support.card := by
  rw [suppC_eq, ← Fin.sum_univ_eq_sum_range (fun i' => if pt (lP n TAB i) i' = i' then 0 else 1) n,
    Equiv.Perm.support, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x]
  by_cases hx : (σ x : ℕ) = x
  · have : σ x = x := Fin.ext hx
    simp [this]
  · have : σ x ≠ x := fun h' => hx (by rw [h'])
    simp [hx, this]

noncomputable def lperm (n : ℕ) (TAB i : ℕ) : Perm (Fin n) := Classical.epsilon (RepP n TAB i)

theorem lperm_eq {i : ℕ} {σ : Perm (Fin n)} (h : RepP n TAB i σ) : lperm n TAB i = σ :=
  (Classical.epsilon_spec (p := RepP n TAB i) ⟨σ, h⟩).unique h

theorem rep_lperm {i : ℕ} {σ : Perm (Fin n)} (h : RepP n TAB i σ) : RepP n TAB i (lperm n TAB i) :=
  Classical.epsilon_spec ⟨σ, h⟩

structure TabChecks (n : ℕ) [NeZero n] (TAB MP INVP : ℕ) (GI : List ℕ)
    (TREE : List (ℕ × ℕ × ℕ)) : Prop where
  idC_pt : ∀ x : Fin n, pt (idC n) x.val = x.val
  sw_pt : ∀ k, k < (genSwaps n).length → ∀ x : Fin n,
    pt (swC n ((genSwaps n).getD k [])) x.val = (swapsPerm n ((genSwaps n).getD k []) x).val
  id : idB n TAB = true
  lanes : lanesB n TAB = true
  sw : swB n TAB GI (genSwaps n) = true
  mp : ∀ g, g < 128 → ∀ c, c < 128 →
    compB n (lP n TAB g) (lP n TAB c) (lP n TAB (lM MP g c)) = true
  tree : (treeG MP GI TREE 1).1 = true
  treeAll : Nat.beq (treeG MP GI TREE 1).2 FULL = true
  inv : invB2 MP INVP = true

namespace TabChecks

variable {MP INVP : ℕ} {GI : List ℕ} {TREE : List (ℕ × ℕ × ℕ)}
  (C : TabChecks n TAB MP INVP GI TREE)
include C

theorem rep_zero : RepP n TAB 0 1 := fun x => by
  rw [Nat.eq_of_beq_eq_true C.id]
  exact C.idC_pt x

theorem rep_mul {g c : ℕ} {σ τ : Perm (Fin n)} (hg : g < 128) (hc : c < 128)
    (h1 : RepP n TAB g σ) (h2 : RepP n TAB c τ) : RepP n TAB (lM MP g c) (σ * τ) := fun x => by
  rw [comp_spec (C.mp g hg c hc) x.val x.isLt, h2 x, h1 (τ x)]
  rfl

theorem gen_rep {k : ℕ} (hk : k < GI.length) :
    GI.getD k 0 < 128 ∧ ∃ τ ∈ genPerms n, RepP n TAB (GI.getD k 0) τ := by
  obtain ⟨hlen, hsw⟩ := sw_spec C.sw
  obtain ⟨hlt, hlane⟩ := hsw k hk
  have hk' : k < (genSwaps n).length := hlen ▸ hk
  refine ⟨hlt, swapsPerm n ((genSwaps n).getD k []), List.mem_map_of_mem (getD_mem hk'), ?_⟩
  intro x
  rw [hlane]
  exact C.sw_pt k hk' x

theorem gen_of_mem {τ : Perm (Fin n)} (hτ : τ ∈ genPerms n) :
    ∃ g ∈ GI, g < 128 ∧ RepP n TAB g τ := by
  obtain ⟨sw, hsw, rfl⟩ := List.mem_map.1 hτ
  obtain ⟨k, hk, rfl⟩ := exists_getD [] hsw
  have hk' : k < GI.length := (sw_spec C.sw).1 ▸ hk
  obtain ⟨hlt, hlane⟩ := (sw_spec C.sw).2 k hk'
  refine ⟨GI.getD k 0, getD_mem hk', hlt, fun x => ?_⟩
  rw [hlane]
  exact C.sw_pt k hk x

theorem exists_rep : ∀ v, v < 128 → ∃ σ ∈ P0 n, RepP n TAB v σ := by
  have hQ := treeG_inv (MP := MP) (GI := GI)
    (Q := fun v => v < 128 ∧ ∃ σ ∈ P0 n, RepP n TAB v σ) ?_ TREE 1 C.tree ?_
  · intro v hv
    refine (hQ v ?_).2
    rw [Nat.eq_of_beq_eq_true C.treeAll]
    exact tb_FULL hv
  · rintro p g ⟨hp, σ, hσ, hrep⟩ hg
    obtain ⟨k, hk, rfl⟩ := exists_getD 0 hg
    obtain ⟨hg128, τ, hτ, hτrep⟩ := C.gen_rep hk
    exact ⟨lM_lt MP _ _, σ * τ, mul_mem hσ (Subgroup.subset_closure hτ),
      C.rep_mul hp hg128 hrep hτrep⟩
  · intro v hv
    rw [tb_one hv]
    exact ⟨by decide, 1, one_mem _, C.rep_zero⟩

theorem rep_lperm' {v : ℕ} (hv : v < 128) : RepP n TAB v (lperm n TAB v) := by
  obtain ⟨σ, -, h⟩ := C.exists_rep v hv
  exact rep_lperm h

theorem lperm_mem {v : ℕ} (hv : v < 128) : lperm n TAB v ∈ P0 n := by
  obtain ⟨σ, hσ, h⟩ := C.exists_rep v hv
  rw [lperm_eq h]
  exact hσ

theorem lperm_zero : lperm n TAB 0 = 1 := lperm_eq C.rep_zero

theorem lperm_mul {g c : ℕ} (hg : g < 128) (hc : c < 128) :
    lperm n TAB (lM MP g c) = lperm n TAB g * lperm n TAB c :=
  lperm_eq (C.rep_mul hg hc (C.rep_lperm' hg) (C.rep_lperm' hc))

theorem lperm_inv {g : ℕ} (hg : g < 128) : lperm n TAB (lI INVP g) = (lperm n TAB g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← C.lperm_mul hg (lI_lt INVP g), inv_spec C.inv g hg, C.lperm_zero]

theorem lperm_inj {i j : ℕ} (hi : i < 128) (hj : j < 128) (h : lperm n TAB i = lperm n TAB j) :
    i = j := by
  have h2 := C.rep_lperm' hj
  rw [← h] at h2
  exact lanes_inj C.lanes i j hi hj ((C.rep_lperm' hi).lane_eq h2)

theorem lperm_surj {σ : Perm (Fin n)} (hσ : σ ∈ P0 n) : ∃ v, v < 128 ∧ lperm n TAB v = σ := by
  refine Subgroup.closure_induction_right (p := fun x _ => ∃ v, v < 128 ∧ lperm n TAB v = x)
    ?_ ?_ ?_ hσ
  · exact ⟨0, by decide, C.lperm_zero⟩
  · rintro x - y hy ⟨v, hv, rfl⟩
    obtain ⟨g, -, hg, hrep⟩ := C.gen_of_mem hy
    exact ⟨lM MP v g, lM_lt MP v g, by rw [C.lperm_mul hv hg, lperm_eq hrep]⟩
  · rintro x - y hy ⟨v, hv, rfl⟩
    obtain ⟨g, -, hg, hrep⟩ := C.gen_of_mem hy
    refine ⟨lM MP v (lI INVP g), lM_lt MP _ _, ?_⟩
    rw [C.lperm_mul hv (lI_lt INVP g), C.lperm_inv hg, lperm_eq hrep]

theorem card_P0 : Nat.card (P0 n) = 2 ^ 7 := by
  let f : Fin 128 → P0 n := fun v => ⟨lperm n TAB v, C.lperm_mem v.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w h => Fin.ext (C.lperm_inj v.2 w.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨σ, hσ⟩
    obtain ⟨v, hv, rfl⟩ := C.lperm_surj hσ
    exact ⟨⟨v, hv⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

end TabChecks

def catSet (n : ℕ) (TAB CATP k : ℕ) : Set (Perm (Fin n)) :=
  {σ | ∃ g, tb (lC CATP k) g = true ∧ lperm n TAB g = σ}

theorem cat_K {CATP k g : ℕ} (hb : bndB CATP 576 = true) (h : tb (lC CATP k) g = true) :
    k < 576 := by
  by_contra hk
  rw [bnd_sound hb k (by omega), tb_zero] at h
  exact Bool.false_ne_true h

theorem cat_complete6132 {MP INVP SQP CATP : ℕ} {GI : List ℕ} {TREE : List (ℕ × ℕ × ℕ)}
    (C : TabChecks n TAB MP INVP GI TREE) (hsq : sqB MP SQP = true)
    (hbnd : bndB CATP 576 = true) (hone : Nat.beq (lC CATP 0) 1 = true)
    (hrecs : ∀ k, k < 576 → ∃ (k0 : ℕ) (rs : List (ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))),
      recsB MP INVP SQP CATP k0 rs = true ∧ k0 ≤ k ∧ k < k0 + rs.length)
    (R : Subgroup (Perm (Fin n))) (hR : R ≤ P0 n) :
    ∃ k, k < 576 ∧ (R : Set (Perm (Fin n))) = catSet n TAB CATP k := by
  have hS0 : IsPGroup 2 (P0 n) := IsPGroup.of_card C.card_P0
  have hlt : ∀ k g, tb (lC CATP k) g = true → g < 128 := fun _ _ h => tb_lC_lt h
  refine cat_complete (P0 n) hS0 576 (catSet n TAB CATP) ?_ ?_ R hR
  · refine ⟨0, by decide, Set.ext fun σ => ⟨?_, ?_⟩⟩
    · rintro ⟨g, hg, rfl⟩
      rw [Nat.eq_of_beq_eq_true hone] at hg
      rw [tb_one hg, C.lperm_zero]
      rfl
    · rintro rfl
      refine ⟨0, ?_, C.lperm_zero⟩
      rw [Nat.eq_of_beq_eq_true hone]
      decide
  · intro k hk B hB g hg hgB hgg hgN
    obtain ⟨g₀, hg₀, rfl⟩ := C.lperm_surj hg
    have hmemB : ∀ c, tb (lC CATP k) c = true → lperm n TAB c ∈ B := fun c hc => by
      rw [← SetLike.mem_coe, hB]
      exact ⟨c, hc, rfl⟩
    have hBmem : ∀ c, c < 128 → lperm n TAB c ∈ B → tb (lC CATP k) c = true := fun c hc hcB => by
      rw [← SetLike.mem_coe, hB] at hcB
      obtain ⟨c', hc', hcc'⟩ := hcB
      rwa [← C.lperm_inj (hlt k c' hc') hc hcc']
    have h1 : tb (lC CATP k) g₀ = false := by
      cases e : tb (lC CATP k) g₀
      · rfl
      · exact absurd (hmemB g₀ e) hgB
    have h2 : tb (lC CATP k) (lM MP g₀ g₀) = true :=
      hBmem _ (lM_lt MP _ _) (by rwa [C.lperm_mul hg₀ hg₀])
    have h3 : ∀ c, c < 128 → tb (lC CATP k) c = true →
        tb (lC CATP k) (lM MP (lM MP g₀ c) (lI INVP g₀)) = true := fun c hc' hc => by
      refine hBmem _ (lM_lt MP _ _) ?_
      rw [C.lperm_mul (lM_lt MP _ _) (lI_lt INVP g₀), C.lperm_mul hg₀ hc', C.lperm_inv hg₀]
      exact hgN _ (hmemB c hc)
    obtain ⟨k0, rs, hrs, hk0, hk1⟩ := hrecs k hk
    obtain ⟨h, k', hh, hk'g, hk'x⟩ := recs_sound hsq hrs k hk0 hk1 g₀ hg₀ h1 h2 h3
    have hk' : k' < 576 := cat_K hbnd hk'g
    obtain ⟨c₀, hc₀', hc₀, hgc₀⟩ := ((hk'x g₀).1 hk'g).resolve_left (by rw [h1]; decide)
    have hgh : lperm n TAB g₀ = lperm n TAB h * lperm n TAB c₀ := by
      rw [← hgc₀, C.lperm_mul hh hc₀']
    refine ⟨k', hk', fun σ => ⟨?_, ?_⟩⟩
    · rintro ⟨x, hx, rfl⟩
      rcases (hk'x x).1 hx with hx | ⟨c, hc', hc, rfl⟩
      · exact Or.inl (hmemB x hx)
      · refine Or.inr ⟨(lperm n TAB c₀)⁻¹ * lperm n TAB c,
          B.mul_mem (B.inv_mem (hmemB c₀ hc₀)) (hmemB c hc), ?_⟩
        rw [C.lperm_mul hh hc', hgh]
        group
    · rintro (hσ | ⟨b, hb, rfl⟩)
      · have hσS : σ ∈ catSet n TAB CATP k := by
          rw [← hB]
          exact hσ
        obtain ⟨c, hc, rfl⟩ := hσS
        exact ⟨c, (hk'x c).2 (Or.inl hc), rfl⟩
      · have hbS : b ∈ catSet n TAB CATP k := by
          rw [← hB]
          exact hb
        obtain ⟨c, hc, rfl⟩ := hbS
        have hc' := hlt k c hc
        have hc0c : tb (lC CATP k) (lM MP c₀ c) = true :=
          hBmem _ (lM_lt MP _ _) (by
            rw [C.lperm_mul hc₀' hc']
            exact B.mul_mem (hmemB c₀ hc₀) hb)
        refine ⟨lM MP h (lM MP c₀ c), (hk'x _).2 (Or.inr ⟨_, lM_lt MP _ _, hc0c, rfl⟩), ?_⟩
        rw [C.lperm_mul hh (lM_lt MP _ _), C.lperm_mul hc₀' hc', hgh, mul_assoc]

theorem gen_sound {MP INVP CATP k : ℕ} {GI : List ℕ} {TREE : List (ℕ × ℕ × ℕ)}
    (C : TabChecks n TAB MP INVP GI TREE) {r : List ℕ × List (ℕ × ℕ × ℕ) × ℕ}
    (hr : genRecB n TAB MP (lC CATP k) r = true) (H : Subgroup (Perm (Fin n)))
    (hH : (H : Set (Perm (Fin n))) = catSet n TAB CATP k) :
    (∃ s : Finset (Perm (Fin n)), s.card ≤ 3 ∧ Subgroup.closure (s : Set (Perm (Fin n))) = H) ∨
    (∃ s : Finset (Perm (Fin n)), s.card ≤ 4 ∧ Subgroup.closure (s : Set (Perm (Fin n))) = H ∧
      ∃ u ∈ H, DblI u) := by
  classical
  obtain ⟨hlen, has, hd1, hd2, hfour⟩ := genRec_spec hr
  have hmem : ∀ c, tb (lC CATP k) c = true → lperm n TAB c ∈ H := fun c hc => by
    rw [← SetLike.mem_coe, hH]
    exact ⟨c, hc, rfl⟩
  let s : Finset (Perm (Fin n)) := (r.1.map (lperm n TAB)).toFinset
  have hscard : s.card ≤ r.1.length := (List.toFinset_card_le _).trans (by simp)
  have hcl : Subgroup.closure (s : Set (Perm (Fin n))) = H := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro σ hσ
      simp only [s, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hσ
      obtain ⟨a, ha, rfl⟩ := hσ
      exact hmem a (has a ha)
    · intro σ hσ
      rw [← SetLike.mem_coe, hH] at hσ
      obtain ⟨v, hv, rfl⟩ := hσ
      have hQ := treeG_inv (MP := MP) (GI := r.1)
        (Q := fun v => v < 128 ∧ lperm n TAB v ∈ Subgroup.closure (s : Set (Perm (Fin n)))) ?_
        r.2.1 1 hd1 ?_
      · rw [← hd2] at hv
        exact (hQ v hv).2
      · rintro p g ⟨hp, hpc⟩ hg
        have hg' := tb_lC_lt (has g hg)
        refine ⟨lM_lt MP _ _, ?_⟩
        rw [C.lperm_mul hp hg']
        refine mul_mem hpc (Subgroup.subset_closure ?_)
        simp only [s, Finset.mem_coe, List.mem_toFinset, List.mem_map]
        exact ⟨g, hg, rfl⟩
      · intro v hv
        rw [tb_one hv, C.lperm_zero]
        exact ⟨by decide, one_mem _⟩
  by_cases h4 : r.1.length = 4
  · obtain ⟨hu, huu, hsupp⟩ := hfour h4
    have hu' := tb_lC_lt hu
    refine Or.inr ⟨s, by omega, hcl, lperm n TAB r.2.2, hmem _ hu, ?_, ?_⟩
    · rw [← C.lperm_mul hu' hu', huu, C.lperm_zero]
    · rw [← suppC_card (C.rep_lperm' hu'), hsupp]
  · exact Or.inl ⟨s, by omega, hcl⟩

theorem gen4Good_of_checks {MP INVP SQP CATP : ℕ} {GI : List ℕ} {TREE : List (ℕ × ℕ × ℕ)}
    (C : TabChecks n TAB MP INVP GI TREE) (hsq : sqB MP SQP = true)
    (hbnd : bndB CATP 576 = true) (hone : Nat.beq (lC CATP 0) 1 = true)
    (hrecs : ∀ k, k < 576 → ∃ (k0 : ℕ) (rs : List (ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))),
      recsB MP INVP SQP CATP k0 rs = true ∧ k0 ≤ k ∧ k < k0 + rs.length)
    (hgens : ∀ k, k < 576 → ∃ r : List ℕ × List (ℕ × ℕ × ℕ) × ℕ,
      genRecB n TAB MP (lC CATP k) r = true) :
    Gen4Good n (P0 n) := by
  intro H hH
  obtain ⟨k, hk, hHk⟩ := cat_complete6132 C hsq hbnd hone hrecs H hH
  obtain ⟨r, hr⟩ := hgens k hk
  exact gen_sound C hr H hHk

end Perm

end CFSG.KD.S75Gen4
