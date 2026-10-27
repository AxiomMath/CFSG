module

public import Certificates.Data.Kernel.GapsK
public import CFSG.Certificates.Kernel.S97RYKSound
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Sound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt

public section

namespace CFSG.KC.GapsK

open CFSG.KC.BstBfs CFSG.KC.S97RYK CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.KS
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75 CFSG.CGT.Timmesfeld75.WCCheck
open CFSG.LargeExtraspecial.S11.PairCheck CFSG.RankThree.GF2n.Tim81 CFSG.RankThree.GF2n.Tim81.Gaps
open scoped Pointwise

def insT (y : Nat) : BT → BT
  | .lf => .nd .lf y .lf
  | .nd l v r => if y < v then .nd (insT y l) v r else if v < y then .nd l v (insT y r) else .nd l v r

theorem insC_eq {α : Type} (y : Nat) : ∀ (t : BT) (k : BT → α), insC t y k = k (insT y t)
  | .lf, _ => rfl
  | .nd l v r, k => by
    change bIfK (Nat.blt y v) (insC l y fun l' => k (BT.nd l' v r))
      (bIfK (Nat.blt v y) (insC r y fun r' => k (BT.nd l v r')) (k (BT.nd l v r))) = _
    rw [bIfK_eq, bIfK_eq, insC_eq y l, insC_eq y r]
    simp only [insT, Nat.blt_eq]
    split_ifs <;> rfl

theorem inorder_eq : ∀ (t : BT) (acc : List Nat), inorder t acc = inorder t [] ++ acc
  | .lf, _ => rfl
  | .nd l v r, acc => by
    change inorder l (v :: inorder r acc) = inorder l (v :: inorder r []) ++ acc
    rw [inorder_eq l, inorder_eq r, inorder_eq l (v :: inorder r [])]
    simp

theorem mem_nd {l r : BT} {v y : Nat} :
    y ∈ inorder (.nd l v r) [] ↔ y ∈ inorder l [] ∨ y = v ∨ y ∈ inorder r [] := by
  change y ∈ inorder l (v :: inorder r []) ↔ _
  rw [inorder_eq l]
  simp

theorem memB_sound {y : Nat} : ∀ t : BT, memB t y = true → y ∈ inorder t []
  | .lf, h => absurd h Bool.false_ne_true
  | .nd l v r, h => by
    change bIfK (Nat.blt y v) (memB l y) (bIfK (Nat.blt v y) (memB r y) true) = true at h
    rw [mem_nd]
    rw [bIfK_eq, bIfK_eq] at h
    split_ifs at h with h1 h2
    · exact Or.inl (memB_sound l h)
    · exact Or.inr (Or.inr (memB_sound r h))
    · simp only [Nat.blt_eq] at h1 h2
      exact Or.inr (Or.inl (by omega))

abbrev AllQ (Q : Nat → Prop) (t : BT) : Prop := ∀ y ∈ inorder t [], Q y

theorem allQ_insT {Q : Nat → Prop} {y : Nat} (hy : Q y) : ∀ (t : BT), AllQ Q t → AllQ Q (insT y t)
  | .lf, _ => by
    intro z hz
    change z ∈ [y] at hz
    rw [List.mem_singleton.1 hz]
    exact hy
  | .nd l v r, ht => by
    have hl : AllQ Q l := fun z hz => ht z (mem_nd.2 (Or.inl hz))
    have hr : AllQ Q r := fun z hz => ht z (mem_nd.2 (Or.inr (Or.inr hz)))
    have hv : Q v := ht v (mem_nd.2 (Or.inr (Or.inl rfl)))
    simp only [insT]
    split_ifs
    · intro z hz
      rcases mem_nd.1 hz with hz | rfl | hz
      · exact allQ_insT hy l hl z hz
      · exact hv
      · exact hr z hz
    · intro z hz
      rcases mem_nd.1 hz with hz | rfl | hz
      · exact hl z hz
      · exact hv
      · exact allQ_insT hy r hr z hz
    · exact ht

section Bfs

variable (mul : Nat → Nat → Nat) (Q : Nat → Prop)

theorem stepB_sound {α : Type} (x : Nat) : ∀ (gs : List Nat), (∀ s ∈ gs, Q (mul x s)) →
    ∀ (t : BT) (F : List Nat) (k : BT → List Nat → α), AllQ Q t → (∀ y ∈ F, Q y) →
      ∃ t' F', AllQ Q t' ∧ (∀ y ∈ F', Q y) ∧ stepB mul x gs t F k = k t' F'
  | [], _, t, F, _, ht, hF => ⟨t, F, ht, hF, rfl⟩
  | s :: gs, hs, t, F, k, ht, hF => by
    have e : stepB mul x (s :: gs) t F k = strictK (mul x s) fun y =>
        bIfK (memB t y) (stepB mul x gs t F k) (insC t y fun t' => stepB mul x gs t' (y :: F) k) :=
      rfl
    have hs' : ∀ s' ∈ gs, Q (mul x s') := fun s' h => hs s' (List.mem_cons_of_mem _ h)
    have hy := hs s List.mem_cons_self
    rw [e, strictK_eq, bIfK_eq]
    split
    · exact stepB_sound x gs hs' t F k ht hF
    · rw [insC_eq]
      refine stepB_sound x gs hs' _ _ k (allQ_insT hy t ht) fun z hz => ?_
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact hF z hz

variable {gs : List Nat} (hQ : ∀ y, Q y → ∀ s ∈ gs, Q (mul y s))
include hQ

theorem roundB_sound {α : Type} : ∀ (fr : List Nat), (∀ x ∈ fr, Q x) →
    ∀ (t : BT) (F : List Nat) (k : BT → List Nat → α), AllQ Q t → (∀ y ∈ F, Q y) →
      ∃ t' F', AllQ Q t' ∧ (∀ y ∈ F', Q y) ∧ roundB mul gs fr t F k = k t' F'
  | [], _, t, F, _, ht, hF => ⟨t, F, ht, hF, rfl⟩
  | x :: fr, hfr, t, F, k, ht, hF => by
    have e : roundB mul gs (x :: fr) t F k =
        stepB mul x gs t F fun t F => roundB mul gs fr t F k := rfl
    obtain ⟨t1, F1, h1, h2, e1⟩ := stepB_sound mul Q x gs (hQ x (hfr x List.mem_cons_self)) t F
      (fun t F => roundB mul gs fr t F k) ht hF
    rw [e, e1]
    exact roundB_sound fr (fun z hz => hfr z (List.mem_cons_of_mem _ hz)) t1 F1 k h1 h2

theorem bfsB_sound {α : Type} : ∀ (fuel : Nat) (t : BT) (fr : List Nat) (k : BT → α),
    AllQ Q t → (∀ x ∈ fr, Q x) → ∃ t', AllQ Q t' ∧ bfsB mul gs fuel t fr k = k t'
  | 0, t, _, _, ht, _ => ⟨t, ht, rfl⟩
  | fuel + 1, t, fr, k, ht, hfr => by
    have e : bfsB mul gs (fuel + 1) t fr k = roundB mul gs fr t [] fun t F =>
        List.rec (motive := fun _ => α) (k t) (fun _ _ _ => bfsB mul gs fuel t F k) F := rfl
    obtain ⟨t1, F1, h1, h2, e1⟩ := roundB_sound mul Q hQ fr hfr t []
      (fun t F => List.rec (motive := fun _ => α) (k t) (fun _ _ _ => bfsB mul gs fuel t F k) F) ht
      (fun _ h => absurd h List.not_mem_nil)
    rw [e, e1]
    cases F1 with
    | nil => exact ⟨t1, h1, rfl⟩
    | cons y F1 => exact bfsB_sound fuel t1 (y :: F1) k h1 h2

theorem bfsB_true {fuel : Nat} {t : BT} {fr : List Nat} {k : BT → Bool} (ht : AllQ Q t)
    (hfr : ∀ x ∈ fr, Q x) (h : bfsB mul gs fuel t fr k = true) : ∃ t', AllQ Q t' ∧ k t' = true := by
  obtain ⟨t', h1, e⟩ := bfsB_sound mul Q hQ fuel t fr k ht hfr
  rw [e] at h
  exact ⟨t', h1, h⟩

end Bfs

theorem sincK_sound : ∀ (L : List Nat) (p : Nat), sincK L p = true →
    (∀ x ∈ L, p < x) ∧ L.Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | x :: L, p, h => by
    change bIfK (Nat.blt p x) (sincK L x) false = true at h
    cases hb : Nat.blt p x with
    | false =>
      rw [hb] at h
      exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      obtain ⟨h2, h3⟩ := sincK_sound L x h
      have hpx : p < x := by
        rw [← Nat.blt_eq]
        exact hb
      refine ⟨fun y hy => ?_, List.Pairwise.cons h2 h3⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hpx
      · exact lt_trans hpx (h2 y hy)

theorem sincL_nodup : ∀ (L : List Nat), sincL L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: L, h => by
    obtain ⟨h1, h2⟩ := sincK_sound L x h
    exact (List.Pairwise.cons h1 h2).imp fun {_ _} h => Nat.ne_of_lt h

section Codes

variable {n : Nat} {M : Subgroup (Equiv.Perm (Fin n))}

def tabP (x : M) : Table := Array.ofFn fun i : Fin n => UInt32.ofNat ((x : Equiv.Perm (Fin n)) i).val

noncomputable def cdM (x : M) : Nat := encK n (tabP x)

theorem rep_tabP (hn : n < 2 ^ 32) (x : M) : Rep n (tabP x) x := by
  intro i hi
  unfold tabP
  rw [ap_ofFn _ hi, idx_of_lt _ hi, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_trans ((x : Equiv.Perm (Fin n)) ⟨i, hi⟩).isLt hn)]
  rfl

theorem validT_tabP (hn : n < 2 ^ 32) (x : M) : validT n (tabP x) = true :=
  validT_iff.2 ⟨Array.size_ofFn, fun i hi => by rw [rep_tabP hn x i hi]; exact idx_lt _ hi⟩

theorem encK_of_rep (hn : n < 2 ^ 32) {t : Table} {x : M} (ht : Rep n t x) (hs : t.size = n) :
    encK n t = cdM x := by
  rw [beq_iff_eq.1 (beq_of_eq ht (rep_tabP hn x) hs Array.size_ofFn)]
  rfl

theorem cdM_mul (h32 : n < 32) (x y : M) : cdM (x * y) = mulK n (cdM x) (cdM y) := by
  have hn : n < 2 ^ 32 := by omega
  rw [← encK_of_rep hn (Rep.compT (rep_tabP hn x) (rep_tabP hn y)) (size_compT' _ _)]
  exact encK_compT h32 (validT_tabP hn y)

theorem cdM_one (hn : n < 2 ^ 32) : cdM (1 : M) = encK n (idT n) :=
  (encK_of_rep hn (Rep.idT hn) size_idT').symm

theorem cdM_inj (h32 : n < 32) : Function.Injective (cdM (M := M)) := by
  intro x y h
  have hn : n < 2 ^ 32 := by omega
  have e := encK_inj h32 (validT_tabP hn x) (validT_tabP hn y) h
  have hy : Rep n (tabP x) y := by
    rw [e]
    exact rep_tabP hn y
  exact eq_of_rep (rep_tabP hn x) hy

theorem imgW_cdM (h32 : n < 32) (x : M) {i : Nat} (hi : i < n) :
    imgW 5 (cdM x) i = ((x : Equiv.Perm (Fin n)) ⟨i, hi⟩).val := by
  have hn : n < 2 ^ 32 := by omega
  unfold cdM
  rw [imgW_encK_lt hi, rep_tabP hn x i hi, idx_of_lt _ hi,
    Nat.mod_eq_of_lt (lt_trans (x • (⟨i, hi⟩ : Fin n)).isLt h32)]
  rfl

end Codes

theorem testBit_bmK (B : List Nat) (j : Nat) : (bmK B).testBit j = true ↔ j ∈ B := by
  induction B with
  | nil => simp [bmK]
  | cons i B ih =>
    change ((1 <<< i) ||| bmK B).testBit j = true ↔ _
    rw [Nat.testBit_lor, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq, List.mem_cons, eq_comm]

theorem testBit_imgMK (x : Nat) (B : List Nat) (j : Nat) :
    (imgMK x B).testBit j = true ↔ ∃ i ∈ B, imgW 5 x i = j := by
  induction B with
  | nil => simp [imgMK]
  | cons i B ih =>
    change ((1 <<< imgW 5 x i) ||| imgMK x B).testBit j = true ↔ _
    rw [Nat.testBit_lor, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq]
    simp

theorem finOfNat_lt {n : Nat} [NeZero n] {b : Nat} (hb : b < n) :
    Fin.ofNat n b = (⟨b, hb⟩ : Fin n) :=
  Fin.ext (by simp [Fin.val_ofNat, Nat.mod_eq_of_lt hb])

theorem imgMK_eq_iff {n : Nat} [NeZero n] {M : Subgroup (Equiv.Perm (Fin n))} (h32 : n < 32)
    (x : M) {B B' : List Nat} (hB : ∀ i ∈ B, i < n) (hB' : ∀ j ∈ B', j < n) :
    imgMK (cdM x) B = bmK B' ↔
      (blockFinset n B).image (x : Equiv.Perm (Fin n)) = blockFinset n B' := by
  constructor
  · intro h
    have key : ∀ j, (∃ i ∈ B, imgW 5 (cdM x) i = j) ↔ j ∈ B' := fun j => by
      rw [← testBit_imgMK, h, testBit_bmK]
    ext y
    simp only [blockFinset, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      have hbn := hB b hb
      refine ⟨((x : Equiv.Perm (Fin n)) (Fin.ofNat n b)).val, (key _).1 ⟨b, hb, ?_⟩,
        Fin.ofNat_val_eq_self _⟩
      rw [imgW_cdM h32 x hbn, finOfNat_lt hbn]
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, hi, e⟩ := (key j).2 hj
      have hin := hB i hi
      refine ⟨Fin.ofNat n i, ⟨i, hi, rfl⟩, Fin.ext ?_⟩
      rw [finOfNat_lt hin, ← imgW_cdM h32 x hin, e, finOfNat_lt (hB' j hj)]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Bool.eq_iff_iff, testBit_imgMK, testBit_bmK]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hin := hB i hi
      have hmem : (x : Equiv.Perm (Fin n)) ⟨i, hin⟩ ∈ blockFinset n B' := by
        rw [← h]
        exact Finset.mem_image.2 ⟨⟨i, hin⟩, by
          simp only [blockFinset, Finset.mem_image, List.mem_toFinset]
          exact ⟨i, hi, finOfNat_lt hin⟩, rfl⟩
      simp only [blockFinset, Finset.mem_image, List.mem_toFinset] at hmem
      obtain ⟨b, hb, e⟩ := hmem
      rw [imgW_cdM h32 x hin, ← e, finOfNat_lt (hB' b hb)]
      exact hb
    · intro hj
      have hjn := hB' j hj
      have hmem : Fin.ofNat n j ∈ (blockFinset n B).image (x : Equiv.Perm (Fin n)) := by
        rw [h]
        simp only [blockFinset, Finset.mem_image, List.mem_toFinset]
        exact ⟨j, hj, rfl⟩
      simp only [blockFinset, Finset.mem_image, List.mem_toFinset] at hmem
      obtain ⟨a, ⟨b, hb, rfl⟩, e⟩ := hmem
      have hbn := hB b hb
      refine ⟨b, hb, ?_⟩
      rw [imgW_cdM h32 x hbn, ← finOfNat_lt hbn, e, finOfNat_lt hjn]

theorem cntK_eq (bs : List (List Nat)) : ∀ E : List Nat, cntK bs E = (E.filter (fixK bs)).length
  | [] => rfl
  | x :: E => by
    change bIfK (fixK bs x) (Nat.succ (cntK bs E)) (cntK bs E) = _
    rw [bIfK_eq, List.filter_cons, cntK_eq bs E]
    cases fixK bs x <;> rfl

theorem closK_sound {n : Nat} {M : Subgroup (Equiv.Perm (Fin n))} (h32 : n < 32)
    {fuel : Nat} {us vs S : List Nat} {k : List Nat → Bool}
    (h : closK n fuel (encK n (idT n)) us vs S k = true) :
    ∃ E : List Nat, encK n (idT n) ∈ E ∧ E.Nodup ∧ (∀ s ∈ S, s ∈ us ++ vs) ∧
      (∀ u ∈ us ++ vs, u ∈ E) ∧ (∀ x ∈ E, ∀ s ∈ S, mulK n x s ∈ E) ∧ k E = true ∧
      ((∀ s ∈ S, ∃ z : M, cdM z = s) →
        ∀ y ∈ E, ∃ x ∈ Subgroup.closure {z : M | cdM z ∈ S}, cdM x = y) := by
  have hn : n < 2 ^ 32 := by omega
  let Q : Nat → Prop := fun y => (∀ s ∈ S, ∃ z : M, cdM z = s) →
    ∃ x ∈ Subgroup.closure {z : M | cdM z ∈ S}, cdM x = y
  have hid : Q (encK n (idT n)) := fun _ => ⟨1, Subgroup.one_mem _, cdM_one hn⟩
  have hQ : ∀ y, Q y → ∀ s ∈ S, Q (mulK n y s) := by
    intro y hy s hs hall
    obtain ⟨x, hx, rfl⟩ := hy hall
    obtain ⟨z, rfl⟩ := hall s hs
    exact ⟨x * z, Subgroup.mul_mem _ hx (Subgroup.subset_closure hs), cdM_mul h32 x z⟩
  unfold closK at h
  simp only [insC_eq] at h
  have h0 : AllQ Q (insT (encK n (idT n)) BT.lf) := by
    intro y hy
    change y ∈ [encK n (idT n)] at hy
    rw [List.mem_singleton.1 hy]
    exact hid
  obtain ⟨t, ht, h⟩ := bfsB_true (mulK n) Q hQ h0 (fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact hid) h
  simp only [forceL_eq, bAnd_iff, List.all_eq_true, memK_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨inorder t [], memB_sound t h1, sincL_nodup _ h2, h3, fun u hu => memB_sound t (h4 u hu),
    fun x hx s hs => memB_sound t (h5 x hx s hs), h6, fun hall y hy => ht y hy hall⟩

theorem closure_of_closK {n : Nat} {M : Subgroup (Equiv.Perm (Fin n))} (h32 : n < 32)
    {G : List M} {X : Subgroup M} (hX : X = Subgroup.closure {g | g ∈ G}) {U S E : List Nat}
    (hU : U = G.map cdM) (hid : cdM (1 : M) ∈ E) (hnd : E.Nodup) (hSU : ∀ s ∈ S, s ∈ U)
    (hUE : ∀ u ∈ U, u ∈ E) (hcl : ∀ x ∈ E, ∀ s ∈ S, mulK n x s ∈ E)
    (hinv : (∀ s ∈ S, ∃ z : M, cdM z = s) →
      ∀ y ∈ E, ∃ x ∈ Subgroup.closure {z : M | cdM z ∈ S}, cdM x = y) :
    (∀ x : M, x ∈ X ↔ cdM x ∈ E) ∧ X = Subgroup.closure {z : M | cdM z ∈ S} ∧
      (∀ r ∈ E, ∃ x : M, cdM x = r) ∧ Nat.card X = E.length := by
  subst hU
  have hS : ∀ s ∈ S, ∃ z : M, cdM z = s := fun s hs => by
    obtain ⟨z, -, e⟩ := List.mem_map.1 (hSU s hs)
    exact ⟨z, e⟩
  have hE := hinv hS
  have hWE : ∀ x ∈ Subgroup.closure {z : M | cdM z ∈ S}, cdM x ∈ E := by
    intro x hx
    have hsub : (Subgroup.closure {z : M | cdM z ∈ S}).toSubmonoid =
        Submonoid.closure {z : M | cdM z ∈ S} := Subgroup.closure_toSubmonoid_of_finite
    have hx' : x ∈ Submonoid.closure {z : M | cdM z ∈ S} := by
      rw [← hsub]
      exact hx
    refine Submonoid.closure_induction_right (motive := fun m _ => cdM m ∈ E) hid ?_ hx'
    intro m _ y hy hm
    rw [cdM_mul h32]
    exact hcl _ hm _ hy
  have hmemW : ∀ x : M, x ∈ Subgroup.closure {z : M | cdM z ∈ S} ↔ cdM x ∈ E := fun x =>
    ⟨hWE x, fun h => by
      obtain ⟨x', hx', e⟩ := hE _ h
      rwa [← cdM_inj h32 e]⟩
  have hXW : X = Subgroup.closure {z : M | cdM z ∈ S} := by
    apply le_antisymm
    · rw [hX, Subgroup.closure_le]
      intro g hg
      exact (hmemW g).2 (hUE _ (List.mem_map_of_mem (hg : g ∈ G)))
    · rw [Subgroup.closure_le]
      intro z hz
      obtain ⟨g, hg, e⟩ := List.mem_map.1 (hSU _ (hz : cdM z ∈ S))
      rw [← cdM_inj h32 e, hX]
      exact Subgroup.subset_closure hg
  have hXE : ∀ x : M, x ∈ X ↔ cdM x ∈ E := fun x => by
    rw [hXW]
    exact hmemW x
  have hEr : ∀ r ∈ E, ∃ x : M, cdM x = r := fun r hr => (hE r hr).imp fun _ hx => hx.2
  exact ⟨hXE, hXW, hEr,
    CFSG.QuasithinUnique.Unc25K1.Six.card_of_list (cdM_inj h32) X E hnd hXE hEr⟩

section Gaps

variable {P : GData} {M : Subgroup (Equiv.Perm (Fin P.D.n))} {genG : ℤ → M}

section Codes

variable (h32 : P.D.n < 32) (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
  (hg : ∀ l, validT P.D.n (P.D.gens l) = true)
include h32 hgen hg

theorem wK_cd (w : List Int) : wK P.D w = cdM (wG P.D genG w) := by
  rw [← encK_wT h32 hg w]
  exact encK_of_rep (by omega) (rep_wT (by omega) hgen w) (size_wT w)

theorem eltK_cd (i : Nat) :
    eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) i = cdM (eltG (pcG P.D genG) i) := by
  rw [← encK_el h32 hg i]
  exact encK_of_rep (by omega) (rep_el (by omega) hgen i) (size_el i)

theorem us_cd (J : List Bool) :
    encK P.D.n (idT P.D.n) :: (idxU P.D J).map
      (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D))) =
      (gensT P.D M J genG).map cdM := by
  have hn : P.D.n < 2 ^ 32 := by omega
  rw [gensT, List.map_cons, List.map_map, cdM_one (M := M) hn]
  congr 1
  exact List.map_congr_left fun i _ => eltK_cd h32 hgen hg i

theorem vs_cd (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (J : List Bool) (c : List Int) :
    ((gensT P.D M J genG).map cdM).map (conjK P.D.n (wK P.D c) (wK P.D (invWord c))) =
      (gensTc P.D M J genG c).map cdM := by
  rw [gensTc, List.map_map, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, conjK]
  rw [wK_cd h32 hgen hg, wK_cd h32 hgen hg, wG_invWord hinv, cdM_mul h32, cdM_mul h32]

theorem closJ_sound (hinv : ∀ l, genG (-l) = (genG l)⁻¹) {T : Subgroup M} {J : List Bool}
    (hmemT : ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU P.D J, eltG (pcG P.D genG) i = x)
    {fuel : Nat} {c : List Int} {k : List Nat → List Nat → Bool}
    (h : closJ P.D fuel (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) J c k = true) :
    ∃ S E : List Nat, k S E = true ∧
      (∀ x : M, x ∈ T ⊔ conjSubgroup (wG P.D genG c) T ↔ cdM x ∈ E) ∧
      T ⊔ conjSubgroup (wG P.D genG c) T = Subgroup.closure {z : M | cdM z ∈ S} ∧
      (∀ r ∈ E, ∃ x : M, cdM x = r) ∧
      Nat.card ↥(T ⊔ conjSubgroup (wG P.D genG c) T) = E.length ∧ E.Nodup := by
  have hn : P.D.n < 2 ^ 32 := by omega
  unfold closJ at h
  simp only [strictK_eq, forceL_eq] at h
  rw [us_cd h32 hgen hg J, vs_cd h32 hgen hg hinv J c] at h
  obtain ⟨E, hid, hnd, hSU, hUE, hcl, hk, hinvE⟩ := closK_sound (M := M) h32 h
  have hX := (closure_gens_eq_sup (P := P) (genG := genG) (c := c) hmemT).symm
  have hid' : cdM (1 : M) ∈ E := by
    rw [cdM_one hn]
    exact hid
  obtain ⟨hXE, hXS, hEr, hcard⟩ := closure_of_closK h32 hX (by rw [List.map_append]) hid' hnd
    hSU hUE hcl hinvE
  exact ⟨_, E, hk, hXE, hXS, hEr, hcard, hnd⟩

end Codes

theorem image_mem_of_closure {n : Nat} {M : Subgroup (Equiv.Perm (Fin n))} {Z : Set M}
    {BS : Finset (Finset (Fin n))}
    (h : ∀ z ∈ Z, ∀ C ∈ BS, C.image (z : Equiv.Perm (Fin n)) ∈ BS) :
    ∀ x ∈ Subgroup.closure Z, ∀ C ∈ BS, C.image (x : Equiv.Perm (Fin n)) ∈ BS := by
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => intro B hB; simpa using hB
  | mul_right x hx y hy ih =>
      intro B hB
      have := ih _ (h y hy B hB)
      simpa [Finset.image_image] using this
  | mul_inv_cancel x hx y hy ih =>
      intro B hB
      have hyInv : B.image (y : Equiv.Perm (Fin n)).symm ∈ BS :=
        image_inv_mem_of_image_mem (h y hy) B hB
      have := ih _ hyInv
      simpa [Finset.image_image, Equiv.Perm.coe_inv] using this

theorem witness_of_alt5K (h32 : P.D.n < 32) (hnpos : 0 < P.D.n)
    (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l)) (hinv : ∀ l, genG (-l) = (genG l)⁻¹)
    (hg : ∀ l, validT P.D.n (P.D.gens l) = true) {T : Subgroup M} {J : List Bool}
    (hD : MaskFacts P M genG T J) {c : List Int} {bs : List (List Nat)} {a : Nat}
    (h : closJ P.D P.fuel (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) J c (fun S E =>
      bAnd(Nat.beq E.length (2 ^ a * 60), bAnd(blocksK P.D.n bs S, Nat.beq (cntK bs E) (2 ^ a))))
      = true) :
    ∃ g : M, SubpairWitnessAt M T g := by
  have : NeZero P.D.n := ⟨Nat.pos_iff_ne_zero.mp hnpos⟩
  obtain ⟨S, E, hk, hXE, hXS, hEr, hcardX, hnd⟩ := closJ_sound h32 hgen hg hinv hD.hmemT h
  simp only [bAnd_iff, Nat.beq_eq] at hk
  obtain ⟨hlenE, hb, hcnt⟩ := hk
  unfold blocksK at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hb
  obtain ⟨⟨⟨⟨hlen, hbnd⟩, hB⟩, hdisj⟩, hgenB⟩ := hb
  have hB' : ∀ B ∈ bs, B ≠ [] ∧ B.Nodup ∧ ∀ x ∈ B, x < P.D.n := by
    intro B hBmem
    have := hB B hBmem
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hlt : ∀ B ∈ bs, ∀ x ∈ B, x < P.D.n := fun B hBm => (hB' B hBm).2.2
  have hdisj' : ∀ i < 5, ∀ j < 5, i ≠ j → ∀ x, x ∈ bs.getD i [] → x ∉ bs.getD j [] := by
    intro i hi j hj hij x hx
    have hd := hdisj i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true] at hd
    rcases hd with hd | hd
    · exact absurd (beq_iff_eq.1 hd) hij
    · rw [List.all_eq_true] at hd
      simp only [List.contains_eq_mem, Bool.not_eq_true'] at hd
      simpa using hd x hx
  let cG := wG P.D genG c
  let X := T ⊔ conjSubgroup cG T
  have hcardX' : Nat.card X = 2 ^ a * 60 := hcardX.trans hlenE
  have hgenPres : ∀ z ∈ {z : M | cdM z ∈ S}, ∀ C ∈ blockSet P.D.n bs,
      C.image (z : Equiv.Perm (Fin P.D.n)) ∈ blockSet P.D.n bs := by
    intro z hz C hC
    rw [blockSet, List.mem_toFinset, List.mem_map] at hC
    obtain ⟨B, hBm, rfl⟩ := hC
    have hm := (memK_iff _ _).1 (hgenB (cdM z) hz B hBm)
    obtain ⟨B', hB'm, e⟩ := List.mem_map.1 hm
    rw [(imgMK_eq_iff h32 z (hlt B hBm) (hlt B' hB'm)).1 e.symm, blockSet, List.mem_toFinset]
    exact List.mem_map_of_mem hB'm
  have hPres : ∀ x ∈ X, ∀ B ∈ blockSet P.D.n bs,
      B.image (x : Equiv.Perm (Fin P.D.n)) ∈ blockSet P.D.n bs := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {z : M | cdM z ∈ S} := by
      rw [← hXS]
      exact hx
    exact image_mem_of_closure hgenPres x hx'
  let Sb : SubMulAction X (Finset (Fin P.D.n)) :=
    { carrier := ↑(blockSet P.D.n bs)
      smul_mem' := by
        rintro ⟨x, hx⟩ B hB
        simpa [Subgroup.smul_def, Finset.smul_finset_def] using hPres x hx B hB }
  let φ : X →* Equiv.Perm Sb := MulAction.toPermHom X Sb
  have hker_iff : ∀ x : X, x ∈ φ.ker ↔
      ∀ B ∈ bs, (blockFinset P.D.n B).image (x : Equiv.Perm (Fin P.D.n)) =
        blockFinset P.D.n B := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h B hB
      have hmem : blockFinset P.D.n B ∈ blockSet P.D.n bs := by
        rw [blockSet, List.mem_toFinset]
        exact List.mem_map_of_mem hB
      have hxB : x • (⟨blockFinset P.D.n B, hmem⟩ : Sb) = ⟨blockFinset P.D.n B, hmem⟩ := by
        have := congrArg (fun p : Equiv.Perm Sb => p ⟨blockFinset P.D.n B, hmem⟩) h
        simpa [φ, MulAction.toPermHom_apply] using this
      simpa [Subgroup.smul_def, Finset.smul_finset_def] using congrArg Subtype.val hxB
    · intro h
      apply Equiv.ext
      intro B
      have hBval : B.val ∈ blockSet P.D.n bs := B.2
      rw [blockSet, List.mem_toFinset, List.mem_map] at hBval
      obtain ⟨C, hC, hCB⟩ := hBval
      have hval : (x • B).val = B.val := by
        change (x : Equiv.Perm (Fin P.D.n)) • (B : Finset (Fin P.D.n)) = B.val
        rw [Finset.smul_finset_def, ← hCB]
        simpa [Equiv.Perm.smul_def] using h C hC
      simpa [φ, MulAction.toPermHom_apply] using Subtype.ext hval
  have hker : Nat.card φ.ker = 2 ^ a := by
    have hinjX : Function.Injective (fun x : X => cdM (x : M)) :=
      fun x y e => Subtype.ext (cdM_inj h32 e)
    have hY : ∀ x : X, x ∈ φ.ker ↔ cdM (x : M) ∈ E.filter (fixK bs) := by
      intro x
      rw [hker_iff, List.mem_filter]
      unfold fixK
      rw [List.all_eq_true]
      simp only [Nat.beq_eq]
      constructor
      · intro hx
        exact ⟨(hXE _).1 x.2, fun B hB => (imgMK_eq_iff h32 (x : M) (hlt B hB) (hlt B hB)).2
          (hx B hB)⟩
      · rintro ⟨-, hx⟩ B hB
        exact (imgMK_eq_iff h32 (x : M) (hlt B hB) (hlt B hB)).1 (hx B hB)
    have hs : ∀ r ∈ E.filter (fixK bs), ∃ x : X, cdM (x : M) = r := by
      intro r hr
      obtain ⟨x, rfl⟩ := hEr r (List.mem_filter.1 hr).1
      exact ⟨⟨x, (hXE x).2 (List.mem_filter.1 hr).1⟩, rfl⟩
    rw [CFSG.QuasithinUnique.Unc25K1.Six.card_of_list hinjX φ.ker _ (hnd.filter _) hY hs,
      ← cntK_eq, hcnt]
  have : Fintype Sb := Fintype.ofFinite Sb
  have hcardS : Fintype.card Sb = 5 := by
    change Fintype.card {B // B ∈ blockSet P.D.n bs} = 5
    rw [Fintype.card_coe]
    exact card_blockSet hlen hbnd (fun B hBm => (hB' B hBm).1) hdisj' hlt
  obtain ⟨R, hRnorm, hRsolv, ⟨e5⟩⟩ := exists_alt5_quotient (a := a) φ hcardS hcardX' hker
  exact ⟨cG, Or.inr ⟨R, hRnorm, hRsolv, ⟨e5⟩⟩⟩

theorem gverdictK_sound (h32 : P.D.n < 32) (hnpos : 0 < P.D.n)
    (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l)) (hinv : ∀ l, genG (-l) = (genG l)⁻¹)
    (hg : ∀ l, validT P.D.n (P.D.gens l) = true) {T : Subgroup M} {J : List Bool}
    {v : GVerdict} (hD : MaskFacts P M genG T J) (hT : IsWC T) (h4 : 4 ≤ Nat.card T)
    (h : gverdictK P.D P.fuel (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) J v = true) :
    ∃ g : M, SubpairWitnessAt M T g := by
  have hn : P.D.n < 2 ^ 32 := by omega
  let P' : PData := ⟨P.D, 0, 0, false, 0, []⟩
  cases v with
  | small =>
    have := hD.hcard
    simp only [gverdictK, Nat.blt_eq] at h
    omega
  | notClosed i j =>
    have h' : pverdictK P' (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) J (.notClosed i j) =
        true := h
    exact False.elim (witness_of_notClosed hn hgen hD (pverdictOK_of_K (P := P') h32 hg h'))
  | bad t y g =>
    simp only [gverdictK, strictK_eq] at h
    have h' : pverdictK P' (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) J (.bad t y g) =
        true := h
    exact False.elim (witness_of_bad hn hgen hinv hD hT (pverdictOK_of_K (P := P') h32 hg h'))
  | solv c a b =>
    simp only [gverdictK] at h
    obtain ⟨S, E, hk, -, -, -, hcard, -⟩ := closJ_sound h32 hgen hg hinv hD.hmemT h
    simp only [bAnd_iff, Nat.beq_eq, Nat.blt_eq] at hk
    obtain ⟨hlen, hb⟩ := hk
    let X := T ⊔ conjSubgroup (wG P.D genG c) T
    have hcardX : Nat.card X = 2 ^ a * 3 ^ b := by rw [hcard, hlen]
    refine ⟨wG P.D genG c, Or.inl ⟨?_, ?_⟩⟩
    · exact CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_card_two_three hcardX
    · intro hp
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := X)).mp hp
      have hb1 : 1 ≤ b := hb
      have h3 : 3 ∣ Nat.card X := by
        rw [hcardX]
        exact dvd_mul_of_dvd_right (pow_dvd_pow 3 hb1) _
      have h3' : 3 ∣ 2 ^ m := by rw [← hm]; exact h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)
  | alt5 c bs a =>
    simp only [gverdictK] at h
    exact witness_of_alt5K h32 hnpos hgen hinv hg hD h

theorem baseCheck_of_gapsBaseK {D : Data} (hg : ∀ l, validT D.n (D.gens l) = true)
    (h : gapsBaseK D = true) : baseCheck D = true := by
  unfold gapsBaseK at h
  simp only [strictK_eq, forceL_eq, Bool.and_eq_true, Nat.blt_eq] at h
  exact baseCheck_of_K h.1 hg h.2

theorem subpairWitness_of_gapsK (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
    (hinv : ∀ l, genG (-l) = (genG l)⁻¹)
    (hM : ∃ m : ℕ, Odd m ∧ Nat.card M = 2 ^ P.D.pc.length * m)
    (hg : ∀ l, validT P.D.n (P.D.gens l) = true) (hbase : baseCheck P.D = true)
    (h : gapsVerdictsK P = true) : SubpairWitness M := by
  unfold gapsVerdictsK at h
  simp only [strictK_eq, forceL_eq, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at h
  obtain ⟨⟨h32, hpos⟩, hv⟩ := h
  refine subpairWitness_of_masks hgen hinv hM (by omega) hpos hbase ?_
  intro J hJ T hD hT h4
  obtain ⟨p, -, hp⟩ := List.any_eq_true.1 (hv J hJ)
  rw [Bool.and_eq_true] at hp
  exact gverdictK_sound h32 hpos hgen hinv hg hD hT h4 hp.2

end Gaps

end CFSG.KC.GapsK

end
