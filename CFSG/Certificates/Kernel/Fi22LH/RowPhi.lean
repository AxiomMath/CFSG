module

public import CFSG.Certificates.Kernel.Fi22LH.Rows
public import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import CFSG.Certificates.Kernel.Fi22LH.Trees
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import CFSG.Certificates.Kernel.Fi22LH.Card
import CFSG.Certificates.Kernel.Fi22LH.Maps
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Acc
import CFSG.Sporadic.Th.CertificateChunks
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW CFSG.KC.Enum

variable {D : LHData}

theorem lb0_facts (h : LHChecks D) :
    (∀ i j, i < j → j < 351 → ent D.lb0 i < ent D.lb0 j) ∧ ∀ j < 351, ent D.lb0 j < 3510 :=
  incK_spec (walk_rest h.walkA).2.1

theorem lb1_facts (h : LHChecks D) :
    (∀ i j, i < j → j < 351 → ent D.lb1 i < ent D.lb1 j) ∧ ∀ j < 351, ent D.lb1 j < 3510 :=
  incK_spec (walk_rest h.walkB).2.1

theorem B0_bits (h : LHChecks D) :
    BitsIs (bitsOf (lhData ())[0]!) fun y => ∃ j < 351, ent D.lb0 j = y := by
  rw [B0_eq h]
  exact (bitsIs_bitsOfNat _).congr fun y _ => by rw [sb_zero h.walkA, testBit_bs]

theorem B1_bits (h : LHChecks D) :
    BitsIs (bitsOf (lhData ())[1]!) fun y => ∃ j < 351, ent D.lb1 j = y := by
  rw [B1_eq h]
  exact (bitsIs_bitsOfNat _).congr fun y _ => by rw [sb_zero h.walkB, testBit_bs]

theorem B0_at (h : LHChecks D) {x : Nat} (hx : x < 3510) :
    bitAt (bitsOf (lhData ())[0]!) x = (bs D.lb0).testBit x := by
  apply Bool.eq_iff_iff.2
  rw [(B0_bits h).2 x (by omega), testBit_bs]

theorem rowF_at (h : LHChecks D) {f : Nat} (hf : f < 3510) :
    rowF D.R D.P D.QA D.lb0 (bs D.lb0) f = true := by
  have hs := h.row (f / 440) (by omega)
  unfold rowSlW rowSl at hs
  rw [strictB_eq] at hs
  have := allN_iff.1 hs (f % 440) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 440) (f / 440)) (f % 440) = f := by
    change 440 * (f / 440) + f % 440 = f
    omega
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hf)] at this
  exact this

theorem rowF_spec (h : LHChecks D) {f : Nat} (hf : f < 3510) :
    ((bs D.lb0).testBit f = true → fd (D.P f) 0 16383 = 14080) ∧
      ((bs D.lb0).testBit f = false → fd (D.P f) 0 16383 < 14080 ∧ fd (D.P f) 0 16383 ≠ 0 ∧
        fd (D.QA (fd (D.P f) 0 16383)) 7780 4095 = f ∧
        (∀ j < 351, (sb (D.QA (fd (D.P f) 0 16383))).testBit (ent (D.R f) (ent D.lb0 j)) = true) ∧
        ∑ j ∈ Finset.range 351, (if ent (D.R f) (ent D.lb0 j) = ent D.lb0 j then 1 else 0) = 63) := by
  have hr := rowF_at h hf
  unfold rowF at hr
  rw [strictB_eq, bIf_eq, memB_eq] at hr
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [if_pos hb] at hr
    exact Nat.eq_of_beq_eq_true hr
  · rw [if_neg (by rw [hb]; simp), strictB_eq] at hr
    simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, notB_eq, Bool.not_eq_true', Nat.beq_eq,
      strictB_eq] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have h2' : fd (D.P f) 0 16383 ≠ 0 := by
      intro e
      rw [beq_true e] at h2
      exact Bool.false_ne_true h2.symm
    rw [sum351_eq] at h4
    simp only [strictN_eq, nIf_eq, memB_eq, Nat.beq_eq] at h4
    have hmem : ∀ j < 351, (sb (D.QA (fd (D.P f) 0 16383))).testBit
        (ent (D.R f) (ent D.lb0 j)) = true := by
      intro j hj
      by_contra hc
      have := Finset.single_le_sum (f := fun j => if (sb (D.QA (fd (D.P f) 0 16383))).testBit
          (ent (D.R f) (ent D.lb0 j)) = true then
          (if ent (D.R f) (ent D.lb0 j) = ent D.lb0 j then 1 else 0) else 1000)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
      rw [if_neg hc, h4] at this
      omega
    refine ⟨h1, h2', h3, hmem, ?_⟩
    rw [← h4]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_pos (hmem j (Finset.mem_range.1 hj))]

theorem rowR_get {f : Nat} (hf : f < 3510) : (rowRD D)[f]! = fd (D.P f) 0 16383 := by
  unfold rowRD
  rw [getElem!_pos _ f (by rw [Array.size_ofFn]; exact hf), Array.getElem_ofFn]

theorem rowInv_get {m : Nat} (hm : m < 14080) : (rowInvD D)[m]! = fd (D.QA m) 7780 4095 := by
  unfold rowInvD
  rw [getElem!_pos _ m (by rw [Array.size_ofFn]; exact hm), Array.getElem_ofFn]

theorem row_img (hO : OrbOK) (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hb : (bs D.lb0).testBit f = false) (y : Nat) :
    (sb (D.QA (fd (D.P f) 0 16383))).testBit y = true ↔ ∃ j < 351, ent (D.R f) (ent D.lb0 j) = y :=
  set_img_eq h.setA ((rowF_spec h hf).2 hb).1 (fun x hx y hy e => row_inj hO h hf hx hy e)
    (lb0_facts h).1 (lb0_facts h).2 ((rowF_spec h hf).2 hb).2.2.2.1 y

theorem row_imgBits (hO : OrbOK) (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hb : (bs D.lb0).testBit f = false) :
    imgBits (tauAll orbL)[f]! (bitsOf (lhData ())[0]!) =
      bitsOfNat (sb (D.QA (fd (D.P f) 0 16383))) := by
  have hT := tauAll_TR hO h f hf
  refine BitsIs.eq_bitsOfNat (bitsIs_imgBits (B0_bits h) fun x hx _ => by
    rw [(hT.2 x hx).1]; have := (hT.2 x hx).2; omega) fun y hy => ?_
  rw [row_img hO h hf hb]
  constructor
  · rintro ⟨x, hx, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, ((hT.2 _ hx).1).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ent D.lb0 j, (lb0_facts h).2 j hj, ⟨j, hj, rfl⟩, (hT.2 _ ((lb0_facts h).2 j hj)).1⟩

theorem rowR_eq (hO : OrbOK) (h : LHChecks D) :
    mkRowR (tauAll orbL) (bitsOf (lhData ())[0]!) (orbDec D.QA) = rowRD D := by
  unfold mkRowR rowRD
  congr 1
  funext f
  rw [B0_at h f.2]
  cases hb : (bs D.lb0).testBit f.val
  · rw [if_neg (by simp)]
    obtain ⟨h1, -⟩ := (rowF_spec h f.2).2 hb
    exact find_orbDec_of (fun i hi j hj e => sb_inj h.walkA hi hj e) h1 (row_imgBits hO h f.2 hb)
  · rw [if_pos rfl]
    exact ((rowF_spec h f.2).1 hb).symm

theorem c_row (hO : OrbOK) (h : LHChecks D) :
    rowOK (tauAll orbL) (bitsOf (lhData ())[0]!) (orbDec D.QA) (rowRD D) (rowInvD D) = true := by
  unfold rowOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨by simp [rowRD], by simp [rowInvD]⟩, ?_⟩, ?_⟩
  · rw [allIn_iff]
    intro f hf
    rw [B0_at h hf]
    cases hb : (bs D.lb0).testBit f
    · obtain ⟨h1, h2, h3, -⟩ := (rowF_spec h hf).2 hb
      simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
        beq_iff_eq, rowR_get hf, rowInv_get h1]
      refine ⟨⟨⟨h1, h2⟩, ?_⟩, h3⟩
      rw [orbDec_sets _ h1]
      have hT := tauAll_TR hO h f hf
      refine mapsOnto_of (B0_bits h) ((bitsIs_bitsOfNat _).congr fun y _ => row_img hO h hf hb y)
        (fun x hx => by rw [(hT.2 x hx).1]; exact (hT.2 x hx).2) fun x hx => ?_
      rw [(hT.2 x hx).1]
      constructor
      · rintro ⟨j, hj, e⟩
        exact ⟨j, hj, row_inj hO h hf ((lb0_facts h).2 j hj) hx e⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
    · rfl
  · rw [allIn_iff]
    intro m hm
    rw [rowInv_get hm]
    have hk := allN_iff.1 h.rowInv m hm
    rw [strictB_eq, bIf_eq] at hk
    by_cases e : fd (D.QA m) 7780 4095 = 3510
    · rw [e]
      rfl
    · rw [if_neg (by rw [beq_false e]; simp)] at hk
      simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, notB_eq, Bool.not_eq_true', memB_eq,
        Nat.beq_eq] at hk
      obtain ⟨h1, h2, h3⟩ := hk
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', B0_at h h1, h2, rowR_get h1, h3]
      simp [h1]

theorem ext_get! {α : Type} [Inhabited α] {a b : Array α} {N : Nat} (ha : a.size = N)
    (hb : b.size = N) (h : ∀ m < N, a[m]! = b[m]!) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro m h1 h2
  have := h m (by omega)
  rwa [getElem!_pos a m h1, getElem!_pos b m h2] at this

theorem set_fold {N v0 : Nat} {Dp : Nat → Nat} {c : Nat → Bool} : ∀ n,
    (∀ f < n, c f = true → Dp f < N) →
    (∀ f < n, ∀ f' < n, c f = true → c f' = true → Dp f = Dp f' → f = f') →
    let r := (List.range n).foldl (fun r f => if c f = true then r.set! (Dp f) f else r)
      (Array.replicate N v0)
    r.size = N ∧ (∀ f < n, c f = true → r[Dp f]! = f) ∧
      ∀ m < N, (∀ f < n, c f = true → Dp f ≠ m) → r[m]! = v0
  | 0, _, _ => by
    refine ⟨by simp, fun f hf => absurd hf (Nat.not_lt_zero _), fun m hm _ => ?_⟩
    rw [List.range_zero, List.foldl_nil, getElem!_pos _ m (by simpa using hm),
      Array.getElem_replicate]
  | n + 1, hD, hinj => by
    obtain ⟨hs, h1, h2⟩ := set_fold n (fun f hf => hD f (by omega))
      (fun f hf f' hf' => hinj f (by omega) f' (by omega))
    intro r
    simp only [r, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun r f => if c f = true then r.set! (Dp f) f else r)
      (Array.replicate N v0) = r0 at hs h1 h2
    by_cases hc : c n = true
    · rw [if_pos hc]
      have hn := hD n (by omega) hc
      refine ⟨by rw [size_set!, hs], fun f hf hcf => ?_, fun m hm hne => ?_⟩
      · rw [get!_set! _ (by rw [hs]; exact hn) (by rw [hs]; exact hD f hf hcf)]
        by_cases e : Dp n = Dp f
        · rw [if_pos e, hinj n (by omega) f hf hc hcf e]
        · rw [if_neg e]
          have hfn : f < n := by
            rcases Nat.lt_or_ge f n with h' | h'
            · exact h'
            · exact absurd (by rw [show f = n by omega]) e
          exact h1 f hfn hcf
      · rw [get!_set! _ (by rw [hs]; exact hn) (by rw [hs]; exact hm),
          if_neg (hne n (by omega) hc)]
        exact h2 m hm fun f hf hcf => hne f (by omega) hcf
    · rw [if_neg hc]
      refine ⟨hs, fun f hf hcf => ?_, fun m hm hne => h2 m hm fun f hf hcf => hne f (by omega) hcf⟩
      have hfn : f < n := by
        rcases Nat.lt_or_ge f n with h' | h'
        · exact h'
        · exact absurd (by rw [show f = n by omega] at hcf; exact hcf) hc
      exact h1 f hfn hcf

private theorem run_bind_forIn {β : Type} (n : Nat) (b : β) (f : Nat → β → Id (ForInStep β)) :
    Id.run (forIn [:n] b f >>= fun s => pure s) = forIn [:n] b f := rfl

theorem rowInv_eq (hO : OrbOK) (h : LHChecks D) :
    mkRowInv (bitsOf (lhData ())[0]!) (rowRD D) = rowInvD D := by
  let c : Nat → Bool := fun f => !bitAt (bitsOf (lhData ())[0]!) f && decide ((rowRD D)[f]! < 14080)
  have hc : ∀ f < 3510, c f = true ↔ (bs D.lb0).testBit f = false := by
    intro f hf
    simp only [c, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, B0_at h hf, rowR_get hf]
    constructor
    · exact fun h => h.1
    · intro hb
      exact ⟨hb, ((rowF_spec h hf).2 hb).1⟩
  have hD : ∀ f < 3510, c f = true → (rowRD D)[f]! < 14080 := fun f hf hcf => by
    rw [rowR_get hf]
    exact ((rowF_spec h hf).2 ((hc f hf).1 hcf)).1
  have hinj : ∀ f < 3510, ∀ f' < 3510, c f = true → c f' = true →
      (rowRD D)[f]! = (rowRD D)[f']! → f = f' := by
    intro f hf f' hf' h1 h2 e
    rw [rowR_get hf, rowR_get hf'] at e
    rw [← ((rowF_spec h hf).2 ((hc f hf).1 h1)).2.2.1,
      ← ((rowF_spec h hf').2 ((hc f' hf').1 h2)).2.2.1, e]
  obtain ⟨hs, h1, h2⟩ := set_fold (N := 14080) (v0 := 3510) (Dp := fun f => (rowRD D)[f]!) (c := c)
    3510 hD hinj
  obtain ⟨r, hr, heq⟩ : ∃ r, mkRowInv (bitsOf (lhData ())[0]!) (rowRD D) = r ∧
      r = (List.range 3510).foldl (fun r f => if c f = true then r.set! (rowRD D)[f]! f else r)
        (Array.replicate 14080 3510) := by
    unfold mkRowInv
    refine ⟨_, rfl, ?_⟩
    dsimp only
    rw [run_bind_forIn]
    refine range_loop (fun q r => r = (List.range q).foldl
        (fun r f => if c f = true then r.set! (rowRD D)[f]! f else r) (Array.replicate 14080 3510))
      (fun r => r = (List.range 3510).foldl
        (fun r f => if c f = true then r.set! (rowRD D)[f]! f else r) (Array.replicate 14080 3510))
      _ 3510 _ ?_ (fun r hr => hr) rfl
    intro q r _ hI
    split
    · rename_i hc
      change r.set! (rowRD D)[q]! q = (List.range (q + 1)).foldl
        (fun r f => if c f = true then r.set! (rowRD D)[f]! f else r) (Array.replicate 14080 3510)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hI, if_pos hc]
    · rename_i hc
      change r = (List.range (q + 1)).foldl
        (fun r f => if c f = true then r.set! (rowRD D)[f]! f else r) (Array.replicate 14080 3510)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hI, if_neg hc]
  rw [hr, heq]
  refine ext_get! hs (by simp [rowInvD]) fun m hm => ?_
  rw [rowInv_get hm]
  by_cases hex : ∃ f < 3510, c f = true ∧ (rowRD D)[f]! = m
  · obtain ⟨f, hf, hcf, e⟩ := hex
    have h1' := h1 f hf hcf
    rw [e] at h1'
    rw [h1']
    have := ((rowF_spec h hf).2 ((hc f hf).1 hcf)).2.2.1
    rw [← rowR_get hf, e] at this
    exact this.symm
  · push Not at hex
    rw [h2 m hm fun f hf hcf => hex f hf hcf]
    have hk := allN_iff.1 h.rowInv m hm
    rw [strictB_eq, bIf_eq] at hk
    by_contra hne
    rw [if_neg (by rw [beq_false (Ne.symm hne)]; simp)] at hk
    simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, notB_eq, Bool.not_eq_true', memB_eq,
      Nat.beq_eq] at hk
    obtain ⟨k1, k2, k3⟩ := hk
    exact hex _ k1 ((hc _ k1).2 k2) (by rw [rowR_get k1]; exact k3)

theorem farK_spec (h : LHChecks D) :
    fd D.mt 0 16383 < 14080 ∧ farB D.QA (fd D.mt 0 16383) = true ∧
      (∀ m < fd D.mt 0 16383, farB D.QA m = false) ∧ (∀ l < 7, (bs D.lb0).testBit (xiK l) = true) ∧
      fd (D.TF 0) 0 16383 = fd D.mt 0 16383 ∧
      posK (fun k => fd (D.TF k) 0 16383) (fun m => fd (D.QA m) 7792 16383) 16383 14080
        (fd D.mt 80 16383) = true ∧
      bfsT (fun h l => e14 (D.ph l) (fd (D.TF h) 0 16383)) 7 (fun m => fd (D.QA m) 7792 16383)
        (fun k => fd (D.TF k) 14 16383) (fun k => fd (D.TF k) 28 7) (fd D.mt 80 16383) = true ∧
      ∀ m < 14080, farB D.QA m = true → fd (D.QA m) 7792 16383 < fd D.mt 80 16383 := by
  have hf := h.far
  unfold farW farK at hf
  rw [strictB_eq] at hf
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  refine ⟨h1, h2, fun m hm => ?_, fun l hl => ?_, h5, h6, h7, fun m hm hfm => ?_⟩
  · have := allN_iff.1 h3 m hm
    rwa [notB_eq, Bool.not_eq_true'] at this
  · have := allN_iff.1 h4 l hl
    rwa [memB_eq] at this
  · have := allN_iff.1 h8 m hm
    rw [bIf_eq, if_pos hfm, Nat.blt_eq] at this
    exact this

theorem isFar_eq {m : Nat} (hm : m < 14080) : isFar (rowInvD D) m = farB D.QA m := by
  unfold isFar farB
  rw [rowInv_get hm, bAnd_eq, notB_eq]
  rfl

theorem v0_eq (hO : OrbOK) (h : LHChecks D) :
    ((List.range 14080).find? fun m => isFar (rowInvD D) m).getD 0 = fd D.mt 0 16383 := by
  obtain ⟨h1, h2, h3, -⟩ := farK_spec h
  have e : List.range 14080 = List.range (fd D.mt 0 16383) ++
      fd D.mt 0 16383 :: (List.range (14080 - (fd D.mt 0 16383 + 1))).map
        (fd D.mt 0 16383 + 1 + ·) := by
    have e1 : 14080 = fd D.mt 0 16383 + 1 + (14080 - (fd D.mt 0 16383 + 1)) := by omega
    conv_lhs => rw [e1]
    rw [List.range_add, List.range_succ, List.append_assoc, List.singleton_append]
  rw [e, List.find?_append, List.find?_eq_none.2 fun m hm => by
      rw [isFar_eq (by have := List.mem_range.1 hm; omega), h3 m (List.mem_range.1 hm)]
      simp,
    Option.none_or, List.find?_cons, isFar_eq h1, h2]
  rfl

theorem uImg_get : ∀ l < 6, uImg[l]! = uiK l := by decide

theorem closDec_ap {C : Nat → Nat} {k : Nat} (hk : k < 3510) :
    ap (closDec C).pts k = fd (C k) 0 4095 ∧ ap (closDec C).par k = fd (C k) 12 4095 ∧
      ap (closDec C).lab k = fd (C k) 24 7 := by
  have e : ∀ (o w : Nat), w < 4096 →
      ap (tabDec 3510 4096 fun k => fd (C k) o w) k = fd (C k) o w := by
    intro o w hw
    unfold ap tabDec
    rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]
    change (if fd (C k) o w = 4096 then none32 else UInt32.ofNat (fd (C k) o w)).toNat = _
    have := fd_le (C k) o w
    rw [if_neg (by omega), UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have h1 : (closDec C).pts = tabDec 3510 4096 fun k => fd (C k) 0 4095 := by simp only [closDec]
  have h2 : (closDec C).par = tabDec 3510 4096 fun k => fd (C k) 12 4095 := by simp only [closDec]
  have h3 : (closDec C).lab = tabDec 3510 4096 fun k => fd (C k) 24 7 := by simp only [closDec]
  rw [h1, h2, h3]
  exact ⟨e 0 4095 (by decide), e 12 4095 (by decide), e 24 7 (by decide)⟩

@[expose] def reconIm (T : Tree) (tc : Array Table) (c0 : Nat) : Array Nat :=
  (List.range' 1 (T.pts.size - 1)).foldl
    (fun im k => im.set! k (ap tc[ap T.lab k]! im[ap T.par k]!))
    ((Array.replicate T.pts.size 0).set! 0 c0)

theorem reconTab_eq (T : Tree) (tc : Array Table) (c0 : Nat) :
    reconTab T tc c0 = (List.range' 0 T.pts.size).foldl
      (fun U k => U.set! (ap T.pts k) (UInt32.ofNat (reconIm T tc c0)[k]!))
      (Array.replicate 3510 0) := by
  unfold reconTab reconIm
  simp only [Id.run_bind, Id.run_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [List.forIn_pure_yield_eq_foldl, Id.run_pure, Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero]

theorem closDec_size (C : Nat → Nat) : (closDec C).pts.size = 3510 := by
  simp [closDec, tabDec]

theorem recon_im (hO : OrbOK) (h : LHChecks D) :
    (reconIm (closDec D.C) (uImg.map (tabOf orbL)) uImg[0]!).size = 3510 ∧
      ∀ k < 3510, (reconIm (closDec D.C) (uImg.map (tabOf orbL)) uImg[0]!)[k]! =
        ent D.u (fd (D.C k) 0 4095) := by
  obtain ⟨-, -, -, hu0, hstep, hu, -⟩ := swapK_spec h.swap
  obtain ⟨hpts, -, htr⟩ := clos_facts hO h
  unfold reconIm
  rw [closDec_size]
  let g : Array Nat → Nat → Array Nat := fun im k =>
    im.set! k (ap (uImg.map (tabOf orbL))[ap (closDec D.C).lab k]! im[ap (closDec D.C).par k]!)
  let im0 : Array Nat := (Array.replicate 3510 0).set! 0 uImg[0]!
  have hgen : ∀ j ≤ 3509, ((List.range' 1 j).foldl g im0).size = 3510 ∧
      ∀ k < j + 1, ((List.range' 1 j).foldl g im0)[k]! = ent D.u (fd (D.C k) 0 4095) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [im0, size_set!], fun k hk => ?_⟩
      have : k = 0 := by omega
      subst this
      simp only [im0, List.range'_zero, List.foldl_nil]
      rw [get!_set! _ (by simp) (by simp), if_pos rfl, uImg_get 0 (by decide), hu0]
    | succ j ih =>
      intro hj
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range' 1 j).foldl g im0 = im1 at hs hv
      simp only [g, Nat.one_mul]
      have hk := htr (1 + j) (by omega) (by omega)
      obtain ⟨hp, hl, hc⟩ := hk
      obtain ⟨cp, cpar, clab⟩ := closDec_ap (C := D.C) (k := 1 + j) (by omega)
      refine ⟨by rw [size_set!, hs], fun k hk' => ?_⟩
      rw [get!_set! _ (by rw [hs]; omega) (by rw [hs]; omega)]
      by_cases e : 1 + j = k
      · subst e
        rw [if_pos rfl, cpar, clab, hv _ (by omega), getElem!_map' _ _ (by change _ < 6; exact hl),
          uImg_get _ hl]
        have hb : uiK (fd (D.C (1 + j)) 24 7) < 3510 := by
          rw [← uImg_get _ hl]
          generalize fd (D.C (1 + j)) 24 7 = l at hl
          revert l
          decide
        have hx : ent D.u (fd (D.C (fd (D.C (1 + j)) 12 4095)) 0 4095) < 3510 :=
          (hu _ (hpts _ (by omega))).1
        rw [← tauAll_get hb, ((tauAll_TR hO h _ hb).2 _ hx).1, hstep (1 + j) (by omega) (by omega)]
      · rw [if_neg e, hv k (by omega)]
  have := hgen 3509 (by decide)
  exact ⟨this.1, fun k hk => this.2 k (by omega)⟩

theorem lhUTab_TR (hO : OrbOK) (h : LHChecks D) : TR 3510 (lhUTab orbL) (ent D.u) := by
  obtain ⟨-, -, -, -, -, hu, -⟩ := swapK_spec h.swap
  obtain ⟨hpts, hsurj, -⟩ := clos_facts hO h
  obtain ⟨-, him⟩ := recon_im hO h
  have hP1 : ∀ k < 3510, ∀ k' < 3510, fd (D.C k) 0 4095 = fd (D.C k') 0 4095 → k = k' := by
    intro k hk k' hk' e
    obtain ⟨-, hpos, -⟩ := swapK_spec h.swap
    unfold posK at hpos
    rw [bAnd_eq, Bool.and_eq_true] at hpos
    have e1 : fd (D.C (fd (D.C k) 0 4095)) 27 4095 = k := Nat.eq_of_beq_eq_true (allN_iff.1 hpos.1 k hk)
    have e2 : fd (D.C (fd (D.C k') 0 4095)) 27 4095 = k' :=
      Nat.eq_of_beq_eq_true (allN_iff.1 hpos.1 k' hk')
    rw [← e1, ← e2, e]
  have hDk : ∀ k < 3510, ((closDec D.C).pts[k]!).toNat = fd (D.C k) 0 4095 :=
    fun k hk => (closDec_ap hk).1
  unfold lhUTab
  rw [closTree_eq hO h, reconTab_eq, closDec_size]
  have hl := set_loopV (N := 3510) (v0 := (0 : UInt32)) (m := 3510)
    (D := fun k => ((closDec D.C).pts[k]!).toNat)
    (v := fun k => UInt32.ofNat (reconIm (closDec D.C) (uImg.map (tabOf orbL)) uImg[0]!)[k]!)
    (fun i hi => by rw [hDk i hi]; exact hpts i hi)
    (fun i hi j hj e => by
      rw [hDk i hi, hDk j (by omega)] at e
      have := hP1 j (by omega) i hi e
      omega)
  refine ⟨hl.1, fun x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hsurj x hx
  have := hl.2 k hk
  rw [hDk k hk] at this
  unfold ap
  rw [this, him k hk, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := (hu _ (hpts k hk)).1; omega)]
  exact ⟨rfl, (hu _ (hpts k hk)).1⟩

theorem u_inj (h : LHChecks D) {x y : Nat} (hx : x < 3510) (hy : y < 3510)
    (e : ent D.u x = ent D.u y) : x = y := by
  obtain ⟨-, -, -, -, -, hu, -⟩ := swapK_spec h.swap
  rw [← (hu x hx).2, ← (hu y hy).2, e]

theorem u_img (hO : OrbOK) (h : LHChecks D) {Q : Nat → Nat} {lb m : Nat}
    (hs : ∀ s < 20, setSl Q D.al D.be s = true) (hm : m < 14080)
    (hinc : (∀ i j, i < j → j < 351 → ent lb i < ent lb j) ∧ ∀ j < 351, ent lb j < 3510)
    (hsub : ∀ j < 351, (sb (Q m)).testBit (ent D.u (ent lb j)) = true) {B : Bits}
    (hB : BitsIs B fun y => ∃ j < 351, ent lb j = y) :
    imgBits (lhUTab orbL) B = bitsOfNat (sb (Q m)) ∧
      mapsOnto (lhUTab orbL) B (bitsOfNat (sb (Q m))) = true := by
  have hT := lhUTab_TR hO h
  have himg := set_img_eq hs hm (fun x hx y hy e => u_inj h hx hy e) hinc.1 hinc.2 hsub
  refine ⟨BitsIs.eq_bitsOfNat (bitsIs_imgBits hB fun x hx _ => by
    rw [(hT.2 x hx).1]; have := (hT.2 x hx).2; omega) fun y hy => ?_, ?_⟩
  · rw [himg]
    constructor
    · rintro ⟨x, hx, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, ((hT.2 _ hx).1).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨ent lb j, hinc.2 j hj, ⟨j, hj, rfl⟩, (hT.2 _ (hinc.2 j hj)).1⟩
  · refine mapsOnto_of hB ((bitsIs_bitsOfNat _).congr fun y _ => himg y)
      (fun x hx => by rw [(hT.2 x hx).1]; exact (hT.2 x hx).2) fun x hx => ?_
    rw [(hT.2 x hx).1]
    constructor
    · rintro ⟨j, hj, e⟩
      exact ⟨j, hj, u_inj h (hinc.2 j hj) hx e⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩

theorem uIdx_eq (hO : OrbOK) (h : LHChecks D) :
    #[(orbDec D.QB).find (imgBits (lhUTab orbL) (bitsOf (lhData ())[0]!)),
      (orbDec D.QA).find (imgBits (lhUTab orbL) (bitsOf (lhData ())[1]!))] =
      #[fd D.mt 42 16383, fd D.mt 56 16383] := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10⟩ := swapK_spec h.swap
  rw [(u_img hO h h.setB h7 (lb0_facts h) h9 (B0_bits h)).1,
    (u_img hO h h.setA h8 (lb1_facts h) h10 (B1_bits h)).1,
    find_orbDec_of (fun i hi j hj e => sb_inj h.walkB hi hj e) h7 rfl,
    find_orbDec_of (fun i hi j hj e => sb_inj h.walkA hi hj e) h8 rfl]

theorem c_swap (hO : OrbOK) (h : LHChecks D) :
    swapOK (lhUTab orbL) (bitsOf (lhData ())[0]!) (bitsOf (lhData ())[1]!) (orbDec D.QA)
      (orbDec D.QB) #[fd D.mt 42 16383, fd D.mt 56 16383] = true := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10⟩ := swapK_spec h.swap
  unfold swapOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have e0 : #[fd D.mt 42 16383, fd D.mt 56 16383][0]! = fd D.mt 42 16383 := by
    rw [getElem!_pos _ 0 (by simp)]; rfl
  have e1 : #[fd D.mt 42 16383, fd D.mt 56 16383][1]! = fd D.mt 56 16383 := by
    rw [getElem!_pos _ 1 (by simp)]; rfl
  rw [e0, e1, orbDec_sets _ h7, orbDec_sets _ h8]
  exact ⟨⟨⟨⟨rfl, h7⟩, (u_img hO h h.setB h7 (lb0_facts h) h9 (B0_bits h)).2⟩, h8⟩,
    (u_img hO h h.setA h8 (lb1_facts h) h10 (B1_bits h)).2⟩

@[expose] noncomputable def dep (op : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, g => g == 0 || dep op f (ent op g)

theorem xi_dep : ∀ l < 7, dep (CFSG.KS.Fi22L.orbT 2) 12 (xiK l) = true := by decide +kernel

theorem xiGens_get : ∀ l < 7, xiGens[l]! = xiK l := by decide

theorem xiK_lt : ∀ l < 7, xiK l < 3510 := by decide

theorem phiW_succ (op ol qa qb qbi f g m : Nat) : phiW op ol qa qb qbi (f + 1) g m =
    if g = 0 then e14 qa m else if ent ol g = 1 then e14 qa (phiW op ol qa qb qbi f (ent op g)
      (e14 qa m)) else e14 qb (phiW op ol qa qb qbi f (ent op g) (e14 qbi m)) := by
  change Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
      (e14 qb (phiW op ol qa qb qbi f (ent op g) (e14 qbi m)))
      (e14 qa (phiW op ol qa qb qbi f (ent op g) (e14 qa m)))
      (Nat.beq (ent ol g) 1)) (e14 qa m) (Nat.beq g 0) = _
  simp only [nIf_eq, Nat.beq_eq]

theorem flat_spec (h : LHChecks D) {m : Nat} (hm : m < 14080) :
    e14 D.qa m = fd (D.QA m) 7722 16383 ∧ e14 D.qb m = fd (D.QA m) 7736 16383 ∧
      e14 D.qbi m < 14080 ∧ e14 D.qb (e14 D.qbi m) = m := by
  have := allN_iff.1 h.flat m hm
  rw [strictB_eq] at this
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at this
  exact this

theorem sbA_lt {m y : Nat} (hy : (sb (D.QA m)).testBit y = true) : y < 3510 := by
  rw [testBit_sb] at hy
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hy
  exact hy.1

theorem phiW_spec (hO : OrbOK) (h : LHChecks D) : ∀ f g, g < 3510 → dep D.op f g = true →
    ∀ m < 14080, phiW D.op D.ol D.qa D.qb D.qbi f g m < 14080 ∧ ∀ y,
      (sb (D.QA (phiW D.op D.ol D.qa D.qb D.qbi f g m))).testBit y = true ↔
        ∃ x, (sb (D.QA m)).testBit x = true ∧ ent (D.R g) x = y := by
  intro f
  induction f with
  | zero => intro g _ hd; simp [dep] at hd
  | succ f ih =>
    intro g hg hd m hm
    obtain ⟨fa, fb, fbi, fbb⟩ := flat_spec h hm
    rw [phiW_succ]
    by_cases hg0 : g = 0
    · subst hg0
      rw [if_pos rfl]
      refine ⟨by rw [fa]; exact pa_lt h.setA hm, fun y => ?_⟩
      rw [fa, sb_pa h.setA hm, row_zero h]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, (sb_mem h.setA hm _).2 ⟨j, hj, rfl⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨j, hj, rfl⟩ := (sb_mem h.setA hm x).1 hx
        exact ⟨j, hj, rfl⟩
    · rw [if_neg hg0]
      have hd' : dep D.op f (ent D.op g) = true := by
        simp only [dep, Bool.or_eq_true, beq_iff_eq, hg0, false_or] at hd
        exact hd
      obtain ⟨hp, hrow⟩ := row_succ h hg (by omega)
      by_cases hl : ent D.ol g = 1
      · rw [if_pos hl]
        have hm1 : e14 D.qa m < 14080 := by rw [fa]; exact pa_lt h.setA hm
        obtain ⟨i1, i2⟩ := ih (ent D.op g) (by omega) hd' _ hm1
        obtain ⟨ga, -⟩ := flat_spec h i1
        refine ⟨by rw [ga]; exact pa_lt h.setA i1, fun y => ?_⟩
        rw [ga, sb_pa h.setA i1]
        constructor
        · rintro ⟨j, hj, rfl⟩
          have hx2 := (sb_mem h.setA i1 _).2 ⟨j, hj, rfl⟩
          obtain ⟨x1, hx1, e1⟩ := (i2 _).1 hx2
          rw [fa, sb_pa h.setA hm] at hx1
          obtain ⟨j0, hj0, rfl⟩ := hx1
          refine ⟨ent (D.QA m) j0, (sb_mem h.setA hm _).2 ⟨j0, hj0, rfl⟩, ?_⟩
          rw [hrow _ (mem_lt h.setA hm hj0), if_pos hl, e1]
        · rintro ⟨x, hx, rfl⟩
          have hx' := sbA_lt hx
          have hm1x : (sb (D.QA (e14 D.qa m))).testBit (ent D.al x) = true := by
            rw [fa, sb_pa h.setA hm]
            obtain ⟨j, hj, rfl⟩ := (sb_mem h.setA hm x).1 hx
            exact ⟨j, hj, rfl⟩
          have h2 := (i2 _).2 ⟨_, hm1x, rfl⟩
          obtain ⟨j, hj, e⟩ := (sb_mem h.setA i1 _).1 h2
          refine ⟨j, hj, ?_⟩
          rw [hrow x hx', if_pos hl, e]
      · rw [if_neg hl]
        obtain ⟨ia, ib⟩ := ih (ent D.op g) (by omega) hd' _ fbi
        obtain ⟨-, gb, -⟩ := flat_spec h ia
        obtain ⟨-, fb1, -⟩ := flat_spec h fbi
        have hbi : ∀ x, (sb (D.QA (e14 D.qbi m))).testBit x = true ↔
            ∃ z, (sb (D.QA m)).testBit z = true ∧ ent D.bi z = x := by
          intro x
          have hS : ∀ y, (sb (D.QA m)).testBit y = true ↔
              ∃ j < 351, ent D.be (ent (D.QA (e14 D.qbi m)) j) = y := by
            intro y
            rw [← sb_pb h.setA fbi, ← fb1, fbb]
          constructor
          · intro hx
            obtain ⟨j, hj, rfl⟩ := (sb_mem h.setA fbi x).1 hx
            refine ⟨ent D.be (ent (D.QA (e14 D.qbi m)) j), (hS _).2 ⟨j, hj, rfl⟩, ?_⟩
            exact bi_be hO h (mem_lt h.setA fbi hj)
          · rintro ⟨z, hz, rfl⟩
            obtain ⟨j, hj, rfl⟩ := (hS z).1 hz
            rw [bi_be hO h (mem_lt h.setA fbi hj)]
            exact (sb_mem h.setA fbi _).2 ⟨j, hj, rfl⟩
        refine ⟨by rw [gb]; exact pb_lt h.setA ia, fun y => ?_⟩
        rw [gb, sb_pb h.setA ia]
        constructor
        · rintro ⟨j, hj, rfl⟩
          have hx2 := (sb_mem h.setA ia _).2 ⟨j, hj, rfl⟩
          obtain ⟨x1, hx1, e1⟩ := (ib _).1 hx2
          obtain ⟨z, hz, rfl⟩ := (hbi x1).1 hx1
          refine ⟨z, hz, ?_⟩
          rw [hrow z (sbA_lt hz), if_neg hl, e1]
        · rintro ⟨x, hx, rfl⟩
          have h2 := (ib _).2 ⟨ent D.bi x, (hbi _).2 ⟨x, hx, rfl⟩, rfl⟩
          obtain ⟨j, hj, e⟩ := (sb_mem h.setA ia _).1 h2
          refine ⟨j, hj, ?_⟩
          rw [hrow x (sbA_lt hx), if_neg hl, e]

theorem phi_facts (hO : OrbOK) (h : LHChecks D) {l m : Nat} (hl : l < 7) (hm : m < 14080) :
    e14 (D.ph l) m < 14080 ∧ imgBits (tauAll orbL)[xiK l]! (bitsOfNat (sb (D.QA m))) =
      bitsOfNat (sb (D.QA (e14 (D.ph l) m))) := by
  have hk := h.phi l hl
  unfold phiK at hk
  rw [strictB_eq, strictB_eq] at hk
  have he := Nat.eq_of_beq_eq_true (allN_iff.1 hk m hm)
  have hxl : xiK l < 3510 := xiK_lt l hl
  have hd : dep D.op 12 (xiK l) = true := by rw [h.op]; exact xi_dep l hl
  obtain ⟨h1, h2⟩ := phiW_spec hO h 12 (xiK l) hxl hd m hm
  rw [he]
  refine ⟨h1, ?_⟩
  have hT := tauAll_TR hO h _ hxl
  refine BitsIs.eq_bitsOfNat (bitsIs_imgBits (bitsIs_bitsOfNat _) fun x hx _ => by
    rw [(hT.2 x hx).1]; have := (hT.2 x hx).2; omega) fun y hy => ?_
  rw [h2]
  constructor
  · rintro ⟨x, hx, hm', rfl⟩
    exact ⟨x, hm', ((hT.2 x hx).1).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, sbA_lt hx, hx, (hT.2 x (sbA_lt hx)).1⟩

theorem phiDec_get {ph : Nat → Nat} {l m : Nat} (hl : l < 7) (hm : m < 14080) :
    (phiDec ph)[l]!.size = 14080 ∧ ((phiDec ph)[l]!)[m]! = UInt32.ofNat (e14 (ph l) m) ∧
      ap (phiDec ph)[l]! m = e14 (ph l) m := by
  have e1 : (phiDec ph)[l]! = tabDec 14080 16384 fun m => e14 (ph l) m := by
    unfold phiDec
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  have e2 : ((phiDec ph)[l]!)[m]! = UInt32.ofNat (e14 (ph l) m) := by
    rw [e1]
    unfold tabDec
    rw [getElem!_pos _ m (by simpa using hm), Array.getElem_ofFn]
    change (if e14 (ph l) m = 16384 then none32 else UInt32.ofNat (e14 (ph l) m)) = _
    have := e14_lt (ph l) m
    rw [if_neg (by omega)]
  refine ⟨by rw [e1]; simp [tabDec], e2, ?_⟩
  unfold ap
  rw [e2, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := e14_lt (ph l) m; omega)]

theorem phi_eq (hO : OrbOK) (h : LHChecks D) : mkPhi (tauAll orbL) (orbDec D.QA) = phiDec D.ph := by
  refine ext_get! (N := 7) (by simp [mkPhi, xiGens]) (by simp [phiDec]) fun l hl => ?_
  refine ext_get! (N := 14080) ?_ (phiDec_get hl (by decide : 0 < 14080)).1 fun m hm => ?_
  · unfold mkPhi
    rw [getElem!_map' _ _ (by change l < 7; exact hl)]
    simp
  · rw [(phiDec_get hl hm).2.1]
    unfold mkPhi
    rw [getElem!_map' _ _ (by change l < 7; exact hl), xiGens_get l hl,
      getElem!_pos _ m (by simpa using hm), Array.getElem_ofFn]
    change UInt32.ofNat ((orbDec D.QA).find (imgBits (tauAll orbL)[xiK l]! (orbDec D.QA).sets[m]!)) = _
    rw [orbDec_sets _ hm, (phi_facts hO h hl hm).2,
      find_orbDec_of (fun i hi j hj e => sb_inj h.walkA hi hj e) (phi_facts hO h hl hm).1 rfl]

theorem c_phi (hO : OrbOK) (h : LHChecks D) :
    phiOK (tauAll orbL) (bitsOf (lhData ())[0]!) (orbDec D.QA) (phiDec D.ph) = true := by
  unfold phiOK
  rw [Bool.and_eq_true]
  refine ⟨by simp [phiDec, xiGens], ?_⟩
  rw [show xiGens.size = 7 from rfl, allIn_iff]
  intro l hl
  have hxl : xiK l < 3510 := xiK_lt l hl
  rw [xiGens_get l hl]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  obtain ⟨-, -, -, hxi, -⟩ := farK_spec h
  refine ⟨⟨⟨hxl, by rw [B0_at h hxl]; exact hxi l hl⟩, (phiDec_get hl (by decide : 0 < 14080)).1⟩, ?_⟩
  refine CFSG.Sporadic.Th.parAll_eq_true_of fun m hm => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq, (phiDec_get hl hm).2.2]
  obtain ⟨p1, p2⟩ := phi_facts hO h hl hm
  refine ⟨p1, ?_⟩
  rw [orbDec_sets _ hm, orbDec_sets _ p1]
  have hT := tauAll_TR hO h _ hxl
  refine mapsOnto_of (bitsIs_bitsOfNat _) (bitsIs_bitsOfNat _)
    (fun x hx => by rw [(hT.2 x hx).1]; exact (hT.2 x hx).2) fun x hx => ?_
  have hb := (bitsIs_imgBits (T := (tauAll orbL)[xiK l]!) (bitsIs_bitsOfNat (sb (D.QA m)))
    fun x hx _ => by rw [(hT.2 x hx).1]; have := (hT.2 x hx).2; omega)
  rw [p2] at hb
  have hy : ap (tauAll orbL)[xiK l]! x < 3510 := by rw [(hT.2 x hx).1]; exact (hT.2 x hx).2
  have := (hb.2 (ap (tauAll orbL)[xiK l]! x) (by omega)).symm.trans
    ((bitsIs_bitsOfNat _).2 (ap (tauAll orbL)[xiK l]! x) (by omega))
  refine this.symm.trans ?_
  constructor
  · rintro ⟨x', hx', hm', e⟩
    rw [(hT.2 x' hx').1, (hT.2 x hx).1] at e
    rw [← row_inj hO h hxl hx' hx e]
    exact hm'
  · intro hmx
    exact ⟨x, hx, hmx, rfl⟩

end CFSG.KS.Fi22LH
