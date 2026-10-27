module

public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Certificates.Kernel.SporSch.PtCntSound
public import CFSG.Certificates.Kernel.SporSch.J1CentSound
public import CFSG.Certificates.Kernel.SporSch.ChainKPack
public import CFSG.Certificates.Kernel.SporSch.ClassOneSound

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

theorem exists_prep {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    ∃ g : Equiv.Perm (Fin n), Orb.PRep n w P g :=
  ⟨_, Orb.prep_of_rep (rep_permOfArr (Orb.isInvA_unpack h)).1⟩

theorem rep_listTbl_of_bind {n w P : Nat} (hn : n < 2 ^ 32) {l : List Nat}
    (hb : bindListK n w P l = true) {g : Equiv.Perm (Fin n)} (hg : Orb.PRep n w P g) :
    CFSG.Sporadic.Th.Rep n (listTbl n l) g := by
  intro x hx
  have ha := toArray_eq_of_bindListK hb
  have hx' : x < l.length := by
    have := congrArg Array.size ha
    simp only [List.size_toArray, unpack, Array.size_ofFn] at this
    omega
  have e : l.getD x 0 = (g ⟨x, hx⟩ : Nat) := by
    have e1 : l[x] = (unpack n w P)[x]! := by
      rw [← ha, getElem!_pos l.toArray x (by simpa using hx'), List.getElem_toArray]
    rw [List.getD_eq_getElem _ _ hx', e1, Orb.unpack_get hx]
    exact hg ⟨x, hx⟩
  rw [CFSG.Sporadic.Th.idx_of_lt _ hx, listTbl, CFSG.Sporadic.Th.ap_ofFn _ hx,
    UInt32.toNat_ofNat', e, Nat.mod_eq_of_lt ((g ⟨x, hx⟩).isLt.trans hn)]
  rfl

theorem invOK_listTbl {n w P : Nat} {l : List Nat} (hsz : szOK n w = true)
    (hb : bindListK n w P l = true)
    (h : permOK n w (mask w) (n * w) P (pinvS n w (mask w) P) = true) :
    invOK n (listTbl n l) (invT n (listTbl n l)) = true := by
  obtain ⟨g, hg⟩ := exists_prep h
  exact Tbl.invOK_invT (szOK_lt hsz) (rep_listTbl_of_bind (szOK_lt hsz) hb hg)

theorem ordTest_listTbl {n w P e : Nat} {l : List Nat} (hsz : szOK n w = true)
    (hb : bindListK n w P l = true)
    (hp : permOK n w (mask w) (n * w) P (pinvS n w (mask w) P) = true)
    (hP : canonK n w (mask w) (n * w) P = true) (he : 0 < e)
    (h : ordIs n w (mask w) (pidn n w) P (e - 1) = true) :
    ordTest n e (listTbl n l) = true := by
  obtain ⟨g, hg⟩ := exists_prep hp
  exact (ordTest_iff perm_faithful (rep_listTbl_of_bind (szOK_lt hsz) hb hg) he).2
    (ordIs_orderOf hsz hg (PF.canon_facts hP).2.2.1 he h)

theorem pairTest_listTbl {n w A B r s mx my : Nat} {lA lB : List Nat} (hsz : szOK n w = true)
    (hA : bindListK n w A lA = true) (hB : bindListK n w B lB = true)
    (hpA : permOK n w (mask w) (n * w) A (pinvS n w (mask w) A) = true)
    (hpB : permOK n w (mask w) (n * w) B (pinvS n w (mask w) B) = true) (hr : 0 < r) (hs : 0 < s)
    (h1 : ordIs n w (mask w) (pidn n w) (pcomp n w (mask w) A B) (r - 1) = true)
    (h2 : ordIs n w (mask w) (pidn n w) (pcomp n w (mask w) A (pcomp n w (mask w) B
      (pcomp n w (mask w) (powK n w (mask w) (pidn n w) A (mx - 1))
        (powK n w (mask w) (pidn n w) B (my - 1))))) (s - 1) = true) :
    pairTest n r s mx my (listTbl n lA) (listTbl n lB) = true := by
  have hn := szOK_lt hsz
  have hw := PF.w_pos (Orb.szOK_facts hsz).2
  obtain ⟨gA, pA⟩ := exists_prep hpA
  obtain ⟨gB, pB⟩ := exists_prep hpB
  have rA := rep_listTbl_of_bind hn hA pA
  have rB := rep_listTbl_of_bind hn hB pB
  have o1 := ordIs_orderOf hsz (Orb.prep_pcomp hn pA pB) (PF.pcomp_shr _ _ hn hw) hr h1
  have o2 := ordIs_orderOf hsz (Orb.prep_pcomp hn pA (Orb.prep_pcomp hn pB
    (Orb.prep_pcomp hn (prep_powK hsz pA _).1 (prep_powK hsz pB _).1))) (PF.pcomp_shr _ _ hn hw)
    hs h2
  have hc : List.Forall₂ (CFSG.Sporadic.Th.Rep n) (commWord (listTbl n lA) (listTbl n lB) mx my)
      (gA :: gB :: (List.replicate (mx - 1) gA ++ List.replicate (my - 1) gB)) :=
    .cons rA (.cons rB (forall₂_append (forall₂_replicate rA _) (forall₂_replicate rB _)))
  unfold pairTest
  rw [Bool.and_eq_true, ordW_iff perm_faithful (.cons rA (.cons rB .nil)) hr,
    ordW_iff perm_faithful hc hs]
  refine ⟨by simpa using o1, ?_⟩
  simpa [List.prod_append, List.prod_replicate] using o2

open CFSG.KS.SporSch.PtCnt Finset

noncomputable abbrev pairF (w m BP mx r s : Nat) (my : Nat) (R T : List Nat) : Bool :=
  bAnd(ordF w m BP 3 (fun x => apL w m R (apL w m T x)) r,
    ordF w m BP 3 (fun x => apL w m R (apL w m T (itF (apL w m R) (Nat.sub mx 1)
      (itF (apL w m T) (Nat.sub my 1) x)))) s)

theorem dJ_split {w m BP mx my r s : Nat} (R T : List Nat) : dJ w m BP mx my r s R T =
    (if ordF w m BP 3 (apL w m T) mx = true then 1 else 0) +
    1048576 * (if ordF w m BP 3 (apL w m T) mx = true then 0 else
      if ordF w m BP 3 (apL w m T) my = true then 1 else 0) +
    1099511627776 * (if ordF w m BP 3 (apL w m T) mx = true then 0 else
      if ordF w m BP 3 (apL w m T) my = true then
        (if pairF w m BP mx r s my R T = true then 1 else 0) else 0) := by
  unfold dJ stepJ pairF
  generalize ordF w m BP 3 (apL w m T) mx = a
  generalize ordF w m BP 3 (apL w m T) my = b
  generalize bAnd(ordF w m BP 3 (fun x => apL w m R (apL w m T x)) r,
    ordF w m BP 3 (fun x => apL w m R (apL w m T (itF (apL w m R) (Nat.sub mx 1)
      (itF (apL w m T) (Nat.sub my 1) x)))) s) = c
  cases a <;> cases b <;> cases c <;> rfl

noncomputable abbrev blk (r0 r1 r2 L : Nat) (f : Nat → Nat → Nat → Nat) (b : Nat) : Nat :=
  ∑ l ∈ range L, if b * L + l < r0 then ∑ k1 ∈ range r1, ∑ k2 ∈ range r2, f (b * L + l) k1 k2
    else 0

theorem blk_lin (r0 r1 r2 L : Nat) (f g h : Nat → Nat → Nat → Nat) (b : Nat) :
    blk r0 r1 r2 L (fun k0 k1 k2 => f k0 k1 k2 + 1048576 * g k0 k1 k2 +
      1099511627776 * h k0 k1 k2) b =
      blk r0 r1 r2 L f b + 1048576 * blk r0 r1 r2 L g b + 1099511627776 * blk r0 r1 r2 L h b := by
  unfold blk
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [mul_sum, ← sum_add_distrib]
  · rfl

theorem blk_le (r0 r1 r2 L : Nat) (f : Nat → Nat → Nat → Nat) (hf : ∀ a b c, f a b c ≤ 1)
    (b : Nat) : blk r0 r1 r2 L f b ≤ L * (r1 * r2) := by
  unfold blk
  calc (∑ l ∈ range L, if b * L + l < r0 then ∑ k1 ∈ range r1, ∑ k2 ∈ range r2,
        f (b * L + l) k1 k2 else 0)
      ≤ ∑ _l ∈ range L, r1 * r2 := by
        refine sum_le_sum fun l _ => ?_
        split_ifs
        · calc ∑ k1 ∈ range r1, ∑ k2 ∈ range r2, f (b * L + l) k1 k2
                ≤ ∑ _k1 ∈ range r1, ∑ _k2 ∈ range r2, 1 :=
                  sum_le_sum fun k1 _ => sum_le_sum fun k2 _ => hf _ _ _
            _ = r1 * r2 := by simp
        · exact Nat.zero_le _
    _ = L * (r1 * r2) := by simp

theorem blk_sum (r0 r1 r2 L : Nat) (f : Nat → Nat → Nat → Nat) (CS : List Nat)
    (hCS : r0 ≤ CS.length * L) :
    ∑ b ∈ range CS.length, blk r0 r1 r2 L f b =
      ∑ k0 ∈ range r0, ∑ k1 ∈ range r1, ∑ k2 ∈ range r2, f k0 k1 k2 := by
  unfold blk
  rw [sum_blocks (fun k => if k < r0 then ∑ k1 ∈ range r1, ∑ k2 ∈ range r2, f k k1 k2 else 0)
    L, sum_range_ind hCS]

theorem field_sum {n w BP mx my r s : Nat} {LR TR : Nat → Nat} {R : List Nat} {CS : List Nat}
    {L : Nat} (hCS : rcnt (LR 0) ≤ CS.length * L)
    (hc : ∀ b < CS.length,
      cntJB n w (mask w) (n * w) BP 3 mx my r s LR TR R (b * L) L = CS.getD b 0)
    (hblk : L * (rcnt (LR 1) * rcnt (LR 2)) < 1048576) :
    let A : Nat → Nat → Nat → Bool := fun k0 k1 k2 =>
      ordF w (mask w) BP 3 (apL w (mask w) (T3 n (n * w) LR TR k0 k1 k2)) mx
    let B : Nat → Nat → Nat → Bool := fun k0 k1 k2 =>
      ordF w (mask w) BP 3 (apL w (mask w) (T3 n (n * w) LR TR k0 k1 k2)) my
    let P : Nat → Nat → Nat → Bool := fun k0 k1 k2 =>
      pairF w (mask w) BP mx r s my R (T3 n (n * w) LR TR k0 k1 k2)
    (CS.map fun v => (v / 1048576) % 1048576).sum =
        ∑ k0 ∈ range (rcnt (LR 0)), ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)),
          (if A k0 k1 k2 = true then 0 else if B k0 k1 k2 = true then 1 else 0) ∧
      (CS.map fun v => (v / 1099511627776) % 1048576).sum =
        ∑ k0 ∈ range (rcnt (LR 0)), ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)),
          (if A k0 k1 k2 = true then 0 else if B k0 k1 k2 = true then
            (if P k0 k1 k2 = true then 1 else 0) else 0) := by
  intro A B P
  let fA : Nat → Nat → Nat → Nat := fun k0 k1 k2 => if A k0 k1 k2 = true then 1 else 0
  let fB : Nat → Nat → Nat → Nat := fun k0 k1 k2 =>
    if A k0 k1 k2 = true then 0 else if B k0 k1 k2 = true then 1 else 0
  let fC : Nat → Nat → Nat → Nat := fun k0 k1 k2 =>
    if A k0 k1 k2 = true then 0 else if B k0 k1 k2 = true then
      (if P k0 k1 k2 = true then 1 else 0) else 0
  have hv : ∀ b < CS.length, CS.getD b 0 =
      blk (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) L fA b +
        1048576 * blk (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) L fB b +
        1099511627776 * blk (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) L fC b := by
    intro b hb
    rw [← hc b hb, cntJB_eq, ← blk_lin]
    unfold blk
    refine sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [cntJ_eq]
      refine sum_congr rfl fun k1 _ => sum_congr rfl fun k2 _ => ?_
      rw [dJ_split]
    · rfl
  have b1 : ∀ f : Nat → Nat → Nat → Nat, (∀ a b c, f a b c ≤ 1) → ∀ b,
      blk (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) L f b < 1048576 := fun f hf b =>
    lt_of_le_of_lt (blk_le _ _ _ _ f hf b) hblk
  have hA1 : ∀ a b c, fA a b c ≤ 1 := fun a b c => by simp only [fA]; split <;> omega
  have hB1 : ∀ a b c, fB a b c ≤ 1 := fun a b c => by simp only [fB]; split_ifs <;> omega
  have hC1 : ∀ a b c, fC a b c ≤ 1 := fun a b c => by simp only [fC]; split_ifs <;> omega
  refine ⟨?_, ?_⟩
  · rw [sum_map_getD, sum_congr rfl fun b hb => (show CS.getD b 0 / 1048576 % 1048576 =
      blk (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) L fB b by
        have := hv b (mem_range.1 hb)
        have := b1 fA hA1 b
        have := b1 fB hB1 b
        have := b1 fC hC1 b
        omega), blk_sum _ _ _ _ _ _ hCS]
  · rw [sum_map_getD, sum_congr rfl fun b hb => (show CS.getD b 0 / 1099511627776 % 1048576 =
      blk (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) L fC b by
        have := hv b (mem_range.1 hb)
        have := b1 fA hA1 b
        have := b1 fB hB1 b
        have := b1 fC hC1 b
        omega), blk_sum _ _ _ _ _ _ hCS]

theorem clsPtK_facts {n w m nw BP nb N A Ai B Bi : Nat} {LR TR E IA IB PA LB DP : Nat → Nat}
    {c r0 k : Nat}
    (h : clsPtK n w m nw BP nb N A Ai B Bi LR TR E IA IB PA LB DP c r0 k = true) (hk : k < c) :
    E k < N ∧ (k + 1 < c → E k < E (k + 1)) ∧ IA k < c ∧ IB k < c ∧
      eqB w m BP nb (conjF w m A Ai (apL w m (elemT n nw LR TR nb (E k))))
        (apL w m (elemT n nw LR TR nb (E (IA k)))) = true ∧
      eqB w m BP nb (conjF w m B Bi (apL w m (elemT n nw LR TR nb (E k))))
        (apL w m (elemT n nw LR TR nb (E (IB k)))) = true ∧
      (k ≠ r0 → PA k < c ∧ DP (PA k) < DP k ∧
        ((LB k = 0 ∧ eqB w m BP nb (apL w m (elemT n nw LR TR nb (E k)))
            (conjF w m A Ai (apL w m (elemT n nw LR TR nb (E (PA k))))) = true) ∨
         (LB k ≠ 0 ∧ eqB w m BP nb (apL w m (elemT n nw LR TR nb (E k)))
            (conjF w m B Bi (apL w m (elemT n nw LR TR nb (E (PA k))))) = true))) := by
  unfold clsPtK at h
  rw [show Nat.blt k c = true by rw [Nat.blt_eq]; exact hk, CIdx.strictB_eq] at h
  obtain ⟨h1, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h2, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h3, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h4, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h5, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h6, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  refine ⟨J1C.blt_iff.1 h1, fun hk1 => ?_, J1C.blt_iff.1 h3, J1C.blt_iff.1 h4, h5, h6,
    fun hr => ?_⟩
  · rw [show Nat.blt (Nat.succ k) c = true from J1C.blt_iff.2 hk1] at h2
    exact J1C.blt_iff.1 h2
  · rw [show Nat.beq k r0 = false from Bool.eq_false_iff.2 fun e => hr (Nat.eq_of_beq_eq_true e)]
      at h
    obtain ⟨h7, h⟩ := (CIdx.bAnd_iff' _ _).1 h
    obtain ⟨h8, h⟩ := (CIdx.bAnd_iff' _ _).1 h
    refine ⟨J1C.blt_iff.1 h7, J1C.blt_iff.1 h8, ?_⟩
    by_cases hl : LB k = 0
    · rw [show Nat.beq (LB k) 0 = true by rw [Nat.beq_eq]; exact hl] at h
      exact Or.inl ⟨hl, h⟩
    · rw [show Nat.beq (LB k) 0 = false from
        Bool.eq_false_iff.2 fun e => hl (Nat.eq_of_beq_eq_true e)] at h
      exact Or.inr ⟨hl, h⟩

theorem pairTest_rep {n r s mx my : Nat} {x y : Table} {xg yg : Equiv.Perm (Fin n)}
    (hx : CFSG.Sporadic.Th.Rep n x xg) (hy : CFSG.Sporadic.Th.Rep n y yg) (hr : 0 < r)
    (hs : 0 < s) : pairTest n r s mx my x y = true ↔
      orderOf (xg * yg) = r ∧ orderOf (xg * (yg * (xg ^ (mx - 1) * yg ^ (my - 1)))) = s := by
  have hc : List.Forall₂ (CFSG.Sporadic.Th.Rep n) (commWord x y mx my)
      (xg :: yg :: (List.replicate (mx - 1) xg ++ List.replicate (my - 1) yg)) :=
    .cons hx (.cons hy (forall₂_append (forall₂_replicate hx _) (forall₂_replicate hy _)))
  unfold pairTest
  rw [Bool.and_eq_true, ordW_iff perm_faithful (.cons hx (.cons hy .nil)) hr,
    ordW_iff perm_faithful hc hs]
  simp [List.prod_append, List.prod_replicate]

theorem orderOf_conj' {M : Type*} [Group M] (h x : M) : orderOf (h * x * h⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply]
  exact MulEquiv.orderOf_eq _ _

abbrev Pp {M : Type*} [Group M] (mx my r s : Nat) (x g : M) : Prop :=
  orderOf g = my ∧ orderOf (x * g) = r ∧ orderOf (x * (g * (x ^ (mx - 1) * g ^ (my - 1)))) = s

theorem pp_conj {M : Type*} [Group M] (mx my r s : Nat) (h x g : M) :
    Pp mx my r s (h * x * h⁻¹) (h * g * h⁻¹) ↔ Pp mx my r s x g := by
  have e1 : h * x * h⁻¹ * (h * g * h⁻¹) = h * (x * g) * h⁻¹ := by group
  have e2 : h * x * h⁻¹ * (h * g * h⁻¹ * ((h * x * h⁻¹) ^ (mx - 1) * (h * g * h⁻¹) ^ (my - 1))) =
      h * (x * (g * (x ^ (mx - 1) * g ^ (my - 1)))) * h⁻¹ := by
    rw [conj_pow, conj_pow]
    simp only [mul_assoc, inv_mul_cancel_left]
  unfold Pp
  rw [e1, e2, orderOf_conj', orderOf_conj', orderOf_conj']

theorem card_conj {M : Type*} [Group M] (G : Subgroup M) {h : M} (hh : h ∈ G) (mx my r s : Nat)
    (x : M) : Nat.card {g // g ∈ G ∧ Pp mx my r s (h * x * h⁻¹) g} =
      Nat.card {g // g ∈ G ∧ Pp mx my r s x g} := by
  refine Nat.card_congr ⟨fun g => ⟨h⁻¹ * g.1 * h, ?_, ?_⟩, fun g => ⟨h * g.1 * h⁻¹, ?_, ?_⟩,
    fun g => ?_, fun g => ?_⟩
  · exact G.mul_mem (G.mul_mem (G.inv_mem hh) g.2.1) hh
  · have := g.2.2
    rwa [show g.1 = h * (h⁻¹ * g.1 * h) * h⁻¹ by group, pp_conj] at this
  · exact G.mul_mem (G.mul_mem hh g.2.1) (G.inv_mem hh)
  · exact (pp_conj mx my r s h x g.1).2 g.2.2
  · apply Subtype.ext
    simp only
    group
  · apply Subtype.ext
    simp only
    group

theorem arr2_get0 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[0]! = a := by
  rw [getElem!_pos _ 0 (by simp)]
  rfl

theorem arr2_get1 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[1]! = b := by
  rw [getElem!_pos _ 1 (by simp)]
  rfl

theorem forall₂_head {α β : Type*} [Inhabited α] {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → (h : 0 < m.length) →
      R l.toArray[0]! (m[0]'h)
  | [], [], .nil, h => absurd h (by simp)
  | _ :: _, _ :: _, .cons hab _, _ => by simpa using hab

theorem countP_filt {M : Type*} [Monoid M] (L : List M) (P Q : M → Bool) :
    (((L.map (1 * ·)).filter P).reverse ++ []).countP Q = L.countP fun g => P g && Q g := by
  simp [List.countP_filter, Bool.and_comm]

section Chain

open CFSG.KS.SporSch.CIdx CFSG.KS.SporSch.J1C CFSG.KS.ClassOne CFSG.KS.Raw.Orb

variable {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hQ : ChainCK n w PS PSI LR TR TRI kS 2 3 BP S base D)
include hQ

theorem two_le : 2 ≤ kS := by
  have h := hQ.2.1
  unfold headK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact Nat.le_of_ble_eq_true h.2.2.1

theorem prep_gen {j : Nat} (hj : j < 2) :
    Orb.PRep n w (PS j) (permOfArr n S[j]!) ∧ Orb.PRep n w (PSI j) (permOfArr n S[j]!)⁻¹ :=
  Orb.prep_PS hQ.1 (perms hQ) (by have := two_le hQ; omega)

omit hQ in
theorem gen_mem {j : Nat} (hj : j < 2) : permOfArr n S[j]! ∈ Gen n S 2 :=
  Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem acts_conjF {j : Nat} (hj : j < 2) (i : Nat) :
    Acts n (conjF w (mask w) (PS j) (PSI j) (apL w (mask w) (elemT n (n * w) LR TR 3 i)))
      (permOfArr n S[j]! * el n S base 3 i * (permOfArr n S[j]!)⁻¹) := by
  intro y
  unfold conjF
  obtain ⟨h1, h2⟩ := prep_gen hQ hj
  rw [h2 y, apL_elemT hQ, h1]
  rfl

theorem cls_sound {mx cap jR : Nat} {E IA IB PA LB DP : Nat → Nat} {c r0 : Nat}
    (hhd : clsPtHdK n w (mask w) (n * w) BP 3 LR TR E c r0 jR mx cap = true)
    (hcl : ∀ k < c, clsPtK n w (mask w) (n * w) BP 3 (ordK LR 3) (PS 0) (PSI 0) (PS 1) (PSI 1)
      LR TR E IA IB PA LB DP c r0 k = true) :
    0 < c ∧ c ≤ cap ∧ jR < ordK LR 3 ∧ orderOf (el n S base 3 jR) = mx ∧
      {x | ∃ k < c, el n S base 3 (E k) = x}.ncard = c ∧
      ∀ x, (∃ k < c, el n S base 3 (E k) = x) ↔
        ∃ g ∈ Gen n S 2, g * el n S base 3 jR * g⁻¹ = x := by
  unfold clsPtHdK at hhd
  obtain ⟨h1, hhd⟩ := (CIdx.bAnd_iff' _ _).1 hhd
  obtain ⟨h2, hhd⟩ := (CIdx.bAnd_iff' _ _).1 hhd
  obtain ⟨h3, hhd⟩ := (CIdx.bAnd_iff' _ _).1 hhd
  obtain ⟨h4, h5⟩ := (CIdx.bAnd_iff' _ _).1 hhd
  have hc0 : 0 < c := J1C.blt_iff.1 h1
  have hcc : c ≤ cap := Nat.le_of_ble_eq_true h2
  have hr0 : r0 < c := J1C.blt_iff.1 h3
  have hE0 : E r0 = jR := Nat.eq_of_beq_eq_true h4
  have F := fun k (hk : k < c) => clsPtK_facts (hcl k hk) hk
  have hlt : ∀ k < c, E k < ordK LR 3 := fun k hk => (F k hk).1
  have hjR : jR < ordK LR 3 := hE0 ▸ hlt r0 hr0
  have hx0 : el n S base 3 jR ∈ Gen n S 2 := el_mem hQ hjR
  have ho : orderOf (el n S base 3 jR) = mx := (ordF_iff hQ (apL_elemT hQ jR) hx0).1 h5
  have hmono : ∀ a b, a < b → b < c → E a < E b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact (ih h (by omega)).trans ((F b (by omega)).2.1 hb)
      · exact (F a (by omega)).2.1 hb
  have hEinj : ∀ a < c, ∀ b < c, E a = E b → a = b := fun a ha b hb e => by
    rcases lt_trichotomy a b with h | h | h
    · exact absurd e (hmono a b h hb).ne
    · exact h
    · exact absurd e.symm (hmono b a h ha).ne
  have hmem : ∀ k < c, el n S base 3 (E k) ∈ Gen n S 2 := fun k hk => el_mem hQ (hlt k hk)
  have cm : ∀ {j : Nat}, j < 2 → ∀ {g : Equiv.Perm (Fin n)}, g ∈ Gen n S 2 →
      permOfArr n S[j]! * g * (permOfArr n S[j]!)⁻¹ ∈ Gen n S 2 := fun hj _ hg =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (gen_mem hj) hg) (Subgroup.inv_mem _ (gen_mem hj))
  have hconjX : ∀ j < 2, ∀ k < c, ∃ k' < c, el n S base 3 (E k') =
      permOfArr n S[j]! * el n S base 3 (E k) * (permOfArr n S[j]!)⁻¹ := by
    intro j hj k hk
    obtain ⟨-, -, hA, hB, eA, eB, -⟩ := F k hk
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ⟨IA k, hA, ((eqB_iff_eq hQ (acts_conjF hQ (by norm_num) _) (apL_elemT hQ _)
        (cm (by norm_num) (hmem k hk)) (hmem _ hA)).1 eA).symm⟩
    · exact ⟨IB k, hB, ((eqB_iff_eq hQ (acts_conjF hQ (by norm_num) _) (apL_elemT hQ _)
        (cm (by norm_num) (hmem k hk)) (hmem _ hB)).1 eB).symm⟩
  have hpar : ∀ d, ∀ k < c, DP k = d →
      ∃ g ∈ Gen n S 2, g * el n S base 3 jR * g⁻¹ = el n S base 3 (E k) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hk hd
      by_cases hr : k = r0
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [hr, hE0]
        group
      · obtain ⟨-, -, -, -, -, -, hp⟩ := F k hk
        obtain ⟨hpc, hdp, hrel⟩ := hp hr
        obtain ⟨g, hg, e⟩ := ih _ (hd ▸ hdp) (PA k) hpc rfl
        have key : ∃ j < 2, el n S base 3 (E k) =
            permOfArr n S[j]! * el n S base 3 (E (PA k)) * (permOfArr n S[j]!)⁻¹ := by
          rcases hrel with ⟨-, h⟩ | ⟨-, h⟩
          · exact ⟨0, by norm_num, (eqB_iff_eq hQ (apL_elemT hQ _) (acts_conjF hQ (by norm_num) _)
              (hmem k hk) (cm (by norm_num) (hmem _ hpc))).1 h⟩
          · exact ⟨1, by norm_num, (eqB_iff_eq hQ (apL_elemT hQ _) (acts_conjF hQ (by norm_num) _)
              (hmem k hk) (cm (by norm_num) (hmem _ hpc))).1 h⟩
        obtain ⟨j, hj, e'⟩ := key
        refine ⟨permOfArr n S[j]! * g, Subgroup.mul_mem _ (gen_mem hj) hg, ?_⟩
        rw [e', ← e]
        group
  have hfin : {x | ∃ k < c, el n S base 3 (E k) = x}.Finite :=
    ((Set.finite_lt_nat c).image fun k => el n S base 3 (E k)).subset fun x ⟨k, hk, e⟩ =>
      ⟨k, hk, e⟩
  refine ⟨hc0, hcc, hjR, ho, ?_, fun x => ⟨?_, ?_⟩⟩
  · have e : {x | ∃ k < c, el n S base 3 (E k) = x} =
        (fun k => el n S base 3 (E k)) '' {k | k < c} := by
      ext x
      simp
    have hi : Set.InjOn (fun k => el n S base 3 (E k)) {k | k < c} := fun a ha b hb e =>
      hEinj a ha b hb (el_inj hQ (hlt a ha) (hlt b hb) e)
    rw [e, hi.ncard_image, show {k | k < c} = ((Finset.range c : Finset Nat) : Set Nat) by
      ext; simp, Set.ncard_coe_finset, Finset.card_range]
  · rintro ⟨k, hk, rfl⟩
    exact hpar _ k hk rfl
  · rintro ⟨g, hg, rfl⟩
    exact conj_closed (kO := 2) hfin (fun j hj y ⟨k, hk, e⟩ => by
      obtain ⟨k', hk', e'⟩ := hconjX j hj k hk
      exact ⟨k', hk', by rw [e', e]⟩) g hg _ ⟨r0, hr0, by rw [hE0]⟩

theorem pairF_iff {mx my r s jR : Nat} (hjR : jR < ordK LR 3) {T : List Nat}
    {p : Equiv.Perm (Fin n)} (hT : Acts n (apL w (mask w) T) p) (hp : p ∈ Gen n S 2) :
    pairF w (mask w) BP mx r s my (elemT n (n * w) LR TR 3 jR) T = true ↔
      orderOf (el n S base 3 jR * p) = r ∧ orderOf (el n S base 3 jR *
        (p * (el n S base 3 jR ^ (mx - 1) * p ^ (my - 1)))) = s := by
  have hR : Acts n (apL w (mask w) (elemT n (n * w) LR TR 3 jR)) (el n S base 3 jR) :=
    apL_elemT hQ jR
  have hx := el_mem hQ hjR
  have a1 : Acts n (fun x => apL w (mask w) (elemT n (n * w) LR TR 3 jR) (apL w (mask w) T x))
      (el n S base 3 jR * p) := fun y => by
    simp only
    rw [hT y, hR]
    rfl
  have a2 : Acts n (fun x => apL w (mask w) (elemT n (n * w) LR TR 3 jR) (apL w (mask w) T
      (itF (apL w (mask w) (elemT n (n * w) LR TR 3 jR)) (Nat.sub mx 1)
        (itF (apL w (mask w) T) (Nat.sub my 1) x))))
      (el n S base 3 jR * (p * (el n S base 3 jR ^ (mx - 1) * p ^ (my - 1)))) := fun y => by
    simp only
    rw [acts_itF hT (Nat.sub my 1) y, acts_itF hR (Nat.sub mx 1), hT, hR]
    rfl
  unfold pairF
  rw [CIdx.bAnd_iff', ordF_iff hQ a1 (Subgroup.mul_mem _ hx hp),
    ordF_iff hQ a2 (Subgroup.mul_mem _ hx (Subgroup.mul_mem _ hp (Subgroup.mul_mem _
      (Subgroup.pow_mem _ hx _) (Subgroup.pow_mem _ hp _))))]

theorem triple_count (q : Equiv.Perm (Fin n) → Bool) (f : Nat → Nat → Nat → Nat)
    (hf : ∀ k0 < sz n S base 0, ∀ k1 < sz n S base 1, ∀ k2 < sz n S base 2,
      f k0 k1 k2 = if q (Orb.trP n S base 0 k0 * (Orb.trP n S base 1 k1 *
        (Orb.trP n S base 2 k2 * 1))) = true then 1 else 0) :
    ∑ k0 ∈ range (rcnt (LR 0)), ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)),
      f k0 k1 k2 = (products (CIdx.trLists n S base 0 3)).countP q := by
  rw [countP_products3, rcnt_eq hQ (i := 0) (by norm_num), rcnt_eq hQ (i := 1) (by norm_num),
    rcnt_eq hQ (i := 2) (by norm_num)]
  exact sum_congr rfl fun k0 h0 => sum_congr rfl fun k1 h1 => sum_congr rfl fun k2 h2 =>
    hf _ (mem_range.1 h0) _ (mem_range.1 h1) _ (mem_range.1 h2)

theorem forall₂_orderTables {e : Nat} (he : 0 < e) :
    List.Forall₂ (CFSG.Sporadic.Th.Rep n)
      (filterProducts n (ordTest n e) (levTables n S base 3) (idT n) [])
      ((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter fun h =>
        decide (orderOf h = e)).reverse ++ []) :=
  filterProducts_spec (n := n) (G := Equiv.Perm (Fin n)) (f := ordTest n e)
    (P := fun g => orderOf g = e) (fun _ _ hTg => ordTest_iff perm_faithful hTg he)
    (forall₂_levTables hQ) (gT := idT n) (g := 1) (CFSG.Sporadic.Th.Rep.idT (PtCnt.n32 hQ))
    (acc := []) (accG := []) List.Forall₂.nil

theorem mem_orderList {e : Nat} (x : Equiv.Perm (Fin n)) :
    x ∈ (((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter fun h =>
      decide (orderOf h = e)).reverse ++ [] ↔ x ∈ Gen n S 2 ∧ orderOf x = e := by
  obtain ⟨hm, -⟩ := products_spec hQ 3 0 (by omega)
  simp only [List.append_nil, List.mem_reverse, List.mem_filter, List.mem_map, one_mul,
    exists_eq_right, decide_eq_true_eq, hm, fix_zero]

theorem nodup_orderList (e : Nat) :
    ((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter fun h =>
      decide (orderOf h = e)).reverse ++ []).Nodup := by
  obtain ⟨-, hnd⟩ := products_spec hQ 3 0 (by omega)
  rw [List.append_nil, List.nodup_reverse]
  exact (hnd.map (mul_right_injective 1)).filter _

end Chain

open CFSG.KS.SporSch.CIdx CFSG.KS.SporSch.J1C CFSG.KS.ClassOne CFSG.KS.Raw.Orb in
theorem ptCount_sound {n w kS BP mx my r s cap : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hQ : ChainCK n w PS PSI LR TR TRI kS 2 3 BP S base D)
    {lA lB : List Nat} (hlA : bindListK n w (PS 0) lA = true) (hlB : bindListK n w (PS 1) lB = true)
    (hpos : 0 < mx ∧ 0 < my ∧ 0 < r ∧ 0 < s ∧ mx ≠ my)
    {jR : Nat} {CS : List Nat} {L : Nat}
    (hCS : rcnt (LR 0) ≤ CS.length * L) (hblk : L * (rcnt (LR 1) * rcnt (LR 2)) < 1048576)
    (hc : ∀ b < CS.length, cntJB n w (mask w) (n * w) BP 3 mx my r s LR TR
      (elemT n (n * w) LR TR 3 jR) (b * L) L = CS.getD b 0)
    {E IA IB PA LB DP : Nat → Nat} {c r0 : Nat}
    (hhd : clsPtHdK n w (mask w) (n * w) BP 3 LR TR E c r0 jR mx cap = true)
    (hcl : ∀ k < c, clsPtK n w (mask w) (n * w) BP 3 (ordK LR 3) (PS 0) (PSI 0) (PS 1) (PSI 1)
      LR TR E IA IB PA LB DP c r0 k = true)
    (hcX : c = (CS.map fun v => v % 1048576).sum) :
    let X := filterProducts n (ordTest n mx) (levTables n S base 3) (idT n) []
    let Y := filterProducts n (ordTest n my) (levTables n S base 3) (idT n) []
    let gens : Array Table := #[listTbl n lA, listTbl n lB]
    let gensInv : Array Table := #[invT n (listTbl n lA), invT n (listTbl n lB)]
    X.length = (CS.map fun v => v % 1048576).sum ∧
      Y.length = (CS.map fun v => (v / 1048576) % 1048576).sum ∧
      classOK n gens gensInv X cap = true ∧
      classTotal n gens gensInv X Y cap r s mx my =
        c * (CS.map fun v => (v / 1099511627776) % 1048576).sum := by
  intro X Y gens gensInv
  have hn := PtCnt.n32 hQ
  obtain ⟨hmx, hmy, hr, hs, hne⟩ := hpos
  obtain ⟨hc0, hcc, hjR, ho0, hncard, hiff⟩ := cls_sound hQ hhd hcl
  obtain ⟨hFB, hFC⟩ := field_sum (w := w) (BP := BP) (mx := mx) (my := my) (r := r) (s := s)
    (R := elemT n (n * w) LR TR 3 jR) hCS hc hblk
  beta_reduce at hFB hFC
  have hx0 := el_mem hQ hjR
  have trip : ∀ k0 < sz n S base 0, ∀ k1 < sz n S base 1, ∀ k2 < sz n S base 2,
      let p := Orb.trP n S base 0 k0 * (Orb.trP n S base 1 k1 * (Orb.trP n S base 2 k2 * 1))
      (∀ e, ordF w (mask w) BP 3 (apL w (mask w) (T3 n (n * w) LR TR k0 k1 k2)) e = true ↔
        orderOf p = e) ∧
      (pairF w (mask w) BP mx r s my (elemT n (n * w) LR TR 3 jR) (T3 n (n * w) LR TR k0 k1 k2) =
        true ↔ orderOf (el n S base 3 jR * p) = r ∧ orderOf (el n S base 3 jR *
          (p * (el n S base 3 jR ^ (mx - 1) * p ^ (my - 1)))) = s) := fun k0 h0 k1 h1 k2 h2 =>
    ⟨fun _ => ordF_iff hQ (acts_T3 hQ h0 h1 h2) (T3_mem hQ h0 h1 h2),
      pairF_iff hQ hjR (acts_T3 hQ h0 h1 h2) (T3_mem hQ h0 h1 h2)⟩
  have hXF := forall₂_orderTables hQ hmx
  have hYF := forall₂_orderTables hQ hmy
  have hXlen : X.length = (CS.map fun v => v % 1048576).sum :=
    ptLen_sound hQ (mx := mx) (my := my) (r := r) (s := s) (R := elemT n (n * w) LR TR 3 jR) hmx
      hCS hc hblk
  have hY : Y.length = (CS.map fun v => (v / 1048576) % 1048576).sum := by
    rw [hYF.length_eq, hFB]
    have e : ((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter fun h =>
        decide (orderOf h = my)).reverse ++ []).length =
        (products (CIdx.trLists n S base 0 3)).countP fun g => decide (orderOf g = my) := by
      simp [List.countP_eq_length_filter]
    rw [e]
    symm
    refine triple_count hQ _ _ fun k0 h0 k1 h1 k2 h2 => ?_
    obtain ⟨hA, -⟩ := trip k0 h0 k1 h1 k2 h2
    simp only [hA]
    generalize orderOf (Orb.trP n S base 0 k0 * (Orb.trP n S base 1 k1 *
      (Orb.trP n S base 2 k2 * 1))) = o
    by_cases ho : o = my
    · subst ho
      simp [Ne.symm hne]
    · simp [ho]
  set Cs : Set (Equiv.Perm (Fin n)) := {x | ∃ k < c, el n S base 3 (E k) = x} with hCsdef
  have hCf : Cs.Finite :=
    ((Set.finite_lt_nat c).image fun k => el n S base 3 (E k)).subset fun x ⟨k, hk, e⟩ =>
      ⟨k, hk, e⟩
  have rA := rep_listTbl_of_bind hn hlA (prep_gen hQ (j := 0) (by norm_num)).1
  have rB := rep_listTbl_of_bind hn hlB (prep_gen hQ (j := 1) (by norm_num)).1
  have hgens : ∀ l < gens.size, CFSG.Sporadic.Th.Rep n gens[l]! (permOfArr n S[l]!) ∧
      CFSG.Sporadic.Th.Rep n gensInv[l]! (permOfArr n S[l]!)⁻¹ := by
    intro l hl
    have hl2 : l < 2 := hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact ⟨by rw [arr2_get0]; exact rA, by rw [arr2_get0]; exact Tbl.invT_rep hn rA⟩
    · exact ⟨by rw [arr2_get1]; exact rB, by rw [arr2_get1]; exact Tbl.invT_rep hn rB⟩
  have hCcl : ∀ l < gens.size, ∀ x ∈ Cs, permOfArr n S[l]! * x * (permOfArr n S[l]!)⁻¹ ∈ Cs := by
    intro l hl x hx
    obtain ⟨g, hg, rfl⟩ := (hiff x).1 hx
    exact (hiff _).2 ⟨permOfArr n S[l]! * g, Subgroup.mul_mem _ (gen_mem (by omega)) hg,
      by group⟩
  have hmin : ∀ g ∈ Cs, ∀ D : Set (Equiv.Perm (Fin n)), D.Finite → g ∈ D →
      (∀ l < gens.size, ∀ y ∈ D, permOfArr n S[l]! * y * (permOfArr n S[l]!)⁻¹ ∈ D) →
        Cs ⊆ D := by
    intro g hg D hD hgD hDc y hy
    have hG := conj_closed (kO := 2) (S := S) hD fun j hj x hx => hDc j (by omega) x hx
    obtain ⟨a, ha, rfl⟩ := (hiff y).1 hy
    obtain ⟨b, hb, rfl⟩ := (hiff g).1 hg
    have := hG (a * b⁻¹) (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)) _ hgD
    have e : a * b⁻¹ * (b * el n S base 3 jR * b⁻¹) * (a * b⁻¹)⁻¹ = a * el n S base 3 jR * a⁻¹ :=
      by group
    rwa [e] at this
  have hXlen' : X.length = c := hXlen.trans hcX.symm
  have hXC : ∀ x ∈ ((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter fun h =>
      decide (orderOf h = mx)).reverse ++ []), x ∈ Cs := by
    have hsub : Cs ⊆ {x | x ∈ ((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter
        fun h => decide (orderOf h = mx)).reverse ++ [])} := fun x hx => by
      obtain ⟨g, hg, rfl⟩ := (hiff x).1 hx
      exact (mem_orderList hQ _).2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx0)
        (Subgroup.inv_mem _ hg), by rw [orderOf_conj']; exact ho0⟩
    have hn2 : {x | x ∈ ((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter
        fun h => decide (orderOf h = mx)).reverse ++ [])}.ncard = c := by
      rw [show {x | x ∈ ((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter
          fun h => decide (orderOf h = mx)).reverse ++ [])} =
          (((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter
            fun h => decide (orderOf h = mx)).reverse ++ []).toFinset : Set _) by ext; simp,
        Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_orderList hQ mx)]
      exact hXF.length_eq.symm.trans hXlen'
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hn2, hncard])
      (List.finite_toSet _)
    intro x hx
    rw [heq]
    exact hx
  obtain ⟨hcls, hok, hcsz⟩ := classOK_one hn hgens hCf hCcl hmin hXF hXC
    (hXlen'.trans hncard.symm) (List.ne_nil_of_length_pos (by rw [hXlen']; exact hc0))
    (hncard.trans_le hcc)
  refine ⟨hXlen, hY, hok, ?_⟩
  rw [classTotal_one hcls, hcsz, hncard]
  refine congrArg (c * ·) ?_
  have hX0 : 0 < X.length := by rw [hXlen']; exact hc0
  have hX0' : 0 < (((((products (CIdx.trLists n S base 0 3)).map (1 * ·)).filter
      fun h => decide (orderOf h = mx)).reverse ++ [])).length :=
    lt_of_lt_of_eq hX0 hXF.length_eq
  have rX0 := forall₂_head hXF hX0'
  change List.countP (pairTest n r s mx my
    (filterProducts n (ordTest n mx) (levTables n S base 3) (idT n) []).toArray[0]!)
    (filterProducts n (ordTest n my) (levTables n S base 3) (idT n) []) = _
  have hmem0 := hXC _ (List.getElem_mem hX0')
  rw [hCsdef, Set.mem_ofPred_eq] at hmem0
  obtain ⟨h, hh, hx1⟩ := (hiff _).1 hmem0
  rw [← hx1] at rX0
  rw [countP_eq_of_forall₂ (q := fun y => decide (orderOf (h * el n S base 3 jR * h⁻¹ * y) = r ∧
      orderOf (h * el n S base 3 jR * h⁻¹ * (y * ((h * el n S base 3 jR * h⁻¹) ^ (mx - 1) *
        y ^ (my - 1)))) = s)) hYF
    (fun T y hTy _ => by rw [pairTest_rep rX0 hTy hr hs, decide_eq_true_iff]),
    countP_filt]
  have e1 : ((products (CIdx.trLists n S base 0 3)).countP fun g => decide (orderOf g = my) &&
      decide (orderOf (h * el n S base 3 jR * h⁻¹ * g) = r ∧
        orderOf (h * el n S base 3 jR * h⁻¹ * (g * ((h * el n S base 3 jR * h⁻¹) ^ (mx - 1) *
          g ^ (my - 1)))) = s)) =
      Nat.card {g // g ∈ Gen n S 2 ∧ Pp mx my r s (h * el n S base 3 jR * h⁻¹) g} := by
    rw [card_filter hQ]
    simp only [Pp, Bool.decide_and]
  rw [e1, card_conj _ hh, card_filter hQ, hFC]
  symm
  refine triple_count hQ _ _ fun k0 h0 k1 h1 k2 h2 => ?_
  obtain ⟨hA, hP⟩ := trip k0 h0 k1 h1 k2 h2
  simp only [hA, hP, Pp]
  generalize Orb.trP n S base 0 k0 * (Orb.trP n S base 1 k1 * (Orb.trP n S base 2 k2 * 1)) = p
  by_cases ho : orderOf p = my
  · simp [ho, Ne.symm hne]
  · simp [ho]

end CFSG.KS.SporSch.MOC

end
