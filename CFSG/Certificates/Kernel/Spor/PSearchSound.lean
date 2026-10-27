module

public import Certificates.Data.Kernel.Spor.HypK
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeKit

public section

namespace CFSG.KS.PSearch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Certificates.ChainArrays

theorem strictN_eqS (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem nIf_eqS (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_eqS (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem foldr_range_addS (f : Nat → Nat) :
    ∀ m a, (List.range m).foldr (fun k s => Nat.add s (f k)) a = a + ∑ k ∈ Finset.range m, f k
  | 0, a => by simp
  | m + 1, a => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_range_addS f m,
      Finset.sum_range_succ]
    change a + f m + _ = _
    omega

theorem sumN_eqS (m : Nat) (f : Nat → Nat) : sumN m f = ∑ k ∈ Finset.range m, f k := by
  unfold sumN
  rw [foldN_eq, foldr_range_addS, Nat.zero_add]

theorem apL_cons (w m T : Nat) (ts : List Nat) (p : Nat) :
    apL w m (T :: ts) p = apL w m ts (pg w m T p) := strictN_eqS _ _

theorem apI_cons (w m T : Nat) (tis : List Nat) (p : Nat) :
    apI w m (T :: tis) p = pg w m T (apI w m tis p) := strictN_eqS _ _

def LRep (n w : Nat) (ts : List Nat) (A : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, apL w (mask w) ts x = A x

def IRep (n w : Nat) (tis : List Nat) (B : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, apI w (mask w) tis x = B x

theorem lrep_nil (n w : Nat) : LRep n w [] 1 := fun _ => rfl

theorem irep_nil (n w : Nat) : IRep n w [] 1 := fun _ => rfl

theorem lrep_cons {n w T : Nat} {ts : List Nat} {A B : Equiv.Perm (Fin n)} (h : LRep n w ts A)
    (hT : PRep n w T B) : LRep n w (T :: ts) (A * B) := fun x => by
  rw [apL_cons, hT x, h (B x), Equiv.Perm.mul_apply]

theorem irep_cons {n w T : Nat} {tis : List Nat} {A B : Equiv.Perm (Fin n)} (h : IRep n w tis A⁻¹)
    (hT : PRep n w T B⁻¹) : IRep n w (T :: tis) (A * B)⁻¹ := fun x => by
  rw [apI_cons, h x, hT (A⁻¹ x), mul_inv_rev, Equiv.Perm.mul_apply]

theorem apply_eq_of_inv_mul_fix {n : Nat} {A c : Equiv.Perm (Fin n)} {x : Fin n}
    (h : (A⁻¹ * c) x = x) : c x = A x := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq] at h
  exact h

theorem testBit_pgS (w p j k : Nat) :
    (pg w (mask w) p j).testBit k = (decide (k < w) && p.testBit (w * j + k)) :=
  PF.testBit_pgM w p j k

theorem im_lt {w i IM q : Nat} (hIM : IM < 2 ^ (w * i)) (hq : q < 2 ^ w) :
    Nat.lor IM (Nat.shiftLeft q (Nat.mul w i)) < 2 ^ (w * (i + 1)) := by
  change IM ||| q <<< (w * i) < _
  have h1 : IM < 2 ^ (w * (i + 1)) :=
    Nat.lt_of_lt_of_le hIM (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left w (by omega)))
  have h2 : q <<< (w * i) < 2 ^ (w * (i + 1)) := by
    rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_left hq (Nat.two_pow_pos _)
  exact Nat.or_lt_two_pow h1 h2

theorem pg_im_old {w i IM q l : Nat} (hl : l < i) :
    pg w (mask w) (Nat.lor IM (Nat.shiftLeft q (Nat.mul w i))) l = pg w (mask w) IM l := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pgS, testBit_pgS]
  by_cases hk : k < w
  · have e : ¬ w * i ≤ w * l + k := by
      have hl1 : l + 1 ≤ i := by omega
      have := Nat.mul_le_mul_left w hl1
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    change (decide (k < w) && (IM ||| q <<< (w * i)).testBit (w * l + k)) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    simp [e]
  · simp [hk]

theorem pg_im_new {w i IM q : Nat} (hIM : IM < 2 ^ (w * i)) (hq : q < 2 ^ w) :
    pg w (mask w) (Nat.lor IM (Nat.shiftLeft q (Nat.mul w i))) i = q := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pgS]
  by_cases hk : k < w
  · change (decide (k < w) && (IM ||| q <<< (w * i)).testBit (w * i + k)) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hIM (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk]

theorem pnode_zero (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP nb : Nat) (src Ys pr : List Nat)
    (i : Nat) (ts tis : List Nat) (IM : Nat) :
    pnode n w m nw LR TR TRI BP nb src Ys pr 0 i ts tis IM =
      nIf(leafOK w m nb BP IM ts pr, 1, 0) := rfl

theorem pnode_succ (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP nb : Nat) (src Ys pr : List Nat)
    (fuel i : Nat) (ts tis : List Nat) (IM : Nat) :
    pnode n w m nw LR TR TRI BP nb src Ys pr (fuel + 1) i ts tis IM =
      nIf(Nat.blt (nthN src i) i,
        nIf(Nat.blt (rpos w m nw (LR i) (apI w m tis (pg w m (nthN Ys i) (pg w m IM (nthN src i)))))
            (rcnt (LR i)),
          pnode n w m nw LR TR TRI BP nb src Ys pr fuel (i + 1)
            (TR (roff n nw (LR i) +
              rpos w m nw (LR i) (apI w m tis (pg w m (nthN Ys i) (pg w m IM (nthN src i))))) :: ts)
            (TRI (roff n nw (LR i) +
              rpos w m nw (LR i) (apI w m tis (pg w m (nthN Ys i) (pg w m IM (nthN src i))))) :: tis)
            (Nat.lor IM (Nat.shiftLeft (pg w m (nthN Ys i) (pg w m IM (nthN src i))) (Nat.mul w i))),
          0),
        sumN (rcnt (LR i)) (fun k =>
          nIf(Nat.beq (pg w m (nthN Ys i) (apL w m ts (rpt w m (LR i) k))) (apL w m ts (rpt w m (LR i) k)),
            pnode n w m nw LR TR TRI BP nb src Ys pr fuel (i + 1) (TR (roff n nw (LR i) + k) :: ts)
              (TRI (roff n nw (LR i) + k) :: tis)
              (Nat.lor IM (Nat.shiftLeft (apL w m ts (rpt w m (LR i) k)) (Nat.mul w i))),
            0))) := by
  unfold pnode
  simp only [Nat.rec_add_one, strictN_eqS, child]
  rfl

theorem leafOK_of {n w nb BP IM : Nat} {ts : List Nat} {A : Equiv.Perm (Fin n)}
    (hts : LRep n w ts A) (hbase : ∀ l < nb, pg w (mask w) BP l < n)
    (hIM : ∀ l (hl : l < nb), pg w (mask w) IM l = A ⟨pg w (mask w) BP l, hbase l hl⟩) :
    ∀ pr : List Nat, (∀ P ∈ pr, ∃ g : Equiv.Perm (Fin n), PRep n w P g ∧ A * g = g * A) →
      leafOK w (mask w) nb BP IM ts pr = true
  | [], _ => rfl
  | P :: pr, hpr => by
    change bAnd(allN nb _, leafOK w (mask w) nb BP IM ts pr) = true
    rw [bAnd_eqS, Bool.and_eq_true]
    refine ⟨allN_iff.2 fun l hl => ?_, leafOK_of hts hbase hIM pr fun P' hP' => hpr P' (by simp [hP'])⟩
    obtain ⟨g, hg, hc⟩ := hpr P (by simp)
    set x : Fin n := ⟨pg w (mask w) BP l, hbase l hl⟩
    have e1 : pg w (mask w) P (pg w (mask w) BP l) = g x := hg x
    rw [e1, hts (g x), hIM l hl, hg (A x), Nat.beq_eq]
    have := congrArg (fun σ : Equiv.Perm (Fin n) => ((σ x : Fin n) : Nat)) hc
    simpa only [Equiv.Perm.mul_apply] using this

section Sound

variable {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {Q : RawSchreierDatum n} {O : Array (Array Nat)} {W : Array (List ℤ)}
  {chunks : Nat}
  (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
include hA hF hQ hb hp hl

theorem card_le_pnode {src Ys pr : List Nat} (hs : srcOK w (mask w) BP nb src Ys = true)
    {Y : Nat → Equiv.Perm (Fin n)} (hY : ∀ l < nb, PRep n w (nthN Ys l) (Y l)) :
    ∀ fuel i, i + fuel = nb → ∀ (ts tis : List Nat) (IM : Nat) (A : Equiv.Perm (Fin n)),
      LRep n w ts A → IRep n w tis A⁻¹ → IM < 2 ^ (w * i) →
      (∀ l (hl : l < i), ∀ hb' : pg w (mask w) BP l < n,
        pg w (mask w) IM l = A ⟨pg w (mask w) BP l, hb'⟩) →
      ∀ X : Finset (Equiv.Perm (Fin n)),
        (∀ c ∈ X, (∀ l < nb, c * Y l = Y l * c) ∧
          (∀ P ∈ pr, ∃ g : Equiv.Perm (Fin n), PRep n w P g ∧ c * g = g * c) ∧
          A⁻¹ * c ∈ Q.levelSubgroup i) →
        X.card ≤ pnode n w (mask w) (n * w) LR TR TRI BP nb src Ys pr fuel i ts tis IM := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hQc : Q.baseCount = nb := hA.base_size ▸ hbs
  have hbl := base_lt_of_levels hb hl
  have hbt : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hbn : ∀ l < nb, pg w (mask w) BP l < n := fun l h => hbt l h ▸ hbl l h
  have hw : n < 2 ^ w := by have := hb.2.1; omega
  have hbase : ∀ l (h : l < Q.baseCount),
      Q.base.get ⟨l, h⟩ = ⟨pg w (mask w) BP l, hbn l (hQc ▸ h)⟩ := fun l h =>
    Fin.ext ((hA.base_val ⟨l, h⟩).trans (hbt l (hQc ▸ h)))
  have hsrc : ∀ l < nb, nthN src l ≤ l ∧
      pg w (mask w) (nthN Ys l) (pg w (mask w) BP (nthN src l)) = pg w (mask w) BP l := fun l h => by
    have := allN_iff.1 hs l h
    rw [bAnd_eqS, Bool.and_eq_true, Nat.ble_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  intro fuel
  induction fuel with
  | zero =>
    intro i hi ts tis IM A hts _ _ hIM X hX
    rw [Nat.add_zero] at hi
    subst hi
    rw [pnode_zero, nIf_eqS]
    have hXA : ∀ c ∈ X, c = A := fun c hc => by
      have h := (hX c hc).2.2
      rw [← hQc, Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot, inv_mul_eq_one] at h
      exact h.symm
    by_cases hne : X = ∅
    · rw [hne, Finset.card_empty]
      exact Nat.zero_le _
    obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hok : leafOK w (mask w) i BP IM ts pr = true := by
      have hcA := hXA c hc
      subst hcA
      exact leafOK_of hts hbn (fun l hl => hIM l hl (hbn l hl)) pr (hX c hc).2.1
    rw [if_pos hok]
    exact Finset.card_le_one.2 fun a ha b hb2 => (hXA a ha).trans (hXA b hb2).symm
  | succ fuel ih =>
    intro i hi ts tis IM A hts htis hIMlt hIM X hX
    have hib : i < nb := by omega
    have hiQ : i < Q.baseCount := hQc ▸ hib
    obtain ⟨Ag, hTK⟩ := agree_levelK hb hp hbl hib (hl i hib)
    set R := LR i with hR
    set o := roff n (n * w) R with ho
    set TK : Nat → Equiv.Perm (Fin n) :=
      fun k => permOfArr n (unpack n w (TR (o + k))) with hTKdef
    set L := lev n S base i with hL
    have LF := hA.levelFacts hF hiQ
    have hTKe : ∀ k < L.pts.size, levT n S base i k = TK k := fun k hk =>
      (hA.rep_levT hF hiQ hk).unique (Ag.tr k hk).1
    set bi : Fin n := ⟨pg w (mask w) BP i, hbn i hib⟩ with hbi
    have hkc : ∀ c ∈ X, L.pos[((A⁻¹ * c) bi : Nat)]! < L.pts.size ∧
        (A * TK L.pos[((A⁻¹ * c) bi : Nat)]!)⁻¹ * c ∈ Q.levelSubgroup (i + 1) := by
      intro c hc
      have h := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T.levT_pos_inv_mul_mem hA hF hQ
        hiQ (hX c hc).2.2
      rw [hbase i hiQ] at h
      refine ⟨h.1, ?_⟩
      rw [← hTKe _ h.1, mul_inv_rev, mul_assoc]
      exact h.2
    have hchild : ∀ k < rcnt R, ∀ q, ∀ Xk : Finset (Equiv.Perm (Fin n)),
        (∀ c ∈ Xk, c ∈ X ∧ (A * TK k)⁻¹ * c ∈ Q.levelSubgroup (i + 1) ∧ ((c bi : Fin n) : Nat) = q) →
        Xk.card ≤ pnode n w (mask w) (n * w) LR TR TRI BP nb src Ys pr fuel (i + 1)
          (TR (o + k) :: ts) (TRI (o + k) :: tis) (Nat.lor IM (Nat.shiftLeft q (Nat.mul w i))) := by
      intro k hk q Xk hXk
      by_cases hne : Xk = ∅
      · rw [hne, Finset.card_empty]
        exact Nat.zero_le _
      obtain ⟨c0, hc0⟩ := Finset.nonempty_iff_ne_empty.2 hne
      obtain ⟨hc0X, hc0H, hc0q⟩ := hXk c0 hc0
      have hq : q < 2 ^ w := hc0q ▸ Nat.lt_trans (c0 bi).2 hw
      refine ih (i + 1) (by omega) _ _ _ (A * TK k) (lrep_cons hts (hTK k hk).1)
        (irep_cons htis (hTK k hk).2) (im_lt hIMlt hq) ?_ Xk fun c hc => ?_
      · intro l hl' hb'
        have hlQ : l < Q.baseCount := by omega
        have hfix := Q.levelSubgroup_fixes_base_index (i + 1) _ hc0H ⟨l, hlQ⟩ hl'
        rw [hbase l hlQ] at hfix
        rw [← apply_eq_of_inv_mul_fix hfix]
        rcases Nat.lt_or_ge l i with hli | hli
        · rw [pg_im_old hli, hIM l hli hb']
          have hfixA := Q.levelSubgroup_fixes_base_index i _ (hX c0 hc0X).2.2 ⟨l, hlQ⟩ hli
          rw [hbase l hlQ] at hfixA
          exact congrArg Fin.val (apply_eq_of_inv_mul_fix hfixA).symm
        · have hli' : l = i := by omega
          subst hli'
          rw [pg_im_new hIMlt hq, ← hc0q]
      · obtain ⟨hcX, hcH, -⟩ := hXk c hc
        exact ⟨(hX c hcX).1, (hX c hcX).2.1, hcH⟩
    rw [pnode_succ, nIf_eqS]
    have hsi := hsrc i hib
    have hYi := hY i hib
    by_cases hlt : nthN src i < i
    ·
      rw [if_pos (Nat.blt_eq.mpr hlt)]
      by_cases hne : X = ∅
      · rw [hne, Finset.card_empty]
        exact Nat.zero_le _
      obtain ⟨c0, hc0⟩ := Finset.nonempty_iff_ne_empty.2 hne
      set s := nthN src i with hsdef
      have hsQ : s < Q.baseCount := by omega
      set bs : Fin n := ⟨pg w (mask w) BP s, hbn s (by omega)⟩ with hbsdef
      have hYbs : Y i bs = bi := Fin.ext (by rw [← hYi bs]; exact hsi.2)
      have hcs : ∀ c ∈ X, c bs = A bs := fun c hc => by
        have hfix := Q.levelSubgroup_fixes_base_index i _ (hX c hc).2.2 ⟨s, hsQ⟩ hlt
        rw [hbase s hsQ] at hfix
        exact apply_eq_of_inv_mul_fix hfix
      have hci : ∀ c ∈ X, c bi = Y i (A bs) := fun c hc => by
        have e := congrArg (fun σ : Equiv.Perm (Fin n) => σ bs) ((hX c hc).1 i hib)
        simp only [Equiv.Perm.mul_apply] at e
        rw [← hYbs, e, hcs c hc]
      set p := pg w (mask w) (nthN Ys i) (pg w (mask w) IM s) with hpdef
      have hpv : p = ((Y i (A bs) : Fin n) : Nat) := by
        rw [hpdef, hIM s hlt (hbn s (by omega)), hYi (A bs)]
      have hAp : apI w (mask w) tis p = (((A⁻¹ * c0) bi : Fin n) : Nat) := by
        rw [hpv, htis (Y i (A bs)), Equiv.Perm.mul_apply, hci c0 hc0]
      have hk0 := (hkc c0 hc0).1
      have hpos : rpos w (mask w) (n * w) R (apI w (mask w) tis p) =
          L.pos[(((A⁻¹ * c0) bi : Fin n) : Nat)]! := by
        rw [hAp]
        exact Ag.posE _ (Fin.is_lt _) hk0
      have hkR : L.pos[(((A⁻¹ * c0) bi : Fin n) : Nat)]! < rcnt R := Ag.cnt ▸ hk0
      rw [hpos, nIf_eqS, if_pos (Nat.blt_eq.mpr hkR)]
      refine hchild _ hkR p X fun c hc => ⟨hc, ?_, ?_⟩
      · have e : (A⁻¹ * c) bi = (A⁻¹ * c0) bi := by
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hci c hc, hci c0 hc0]
        have := (hkc c hc).2
        rwa [e] at this
      · rw [hpv, hci c hc]
    ·
      rw [if_neg (by rw [Nat.blt_eq]; exact hlt)]
      have hsi' : nthN src i = i := le_antisymm hsi.1 (Nat.le_of_not_lt hlt)
      have hYbi : Y i bi = bi := Fin.ext (by rw [← hYi bi]; have := hsi.2; rwa [hsi'] at this)
      rw [sumN_eqS]
      set kOf : Equiv.Perm (Fin n) → Nat := fun c => L.pos[(((A⁻¹ * c) bi : Fin n) : Nat)]!
        with hkOf
      rw [Finset.card_eq_sum_card_fiberwise (f := kOf) (t := Finset.range (rcnt R))
        (fun c hc => Finset.mem_range.2 (Ag.cnt ▸ (hkc c hc).1))]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : k < rcnt R := Finset.mem_range.1 hk
      have hkL : k < L.pts.size := Ag.cnt ▸ hk'
      set q := apL w (mask w) ts (rpt w (mask w) R k) with hqdef
      by_cases hne : X.filter (fun c => kOf c = k) = ∅
      · rw [hne, Finset.card_empty]
        exact Nat.zero_le _
      obtain ⟨c0, hc0⟩ := Finset.nonempty_iff_ne_empty.2 hne
      obtain ⟨hc0X, hc0k⟩ := Finset.mem_filter.1 hc0
      have hqc : ∀ c ∈ X, kOf c = k → q = ((c bi : Fin n) : Nat) := fun c hc hck => by
        have hpk := (hkc c hc).1
        have hpt := LF.pts_pos _ (Fin.is_lt _) hpk
        have e : rpt w (mask w) R k = (((A⁻¹ * c) bi : Fin n) : Nat) := by
          rw [Ag.pt k hkL, ← hck]
          exact hpt
        rw [hqdef, e, hts ((A⁻¹ * c) bi)]
        simp
      have hfl : Nat.beq (pg w (mask w) (nthN Ys i) q) q = true := by
        rw [Nat.beq_eq, hqc c0 hc0X hc0k, hYi (c0 bi)]
        have e := congrArg (fun σ : Equiv.Perm (Fin n) => σ bi) ((hX c0 hc0X).1 i hib)
        simp only [Equiv.Perm.mul_apply, hYbi] at e
        rw [← e]
      rw [nIf_eqS, if_pos hfl]
      refine hchild k hk' q _ fun c hc => ?_
      obtain ⟨hcX, hck⟩ := Finset.mem_filter.1 hc
      refine ⟨hcX, ?_, (hqc c hcX hck).symm⟩
      have := (hkc c hcX).2
      have hck' : L.pos[(((A⁻¹ * c) bi : Fin n) : Nat)]! = k := hck
      rwa [hck'] at this

theorem card_le_pcnt {src Ys pr : List Nat} (hs : srcOK w (mask w) BP nb src Ys = true)
    {Y : Nat → Equiv.Perm (Fin n)} (hY : ∀ l < nb, PRep n w (nthN Ys l) (Y l))
    (X : Finset (Equiv.Perm (Fin n)))
    (hX : ∀ c ∈ X, c ∈ Q.originalSubgroup ∧ (∀ l < nb, c * Y l = Y l * c) ∧
      ∀ P ∈ pr, ∃ g : Equiv.Perm (Fin n), PRep n w P g ∧ c * g = g * c) :
    X.card ≤ pcnt n w (mask w) (n * w) LR TR TRI BP nb src Ys pr := by
  refine card_le_pnode hA hF hQ hb hp hl hs hY nb 0 (Nat.zero_add nb) [] [] 0 1 (lrep_nil n w)
    (by rw [inv_one]; exact irep_nil n w) (Nat.two_pow_pos _) (fun l hl => absurd hl (Nat.not_lt_zero l)) X
    fun c hc => ⟨(hX c hc).2.1, (hX c hc).2.2, ?_⟩
  rw [inv_one, one_mul, Q.levelSubgroup_zero_eq_original hQ]
  exact (hX c hc).1

theorem natCard_le_pcnt {src Ys pr : List Nat} (hs : srcOK w (mask w) BP nb src Ys = true)
    {Y : Nat → Equiv.Perm (Fin n)} (hY : ∀ l < nb, PRep n w (nthN Ys l) (Y l))
    {K : Subgroup (Equiv.Perm (Fin n))} (hK : K ≤ Q.originalSubgroup)
    (hKY : ∀ c ∈ K, ∀ l < nb, c * Y l = Y l * c)
    (hKpr : ∀ P ∈ pr, ∃ g : Equiv.Perm (Fin n), PRep n w P g ∧ ∀ c ∈ K, c * g = g * c) :
    Nat.card K ≤ pcnt n w (mask w) (n * w) LR TR TRI BP nb src Ys pr := by
  classical
  have e : Nat.card K = (Finset.univ.filter (· ∈ K)).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rw [e]
  refine card_le_pcnt hA hF hQ hb hp hl hs hY _ fun c hc => ?_
  have hcK : c ∈ K := (Finset.mem_filter.1 hc).2
  refine ⟨hK hcK, hKY c hcK, fun P hP => ?_⟩
  obtain ⟨g, hg, hgc⟩ := hKpr P hP
  exact ⟨g, hg, hgc c hcK⟩

end Sound

end CFSG.KS.PSearch

namespace CFSG.KS.HypK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PSearch CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem card_le_of_searchOK {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {Q : RawSchreierDatum n} {O : Array (Array Nat)}
    {W : Array (List ℤ)} {chunks : Nat}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS 6 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 6 BP) {src Yl Yp : List Nat}
    (h : searchOK n w LR TR TRI BP src Yl Yp = true)
    {Y : Nat → Equiv.Perm (Fin n)} (hY : ∀ l < 6, PRep n w (nthN Yl l) (Y l))
    {K : Subgroup (Equiv.Perm (Fin n))} (hK : K ≤ Q.originalSubgroup)
    (hKY : ∀ c ∈ K, ∀ l < 6, c * Y l = Y l * c)
    (hKp : ∀ P ∈ Yp, ∃ g : Equiv.Perm (Fin n), PRep n w P g ∧ ∀ c ∈ K, c * g = g * c) :
    Nat.card K ≤ 243 := by
  unfold searchOK at h
  rw [bAnd_eqS, Bool.and_eq_true, Nat.ble_eq] at h
  exact (natCard_le_pcnt hA hF hQ hb hp hl h.1 hY hK hKY hKp).trans h.2

end CFSG.KS.HypK

end
