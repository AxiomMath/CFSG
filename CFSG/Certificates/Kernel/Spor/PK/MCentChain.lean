module

public import CFSG.Certificates.Kernel.Spor.PK.MCnt
public import CFSG.Certificates.Kernel.Spor.PK.MBase
public import CFSG.Certificates.Kernel.Spor.PK.MCentSearch
public import Certificates.Data.Kernel.Spor.MCentS

public section

namespace CFSG.KS.MCent

open CFSG.KS.PK CFSG.Sporadic.Schreier CFSG.KC.Enum CFSG.KS

theorem transB_fix {n r b : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {s : BS}
    (hs : RunOK n F lv r s) (hF : ∀ l ∈ lv, F l b = b) {k : Nat} (hk : k < s.pts.length) :
    BS.trans F s k b = b := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk0 : 0 < k
    · have hpar := hs.par_lt k hk0 hk
      rw [BS.trans, dite_eq_left ⟨hk0, hpar⟩, ih _ hpar (by omega)]
      exact hF _ (hs.lab_mem k hk0 hk)
    · rw [BS.trans, dite_eq_right (by omega)]

theorem lvAt_fix (F : Nat → Nat → Nat) (NL : Nat) (bs : List Nat) :
    ∀ i, ∀ l ∈ lvAt F NL bs i, ∀ j < i, F l (bs.getD j 0) = bs.getD j 0
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | i + 1, l, hl, j, hj => by
    rw [lvAt, List.mem_filter, beq_iff_eq] at hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact lvAt_fix F NL bs i l hl.1 j h
    · rw [h]
      exact hl.2

theorem tauM_fix {n NL : Nat} {F : Nat → Nat → Nat} {bs : List Nat} {i k j : Nat}
    (hF : ∀ l ∈ lvAt F NL bs i, IsPermN n (F l)) (hb : bs.getD i 0 < n)
    (hk : k < (mbS n F NL bs i).pts.length) (hj : j < i) (hbj : bs.getD j 0 < n) :
    tau n F (mbS n F NL bs) i k ⟨bs.getD j 0, hbj⟩ = ⟨bs.getD j 0, hbj⟩ := by
  have hs : RunOK n F (lvAt F NL bs i) (bs.getD i 0) (mbS n F NL bs i) :=
    run_ok (fun l hl => (hF l hl).1) hb
  apply Fin.ext
  rw [tau, permOf_apply (trans_isPermN hs hF hk)]
  exact transB_fix hs (fun l hl => lvAt_fix F NL bs i l hl j hj) hk

theorem prods_fix {n : Nat} (a : Fin n) (Ts : List (List (Equiv.Perm (Fin n))))
    (h : ∀ T ∈ Ts, ∀ t ∈ T, t a = a) : ∀ x ∈ products Ts, x a = a :=
  mem_of_mem_products (MulAction.stabilizer (Equiv.Perm (Fin n)) a).toSubmonoid Ts h

theorem cfn_mul_permOf {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) (σ : Equiv.Perm (Fin n))
    {x : Nat} (hx : x < n) : cfn σ (f x) = cfn (σ * permOf n f) x := by
  simp only [cfn, dite_eq_left hx, dite_eq_left (hf.1 x hx), Equiv.Perm.mul_apply]
  congr 2
  exact Fin.ext (permOf_apply hf ⟨x, hx⟩).symm

theorem cSrch_eq {n w : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) {F : Nat → Nat → Nat}
    {s : Nat → BS} {V : Nat → Nat} (hg : ∀ i, GoodBS n F (s i)) (tst : Nat → Nat → Bool)
    (leaf : Nat → Bool) : ∀ (is : List Nat) (l : Nat) (σ : Equiv.Perm (Fin n)),
      cSrch n w (mask w) (n * w) (mask (n * w)) tst leaf l
          (is.map fun i => recBS n w F (s i) (V i)) (enc w (cfn σ) n) =
        prCnt (fun l τ => tst l (enc w (cfn τ) n)) (fun τ => leaf (enc w (cfn τ) n)) l
          (is.map fun i => (List.range (s i).pts.length).map (tau n F s i)) σ
  | [], l, σ => by
    simp only [List.map_nil, cSrch, prCnt, nIf_eq]
  | i :: is, l, σ => by
    have hn32 : n < 2 ^ 32 := by
      have : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
      omega
    have hwn : n < 2 ^ w := by omega
    simp only [List.map_cons, cSrch, prCnt]
    rw [foldUp_add _ (fun k s => by simp only [strictN_eq, nIf_eq, Nat.add_eq]; split <;> omega),
      lcnt_recBS hn16 hw (hg i), Nat.zero_add, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
    have hk' := List.mem_range.1 hk
    have hP := (hg i).2.2.2.2 k hk'
    simp only [Function.comp, strictN_eq, nIf_eq, Nat.add_eq, Nat.zero_add]
    rw [ltr_recBS hn16 hw (hg i) _ hk', pcomp_encode hn32 hwn (fun x hx => cfn_lt σ hx) hP.1]
    have e : enc w (fun x => cfn σ (BS.trans F (s i) k x)) n = enc w (cfn (σ * tau n F s i k)) n :=
      enc_congr fun x hx => cfn_mul_permOf hP σ hx
    rw [e, cSrch_eq hn16 hw hg tst leaf is (l + 1)]

theorem pg_cfn {n w : Nat} (hwn : n < 2 ^ w) (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    pg w (mask w) (enc w (cfn σ) n) x = σ x := by
  rw [pg_encode hwn (fun _ hx => cfn_lt σ hx) x.isLt, cfn_apply]

theorem leafC_iff {n w : Nat} (hwn : n < 2 ^ w) (g g' q : Equiv.Perm (Fin n)) :
    leafC n w (mask w) (enc w (cfn g) n) (enc w (cfn g') n) (enc w (cfn q) n) = true ↔
      q * g = g' * q := by
  unfold leafC
  rw [allFrom_iff]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have hi := h i i.isLt
    rw [Nat.zero_add, Nat.beq_eq, pg_cfn hwn g i, pg_cfn hwn q (g i), pg_cfn hwn q i,
      pg_cfn hwn g' (q i)] at hi
    exact hi
  · intro h i hi
    rw [Nat.zero_add, Nat.beq_eq]
    have e := congrArg (fun τ : Equiv.Perm (Fin n) => (τ ⟨i, hi⟩ : Nat)) h
    simp only [Equiv.Perm.mul_apply] at e
    rw [pg_cfn hwn g ⟨i, hi⟩, pg_cfn hwn q (g ⟨i, hi⟩), pg_cfn hwn q ⟨i, hi⟩,
      pg_cfn hwn g' (q ⟨i, hi⟩)]
    exact e

theorem tstC_nec {n w : Nat} (hwn : n < 2 ^ w) {g g' : Equiv.Perm (Fin n)} {bs : List Nat}
    {D : List (List (Nat × Nat × Nat))} (hok : trOKC w (mask w) (enc w (cfn g) n) bs D = true)
    (hbs : ∀ i, bs.getD i 0 < n) {l : Nat} {q x : Equiv.Perm (Fin n)}
    (hx : ∀ i ≤ l, x ⟨bs.getD i 0, hbs i⟩ = ⟨bs.getD i 0, hbs i⟩)
    (hl : q * x * g = g' * (q * x)) :
    tstC w (mask w) (enc w (cfn g') n) bs D l (enc w (cfn q) n) = true := by
  unfold tstC
  by_cases hlD : l < D.length
  · rw [List.all_eq_true]
    intro t ht
    unfold trOKC at hok
    rw [List.all_eq_true] at hok
    have h3 := List.all_eq_true.1 (hok l (List.mem_range.2 hlD)) t ht
    simp only [bAnd_eq, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h3
    obtain ⟨hi, hj, he⟩ := h3
    set bi : Fin n := ⟨bs.getD t.1 0, hbs _⟩
    set bj : Fin n := ⟨bs.getD t.2.2 0, hbs _⟩
    have hG : ∀ (σ : Equiv.Perm (Fin n)) (k : Nat) (z : Fin n),
        MEnum.itr (fun z => pg w (mask w) (enc w (cfn σ) n) z) k z = ((σ ^ k) z : Nat) := by
      intro σ k z
      rw [(itr_congr (fun y hy => pg_encode hwn (fun _ hx => cfn_lt σ hx) hy)
        (fun y hy => by rw [pg_encode hwn (fun _ hx => cfn_lt σ hx) hy]; exact cfn_lt σ hy)
        k z.isLt).1, itr_cfn]
    have he' : (g ^ t.2.1) bi = bj := Fin.ext ((hG g t.2.1 bi).symm.trans he)
    have hs : SemiconjBy (q * x) g g' := hl
    have hc := congrArg (fun τ : Equiv.Perm (Fin n) => τ bi) (hs.pow_right t.2.1)
    have hxi : x bi = bi := hx _ hi
    have hxj : x bj = bj := hx _ hj
    simp only [Equiv.Perm.mul_apply, he', hxi, hxj] at hc
    rw [Nat.beq_eq, pg_cfn hwn q bi, pg_cfn hwn q bj, hG g' t.2.1 (q bi), ← hc]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem cSrch_card {n w NL N : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    {F : Nat → Nat → Nat} {bs : List Nat} (hbs : ∀ i, bs.getD i 0 < n)
    (hF : ∀ i, ∀ l ∈ lvAt F NL bs i, IsPermN n (F l)) (V : Nat → Nat)
    {K : Subgroup (Equiv.Perm (Fin n))} {E : List (Equiv.Perm (Fin n))} (hnd : E.Nodup)
    (hmem : ∀ σ, σ ∈ E ↔ σ ∈ K)
    (hperm : E.Perm (products ((List.range N).map fun i =>
      (List.range (mbS n F NL bs i).pts.length).map (tau n F (mbS n F NL bs) i))))
    (g g' : Equiv.Perm (Fin n)) {D : List (List (Nat × Nat × Nat))}
    (hok : trOKC w (mask w) (enc w (cfn g) n) bs D = true) :
    cSrch n w (mask w) (n * w) (mask (n * w)) (tstC w (mask w) (enc w (cfn g') n) bs D)
        (leafC n w (mask w) (enc w (cfn g) n) (enc w (cfn g') n)) 0
        ((List.range N).map fun i => recBS n w F (mbS n F NL bs i) (V i)) (pidn n w) =
      Nat.card {h : K // (h : Equiv.Perm (Fin n)) * g = g' * h} := by
  have hwn : n < 2 ^ w := by omega
  have hg : ∀ i, GoodBS n F (mbS n F NL bs i) := fun i => goodBS_run (hbs i) (hF i)
  have hid : pidn n w = enc w (cfn (1 : Equiv.Perm (Fin n))) n := by
    rw [pidn_eq (by omega) (by omega)]
    exact enc_congr fun x hx => by simp [cfn, hx]
  rw [hid, cSrch_eq hn16 hw hg _ _ (List.range N) 0 1, prCnt_eq _ _ _ 0 1 ?_,
    ← hperm.countP_eq, card_subtype_eq_countP K E hnd hmem fun σ => σ * g = g' * σ]
  · exact List.countP_congr fun σ _ => by rw [one_mul, leafC_iff hwn, decide_eq_true_iff]
  · intro k hk q x hx hl
    rw [leafC_iff hwn] at hl
    rw [Nat.zero_add]
    refine tstC_nec hwn hok hbs (fun i hi => ?_) hl
    refine prods_fix _ _ (fun T hT t ht => ?_) x hx
    rw [← List.map_drop, List.mem_map] at hT
    obtain ⟨i', hi', rfl⟩ := hT
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
    have e : ((List.range N).drop (k + 1))[m] = k + 1 + m := by
      rw [List.getElem_drop, List.getElem_range]
    exact tauM_fix (hF _) (hbs _) (List.mem_range.1 hj) (by omega) (hbs i)

theorem cntCM_eq {n w NW : Nat} {tA tB : List Nat} {W : List (List Int)} {bs : List Nat}
    (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l < NW + NW, IsPermN n (mbF n w tA tB W l)) (hbsl : ∀ b ∈ bs, b < n)
    (G G' : Nat) (D : List (List (Nat × Nat × Nat))) :
    cntCM n w bs NW tA tB W G G' D =
      cSrch n w (mask w) (n * w) (mask (n * w)) (tstC w (mask w) G' bs D)
        (leafC n w (mask w) G G') 0 ((List.range bs.length).map fun i =>
          recBS n w (mbF n w tA tB W) (mbS n (mbF n w tA tB W) (NW + NW) bs i)
            (levMaskAt n w (MEnum.mLT n w tA tB W) (NW + NW) bs i)) (pidn n w) := by
  unfold cntCM
  simp only [strictN_eq, Nat.mul_eq, Nat.add_eq]
  rw [levN_eq hn16 hw hL hbsl, levPairs_eq, List.map_map]
  rfl

end CFSG.KS.MCent

end
