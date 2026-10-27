module

public import CFSG.Certificates.Kernel.MaxD2.Max
public import CFSG.LocalAnalysis.StandardType.TitsOvergroupCheck

public section

namespace CFSG.KS.TitsOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.KS.MaxD2 Certificates.MaxD2Perm

structure HypsC (K : Pk) (pts : List Nat) (nOrder gOrder : Nat) : Prop where
  hn : szOK K.n K.w = true
  hNt : ∀ i < K.cnt, Cn K.n K.w (K.NT i)
  hNL : ∀ i < K.cnt, LPerm K.n K.w K.L (K.NT i)
  hNc : K.cnt = nOrder
  hR0 : K.REP 0 = pidn K.n K.w
  hRi : ∀ i < K.nr, permOK K.n K.w (mask K.w) (K.n * K.w) (K.REP i) (K.REPI i) = true
  hPts : PtsOK K.n K.np pts K.PT
  hS : ∀ s < K.cnt, sortK K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS s = true
  hTest : ∀ i, 0 < i → i < K.nr →
    repK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB K.H i = true
  hCnt : ∀ i, 0 < i → i < K.nr → posCnt K.cnt K.H i = K.CN i
  hSum : (List.range K.nr).foldl
    (fun s i => s + nOrder * nOrder / (if i = 0 then K.cnt else K.CN i)) 0 = gOrder
  hM : K.n ≤ 64 * K.hi
  hMK : ∀ i < K.nr, K.MK i = mkeyK K.n K.w K.hi K.cw K.nl K.L (K.REP i)
  hMd : ∀ i < K.nr, ∀ j < K.nr, i < j → K.MK i ≠ K.MK j ∨
    pairK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB2 K.H2 (K.PQ i j) i j =
      true

@[expose] def RepB (n w m : Nat) (P : Nat → Nat) (A : Array Tab) : Prop :=
  A.size = m ∧ ∀ i < m, A[i]! = unpack n w (P i)

theorem lperm_of_tree {n w k cnt : Nat} {G GN T L : Nat → Nat} {par lab : Nat → Nat}
    (hn : szOK n w = true) (hT0 : T 0 = pidn n w)
    (htree : ∀ i < cnt, i ≠ 0 → par i < i ∧ lab i < k ∧ T i = pcomp n w (mask w) (G (lab i)) (T (par i)))
    (hG : ∀ j < k, permOK n w (mask w) (n * w) (G j) (GN j) = true)
    (hL : labK n w k G L = true) : ∀ i < cnt, LPerm n w L (T i) := by
  have hGL : ∀ j < k, LPerm n w L (G j) := fun j hj => by
    have hs := perm_spec (hG j hj)
    refine ⟨fun x hx => (hs.1 x hx).1, fun x hx y hy e => ?_, fun x hx => ?_⟩
    · rw [← (hs.1 x hx).2, ← (hs.1 y hy).2, e]
    · unfold labK at hL
      have := (PK.allN_iff.1 hL) j hj
      rw [PK.strictB_eq] at this
      exact Nat.eq_of_beq_eq_true ((PK.allN_iff.1 this) x hx)
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      rw [hT0]
      refine ⟨fun x hx => by rw [pidn_get hn hx]; exact hx, fun x hx y hy e => ?_,
        fun x hx => by rw [pidn_get hn hx]⟩
      rwa [pidn_get hn hx, pidn_get hn hy] at e
    · obtain ⟨h1, h2, h3⟩ := htree i hi h0
      rw [h3]
      exact lperm_pc hn (hGL _ h2) (ih _ h1 (by omega))

section

variable {K : Pk} {pts : List Nat} {nOrder gOrder : Nat}

theorem rec_getC {i : Nat} (hi : i < K.cnt) :
    (penumRec K.n K.w K.cnt K.NT K.NPL).tabs[i]! = unpack K.n K.w (K.NT i) := rec_get hi

theorem rec_sizeC : (penumRec K.n K.w K.cnt K.NT K.NPL).tabs.size = K.cnt := rec_size _ _ _ _ _

theorem fp_injC (H : HypsC K pts nOrder gOrder) :
    ∀ a < (penumRec K.n K.w K.cnt K.NT K.NPL).tabs.size,
      ∀ b < (penumRec K.n K.w K.cnt K.NT K.NPL).tabs.size,
      fpTab pts (penumRec K.n K.w K.cnt K.NT K.NPL).tabs[a]! =
        fpTab pts (penumRec K.n K.w K.cnt K.NT K.NPL).tabs[b]! → a = b := by
  intro a ha b hb e
  rw [rec_sizeC] at ha hb
  rw [rec_getC ha, rec_getC hb] at e
  exact sort_keyInj H.hS ha hb (fpK_of_fpTab H.hPts e)

theorem memN_iffC (H : HypsC K pts nOrder gOrder) {X : Nat} (hX : Cn K.n K.w X) :
    memFp pts (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
      ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
      (penumRec K.n K.w K.cnt K.NT K.NPL).tabs (unpack K.n K.w X) = true ↔
      ∃ e < K.cnt, K.NT e = X := by
  rw [memFp_iff (fp_injC H), rec_sizeC]
  constructor
  · rintro ⟨m, hm, e⟩
    rw [rec_getC hm] at e
    exact ⟨m, hm, u_inj (H.hNt m hm) hX e⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rec_getC hm⟩

theorem conjCount_eqC (H : HypsC K pts nOrder gOrder) {rep repi : Array Tab}
    (hr : RepB K.n K.w K.nr K.REP rep) (hri : RepB K.n K.w K.nr K.REPI repi) {i : Nat}
    (hi : i < K.nr) :
    conjCount K.n pts (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
      ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
      (penumRec K.n K.w K.cnt K.NT K.NPL).tabs repi[i]! rep[i]! =
      if i = 0 then K.cnt else K.CN i := by
  have hn := H.hn
  have hr' := perm_canon (H.hRi i hi) hn
  unfold conjCount
  rw [hri.2 i hi, hr.2 i hi, rec_sizeC]
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl]
    refine (countBelow_eq (g := fun _ => true) fun k hk => ?_).trans (countBelow_true K.cnt)
    have hq := perm_spec (H.hRi 0 hi)
    rw [H.hR0] at hq
    have hqid : ∀ j < K.n, pg K.w (mask K.w) (K.REPI 0) j = j := fun j hj => by
      have := (hq.1 j hj).2
      rwa [pidn_get hn hj] at this
    have e : comp K.n (comp K.n (unpack K.n K.w (K.REPI 0))
        (penumRec K.n K.w K.cnt K.NT K.NPL).tabs[k]!) (unpack K.n K.w (K.REP 0)) =
        unpack K.n K.w (K.NT k) := by
      rw [rec_getC hk]
      refine tab_ext (comp_size _ _) (size_u _) fun x hx => ?_
      rw [comp_get hx, H.hR0, get_u hx, pidn_get hn hx, comp_get hx, get_u hx,
        get_u (canon_lt (H.hNt k hk) hx), hqid _ (canon_lt (H.hNt k hk) hx)]
    rw [e, memN_iffC H (H.hNt k hk)]
    exact ⟨k, hk, rfl⟩
  · rw [if_neg h0, ← H.hCnt i (Nat.pos_of_ne_zero h0) hi]
    unfold posCnt
    rw [PK.foldN_eq, foldr_count]
    refine countBelow_eq fun k hk => ?_
    have ht := H.hTest i (Nat.pos_of_ne_zero h0) hi
    unfold repK at ht
    simp only [PK.strictB_eq] at ht
    obtain ⟨hrb, hts⟩ := band_e ht
    have hk' := (PK.allN_iff.1 hts) k hk
    have hspec := testK_spec hn (fun e he => H.hNt e he) H.hS (fun t ht => (H.hPts.2 t ht).2)
      (H.hRi i hi) (fun t ht => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 hrb) t ht)) hk hk'
    have ha := H.hNt k hk
    rw [rec_getC hk, comp_u hr'.2 ha, comp_u (cc hr'.2 ha) hr'.1, Bool.eq_iff_iff,
      memN_iffC H (cc (cc hr'.2 ha) hr'.1), hspec, beq_iff_eq]

theorem dcSum_ofC (H : HypsC K pts nOrder gOrder) {rep repi : Array Tab}
    (hr : RepB K.n K.w K.nr K.REP rep) (hri : RepB K.n K.w K.nr K.REPI repi) :
    dcSum K.n nOrder pts (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
      ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
      (penumRec K.n K.w K.cnt K.NT K.NPL).tabs rep repi = gOrder := by
  unfold dcSum
  rw [← H.hSum, hr.1]
  refine foldl_congr_range (fun s i hi => ?_) 0
  rw [conjCount_eqC H hr hri hi]

theorem dcDisjoint_ofC (H : HypsC K pts nOrder gOrder) {rep repi : Array Tab}
    (hr : RepB K.n K.w K.nr K.REP rep) (hri : RepB K.n K.w K.nr K.REPI repi) :
    dcDisjoint K.n pts (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
      ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
      (penumRec K.n K.w K.cnt K.NT K.NPL).tabs rep repi = true := by
  have hn := H.hn
  unfold dcDisjoint
  rw [allBelow_iff']
  intro i hi
  rw [allBelow_iff']
  intro j hj
  rw [hr.1] at hi hj
  rw [Bool.or_eq_true]
  by_cases hij : i < j
  · right
    rw [allBelow_iff']
    intro k hk
    rw [rec_sizeC] at hk
    have hri' := perm_canon (H.hRi i hi) hn
    have hrj := perm_canon (H.hRi j hj) hn
    have ha := H.hNt k hk
    rw [hri.2 i hi, hr.2 j hj, rec_getC hk, comp_u hri'.2 ha, comp_u (cc hri'.2 ha) hrj.1,
      Bool.not_eq_true', Bool.eq_false_iff]
    intro hm
    obtain ⟨m, hm', em⟩ := (memN_iffC H (cc (cc hri'.2 ha) hrj.1)).1 hm
    have hj' := perm_spec (H.hRi j hj)
    rcases H.hMd i hi j hj hij with hd | hp
    · have key := mkey_eq hn (hi := K.hi) (cw := K.cw) (nl := K.nl) H.hM (H.hRi i hi)
        (fun y hy => (hj'.1 y hy).1) (H.hNL k hk) (H.hNL m hm') (fun y hy => by
          rw [em, pg_pc hn hy, pg_pc hn ((hj'.1 y hy).1)])
      rw [← H.hMK j hj, ← H.hMK i hi] at key
      exact hd key.symm
    · exact pairK_spec hn (fun e he => H.hNt e he) H.hS (fun t ht => (H.hPts.2 t ht).2)
        (fun y hy => (hj'.1 y hy).1) hk hp ⟨m, hm', em⟩
  · left
    simpa using hij

theorem invsOK_ofC (H : HypsC K pts nOrder gOrder) {rep repi : Array Tab}
    (hr : RepB K.n K.w K.nr K.REP rep) (hri : RepB K.n K.w K.nr K.REPI repi) :
    invsOK K.n rep repi = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [hri.1, hr.1], allBelow_iff'.2 fun k hk => ?_⟩
  rw [hr.1] at hk
  rw [hri.2 k hk, hr.2 k hk, inv_comp (H.hRi k hk)]
  simp [size_u]

theorem fp3_eqC {n : Nat} {pts : List Nat} (hpts : ∀ x ∈ pts, x < n) {a b c : Tab}
    (hc : ∀ x < n, c[x]! < n) (hb : ∀ x < n, b[x]! < n) :
    CFSG.StandardType.TitsOvergroup.fp3 pts a b c = fpTab pts (comp n (comp n a b) c) := by
  unfold CFSG.StandardType.TitsOvergroup.fp3 fpTab
  apply congrArg List.toArray
  apply List.map_congr_left
  intro x hx
  have hx' : x < n := hpts x hx
  rw [comp_get hx', comp_get (hc x hx')]

theorem memFp3_eqC {n : Nat} {pts : List Nat} (hpts : ∀ x ∈ pts, x < n) {fpIdx : Std.HashMap Tab Nat}
    {fpT T : Array Tab} {a b c : Tab} (hc : ∀ x < n, c[x]! < n) (hb : ∀ x < n, b[x]! < n) :
    CFSG.StandardType.TitsOvergroup.memFp3 n pts fpIdx fpT T a b c =
      memFp pts fpIdx fpT T (comp n (comp n a b) c) := by
  unfold CFSG.StandardType.TitsOvergroup.memFp3 memFp
  rw [fp3_eqC hpts hc hb]

theorem unpack_lt {n w p : Nat} (hp : Cn n w p) : ∀ x < n, (unpack n w p)[x]! < n := by
  intro x hx
  rw [get_u hx]
  exact canon_lt hp hx

theorem checkCover_ofC (H : HypsC K pts nOrder gOrder) {rep repi : Array Tab}
    (hr : RepB K.n K.w K.nr K.REP rep) (hri : RepB K.n K.w K.nr K.REPI repi)
    (hpts : ∀ x ∈ pts, x < K.n) :
    (pts.all (· < K.n) && fpOK pts (penumRec K.n K.w K.cnt K.NT K.NPL).tabs &&
      invsOK K.n rep repi &&
      CFSG.StandardType.TitsOvergroup.dcSum3 K.n nOrder pts
        (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
        ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
        (penumRec K.n K.w K.cnt K.NT K.NPL).tabs rep repi == gOrder &&
      CFSG.StandardType.TitsOvergroup.dcDisjoint3 K.n pts
        (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
        ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
        (penumRec K.n K.w K.cnt K.NT K.NPL).tabs rep repi) = true := by
  have hn := H.hn
  have hNlt : ∀ k < (penumRec K.n K.w K.cnt K.NT K.NPL).tabs.size,
      ∀ x < K.n, ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs[k]!)[x]! < K.n := by
    intro k hk
    rw [rec_sizeC] at hk
    rw [rec_getC hk]
    exact unpack_lt (H.hNt k hk)
  have hRlt : ∀ i < K.nr, ∀ x < K.n, (rep[i]!)[x]! < K.n := fun i hi => by
    rw [hr.2 i hi]
    exact unpack_lt (perm_canon (H.hRi i hi) hn).1
  have hsum : CFSG.StandardType.TitsOvergroup.dcSum3 K.n nOrder pts
      (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
      ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
      (penumRec K.n K.w K.cnt K.NT K.NPL).tabs rep repi =
      dcSum K.n nOrder pts (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
        ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
        (penumRec K.n K.w K.cnt K.NT K.NPL).tabs rep repi := by
    unfold CFSG.StandardType.TitsOvergroup.dcSum3 dcSum
    rw [hr.1]
    refine foldl_congr_range (fun s i hi => ?_) 0
    unfold CFSG.StandardType.TitsOvergroup.conjCount3 conjCount
    rw [countBelow_eq fun k hk => memFp3_eqC hpts (hRlt i hi) (hNlt k hk)]
  have hdis : CFSG.StandardType.TitsOvergroup.dcDisjoint3 K.n pts
      (indexOf ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts)))
      ((penumRec K.n K.w K.cnt K.NT K.NPL).tabs.map (fpTab pts))
      (penumRec K.n K.w K.cnt K.NT K.NPL).tabs rep repi = true := by
    have hD := dcDisjoint_ofC H hr hri
    unfold dcDisjoint at hD
    unfold CFSG.StandardType.TitsOvergroup.dcDisjoint3
    dsimp only at hD ⊢
    rw [allBelow_iff'] at hD ⊢
    intro i hi
    have hDi := hD i hi
    rw [allBelow_iff'] at hDi ⊢
    intro j hj
    have hDij := hDi j hj
    rw [Bool.or_eq_true] at hDij ⊢
    rcases hDij with h | h
    · exact Or.inl h
    · right
      rw [allBelow_iff'] at h ⊢
      intro k hk
      have hj' : j < K.nr := by rw [← hr.1]; exact hj
      rw [memFp3_eqC hpts (hRlt j hj') (hNlt k hk)]
      exact h k hk
  rw [hsum, hdis, dcSum_ofC H hr hri, invsOK_ofC H hr hri, fpOK_of (fp_injC H)]
  simp only [List.all_eq_true, decide_eq_true_eq, beq_self_eq_true, Bool.and_true]
  exact hpts

end

end CFSG.KS.TitsOver

end
