module

public import Certificates.Data.Kernel.HeLoc.PTail
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import CFSG.RankThree.PartOne.KS.PKit
import CFSG.Certificates.Kernel.SporSch.TabChainLv
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.KC.HeLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne

private theorem bsK_succ (KE SK : Nat → Nat) (key f lo hi : Nat) :
    bsK KE SK key (f + 1) lo hi =
      bIf(Nat.blt lo hi,
        strictB (Nat.div (Nat.add lo hi) 2) (fun mid => strictB (KE (SK mid)) (fun v =>
          bIf(Nat.beq v key, true, bIf(Nat.blt v key, bsK KE SK key f (Nat.succ mid) hi,
            bsK KE SK key f lo mid)))), false) := rfl

private theorem bIf_true_of {t e : Bool} {c : Bool} (hc : c = true)
    (h : Bool.rec (motive := fun _ => Bool) e t c = true) : t = true := by
  subst hc
  exact h

private theorem bIf_false_of {t e : Bool} {c : Bool} (hc : c = false)
    (h : Bool.rec (motive := fun _ => Bool) e t c = true) : e = true := by
  subst hc
  exact h

private theorem bsK_sound (KE SK : Nat → Nat) (key : Nat) :
    ∀ f lo hi, bsK KE SK key f lo hi = true → ∃ j, lo ≤ j ∧ j < hi ∧ KE (SK j) = key := by
  intro f
  induction f with
  | zero => intro lo hi h; exact absurd h (by simp [bsK])
  | succ f ih =>
    intro lo hi h
    rw [bsK_succ] at h
    cases hlt : Nat.blt lo hi
    · exact absurd (bIf_false_of hlt h) (by simp)
    · have hlh : lo < hi := Nat.blt_eq.mp hlt
      have h1 := bIf_true_of hlt h
      simp only [Orb.strictB_eq] at h1
      have hm1 : lo ≤ Nat.div (Nat.add lo hi) 2 := by show lo ≤ (lo + hi) / 2; omega
      have hm2 : Nat.div (Nat.add lo hi) 2 < hi := by show (lo + hi) / 2 < hi; omega
      generalize Nat.div (Nat.add lo hi) 2 = mid at h1 hm1 hm2
      cases hbe : Nat.beq (KE (SK mid)) key
      · cases hbl : Nat.blt (KE (SK mid)) key
        · have h2 := bIf_false_of hbl (bIf_false_of hbe h1)
          obtain ⟨j, hj1, hj2, hj3⟩ := ih lo mid h2
          exact ⟨j, hj1, by omega, hj3⟩
        · have h2 := bIf_true_of hbl (bIf_false_of hbe h1)
          obtain ⟨j, hj1, hj2, hj3⟩ := ih (Nat.succ mid) hi h2
          exact ⟨j, by omega, hj2, hj3⟩
      · exact ⟨mid, hm1, hm2, Nat.eq_of_beq_eq_true hbe⟩


private theorem exists_bound (ps : List Nat) : ∃ N, ∀ q ∈ ps, q < N := by
  induction ps with
  | nil => exact ⟨0, nofun⟩
  | cons p ps ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨max (p + 1) N, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (hN q hq) (le_max_right _ _)

private theorem keyV_eq' (n : Nat) (ps : List Nat) (h : Nat → Nat) :
    keyV n ps h = Nat.ofDigits n (ps.map h) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change h p + n * keyV n ps h = _
    rw [ih, List.map_cons, Nat.ofDigits_cons]

private theorem eqA_congr_left {n : Nat} {a b : Array Nat} (h : ∀ i < n, a[i]! = b[i]!)
    (e : Array Nat) : eqA n a e = eqA n b e := by
  rw [Bool.eq_iff_iff]
  unfold eqA
  rw [allLt_iff, allLt_iff]
  exact forall₂_congr fun i hi => by rw [h i hi]

private theorem relK_of_forall {rels : List (Nat × Nat × Nat)} {xm img : Nat → Nat} {i : Nat}
    (h : ∀ r ∈ rels, max r.1 r.2.1 = i → img r.2.1 = powF xm r.2.2 (img r.1)) :
    relK rels xm img i = true := by
  induction rels with
  | nil => rfl
  | cons r rels ih =>
    have ih' := ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    have e : relK (r :: rels) xm img i = bAnd(bIf(Nat.beq (Nat.max r.1 r.2.1) i,
        Nat.beq (img r.2.1) (powF xm r.2.2 (img r.1)), true), relK rels xm img i) := rfl
    rw [e, ih']
    cases hm : Nat.beq (Nat.max r.1 r.2.1) i
    · rfl
    · have hd : Nat.beq (img r.2.1) (powF xm r.2.2 (img r.1)) = true := by
        rw [h r List.mem_cons_self (Nat.eq_of_beq_eq_true hm)]
        exact Nat.beq_refl _
      rw [hd]

section Levels

variable {n w kS nb BP NS CH : Nat} {PS PSI LR : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat}

private theorem step_facts (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) {i j : Nat}
    (hj : j < (rawSteps n S base i).size) :
    Orb.stp n S base i j ∈ Subgroup.closure (Set.range fun j : Fin kS => permOfArr n S[j.val]!) ∧
      ∀ m < i, ∀ (hm : base[m]! < n),
        Orb.stp n S base i j ⟨base[m]!, hm⟩ = ⟨base[m]!, hm⟩ := by
  have hmem : (rawSteps n S base i)[j]! ∈ levelSteps S (rawInvs n S) base i := by
    rw [getElem!_pos _ j hj]
    exact Array.getElem_mem hj
  have hS : S.size = kS := hb.2.2.2.1
  have hidx : ∀ j' ∈ levelIdx S base i, j' < S.size ∧ ∀ m < i, (S[j']!)[base[m]!]! = base[m]! := by
    intro j' hj'
    rw [levelIdx, List.mem_filter, List.mem_range, fixesFirst, allLt_iff] at hj'
    exact ⟨hj'.1, fun m hm => beq_iff_eq.1 (hj'.2 m hm)⟩
  have hrepS := Orb.rep_S_of hb hp
  have hrepI := Orb.rep_Si_of hb hp
  unfold levelSteps at hmem
  rw [Array.mem_append, List.mem_toArray, List.mem_toArray, List.mem_map, List.mem_map] at hmem
  unfold Orb.stp
  rcases hmem with ⟨j', hj', hjj⟩ | ⟨j', hj', hjj⟩
  · obtain ⟨hj'lt, hfix⟩ := hidx j' hj'
    rw [← hjj]
    refine ⟨Subgroup.subset_closure ⟨⟨j', by rwa [← hS]⟩, rfl⟩, fun m hm hbm => ?_⟩
    apply Fin.ext
    show (permOfArr n S[j']! ⟨base[m]!, hbm⟩ : Nat) = base[m]!
    rw [← (hrepS j' hj'lt) ⟨base[m]!, hbm⟩]
    exact hfix m hm
  · obtain ⟨hj'lt, hfix⟩ := hidx j' hj'
    rw [← hjj, permOfArr_eq_of_rep (hrepI j' hj'lt)]
    refine ⟨Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨j', by rwa [← hS]⟩, rfl⟩),
      fun m hm hbm => ?_⟩
    have hgb : permOfArr n S[j']! ⟨base[m]!, hbm⟩ = ⟨base[m]!, hbm⟩ :=
      Fin.ext (by rw [← (hrepS j' hj'lt) ⟨base[m]!, hbm⟩]; exact hfix m hm)
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hgb.symm

private theorem trT_facts (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH) {i k : Nat} (hi : i < nb)
    (hk : k < rcnt (LR i)) :
    Tab.trT n w LR S base i k ∈
        Subgroup.closure (Set.range fun j : Fin kS => permOfArr n S[j.val]!) ∧
      ∀ m < i, ∀ (hm : base[m]! < n),
        Tab.trT n w LR S base i k ⟨base[m]!, hm⟩ = ⟨base[m]!, hm⟩ := by
  obtain ⟨hpl, -⟩ := Tab.agree hb hp ho hN hi
  suffices H : ∀ f k, k < rcnt (LR i) →
      Orb.treeF (Orb.stp n S base i) (rpar w (mask w) (n * w) (LR i))
        (rlab n (n * w) (LR i)) f k ∈
          Subgroup.closure (Set.range fun j : Fin kS => permOfArr n S[j.val]!) ∧
      ∀ m < i, ∀ (hm : base[m]! < n),
        Orb.treeF (Orb.stp n S base i) (rpar w (mask w) (n * w) (LR i))
          (rlab n (n * w) (LR i)) f k ⟨base[m]!, hm⟩ = ⟨base[m]!, hm⟩ from H k k hk
  intro f
  induction f with
  | zero =>
    intro k _
    refine ⟨?_, fun m _ hm => ?_⟩
    · simp only [Orb.treeF]
      exact Subgroup.one_mem _
    · simp only [Orb.treeF]
      rfl
  | succ f ih =>
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [Orb.treeF_zero]
      exact ⟨Subgroup.one_mem _, fun m _ hm => rfl⟩
    · obtain ⟨hpk, hlk⟩ := hpl k hk (Nat.pos_of_ne_zero hk0)
      obtain ⟨h1, h2⟩ := step_facts hb hp (i := i) hlk
      obtain ⟨h3, h4⟩ := ih _ (lt_trans hpk hk)
      simp only [Orb.treeF, hk0, ↓reduceIte]
      refine ⟨Subgroup.mul_mem _ h1 h3, fun m hm hbm => ?_⟩
      rw [Equiv.Perm.mul_apply, h4 m hm hbm]
      exact h2 m hm hbm

end Levels

private theorem imgExt_lt {img : Nat → Nat} {i p m : Nat} (h : m < i) :
    imgExt img i p m = img m := by
  unfold imgExt
  rw [blt_true h]

private theorem imgExt_ge {img : Nat → Nat} {i p m : Nat} (h : i ≤ m) :
    imgExt img i p m = p := by
  unfold imgExt
  rw [blt_false (not_lt.2 h)]

private theorem ptK_succ (n w kS NR NL : Nat) (LT PT QT LR FR : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (xm : Nat → Nat) (cb ps : List Nat) (KE SK : Nat → Nat)
    (NE f i : Nat) (acc accI img : Nat → Nat) :
    ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE (f + 1) i acc accI img =
      strictB (rcnt (LR i)) fun c =>
      strictB (FR i) fun fr =>
        bIf(Nat.beq fr 0,
          allN c fun k => strictB (acc (rpt w (mask w) (LR i) k)) fun p =>
            bIf(relK rels xm (imgExt img i p) i,
              ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE f (Nat.succ i)
                (fun y => acc (trPtT w NR NL LT PT i k y))
                (fun y => trInvPtT w kS NR NL LT PT i k (accI y)) (imgExt img i p), true),
          strictB (accI (powF xm (Nat.mod (Nat.sub fr 1) 8) (img (Nat.div (Nat.sub fr 1) 8))))
            fun q => strictB (lvT NL w QT i q) fun k =>
            bIf(Nat.blt k c, strictB (acc (rpt w (mask w) (LR i) k)) fun p =>
              bIf(relK rels xm (imgExt img i p) i,
                ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE f (Nat.succ i)
                  (fun y => acc (trPtT w NR NL LT PT i k y))
                  (fun y => trInvPtT w kS NR NL LT PT i k (accI y)) (imgExt img i p), true),
              true)) := rfl

section Sound

variable {n w kS nb BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT FR : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}

private theorem ptK_sound_aux (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
    (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ)
    {x : Array Nat} {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {xm : Nat → Nat}
    (hxm : RepF n xm X) {p : Nat} {rels : List (Nat × Nat × Nat)}
    (hrels : ∀ r ∈ rels, r.2.2 < p)
    (hFR : ∀ i < nb, FR i = 0 ∨ ∃ l e, FR i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧ (l, i, e) ∈ rels)
    {E : List (Array Nat)} {cb ps : List Nat} (hcb : ∀ b ∈ cb, b < n) {KE SK : Nat → Nat}
    {NE : Nat}
    (hE : ∀ (a : Array Nat) (A : Equiv.Perm (Fin n)), Rep n a A →
      A ∈ Subgroup.closure (Set.range fun j : Fin kS => permOfArr n S[j.val]!) →
      (∃ j < NE, keyA n ps a = KE (SK j)) → E.any (eqA n a) = true) :
    ∀ f i, i + f = nb → ∀ (acc accI img : Nat → Nat) (accArr : Array Nat) (A : Equiv.Perm (Fin n)),
      RepF n acc A → RepF n accI A⁻¹ → Rep n accArr A →
      A ∈ Subgroup.closure (Set.range fun j : Fin kS => permOfArr n S[j.val]!) →
      (∀ m < i, img m = accArr[base[m]!]!) →
      ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE f i acc accI img = true →
      ptailOK n (rawLevels n S base) base x (powPA p n x) rels E f i accArr = true := by
  have hbl := Tab.base_lt hb ho hN
  intro f
  induction f with
  | zero =>
    intro i _ acc _ _ accArr A hacc _ harr hAmem _ h
    change Bool.rec true (bsK KE SK (keyV n ps acc) 20 0 NE)
      (eqOnL cb (fun y => acc (xm y)) (fun y => xm (acc y))) = true at h
    change (!(commA n accArr x) || E.any (eqA n accArr)) = true
    cases hc : eqOnL cb (fun y => acc (xm y)) (fun y => xm (acc y))
    ·
      have hne : ¬ ∀ b ∈ cb, acc (xm b) = xm (acc b) := fun hall =>
        absurd ((eqOnL_iff cb _ _).2 hall) (by rw [hc]; exact Bool.false_ne_true)
      obtain ⟨y, hyne'⟩ := not_forall.1 hne
      obtain ⟨hy, hyne⟩ := not_imp.1 hyne'
      have hyn : y < n := hcb y hy
      have hcomm : commA n accArr x = false := by
        cases hcA : commA n accArr x
        · rfl
        · exfalso
          have hAX : A * X = X * A := (commA_iff harr hx).1 hcA
          have e1 := (hacc.comp hxm) y hyn
          have e2 := (hxm.comp hacc) y hyn
          rw [hAX] at e1
          exact hyne (e1.trans e2.symm)
      rw [hcomm]
      rfl
    ·
      have h2 := bIf_true_of hc h
      obtain ⟨j, -, hjNE, hjkey⟩ := bsK_sound KE SK (keyV n ps acc) 20 0 NE h2
      obtain ⟨N, hNb⟩ := exists_bound ps
      have hga : ∀ q < n + N, (Array.ofFn (n := n + N) fun z => acc z.val)[q]! = acc q :=
        fun q hq => getElem!_ofFn_nat _ hq
      have hrep : Rep n (Array.ofFn (n := n + N) fun z => acc z.val) A := fun z => by
        rw [hga z (by have := z.2; omega)]
        exact hacc z z.2
      have hkey : keyA n ps (Array.ofFn (n := n + N) fun z => acc z.val) = KE (SK j) := by
        rw [hjkey, keyV_eq', keyA]
        congr 1
        exact List.map_congr_left fun q hq => hga q (by have := hNb q hq; omega)
      have hEa := hE _ A hrep hAmem ⟨j, hjNE, hkey⟩
      have hacceq : ∀ z < n, (Array.ofFn (n := n + N) fun z => acc z.val)[z]! = accArr[z]! :=
        fun z hz => by
          rw [hga z (by omega), hacc z hz]
          exact (harr ⟨z, hz⟩).symm
      rw [List.any_eq_true] at hEa
      obtain ⟨e, he, hee⟩ := hEa
      rw [eqA_congr_left hacceq e] at hee
      rw [Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.2 ⟨e, he, hee⟩)
  | succ f ih =>
    intro i hif acc accI img accArr A hacc haccI harr hAmem himg h
    have hi : i < nb := by omega
    obtain ⟨-, hAg0⟩ := Tab.agree hb hp ho hN hi
    have hAg : Orb.Agree n w (LR i) ((rawLevels n S base)[i]!) (Tab.trT n w LR S base i) := hAg0
    have hRF := Tab.recFacts ho hN hi
    have hacc_arr : ∀ y < n, acc y = accArr[y]! := fun y hy => by
      rw [hacc y hy]
      exact (harr ⟨y, hy⟩).symm
    have hcnt : rcnt (LR i) = ((rawLevels n S base)[i]!).pts.size := hAg.cnt
    have key : ∀ k (hk : k < ((rawLevels n S base)[i]!).pts.size),
        relOK base (powPA p n x) rels i accArr ((rawLevels n S base)[i]!).pts[k]! = true →
        (relK rels xm (imgExt img i (acc (rpt w (mask w) (LR i) k))) i = true →
          ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE f (i + 1)
            (fun y => acc (trPtT w NR NL LT PT i k y))
            (fun y => trInvPtT w kS NR NL LT PT i k (accI y))
            (imgExt img i (acc (rpt w (mask w) (LR i) k))) = true) →
        ptailOK n (rawLevels n S base) base x (powPA p n x) rels E f (i + 1)
          (compA n accArr ((rawLevels n S base)[i]!).tr[k]!) = true := by
      intro k hk hrel hker
      have hkc : k < rcnt (LR i) := hcnt ▸ hk
      have hqpt : rpt w (mask w) (LR i) k = ((rawLevels n S base)[i]!).pts[k]! := hAg.pt k hk
      have hqn : ((rawLevels n S base)[i]!).pts[k]! < n := hqpt ▸ (hRF.pt k hkc).1
      have hTP : RepF n (fun y => trPtT w NR NL LT PT i k y) (Tab.trT n w LR S base i k) :=
        fun y hy => Tab.trPtT_eq hb hp ho hN ht hi hkc ⟨y, hy⟩
      have hTI : RepF n (fun y => trInvPtT w kS NR NL LT PT i k y)
          (Tab.trT n w LR S base i k)⁻¹ :=
        fun y hy => Tab.trInvPtT_eq hb hp ho hN ht hi hkc ⟨y, hy⟩
      have hacc' : RepF n (fun y => acc (trPtT w NR NL LT PT i k y))
          (A * Tab.trT n w LR S base i k) := hacc.comp hTP
      have haccI' : RepF n (fun y => trInvPtT w kS NR NL LT PT i k (accI y))
          (A * Tab.trT n w LR S base i k)⁻¹ := (hTI.comp haccI).congr (mul_inv_rev A _).symm
      have harr' : Rep n (compA n accArr ((rawLevels n S base)[i]!).tr[k]!)
          (A * Tab.trT n w LR S base i k) := rep_compA harr (hAg.tr k hk).1
      have hAmem' := Subgroup.mul_mem _ hAmem (trT_facts hb hp ho hN hi hkc).1
      have himg' : ∀ m < i + 1, imgExt img i (acc (rpt w (mask w) (LR i) k)) m =
          (compA n accArr ((rawLevels n S base)[i]!).tr[k]!)[base[m]!]! := by
        intro m hm
        have hbm := hbl m (by omega)
        rw [compA_get hbm, (hAg.tr k hk).1.apply hbm]
        rcases Nat.lt_or_ge m i with hmi | hmi
        · rw [imgExt_lt hmi, (trT_facts hb hp ho hN hi hkc).2 m hmi hbm]
          exact himg m hmi
        · obtain rfl : m = i := by omega
          rw [imgExt_ge le_rfl, ← Tab.rpt_eq hb hp ho hN hi hkc]
          exact hacc_arr _ (hRF.pt k hkc).1
      have hrelK : relK rels xm (imgExt img i (acc (rpt w (mask w) (LR i) k))) i = true := by
        set q := ((rawLevels n S base)[i]!).pts[k]! with hq
        have hpimg : ∀ m, imgExt img i (acc (rpt w (mask w) (LR i) k)) m =
            relImg base i accArr q m := by
          intro m
          unfold relImg
          rcases Nat.lt_or_ge m i with hmi | hmi
          · rw [imgExt_lt hmi, if_pos hmi]
            exact himg m hmi
          · rw [imgExt_ge hmi, if_neg (not_lt.2 hmi), hqpt]
            exact hacc_arr q hqn
        have hvn : ∀ m, m < nb → relImg base i accArr q m < n := by
          intro m hm
          unfold relImg
          split_ifs
          · exact harr.lt (hbl m hm)
          · exact harr.lt hqn
        refine relK_of_forall fun r hr hmax => ?_
        have hr1 := List.all_eq_true.1 hrel r hr
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hr1
        rcases hr1 with hne | heq
        · exact absurd hmax hne
        · rw [hpimg, hpimg]
          have hr1lt : r.1 < nb := by
            have := le_max_left r.1 r.2.1
            omega
          have hv := hvn r.1 hr1lt
          have he := hrels r hr
          have hsz : r.2.2 < (powPA p n x).size := by simpa [powPA] using he
          rw [heq, (rep_powPA hx r.2.2 hsz).apply hv]
          exact ((hxm.powF r.2.2) _ hv).symm
      exact ih (i + 1) (by omega) _ _ _ _ (A * Tab.trT n w LR S base i k) hacc' haccI' harr'
        hAmem' himg' (hker hrelK)
    rw [ptK_succ] at h
    simp only [Orb.strictB_eq] at h
    rw [ptailOK, allLt_iff]
    intro k hk
    by_cases hr : relOK base (powPA p n x) rels i accArr
        ((rawLevels n S base)[i]!).pts[k]! = true
    · rw [hr, Bool.not_true, Bool.false_or]
      refine key k hk hr ?_
      have hkc : k < rcnt (LR i) := hcnt ▸ hk
      rcases hFR i hi with hfr | ⟨l, e, hfr, hli, he8, hmem⟩
      ·
        have hbeq : Nat.beq (FR i) 0 = true := by rw [hfr]; rfl
        have h1 := bIf_true_of hbeq h
        have h2 := Orb.allN_iff.1 h1 k hkc
        intro hrk
        exact bIf_true_of hrk h2
      ·
        have hbeq : Nat.beq (FR i) 0 = false := by rw [hfr]; rfl
        have h1 := bIf_false_of hbeq h
        have e1 : Nat.mod (Nat.sub (FR i) 1) 8 = e := by
          rw [hfr]
          show (8 * l + e + 1 - 1) % 8 = e
          omega
        have e2 : Nat.div (Nat.sub (FR i) 1) 8 = l := by
          rw [hfr]
          show (8 * l + e + 1 - 1) / 8 = l
          omega
        rw [e1, e2] at h1
        have hqpt : rpt w (mask w) (LR i) k = ((rawLevels n S base)[i]!).pts[k]! := hAg.pt k hk
        have hqn : ((rawLevels n S base)[i]!).pts[k]! < n := hqpt ▸ (hRF.pt k hkc).1
        set q := ((rawLevels n S base)[i]!).pts[k]! with hq
        have hrel1 := List.all_eq_true.1 hr (l, i, e) hmem
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          beq_iff_eq] at hrel1
        rcases hrel1 with hne | heq
        · exact absurd (max_eq_right hli.le) hne
        · have hl1 : relImg base i accArr q l = accArr[base[l]!]! := by
            unfold relImg
            rw [if_pos hli]
          have hl2 : relImg base i accArr q i = accArr[q]! := by
            unfold relImg
            rw [if_neg (lt_irrefl i)]
          have hv : accArr[base[l]!]! < n := harr.lt (hbl l (by omega))
          have hep : e < p := hrels _ hmem
          have hsz : e < (powPA p n x).size := by simpa [powPA] using hep
          rw [hl1, hl2, (rep_powPA hx e hsz).apply hv] at heq
          have hAq : (A ⟨q, hqn⟩ : Nat) = ((X ^ e) ⟨accArr[base[l]!]!, hv⟩ : Nat) := by
            rw [← harr ⟨q, hqn⟩]
            exact heq
          have hpow : powF xm e (img l) = ((X ^ e) ⟨accArr[base[l]!]!, hv⟩ : Nat) := by
            rw [himg l hli]
            exact (hxm.powF e) _ hv
          have hY : accI (powF xm e (img l)) = q := by
            rw [hpow]
            have hlt : ((X ^ e) ⟨accArr[base[l]!]!, hv⟩ : Nat) < n := ((X ^ e) _).2
            have hz : A⁻¹ ((X ^ e) ⟨accArr[base[l]!]!, hv⟩) = ⟨q, hqn⟩ := by
              rw [Equiv.Perm.inv_eq_iff_eq]
              exact (Fin.ext hAq).symm
            rw [haccI _ hlt]
            simp only [Fin.eta]
            rw [hz]
          have hlv : lvT NL w QT i q = k := by
            rw [Tab.lvT_QT ht hi hqn]
            exact hqpt ▸ (hRF.pt k hkc).2
          rw [hY, hlv] at h1
          have h2 := bIf_true_of (blt_true hkc) h1
          intro hrk
          exact bIf_true_of hrk h2
    · have hr' : relOK base (powPA p n x) rels i accArr ((rawLevels n S base)[i]!).pts[k]! =
          false := by simpa using hr
      rw [hr']
      rfl

end Sound


theorem ptailOK_of_ptK_ {n w kS nb BP NS CH NR NL NT BT NQ BQ : Nat}
    {PS PSI LR Ts LT PT QT FR : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
    {bs : List Nat}
    (hT : TabChain n w kS nb BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base bs)
    {x : Array Nat} {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {xm : Nat → Nat}
    (hxm : RepF n xm X) {p : Nat} {rels : List (Nat × Nat × Nat)} (hrels : ∀ r ∈ rels, r.2.2 < p)
    (hFR : ∀ i < nb, FR i = 0 ∨ ∃ l e, FR i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧ (l, i, e) ∈ rels)
    {E : List (Array Nat)} {cb ps : List Nat} (hcb : ∀ b ∈ cb, b < n) {KE SK : Nat → Nat}
    {NE : Nat}
    (hE : ∀ (a : Array Nat) (A : Equiv.Perm (Fin n)), Rep n a A →
      A ∈ Subgroup.closure (Set.range fun j : Fin kS => permOfArr n S[j.val]!) →
      (∃ j < NE, keyA n ps a = KE (SK j)) → E.any (eqA n a) = true)
    (hNE : NE < 2 ^ 20)
    (h : ptK n w kS NR NL LT PT QT LR FR rels xm cb ps KE SK NE nb 0 (fun y => y) (fun y => y)
      (fun _ => 0) = true) :
    ptailOK n (rawLevels n S base) base x (powPA p n x) rels E nb 0 (idA n) = true := by
  have _ := hNE
  obtain ⟨hb, hp, ho, hN, ht, -⟩ := hT
  exact ptK_sound_aux hb hp ho hN ht hx hxm hrels hFR hcb hE nb 0 (by omega) (fun y => y)
    (fun y => y) (fun _ => 0) (idA n) 1 RepF.one (RepF.one.congr inv_one.symm) rep_idA
    (Subgroup.one_mem _) (fun m hm => absurd hm (Nat.not_lt_zero m)) h

end CFSG.KC.HeLoc

end
