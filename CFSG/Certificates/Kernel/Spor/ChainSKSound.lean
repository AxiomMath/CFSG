module

public import Certificates.Data.Kernel.Spor.ChainSK
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.Spor.CBLevelSound
import CFSG.Certificates.Kernel.Spor.ChainSKBase
import CFSG.Certificates.Kernel.Spor.ChainSKTree
public import CFSG.Certificates.Kernel.Spor.ChainKGen

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS.CB CFSG.ONSchreier.Native CFSG.Monster.B.Co2

theorem pointChain3_sound {n m s chunks : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} {F FI : Nat → Nat → Nat} {B LEN : Nat → Nat} {IDX : Nat → Nat → Nat}
    {Mr : Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s) (hWs : W.size = s) (hm : m ≤ s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (CFSG.KS.TW.GZ F FI) x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n)
    (hidx : ∀ i < 3, idxOK F s B i (IDX i) (LEN i) = true)
    (hh : ∀ i < 3, cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) = true)
    (hp : ∀ i < 3, ∀ k < Mr i, cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < 3, ∀ z < n, cbPos n (Mr i) (PTS i) (POS i) z = true)
    (hsch : ∀ i < 3, ∀ h < Mr i, ∀ j < Nat.mul 2 (LEN i),
      schK (fun i => stepX F FI (IDX i) (LEN i)) (fun i => invX F FI (IDX i) (LEN i)) PTS POS PAR
        LAB Mr B i h j = true) :
    pointChainOK n m S base W chunks = true ∧ cOrbitSizes n S base = [Mr 0, Mr 1, Mr 2] := by
  have hst : ∀ i < 3, (allSteps S (pinvs n S) base)[i]!.size = Nat.mul 2 (LEN i) ∧
      ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
        (((allSteps S (pinvs n S) base)[i]!)[j]!)[x]! = stepX F FI (IDX i) (LEN i) j x ∧
          stepX F FI (IDX i) (LEN i) j x < n :=
    fun i hi => SKB.steps3_get hS hF hb hB hi (hidx i hi)
  have hinv : ∀ i < 3, ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
      (((allInvSteps S (pinvs n S) base)[i]!)[j]!)[x]! = invX F FI (IDX i) (LEN i) j x ∧
        invX F FI (IDX i) (LEN i) j x < n :=
    fun i hi => SKB.invSteps3_get hS hF hb hB hi (hidx i hi)
  have hSlt : ∀ i < 3, ∀ j < Nat.mul 2 (LEN i), ∀ x < n, stepX F FI (IDX i) (LEN i) j x < n :=
    fun i hi j hj x hx => ((hst i hi).2 j hj x hx).2
  have hIlt : ∀ i < 3, ∀ j < Nat.mul 2 (LEN i), ∀ x < n, invX F FI (IDX i) (LEN i) j x < n :=
    fun i hi j hj x hx => (hinv i hi j hj x hx).2
  have hlev : ∀ i < 3, (cLevels n base (allSteps S (pinvs n S) base))[i]! =
      ⟨Array.ofFn (n := Mr i) fun k => PTS i k.val, Array.ofFn (n := n) fun z => POS i z.val,
        Array.ofFn (n := Mr i) fun k => PAR i k.val,
        Array.ofFn (n := Mr i) fun k => LAB i k.val⟩ := by
    intro i hi
    unfold cLevels
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    change cbfs n base[i]! (allSteps S (pinvs n S) base)[i]! = _
    rw [(hB i hi).1]
    exact cbfsK_sound ⟨(hst i hi).1, fun j hj x hx => ((hst i hi).2 j hj x hx).1⟩ (hh i hi)
      (hp i hi) (hz i hi)
  have hcs : (cLevels n base (allSteps S (pinvs n S) base)).size = 3 := by simp [cLevels, hb]
  have hmb : ∀ i < 3, ∀ k < Mr i, k ≠ 0 → PAR i k < Mr i ∧ LAB i k < Nat.mul 2 (LEN i) := by
    intro i hi k hk hk0
    obtain ⟨a, b⟩ := cbPt_bounds (hp i hi k hk) hk0
    exact ⟨by omega, b⟩
  have hcl : ∀ i < 3, clevelOK n base[i]! (allSteps S (pinvs n S) base)[i]!
      (cLevels n base (allSteps S (pinvs n S) base))[i]! = true := by
    intro i hi
    have e : (cLevels n base (allSteps S (pinvs n S) base))[i]! =
        cbfs n base[i]! (allSteps S (pinvs n S) base)[i]! := by
      unfold cLevels
      rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    rw [e]
    refine CFSG.KS.CBF.clevelOK_cbfs (by rw [(hB i hi).1]; exact (hB i hi).2) fun j hj x hx => ?_
    rw [(hst i hi).1] at hj
    rw [((hst i hi).2 j hj x hx).1]
    exact hSlt i hi j hj x hx
  have hsc : ∀ i < 3, cschreierOK (cLevels n base (allSteps S (pinvs n S) base))
      (allSteps S (pinvs n S) base) (allInvSteps S (pinvs n S) base) base
      (Array.ofFn (n := base.size) fun i => i.val) false i chunks = true := by
    generalize cLevels n base (allSteps S (pinvs n S) base) = LV at hlev hcs ⊢
    generalize allSteps S (pinvs n S) base = SV at hst ⊢
    generalize allInvSteps S (pinvs n S) base = IV at hinv ⊢
    have hpos : ∀ i < 3, ∀ x < n, LV[i]!.pos[x]! = POS i x := fun i hi x hx => by
      rw [hlev i hi]
      exact getD_ofFn hx
    have hsz : ∀ i < 3, LV[i]!.pts.size = Mr i := fun i hi => by
      rw [hlev i hi, Array.size_ofFn]
    have hptsv : ∀ i < 3, ∀ k < Mr i, LV[i]!.pts[k]! = PTS i k := fun i hi k hk => by
      rw [hlev i hi]
      exact getD_ofFn hk
    have bid : ∀ t < 3, (Array.ofFn (n := base.size) fun i => i.val)[t]! = t := fun t ht =>
      getD_ofFn (f := fun i => i) (by rw [hb]; exact ht)
    have step : ∀ l < 3, ∀ ψ : Nat → Nat, (∀ t < 3, ψ t < n) →
        psift LV IV base (Array.ofFn (n := base.size) fun i => i.val) false l
          (Array.ofFn (n := 3) fun t => ψ t.val) =
        (decide (POS l (ψ l) < Mr l) && psift LV IV base
          (Array.ofFn (n := base.size) fun i => i.val) false (l + 1)
          (Array.ofFn (n := 3) fun t =>
            trInvK (PAR l) (LAB l) (invX F FI (IDX l) (LEN l)) (Mr l) (POS l (ψ l)) (ψ t.val))) :=
      fun l hl ψ hψ => SKB.psift_ofFn_step (by rw [hcs]; exact hl) hl (bid l hl) (hlev l hl)
        (hmb l hl) (hinv l hl) hψ
    intro i hi
    unfold cschreierOK
    dsimp only
    rw [hsz i hi, (hst i hi).1]
    refine CFSG.KS.PCC.parBelow_of fun h hh => allBelowN_iff'.2 fun j hj => ?_
    have hpt : PTS i h < n := (cbPt_facts (hp i hi h hh)).1
    have hstv := (hst i hi).2 j hj _ hpt
    rw [hptsv i hi h hh, hstv.1, hpos i hi _ hstv.2]
    have hs0 := hsch i hi h hh j hj
    simp only [schK, strictB_v] at hs0
    rw [bAnd_iff] at hs0
    obtain ⟨hk, hs0⟩ := hs0
    have hk' : POS i (stepX F FI (IDX i) (LEN i) j (PTS i h)) < Mr i := Nat.blt_eq.mp hk
    rw [decide_eq_true hk', Bool.true_and, hlev i hi,
      SKB.schreierImgs_eq (STEP := fun i => stepX F FI (IDX i) (LEN i))
        (INV := fun i => invX F FI (IDX i) (LEN i)) hb hB (hmb i hi) (hst i hi).2 (hinv i hi) hh
        hj hk']
    generalize POS i (stepX F FI (IDX i) (LEN i) j (PTS i h)) = K at hk' hs0 ⊢
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    ·
      have hψ : ∀ t < 3, schImg (fun i => stepX F FI (IDX i) (LEN i))
          (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr 0 h j K (B t) < n := fun t ht =>
        SKB.schImg_lt (hmb 0 (by norm_num)) (hSlt 0 (by norm_num)) (hIlt 0 (by norm_num)) hh hj
          hk' (hB t ht).2
      have hs1 : bAnd(Nat.blt (POS 1 (schImg (fun i => stepX F FI (IDX i) (LEN i))
            (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr 0 h j K (B 1))) (Mr 1),
          Nat.blt (POS 2 (trInvK (PAR 1) (LAB 1) (invX F FI (IDX 1) (LEN 1)) (Mr 1)
            (POS 1 (schImg (fun i => stepX F FI (IDX i) (LEN i))
              (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr 0 h j K (B 1)))
            (schImg (fun i => stepX F FI (IDX i) (LEN i))
              (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr 0 h j K (B 2)))) (Mr 2)) = true :=
        hs0
      rw [bAnd_iff] at hs1
      have h1 := Nat.blt_eq.mp hs1.1
      have h2 := Nat.blt_eq.mp hs1.2
      refine (step 1 (by norm_num) _ hψ).trans ?_
      rw [decide_eq_true h1, Bool.true_and]
      refine (step 2 (by norm_num) _ fun t ht => trInvK_lt_nz (hmb 1 (by norm_num))
        (hIlt 1 (by norm_num)) (Mr 1) _ _ h1 (hψ t ht)).trans ?_
      rw [decide_eq_true h2, Bool.true_and]
      exact psift_end (by rw [hcs]; norm_num)
    ·
      have hψ : ∀ t < 3, schImg (fun i => stepX F FI (IDX i) (LEN i))
          (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr 1 h j K (B t) < n := fun t ht =>
        SKB.schImg_lt (hmb 1 (by norm_num)) (hSlt 1 (by norm_num)) (hIlt 1 (by norm_num)) hh hj
          hk' (hB t ht).2
      have hs1 : Nat.blt (POS 2 (schImg (fun i => stepX F FI (IDX i) (LEN i))
          (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr 1 h j K (B 2))) (Mr 2) = true := hs0
      refine (step 2 (by norm_num) _ hψ).trans ?_
      rw [decide_eq_true (Nat.blt_eq.mp hs1), Bool.true_and]
      exact psift_end (by rw [hcs]; norm_num)
    ·
      exact psift_end (by rw [hcs]; norm_num)
  refine ⟨SKB.pointChainOK_of_levels hS hWs hm hF hW hb hB hcl hsc, ?_⟩
  exact (SKB.cOrbitSizes_eq hb (M := Mr) fun i hi => by rw [hlev i hi, Array.size_ofFn]).trans rfl

theorem pointChainTree_sound {n m s chunks : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} {F FI : Nat → Nat → Nat} {B LEN t : Nat → Nat} {IDX : Nat → Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s) (hWs : W.size = s) (hm : m ≤ s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (CFSG.KS.TW.GZ F FI) x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n)
    (hidx : ∀ i < 3, idxOK F s B i (IDX i) (LEN i) = true)
    (htree : ∀ i < 3, ∀ k < t i, treePt n (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) (B i) k = true)
    (hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin m => permOfArr n S[j.val]!)) ≤
      t 0 * t 1 * t 2) :
    pointChainOK n m S base W chunks = true ∧ cOrbitSizes n S base = [t 0, t 1, t 2] := by
  have hn : 0 < n := by
    have := (hB 0 (by norm_num)).2
    omega
  have hbn : ∀ k < base.size, base[k]! < n := fun k hk => by
    rw [hb] at hk
    rw [(hB k hk).1]
    exact (hB k hk).2
  have H := SKT.hyp_of (W := W) hn hS hm hF hW hbn
  have hst : ∀ i < 3, (levSteps S (pinvs n S) base i).size = Nat.mul 2 (LEN i) ∧
      ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
        ((levSteps S (pinvs n S) base i)[j]!)[x]! = stepX F FI (IDX i) (LEN i) j x ∧
          stepX F FI (IDX i) (LEN i) j x < n := by
    intro i hi
    rw [← CFSG.KS.PCC.steps_get (show i < base.size by omega)]
    exact SKB.steps3_get hS hF hb hB hi (hidx i hi)
  have hle : ∀ i < 3, t i ≤ (CFSG.KS.PCC.lv n S base i).pts.size := by
    intro i hi
    unfold CFSG.KS.PCC.lv
    rw [(hB i hi).1]
    exact SKT.le_size_of_tree (hB i hi).2 (hst i hi).1 (hst i hi).2 (htree i hi)
  have hcardG : Nat.card (Subgroup.closure (Set.range fun j : Fin m =>
      CFSG.ONSchreier.permOfArr n S[j.val]!)) ≤ t 0 * t 1 * t 2 := by
    have e : (fun j : Fin m => permOfArr n S[j.val]!) =
        fun j : Fin m => CFSG.ONSchreier.permOfArr n S[j.val]! :=
      funext fun j => CFSG.KS.PCC.permOfArr_eq _
    rw [← e]
    exact hcard
  have hprod : (cOrbitSizes n S base).prod = (CFSG.KS.PCC.lv n S base 0).pts.size *
      (CFSG.KS.PCC.lv n S base 1).pts.size * (CFSG.KS.PCC.lv n S base 2).pts.size := by
    rw [CFSG.KS.PCC.cOrbitSizes_prod, hb]
    simp [Finset.prod_range_succ]
  have hcard' : Nat.card (Subgroup.closure (Set.range fun j : Fin m =>
      CFSG.ONSchreier.permOfArr n S[j.val]!)) ≤ (cOrbitSizes n S base).prod := by
    rw [hprod]
    exact hcardG.trans (Nat.mul_le_mul (Nat.mul_le_mul (hle 0 (by norm_num))
      (hle 1 (by norm_num))) (hle 2 (by norm_num)))
  have hcl : ∀ i < 3, clevelOK n base[i]! (allSteps S (pinvs n S) base)[i]!
      (cLevels n base (allSteps S (pinvs n S) base))[i]! = true := by
    intro i hi
    have hi' : i < base.size := by omega
    rw [CFSG.KS.PCC.lev_get hi', CFSG.KS.PCC.steps_get hi']
    exact CFSG.KS.CBF.clevelOK_of_facts (CFSG.KS.PCC.lv_facts H hi')
  have hsc : ∀ i < 3, cschreierOK (cLevels n base (allSteps S (pinvs n S) base))
      (allSteps S (pinvs n S) base) (allInvSteps S (pinvs n S) base) base
      (Array.ofFn (n := base.size) fun i => i.val) false i chunks = true :=
    fun i hi => CFSG.KS.PCC.schreier_ok H hcard' (by omega) chunks
  refine ⟨SKB.pointChainOK_of_levels hS hWs hm hF hW hb hB hcl hsc, ?_⟩
  have hsz := SKT.sizes_eq_of_card H (t := t) (fun l hl => hle l (by omega)) (by
    rw [hb]
    simpa [Finset.prod_range_succ] using hcardG)
  exact (SKB.cOrbitSizes_eq hb (M := t) fun i hi => by
    rw [CFSG.KS.PCC.lev_get (show i < base.size by omega)]
    exact hsz i (by omega)).trans rfl

end CFSG.KS.CH

end
