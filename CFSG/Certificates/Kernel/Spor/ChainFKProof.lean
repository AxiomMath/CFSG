module

public import Certificates.Data.Kernel.Spor.ChainFK
public import CFSG.Certificates.Kernel.Spor.ChainKProof
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.ONSchreier.Native

theorem psift_end_full {levels : Array CLevel} {invs : Array (Array (Array Nat))}
    {pts bidx : Array Nat} {l : Nat} {img : Array Nat} (hl : ¬ l < levels.size) :
    psift levels invs pts bidx true l img = allBelowN pts.size fun t => img[t]! == pts[t]! := by
  rw [psift, dite_eq_right hl]
  rfl

theorem memFull3_proved {n s : Nat} {S : Array (Array Nat)} {base g : Array Nat}
    {F FI : Nat → Nat → Nat} {B G LEN : Nat → Nat} {IDX : Nat → Nat → Nat} {Mr : Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s) (hSz : ∀ j < s, S[j]!.size = n)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n) (hg : ∀ y < n, g[y]! = G y)
    (hG : ∀ y < n, G y < n) (hlen : ∀ i < 3, 0 < LEN i)
    (hidx : ∀ i < 3, idxOK F s B i (IDX i) (LEN i) = true)
    (hh : ∀ i < 3, cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) = true)
    (hp : ∀ i < 3, ∀ k < Mr i, cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < 3, ∀ z < n, cbPos n (Mr i) (PTS i) (POS i) z = true)
    (hsift : siftFull3 n POS PAR LAB Mr (fun i => invX F FI (IDX i) (LEN i)) B G = true) :
    memFull n (cLevels n base (allSteps S (pinvs n S) base)) (allInvSteps S (pinvs n S) base) base
      g = true := by
  have hSe : ∀ j < s, S[j]! = Array.ofFn (n := n) fun x => F j x.val :=
    fun j hj => CFSG.KS.PW.arr_ext (hSz j hj) fun x hx => (hF j hj x hx).1
  have hSi : ∀ j < s, ∀ x < n, ((pinvs n S)[j]!)[x]! = FI j x := by
    intro j hj x hx
    unfold pinvs
    rw [getElem!_pos _ j (by simp [hS]; exact hj), Array.getElem_map,
      ← getElem!_pos S j (by rw [hS]; exact hj), hSe j hj]
    have hsurj : ∀ y < n, ∃ x < n, F j x = y := by
      intro y hy
      obtain ⟨x, hx, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n)
        (t := Finset.range n) (fun x _ => F j x)
        (fun x hx => Finset.mem_range.2 (hF j hj x (Finset.mem_range.1 hx)).2.1)
        (fun a b ha hb hab => by
          rw [← (hF j hj a (Finset.mem_range.1 ha)).2.2.2,
            ← (hF j hj b (Finset.mem_range.1 hb)).2.2.2, hab])
        le_rfl y (Finset.mem_range.2 hy)
      exact ⟨x, Finset.mem_range.1 hx, e.symm⟩
    obtain ⟨x0, hx0, e0⟩ := hsurj x hx
    rw [← e0]
    rw [CFSG.KS.CB.pinvCand_get (fun y hy => (hF j hj y hy).2.1) (fun y hy => (hF j hj y hy).2.2.2)
      (by rw [e0]; exact hx), (hF j hj x0 hx0).2.2.2]
  have hst : ∀ i < 3, (allSteps S (pinvs n S) base)[i]!.size = Nat.mul 2 (LEN i) ∧
      ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
        ((allSteps S (pinvs n S) base)[i]!)[j]![x]! = stepX F FI (IDX i) (LEN i) j x := by
    intro i hi
    obtain ⟨hl, hlt⟩ := levIdx_eq hS hF hB hi (hidx i hi)
    unfold allSteps
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    unfold levSteps
    rw [hl]
    refine ⟨by simp; omega, fun j hj x hx => ?_⟩
    simp only [Nat.mul_eq] at hj
    unfold stepX
    rw [nIf_v]
    by_cases hjl : j < LEN i
    · rw [ite_eq_left (Nat.blt_eq.mpr hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_left (by simp; exact hjl)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      exact (hF _ (hlt j hjl) x hx).1
    · rw [ite_eq_right (by simpa using hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_right (by simp; omega)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
        List.length_map, List.length_range]
      exact hSi _ (hlt _ (by omega)) x hx
  have hinv : ∀ i < 3, ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
      ((allInvSteps S (pinvs n S) base)[i]!)[j]![x]! = invX F FI (IDX i) (LEN i) j x ∧
        invX F FI (IDX i) (LEN i) j x < n := by
    intro i hi j hj x hx
    simp only [Nat.mul_eq] at hj
    obtain ⟨hl, hlt⟩ := levIdx_eq hS hF hB hi (hidx i hi)
    unfold allInvSteps
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    unfold levInvSteps invX
    rw [hl, nIf_v]
    by_cases hjl : j < LEN i
    · rw [ite_eq_left (Nat.blt_eq.mpr hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_left (by simp; exact hjl)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [hSi _ (hlt j hjl) x hx]
      exact ⟨rfl, (hF _ (hlt j hjl) x hx).2.2.1⟩
    · rw [ite_eq_right (by simpa using hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_right (by simp; omega)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
        List.length_map, List.length_range]
      have hjs : j - LEN i < LEN i := by omega
      exact ⟨(hF _ (hlt _ hjs) x hx).1, (hF _ (hlt _ hjs) x hx).2.1⟩
  have hlev : ∀ i < 3, (cLevels n base (allSteps S (pinvs n S) base))[i]! =
      ⟨Array.ofFn (n := Mr i) fun k => PTS i k.val, Array.ofFn (n := n) fun z => POS i z.val,
        Array.ofFn (n := Mr i) fun k => PAR i k.val,
        Array.ofFn (n := Mr i) fun k => LAB i k.val⟩ := by
    intro i hi
    unfold cLevels
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    change cbfs n base[i]! (allSteps S (pinvs n S) base)[i]! = _
    rw [(hB i hi).1]
    exact cbfsK_sound (hst i hi) (hh i hi) (hp i hi) (hz i hi)
  have hcs : (cLevels n base (allSteps S (pinvs n S) base)).size = 3 := by simp [cLevels, hb]
  have hm : ∀ i < 3, ∀ k < Mr i, PAR i k < Mr i ∧ LAB i k < Nat.mul 2 (LEN i) := by
    intro i hi k hk
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨h1, -, h3, h4⟩ := cbHead_facts (hh i hi)
      rw [h3, h4]
      refine ⟨h1, ?_⟩
      have := hlen i hi
      simp only [Nat.mul_eq]
      omega
    · obtain ⟨a, b⟩ := cbPt_bounds (hp i hi k hk) hk0
      exact ⟨by omega, b⟩
  have hIlt : ∀ i < 3, ∀ j < Nat.mul 2 (LEN i), ∀ x < n, invX F FI (IDX i) (LEN i) j x < n :=
    fun i hi j hj x hx => (hinv i hi j hj x hx).2
  generalize hLV : cLevels n base (allSteps S (pinvs n S) base) = LV at hlev hcs
  generalize hIV : allInvSteps S (pinvs n S) base = IV at hinv
  have hpos : ∀ i < 3, ∀ x < n, LV[i]!.pos[x]! = POS i x := fun i hi x hx => by
    rw [hlev i hi]
    exact getD_ofFn hx
  have hsz : ∀ i < 3, LV[i]!.pts.size = Mr i := fun i hi => by
    rw [hlev i hi, Array.size_ofFn]
  have step : ∀ l < 3, ∀ (img : Array Nat) (φ : Nat → Nat), (∀ y < n, img[y]! = φ y) →
      (∀ y < n, φ y < n) → POS l (φ (B l)) < Mr l →
      psift LV IV (pid n) base true l img = psift LV IV (pid n) base true (l + 1)
        (img.map fun y => trInvApp IV[l]! LV[l]! (Mr l) (POS l (φ (B l))) y) := by
    intro l hl img φ hv hφ hk
    rw [psift_step (by rw [hcs]; exact hl), (hB l hl).1, hv _ (hB l hl).2,
      hpos l hl _ (hφ _ (hB l hl).2), hsz l hl, decide_eq_true hk, Bool.true_and]
  have mapv : ∀ l < 3, ∀ (img : Array Nat) (φ : Nat → Nat), img.size = n →
      (∀ y < n, img[y]! = φ y) → (∀ y < n, φ y < n) → ∀ k < Mr l,
      (img.map fun y => trInvApp IV[l]! LV[l]! (Mr l) k y).size = n ∧
        ∀ y < n, (img.map fun y => trInvApp IV[l]! LV[l]! (Mr l) k y)[y]! =
          trInvK (PAR l) (LAB l) (invX F FI (IDX l) (LEN l)) (Mr l) k (φ y) := by
    intro l hl img φ hs hv hφ k hk
    refine ⟨by rw [Array.size_map, hs], fun y hy => ?_⟩
    rw [getElem!_pos _ y (by rw [Array.size_map, hs]; exact hy), Array.getElem_map,
      ← getElem!_pos img y (by rw [hs]; exact hy), hv y hy, hlev l hl]
    exact trInvApp_eq (hm l hl) (fun j hj x hx => hinv l hl j hj x hx) (Mr l) k (φ y) hk (hφ y hy)
  have tlt : ∀ l < 3, ∀ k < Mr l, ∀ p < n,
      trInvK (PAR l) (LAB l) (invX F FI (IDX l) (LEN l)) (Mr l) k p < n :=
    fun l hl k hk p hpn => trInvK_lt (hm l hl) (hIlt l hl) _ _ _ hk hpn
  unfold siftFull3 at hsift
  simp only [strictB_v, bAnd_iff] at hsift
  obtain ⟨s0, s1, s2, s3⟩ := hsift
  have k0lt := Nat.blt_eq.mp s0
  have k1lt := Nat.blt_eq.mp s1
  have k2lt := Nat.blt_eq.mp s2
  unfold memFull
  have v0 : ∀ y < n, (Array.ofFn (n := n) fun i => g[i.val]!)[y]! = G y := fun y hy => by
    rw [getD_ofFn (f := fun i => g[i]!) hy, hg y hy]
  rw [step 0 (by norm_num) _ G v0 hG k0lt]
  obtain ⟨z1, v1⟩ := mapv 0 (by norm_num) _ G (by simp) v0 hG _ k0lt
  have hφ1 := fun y hy => tlt 0 (by norm_num) _ k0lt (G y) (hG y hy)
  rw [step 1 (by norm_num) _ _ v1 hφ1 k1lt]
  obtain ⟨z2, v2⟩ := mapv 1 (by norm_num) _ _ z1 v1 hφ1 _ k1lt
  have hφ2 := fun y hy => tlt 1 (by norm_num) _ k1lt _ (hφ1 y hy)
  rw [step 2 (by norm_num) _ _ v2 hφ2 k2lt]
  obtain ⟨-, v3⟩ := mapv 2 (by norm_num) _ _ z2 v2 hφ2 _ k2lt
  rw [psift_end_full (by rw [hcs]; norm_num), allBelowN_iff']
  intro t ht
  have htn : t < n := by simpa [pid] using ht
  rw [v3 t htn, pid, getD_ofFn (f := fun i => i) htn]
  exact allN_spec s3 t htn

end CFSG.KS.CH

end
