module

public import Certificates.Data.Kernel.D4LocalK
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.D4Local

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K
open CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.Monster.B.Co2 (allLt_iff)

private theorem flagRanks_count {fl : Array Bool} {R : ℕ → ℕ} (h0 : R 0 = 0)
    (hR : ∀ i < fl.size, R (i + 1) = R i + if fl[i]! = true then 1 else 0) :
    (∀ i < fl.size, (flagRanks fl)[i]! = R i) ∧ flagCount fl = R fl.size := by
  constructor
  · have key := Array.foldl_induction (as := fl)
      (motive := fun k (acc : Array ℕ × ℕ) =>
        acc.1.size = k ∧ (∀ i < k, acc.1[i]! = R i) ∧ acc.2 = R k)
      (init := ((#[] : Array ℕ), 0))
      (f := fun (acc : Array ℕ × ℕ) b => (acc.1.push acc.2, if b then acc.2 + 1 else acc.2))
      ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i), h0.symm⟩ ?_
    · exact key.2.1
    · rintro ⟨i, hi⟩ ⟨a, c⟩ ⟨h1, h2, h3⟩
      simp only at h1 h2 h3 ⊢
      have hs := hR i hi
      rw [getElem!_pos fl i hi] at hs
      refine ⟨by simp [h1], fun j hj => ?_, ?_⟩
      · by_cases hji : j < i
        · rw [getElem!_pos _ j (by simp [h1]; omega), Array.getElem_push_lt (by omega)]
          rw [← getElem!_pos a j (by omega)]
          exact h2 j hji
        · have hj' : j = i := by omega
          subst hj'
          subst h1
          rw [getElem!_pos _ a.size (by simp), Array.getElem_push_eq, h3]
      · rw [hs, h3]
        cases fl[i] <;> simp
  · have key := Array.foldl_induction (as := fl)
      (motive := fun k (acc : ℕ) => acc = R k)
      (init := 0)
      (f := fun (acc : ℕ) b => if b then acc + 1 else acc)
      h0.symm ?_
    · exact key
    · rintro ⟨i, hi⟩ c hc
      simp only at hc ⊢
      have hs := hR i hi
      rw [getElem!_pos fl i hi] at hs
      rw [hs, hc]
      cases fl[i] <;> simp

private theorem rankAt_spec {f : ℕ → Bool} {I R : ℕ → ℕ} {i : ℕ} (h : rankAt f I R i = true) :
    R (i + 1) = R i + (if f i = true then 1 else 0) ∧ (f i = true → I (R i) = i) := by
  unfold rankAt at h
  rw [Orb.bIf_eq] at h
  by_cases hf : f i = true
  · rw [if_pos hf, Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨by rw [if_pos hf]; exact Nat.eq_of_beq_eq_true h2,
      fun _ => Nat.eq_of_beq_eq_true h1⟩
  · rw [if_neg hf] at h
    exact ⟨by rw [if_neg hf]; exact (Nat.eq_of_beq_eq_true h).trans (Nat.add_zero _).symm,
      fun h' => absurd h' hf⟩

private theorem rank_mono {R : ℕ → ℕ} {N : ℕ} (h : ∀ i < N, R i ≤ R (i + 1)) :
    ∀ j, j ≤ N → ∀ i ≤ j, R i ≤ R j := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    obtain rfl : i = 0 := by omega
    exact le_rfl
  | succ j ih =>
    intro hj i hi
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · exact (ih (by omega) i (by omega)).trans (h j (by omega))
    · obtain rfl : i = j + 1 := by omega
      exact le_rfl

private theorem ranks_of {fl : Array Bool} {N c : ℕ} {f : ℕ → Bool} {I R : ℕ → ℕ}
    (hN : fl.size = N) (hf : ∀ i < N, fl[i]! = f i) (hr : ∀ i < N, rankAt f I R i = true)
    (he : rankEnds N R c = true) :
    (∀ i < N, (flagRanks fl)[i]! = R i) ∧ flagCount fl = c ∧
      ∀ i < N, fl[i]! = true → R i < c ∧ I (R i) = i := by
  unfold rankEnds at he
  rw [Orb.bAnd_eq, Bool.and_eq_true] at he
  obtain ⟨h0, hc⟩ := he
  have h0' : R 0 = 0 := Nat.eq_of_beq_eq_true h0
  have hc' : R N = c := Nat.eq_of_beq_eq_true hc
  have hstep : ∀ i < N, R (i + 1) = R i + (if fl[i]! = true then 1 else 0) := fun i hi => by
    rw [hf i hi]
    exact (rankAt_spec (hr i hi)).1
  have hmono : ∀ i < N, R i ≤ R (i + 1) := fun i hi => by
    rw [hstep i hi]
    omega
  obtain ⟨h1, h2⟩ := flagRanks_count (fl := fl) h0' (by rwa [hN])
  refine ⟨fun i hi => h1 i (by omega), by rw [h2, hN, hc'], fun i hi hfl => ?_⟩
  have hfi : f i = true := (hf i hi) ▸ hfl
  have hs := hstep i hi
  rw [if_pos hfl] at hs
  refine ⟨?_, (rankAt_spec (hr i hi)).2 hfi⟩
  have := rank_mono hmono N le_rfl (i + 1) (by omega)
  omega

private theorem periodGoK_eq {n : ℕ} {f f' : ℕ → ℕ} {i : ℕ} (hlt : ∀ q < n, f q < n)
    (hag : ∀ q < n, f q = f' q) :
    ∀ (fuel cur l : ℕ), cur < n → periodGoK f i fuel cur l = periodGo f' i fuel cur l := by
  intro fuel
  induction fuel with
  | zero => intro cur l _; rfl
  | succ fuel ih =>
    intro cur l hc
    have e : periodGoK f i (fuel + 1) cur l = strictN (f cur) (fun c => strictN (Nat.succ l)
        (fun l' => nIf(Nat.beq c i, l', periodGoK f i fuel c l'))) := rfl
    rw [e, Orb.strictN_eq, Orb.strictN_eq, Orb.nIf_eq]
    simp only [periodGo]
    rw [← hag cur hc]
    by_cases h : f cur = i
    · simp [h]
    · simp only [h, Nat.beq_eq, if_false]
      exact ih (f cur) (l + 1) (hlt cur hc)

private theorem periodK_eq {n : ℕ} {f f' : ℕ → ℕ} {i : ℕ} (hi : i < n) (hlt : ∀ q < n, f q < n)
    (hag : ∀ q < n, f q = f' q) (fuel : ℕ) : periodK f i fuel = period f' i fuel :=
  periodGoK_eq hlt hag fuel i 0 hi

private theorem witT_eq (l : ℕ) : witT l = (decide (0 < l) && decide (l % 3 = 0)) := by
  unfold witT
  rw [Orb.bAnd_eq, Orb.blt_dec, Orb.beq_dec]
  rfl

private theorem upowK_eq {n w u : ℕ} (hw : szOK n w = true) (hu : permB n w u = true) (k : ℕ)
    {p : ℕ} (hp : p < n) :
    upowK w (mask w) u k p = upow (unpack n w u) k p ∧ upowK w (mask w) u k p < n := by
  have hlt : ∀ q < n, pg w (mask w) u q < n := (pp_of_permB hw hu).2.1
  rcases k with _ | _ | k
  · exact ⟨rfl, hp⟩
  · exact ⟨(Orb.unpack_get hp).symm, hlt p hp⟩
  · have h1 := hlt p hp
    refine ⟨?_, hlt _ h1⟩
    show pg w (mask w) u (pg w (mask w) u p) = (unpack n w u)[(unpack n w u)[p]!]!
    rw [Orb.unpack_get hp, Orb.unpack_get h1]

private theorem yconjK_eq {n w u y : ℕ} (hw : szOK n w = true) (hu : permB n w u = true)
    (hy : permB n w y = true) (k : ℕ) {p : ℕ} (hp : p < n) :
    yconjK w (mask w) u y k p = yconj (unpack n w u) (unpack n w y) k p ∧
      yconjK w (mask w) u y k p < n := by
  have hlty : ∀ q < n, pg w (mask w) y q < n := (pp_of_permB hw hy).2.1
  obtain ⟨e1, l1⟩ := upowK_eq hw hu ((3 - k) % 3) hp
  have l2 := hlty _ l1
  obtain ⟨e3, l3⟩ := upowK_eq hw hu k l2
  have e2 : (unpack n w y)[upow (unpack n w u) ((3 - k) % 3) p]! =
      pg w (mask w) y (upowK w (mask w) u ((3 - k) % 3) p) := by
    rw [← e1]
    exact Orb.unpack_get l1
  refine ⟨?_, l3⟩
  show upowK w (mask w) u k (pg w (mask w) y (upowK w (mask w) u ((3 - k) % 3) p)) =
    upow (unpack n w u) k ((unpack n w y)[upow (unpack n w u) ((3 - k) % 3) p]!)
  rw [e2]
  exact e3

private theorem wordK_eq {n w u y : ℕ} (hw : szOK n w = true) (hu : permB n w u = true)
    (hy : permB n w y = true) (wc : ℕ) {q : ℕ} (hq : q < n) :
    wordK w (mask w) u y wc q = wordPt (unpack n w u) (unpack n w y) (wordLetters wc) q ∧
      wordK w (mask w) u y wc q < n := by
  rcases wc with _ | _ | _ | wc
  · obtain ⟨e1, l1⟩ := yconjK_eq hw hu hy 1 hq
    obtain ⟨e2, l2⟩ := yconjK_eq hw hu hy 0 l1
    refine ⟨?_, l2⟩
    show yconjK w (mask w) u y 0 (yconjK w (mask w) u y 1 q) =
      yconj (unpack n w u) (unpack n w y) 0 (yconj (unpack n w u) (unpack n w y) 1 q)
    rw [e2, e1]
  · obtain ⟨e1, l1⟩ := yconjK_eq hw hu hy 1 hq
    obtain ⟨e2, l2⟩ := yconjK_eq hw hu hy 0 l1
    obtain ⟨e3, l3⟩ := yconjK_eq hw hu hy 0 l2
    refine ⟨?_, l3⟩
    show yconjK w (mask w) u y 0 (yconjK w (mask w) u y 0 (yconjK w (mask w) u y 1 q)) =
      yconj (unpack n w u) (unpack n w y) 0 (yconj (unpack n w u) (unpack n w y) 0
        (yconj (unpack n w u) (unpack n w y) 1 q))
    rw [e3, e2, e1]
  · obtain ⟨e1, l1⟩ := yconjK_eq hw hu hy 2 hq
    obtain ⟨e2, l2⟩ := yconjK_eq hw hu hy 1 l1
    obtain ⟨e3, l3⟩ := yconjK_eq hw hu hy 0 l2
    refine ⟨?_, l3⟩
    show yconjK w (mask w) u y 0 (yconjK w (mask w) u y 1 (yconjK w (mask w) u y 2 q)) =
      yconj (unpack n w u) (unpack n w y) 0 (yconj (unpack n w u) (unpack n w y) 1
        (yconj (unpack n w u) (unpack n w y) 2 q))
    rw [e3, e2, e1]
  · obtain ⟨e1, l1⟩ := yconjK_eq hw hu hy 1 hq
    obtain ⟨e2, l2⟩ := yconjK_eq hw hu hy 2 l1
    obtain ⟨e3, l3⟩ := yconjK_eq hw hu hy 0 l2
    refine ⟨?_, l3⟩
    show yconjK w (mask w) u y 0 (yconjK w (mask w) u y 2 (yconjK w (mask w) u y 1 q)) =
      yconj (unpack n w u) (unpack n w y) 0 (yconj (unpack n w u) (unpack n w y) 2
        (yconj (unpack n w u) (unpack n w y) 1 q))
    rw [e3, e2, e1]

private theorem selfWit_eq {n w y : ℕ} (hw : szOK n w = true) (hy : permB n w y = true)
    (fuel p : ℕ) : selfWitOK n (unpack n w y) p fuel = selfWitK n w fuel y p := by
  unfold selfWitOK selfWitK
  rw [Orb.bAnd_eq, witT_eq, Orb.blt_dec]
  by_cases hp : p < n
  · rw [periodK_eq hp (fun q hq => (pp_of_permB hw hy).2.1 q hq)
      (fun q hq => (Orb.unpack_get hq).symm) fuel]
    rw [Bool.and_assoc]
  · simp [hp]

private theorem pairWit_eq {n w u y : ℕ} (hw : szOK n w = true) (hu : permB n w u = true)
    (hy : permB n w y = true) (fuel wc p : ℕ) :
    pairWitOK n (unpack n w u) (unpack n w y) wc p fuel = pairWitK n w fuel u y wc p := by
  unfold pairWitOK pairWitK
  rw [Orb.bAnd_eq, witT_eq, Orb.blt_dec]
  by_cases hp : p < n
  · rw [periodK_eq hp (fun q hq => (wordK_eq hw hu hy wc hq).2)
      (fun q hq => (wordK_eq hw hu hy wc hq).1) fuel]
    rw [Bool.and_assoc]
  · simp [hp]

private theorem uFlag_eq {n w X u : ℕ} (hw : szOK n w = true) (hX : permB n w X = true)
    (hu : permB n w u = true) :
    uFlag n (unpack n w X) (unpack n w u) = uFlagK n w X (pw n w X 2) u := by
  unfold uFlag uFlagK
  rw [eqA_id hw hu, powEq_id hw hu 3, eqA_unpack' hw hu hX, pow_unpack' hw hX 2,
    eqA_unpack' hw hu (permB_ppow hw hX 2)]
  simp only [Orb.bAnd_eq, Bool.and_assoc]
  rfl

private theorem yFlag_eq {n w y : ℕ} (hw : szOK n w = true) (hy : permB n w y = true)
    (fuel p : ℕ) : yFlag n fuel (unpack n w y) p = yFlagK n w fuel y p := by
  unfold yFlag yFlagK
  rw [eqA_id hw hy, selfWit_eq hw hy, Orb.bAnd_eq]

theorem localK_sound {n w fuel N X nu ny : ℕ} {T SP PW UI YI RU RY : ℕ → ℕ}
    {pts : Array (Array ℕ)} {selfPt pairWit : Array ℕ}
    (hw : szOK n w = true) (hX : permB n w X = true) (hT : ∀ i < N, permB n w (T i) = true)
    (hpts : pts.size = N) (hp : ∀ i < N, pts[i]! = unpack n w (T i))
    (hsp : ∀ i < N, selfPt[i]! = SP i) (hpw : ∀ j < nu * ny, pairWit[j]! = PW j)
    (hU : ∀ i < N, rankAt (fun i => uFlagK n w X (pw n w X 2) (T i)) UI RU i = true)
    (hUe : rankEnds N RU nu = true)
    (hY : ∀ i < N, rankAt (fun i => yFlagK n w fuel (T i) (SP i)) YI RY i = true)
    (hYe : rankEnds N RY ny = true)
    (hpairs : ∀ a < nu, pairsK n w fuel T UI YI PW ny a = true) :
    localOK n fuel (unpack n w X) pts selfPt pairWit = true := by
  have hUF : ∀ i < N, (pts.map (uFlag n (unpack n w X)))[i]! =
      uFlagK n w X (pw n w X 2) (T i) := by
    intro i hi
    have hi' : i < pts.size := by omega
    rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_map, ← getElem!_pos pts i hi',
      hp i hi]
    exact uFlag_eq hw hX (hT i hi)
  have hYF : ∀ i < N, (Array.ofFn (n := pts.size) fun iy =>
      yFlag n fuel pts[iy.val]! selfPt[iy.val]!)[i]! = yFlagK n w fuel (T i) (SP i) := by
    intro i hi
    have hi' : i < pts.size := by omega
    rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_ofFn]
    show yFlag n fuel pts[i]! selfPt[i]! = _
    rw [hp i hi, hsp i hi]
    exact yFlag_eq hw (hT i hi) fuel (SP i)
  obtain ⟨hRU, hcU, hflagU⟩ := ranks_of (fl := pts.map (uFlag n (unpack n w X))) (N := N)
    (c := nu) (f := fun i => uFlagK n w X (pw n w X 2) (T i)) (I := UI) (R := RU)
    (by simpa using hpts) hUF hU hUe
  obtain ⟨hRY, hcY, hflagY⟩ := ranks_of (fl := Array.ofFn (n := pts.size) fun iy =>
      yFlag n fuel pts[iy.val]! selfPt[iy.val]!) (N := N) (c := ny)
    (f := fun i => yFlagK n w fuel (T i) (SP i)) (I := YI) (R := RY)
    (by simpa using hpts) hYF hY hYe
  unfold localOK
  dsimp only
  rw [allLt_iff]
  intro iu hiu
  have hiuN : iu < N := hpts ▸ hiu
  cases hF : (pts.map (uFlag n (unpack n w X)))[iu]! with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    rw [allLt_iff]
    intro iy hiy
    have hiyN : iy < N := hpts ▸ hiy
    cases hG : (Array.ofFn (n := pts.size) fun iy =>
        yFlag n fuel pts[iy.val]! selfPt[iy.val]!)[iy]! with
    | false => rfl
    | true =>
      obtain ⟨hlu, hIu⟩ := hflagU iu hiuN hF
      obtain ⟨hly, hIy⟩ := hflagY iy hiyN hG
      simp only [Bool.not_true, Bool.false_or]
      rw [hRU iu hiuN, hRY iy hiyN, hcY]
      have hidx : RU iu * ny + RY iy < nu * ny := by
        calc RU iu * ny + RY iy < RU iu * ny + ny := by omega
          _ = (RU iu + 1) * ny := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ nu * ny := Nat.mul_le_mul_right ny hlu
      rw [hpw _ hidx, hp iu hiuN, hp iy hiyN, pairWit_eq hw (hT iu hiuN) (hT iy hiyN)]
      have h1 := hpairs (RU iu) hlu
      unfold pairsK at h1
      rw [Orb.allN_iff] at h1
      have h2 := h1 (RY iy) hly
      rw [Orb.strictB_eq, hIu, hIy] at h2
      exact h2

end CFSG.KC.D4Local

end
