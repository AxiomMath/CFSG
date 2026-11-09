module

public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.SchreierChainCard

public noncomputable section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n : ℕ}

theorem ChainArrays.schreierOK_of_card {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W 0)
    (hc : Nat.card (Q.levelSubgroup 0) ≤ Q.orderCertificate) (chunks : ℕ) {i : ℕ}
    (hi : i < base.size) :
    schreierOK n (rawLevels n S base) base i (rawSteps n S base i) (rawLevels n S base)[i]!
      chunks = true := by
  have hiQ : i < Q.baseCount := hA.base_size ▸ hi
  have F := hA.levelFacts hF hiQ
  have hsz := hA.chainSteps_size hF (Nat.le_of_lt hiQ)
  have hT := (RawSchreierDatum.schTests_of_card hc).2 ⟨i, hiQ⟩
  unfold schreierOK
  refine CFSG.KS.Raw.Orb.parLt_of_forall fun h hh => allLt_iff.2 fun j hj => ?_
  change h < (lev n S base i).pts.size at hh
  change j < (rawSteps n S base i).size at hj
  have hj' : j < (Q.levelSteps i).length := hsz ▸ hj
  have hrs := hA.rep_chainSteps hF (Nat.le_of_lt hiQ) hj'
  obtain ⟨hk, -⟩ := F.closed h hh j hj
  have hzv : ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! =
      ((Q.levelSteps i)[j] (levPts Q S base i h) : ℕ) := by
    rw [hrs.apply (F.pts_lt h hh)]
    congr 2
    exact Fin.ext (hA.levPts_val hF hiQ hh).symm
  have hpts : levPts Q S base i
      ((lev n S base i).pos[((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!]!) =
      (Q.levelSteps i)[j] (levPts Q S base i h) := by
    apply Fin.ext
    rw [hA.levPts_val hF hiQ hk, F.pts_pos _ (by rw [hzv]; exact Fin.isLt _) hk, hzv]
  have htx := hA.transversal_of_lt hF hiQ hh
  have hty := hA.transversal_of_lt hF hiQ hk
  rw [hpts] at hty
  rw [← RawSchreierDatum.orbitTables_get] at htx hty
  obtain ⟨ty, hty', hsift⟩ := hT _ _ htx _ (List.getElem_mem hj')
  rw [hty] at hty'
  obtain rfl := Option.some.inj hty'
  have hrep := rep_compA (hA.rep_levTInv hF hiQ hk) (rep_compA hrs (hA.rep_levT hF hiQ hh))
  change (decide (_ < (lev n S base i).pts.size) && siftA n (rawLevels n S base) base (i + 1)
    (compA n (lev n S base i).trInv[(lev n S base i).pos[((rawSteps n S base i)[j]!)[
      (lev n S base i).pts[h]!]!]!]! (compA n (rawSteps n S base i)[j]! (lev n S base i).tr[h]!)))
    = true
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hk, ?_⟩
  rw [hA.siftA_eq hF (Q.baseCount - (i + 1)) (i + 1) (by omega) _ _ hrep, ← mul_assoc]
  exact hsift

theorem ChainArrays.orderCertificate_eq {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W 0) :
    Q.orderCertificate = (rawOrbitSizes n S base).prod := by
  have hsz : ∀ i : Fin Q.baseCount,
      Q.orbitSize i = ((rawLevels n S base)[(i : ℕ)]!).pts.size := fun i => hA.orbitSize_eq hF i.2
  rw [RawSchreierDatum.orderCertificate, rawOrbitSizes]
  congr 1
  apply List.ext_getElem
  · simp [ChainArrays.chainLevels_size, hA.base_size]
  · intro k h1 h2
    have hk : k < (rawLevels n S base).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [hsz]
    change ((rawLevels n S base)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem rawChainOK_of_card {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} (hA : ChainArrays Q O S base W) (h0 : rawChainOK n O S base W 0 = true)
    (hc : Nat.card (Q.levelSubgroup 0) ≤ Q.orderCertificate) (chunks : ℕ) :
    rawChainOK n O S base W chunks = true := by
  have hs : allLt base.size (fun i => schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! chunks) = true :=
    allLt_iff.2 fun i hi => hA.schreierOK_of_card (chainCheckFacts h0) hc chunks hi
  simp only [rawChainOK, Bool.and_eq_true] at h0 ⊢
  exact ⟨h0.1, hs⟩

end CFSG.Certificates

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem rawChainOK_zero_of_K {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      0 = true := by
  obtain ⟨hk, hH⟩ := rawHeadOK_of hb hh
  have hd := hd_of_head hk hH
  have hlv : ∀ i < base.size, levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]! = true := fun i hi => by
    rw [rawLevels_get hi]
    exact levelOK_of (levelOKT_bfs (hd.base_lt i hi) (steps_lt hd))
      (levelTrOK_bfs fun j hj => ⟨_, (step_rep hd hj).choose_spec.1⟩)
  have hsc : ∀ i < base.size, CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! 0 = true := fun i _ => rfl
  change (rawHeadOK n (S.extract 0 kO) S base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) &&
    allLt base.size (fun i => levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]!) &&
    allLt base.size (fun i => CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! 0)) = true
  rw [hH, allLt_iff.2 hlv, allLt_iff.2 hsc]
  rfl

end CFSG.KS.Raw.Orb

end
