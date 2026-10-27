module

public import CFSG.Sporadic.Schreier.TitsChain

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem siftA_mem_of {n : ℕ} [NeZero n] (hn : 1 ≤ n) {S : Array (Array ℕ)} {k : ℕ}
    (hk : k ≤ S.size) {b : List ℕ} (hb : (finList n b).Nodup) {W : Array (List ℤ)} {chunks : ℕ}
    (hP : allPermsOK n S = true) (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) W chunks = true) {g : Array ℕ}
    (hg : isInvA n g (invCand n g) = true)
    (hs : siftA n (rawLevels n S (baseArr n b)) (baseArr n b) 0 g = true) :
    permOfArr n g ∈ Subgroup.closure (Set.range fun j : Fin k => permOfArr n S[j.val]!) := by
  rw [← originalSubgroup_ofArrays (hn := hn) (hk := hk) (hb := hb) (W := W)]
  exact (siftA_iff_mem_ofArrays (hn := hn) (hk := hk) (hb := hb) hP hc h
    (rep_permOfArr hg).1).1 hs

end CFSG.Sporadic.Schreier.Tits

end
