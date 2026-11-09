module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainLowerBound

public section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)}

theorem rawOrbitSizes_prod_le_card (hA : ChainArrays Q O S base W)
    (h : rawChainOK n O S base W 0 = true) :
    (rawOrbitSizes n S base).prod ≤ Nat.card Q.originalSubgroup := by
  have hF := chainCheckFacts h
  have hsz : ∀ i : Fin Q.baseCount,
      Q.orbitSize i = ((rawLevels n S base)[(i : ℕ)]!).pts.size := fun i => hA.orbitSize_eq hF i.2
  have hle := Q.orderCertificate_le_card (hA.initial hF) (hA.words hF)
  rw [RawSchreierDatum.orderCertificate] at hle
  refine le_of_eq_of_le ?_ hle
  rw [rawOrbitSizes]
  congr 1
  apply List.ext_getElem
  · simp [ChainArrays.chainLevels_size, hA.base_size]
  · intro k h1 h2
    have hk : k < (rawLevels n S base).size := by simpa using h1
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [hsz]
    show _ = ((rawLevels n S base)[k]!).pts.size
    rw [getElem!_pos _ k hk]

theorem mem_originalSubgroup_of_siftA (hA : ChainArrays Q O S base W) {chunks : ℕ}
    (h : rawChainOK n O S base W chunks = true) {g : Array ℕ} {G : Equiv.Perm (Fin n)}
    (hG : Rep n g G) (hs : siftA n (rawLevels n S base) base 0 g = true) :
    G ∈ Q.originalSubgroup := by
  have hF := chainCheckFacts h
  rw [hA.siftA_eq hF Q.baseCount 0 (Nat.zero_add _) g G hG] at hs
  exact Q.mem_originalSubgroup_of_sift (hA.initial hF) (hA.words hF) hs

end CFSG.Certificates
