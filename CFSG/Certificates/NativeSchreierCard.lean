module

public import CFSG.Certificates.NativeSchreierArrays

public section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

theorem card_originalSubgroup_of_chainOK (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) :
    Nat.card Q.originalSubgroup = (rawOrbitSizes n S base).prod := by
  obtain ⟨hQ, hsz⟩ := validSchreier_of_chainOK hA hc h
  rw [← Q.orderCertificate_eq_card hQ, RawSchreierDatum.orderCertificate, rawOrbitSizes]
  congr 1
  apply List.ext_getElem
  · simp [ChainArrays.chainLevels_size, hA.base_size]
  · intro k h1 h2
    have hk : k < (rawLevels n S base).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [hsz]
    show ((rawLevels n S base)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem siftA_iff_mem_originalSubgroup (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) {g : Array ℕ} {G : Equiv.Perm (Fin n)}
    (hG : Rep n g G) :
    siftA n (rawLevels n S base) base 0 g = true ↔ G ∈ Q.originalSubgroup := by
  rw [hA.siftA_eq (chainCheckFacts h) Q.baseCount 0 (Nat.zero_add _) g G hG]
  exact Q.sift_eq_true_iff_mem_original (validSchreier_of_chainOK hA hc h).1 G

theorem RawSchreierDatum.mem_ofArrays_original {hn : 1 ≤ n} {k : ℕ} {hk : k ≤ S.size}
    {base : List (Fin n)} {hb : base.Nodup} {g : Equiv.Perm (Fin n)} :
    g ∈ (RawSchreierDatum.ofArrays n hn S k hk base hb W).original.toList ↔
      ∃ i < k, permOfArr n S[i]! = g := by
  change g ∈ (Vector.ofFn fun i : Fin k => permOfArr n S[(i : ℕ)]!).toList ↔ _
  rw [Vector.toList_ofFn, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

end CFSG.Certificates
