module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S10

theorem substable_of_facts
    (hU5 : CompFact S9.isU5two S9.isU4two)
    (hU6 : CompFact S9.isU6two (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S10.isL2eight i))
    (hSp8 : CompFactSp8)
    (hD4 : CompFact S9.isD4two S9.isU4two)
    (hdist : ListDistinct)
    (G : Type) [Group G] [Finite G] : StdSubTableAt G := by
  obtain ⟨dU4A6, dU5A6, dA6L2, dU4L2, dSp6L2⟩ := hdist
  intro B a J D K hS hYs hI hP
  obtain ⟨-, -, ha1, hJC, hcyc⟩ := hS
  obtain ⟨hDB, hDab, hDcard, haD, -, hKcomp, -⟩ := hP
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJC.2.2
  have haJ : ∀ x ∈ J, x * a = a * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJC.1 hx)
  have hDexp : ∀ x ∈ D, x ^ 3 = 1 := hDab.2
  have hD9 : Nat.card D = 3 ^ 2 := hDcard
  obtain ⟨d, hdD, hdJ⟩ := exists_mem_not_mem_centralizer hD9 hDexp hcyc
  have hcent := inf_centralizer_singleton_eq hD9 hDexp haD ha1 haJ hdD hdJ
  have hKd : CFSG.Open.IsComponentOf K (J ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [hcent]
    exact hKcomp
  have hdB : d ∈ B := hDB hdD
  have hd3 : d ^ 3 = 1 := hDexp d hdD
  obtain ⟨i, hi, ⟨e⟩⟩ := hYs
  rcases hi with h5 | h6 | h8 | h4
  ·
    have hPS : catalogIs (PSimple 3 J) S9.isU5two := ⟨i, h5, ⟨e⟩⟩
    have hK := hU5 G J B d hJq hPS hdB hI hd3 hdJ K hKd
    refine ⟨catalogIs_mono (fun j hj => stdSub_of_u4 hj) hK, fun hA6 => ?_, fun hL2 => ?_⟩
    · exact (dU4A6 _ hK hA6).elim
    · exact (dU4L2 _ hK hL2).elim
  ·
    have hPS : catalogIs (PSimple 3 J) S9.isU6two := ⟨i, h6, ⟨e⟩⟩
    have hK := hU6 G J B d hJq hPS hdB hI hd3 hdJ K hKd
    refine ⟨catalogIs_mono (fun j hj => ?_) hK, fun hA6 => ?_, fun _ => hPS⟩
    · rcases hj with h | h | h
      · exact stdSub_of_u4 h
      · exact stdSub_of_u5 h
      · exact stdSub_of_l2 h
    · rcases catalogIs_or hK with h | h
      · exact (dU4A6 _ h hA6).elim
      · rcases catalogIs_or h with h' | h'
        · exact (dU5A6 _ h' hA6).elim
        · exact (dA6L2 _ hA6 h').elim
  ·
    have hPS : catalogIs (PSimple 3 J) S9.isSp8two := ⟨i, h8, ⟨e⟩⟩
    obtain ⟨hK, hK6⟩ := hSp8 G J B d hJq hPS hdB hI hd3 hdJ K hKd
    refine ⟨catalogIs_mono (fun j hj => ?_) hK, hK6, fun hL2 => ?_⟩
    · rcases hj with h | h | h
      · exact stdSub_of_u4 h
      · exact stdSub_of_sp6 h
      · exact stdSub_of_a6 h
    · rcases catalogIs_or hK with h | h
      · exact (dU4L2 _ h hL2).elim
      · rcases catalogIs_or h with h' | h'
        · exact (dSp6L2 _ h' hL2).elim
        · exact (dA6L2 _ h' hL2).elim
  ·
    have hPS : catalogIs (PSimple 3 J) S9.isD4two := ⟨i, h4, ⟨e⟩⟩
    have hK := hD4 G J B d hJq hPS hdB hI hd3 hdJ K hKd
    refine ⟨catalogIs_mono (fun j hj => stdSub_of_u4 hj) hK, fun hA6 => ?_, fun hL2 => ?_⟩
    · exact (dU4A6 _ hK hA6).elim
    · exact (dU4L2 _ hK hL2).elim

end CFSG.LocalAnalysis.GLTheoremA.KSubT
