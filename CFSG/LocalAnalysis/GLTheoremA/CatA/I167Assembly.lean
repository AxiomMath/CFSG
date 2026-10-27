module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Step0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10


theorem i167Univ_of_cases (hF : I167Field) (hT : I167Tri) (hC : I167Class) (hE3 : I167Exc3)
    (hE : I167Exc) : T123C.I167Univ := by
  intro Ω _ _ p B X D J hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase
  have hCD := inf_cs_le_of_glaPComponent hJ hDJ
  by_cases hfld : ∃ d ∈ D, FieldOn p d X
  · obtain ⟨d, hdD, hdF⟩ := hfld
    have hdc := notMem_cs_of_fieldOn hp hdF
    exact hF Ω p B X D J d hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hdD hdc
      (eq_sup_zpowers_of_notMem_cs hp hD hcard hCD hdD hdc) hdF
  · have hhalf : HalfSplit16At p X := hcase.resolve_right hfld
    have hnf : ∀ d ∈ D, ¬ FieldOn p d X := fun d hd hf => hfld ⟨d, hd, hf⟩
    obtain ⟨x, hxD, hxc⟩ := exists_mem_notMem_cs hp hD hcard
    have hDx := eq_sup_zpowers_of_notMem_cs hp hD hcard hCD hxD hxc
    have hxB : x ∈ B := hD.1 hxD
    by_cases hinn : InnDiagOn p (Subgroup.zpowers x) X
    · by_cases hcl : catalogIs (PSimple p X) K1419.I1419Classical2
      · exact hC Ω p B X D J x hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc hDx
          hnf hhalf hinn hcl
      · by_cases hp3 : p = 3
        · exact (hE3 Ω p B X D J x hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc
            hDx hnf hhalf hinn hcl hp3).elim
        · exact (hE Ω p B X D J x hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc
            hDx hnf hhalf hinn hcl hp3).elim
    · have hxN : x ∈ Subgroup.normalizer (X : Set Ω) := hBN hxB
      rcases fieldOn_or_triality_of_not_innDiagOn hp hp2 hX hchev hxN (hB.2 x hxB) hinn with
        hf | ⟨hp3, hD4⟩
      · exact (hnf x hxD hf).elim
      · exact (hT Ω p B X D J x hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc
          hDx hnf ⟨hxN, hinn⟩ hp3 hD4).elim

end CFSG.LocalAnalysis.GLTheoremA.I167

end
