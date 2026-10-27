module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTheoremBStar
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeV4Inputs

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB SmallerRecognitionOriginalField

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem wreathedSetting_bStarInputs
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    WreathedBStarInputs (wreathedSetting n S e p f) where
  ii42 := wreathedSetting_lemmaII42Input hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  ii46 := wreathedSetting_lemmaII46Input hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  ii49 := wreathedSetting_lemmaII49Input hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  ii49i := wreathedSetting_x₂_commutator_mem_ON hnonab n hn S e hfour p f hp hpodd hf hq hlocal

theorem wreathedSetting_theoremBStar
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (hsd : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G) :
    (wreathedSetting n S e p f).TheoremBStar :=
  wreathedSetting_theoremBStar_of_inputs hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec hsd
    (wreathedSetting_bStarInputs hnonab n hn S e hfour p f hp hpodd hf hq hlocal)

omit [Finite G] [IsSimpleGroup G] in
theorem stationaryCoverageStatement_holds :
    CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement :=
  stationaryCoverageStatement_of_bStarInputs
    fun _ _ _ _ hnonab _ _ n hn S e hfour p f hp hpodd hf hq hlocal =>
      wreathedSetting_bStarInputs hnonab n hn S e hfour p f hp hpodd hf hq hlocal

end CFSG.Wreathed.OriginalAllPrime
