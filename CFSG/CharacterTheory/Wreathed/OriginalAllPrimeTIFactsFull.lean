module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFacts
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersFacts

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB

theorem wreathedSetting_tiFacts_of
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    (wreathedSetting n S e p f).TIFacts :=
  wreathedSetting_tiFacts hnonab n hn S e hfour p f hp hpodd hf hq hlocal
    ModelSignalizers.allModelSignalizerFacts

end CFSG.Wreathed.OriginalAllPrime
