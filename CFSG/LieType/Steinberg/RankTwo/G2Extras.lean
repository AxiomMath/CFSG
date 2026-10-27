module

public import CFSG.LieType.Steinberg.RankTwo.G2ExtrasRankTwo
public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Steinberg.Conclusion
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem g2_rankOne
    (k : Type) [Field k] (i : Fin (Tag.rank .G2)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* ↥(adjointGroup .G2 k), Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = xPar (rootOperatorFamily .G2) (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = xPar (rootOperatorFamily .G2) (-Pi.single i 1) c := by
  obtain ⟨φ, hφ, hup, hlow⟩ := g2_exists_sl2_hom (K := k) i
  exact ⟨φ, hφ, fun c => (hup c).trans (xPar_simple i c).symm,
    fun c => (hlow c).trans (xPar_neg_simple i c).symm⟩

theorem g2_chevalleyExtras
    (k : Type) [Field k]
    (O : CommOrder (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible))
    (C : (Fin (Tag.rank .G2) → ℤ) → (Fin (Tag.rank .G2) → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (xPar (rootOperatorFamily .G2) (K := k)) O C) :
    ChevalleyExtras (g2Datum k) k (xPar (rootOperatorFamily .G2)) C O where
  param := adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := k) _
    (adjDatum_roots (rootOperatorFamily .G2) k)
  comm := hC
  weyl i _ hβ := weylElement_xPar_conj (F := rootOperatorFamily .G2) (K := k) i
    (mem_adjDatum_roots.1 hβ)
  rankOne i := g2_rankOne k i
  prodInjective f L hnd hL hsort := prodInjective (F := rootOperatorFamily .G2) (K := k) f L hnd
    (fun γ hγ => ⟨mem_adjDatum_roots.1 (hL γ hγ).1, (hL γ hγ).2⟩) hsort
  rankTwo i := g2_rankTwo (adjDatum_roots _ k) hC i

theorem g2_conclusionB_of_comm
    {k : Type} [Field k] [Finite k]
    (hC : ∀ O : CommOrder (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible),
      ∃ C : (Fin (g2Datum k).rank → ℤ) → (Fin (g2Datum k).rank → ℤ) → ℕ × ℕ → ℤ,
        (∀ α ∈ (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible).roots,
          ∀ β ∈ (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible).roots,
            ∀ p ∈ expPairs (RootSystem.ofCartan (g2Datum k).isFiniteType
              (g2Datum k).divisible) α β, (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧
          CommutatorFormula (xPar (rootOperatorFamily .G2) (K := k)) O C) :
    ConclusionB (g2Datum k) k (xPar (rootOperatorFamily .G2)) :=
  conclusionB_of rfl (g2_isCTGroupDatum k) (g2_steinbergExtras k)
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := k) _
      (adjDatum_roots (rootOperatorFamily .G2) k)) hC
    (fun O C h => g2_chevalleyExtras k O C h)

end CFSG.LieType.Steinberg.RankTwo
