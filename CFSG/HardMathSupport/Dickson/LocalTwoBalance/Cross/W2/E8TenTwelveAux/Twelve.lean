module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveRigid
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveD4Order
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_adjointE8_twelve (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 12) :
    InnerPlaneBalance p (adjointGroup Tag.E8 K) := by
  classical
  obtain ⟨ℓ, f, hℓ, hcharK, hf, hK⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hcharK
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hp7', -, hΦ, -⟩ := e8Twelve_arith hp hp7 he
  obtain ⟨F⟩ := exists_e8TwelveFrame K hf hK hp hp7 he L
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8) :=
    not_dvd_card_weylGroup_E hp hp7' (Or.inr (Or.inr rfl))
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hexist : E8TwelveOrderP F := fun ζ hζ c hc =>
    e8T12_exists_order_p_mem_D4 hp hp7' hζ hFr hΦ F.hT hc
  exact innerPlaneBalance_adjointE8_of_rigid hf hK hp hordW F.n F.g0 F.hg0C F.hg0 F.hperf F.hconj
    e8T12Basis e8T12Basis_root e8T12Basis_span fun b hbT hap hb1 hβ =>
      e8Twelve_rigid hf hK hp hp7' hΦ F hexist b hbT hap hb1 hβ

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
