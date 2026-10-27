module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Reg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Adapt
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.GraphAux

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem graph_coset_false {L : Type} [Field L] [IsAlgClosed L]
    (a b : Fin Tag.E6.rank → Lˣ) (ha : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizer a) (hsh : rootChar a (e6Shift w) ≠ 1)
    {z : ModGL Tag.E6 L} (hz : ∃ g ∈ adjointGroup Tag.E6 L, z = g * graphP L)
    (hker : ∀ β, IsRoot Tag.E6 β → rootChar a β = 1 → ∀ c : L, Commute z (pinnedX Tag.E6 L β c))
    (hx : Commute z (rootDiagUnit Tag.E6 a))
    (hy : Commute z (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w)) :
    False := by
  obtain ⟨b₃, hker₃, hw₃, hsh₃⟩ := exists_triData a ha hw hsh
  obtain ⟨ℓ, hℓ, hℓ7, ζ, hζ, zv, hreg, hcomm⟩ := regular_witness (L := L) b₃ hw₃ hsh₃
  have ht₀ : Commute z (rootDiagUnit Tag.E6 fun j => ζ ^ zv j) :=
    hcomm z fun β hβ c => hker β ((hker₃ β).2 hβ).1 ((hker₃ β).2 hβ).2 c
  obtain ⟨g, hg, rfl⟩ := hz
  obtain ⟨u, c, rfl⟩ := GraphAux.exists_monomial_of_commute_regular hℓ hℓ7 hζ zv hreg hg ht₀
  have hmz : GraphAux.MapsRootLinesBy
      (canonicalRep (coxeterSystem Tag.E6) L u * rootDiagUnit Tag.E6 c * graphP L)
      (GraphAux.sigmaHom u GraphAux.rhoE6) :=
    (((GraphAux.mapsRootLinesBy_of_mapsRootLines (mapsRootLines_canonicalRep u)).mul
      (GraphAux.mapsRootLinesBy_rootDiagUnit c)).mul
      (GraphAux.mapsRootLinesBy_diagramMap TwistTag.E6)).congr fun _ => rfl
  have hmy : GraphAux.MapsRootLinesBy
      (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) (w • ·) :=
    ((GraphAux.mapsRootLinesBy_rootDiagUnit b).mul
      (GraphAux.mapsRootLinesBy_of_mapsRootLines (mapsRootLines_canonicalRep w))).congr
      fun _ => rfl
  exact hsh (GraphAux.rootChar_e6Shift_eq_one ha hw u
    (GraphAux.sigmaHom_smul_comm_of_commute hmz hmy hy)
    (GraphAux.rootChar_sigmaHom_of_commute hmz hx))

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
