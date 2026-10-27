module

public import CFSG.GH74.GLS.Stage4.HexQuotient
public import CFSG.GH74.GLS.Stage4.Statements
public import CFSG.LieType.Steinberg.G2.Perfect

public noncomputable section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.GH74.GLS.Stage4.Hex

variable (F : Type) [Field F]

theorem g2Data :
    G2Data (rootGroup (rootOperatorFamily .G2) F)
    (weylElement .G2 F) (torus (τ := .G2) F) where
  ct := g2_isCTGroupDatum F
  ext := g2_steinbergExtras F
  bruhat := g2_bruhatExtras F
  comm := g2_rootGroupCommutators F

abbrev g2Roots
    : (Fin 2 → ℤ) → Subgroup ↥(adjointGroup .G2 F) :=
  rootGroup (rootOperatorFamily .G2) F

theorem g2RGD2
    : RGD2 6 (⨆ i, torus (τ := .G2) F i) (weylElement .G2 F (1 : Fin 2))
    (weylElement .G2 F (0 : Fin 2)) (posUnipotent (g2Shape (g2Roots F))) (hexGroup (g2Roots F)) :=
  hexRGD2 (g2Data F)

variable {F}

theorem isSimpleGroup_g2Model
    (hF : 3 ≤ Nat.card F) : IsSimpleGroup (AdjointQuotient .G2 F) :=
  (isQuasisimple_g2_of_three_le_card F hF).2.1

@[expose] def g2ModelSystem
    (F : Type) [Field F] (hF : 3 ≤ Nat.card F) :
    RankTwoSystem (AdjointQuotient .G2 F) 6 :=
  haveI := isSimpleGroup_g2Model hF
  hexQuotSystem (g2Data F)

theorem g2ModelSystem_root
    (hF : 3 ≤ Nat.card F) (i : ℤ) :
    (g2ModelSystem F hF).root i = (hexGroup (g2Roots F) i).map (hexProj ↥(adjointGroup .G2 F)) :=
  rfl

theorem g2ModelSystem_U
    (hF : 3 ≤ Nat.card F) :
    (g2ModelSystem F hF).U = (posUnipotent (g2Shape (g2Roots F))).map (hexProj ↥(adjointGroup .G2 F)) :=
  rfl

theorem card_g2Roots
    {γ : Fin 2 → ℤ} (hγ : IsRoot .G2 γ) : Nat.card (g2Roots F γ) = Nat.card F := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun c : F => (⟨xPar (rootOperatorFamily .G2) γ c,
    xPar_mem hγ c⟩ : g2Roots F γ)) ⟨fun c d h => xPar_injective hγ (congrArg Subtype.val h), ?_⟩)
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
  exact ⟨c, rfl⟩

theorem card_g2ModelSystem_root
    (hF : 3 ≤ Nat.card F) {i : ℤ} (h1 : 1 ≤ i) (h6 : i ≤ 6) :
    Nat.card ((g2ModelSystem F hF).root i) = Nat.card F := by
  rw [g2ModelSystem_root]
  rw [card_hexQuotGroup (g2Data F) h1 h6]
  exact card_g2Roots (isRoot_hexPos (by omega) (by omega))

theorem g2Model_rootOrders
    (hF : 3 ≤ Nat.card F) :
    RootOrdersG2 (g2ModelSystem F hF).root (Nat.card F) :=
  fun _ h1 h6 => card_g2ModelSystem_root hF h1 h6

end CFSG.GH74.GLS.Stage4.Hex
