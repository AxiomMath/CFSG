module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Cfg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

namespace KD309

@[expose] def restrictRep {Y V : Type} [Group Y] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Y V) (H : Subgroup Y) (U : Submodule (ZMod 2) V)
    (hU : ∀ g ∈ H, ∀ u ∈ U, ρ g u ∈ U) : Representation (ZMod 2) H U where
  toFun g := (ρ (g : Y)).restrict (fun u hu => hU g g.2 u hu)
  map_one' := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp
  map_mul' a b := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp

end KD309

@[expose] def KD309LieOrder : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 5 Y) (x z : Y), Plane63 5 Y P x z →
    ∀ L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L) →
      I291P65.Is29a ↥L → Nat.card (P : Subgroup Y) ≤ 5 ^ 6 → Nat.card (P : Subgroup Y) ≤ 5 ^ 5

@[expose] def KD309LieMono : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 5 Y) (x z : Y), Plane63 5 Y P x z →
    ∀ L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L) →
      I291P65.Is29a ↥L → Nat.card (P : Subgroup Y) = 5 ^ 5 →
      ∃ (J : Subgroup Y) (n g h : Y), KD309Cfg (P : Subgroup Y) z J n g h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
