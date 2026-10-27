module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.Adapters.CatalogueFieldBridges.Symplectic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3ResidualQ
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open
open CFSG.HardMathSupport.Timmesfeld.CrossChar (primePower_p_eq_two_of_card_eq_two)

@[expose] def SpOneBlock : Prop :=
  ∀ (n : ℕ) (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (Bb : Subgroup (StatedSp n (ZMod 2))),
    SmallModel (StatedSp n (ZMod 2)) Bb →
      ∃ y ∈ Bb, y ≠ 1 ∧ StdAt Bb y ∧
        Nonempty (↥(GLALayer (Subgroup.centralizer ({y} : Set (StatedSp n (ZMod 2))))) ≃*
          StatedSp (n - 1) (ZMod 2))

theorem nonempty_mulEquiv_lie_statedSp (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n q).Valid) (hq : q.card = 2) (hn : 3 ≤ n) :
    Nonempty ((TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group ≃*
      StatedSp n (ZMod 2)) := by
  have hq2 : q.p = 2 := primePower_p_eq_two_of_card_eq_two hq
  have hk : Nat.card (ZMod 2) = q.card := by rw [Nat.card_zmod, hq]
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
    hv hq2 hn (k := ZMod 2) hk
  exact ⟨e.symm.trans
    (CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := ZMod 2) (by omega : 1 ≤ n))⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
