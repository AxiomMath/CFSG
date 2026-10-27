module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSporJ1
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SporKL (s : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], NativeSporadic.IsSporadic Y s →
    ∀ (p : ℕ) (α : MulAut Y) (Xh : Subgroup Y), QuotCfg p α Xh → False

theorem isMulCommutative_of_card_le_two {Γ : Type*} [Group Γ] [Finite Γ] (h : Nat.card Γ ≤ 2) :
    IsMulCommutative Γ := by
  rcases Nat.lt_or_ge (Nat.card Γ) 2 with h1 | h2
  · have : Nat.card Γ = 1 := le_antisymm (by omega) Nat.card_pos
    have : Subsingleton Γ := Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have hc : Nat.card Γ = 2 := le_antisymm h h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic Γ := isCyclic_of_prime_card hc
    exact ⟨⟨fun a b => (IsCyclic.commGroup (α := Γ)).mul_comm a b⟩⟩

theorem cell87_FSpor
    (hM11 : SporKL .M11) (hM12 : SporKL .M12) (hM22 : SporKL .M22) (hM23 : SporKL .M23)
    (hJ2 : SporKL .J2) (hJ3 : SporKL .J3) : Cell87 FSpor := by
  refine cell87_of_quot (F := FSpor) ?_ ?_
  · intro Y _ _ hY
    rcases hY with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact outAbelian_of_mulEquiv e.symm
        (outAbelian_of_outer_comm CFSG.Sporadic.Schreier.at_m11_schreier.2.1)
    · exact outAbelian_of_mulEquiv e.symm
        (outAbelian_of_outer_comm CFSG.Sporadic.Schreier.at_m12_schreier.2.1)
    · exact outAbelian_of_mulEquiv e.symm
        (outAbelian_of_outer_comm CFSG.Sporadic.Schreier.at_m22_schreier.2.1)
    · exact outAbelian_of_mulEquiv e.symm
        (outAbelian_of_outer_comm CFSG.Sporadic.Schreier.at_m23_schreier.2.1)
    · exact outAbelian_of_mulEquiv e.symm
        (outAbelian_of_inner_top CFSG.Sporadic.Schreier.at_j1_schreier.2.1)
    · exact outAbelian_of_mulEquiv e.symm
        (outAbelian_of_outer_comm CFSG.Sporadic.Schreier.AT_J2_Schreier.2.1)
    · have hfin : Finite CFSG.Sporadic.Schreier.j3P := inferInstance
      have hfin' : Finite (Outer CFSG.Sporadic.Schreier.j3P) := by
        have : Finite (MulAut CFSG.Sporadic.Schreier.j3P) :=
          Finite.of_injective (fun f : MulAut CFSG.Sporadic.Schreier.j3P =>
            (f : CFSG.Sporadic.Schreier.j3P → CFSG.Sporadic.Schreier.j3P))
            fun f g h => MulEquiv.ext (congrFun h)
        infer_instance
      have hcard : Nat.card (Outer CFSG.Sporadic.Schreier.j3P) ≤ 2 :=
        CFSG.Sporadic.SmallOddCore.j3_outer_card_le
      exact outAbelian_of_mulEquiv (e.trans CFSG.Sporadic.Schreier.j3PermEquiv).symm
        (outAbelian_of_outer_comm (isMulCommutative_of_card_le_two hcard))
  · intro Y _ _ hY p α Xh h
    rcases hY with h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact hM11 Y h1 p α Xh h
    · exact hM12 Y h2 p α Xh h
    · exact hM22 Y h3 p α Xh h
    · exact hM23 Y h4 p α Xh h
    · exact noQuotCfg_J1 h5 h
    · exact hJ2 Y h6 p α Xh h
    · exact hJ3 Y h7 p α Xh h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
