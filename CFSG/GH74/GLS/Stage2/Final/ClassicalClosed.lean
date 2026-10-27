module

public import CFSG.GH74.GLS.Stage1.Main.Out

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec7

@[expose] def IsClassicalModel (Gs : Type) [Group Gs] (p f : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧
    (LieModel Gs .PSp 2 p f ∨ (p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨
      (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f))

@[expose] def ModelCenter : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), IsClassicalModel Gs p f → ∀ S' : Sylow 2 Gs,
    ∃ z' : Gs, orderOf z' = 2 ∧
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z'

@[expose] def ModelOddCore : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ) (S' : Sylow 2 Gs) (z' : Gs), IsClassicalModel Gs p f →
    orderOf z' = 2 → (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
      (p ^ f % 8 ≠ 1 → LieModel Gs .PSL 4 p f →
        Nat.card ↥(pPrimeCore 2 ↥(centralizer ({z'} : Set Gs))) = ordCompl[2] (p ^ f - 1)) ∧
      (p ^ f % 8 ≠ 7 → LieModel Gs .PSU 4 p f →
        Nat.card ↥(pPrimeCore 2 ↥(centralizer ({z'} : Set Gs))) = ordCompl[2] (p ^ f + 1))

@[expose] def ModelOneClass : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), p.Prime → p ≠ 2 →
    ((p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ LieModel Gs .PSU 4 p f)) →
      ∀ u v : Gs, orderOf u = 2 → orderOf v = 2 → IsConj u v

@[expose] def ModelsDisjoint : Prop :=
  ∀ (Gs : Type) [Group Gs] (p f p' f' : ℕ), p.Prime → p ≠ 2 → p'.Prime → p' ≠ 2 →
    LieModel Gs .PSp 2 p f → ¬ LieModel Gs .PSL 4 p' f' ∧ ¬ LieModel Gs .PSU 4 p' f'

@[expose] def ModelLayerBar : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ) (S' : Sylow 2 Gs) (z' : Gs), IsClassicalModel Gs p f →
    (LieModel Gs .PSL 4 p f ∨ LieModel Gs .PSU 4 p f) → orderOf z' = 2 →
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
        layerTimesSylow z' (S' : Subgroup Gs) ⊓ OddCore z' = ⊥ ∧
          barOf z' (layerTimesSylow z' (S' : Subgroup Gs)) = oPrimeResidual 2 (CentralizerBar z')

end CFSG.GH74.GLS.Stage2.Final
