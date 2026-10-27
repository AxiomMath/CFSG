module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeModelBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open CFSG.Open CFSG.AGLEmbedding CFSG.EvenSmallLie.OmegaEightMinus

structure FrameProps {G : Type*} [Group G] (ν : G → ℕ) (s : ℕ) (R J : Subgroup G) : Prop where
  one_ne : ν 1 ≠ s
  ncard_eq : {x : G | x ∈ J ∧ ν x = s}.ncard = 6
  le_closure : J ≤ Subgroup.closure {x : G | x ∈ J ∧ ν x = s}
  sep : ∀ x ∈ J, x ≠ 1 → ν x ≠ s → ∃ m : Fin 4 → G,
    (∀ k, m k ∈ R ∧ m k ∈ Subgroup.normalizer (J : Set G)) ∧
    ∀ k l, k ≠ l → m k * x * (m k)⁻¹ ≠ m l * x * (m l)⁻¹ ∧
      m k * x * (m k)⁻¹ ≠ m l * x⁻¹ * (m l)⁻¹
  simple : ∀ x ∈ J, ν x = s → ∃ W : Subgroup G, W ≤ R ⊓ Subgroup.centralizer ({x} : Set G) ∧
    IsSimpleGroup W ∧ (∃ a b : W, a * b ≠ b * a) ∧ 3 ∣ Nat.card W

structure Omega8FrameModel : Prop where
  card : Nat.card omegaT = 197406720
  frame : ∃ J₀ T₀ : Subgroup (Equiv.Perm (Fin 136)), J₀ ≤ T₀ ∧ T₀ ≤ omegaT ∧
    Nat.card T₀ = 81 ∧ IsElemAbelian 3 J₀ ∧ Nat.card J₀ = 27 ∧
    (∀ J' : Subgroup (Equiv.Perm (Fin 136)), J' ≤ T₀ → IsElemAbelian 3 J' →
      Nat.card J' = 27 → J' = J₀) ∧
    FrameProps (fun g : Equiv.Perm (Fin 136) => g.support.card) 108 omegaT J₀
  aut : ∀ (α : MulAut omegaT) (z : omegaT),
    ((α z : omegaT) : Equiv.Perm (Fin 136)).support.card = (z : Equiv.Perm (Fin 136)).support.card
  bridge : ∀ (L : Type) [Group L] (d : TauCeti.ValidLieTypeIndex), IsOmegaMinusTwoIndex 4 d →
    Nonempty (L ≃* CatGroup d) → Nonempty (L ≃* omegaT)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
