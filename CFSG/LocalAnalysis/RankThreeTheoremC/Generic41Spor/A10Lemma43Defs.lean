module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

structure A10YData (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x t₁ t₂ : Y) (J₁ J₂ F : Subgroup Y) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections Y
  core : primeComplementCore (G := Y) 5 = ⊥
  sylow : ∃ S : Sylow 5 Y, (S : Subgroup Y) = P
  rank : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 3
  P_comm : IsMulCommutative P
  x_mem : x ∈ P
  x_ord : orderOf x = 5
  t₁_mem : t₁ ∈ P ⊓ J₁
  t₂_mem : t₂ ∈ P ⊓ J₂
  t₁_ord : orderOf t₁ = 5
  t₂_ord : orderOf t₂ = 5
  x_not_mem : x ∉ zpowers t₁ ⊔ zpowers t₂
  t₁_not_mem : t₁ ∉ zpowers t₂
  comp₁ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) J₁
  comp₂ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) J₂
  ne : J₁ ≠ J₂
  layer : GLAPLayer 5 (Subgroup.centralizer ({x} : Set Y)) = J₁ ⊔ J₂
  A5₁ : Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5))
  A5₂ : Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5))
  F_le : F ≤ Subgroup.centralizer ({x} : Set Y)
  F_norm : ∀ f ∈ F, ∀ t ∈ zpowers t₁ ⊔ zpowers t₂, f * t * f⁻¹ ∈ zpowers t₁ ⊔ zpowers t₂
  F_irr : ∀ A : Subgroup Y, A ≤ zpowers t₁ ⊔ zpowers t₂ → (∀ f ∈ F, ∀ a ∈ A, f * a * f⁻¹ ∈ A) →
    A = ⊥ ∨ A = zpowers t₁ ⊔ zpowers t₂
  F_fix : ∀ t ∈ zpowers t₁ ⊔ zpowers t₂, (∀ f ∈ F, f * t * f⁻¹ = t) → t = 1
  F_swap : ∃ f ∈ F, J₁.map (MulAut.conj f).toMonoidHom = J₂ ∧
    (zpowers t₁).map (MulAut.conj f).toMonoidHom = zpowers t₂
  fusion : ∀ y : Y, (zpowers x).map (MulAut.conj y).toMonoidHom ≤ P →
    (zpowers x).map (MulAut.conj y).toMonoidHom = zpowers x ∨
      (zpowers x).map (MulAut.conj y).toMonoidHom = zpowers t₁ ∨
      (zpowers x).map (MulAut.conj y).toMonoidHom = zpowers t₂

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
