module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

section Notation

variable {G : Type} [Group G]

@[expose] def Wsub (S U : Subgroup G) : Subgroup G := S ⊓ centralizer (U : Set G)

@[expose] def Vof (S K W : Subgroup G) : Subgroup G := W ⊓ Pof S K

@[expose] def Aof (S K₁ W₂ : Subgroup G) (h : G) : Subgroup G :=
  Vof S K₁ W₂ ⊔ conjugate (Vof S K₁ W₂) h

@[expose] def IsMaxCyc (W Q : Subgroup G) : Prop :=
  W ≤ Q ∧ IsCyclic ↥W ∧ ∀ C : Subgroup G, W ≤ C → C ≤ Q → IsCyclic ↥C → C = W

@[expose] def NormedBy (W X : Subgroup G) : Prop := ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W

end Notation

@[expose] def P66Concl {G : Type} [Group G] (z : G) (S K₁ K₂ : Subgroup G) : Prop :=
  ((∃ n, IVK.IsQuaternionTwoGroup ↥(Qof S K₁) n) ∧ (∃ n, IVK.IsQuaternionTwoGroup ↥(Qof S K₂) n) ∧
      (Pof S K₂).relIndex (Qof S K₁) ≤ 2 ∧ (Pof S K₁).relIndex (Qof S K₂) ≤ 2) ∧
    ((S1 S K₁).relIndex S ≤ 2 ∧ (Pz S z).relIndex (S1 S K₁) ≤ 4) ∧
    (∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∃ _ : ((Qof S K).subgroupOf (S1 S K₁)).Normal,
      (∃ n, IVK.IsDihedralTwoGroup (↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁)) n) ∨
      ∃ n, IVK.IsSemidihedralTwoGroup (↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁)) n) ∧
    ((Pz S z).relIndex (S1 S K₁) = 4 →
      (∃ _ : ((Pz S z).subgroupOf (S1 S K₁)).Normal,
        Nonempty ((↥(S1 S K₁) ⧸ (Pz S z).subgroupOf (S1 S K₁)) ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
      S1 S K₁ = Qof S K₁ ⊔ Qof S K₂)

structure Fused8 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) : Prop where
  std : Std4 G z S K₁ K₂
  a₁ : Cond6a S K₁
  a₂ : Cond6a S K₂
  b₁ : Cond6b S K₁
  b₂ : Cond6b S K₂
  d₁ : ¬ IsDoubleCoverOfAlt (HatT K₁) 7
  d₂ : ¬ IsDoubleCoverOfAlt (HatT K₂) 7
  hQ : Qz S z = zpowers z
  p66 : P66Concl z S K₁ K₂
  fused : ∃ u ∈ Pz S z, IsConj z u ∧ u ≠ z
  ord₁ : Nat.card ↥(Pof S K₂) ≤ Nat.card ↥(Pof S K₁)
  ord₂ : Nonempty (↥(Pof S K₁) ≃* ↥(Pof S K₂)) → Nat.card ↥(Qof S K₁) ≤ Nat.card ↥(Qof S K₂)

structure Setup8 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) :
    Prop where
  fused : Fused8 G z S K₁ K₂
  W₁_max : IsMaxCyc W₁ (Qof S K₁)
  W₂_max : IsMaxCyc W₂ (Qof S K₂)
  W₁_norm : NormedBy W₁ (S1 S K₁)
  W₂_norm : NormedBy W₂ (S1 S K₁)
  U_le : U ≤ W₁ ⊔ W₂
  U_four : IVK.IsFourSubgroup U
  U_norm : NormedBy U S
  z_mem : z ∈ U
  u_mem : u ∈ U
  u_ne : u ∉ zpowers z
  u_conj : IsConj z u
  h_norm : h ∈ normalizer (U : Set G)
  h_three : IsPGroup 3 ↥(zpowers h)
  h_move : h⁻¹ * z * h ≠ z
  h_W : h ∈ normalizer (Wsub S U : Set G)
  h_cube : ∀ w ∈ Wsub S U, h ^ 3 * w = w * h ^ 3
  h_prod : (S : Set G) * (zpowers h : Set G) = (zpowers h : Set G) * (S : Set G)

@[expose] def G2TermType (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  ∃ q : ℕ, (∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ p ^ f = q ∧
      LieModel Gs .G2 0 p f ∧ ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))) ∧
    (∀ v : G, orderOf v = 2 → IsConj z v) ∧
    HasSL2ProductOfIndexTwoStage1 (oPrimeResidual 2 (CentralizerBar z)) q

@[expose] def layerSBar {G : Type} [Group G] (z : G) (S : Subgroup G) : Subgroup (CentralizerBar z) :=
  layer (CentralizerBar z) ⊔
    (S.subgroupOf (centralizer ({z} : Set G))).map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))))

@[expose] def L4U4TermType (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  (∀ v : G, orderOf v = 2 → IsConj z v) ∧
  ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧
    ((p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ 3 < p ^ f ∧ LieModel Gs .PSU 4 p f)) ∧
    (∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))) ∧
    ∀ (z' : Gs) (S' : Sylow 2 ↥(centralizer ({z'} : Set Gs))), IsCentralInvolution z' →
      ∀ S'' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S'' : Subgroup Gs)) →
        (S'' : Subgroup Gs) = (S' : Subgroup ↥(centralizer ({z'} : Set Gs))).map
            (centralizer ({z'} : Set Gs)).subtype →
          Nonempty (↥(layerSBar z S) ≃* ↥(layerSBar z' (S'' : Subgroup Gs)))

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
