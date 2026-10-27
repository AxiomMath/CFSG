module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

@[expose] def IVK_1_4j_lifted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), HasSL2Model (HatT K) Odd →
      ∀ s ∈ S, s ∈ normalizer (K : Set G) → (∀ p ∈ Pof S K, s * p = p * s) → s ∈ cSec K

@[expose] def IV2_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T P₁ P₂ Q₁ Q₂ U : Subgroup G) (z : G),
    IsPGroup 2 ↥T → T = P₁ ⊔ P₂ ⊔ U → T = Q₂ ⊔ Q₁ →
    (∀ x ∈ T, ∀ y ∈ Q₁, x * y * x⁻¹ ∈ Q₁) → (∀ x ∈ T, ∀ y ∈ Q₂, x * y * x⁻¹ ∈ Q₂) →
    IVK.IsQuaternionTwoGroup ↥Q₁ 4 → IVK.IsQuaternionTwoGroup ↥Q₂ 4 →
    Q₁ ⊓ Q₂ = zpowers z → (center ↥Q₁).map Q₁.subtype = zpowers z →
    (center ↥Q₂).map Q₂.subtype = zpowers z →
    IVK.IsQuaternionTwoGroup ↥P₁ 3 → IVK.IsQuaternionTwoGroup ↥P₂ 3 → P₂ ≤ Q₁ → P₁ ≤ Q₂ →
    Q₁ = T ⊓ centralizer (P₁ : Set G) → Q₂ = T ⊓ centralizer (P₂ : Set G) →
    IVK.IsFourSubgroup U → (P₁ ⊔ P₂) ⊓ U = ⊥ →
      ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a

@[expose] def IG_10_32_P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ x ∈ S, orderOf x = 2 → Interchanges x K₁ K₂ →
      ∀ v : G, v * x⁻¹ ∈ Pz S z → orderOf v = 2 →
        ∃ c ∈ Pz S z, c * x * c⁻¹ = v ∨ c * (x * z) * c⁻¹ = v

@[expose] def IVK_1_2d_lifted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (q : ℕ), Std4 G z S K₁ K₂ →
    Odd q → ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), HatSL2 K q →
      ∀ w ∈ S, orderOf w = 2 → w ∈ normalizer (K : Set G) → ¬ InducesInner w K → ¬ InducesFAut w K →
        ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Nat.card Fq = q ∧ PGLQuot z w K Fq

@[expose] def IVK_3_1c_lifted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) (w : G),
    Cfg7 G z S K₁ K₂ t u q → Concl72abcf z S K₁ K₂ t q w → w ≠ 1 →
      ∀ x ∈ S, ∀ x' ∈ S, x * w⁻¹ ∈ Pz S z → x' * w⁻¹ ∈ Pz S z → orderOf x = 2 → orderOf x' = 2 →
        ∃ c ∈ Cz z, c * x * c⁻¹ = x'

@[expose] def L76_struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q → (Pz S z).relIndex (S1 S K₁) = 2 →
      ∀ D : Subgroup G, Data74 z S K₁ K₂ t D → (∃ n, IVK.IsSemidihedralTwoGroup ↥D n) →
        16 ≤ Nat.card ↥(Pof S K₁) →
          ∃ u₁ ∈ Pof S K₁, u₁ * u₁ = z ∧
            (∀ s ∈ S1 S K₁, s * u₁ * s⁻¹ = u₁ ∨ s * u₁ * s⁻¹ = u₁⁻¹) ∧
            (center ↥D).map D.subtype = zpowers (u₁ * (t * u₁ * t⁻¹)) ∧
            (∃ y ∈ D, y ∉ Pz S z ∧ y * y = u₁ * (t * u₁ * t⁻¹) ∧ y * u₁ * y⁻¹ = u₁⁻¹) ∧
            (∀ x ∈ S, orderOf x = 2 → x ∈ Pz S z ⊔ zpowers t)

@[expose] def L77_no_conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
    Cfg7 G z S K₁ K₂ t u q → (Pz S z).relIndex (S1 S K₁) = 2 →
      ∀ D : Subgroup G, Data74 z S K₁ K₂ t D → (∃ n, IVK.IsSemidihedralTwoGroup ↥D n) →
        16 ≤ Nat.card ↥(Pof S K₁) →
          ∀ d₀ y : G, (center ↥D).map D.subtype = zpowers d₀ → y ∈ D → y ∉ Pz S z → y * y = d₀ →
            ∀ t₁ ∈ ({t, z * d₀ * t} : Set G), ∀ y₁ ∈ ({y, y * z} : Set G), ∀ h : G,
              h⁻¹ * t₁ * h = z → h⁻¹ * y₁ * h ∉ Pz S z

@[expose] def L79_C_S_u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) (w : G),
    Cfg7 G z S K₁ K₂ t u q → Concl72abcf z S K₁ K₂ t q w → w ≠ 1 →
      ∀ x : G, IsConj (t * z) x → ∀ V : Subgroup G,
        CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.Syl2In V (centralizer ({x} : Set G)) →
        ∃ (V₁ V₂ : Subgroup G) (n : ℕ), 3 ≤ n ∧ V₁ ≤ V ∧ V₂ ≤ V ∧
          (∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) ∧ V₁ ⊓ V₂ = ⊥ ∧ V₁ ⊔ V₂ = V ∧
          IVK.IsDihedralTwoGroup ↥V₁ n ∧ IVK.IsDihedralTwoGroup ↥V₂ n ∧ x ∈ V₁ ∧ ∀ a ∈ V₁, a * x = x * a

@[expose] def IVK_4_10_supp : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), Odd q → 5 ≤ q → IVK.IsSp4L4U4 K q →
    ∀ (z' : K) (S' : Sylow 2 K) (t' w' : K) (E₁ E₂ : Subgroup K), orderOf z' = 2 →
      (∀ x ∈ (S' : Subgroup K), x * z' = z' * x) → z' ∈ (S' : Subgroup K) →
      Dat410 q z' (S' : Subgroup K) t' w' E₁ E₂ → w' ≠ 1 → ¬ IsConj z' (t' * w' * z')

@[expose] def IVK_Y_unique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) (w : G),
    Cfg7 G z S K₁ K₂ t u q → Concl72abcf z S K₁ K₂ t q w →
      ∀ (Gs : Type) [Group Gs] [Finite Gs] (z' : Gs) (S' : Sylow 2 Gs) (t' w' : Gs)
        (E₁ E₂ : Subgroup Gs), Model7 Gs q (w = 1) → orderOf z' = 2 →
        (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
        Dat410 q z' (S' : Subgroup Gs) t' w' E₁ E₂ → (w' = 1 ↔ w = 1) →
          PsiData7 z (K₁ ⊔ K₂ ⊔ S) S (Pz S z) t w (IVK.Ez z') (S' : Subgroup Gs) t' w'

@[expose] def C1_eq_KS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) (w : G),
    Cfg7 G z S K₁ K₂ t u q → Concl72abcf z S K₁ K₂ t q w →
      oPrimeResidual 2 (CentralizerBar z) =
        ((K₁ ⊔ K₂ ⊔ S).subgroupOf (centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))))

@[expose] def IVK_PSp4_ne_LU : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), IVK.IsPSp4 K q →
    ¬ IVK.IsLnEps 4 K 1 q ∧ ¬ IVK.IsLnEps 4 K (-1) q

@[expose] def L711_inspection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) (w : G),
    Cfg7 G z S K₁ K₂ t u q → Concl72abcf z S K₁ K₂ t q w → Concl72de z t u w →
      ∀ E : Subgroup G, E ≤ S ⊓ pLayerOf 2 ((K₁ ⊔ K₂) ⊓ centralizer ({t} : Set G)) →
        IVK.IsFourSubgroup E →
          (IsElementaryAbelian 2 ↥(E ⊔ zpowers t ⊔ zpowers z) ∧
            Nat.card ↥(E ⊔ zpowers t ⊔ zpowers z) = 16) ∧
          ∃ Ω : Finset G, (∀ a : G, a ∈ Ω ↔ (a ∈ E ⊔ zpowers t ⊔ zpowers z ∧ IsConj z a)) ∧ Ω.card = 5 ∧
            Subgroup.closure (Ω : Set G) = E ⊔ zpowers t ⊔ zpowers z ∧
            (∀ a ∈ Ω, ∀ b ∈ Ω, ∀ c ∈ Ω, ∀ d ∈ Ω, a ≠ b → c ≠ d →
              ∃ n ∈ normalizer ((E ⊔ zpowers t ⊔ zpowers z : Subgroup G) : Set G),
                n * a * n⁻¹ = c ∧ n * b * n⁻¹ = d) ∧
            (Nat.card ↥S = 2 ^ 6 →
              (centralizer ((E ⊔ zpowers t ⊔ zpowers z : Subgroup G) : Set G)).relIndex
                (normalizer ((E ⊔ zpowers t ⊔ zpowers z : Subgroup G) : Set G) ⊓
                  centralizer ({z, t} : Set G)) = 3) ∧
            (2 ^ 6 < Nat.card ↥S →
              (centralizer ((E ⊔ zpowers t ⊔ zpowers z : Subgroup G) : Set G)).relIndex
                (normalizer ((E ⊔ zpowers t ⊔ zpowers z : Subgroup G) : Set G) ⊓
                  centralizer ({z, t} : Set G)) = 6)

@[expose] def Quat_mod_center : Prop :=
  ∀ (G : Type) [Group G] (P : Subgroup G) (z : G) (n : ℕ), IVK.IsQuaternionTwoGroup ↥P n → z ∈ P →
    orderOf z = 2 →
      ∃ _ : ((zpowers z).subgroupOf P).Normal,
        IVK.IsDihedralOrder (↥P ⧸ (zpowers z).subgroupOf P) (2 ^ (n - 1))

@[expose] def Dih_index2_invol : Prop :=
  ∀ (G : Type) [Group G] (D M : Subgroup G) (n : ℕ), M ≤ D → M.relIndex D = 2 →
    IVK.IsDihedralTwoGroup ↥D n → (∃ m, IVK.IsDihedralOrder ↥M m) →
      ∃ y ∈ D, y ∉ M ∧ orderOf y = 2

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
