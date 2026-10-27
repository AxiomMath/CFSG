module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.IVK.Statements.Sec4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section Notation

variable {G : Type} [Group G]

@[expose] def HatSL2 (K : Subgroup G) (q : ℕ) : Prop := HasSL2Model (HatT K) (fun r => r = q)

@[expose] def IsHalfTwoCentral (x : G) : Prop :=
  ∃ T : Sylow 2 G, x ∈ (T : Subgroup G) ∧
    ((T : Subgroup G) ⊓ centralizer ({x} : Set G)).relIndex (T : Subgroup G) ≤ 2

@[expose] def QuotEquiv7 (X N D : Subgroup G) : Prop :=
  ∃ _ : (N.subgroupOf X).Normal, Nonempty ((↥X ⧸ N.subgroupOf X) ≃* ↥D)

@[expose] def Ysub (t w : G) : Subgroup G := zpowers t ⊔ zpowers w

end Notation

@[expose] def Concl66 {G : Type} [Group G] (z : G) (S K₁ K₂ : Subgroup G) : Prop :=
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

structure Std7 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) : Prop where
  std : Std4 G z S K₁ K₂
  a₁ : Cond6a S K₁
  a₂ : Cond6a S K₂
  b₁ : Cond6b S K₁
  b₂ : Cond6b S K₂
  d₁ : ¬ IsDoubleCoverOfAlt (HatT K₁) 7
  d₂ : ¬ IsDoubleCoverOfAlt (HatT K₂) 7
  hQ : Qz S z = zpowers z
  p66 : Concl66 z S K₁ K₂
  nonfused : ∀ u ∈ Pz S z, IsConj z u → u = z

structure Choice7 (G : Type) [Group G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) : Prop where
  t_mem : t ∈ S
  t_conj : IsConj z t
  t_ne : t ≠ z
  t_swap : Interchanges t K₁ K₂
  t_fus : ∀ x ∈ Pz S z, orderOf x = 2 → x ≠ z → IsConj (t * z) x
  tz_ne : ¬ IsConj z (t * z)
  u_mem : u ∈ Pz S z
  u_ord : orderOf u = 2
  u_ne : u ≠ z
  u_norm : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z
  q_odd : Odd q
  q_ge : 5 ≤ q
  hq₁ : HatSL2 K₁ q
  hq₂ : HatSL2 K₂ q

structure Cfg7 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ) :
    Prop where
  std : Std7 G z S K₁ K₂
  ch : Choice7 G z S K₁ K₂ t u q

@[expose] def Concl72abcf {G : Type} [Group G] (z : G) (S K₁ K₂ : Subgroup G) (t : G) (q : ℕ) (w : G) :
    Prop :=
  w ∈ S ∧ (w = 1 ∨ orderOf w = 2) ∧ t * w = w * t ∧
    (Pz S z ⊓ Ysub t w = ⊥ ∧ S = Pz S z ⊔ Ysub t w) ∧
    S1 S K₁ = Pz S z ⊔ zpowers w ∧ Interchanges t K₁ K₂ ∧
    (w ≠ 1 → ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)),
      ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Nat.card Fq = q ∧ PGLQuot z w K Fq)

@[expose] def Concl72de {G : Type} [Group G] (z : G) (t u : G) (w : G) : Prop :=
  (IsConj z t ∧ IsConj z (t * w)) ∧ (IsConj u (t * z) ∧ IsConj u (t * w * z)) ∧ (w ≠ 1 → IsConj z w)

structure Data74 {G : Type} [Group G] (z : G) (S K₁ K₂ : Subgroup G) (t : G) (D : Subgroup G) : Prop where
  le : D ≤ S1 S K₁
  prod : IsInternalDirectProduct (zpowers z ⊔ zpowers t) D (S ⊓ centralizer ({t} : Set G))
  quot : QuotEquiv7 (S1 S K₁) (Pof S K₁) D
  dih_or_sd : (∃ n, IVK.IsDihedralTwoGroup ↥D n) ∨ ∃ n, IVK.IsSemidihedralTwoGroup ↥D n
  inter_dih : ∃ n, IVK.IsDihedralOrder ↥(D ⊓ Pz S z) n
  index_eq : (D ⊓ Pz S z).relIndex D = (Pz S z).relIndex (S1 S K₁)

@[expose] def Model7 (Gs : Type) [Group Gs] (q : ℕ) (w1 : Prop) : Prop :=
  (w1 ∧ IVK.IsPSp4 Gs q) ∨
    (¬ w1 ∧ ((q % 4 = 3 ∧ IVK.IsLnEps 4 Gs 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 Gs (-1) q)))

@[expose] def Compat7 {G : Type} [Group G] (z : G) (X S : Subgroup G) {Gs : Type} [Group Gs]
    (E S' : Subgroup Gs) : Prop :=
  ∃ _ : ((Oz z).subgroupOf X).Normal,
    ∃ ψ : (↥X ⧸ (Oz z).subgroupOf X) ≃* ↥(E ⊔ S'),
      (∀ s : ↥X, (s : G) ∈ S → (ψ (QuotientGroup.mk s) : Gs) ∈ S') ∧
      (∀ a : ↥X ⧸ (Oz z).subgroupOf X, (ψ a : Gs) ∈ S' →
        ∃ s : ↥X, (s : G) ∈ S ∧ (QuotientGroup.mk s : ↥X ⧸ (Oz z).subgroupOf X) = a) ∧
      (∀ u v : ↥X, (u : G) ∈ S → (v : G) ∈ S → orderOf (u : G) = 2 → orderOf (v : G) = 2 →
        (IsConj (u : G) (v : G) ↔
          IsConj (ψ (QuotientGroup.mk u) : Gs) (ψ (QuotientGroup.mk v) : Gs)))

@[expose] def Term7 {G : Type} [Group G] (z : G) (S K₁ K₂ : Subgroup G) (q : ℕ) (w : G) : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (z' : Gs) (S' : Sylow 2 Gs),
    Model7 Gs q (w = 1) → orderOf z' = 2 →
    (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
      Compat7 z (K₁ ⊔ K₂ ⊔ S) S (IVK.Ez z') (S' : Subgroup Gs)

structure Dat410 {Gs : Type} [Group Gs] (q : ℕ) (z' : Gs) (S' : Subgroup Gs) (t' w' : Gs)
    (E₁ E₂ : Subgroup Gs) : Prop where
  t_mem : t' ∈ S'
  w_mem : w' ∈ S'
  t_ord : orderOf t' = 2
  w_ord : w' = 1 ∨ orderOf w' = 2
  comm : t' * w' = w' * t'
  prod : S' = (S' ⊓ IVK.Ez z') ⊔ zpowers t' ⊔ zpowers w'
  inter : IVK.Ez z' ⊓ (zpowers t' ⊔ zpowers w') = ⊥
  t_conj : IsConj z' t'
  Ez_eq : IVK.Ez z' = E₁ ⊔ E₂
  E₂_eq : E₂ = E₁.map (MulAut.conj t').toMonoidHom
  sl2 : HasSL2Model ↥E₁ (fun r => r = q)
  inter_E : E₁ ⊓ E₂ = zpowers z'
  comm_E : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a
  norm_E : normalizer (E₁ : Set Gs) ⊓ S' = (S' ⊓ IVK.Ez z') ⊔ zpowers w'
  classes : ∀ x : Gs, orderOf x = 2 → IsConj z' x ∨ IsConj (t' * z') x
  tz_ne : ¬ IsConj z' (t' * z')
  E_fus : ∀ x ∈ IVK.Ez z', orderOf x = 2 → x ≠ z' → IsConj (t' * z') x
  pgl : w' ≠ 1 → ∀ Ei ∈ ({E₁, E₂} : Set (Subgroup Gs)),
    ∃ _ : ((zpowers z').subgroupOf (Ei ⊔ zpowers w')).Normal,
      IVK.IsPGL2 (↥(Ei ⊔ zpowers w') ⧸ (zpowers z').subgroupOf (Ei ⊔ zpowers w')) (fun r => r = q)
  w_fus : w' ≠ 1 → IsConj z' (t' * w') ∧
    ∀ x ∈ S' ⊓ IVK.Ez z', orderOf (x * w') = 2 → IsConj z' (x * w')

@[expose] def PsiData7 {G : Type} [Group G] (z : G) (X S P : Subgroup G) (t w : G) {Gs : Type} [Group Gs]
    (E S' : Subgroup Gs) (t' w' : Gs) : Prop :=
  ∃ _ : ((Oz z).subgroupOf X).Normal,
    ∃ ψ : (↥X ⧸ (Oz z).subgroupOf X) ≃* ↥(E ⊔ S'),
      ((∀ s : ↥X, (s : G) ∈ S → (ψ (QuotientGroup.mk s) : Gs) ∈ S') ∧
        (∀ a : ↥X ⧸ (Oz z).subgroupOf X, (ψ a : Gs) ∈ S' →
          ∃ s : ↥X, (s : G) ∈ S ∧ (QuotientGroup.mk s : ↥X ⧸ (Oz z).subgroupOf X) = a)) ∧
      ((∀ s : ↥X, (s : G) ∈ P → (ψ (QuotientGroup.mk s) : Gs) ∈ E) ∧
        (∀ a : ↥X ⧸ (Oz z).subgroupOf X, (ψ a : Gs) ∈ E → (ψ a : Gs) ∈ S' →
          ∃ s : ↥X, (s : G) ∈ P ∧ (QuotientGroup.mk s : ↥X ⧸ (Oz z).subgroupOf X) = a)) ∧
      (∀ s : ↥X, (s : G) = t → (ψ (QuotientGroup.mk s) : Gs) = t') ∧
      (∀ s : ↥X, (s : G) = w → (ψ (QuotientGroup.mk s) : Gs) = w')

@[expose] def NormIso7 {X : Type} [Group X] (A : Subgroup X) (Y : Type) [Group Y] : Prop :=
  ∃ _ : ((centralizer (A : Set X)).subgroupOf (normalizer (A : Set X))).Normal,
    Nonempty ((↥(normalizer (A : Set X)) ⧸
      (centralizer (A : Set X)).subgroupOf (normalizer (A : Set X))) ≃* Y)

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
