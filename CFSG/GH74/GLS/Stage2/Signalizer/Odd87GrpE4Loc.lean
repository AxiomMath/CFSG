module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSub
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecClosure

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Disj

variable {B : Type} [Group B] [Finite B]

@[expose] def C42a (p : ℕ) (z : B) (X K : Subgroup B) : Prop :=
  HasSL2Model ↥K (fun q => q = 5) ∧ Nat.card ↥X = 3 ∧ p = 3 ∧ X ≤ K ∧
    K ⊓ normalizer (X : Set B) ≤ X ⊔ K ⊓ centralizer ({z} : Set B)

@[expose] def C42b (p : ℕ) (z : B) (X K : Subgroup B) : Prop :=
  ∃ n : ℕ, 3 < p ^ n ∧ HasSL2Model ↥K (fun q => q = p ^ n) ∧ CFSG.ABGLocalTools.IsSylowOf p X K ∧
    K ⊓ normalizer (X : Set B) ≤ X ⊔ K ⊓ centralizer ({z} : Set B)

@[expose] def C42c (p : ℕ) (z : B) (X K : Subgroup B) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ LieModel ↥K .PSL 3 p n ∧ z ∈ K ⊔ centralizer (K : Set B) ∧ IsElementaryAbelian p ↥X ∧
    Nat.card ↥X = p ^ (2 * n) ∧
    ∃ P : Subgroup B, IsMaxParabolicP p K P ∧ X = Op p P ∧ P = X ⊔ K ⊓ centralizer ({z} : Set B)

@[expose] def C42d (k : Kind) (z : B) (X K : Subgroup B) : Prop :=
  (k = Kind.mcl ∨ k = Kind.ly) ∧ IsPGL3Four ↥(K ⊔ X) ∧ LieModel ↥K .PSL 3 2 2 ∧ Nat.card ↥X = 3 ∧
    K ⊓ centralizer ({z} : Set B) = K ⊓ centralizer (X : Set B) ∧
    IVK.IsL2 ↥(K ⊓ centralizer ({z} : Set B)) (fun q => q = 4) ∧
    (K ⊔ X ⊔ zpowers z) ⊓ centralizer ((K ⊓ centralizer ({z} : Set B) : Subgroup B) : Set B) = X ⊔ zpowers z

@[expose] def Concl42Loc (k : Kind) (z : B) (p : ℕ) (X : Subgroup B) : Prop :=
  C42a p z X (layer B) ∨ C42b p z X (layer B) ∨ C42c p z X (layer B) ∨ C42d k z X (layer B)

end Disj

structure E4Hyp (G : Type) [Group G] (z : G) (k : Kind) : Prop where
  p42 : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ (p : ℕ) (X : Subgroup B),
    Sig4A b (⊤ : Subgroup B) p X → pCore p B = ⊥ → Hyp42 b X → Concl42Loc k b p X
  two : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ J₁ J₂ J₃ : Subgroup B,
    IsComponent J₁ → IsComponent J₂ → IsComponent J₃ → J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False
  f3 : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ J : Subgroup B, IsComponent J →
    ∀ p n : ℕ, p.Prime → 1 ≤ n → (Odd (p ^ n) ∨ p ^ n = 4) → LieModel (Hat J) .PSL 3 p n →
      ∀ c : B, orderOf c = 2 → c ∈ centralizer (J : Set B) → False
  uinv : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ J : Subgroup B, IsComponent J →
    center (Hat J) ≠ ⊥ → ∀ u v : B, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 →
      u ∈ centralizer (J : Set B) → v ∈ centralizer (J : Set B) → u * v = v * u → u = v

structure E4Ctx (G : Type) [Group G] (z : G) (A : Type) [Group A] [Finite A] (a : A) (p : ℕ)
    (X : Subgroup A) : Prop where
  sec : SecOfG G z A a
  A4 : Sig4A a (⊤ : Subgroup A) p X
  z2 : a * a = 1
  op : pCore p A = ⊥
  a41 : ∀ r : ℕ, r.Prime → r ≠ 2 → X ≤ centralizer ((pCore r A : Subgroup A) : Set A)
  b41 : X ⊓ centralizer ((pCore 2 A ⊔ layer A : Subgroup A) : Set A) = ⊥

section Main

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X : Subgroup A}

theorem E4Ctx.inv (c : E4Ctx G z A a p X) (g : A) (hg : g * a = a * g) : g ∈ normalizer (X : Set A) :=
  c.A4.inv g (Subgroup.mem_top g) (by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hg.symm)

theorem E4Ctx.a_mem_normalizer (c : E4Ctx G z A a p X) : a ∈ normalizer (X : Set A) :=
  c.inv a rfl

theorem E4Ctx.secOfG_sub (c : E4Ctx G z A a p X) (J : Subgroup A) :
    SecOfG G z (secB a X J) (secZ a X J) := by
  have h1 : SecOfG G z ↥(secY a X J) ⟨a, z_mem_secY a X J⟩ := c.sec.sub (secY a X J) (z_mem_secY a X J)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(secY a X J))) :=
    (pPrimeCore_coprime_card (p := 2) (G := ↥(secY a X J))).odd_of_left
  exact h1.quot (pPrimeCore 2 ↥(secY a X J)) hodd

structure SubData (c : E4Ctx G z A a p X) (J : Subgroup A) : Prop where
  comp : IsComponent J
  XJ : X ≤ normalizer (J : Set A)
  zJ : a ∈ normalizer (J : Set A)
  JX : ⁅J, X⁆ ≠ ⊥

theorem SubData.hyp {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J) : SubHyp a p X J :=
  ⟨c.A4, c.z2, d.comp, d.XJ, d.zJ, d.JX⟩

theorem SubData.cases (F : E4Hyp G z k) {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J) :
    C42a p (secZ a X J) (secX a X J) (secJ a X J) ∨ C42b p (secZ a X J) (secX a X J) (secJ a X J) ∨
    C42c p (secZ a X J) (secX a X J) (secJ a X J) ∨ C42d k (secZ a X J) (secX a X J) (secJ a X J) := by
  have h := F.p42 (secB a X J) (secZ a X J) (c.secOfG_sub J) p (secX a X J) (secB_Sig4A d.hyp)
    (secB_pCore d.hyp) (secB_Hyp42 d.hyp)
  unfold Concl42Loc at h
  rwa [secB_layer d.hyp] at h

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
