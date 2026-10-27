module

public import CFSG.GH74.Generic.S3.Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

structure Hyp2 (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  rank : 3 ≤ Open.twoRank G
  gen4 : Gen4 G
  kgh : KGH G
  sylow : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)
  generic : GLS.L2Meets G GLS.InG2
  noThin : ¬ GLS.HasTwoThinConfiguration G

section Bar

variable {G : Type} [Group G]

open Classical in
noncomputable def bar (x y : G) : CentralizerBar x :=
  if h : y ∈ centralizer ({x} : Set G) then proj x ⟨y, h⟩ else 1

theorem bar_of_mem {x y : G} (h : y ∈ centralizer ({x} : Set G)) : bar x y = proj x ⟨y, h⟩ := by
  classical
  simp [bar, h]

end Bar

section Abstract

variable {X : Type} [Group X]

@[expose] def IsSolv2CompIn (H L : Subgroup X) : Prop :=
  ∃ Lb : Subgroup (↥H ⧸ pPrimeCore 2 ↥H), Lb.IsSubnormal ∧
    Nonempty (↥Lb ≃* SL(2, ZMod 3)) ∧
      L = (Lb.comap (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map H.subtype

@[expose] def IsQuasi2CompIn (H L : Subgroup X) : Prop :=
  IsPCompIn 2 H L ∨ IsSolv2CompIn H L

@[expose] def solvLayer2 (H : Subgroup X) : Subgroup X :=
  ⨆ (L : Subgroup X) (_ : IsSolv2CompIn H L), L

@[expose] def extLayer2 (H : Subgroup X) : Subgroup X :=
  pLayerOf 2 H ⊔ solvLayer2 H

@[expose] def IsDirectFactorIn {Y : Type*} [Group Y] (P Q : Subgroup Y) : Prop :=
  P ≤ Q ∧ ∃ R : Subgroup Y, R ≤ Q ∧ P ⊓ R = ⊥ ∧ P ⊔ R = Q ∧ ⁅P, R⁆ = ⊥

@[expose] def NotDirectFactor6b (H Ie : Subgroup X) : Prop :=
  ¬ IsDirectFactorIn
    (oPrimeResidualOf 2 ((Ie.subgroupOf (solvLayer2 H)).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(solvLayer2 H)))))
    (oPrimeResidual 2 (↥(solvLayer2 H) ⧸ pPrimeCore 2 ↥(solvLayer2 H)))

@[expose] def SubtermRel (J : Subgroup X) (y : X) (L : Subgroup X) : Prop :=
  orderOf y = 2 ∧ y ∈ normalizer (J : Set X) ∧
    ((IsPCompIn 2 (centralizer ({y} : Set X) ⊓ J) L ∧
        ∀ z ∈ (centralizer (L : Set X) ⊓ (J ⊔ zpowers y)) ⊔ centralizer (J : Set X), orderOf z = 2 →
          IsPCompIn 2 (centralizer ({z} : Set X) ⊓ J) L ∨ z ∈ centralizer (J : Set X)) ∨
      (IsSolv2CompIn (centralizer ({y} : Set X) ⊓ J) L ∧
        ∃ L₀ : Subgroup X, L = L₀ ⊔ pPrimeCoreOf 2 L ∧ L₀ ⊓ pPrimeCoreOf 2 L = ⊥ ∧
          ⁅L₀, pPrimeCoreOf 2 L⁆ = ⊥ ∧
          ∀ z ∈ (centralizer (L₀ : Set X) ⊓ (J ⊔ zpowers y)) ⊔ centralizer (J : Set X), orderOf z = 2 →
            IsSubnormalIn L₀ (centralizer ({z} : Set X) ⊓ J) ∨ z ∈ centralizer (J : Set X)))

end Abstract

@[expose] def QShape1 (Kt : Type) [Group Kt] : Prop := IsSL4Model Kt

@[expose] def QShape3 (Kt : Type) [Group Kt] : Prop := IsL3OddGt3 Kt

@[expose] def QShape4 (Kt : Type) [Group Kt] : Prop := ∃ f : ℕ, LieModel Kt .twistedG2 0 3 f

@[expose] def QShape5 (Kt : Type) [Group Kt] : Prop := NativeSporadic.IsSporadic Kt .J1

@[expose] def QShapeNS (Kt : Type) [Group Kt] : Prop :=
  QShape1 Kt ∨ QShape3 Kt ∨ QShape4 Kt ∨ QShape5 Kt

theorem QShapeNS.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShapeNS A) :
    QShapeNS B := by
  rcases h with h | h | h | h
  · exact Or.inl (IsSL4Model.of_mulEquiv h e)
  · obtain ⟨p, f, hp, hp2, hq, h⟩ := h
    refine Or.inr (Or.inl ⟨p, f, hp, hp2, hq, ?_⟩)
    rcases h with h | h
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · obtain ⟨f, h⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h⟩))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩))

section Pairs

variable {G : Type} [Group G]

@[expose] def IsSource2 (x : G) (K A : Subgroup G) : Prop :=
  A ≤ centralizer ({x} : Set G) ∧ CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 8 ∧
    ((A ≤ K ∧ QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) ∨
      (∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ x ∉ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
        Nat.card ↥E = 4 ∧ (QShape3 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨
          QShape5 (↥K ⧸ pPrimeCore 2 ↥K))))

structure IsSubtermPair (x : G) (K : Subgroup G) (y : G) (Lb : Subgroup (CentralizerBar x)) : Prop where
  y_mem : y ∈ centralizer ({x} : Set G)
  y_ord : orderOf y = 2
  y_ne : bar x y ∉ zpowers (xbar x)
  rel : SubtermRel (imgBar x K) (bar x y) Lb
  maximal : pLayerOf 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) ≠ ⊥ →
    IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) Lb ∧
      ∀ L' : Subgroup (CentralizerBar x),
        IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) L' →
          SubtermRel (imgBar x K) (bar x y) L' → Nat.card ↥L' ≤ Nat.card ↥Lb

structure Setup1E (x y : G) (E : Subgroup G) : Prop where
  y_mem : y ∈ centralizer ({x} : Set G)
  y_ord : orderOf y = 2
  y_ne : bar x y ∉ zpowers (xbar x)
  E_le : E ≤ centralizer ({x} : Set G)
  E_ea : CFSG.IsElementaryAbelian 2 ↥E
  E_norm : ∀ d ∈ closure ({x, y} : Set G), d ∈ normalizer (E : Set G)
  E_rank : 2 ≤ pRank 2 ↥(E ⊓ centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G))

structure NonsolvAdm (x y : G) (K E : Subgroup G) (Lb Ib : Subgroup (CentralizerBar x)) : Prop where
  setup : Setup1E x y E
  leaves : y ∈ normalizer (K : Set G)
  layer : pLayerOf 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) ≠ ⊥
  compL : IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) Lb
  compI : IsPCompIn 2 (pLayerOf 2 (centralizer ((imgBar x E : Subgroup (CentralizerBar x)) :
    Set (CentralizerBar x)) ⊓ Lb)) Ib

structure SolvAdm (x y : G) (K E : Subgroup G) (Lb Ib : Subgroup (CentralizerBar x)) : Prop where
  setup : Setup1E x y E
  leaves : y ∈ normalizer (K : Set G)
  centE : ∀ e ∈ E, e * y = y * e
  layer : extLayer2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) ≠ ⊥
  quasiL : IsQuasi2CompIn (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) Lb
  invL : ∀ e ∈ imgBar x E, e ∈ normalizer (Lb : Set (CentralizerBar x))
  solvI : IsSolv2CompIn (extLayer2 (centralizer ((imgBar x E : Subgroup (CentralizerBar x)) :
    Set (CentralizerBar x)) ⊓ Lb)) Ib
  exists_Ie : ∀ e ∈ imgBar x E, e ≠ 1 → ∃ Ie : Subgroup (CentralizerBar x),
    IsQuasi2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie ∧
      oPrimeResidualOf 2 Ib ≤ Ie
  cond6 : ∀ e ∈ imgBar x E, e ≠ 1 → ∀ Ie : Subgroup (CentralizerBar x),
    IsQuasi2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie →
      oPrimeResidualOf 2 Ib ≤ Ie →
      IsSolv2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie →
        (∃ l ∈ Ie, orderOf l = 2 ∧ ∀ k ∈ imgBar x K, e * k * e⁻¹ = l * k * l⁻¹) ∨
        NotDirectFactor6b (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie

structure IsAdmPair (x : G) (K A : Subgroup G) (y : G) (Lb : Subgroup (CentralizerBar x)) : Prop where
  sub : IsSubtermPair x K y Lb
  adm : ∃ (E : Subgroup G) (Ib : Subgroup (CentralizerBar x)), IsE 2 A E ∧
    (NonsolvAdm x y K E Lb Ib ∨ SolvAdm x y K E Lb Ib)

@[expose] noncomputable def liftAt (x y : G) (Lb : Subgroup (CentralizerBar x)) : Subgroup G :=
  oPrimeResidualOf 2 (((Lb.comap (proj x)).map (centralizer ({x} : Set G)).subtype) ⊓
    centralizer ({y} : Set G))

@[expose] def NbhdSemisimple (x y : G) (Lb : Subgroup (CentralizerBar x)) : Prop :=
  ∀ d ∈ closure ({x, y} : Set G), d ≠ 1 → ⁅liftAt x y Lb, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥

@[expose] def IsAllowable (x : G) (K A : Subgroup G) : Prop :=
  ∀ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb → NbhdSemisimple x y Lb

@[expose] def IsBal32 (A : Subgroup G) : Prop := IsKBal 2 A ∧ IsWeakKBal 1 A

@[expose] def IsReg32 (A : Subgroup G) : Prop :=
  IsBal32 A ∧ thetaHalf 1 A ≠ ⊥ ∧ Odd (Nat.card ↥(thetaHalf 1 A))

end Pairs

end CFSG.GH74.Generic.BProg
