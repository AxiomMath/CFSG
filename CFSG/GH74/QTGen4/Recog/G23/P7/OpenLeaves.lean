module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs
public import CFSG.CharacterTheory.Blocks.InnerProduct
public import CFSG.GH74.QTGen4.Recog.G23.Native
public import Certificates.Data.G23RecogTriInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

class G23Leaf (L : Prop) : Prop where
  out : L

@[expose] def LeafHR : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G},
    G23Ctx G T H H₁ H₂ M → ∃ x ∈ M, x * x = 1 ∧ x ∉ quasithinGenFitting M

@[expose] def LeafLettersH : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G},
    G23Ctx G T H H₁ H₂ M → ∃ e : Fin 6 → G, HLetters H H₁ H₂ e

@[expose] def LeafHFacts : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G},
    G23One H H₁ H₂ → HLetters H H₁ H₂ e → HFacts H H₁ H₂ e

@[expose] def LeafZFitting : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G},
    Setup G T H H₁ H₂ M e → zOf e ∈ quasithinGenFitting M

@[expose] def LeafOneClass : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → zOf e ∈ quasithinGenFitting M → OneClass e

@[expose] def LeafSylow2Cent : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {Y : Subgroup G} {z : G}, orderOf z = 2 → z ∈ Y →
    ((∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y ⊓ Subgroup.centralizer {z} → Nat.card R ≤ 2) →
      ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Nat.card R ≤ 2) ∧
    (∀ Q₀ : Subgroup G, Q₀ ≤ Y → IsPGroup 2 Q₀ → z ∈ Q₀ →
      (∀ q ∈ Q₀, (∀ q' ∈ Q₀, q * q' = q' * q) ↔ q ∈ Subgroup.zpowers z) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y ⊓ Subgroup.centralizer {z} → Q₀ ≤ R → R = Q₀) →
      ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Q₀ ≤ R → R = Q₀)

@[expose] def LeafVertexCores : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    ∃ M₁ M₂ : Subgroup G, VertexCore e H (e 0) H₂ M₁ ∧ VertexCore e H (e 2) H₁ M₂

@[expose] def LeafPbarMixed : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    ∃ Pb Np Nm : Subgroup G, PbarCore e Pb ∧ MixedCore e (e 0 * e 2) Np ∧
      MixedCore e (e 0 * (e 2)⁻¹) Nm

@[expose] def LeafFourClasses : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e → VertexCore e H (e 0) H₂ M₁ →
    VertexCore e H (e 2) H₁ M₂ → PbarCore e Pb → MixedCore e (e 0 * e 2) Np →
    MixedCore e (e 0 * (e 2)⁻¹) Nm → FourClasses e

@[expose] def LeafCor37 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e → VertexCore e H (e 0) H₂ M₁ →
    VertexCore e H (e 2) H₁ M₂ → PbarCore e Pb → Cor37 e M₁ M₂ Pb

@[expose] def StepASylow (g : ℕ) : Prop :=
  9 ∣ g ∧ ¬ 27 ∣ g ∧ 64 ∣ g ∧ ¬ 128 ∣ g ∧ 36 ∣ g ∧ (g / 36) % 3 = 1

@[expose] def LeafStepALocal : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm → Nat.card Pb = 9 →
    SpecialSet e H ∧ StepASylow (Nat.card G)

@[expose] def LeafStepAArith : Prop :=
  ∀ (g : ℕ) (x₁ x₂ : ℤ), StepAArith g x₁ x₂ → StepASylow g → False

open scoped Classical in
@[expose] def psiTerms : Fin 15 → List (Fin 20 × ℤ) := ![
  [(0, 1), (8, -1), (19, 1)], [(5, 1), (2, -1)], [(12, 1), (2, -1)], [(13, 1), (2, -1)],
  [(10, 1), (11, -1)], [(16, 1), (19, -1)], [(17, 1), (19, -1)], [(18, 1), (19, -1)],
  [(6, 1), (3, -1)], [(4, 1), (7, -1)], [(0, 1), (1, 1), (2, -1)], [(14, 1), (15, 1), (19, -1)],
  [(3, 1), (7, 1), (11, -1)], [(1, 1), (9, -1), (19, 1)], [(2, 1), (11, 1), (19, -1)]]

@[expose] def psiGram : Fin 15 → Fin 15 → ℤ := ![
  ![3, 0, 0, 0, 0, -1, -1, -1, 0, 0, 1, -1, 0, 1, -1],
  ![0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
  ![0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
  ![0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
  ![0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
  ![-1, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 1, 0, -1, 1],
  ![-1, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, -1, 1],
  ![-1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0, -1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, -1],
  ![-1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 3, 0, -1, 1],
  ![0, 0, 0, 0, 1, 0, 0, 0, -1, -1, 0, 0, 3, 0, -1],
  ![1, 0, 0, 0, 0, -1, -1, -1, 0, 0, 1, -1, 0, 3, -1],
  ![-1, -1, -1, -1, -1, 1, 1, 1, 0, 0, -1, 1, -1, -1, 3]]

@[expose] def charDegs : Fin 20 → ℕ :=
  ![1, 1, 2, 3, 3, 2, 3, 3, 9, 9, 6, 6, 2, 2, 4, 4, 8, 8, 8, 8]

open scoped Classical in
@[expose] noncomputable def psiFun {G : Type} [Group G] (H : Subgroup G) (χ : Fin 20 → H → ℂ)
    (k : Fin 15) : H → ℂ :=
  fun y => ((psiTerms k).map fun p => (p.2 : ℂ) * χ p.1 y).sum

open scoped Classical in
structure HCharProps {G : Type} [Group G] [Fintype G] (H : Subgroup G) (z : G)
    (χ : Fin 20 → H → ℂ) : Prop where
  irr : ∀ i, χ i ∈ CFSG.BlocksIrr H
  inj : Function.Injective χ
  triv : ∀ y, χ 0 y = 1
  deg : ∀ i, χ i 1 = (charDegs i : ℂ)
  vanish : ∀ k (y : H), (y : G) ∉ specialD z H → psiFun H χ k y = 0
  span : ∀ f : H → ℂ, CFSG.BlocksIsClassFunction f → (∀ y : H, (y : G) ∉ specialD z H → f y = 0) →
    ∃ c : Fin 15 → ℂ, f = fun y => ∑ k, c k * psiFun H χ k y
  gram : ∀ k l, CFSG.BlocksInnerProduct (psiFun H χ k) (psiFun H χ l) = (psiGram k l : ℂ)
  inner_triv : ∀ k, CFSG.BlocksInnerProduct (psiFun H χ k) (χ 0) =
    if k = 0 ∨ k = 10 then 1 else 0
  chi9_absent : ∀ k, k ≠ 0 → CFSG.BlocksInnerProduct (psiFun H χ k) (χ 8) = 0
  chi9_z : ∀ y : H, (y : G) = z → χ 8 y = 9
  chi20_z : ∀ y : H, (y : G) = z → χ 19 y = -8
  chi9_order4 : ∀ y : H, (y : G) ∈ specialD z H → orderOf y = 4 → χ 8 y = -3
  sum_chi9 : ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD z H), χ 8 y = -171
  count_invol : (Finset.univ.filter (fun y : H => orderOf y = 2 ∧ (y : G) ≠ z)).card = 90
  count_order4 : (Finset.univ.filter (fun y : H => orderOf y = 4 ∧ (y : G) ∉ specialD z H)).card = 72
  count_D : (Finset.univ.filter (fun y : H => (y : G) ∈ specialD z H)).card = 413
  sum_N : ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD z H),
      psiFun H χ 0 y * (((Finset.univ.filter (fun u : H => orderOf u = 2 ∧
        (if (y : G) = z then (u : G) ≠ z else (u : G) * y * (u : G)⁻¹ = (y : G)⁻¹))).card : ℕ) : ℂ)
      = 7200

open scoped Classical in
@[expose] def LeafHCharTable : Prop :=
  ∀ {G : Type} [Group G] [Fintype G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G},
    G23One H H₁ H₂ → HLetters H H₁ H₂ e → ∃ χ : Fin 20 → H → ℂ, HCharProps H (zOf e) χ

open scoped Classical in
structure SuzukiCoherent {G : Type} [Group G] [Fintype G] (H : Subgroup G) (D : Set G)
    (χ : Fin 20 → H → ℂ) (X₁ X₂ : G → ℂ) (ε₁ ε₂ : ℤ) : Prop where
  ε₁_pm : ε₁ = 1 ∨ ε₁ = -1
  ε₂_pm : ε₂ = 1 ∨ ε₂ = -1
  irr₁ : X₁ ∈ CFSG.BlocksIrr G
  irr₂ : X₂ ∈ CFSG.BlocksIrr G
  ne : X₁ ≠ X₂
  ne_triv₁ : X₁ ≠ fun _ => 1
  ne_triv₂ : X₂ ≠ fun _ => 1
  ind : CFSG.TwoRankLowerBound.Helpers.inducedFunction H (psiFun H χ 0) =
    (fun _ => 1) + (ε₁ : ℂ) • X₁ + (ε₂ : ℂ) • X₂
  val₁ : ∀ x : H, (x : G) ∈ D → X₁ x = (ε₁ : ℂ) * χ 19 x
  val₂ : ∀ x : H, (x : G) ∈ D → X₂ x = -(ε₂ : ℂ) * χ 8 x

open scoped Classical in
@[expose] def LeafSuzukiCoherence : Prop :=
  ∀ {G : Type} [Group G] [Fintype G] {H : Subgroup G} {e : Fin 6 → G} {χ : Fin 20 → H → ℂ},
    SpecialSet e H → HCharProps H (zOf e) χ →
    ∃ (X₁ X₂ : G → ℂ) (ε₁ ε₂ : ℤ), SuzukiCoherent H (specialD (zOf e) H) χ X₁ X₂ ε₁ ε₂

open scoped Classical in
@[expose] def LeafSuzukiIntegers : Prop :=
  ∀ {G : Type} [Group G] [Fintype G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {χ : Fin 20 → H → ℂ} {X₁ X₂ : G → ℂ} {ε₁ ε₂ : ℤ},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e → SpecialSet e H →
    HCharProps H (zOf e) χ → SuzukiCoherent H (specialD (zOf e) H) χ X₁ X₂ ε₁ ε₂ →
    ∃ x₁ x₂ : ℤ, StepAArith (Nat.card G) x₁ x₂

@[expose] def LeafB27Abelian : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm → Nat.card Pb = 27 →
    IsElemAbelian 3 M₁ ∧ IsElemAbelian 3 M₂

@[expose] def LeafB27Normalizer : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm → Nat.card Pb = 27 → IsElemAbelian 3 M₁ →
    IsElemAbelian 3 M₂ → ∃ (W₁ Mf : Subgroup G) (t' : G), B27State e M₁ Pb W₁ Mf t'

@[expose] def LeafB27Contradiction : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm W₁ Mf : Subgroup G} {t' : G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm → Nat.card Pb = 27 → IsElemAbelian 3 M₁ →
    IsElemAbelian 3 M₂ → B27State e M₁ Pb W₁ Mf t' → False

@[expose] def Y0Set : Set (GL (Fin 3) (ZMod 3)) :=
  {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 0 =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 1 * (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 2 -
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2 * (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1}

@[expose] def LeafGL3Facts : Prop :=
  (∀ g : GL (Fin 3) (ZMod 3), orderOf g = 13 → ∀ u v : Fin 3 → ZMod 3, u ≠ 0 → v ≠ 0 →
      ∃ k : ℕ, ∃ c : ZMod 3, c ≠ 0 ∧
        ((g ^ k : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)).mulVec u = c • v) ∧
  (∀ Y : Subgroup (GL (Fin 3) (ZMod 3)), (∀ g ∈ Y0Set, g ∈ Y) → ¬ 13 ∣ Nat.card Y →
      (∃ g ∈ Y, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 0 ≠ 0 ∨
        (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 ≠ 0) →
      (∀ g ∈ Y, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0) ∧ 432 ∣ Nat.card Y)

@[expose] def LeafMStruct : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm → Nat.card Pb = 81 → MStruct e M₁ M₂

@[expose] def LeafLoc5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm → Nat.card Pb = 81 → MStruct e M₁ M₂ →
    ∃ W : Subgroup G, Loc5 e M₁ M₂ Pb W

@[expose] def LeafVertexLetters : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {σ a b z : G} {M W : Subgroup G} {w₁ w₂ : G},
    VertexHyp σ a b z M W w₁ w₂ →
    ∃ k : Fin 6, SatWords (vertexRels1 k) (![σ, a, b, w₁, w₂] : Fin 5 → G) ∧
      SatWords (vertexRels2 k) (![σ, a, b, w₁, w₂] : Fin 5 → G) ∧
      Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) = M ⊔ Subgroup.closure ({a, b} : Set G)

@[expose] def LeafTriClassify : Prop :=
  ∀ k₁ k₂ : Fin 6, (k₁, k₂) ∈ modelPairs ∨
    (Finite (PG 6 (cfgWords k₁ k₂)) ∧ Nat.card (PG 6 (cfgWords k₁ k₂)) ≤ 288)

@[expose] def LeafTriCosetBound : Prop :=
  Finite (PG 6 triWords) ∧ Nat.card (PG 6 triWords) ≤ 7371 * 576

@[expose] def LeafTriNative : Prop :=
  ∃ u : Fin 6 → Ghat, SatWords triWords u ∧ Subgroup.closure (Set.range u) = ⊤

@[expose] def LeafTriLetters : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm W : Subgroup G},
    Setup G T H H₁ H₂ M e → HFacts H H₁ H₂ e → OneClass e →
    Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm → Loc5 e M₁ M₂ Pb W →
    ∃ f : Fin 6 → G, SatWords triWords f ∧
      Subgroup.closure ({f 0, f 1, f 2, f 3} : Set G) = H₁ ⊔ H₂

@[expose] def LeafGhatInvolCent : Prop :=
  ∀ y : Ghat, orderOf y = 2 → Nat.card (Subgroup.centralizer ({y} : Set Ghat)) = 576

end CFSG.GH74.QTGen4.Recog.G23.P7
