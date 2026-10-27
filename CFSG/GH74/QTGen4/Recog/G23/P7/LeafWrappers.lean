module

public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

theorem exists_hR [Finite G] [G23Leaf LeafHR] {T H H₁ H₂ M : Subgroup G}
    (h : G23Ctx G T H H₁ H₂ M) : ∃ x ∈ M, x * x = 1 ∧ x ∉ quasithinGenFitting M :=
  G23Leaf.out (L := LeafHR) h

theorem exists_lettersH [Finite G] [G23Leaf LeafLettersH] {T H H₁ H₂ M : Subgroup G}
    (h : G23Ctx G T H H₁ H₂ M) : ∃ e : Fin 6 → G, HLetters H H₁ H₂ e :=
  G23Leaf.out (L := LeafLettersH) h

theorem sylow2_le_two_of_cent [Finite G] [G23Leaf LeafSylow2Cent] {Y : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hzY : z ∈ Y)
    (h : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y ⊓ Subgroup.centralizer {z} → Nat.card R ≤ 2)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hRY : R ≤ Y) : Nat.card R ≤ 2 :=
  (G23Leaf.out (L := LeafSylow2Cent) hz hzY).1 h R hR hRY

theorem maximal_two_of_cent [Finite G] [G23Leaf LeafSylow2Cent] {Y : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hzY : z ∈ Y) {Q₀ : Subgroup G} (hQY : Q₀ ≤ Y) (hQ : IsPGroup 2 Q₀)
    (hzQ : z ∈ Q₀) (hcent : ∀ q ∈ Q₀, (∀ q' ∈ Q₀, q * q' = q' * q) ↔ q ∈ Subgroup.zpowers z)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y ⊓ Subgroup.centralizer {z} → Q₀ ≤ R → R = Q₀)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hRY : R ≤ Y) (hQR : Q₀ ≤ R) : R = Q₀ :=
  (G23Leaf.out (L := LeafSylow2Cent) hz hzY).2 Q₀ hQY hQ hzQ hcent hmax R hR hRY hQR

namespace Setup

variable [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}

theorem hFacts [G23Leaf LeafHFacts] (h : Setup G T H H₁ H₂ M e) : HFacts H H₁ H₂ e :=
  G23Leaf.out (L := LeafHFacts) h.ctx.one h.lets

theorem zFitting [G23Leaf LeafZFitting] (h : Setup G T H H₁ H₂ M e) :
    zOf e ∈ quasithinGenFitting M :=
  G23Leaf.out (L := LeafZFitting) h

theorem oneClass [G23Leaf LeafOneClass] (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e)
    (hz : zOf e ∈ quasithinGenFitting M) : OneClass e :=
  G23Leaf.out (L := LeafOneClass) h hF hz

theorem exists_vertexCores [G23Leaf LeafVertexCores] (h : Setup G T H H₁ H₂ M e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) :
    ∃ M₁ M₂ : Subgroup G, VertexCore e H (e 0) H₂ M₁ ∧ VertexCore e H (e 2) H₁ M₂ :=
  G23Leaf.out (L := LeafVertexCores) h hF hO

theorem exists_pbarMixed [G23Leaf LeafPbarMixed] (h : Setup G T H H₁ H₂ M e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) :
    ∃ Pb Np Nm : Subgroup G, PbarCore e Pb ∧ MixedCore e (e 0 * e 2) Np ∧
      MixedCore e (e 0 * (e 2)⁻¹) Nm :=
  G23Leaf.out (L := LeafPbarMixed) h hF hO

theorem fourClasses [G23Leaf LeafFourClasses] {M₁ M₂ Pb Np Nm : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (h₁ : VertexCore e H (e 0) H₂ M₁) (h₂ : VertexCore e H (e 2) H₁ M₂) (hp : PbarCore e Pb)
    (hnp : MixedCore e (e 0 * e 2) Np) (hnm : MixedCore e (e 0 * (e 2)⁻¹) Nm) : FourClasses e :=
  G23Leaf.out (L := LeafFourClasses) h hF hO h₁ h₂ hp hnp hnm

theorem cor37 [G23Leaf LeafCor37] {M₁ M₂ Pb : Subgroup G} (h : Setup G T H H₁ H₂ M e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) (h₁ : VertexCore e H (e 0) H₂ M₁)
    (h₂ : VertexCore e H (e 2) H₁ M₂) (hp : PbarCore e Pb) : Cor37 e M₁ M₂ Pb :=
  G23Leaf.out (L := LeafCor37) h hF hO h₁ h₂ hp

theorem stepALocal [G23Leaf LeafStepALocal] {M₁ M₂ Pb Np Nm : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 9) :
    SpecialSet e H ∧ StepASylow (Nat.card G) :=
  G23Leaf.out (L := LeafStepALocal) h hF hO hL hPb

theorem b27Abelian [G23Leaf LeafB27Abelian] {M₁ M₂ Pb Np Nm : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 27) :
    IsElemAbelian 3 M₁ ∧ IsElemAbelian 3 M₂ :=
  G23Leaf.out (L := LeafB27Abelian) h hF hO hL hPb

theorem b27Normalizer [G23Leaf LeafB27Normalizer] {M₁ M₂ Pb Np Nm : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 27) (ha₁ : IsElemAbelian 3 M₁)
    (ha₂ : IsElemAbelian 3 M₂) : ∃ (W₁ Mf : Subgroup G) (t' : G), B27State e M₁ Pb W₁ Mf t' :=
  G23Leaf.out (L := LeafB27Normalizer) h hF hO hL hPb ha₁ ha₂

theorem b27Contradiction [G23Leaf LeafB27Contradiction] {M₁ M₂ Pb Np Nm W₁ Mf : Subgroup G}
    {t' : G} (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 27) (ha₁ : IsElemAbelian 3 M₁)
    (ha₂ : IsElemAbelian 3 M₂) (hst : B27State e M₁ Pb W₁ Mf t') : False :=
  G23Leaf.out (L := LeafB27Contradiction) h hF hO hL hPb ha₁ ha₂ hst

theorem mStruct [G23Leaf LeafMStruct] {M₁ M₂ Pb Np Nm : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 81) : MStruct e M₁ M₂ :=
  G23Leaf.out (L := LeafMStruct) h hF hO hL hPb

theorem exists_loc5 [G23Leaf LeafLoc5] {M₁ M₂ Pb Np Nm : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 81) (hM : MStruct e M₁ M₂) :
    ∃ W : Subgroup G, Loc5 e M₁ M₂ Pb W :=
  G23Leaf.out (L := LeafLoc5) h hF hO hL hPb hM

theorem triLetters [G23Leaf LeafTriLetters] {M₁ M₂ Pb Np Nm W : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (h5 : Loc5 e M₁ M₂ Pb W) :
    ∃ f : Fin 6 → G, SatWords triWords f ∧ Subgroup.closure ({f 0, f 1, f 2, f 3} : Set G) = H₁ ⊔ H₂ :=
  G23Leaf.out (L := LeafTriLetters) h hF hO hL h5

end Setup

section Chars

variable [Fintype G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}

open scoped Classical in
theorem exists_hCharTable [G23Leaf LeafHCharTable] (hH : G23One H H₁ H₂)
    (hL : HLetters H H₁ H₂ e) : ∃ χ : Fin 20 → H → ℂ, HCharProps H (zOf e) χ :=
  G23Leaf.out (L := LeafHCharTable) hH hL

open scoped Classical in
theorem exists_suzukiCoherent [G23Leaf LeafSuzukiCoherence] {χ : Fin 20 → H → ℂ}
    (hD : SpecialSet e H) (hχ : HCharProps H (zOf e) χ) :
    ∃ (X₁ X₂ : G → ℂ) (ε₁ ε₂ : ℤ), SuzukiCoherent H (specialD (zOf e) H) χ X₁ X₂ ε₁ ε₂ :=
  G23Leaf.out (L := LeafSuzukiCoherence) hD hχ

open scoped Classical in
theorem exists_stepAArith [G23Leaf LeafSuzukiIntegers] {χ : Fin 20 → H → ℂ} {X₁ X₂ : G → ℂ}
    {ε₁ ε₂ : ℤ} (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hD : SpecialSet e H) (hχ : HCharProps H (zOf e) χ)
    (hc : SuzukiCoherent H (specialD (zOf e) H) χ X₁ X₂ ε₁ ε₂) :
    ∃ x₁ x₂ : ℤ, StepAArith (Nat.card G) x₁ x₂ :=
  G23Leaf.out (L := LeafSuzukiIntegers) h hF hO hD hχ hc

end Chars

theorem false_of_stepAArith [G23Leaf LeafStepAArith] {g : ℕ} {x₁ x₂ : ℤ}
    (h : StepAArith g x₁ x₂) (hs : StepASylow g) : False :=
  G23Leaf.out (L := LeafStepAArith) g x₁ x₂ h hs

theorem exists_vertexLetters [Finite G] [G23Leaf LeafVertexLetters] {σ a b z : G}
    {M W : Subgroup G} {w₁ w₂ : G} (h : VertexHyp σ a b z M W w₁ w₂) :
    ∃ k : Fin 6, SatWords (vertexRels1 k) (![σ, a, b, w₁, w₂] : Fin 5 → G) ∧
      SatWords (vertexRels2 k) (![σ, a, b, w₁, w₂] : Fin 5 → G) ∧
      Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) = M ⊔ Subgroup.closure ({a, b} : Set G) :=
  G23Leaf.out (L := LeafVertexLetters) h

theorem modelPair_or_collapse [G23Leaf LeafTriClassify] (k₁ k₂ : Fin 6) :
    (k₁, k₂) ∈ modelPairs ∨
      (Finite (PG 6 (cfgWords k₁ k₂)) ∧ Nat.card (PG 6 (cfgWords k₁ k₂)) ≤ 288) :=
  G23Leaf.out (L := LeafTriClassify) k₁ k₂

theorem card_PG_tri_le [G23Leaf LeafTriCosetBound] :
    Finite (PG 6 triWords) ∧ Nat.card (PG 6 triWords) ≤ 7371 * 576 :=
  G23Leaf.out (L := LeafTriCosetBound)

theorem exists_native_tri [G23Leaf LeafTriNative] :
    ∃ u : Fin 6 → Ghat, SatWords triWords u ∧ Subgroup.closure (Set.range u) = ⊤ :=
  G23Leaf.out (L := LeafTriNative)

theorem ghat_card_centralizer_invol [G23Leaf LeafGhatInvolCent] {y : Ghat} (hy : orderOf y = 2) :
    Nat.card (Subgroup.centralizer ({y} : Set Ghat)) = 576 :=
  G23Leaf.out (L := LeafGhatInvolCent) y hy

end CFSG.GH74.QTGen4.Recog.G23.P7
