module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextNormalizer
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Setup

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G)

@[expose] def sp6A₂ : Subgroup G := pullSub φ (pointwiseStabilizer b (lagrangianOf e))

@[expose] def sp6R₂ : Subgroup G := sp6A₂ φ e ⊔ zpowers z

@[expose] def sp6N₂ : Subgroup G := normalizer (sp6R₂ φ e z : Set G)

@[expose] def sp6D₂ : Subgroup G := CFSG.Assembly.pCoreOf 2 (sp6N₂ φ e z)

end Setup

section SetupBasis

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

@[expose] def sp6I₂ : Set G :=
  {x | ∃ B : ↥(binarySymMatrices 3), symThreeDiag (B : M₃) = 0 ∧
    tauHom φ he (Multiplicative.ofAdd B) = x}

@[expose] def sp6F₂ : Set G := {d | d ∈ sp6D₂ φ e z ∧ z⁻¹ * (d⁻¹ * z * d) ∈ sp6I₂ φ he}

@[expose] def sp6E₂ : Subgroup G :=
  Classical.epsilon fun E : Subgroup G =>
    (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512

@[expose] def sp6C₂ : Subgroup G := sp6D₂ φ e z ⊓ centralizer (sp6E₂ φ he z : Set G)

@[expose] def sp6X : Subgroup G := normalizer (sp6C₂ φ he z : Set G)

instance sp6C₂_normal : ((sp6C₂ φ he z).subgroupOf (sp6X φ he z)).Normal :=
  Subgroup.normal_in_normalizer

abbrev Sp6F : Type := ↥(sp6X φ he z) ⧸ (sp6C₂ φ he z).subgroupOf (sp6X φ he z)

@[expose] def sp6πX : sp6X φ he z →* Sp6F φ he z := QuotientGroup.mk' _

open Classical in
@[expose] def sp6a : Sp6F φ he z :=
  if h : z ∈ sp6X φ he z then sp6πX φ he z ⟨z, h⟩ else 1

open Classical in
@[expose] def sp6Levi (g : GL (Fin 3) (ZMod 2)) : Sp6F φ he z :=
  if h : leviHom φ he g ∈ sp6X φ he z then sp6πX φ he z ⟨_, h⟩ else 1

@[expose] def sp6JL : Subgroup (Sp6F φ he z) :=
  (((leviHom φ he).range).subgroupOf (sp6X φ he z)).map (sp6πX φ he z)

@[expose] def sp6Ro : Subgroup (Sp6F φ he z) := CFSG.pPrimeCore 2 (Sp6F φ he z)

instance sp6Ro_normal : (sp6Ro φ he z).Normal := CFSG.pPrimeCore_normal

abbrev Sp6Y : Type := Sp6F φ he z ⧸ sp6Ro φ he z

@[expose] def sp6θ : Sp6F φ he z →* Sp6Y φ he z := QuotientGroup.mk' _

@[expose] def sp6aBar : Sp6Y φ he z := sp6θ φ he z (sp6a φ he z)

@[expose] def sp6JLBar : Subgroup (Sp6Y φ he z) := (sp6JL φ he z).map (sp6θ φ he z)

@[expose] def sp6Dstar : Subgroup (Sp6Y φ he z) :=
  normalClosure (sp6JLBar φ he z : Set (Sp6Y φ he z))

@[expose] def sp6Qstar : Subgroup (Sp6F φ he z) :=
  normalClosure (sp6JL φ he z : Set (Sp6F φ he z))

@[expose] def sp6K : Subgroup G :=
  (CFSG.oddCore (centralizer (sp6C₂ φ he z : Set G))).map
    (centralizer (sp6C₂ φ he z : Set G)).subtype

@[expose] def sp6KBar : Subgroup (Sp6F φ he z) :=
  ((sp6K φ he z).subgroupOf (sp6X φ he z)).map (sp6πX φ he z)

@[expose] def Sp6LayerSimple : Prop :=
  IsSimpleGroup (sp6Dstar φ he z) ∧ (∃ x y : sp6Dstar φ he z, x * y ≠ y * x) ∧
    sp6JLBar φ he z < sp6Dstar φ he z ∧
    ∃ d ∈ sp6Dstar φ he z, (sp6aBar φ he z)⁻¹ * d * sp6aBar φ he z ≠ d

@[expose] def Sp6LayerTwoFactor : Prop :=
  ∃ D₁ D₂ : Subgroup (Sp6Y φ he z), CFSG.IsComponent D₁ ∧ CFSG.IsComponent D₂ ∧ D₁ ≠ D₂ ∧
    IsSimpleGroup D₁ ∧ (∃ x y : D₁, x * y ≠ y * x) ∧
    IsSimpleGroup D₂ ∧ (∃ x y : D₂, x * y ≠ y * x) ∧
    D₁ ⊔ D₂ = sp6Dstar φ he z ∧ D₁ ⊓ D₂ = ⊥ ∧ ⁅D₁, D₂⁆ = ⊥ ∧
    D₁.map (MulAut.conj (sp6aBar φ he z)⁻¹).toMonoidHom = D₂ ∧
    sp6JLBar φ he z = sp6Dstar φ he z ⊓ centralizer {sp6aBar φ he z} ∧
    (∀ K : Subgroup (Sp6Y φ he z), CFSG.IsComponent K → K = D₁ ∨ K = D₂) ∧
    ∃ Ψ : sp6Dstar φ he z ≃* GL (Fin 3) (ZMod 2) × GL (Fin 3) (ZMod 2),
      (∀ (g : GL (Fin 3) (ZMod 2)) (h : sp6θ φ he z (sp6Levi φ he z g) ∈ sp6Dstar φ he z),
        Ψ ⟨_, h⟩ = (g, g)) ∧
      ∀ (d : Sp6Y φ he z) (hd : d ∈ sp6Dstar φ he z)
        (hda : (sp6aBar φ he z)⁻¹ * d * sp6aBar φ he z ∈ sp6Dstar φ he z),
        Ψ ⟨_, hda⟩ = (Ψ ⟨d, hd⟩).swap

@[expose] def Sp6LagrangianLayerConclusion (V₁ : Subgroup G) : Prop :=
  sp6X φ he z ≠ ⊤ ∧ CFSG.SectionRank.IsKGroupCat (sp6X φ he z) ∧
  (∃ hzX : z ∈ sp6X φ he z, sp6a φ he z = sp6πX φ he z ⟨z, hzX⟩) ∧
  (∃ hLX : ∀ g, leviHom φ he g ∈ sp6X φ he z,
    ∀ g, sp6Levi φ he z g = sp6πX φ he z ⟨_, hLX g⟩) ∧
  (∃ ι : GL (Fin 3) (ZMod 2) →* Sp6F φ he z, (∀ g, ι g = sp6Levi φ he z g) ∧
    Function.Injective ι ∧ ι.range = sp6JL φ he z) ∧
  CFSG.SectionRank.IsKGroupCat (Sp6F φ he z) ∧ CFSG.SectionRank.IsKGroupCat (Sp6Y φ he z) ∧
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog (Sp6Y φ he z) ∧
  IsMulCommutative (sp6Ro φ he z) ∧
  (∀ r ∈ sp6Ro φ he z, (sp6a φ he z)⁻¹ * r * sp6a φ he z = r⁻¹) ∧
  sp6Ro φ he z ⊓ centralizer {sp6a φ he z} = ⊥ ∧
  Set.InjOn (sp6θ φ he z) (sp6JL φ he z) ∧
  Set.InjOn (sp6θ φ he z) (centralizer {sp6a φ he z}) ∧
  (∀ P : Subgroup (Sp6F φ he z), IsPGroup 2 P → Set.InjOn (sp6θ φ he z) P) ∧
  orderOf (sp6a φ he z) = 2 ∧
  sp6JL φ he z ≤ centralizer {sp6a φ he z} ∧ zpowers (sp6a φ he z) ⊓ sp6JL φ he z = ⊥ ∧
  zpowers (sp6a φ he z) ⊔ sp6JL φ he z = centralizer {sp6a φ he z} ∧
  orderOf (sp6aBar φ he z) = 2 ∧
  sp6JLBar φ he z ≤ centralizer {sp6aBar φ he z} ∧
  zpowers (sp6aBar φ he z) ⊓ sp6JLBar φ he z = ⊥ ∧
  zpowers (sp6aBar φ he z) ⊔ sp6JLBar φ he z = centralizer {sp6aBar φ he z} ∧
  CFSG.pPrimeCore 2 (Sp6Y φ he z) = ⊥ ∧ CFSG.pCore 2 (Sp6Y φ he z) = ⊥ ∧
  CFSG.fittingSubgroup (Sp6Y φ he z) = ⊥ ∧
  IsPGroup 2 ((((V₁ ⊔ sp6C₂ φ he z).subgroupOf (sp6X φ he z)).map (sp6πX φ he z)).map
    (sp6θ φ he z)) ∧
  Nat.card ((((V₁ ⊔ sp6C₂ φ he z).subgroupOf (sp6X φ he z)).map (sp6πX φ he z)).map
    (sp6θ φ he z)) = 32 ∧
  (∀ S : Sylow 2 (Sp6Y φ he z), sp6aBar φ he z ∈ S →
    ∃ s ∈ S, s * sp6aBar φ he z ≠ sp6aBar φ he z * s) ∧
  CFSG.IsStandardSubgroup (sp6JLBar φ he z) ∧
  ¬ 2 ∣ (zpowers (sp6aBar φ he z)).relIndex
    (centralizer (sp6JLBar φ he z : Set (Sp6Y φ he z))) ∧
  (∀ t ∈ centralizer (sp6JLBar φ he z : Set (Sp6Y φ he z)), orderOf t = 2 →
    ∃ c ∈ centralizer (sp6JLBar φ he z : Set (Sp6Y φ he z)), c⁻¹ * t * c = sp6aBar φ he z) ∧
  ¬ (sp6JLBar φ he z).Normal ∧
  sp6Dstar φ he z = CFSG.layer (Sp6Y φ he z) ∧
  centralizer (sp6Dstar φ he z : Set (Sp6Y φ he z)) = ⊥ ∧
  Xor (Sp6LayerSimple φ he z) (Sp6LayerTwoFactor φ he z) ∧
  (∀ y : Sp6Y φ he z, (∀ d ∈ sp6Dstar φ he z, y⁻¹ * d * y = d) → y = 1) ∧
  (∀ x ∈ (sp6Dstar φ he z).comap (sp6θ φ he z), ∀ r ∈ sp6Ro φ he z, x * r = r * x) ∧
  ⁅sp6JL φ he z, sp6Ro φ he z⁆ = ⊥ ∧
  (sp6Qstar φ he z).Normal ∧ ⁅sp6Qstar φ he z, sp6Qstar φ he z⁆ = sp6Qstar φ he z ∧
  (sp6Qstar φ he z).map (sp6θ φ he z) = sp6Dstar φ he z ∧
  (sp6Dstar φ he z).comap (sp6θ φ he z) = sp6Ro φ he z ⊔ sp6Qstar φ he z ∧
  (center (sp6Qstar φ he z)).map (sp6Qstar φ he z).subtype = sp6Qstar φ he z ⊓ sp6Ro φ he z ∧
  centralizer (sp6Qstar φ he z : Set (Sp6F φ he z)) = sp6Ro φ he z ∧
  (∃ eQ : ↥(sp6Qstar φ he z) ⧸ (sp6Ro φ he z).subgroupOf (sp6Qstar φ he z) ≃*
      sp6Dstar φ he z,
    ∀ q : sp6Qstar φ he z, (eQ (QuotientGroup.mk q) : Sp6Y φ he z) = sp6θ φ he z q) ∧
  CFSG.fittingSubgroup (Sp6F φ he z) = sp6Ro φ he z ∧
  sp6KBar φ he z ≤ sp6Ro φ he z ∧
  ((sp6Ro φ he z).comap (sp6πX φ he z)).Normal ∧
  (sp6C₂ φ he z).subgroupOf (sp6X φ he z) ≤ (sp6Ro φ he z).comap (sp6πX φ he z) ∧
  ((sp6Ro φ he z).comap (sp6πX φ he z)).map (sp6πX φ he z) = sp6Ro φ he z ∧
  ((sp6πX φ he z).comp ((sp6Ro φ he z).comap (sp6πX φ he z)).subtype).ker =
    ((sp6C₂ φ he z).subgroupOf (sp6X φ he z)).subgroupOf ((sp6Ro φ he z).comap (sp6πX φ he z)) ∧
  (∃ κF : Sp6F φ he z →* MulAut (sp6C₂ φ he z),
    (∀ (x : sp6X φ he z) (c : sp6C₂ φ he z),
      ((κF (sp6πX φ he z x) c : sp6C₂ φ he z) : G) = x * c * (x : G)⁻¹) ∧
    κF.ker = sp6KBar φ he z ∧
    (κF.comp (sp6Ro φ he z).subtype).ker = (sp6KBar φ he z).subgroupOf (sp6Ro φ he z)) ∧
  (sp6KBar φ he z).Normal ∧ ((sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z)).Normal ∧
  ∀ [(sp6KBar φ he z).Normal] [((sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z)).Normal],
    (∃ eK : ↥(sp6X φ he z) ⧸ (sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z) ≃*
        Sp6F φ he z ⧸ sp6KBar φ he z,
      ∀ x : sp6X φ he z, eK (QuotientGroup.mk x) = QuotientGroup.mk (sp6πX φ he z x)) ∧
    CFSG.pPrimeCore 2 (Sp6F φ he z ⧸ sp6KBar φ he z) =
      (sp6Ro φ he z).map (QuotientGroup.mk' (sp6KBar φ he z))

end SetupBasis

@[expose] def Sp6LagrangianFullOddCoreStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → CFSG.oddCore G = ⊥ →
  ∀ (L : Subgroup G), CFSG.Assembly.ComponentType.IsStandardSubgroup L → ¬ L.Normal →
    center L = ⊥ → CFSG.Blueprint.LieModel L .PSp 3 2 1 →
  ∀ (T : Sylow 2 (centralizer (L : Set G))), IsCyclic (T : Subgroup (centralizer (L : Set G))) →
  ∀ z : G, z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype →
    orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V) (hb : b.IsAlt), b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) →
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let θ₂ : ↥(binarySymMatrices 3) × ZMod 2 → G := fun x => τ x.1 * z ^ x.2.val
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₂ := sp6A₂ φ e
    let R₂ := sp6R₂ φ e z
    let N₂ := sp6N₂ φ e z
    let D₂ := sp6D₂ φ e z
    let I₂ := sp6I₂ φ he
    let F₂ := sp6F₂ φ he z
    let A₁ := pullSub φ (pointRadical b hb u f)
    let b₁ : G := ((φ.symm (n 0 1) : L) : G)
    let I₁ := zpowers b₁
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    let F₁ : Set G := {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ I₁}
    let J := A₁ ⊓ A₂
    let J₀ : Set G := (A₁ : Set G) ∩ I₂
    ∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) →
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
      κ₂ = 0 ∧ ∃ C₁ E₂ : Subgroup G,
        let E₁ : Set G := (C₁ : Set G) ∩ F₁
        let K₀ := C₁ ⊓ D₂
        let M : Set G := (C₁ : Set G) ∩ F₂
        let C₂ := D₂ ⊓ centralizer (E₂ : Set G)
        let Z₁ := (center C₁).map C₁.subtype
        E₂ = sp6E₂ φ he z ∧ C₂ = sp6C₂ φ he z ∧
        C₁ ≤ D₁ ∧ (∀ m ∈ N₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧ Nat.card C₁ = 1024 ∧
        zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ B₁ = A₁ ∧ closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ I₁ ∧
        Nat.card ↥E₁ = 64 ∧ Nat.card K₀ = 64 ∧ Nat.card ↥M = 32 ∧ Nat.card J = 8 ∧
        Nat.card ↥J₀ = 4 ∧
        (∀ m ∈ N₂, ∀ x ∈ E₂, m * x * m⁻¹ ∈ E₂) ∧ (E₂ : Set G) ⊆ F₂ ∧ IsMulCommutative E₂ ∧
        Nat.card E₂ = 512 ∧
        (∀ E' : Subgroup G, (E' : Set G) ⊆ F₂ → IsMulCommutative E' → Nat.card E' = 512 →
          E' = E₂) ∧
        IsElementaryAbelian 2 E₂ ∧
        (∀ m ∈ N₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂) ∧ Nat.card C₂ = 4096 ∧
        (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G) ∧ C₂ ⊓ R₂ = A₂ ∧
        (C₂ : Set G) ∩ F₂ = E₂ ∧ C₁ ⊓ C₂ = K₀ ∧ (C₁ : Set G) ∩ E₂ = M ∧
        (∀ k ∈ K₀, ∀ k' ∈ K₀, k * k' = k' * k) ∧ conjClass K₀ z = z • (J : Set G) ∧
        ⁅K₀, A₂⁆ = ⊥ ∧
        ∃ (ν₂ : G → ↥(binarySymMatrices 3)) (ε : ZMod 2),
          (∀ d ∈ D₂, z⁻¹ * (d⁻¹ * z * d) = τ (ν₂ d)) ∧
          (∀ c ∈ C₂, c ^ 2 = θ₂ (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)), 0)) ∧
          (ε = 0 →
            let P := A₂ ⊔ K₀
            let V₁ := D₁ ⊔ A₂
            let B := zpowers z ⊔ A₁ ⊔ A₂ ⊔ K₀
            let Q₀ : Set G := (K₀ : Set G) ∩ F₁
            let N := normalizer (B : Set G) ⊓ centralizer ({b₁} : Set G)
            let X := normalizer (C₂ : Set G)
            let K := (CFSG.oddCore (centralizer (C₂ : Set G))).map
              (centralizer (C₂ : Set G)).subtype
            IsElementaryAbelian 2 P ∧ Nat.card P = 512 ∧
            (∃ Q : Subgroup G, (Q : Set G) = Q₀ ∧ IsElementaryAbelian 2 Q ∧ Nat.card Q = 16) ∧
            Nat.card B = 4096 ∧ Nat.card V₁ = 16384 ∧ B ≤ V₁ ∧
            (∀ v ∈ V₁, ∀ x ∈ B, v * x * v⁻¹ ∈ B) ∧ I₁ ≤ P ∧ P ≤ B ∧
            (∀ Y : Subgroup G, I₁ ≤ Y → Y ≤ B → Nat.card Y = 512 → (∀ y ∈ Y, y ^ 2 ∈ I₁) →
              (∀ y ∈ Y, ∀ y' ∈ Y, y⁻¹ * y'⁻¹ * y * y' ∈ I₁) → Y = P) ∧
            (∀ m ∈ N, ∀ p ∈ P, m * p * m⁻¹ ∈ P) ∧ V₁ ≤ N ∧
            (∀ m : G, (m ∈ N ∧ ∀ x ∈ B, m * x * m⁻¹ * x⁻¹ ∈ P) ↔ m ∈ A₁ ⊔ D₂) ∧
            (A₁ ⊔ D₂) ⊓ centralizer (P : Set G) = C₂ ∧
            N ≤ X ∧ V₁ ≤ X ∧ V₁ ⊓ C₂ = P ∧ C₂.relIndex (V₁ ⊔ C₂) = 32 ∧
            (∀ c ∈ C₂, c * z = z * c ↔ c ∈ A₂) ∧
            (fun c => z⁻¹ * c⁻¹ * z * c) '' (C₂ : Set G) = A₂ ∧
            (∃ hzX : z ∈ X,
              centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)} =
                (N₂.subgroupOf X).map (QuotientGroup.mk' (C₂.subgroupOf X)) ∧ N₂ ≤ X ∧
              (∃ ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
                  centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)},
                ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2)) (h : z ^ s.val * leviHom φ he g ∈ X),
                  (ψ (Multiplicative.ofAdd s, g) : X ⧸ C₂.subgroupOf X) =
                    QuotientGroup.mk ⟨_, h⟩) ∧
              (∀ S : Sylow 2 (X ⧸ C₂.subgroupOf X),
                (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) ∈ S →
                  ∃ y ∈ S, y * (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) ≠
                    (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) * y) ∧
              CFSG.Assembly.pCore 2 (X ⧸ C₂.subgroupOf X) = ⊥) ∧
            centralizer (C₂ : Set G) = C₂ ⊔ K ∧ C₂ ⊓ K = ⊥ ∧ Odd (Nat.card K) ∧
            (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∧ (∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧
            (∀ k ∈ K, z * k * z⁻¹ = k⁻¹) ∧
            (∃ κ : X →* MulAut C₂,
              (∀ (x : X) (c : C₂), ((κ x c : C₂) : G) = x * c * (x : G)⁻¹) ∧
              κ.ker = (C₂ ⊔ K).subgroupOf X) ∧
            IsElementaryAbelian 2 C₂ ∧ Nat.card C₂ = 2 ^ 12 ∧ Nat.card A₂ = 2 ^ 6 ∧
            (∃ Ψ : Multiplicative ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2)) ≃* C₂,
              (∀ u v, z * (Ψ (Multiplicative.ofAdd (u, v)) : G) * z⁻¹ =
                Ψ (Multiplicative.ofAdd (u, u + v))) ∧
              ∀ u v, (Ψ (Multiplicative.ofAdd (u, v)) : G) ∈ A₂ ↔ u = 0) ∧
            (center C₂).map C₂.subtype = C₂ ∧
            (lam = 0 → IsElementaryAbelian 2 C₁ ∧ Z₁ = C₁) ∧
            (lam = 1 → ⁅C₁, C₁⁆ = I₁ ∧ closure {x | ∃ y ∈ C₁, y ^ 2 = x} = I₁ ∧
              IsElementaryAbelian 2 Z₁ ∧ Nat.card Z₁ = 4 ∧
              E₁ = ((A₁ ⊔ Z₁ : Subgroup G) : Set G) ∧ Z₁ ≤ C₂) ∧
            Sp6LagrangianLayerConclusion φ he z V₁)

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
