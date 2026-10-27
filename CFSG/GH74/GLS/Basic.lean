module

public import CFSG.GH74.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def IsKGroupNative (X : Type) [Group X] : Prop := SectionRank.IsKGroupCat X

@[expose] def IsKProperSimple (G : Type) [Group G] : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ Assembly.KProper Blueprint.Catalog G

theorem isKGroupNative_of_kProper {G : Type} [Group G] [Finite G]
    (hK : Assembly.KProper Blueprint.Catalog G) {H : Subgroup G} (hH : H ≠ ⊤) :
    IsKGroupNative H :=
  ComponentClassification.UnbalancingLocal.kGroupOver_of_kProper SectionRank.catalog_of_mulEquiv
    (fun S _ _ _ h => ComponentClassification.UnbalancingLocal.catalog_of_abelian_simple S h)
    hK H hH

theorem kProper_of_forall_isKGroupNative {G : Type} [Group G]
    (h : ∀ H : Subgroup G, H ≠ ⊤ → IsKGroupNative H) : Assembly.KProper Blueprint.Catalog G :=
  CFSG.KCore.KProperAllSimple.kProperNonab SectionRank.catalog_isoInvariant h

theorem kProper_iff_forall_isKGroupNative {G : Type} [Group G] [Finite G] :
    Assembly.KProper Blueprint.Catalog G ↔ ∀ H : Subgroup G, H ≠ ⊤ → IsKGroupNative H :=
  ⟨fun hK _ hH => isKGroupNative_of_kProper hK hH, kProper_of_forall_isKGroupNative⟩

theorem kProper_of_isKGroupNative {G : Type} [Group G] (hG : IsKGroupNative G) :
    Assembly.KProper Blueprint.Catalog G :=
  fun K L _ _ _ hsimple _ => hG K (L.subgroupOf K) hsimple

theorem isKProperSimple_iff {G : Type} [Group G] [Finite G] :
    IsKProperSimple G ↔ IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧
      ∀ H : Subgroup G, H ≠ ⊤ → IsKGroupNative H :=
  and_congr_right fun _ => and_congr_right fun _ => kProper_iff_forall_isKGroupNative

theorem IsKProperSimple.isKGroupNative_of_ne_top {G : Type} [Group G] [Finite G]
    (hG : IsKProperSimple G) {H : Subgroup G} (hH : H ≠ ⊤) : IsKGroupNative H :=
  isKGroupNative_of_kProper hG.2.2 hH

theorem isKProperSimple_of_isKGroupNative {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hG : IsKGroupNative G) : IsKProperSimple G :=
  ⟨hs, hn, kProper_of_isKGroupNative hG⟩

section Sections

variable {G : Type*} [Group G]

@[expose] def IsCompIn (H K : Subgroup G) : Prop :=
  K ≤ H ∧ IsComponent (K.subgroupOf H)

@[expose] def IsPCompIn (p : ℕ) (H K : Subgroup G) : Prop :=
  K ≤ H ∧ IsPComponent p (K.subgroupOf H)

@[expose] def pPrimeCoreOf (p : ℕ) (K : Subgroup G) : Subgroup G :=
  (pPrimeCore p ↥K).map K.subtype

@[expose] def centralizerSection (K M : Subgroup G) : Subgroup G where
  carrier := {c | c ∈ normalizer (K : Set G) ∧ c ∈ normalizer (M : Set G) ∧
    ∀ k ∈ K, ⁅k, c⁆ ∈ M}
  one_mem' := ⟨one_mem _, one_mem _, fun k _ => by simp⟩
  mul_mem' := by
    rintro c d ⟨hcK, hcM, hc⟩ ⟨hdK, hdM, hd⟩
    refine ⟨mul_mem hcK hdK, mul_mem hcM hdM, fun k hk => ?_⟩
    have h1 : ⁅k, c * d⁆ = ⁅k, c⁆ * (c * ⁅k, d⁆ * c⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact M.mul_mem (hc k hk) ((mem_normalizer_iff.mp hcM _).mp (hd k hk))
  inv_mem' := by
    rintro c ⟨hcK, hcM, hc⟩
    refine ⟨inv_mem hcK, inv_mem hcM, fun k hk => ?_⟩
    have h1 : ⁅k, c⁻¹⁆ = c⁻¹ * (⁅k, c⁆)⁻¹ * c⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact (mem_normalizer_iff.mp (inv_mem hcM) _).mp (M.inv_mem (hc k hk))

@[expose] def zStar (X : Subgroup G) : Subgroup G :=
  X ⊓ centralizerSection X (pPrimeCoreOf 2 X)

@[expose] def elementsOfOrder (p : ℕ) (X : Type*) [Group X] : Set X := {x | orderOf x = p}

end Sections

@[expose] def oPrimeResidual (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  Subgroup.closure {x : X | ∃ k : ℕ, x ^ (p ^ k) = 1}

@[expose] def oResidual (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  Subgroup.closure {x : X | Nat.Coprime (orderOf x) p}

@[expose] def pPrimePCore (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  (pCore p (X ⧸ pPrimeCore p X)).comap (QuotientGroup.mk' (pPrimeCore p X))

instance pPrimePCore_normal (p : ℕ) (X : Type*) [Group X] : (pPrimePCore p X).Normal := by
  unfold pPrimePCore
  infer_instance

@[expose] def oPrimeResidualOf {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (oPrimeResidual p ↥X).map X.subtype

@[expose] def oPrimePResidual (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  (oResidual p ↥(oPrimeResidual p X)).map (oPrimeResidual p X).subtype

@[expose] def L2Sub (G : Type) [Group G] (P : Assembly.GroupProp) : Prop :=
  ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → P ↥K

@[expose] def L2Meets (G : Type) [Group G] (P : Assembly.GroupProp) : Prop :=
  ∃ x : G, orderOf x = 2 ∧ ∃ K : Subgroup (CentralizerBar x), IsComponent K ∧ P ↥K

section Pairs

variable {G : Type*} [Group G]

@[expose] def IsIL2Pair (x : G) (K : Subgroup G) : Prop :=
  orderOf x = 2 ∧ IsPCompIn 2 (centralizer ({x} : Set G)) K

@[expose] def CxK (x : G) (K : Subgroup G) : Subgroup G :=
  centralizer ({x} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def NxK (x : G) (K : Subgroup G) : Subgroup G :=
  centralizer ({x} : Set G) ⊓ normalizer (K : Set G)

@[expose] def IsTerminalPair (p : ℕ) (x : G) (K : Subgroup G) : Prop :=
  orderOf x = p ∧ IsCompIn (centralizer ({x} : Set G)) K ∧ p ∣ Nat.card K ∧
    ∀ y : G, orderOf y = p → y ∈ centralizer (K : Set G) →
      IsCompIn (centralizer ({y} : Set G)) K

@[expose] def pLayerOf (p : ℕ) (H : Subgroup G) : Subgroup G :=
  sSup {L | IsPCompIn p H L}

@[expose] def pumpUp (p : ℕ) (K : Subgroup G) (y : G) : Subgroup G :=
  ⨆ g ∈ pLayerOf p (centralizer ({y} : Set G)),
    (pLayerOf p (K ⊓ centralizer ({y} : Set G))).map (MulAut.conj g).toMonoidHom

@[expose] def oBound (p : ℕ) : ℕ := if p = 2 then 3 else 4

@[expose] def IsILo (p : ℕ) (x : G) (K : Subgroup G) : Prop :=
  orderOf x = p ∧ oBound p ≤ pRank p ↥(centralizer ({x} : Set G)) ∧
    IsPCompIn p (centralizer ({x} : Set G)) K

@[expose] def PumpUpLT (p : ℕ) (x : G) (K : Subgroup G) (x' : G) (K' : Subgroup G) : Prop :=
  IsILo p x K ∧ IsILo p x' K' ∧ x' ∈ centralizer ({x} : Set G) ∧
    x' ∈ centralizerSection K (pPrimeCoreOf p K) ∧ IsPCompIn p (pumpUp p K x') K'

@[expose] def LongPumpUp (p : ℕ) (x : G) (K : Subgroup G) (x' : G) (K' : Subgroup G) : Prop :=
  IsILo p x K ∧ Relation.ReflTransGen
    (fun a b : G × Subgroup G => PumpUpLT p a.1 a.2 b.1 b.2) (x, K) (x', K')

@[expose] def IsPTerminal (p : ℕ) (x : G) (K : Subgroup G) : Prop :=
  IsILo p x K ∧
    (∀ (x' : G) (K' : Subgroup G), PumpUpLT p x K x' K' →
      x ∈ normalizer (K' : Set G) ∧
        Nonempty ((↥K' ⧸ pPrimeCore p ↥K') ≃* (↥K ⧸ pPrimeCore p ↥K))) ∧
    (∀ Q : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p Q
        (centralizer ({x} : Set G) ⊓ centralizerSection K (pPrimeCoreOf p K)) →
      ∀ (x' : G) (K' : Subgroup G), PumpUpLT p x K x' K' → x' ∈ Q → (∀ q ∈ Q, x' * q = q * x') →
        CFSG.ABGLocalTools.IsSylowOf p Q
          (centralizer ({x'} : Set G) ⊓ centralizerSection K' (pPrimeCoreOf p K')))

@[expose] def IsTwoTerminal (x : G) (K : Subgroup G) : Prop := IsPTerminal 2 x K

@[expose] def IsPRigid (p : ℕ) (x : G) (K : Subgroup G) : Prop :=
  IsILo p x K ∧ ∀ (x' : G) (K' : Subgroup G), LongPumpUp p x K x' K' →
    Nonempty ((↥K' ⧸ pPrimeCore p ↥K') ≃* (↥K ⧸ pPrimeCore p ↥K))

end Pairs

end CFSG.GH74.GLS
