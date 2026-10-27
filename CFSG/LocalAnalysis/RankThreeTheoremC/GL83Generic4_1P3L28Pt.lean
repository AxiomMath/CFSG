module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28L45

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

@[expose] def L28Z {G : Type} [Group G] (P : Subgroup G) : Subgroup G :=
  (center ↥P).map P.subtype

@[expose] def L28Prop34 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) : Prop :=
  (P : Subgroup G) ≤ centralizer ({x} : Set G) ∧ Nat.card (L28Z (P : Subgroup G)) = p ^ 2 ∧
  (∀ t ∈ (P : Subgroup G) ⊓ J, t ^ p = 1 → t ∈ L28Z (P : Subgroup G)) ∧
  (∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
      (zpowers x).map (MulAut.conj g).toMonoidHom ≤ J) ∧
  (∀ u ∈ (P : Subgroup G), u ^ p = 1 → u ∉ L28Z (P : Subgroup G) → L28OuterOn J u)

@[expose] def L28InV (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (x : G)
    (U : Subgroup G) : Prop :=
  U ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
  x ∈ U ∧ U ≠ L28Z (P : Subgroup G)

@[expose] def L28PointLemma42 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M : Subgroup G) (x : G) : Prop :=
  ∀ U : Subgroup G, L28InV p P x U → ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M

@[expose] def L28PointLemma43 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M : Subgroup G) (x : G) : Prop :=
  ∃ U : Subgroup G, L28InV p P x U ∧
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ GLBPrimeCore p M) (GLBPrimeCore p M) → normalizer (Y : Set G) ≤ M

@[expose] def L28PointFAbelian (p : ℕ) {G : Type} [Group G] [Finite G] (M U : Subgroup G) :
    Prop :=
  ∀ S R₀ F : Subgroup G, IsPGroup 2 S → S ≠ ⊥ → U ≤ normalizer (S : Set G) →
    ¬ normalizer (S : Set G) ≤ M → IsPGroup 2 R₀ → R₀ ≤ GLBPrimeCore p M →
    R₀ ≤ normalizer (S : Set G) → U ≤ normalizer (R₀ : Set G) →
    ¬ R₀ ≤ GLBPrimeCore p (normalizer (S : Set G)) → IsSylowOf p F (normalizer (S : Set G)) →
    U ≤ F → F ≤ M → CFSG.Open.pRank p F ≤ 2 → IsMulCommutative F

end CFSG.LocalAnalysis.RankThreeTheoremC
