module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264A
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Defs

variable {Y : Type} [Group Y]

@[expose] def ActsTriv (Λ : Subgroup Y) (x : Y) : Prop :=
  ∀ z ∈ Λ, x * z * x⁻¹ * z⁻¹ ∈ oddCoreOf Λ

@[expose] def ActsLike (Λ : Subgroup Y) (x w : Y) : Prop :=
  ∀ z ∈ Λ, x * z * x⁻¹ * (w * z * w⁻¹)⁻¹ ∈ oddCoreOf Λ

abbrev edgeCent (P : Subgroup Y) (t u : Y) : Subgroup Y :=
  P ⊓ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y)

@[expose] def NoA1 (t u : Y) (R₀ T₀ : Subgroup Y) : Prop :=
  ¬ ∃ w : Y, w * w = 1 ∧ w * t = t * w ∧ w * u = u * w ∧
    w ∉ Subgroup.closure ({t, u} : Set Y) ∧
    R₀ ≤ Subgroup.centralizer ({w} : Set Y) ∧ T₀ ≤ Subgroup.centralizer ({w} : Set Y)

@[expose] def NoThreeMeetSylow (Ω : Set (Subgroup Y)) : Prop :=
  ∀ (S₂ : Sylow 2 Y) (L₁ L₂ L₃ : Subgroup Y), L₁ ∈ Ω → L₂ ∈ Ω → L₃ ∈ Ω → L₁ ≠ L₂ → L₁ ≠ L₃ →
    L₂ ≠ L₃ → 2 < Nat.card ↥(L₁ ⊓ (S₂ : Subgroup Y)) → 2 < Nat.card ↥(L₂ ⊓ (S₂ : Subgroup Y)) →
      2 < Nat.card ↥(L₃ ⊓ (S₂ : Subgroup Y)) → False

noncomputable abbrev fixSylGen (Φ : Set (Subgroup Y)) (σ : MulAut Y) : Subgroup Y :=
  ⨆ Q ∈ {Q : Subgroup Y | (∃ M ∈ Φ, IsSylow2In Q M) ∧ ∀ x ∈ Q, σ x = x}, Q

structure TwinSProp3 {W : Type} [Group W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W) : Prop extends TwinBase3 Φ K K' k k' where
  perm : ∀ M ∈ Φ, M.map σ.toMonoidHom ∈ Φ
  sq : σ * σ = 1
  fixK : ∃ Q : Subgroup W, IsSylow2In Q K ∧ ∀ x ∈ Q, σ x = x
  onK' : ∃ Q : Subgroup W, IsSylow2In Q K' ∧ (∀ x ∈ Q, σ x ∈ Q) ∧ ∀ x ∈ Q, σ x = x → x * x = 1

end Defs

section Cit3

structure Z2Set (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y) : Prop where
  large : TightLargeHypR 3 n Y R S t
  conn : DConnected (CoreAssembly.conjClass (tightCore R))
  noTri : ¬ TriNbrAll R t
  z2 : LinkZ2 R t
  simple : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t))
  index : (genFittingFStar ↥(linkGrp R t)).index ≤ 2
  model : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
    LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f
  hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  hu : IsUniqueInvolution J u
  hR₀ : IsSylow2In R₀ (tightCore R)
  hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y)
  hT₀ : IsSylow2In T₀ J
  hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)
  noA1 : NoA1 t u R₀ T₀
  hR₀P : R₀ ≤ (P : Subgroup Y)
  hT₀P : T₀ ≤ (P : Subgroup Y)

@[expose] def TightLinkZ2L2CoreR (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR 3 n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkZ2 R t →
      IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)) →
      (genFittingFStar ↥(linkGrp R t)).index ≤ 2 →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
        LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
        IsUniqueInvolution J u →
      (∀ R₀ T₀ : Subgroup Y, IsSylow2In R₀ (tightCore R) →
        R₀ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₀ J →
        T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₀ T₀) →
          False

@[expose] def TightLinkC264One (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → Thm4RBelow 3 n → PhilipHall.Frame.Thm1RTwinLiftSetEBelow n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR 3 n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkZ2 R t →
      IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)) →
      (genFittingFStar ↥(linkGrp R t)).index ≤ 2 →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
        LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
        IsUniqueInvolution J u →
      ∀ R₀ T₀ : Subgroup Y, IsSylow2In R₀ (tightCore R) →
        R₀ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₀ J →
        T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) →
        (¬ ∃ w : Y, w * w = 1 ∧ w * t = t * w ∧ w * u = u * w ∧
          w ∉ Subgroup.closure ({t, u} : Set Y) ∧
          R₀ ≤ Subgroup.centralizer ({w} : Set Y) ∧ T₀ ≤ Subgroup.centralizer ({w} : Set Y)) →
        (∃ P : Sylow 2 Y, R₀ ≤ (P : Subgroup Y) ∧ T₀ ≤ (P : Subgroup Y)) →
        C264One (CoreAssembly.conjClass (tightCore R)) t u

theorem Z2Set.c264One {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}
    (hs : Z2Set n R S t J u R₀ T₀ P) (h : TightLinkC264One n) (hP : TightBelowRPlus 3 n)
    (h4 : Thm4RBelow 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) :
    C264One (CoreAssembly.conjClass (tightCore R)) t u :=
  h hP h4 htw Y R S t hs.large hs.conn hs.noTri hs.z2 hs.simple hs.index hs.model J hs.hJ u hs.hu
    R₀ T₀ hs.hR₀ hs.hR₀u hs.hT₀ hs.hT₀N hs.noA1 ⟨P, hs.hR₀P, hs.hT₀P⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
