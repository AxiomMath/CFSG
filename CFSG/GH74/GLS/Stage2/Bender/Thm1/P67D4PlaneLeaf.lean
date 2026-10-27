module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCoreReduction
public import CFSG.RankThree.PartOne.KGD.D4T36Torus

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Frames

structure D4PhiFrame (K : Type) [Field K] (σ : K ≃+* K) (q : ℕ) (ε : ℤ) where
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ q
  n : ModGL TwistTag.D4.tag (AlgebraicClosure K)
  hn : n ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K)
  w : WeylGroup TwistTag.D4.tag
  hnw : weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨n, hn⟩ = w
  hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x
  g0 : ModGL TwistTag.D4.tag (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K)
  hg0 : twistHom TwistTag.D4 (AlgebraicClosure K) Fr g0 = g0 * n
  hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag (AlgebraicClosure K)),
    P ≤ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) →
      (∀ x ∈ P, twistHom TwistTag.D4 (AlgebraicClosure K) Fr x = x) →
        P ≤ (triEmb K σ (AlgebraicClosure K)).range

@[expose] def D4PhiFrame.Contains {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ} {ε : ℤ}
    (F : D4PhiFrame K σ q ε) (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Prop :=
  ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ E,
    F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr)

structure D4SteinbergFrame (K : Type) [Field K] (σ : K ≃+* K) (q : ℕ) (ε : ℤ) where
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ q
  g : ModGL TwistTag.D4.tag (AlgebraicClosure K)
  hgG : g ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K)
  hFg : trialityFrob (AlgebraicClosure K) Fr g = g * threeSixN (AlgebraicClosure K) ε

@[expose] def D4SteinbergFrame.Contains {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ} {ε : ℤ}
    (F : D4SteinbergFrame K σ q ε) (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Prop :=
  ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    E.map (MulAut.conj c).toMonoidHom ≤ threeSixFixedTorsion K (AlgebraicClosure K) σ F.Fr ε 3 F.g

@[expose] def D4PlaneZ0 {K : Type} [Field K] (σ : K ≃+* K)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Prop :=
  ∀ Z₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    (∀ t ∈ Z₀, ∀ e ∈ E, t * e = e * t) → (∀ a ∈ Z₀, ∀ b ∈ Z₀, a * b = b * a) →
    (∀ x ∈ E, x ≠ 1 → ∀ s ∈ Subgroup.centralizer
      ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), ∀ t ∈ Z₀, s * t * s⁻¹ ∈ Z₀) →
    (∀ t ∈ Z₀, Nat.Coprime 3 (orderOf t)) → ∀ t ∈ Z₀, t = 1

@[expose] def D4PlaneGood {K : Type} [Field K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Prop :=
  (∃ x ∈ E, x ≠ 1 ∧ SingularCentralizerData σ q x) ∧ D4PlaneZ0 σ E

end Frames

end CFSG.GH74.GLS.Stage2.Bender.Thm1
