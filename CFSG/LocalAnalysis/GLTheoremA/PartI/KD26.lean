module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def IsKHat (K : Type*) [Group K] : Prop :=
  CFSG.Open.IsQuasisimple K ∧ CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K)

theorem IsKHat.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (h : IsKHat K) :
    IsKHat K' := by
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e h.1, ?_⟩
  obtain ⟨i, ⟨f⟩⟩ := h.2
  have hc : (Subgroup.center K).map (e : K →* K') = Subgroup.center K' :=
    Subgroup.map_center_eq e
  exact ⟨i, ⟨(QuotientGroup.congr _ _ e hc).symm.trans f⟩⟩

@[expose] def fixSub {K : Type*} [Group K] (y : MulAut K) : Subgroup K :=
  (y.toMonoidHom).eqLocus (MonoidHom.id K)

@[expose] def qEps (lin : Bool) (q : ℕ) : ℕ := if lin then q - 1 else q + 1

@[expose] def isLnEps (n q : ℕ) : Bool → TauCeti.LieTypeIndex → Prop
  | true, .A r qq => r + 1 = n ∧ qq.card = q
  | false, .twistedA r qq => r + 1 = n ∧ qq.card = q
  | _, _ => False

@[expose] def isE6Eps (q : ℕ) : Bool → TauCeti.LieTypeIndex → Prop
  | true, .E6 qq => qq.card = q
  | false, .twistedE6 qq => qq.card = q
  | _, _ => False

@[expose] def IsLnEps (S : Type) [Group S] (n q : ℕ) (lin : Bool) : Prop :=
  catalogIs S (onLie (isLnEps n q lin))

theorem IsLnEps.one_le {S : Type} [Group S] {n q : ℕ} {lin : Bool} (h : IsLnEps S n q lin) :
    1 ≤ n := by
  obtain ⟨i, hi, -⟩ := h
  cases i with
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases lin <;> cases d <;> simp [onLie, isLnEps] at hi <;> omega

@[expose] def IsE6Eps (S : Type) [Group S] (q : ℕ) (lin : Bool) : Prop :=
  catalogIs S (onLie (isE6Eps q lin))

@[expose] def KD26a : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKHat K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ D : Subgroup (MulAut K), IsElemAbelian p D →
      Nat.card D ≤ p ^ 2 * Nat.card ↥(D ⊓ inner K)

@[expose] def KD26bc : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKHat K → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K →
    ¬ (p = 3 ∧ IsLnEps (K ⧸ Subgroup.center K) 3 8 false) →
    ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 2 → D ⊓ inner K = ⊥ →
      ∃ y ∈ D, y ≠ 1 ∧ GLAPLayer p (fixSub y) ≠ ⊥

@[expose] def KD26d : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsLnEps S 3 8 false →
    ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D = 9 →
      ∃ x ∈ D ⊓ inner S, x ≠ 1

@[expose] def KD26e : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKHat K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsPGroup p (Subgroup.center K) → p ∣ Nat.card (Subgroup.center K) →
    (∃ α : MulAut K, α ^ p = 1 ∧ α ∉ inner K) →
    (∃ (n q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) n q lin ∧
        p ∣ Nat.gcd n (qEps lin q) ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd n (qEps lin q)) ∨
    (∃ (q : ℕ) (lin : Bool), IsE6Eps (K ⧸ Subgroup.center K) q lin ∧ p = 3 ∧ 3 ∣ qEps lin q ∧
        Nat.card (Subgroup.center K) ∣ 3)

@[expose] def KD26f : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKHat K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((∃ (n q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) n q lin ∧
        p ∣ Nat.gcd n (qEps lin q) ∧ ¬ p ^ 2 ∣ Nat.gcd n (qEps lin q)) ∨
      (∃ (q : ℕ) (lin : Bool), IsE6Eps (K ⧸ Subgroup.center K) q lin ∧ p = 3 ∧
        3 ∣ qEps lin q)) →
    ∀ D : Subgroup (MulAut K), IsElemAbelian p D →
      Nat.card D ≤ p * Nat.card ↥(D ⊓ inner K)

@[expose] def KD26g : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsPGroup p (Subgroup.center K) → p ∣ Nat.card (Subgroup.center K) →
    (∀ (n q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) n q lin →
        p ∣ Nat.gcd n (qEps lin q) →
        n - 3 ≤ GLATwoLocalRank p K ∧
        (Nat.card (Subgroup.center K) = p ^ (Nat.gcd n (qEps lin q)).factorization p →
          n - 2 ≤ GLATwoLocalRank p K)) ∧
    (∀ (q : ℕ) (lin : Bool), IsE6Eps (K ⧸ Subgroup.center K) q lin → p = 3 →
        3 ∣ qEps lin q → 4 ≤ GLATwoLocalRank p K)

@[expose] def KD26h : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) p q lin → p ∣ qEps lin q →
      Nat.card (Subgroup.center K) = p →
      ∀ d : K, d ^ p ∈ Subgroup.center K → d ^ p ≠ 1 →
        GLAPLayer p (Subgroup.centralizer ({d} : Set K)) ≠ ⊥

theorem mem_inner_of_centerQuotientHom_mem {G : Type*} [Group G] [Group.IsPerfect G] {α : MulAut G}
    (h : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom G α ∈
      inner (G ⧸ Subgroup.center G)) : α ∈ inner G := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) q
  exact ⟨g, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective G
    ((CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj g).trans hq)⟩

end CFSG.LocalAnalysis.GLTheoremA
