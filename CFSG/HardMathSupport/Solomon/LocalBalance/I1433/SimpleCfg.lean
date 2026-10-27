module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433Reduction

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.Yardstones.Md42047359a2a

structure I1433SCfg {S : Type} [Group S] [Finite S] (Q : Subgroup (MulAut S)) (x : S)
    (J : Subgroup S) (q : ℕ) : Prop where
  derived : Q ≤ commutator (MulAut S)
  card : Nat.card Q = 27
  exponent : ∀ g ∈ Q, g ^ 3 = 1
  nonabelian : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a
  center : (Subgroup.center ↥Q).map Q.subtype = Subgroup.zpowers (MulAut.conj x)
  order : orderOf x = 3
  comp : GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) J
  mem : x ∈ J
  sl3 : IsSL3EpsOver (↥J ⧸ GLAPPrimeCore 3 ↥J) q
  zctr : ((Subgroup.zpowers x).subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) =
    Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J)
  ord : (Nat.card J).factorization 3 = 3
  centralizes : ∀ L : Subgroup S, GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) L →
    ∀ α ∈ Q, ∀ l ∈ L, α l = l

@[expose] def NonD4LieContraS (F : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ p : ℕ, p.Prime → p ≠ 3 →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = F → IsChevIndexOfChar p idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → ¬ IsD4Simple S →
      ∀ (Q : Subgroup (MulAut S)) (x : S) (J : Subgroup S) (q : ℕ), ¬ I1433SCfg Q x J q

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
