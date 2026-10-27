module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyReduction
public import CFSG.Blueprint.Catalog

public section

open CFSG.LieType.SeitzGeneration CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

theorem centerless_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center A = ⊥) : Subgroup.center B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  have : e.symm x ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply e.injective
    simpa using hx (e a)
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  simpa using congrArg e this

theorem g2ThreeCatBasic_of_native
    (hB : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
      (K : Type) [Field K] [Finite K], Nat.card K = q.card →
        Nonempty (AdjointQuotient .G2 K ≃*
          TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.G2 q, hv⟩))
    (hfin : ∀ (K : Type) [Field K] [Finite K], Finite (adjointGroup .G2 K))
    (hcen : ∀ (K : Type) [Field K] [Finite K], Subgroup.center (adjointGroup .G2 K) = ⊥) :
    G2ThreeCatBasic := by
  intro q hv _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  obtain ⟨e⟩ := hB q hv K hK
  have hfinK := hfin K
  refine ⟨?_, ?_⟩
  · have : Finite (AdjointQuotient .G2 K) := inferInstanceAs (Finite (_ ⧸ _))
    exact Finite.of_equiv _ e.toEquiv
  · have e' : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
      (QuotientGroup.quotientMulEquivOfEq (hcen K)).trans QuotientGroup.quotientBot
    exact centerless_of_mulEquiv (e'.symm.trans e) (hcen K)

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
