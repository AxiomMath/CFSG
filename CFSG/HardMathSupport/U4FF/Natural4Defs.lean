module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis.RankThreeUC CFSG.Open CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

@[expose] def NaturalSU4 (n : ℕ) {S : Type} [CommGroup S] (L : Subgroup (MulAut S)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    ∃ (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)) (ψ : S ≃* Multiplicative (Fin 4 → F)),
      ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
          (Multiplicative.toAdd (ψ s)))

theorem NaturalSU4.naturalU4Mod {n : ℕ} {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}
    (h : NaturalSU4 n L) : NaturalU4Mod n L :=
  Or.inl h

@[expose] def Natural4Input : Prop :=
  ∀ (S : Type) [CommGroup S] (n : ℕ) (L : Subgroup (MulAut S)), IsU4Group n L → IsIrrOn L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ n) ^ 2 →
    ∀ (η : ↥L ≃* ↥(SU (unitaryInvolution K 2 n) 4))
      (E : Type) [Field E] [Finite E] (ι : K →+* E),
      ∀ (ε : S ≃* Multiplicative (Fin 4 → E)) (R : ↥L →* GL (Fin 4) E),
        (∀ (l : ↥L) (s : S), ε ((l : MulAut S) s) =
          Multiplicative.ofAdd ((R l : Matrix (Fin 4) (Fin 4) E).mulVec
            (Multiplicative.toAdd (ε s)))) →
        ∀ (k : Type) [Field k] [Algebra E k] (P : GL (Fin 4) k) (i₀ : ℕ),
          (∀ l : ↥L, (P : Matrix (Fin 4) (Fin 4) k) *
              (R l : Matrix (Fin 4) (Fin 4) E).map (algebraMap E k) =
            ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
              (fun x => algebraMap E k (ι (x ^ 2 ^ i₀))) * (P : Matrix (Fin 4) (Fin 4) k)) →
          NaturalSU4 n L

end CFSG.HardMathSupport.U4FF
