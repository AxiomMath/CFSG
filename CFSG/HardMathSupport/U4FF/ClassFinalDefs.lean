module

public import CFSG.HardMathSupport.U4FF.Omega2Defs
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis.RankThreeUC CFSG.Open CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

@[expose] def Omega2InputGen : Prop :=
  ∀ (S : Type) [CommGroup S] (n : ℕ) (L : Subgroup (MulAut S)), IsU4Group n L → IsIrrOn L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ n) ^ 2 →
    ∀ (η : ↥L ≃* ↥(SU (unitaryInvolution K 2 n) 4))
      (E : Type) [Field E] [Finite E] (m : ℕ), Nat.card E = 2 ^ (n * m) →
      ∀ (ε : S ≃* Multiplicative (Fin 6 → E)) (R : ↥L →* GL (Fin 6) E),
        (∀ (l : ↥L) (s : S), ε ((l : MulAut S) s) =
          Multiplicative.ofAdd ((R l : Matrix (Fin 6) (Fin 6) E).mulVec
            (Multiplicative.toAdd (ε s)))) →
        ∀ (k : Type) [Field k] [Algebra E k] [Algebra K k] (P : GL (Fin 6) k) (i₀ : ℕ),
          (∀ l : ↥L, (P : Matrix (Fin 6) (Fin 6) k) *
              (R l : Matrix (Fin 6) (Fin 6) E).map (algebraMap E k) =
            comp2 (((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
              (fun x => algebraMap K k (x ^ 2 ^ i₀))) * (P : Matrix (Fin 6) (Fin 6) k)) →
          NaturalOmega6 n L

end CFSG.HardMathSupport.U4FF
