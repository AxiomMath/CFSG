module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


@[expose] def TwE6VtwInput : Prop :=
  ∀ {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f), ℓ ≠ 2 → 3 ∣ ℓ ^ f + 1 →
    ∀ {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
      (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
        (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
      {c : Kˣ}, orderOf c = 3 →
    ∀ (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)),
    ∃ V : Subgroup (MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))),
      V ≤ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f) ∧
      IsElemAbelian 3 V ∧ Nat.card V = 3 ^ 6 ∧
      MulAut.conj (TwE6Conc.twE6R0 c hct) ∈ V ∧
      (∀ v ∈ V, v (TwE6Conc.twE6T K ℓ f) = TwE6Conc.twE6T K ℓ f) ∧
      (∀ v ∈ V, ((TwE6Conc.leviJ K ℓ f).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ f))).map v.toMonoidHom =
        (TwE6Conc.leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      (∀ v ∈ V, (∀ j ∈ (TwE6Conc.leviJ K ℓ f).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ f)),
          j * (v j)⁻¹ ∈ GLAPPrimeCoreOf 3 ((TwE6Conc.leviJ K ℓ f).subgroupOf
            (twistedE6RootGroup K (unitaryInvolution K ℓ f)))) →
        v ∈ Subgroup.zpowers (MulAut.conj (TwE6Conc.twE6R0 c hct))) ∧
      (∃ v₁ ∈ V, v₁ ∉ Subgroup.zpowers (MulAut.conj (TwE6Conc.twE6R0 c hct)) ∧
        GLAPLayer 3 ((TwE6Conc.leviJ K ℓ f).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ⊓ fixSubgroup v₁) ≠ ⊥) ∧
      (∀ δ : K ≃+* K, δ ζ = ζ → δ c = c →
        (∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j) →
        ∀ v ∈ V, fieldActor (unitaryInvolution K ℓ f) δ * v =
          v * fieldActor (unitaryInvolution K ℓ f) δ) ∧
      (∀ v ∈ V, ∀ s : Su K ℓ f 6, ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag →
        v (TwE6Conc.leviSU hK hf hζ hσζ P hP s) = TwE6Conc.leviSU hK hf hζ hσζ P hP s)

@[expose] def TwE6JCompInput : Prop :=
  ∀ {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ],
    Nat.card K = (ℓ ^ f) ^ 2 → 1 ≤ f → ℓ ≠ 2 → 3 ∣ ℓ ^ f + 1 →
    ∀ {c : Kˣ}, orderOf c = 3 →
    ∀ (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)),
    GLAPComponent 3 (Subgroup.centralizer
        ((Subgroup.zpowers (TwE6Conc.twE6R0 c hct) :
          Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
            Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))))
      ((TwE6Conc.leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)))

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
