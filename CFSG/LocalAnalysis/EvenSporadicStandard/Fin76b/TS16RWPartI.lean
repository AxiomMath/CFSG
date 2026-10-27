module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClauses
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurjM
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWE0

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open Subgroup

section PartI

variable {M : Type*} [Group M] [Finite M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4}
  {t z σ g : M} {N : Subgroup M}

@[expose] def InducedStab (D E : Subgroup M) [(D ⊔ E).Normal] : Prop :=
  ∀ α : MulAut ↥(D ⊔ E),
    (∀ x : ↥(D ⊔ E), (x : M) ∈ D → ((α x : ↥(D ⊔ E)) : M) ∈ D) →
    (∀ x : ↥(D ⊔ E), (x : M) ∈ E → ((α x : ↥(D ⊔ E)) : M) ∈ E) →
    ∃ m : M, MulAut.conjNormal m = α

section Generic

variable [(D ⊔ E).Normal] [N.Normal] {eltE : ℕ → M}

theorem partI_surj (hctx : DECtx D E eD t eltE) (hΓ0 : InducedStab D E)
    (hza : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹) (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1)
    (hg : g * z * g⁻¹ = σ) : ∀ α : MulAut ↥(D ⊔ E), ∃ m : M, MulAut.conjNormal m = α := by
  obtain ⟨h1, h2⟩ := moves_lemma hza hσa hg hctx.a_ne_inv
  exact hctx.surj_of_moves hΓ0 h1 h2

theorem partI_clauses (hctx : DECtx D E eD t eltE) (hΓ0 : InducedStab D E)
    (hN : ∀ n ∈ N, Odd (orderOf n))
    (hker : Subgroup.centralizer ((D ⊔ E : Subgroup M) : Set M) = N ⊔ Subgroup.zpowers t)
    (hz2 : z * z = 1) (hzE : ∀ e ∈ E, z * e = e * z)
    (hza : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹)
    (hzb : z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4)
    (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1) (hg : g * z * g⁻¹ = σ) :
    ∃ Q' P : Subgroup M, IsPGroup 2 Q' ∧ ¬ 2 ∣ Q'.index ∧ z ∈ Q' ∧ P ≤ Q' ∧
      P.relIndex Q' = 2 ∧ z ∉ P ∧
      (∃ R : Subgroup M, IsPGroup 2 R ∧ R ≤ Subgroup.centralizer ({z} : Set M) ∧
        Nat.card R = 512) ∧
      (∀ η ∈ P, η * η = 1 → η ≠ 1 → ∃ R : Subgroup M, IsPGroup 2 R ∧
        R ≤ Subgroup.centralizer ({η} : Set M) ∧ 1024 ≤ Nat.card R) ∧
      (∀ y ∈ Q', y * y = 1 → y ∉ P →
        512 ≤ Nat.card ↥(Q' ⊓ Subgroup.centralizer ({y} : Set M)) → ∃ m : M, y = m * z * m⁻¹) :=
  PartIData.clauses ⟨hctx, hN, hker, partI_surj hctx hΓ0 hza hσa hg, hz2, hzE, hza, hzb⟩

end Generic

end PartI

end CFSG.EvenSporadicStandard.Fin76b.W16
