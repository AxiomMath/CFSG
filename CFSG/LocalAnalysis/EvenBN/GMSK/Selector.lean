module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRoot

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint

@[expose] def FixedRootSurvivors (D : Type) [Group D] (n : ℕ) : Prop :=
  LieModel D .PSL 2 2 (2 * n) ∨ LieModel D .PSU 3 2 n ∨ LieModel D .PSL 3 2 n ∨
    (n = 2 ∧ (NativeSporadic.IsSporadic D .J1 ∨ NativeSporadic.IsSporadic D .M12 ∨
      Nonempty (D ≃* alternatingGroup (Fin 7)) ∨ LieModel D .PSL 2 5 2 ∨
      LieModel D .PSL 3 5 1 ∨ LieModel D .PSU 3 5 1)) ∨
    (n = 3 ∧ LieModel D .G2 0 3 1)

@[expose] def FixedRootSelector (P : (D : Type) → [Group D] → Prop) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → P D → ∀ (n : ℕ), 2 ≤ n →
    ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
    ∀ (α : MulAut D), orderOf α = 2 → ∀ (S : Subgroup D),
      S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) →
      (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal →
      Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) → FixedRootRankOne α S →
      FixedRootSurvivors D n

theorem FixedRootSelector.mono {P Q : (D : Type) → [Group D] → Prop} (hQ : FixedRootSelector Q)
    (hPQ : ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → P D → Q D) :
    FixedRootSelector P :=
  fun D _ _ hD hP => hQ D hD (hPQ D hD hP)

end CFSG.LocalAnalysis.EvenBN.GMSK
