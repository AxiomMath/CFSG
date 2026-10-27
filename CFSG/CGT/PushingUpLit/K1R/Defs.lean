module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint

@[expose] def NoFour {D : Type*} [Group D] (H : Subgroup D) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * x = 1 → y * y = 1 → x * y = y * x → x = 1 ∨ y = 1 ∨ x = y

theorem NoFour.mono {D : Type*} [Group D] {H H' : Subgroup D} (h : NoFour H) (hle : H' ≤ H) :
    NoFour H' :=
  fun x hx y hy => h x (hle hx) y (hle hy)

@[expose] def InnerKernelSelector (P : (D : Type) → [Group D] → Prop) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → P D → ∀ (n : ℕ), 2 ≤ n →
    ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
    ∀ (α : MulAut D), orderOf α = 2 → α ∈ (MulAut.conj : D →* MulAut D).range →
    ∀ (S : Subgroup D), S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) →
      (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal →
      Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) →
      NoFour (α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D)) →
      ∀ Q : Subgroup D, Q ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D) →
        IsPGroup 2 Q → Nat.card Q ≤ 2

theorem InnerKernelSelector.of_false {P : (D : Type) → [Group D] → Prop}
    (h : ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → P D → ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ∀ (α : MulAut D), orderOf α = 2 → α ∈ (MulAut.conj : D →* MulAut D).range →
      ∀ (S : Subgroup D), S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) →
        (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal →
        Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) →
        NoFour (α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D)) → False) :
    InnerKernelSelector P :=
  fun D _ _ hD hP n hn K _ _ hK α hα hin S hSα hSn hSK h4 _ _ _ =>
    (h D hD hP n hn K hK α hα hin S hSα hSn hSK h4).elim

end CFSG.CGT.PushingUpLit.K1R
