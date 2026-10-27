module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

structure K7Abs {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] (ρ : Γ →* MulAut M)
    (t : Γ) (J Q P M6 M7 : Subgroup Γ) : Prop where
  kgroup : CFSG.SectionRank.IsKGroupCat Γ
  M_E : IsE 6 M
  t_sq : t ^ 2 = 1
  t_ne : t ≠ 1
  J_iso : Nonempty (↥J ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))
  J_cent : ∀ j ∈ J, j * t = t * j
  J_fpf : ∀ x ∈ J, x ^ 7 = 1 → x ≠ 1 → ∀ m : M, ρ x m = m → m = 1
  ρ_inj : ∀ j ∈ J, ρ j = 1 → j = 1
  Q_two : IsPGroup 2 ↥Q
  Q_card : Nat.card ↥Q ≤ 4
  Q_J : ∀ q ∈ Q, ∀ j ∈ J, q * j = j * q
  t_mem_Q : t ∈ Q
  cent : ∀ x : Γ, x * t = t * x → ∃ j ∈ J, ∃ q ∈ Q, x = j * q
  P_two : IsPGroup 2 ↥P
  P_card : Nat.card ↥P = 2 ^ 6
  P_sup : P = M6 ⊔ M7
  M6_E : IsE 4 ↥M6
  M7_E : IsE 4 ↥M7
  M67 : M6 ≠ M7
  P_norm_t : ∀ x ∈ P, t * x * t⁻¹ ∈ P
  P_cent_t : ∀ x ∈ P, x * t = t * x → x ∈ J
  M6_gen : M6 ≤ ⁅J, M6⁆
  M7_gen : M7 ≤ ⁅J, M7⁆
  comm_wit : ∃ m : Γ, ⁅m, t⁆ ∈ J ∧ ⁅m, t⁆ ≠ 1

end CFSG.OddStandard.HigherRank.YamadaG23
