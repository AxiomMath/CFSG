module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1132

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {Q : Type} [Group Q] [Finite Q]

structure GoodData (B M D E1 E2 M4 : Subgroup Q) : Prop where
  D_le : D ≤ B
  B0_le : t113B0 B M ≤ D
  D_norm : D ≤ Subgroup.normalizer (M : Set Q)
  E1_le : E1 ≤ t113K B M
  E1_el : IsElemAbelian 3 E1
  E1_cent : ∀ e ∈ E1, ∀ m ∈ M, e * m = m * e
  E1_dvd : 27 ∣ Nat.card E1
  D_E1 : ∀ z ∈ D, ∀ e ∈ E1, z * e = e * z
  M4_comp : IsComponentOf M4 ⊤
  E2_le : E2 ≤ M4
  E2_el : IsElemAbelian 3 E2
  E2_cent : ∀ e ∈ E2, ∀ m ∈ M, e * m = m * e
  DE1_norm : D ⊔ E1 ≤ Subgroup.normalizer (M4 : Set Q)
  DE1_E2 : ∀ z ∈ D ⊔ E1, ∀ e ∈ E2, z * e = e * z
  card_le : Nat.card B ≤ Nat.card ↥(D ⊔ E1 ⊔ E2)

end CFSG.LocalAnalysis.GLTheoremA.I1132
