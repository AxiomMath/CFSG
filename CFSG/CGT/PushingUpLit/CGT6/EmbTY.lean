module

public import CFSG.CGT.PushingUpLit.CGT6.EmbHyp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.ThompsonPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem commutator_eq_bot_of_centralizer {G₀ T Y Q : Subgroup Γ} (hNo : SubTwo.NoTwoQuotient Y)
    (hcase : ⁅Y, Y⁆ = Y ∨ Nat.card ↥Y = 3) (hO : ⁅oTwoIn Y, Y⁆ = ⊥) (hT2 : IsPGroup 2 T)
    (hQ2 : IsPGroup 2 Q) (hQG : Q ≤ G₀) (hTQ : T ≤ Subgroup.normalizer (Q : Set Γ))
    (hYQ : Y ≤ Subgroup.normalizer (Q : Set Γ))
    (hYH : Y ≤ G₀ ⊓ Subgroup.centralizer (T : Set Γ))
    (hs : (Y.subgroupOf (G₀ ⊓ Subgroup.centralizer (T : Set Γ))).IsSubnormal) : ⁅Q, Y⁆ = ⊥ := by
  have hYT : Y ≤ Subgroup.centralizer (T : Set Γ) := fun y hy => (hYH hy).2
  set R : Subgroup Γ := Q ⊓ Subgroup.centralizer (T : Set Γ) with hR
  have hR2 : IsPGroup 2 R := hQ2.to_le inf_le_left
  have hRH : R ≤ G₀ ⊓ Subgroup.centralizer (T : Set Γ) :=
    le_inf (inf_le_left.trans hQG) inf_le_right
  have hYR : Y ≤ Subgroup.normalizer (R : Set Γ) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hYQ hy, Subgroup.le_normalizer (hYT hy)⟩
  have hRY : ⁅R, Y⁆ = ⊥ :=
    commutator_eq_bot_of_subnormal_sup hNo hR2 hYR hYH hRH hs hO hcase
  have hTY : ⁅T, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hYT
  have hfix : Q ⊓ Subgroup.centralizer (T : Set Γ) ≤ Subgroup.centralizer (Y : Set Γ) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hRY
  rcases hcase with hperf | h3
  · exact thompson_p_times_perfect T Y Q hT2 hQ2 hperf hTQ hYQ hTY hfix
  · exact GorensteinWalter.ThompsonPQ.thompson_p_times_q T Y Q hT2 hQ2 (by rw [h3]; norm_num) hTQ
      hYQ hTY hfix

end CFSG.CGT.PushingUpLit.CGT6
