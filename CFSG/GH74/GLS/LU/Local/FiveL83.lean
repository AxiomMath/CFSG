module

public import CFSG.GH74.GLS.LU.Local.FiveL83g
public import CFSG.GH74.GLS.LU.Local.FiveL83f

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

theorem exists_Y83W
    {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (ctx : FiveCtx G p f z S K₁ K₂ t u) {H : Subgroup G} {w₁ : G}
    (b66 : Five66W z t u K₁ K₂ H w₁) {X₁ : Subgroup G} (b82 : Five82W z t u K₁ K₂ H w₁ X₁) :
    ∃ Y : Subgroup G, Five83 z t u H X₁ Y := by
  have c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁ := ⟨ctx, b66, b82⟩
  have hcent : ∀ y : G, y * y = 1 → y ≠ 1 → y ∈ CZ t X₁ ⊔ zpowers u →
      Nat.card ↥(centralizer ({y} : Set G)) ∣ 28800 := by
    intro y hy2 hy1 _
    have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    exact (c.card_cent_of_conj (c.isConj_of_invol hord)) ▸ dvd_refl _
  have hq : C0Quot (CZ t X₁) (TT z t) :=
    c0Quot_abstract (CZ t X₁) (TT z t) u c.hs.u_sq c.u_norm_C0 c.u_not_mem_C0 c.T_le_C0 c.card_TT
      c.TT_comm c.TT_sq c.card_C0_two c.u_comm_TT hcent
  exact c.exists_Y83 hq

theorem leaf83 :
    Leaf83 := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82
  exact exists_Y83W ctx b66.toW b82.toW

end CFSG.GH74.GLS.LU.Local.Five
