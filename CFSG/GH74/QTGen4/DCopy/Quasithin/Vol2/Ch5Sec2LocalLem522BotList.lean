module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotA

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.Background.Harris.F112S3Big

@[expose] def Stmt5_2_2_bot_D4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    Hyp111 L₂ (Dp ⊔ sec52S M H) (sec52S M H) →
    (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
        centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
      centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G)) →
    IsL2Quot 3 (oTwoQuot ↥L₂) → IsSpecialPow 2 2 4 ↥(pCoreOf 2 L₂) →
    Nat.card ↥(pCoreOf 2 (Dp ⊔ sec52S M H)) = 2 ^ 11 → False

@[expose] def Stmt5_2_2_bot_J2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    Hyp111 L₂ (Dp ⊔ sec52S M H) (sec52S M H) →
    (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
        centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
      centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G)) →
    IsL2Quot 2 (oTwoQuot ↥L₂) → IsQ8D8 ↥(pCoreOf 2 L₂) →
    Nat.card ↥(pCoreOf 2 (Dp ⊔ sec52S M H)) = 2 ^ 6 → False

@[expose] def Stmt5_2_2_bot_U4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    Hyp111 (Dp ⊔ sec52S M H) L₂ (sec52S M H) →
    (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
        centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
      centerOf (sec52S M H) ≤
        Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G)) →
    IsSpecialPow 2 2 2 ↥(pCoreOf 2 (Dp ⊔ sec52S M H)) → IsBlock2 L₂ L₂ →
    IsL2Quot 2 (oTwoQuot ↥L₂) → IsOmega4MinusType L₂ 1 → IsAltType L₂ 5 → False

theorem stmt5_2_2_bot_list_of_F4 (hD4 : Stmt5_2_2_bot_D4_F4) (hJ2 : Stmt5_2_2_bot_J2_F4)
    (hU4 : Stmt5_2_2_bot_U4_F4) : Stmt5_2_2_bot_list_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n hyp hO hS3 L1' L2' hor h111 hcen hlist
  have hY : ∀ {X : Subgroup G}, X = Dp ⊔ sec52S M H →
      IsSylowTwoOf (sec52S M H ⊓ X) X → IsSylowTwoOf (sec52S M H) (Dp ⊔ sec52S M H) := by
    rintro X rfl h
    rwa [inf_eq_left.mpr le_sup_right] at h
  unfold F112ListBLoc F112B4Loc F112B6Loc F112B10Loc F112B11Loc at hlist
  rcases hlist with h4 | h6 | h10 | h11
  · obtain ⟨rfl, rfl⟩ := orient_of_isL2Quot_left (f := 3) (by norm_num) hS3 hor h4.1
    exact hD4 G T M L V H B D L1' Dp n hyp hO hS3 h111 hcen h4.1 h4.2.1 h4.2.2.2
  · obtain ⟨rfl, rfl⟩ := orient_of_isL2Quot_right (f := 2) (by norm_num) hS3 hor h6.2.2.2.1
    exact hU4 G T M L V H B D L2' Dp n hyp hO hS3 h111 hcen h6.2.1 h6.2.2.1 h6.2.2.2.1
      h6.2.2.2.2.1 h6.2.2.2.2.2
  · obtain ⟨rfl, rfl⟩ := orient_of_isL2Quot_left (f := 2) (by norm_num) hS3 hor h10.1
    exact hJ2 G T M L V H B D L1' Dp n hyp hO hS3 h111 hcen h10.1 h10.2.1 h10.2.2.2
  · obtain ⟨rfl, rfl⟩ := orient_of_perm_five le_sup_right hS3 hor h11.1
    exact false_of_autJ2_entry (hY rfl h111.h2.sylow) hS3 h11.2.2.2 h111.h1.normalizes
      h111.h1.sylow h11.1 h11.2.1.1

end CFSG.Quasithin.H13
