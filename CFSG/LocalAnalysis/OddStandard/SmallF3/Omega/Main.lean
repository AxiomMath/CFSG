module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Bridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.LBalMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Cores

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def AschOmega5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .PSp 2 3 1 → LieModel G .PSL 4 2 2

@[expose] def AschOmega6Plus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .PSL 4 3 1 → False

@[expose] def AschOmega6Minus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .PSU 4 3 1 → False

@[expose] def AschOmega7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .POmegaOdd 3 3 1 → False

@[expose] def AschOmega8Plus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .POmegaPlus 4 3 1 → False

@[expose] def AschOmega8Minus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .POmegaMinus 4 3 1 → False

@[expose] def AschOmega6MinusZ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsTwoU43 (L ⧸ oddCore L) → False

theorem aschMainTheorem_of_cases (h5 : AschOmega5) (h6p : AschOmega6Plus)
    (h6m : AschOmega6Minus) (h7 : AschOmega7) (h8p : AschOmega8Plus) (h8m : AschOmega8Minus)
    (h6z : AschOmega6MinusZ2) : AschMainTheorem := by
  intro G _ _ hsimple hK hn hA1 hA2 ⟨L, hF, hC⟩
  by_cases hchev : Chev3 G
  · exact Or.inl hchev
  · obtain ⟨t, ht, hLt⟩ := hC
    have hset : Sec3SettingLB G t L :=
      sec3SettingLB_of_sec3Setting hK hn ⟨hsimple, hA1, hA2, hchev, ht, hLt, hF⟩
    unfold InF IsFGroup at hF
    obtain ⟨-, hQ⟩ := hF
    rcases hQ with hQ | hQ
    · unfold SmallF3OmegaQuotient at hQ
      rcases hQ with h | h | h | h | h | h
      · exact Or.inr (h5 G t L hset h)
      · exact (h6p G t L hset h).elim
      · exact (h6m G t L hset h).elim
      · exact (h7 G t L hset h).elim
      · exact (h8p G t L hset h).elim
      · exact (h8m G t L hset h).elim
    · exact (h6z G t L hset hQ).elim

theorem smallF3OmegaAsc_of_cases (h5 : AschOmega5) (h6p : AschOmega6Plus)
    (h6m : AschOmega6Minus) (h7 : AschOmega7) (h8p : AschOmega8Plus) (h8m : AschOmega8Minus)
    (h6z : AschOmega6MinusZ2) : SmallF3OmegaAsc :=
  smallF3OmegaAsc_of_aschMainTheorem (aschMainTheorem_of_cases h5 h6p h6m h7 h8p h8m h6z)

theorem smallF3OmegaCore_of_cases (h5 : AschOmega5) (h6p : AschOmega6Plus)
    (h6m : AschOmega6Minus) (h7 : AschOmega7) (h8p : AschOmega8Plus) (h8m : AschOmega8Minus)
    (h6z : AschOmega6MinusZ2) (hV : SmallF3OmegaV) : SmallF3OmegaCore :=
  smallF3OmegaCore_of_asc_of_v (smallF3OmegaAsc_of_cases h5 h6p h6m h7 h8p h8m h6z) hV

end CFSG.OddStandard.SmallF3.Omega
