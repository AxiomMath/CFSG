module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67J1
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def CF67Fam (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (J : Subgroup N), IsComponent J →
    F (↥J ⧸ Subgroup.center ↥J) →
    ∀ (r : ℕ), r.Prime → Odd r → ∀ (V Z : Subgroup N),
      IsElementaryAbelian r ↥V → Nat.card ↥V = r ^ 2 →
      (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → Odd (Nat.card ↥Z) → Nat.Coprime (Nat.card ↥Z) r →
      (∀ v ∈ V, ∀ w ∈ Z, v * w = w * v) →
      V ≤ normalizer (J : Set N) → Z ≤ normalizer (J : Set N) →
      (∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N)) →
      ¬ J ≤ centralizer (Z : Set N) →
      (∀ v ∈ V, v ≠ 1 → ∀ c ∈ J, c ∈ centralizer ({v} : Set N) → c ∈ normalizer (Z : Set N)) →
      False

@[expose] def FSporNJ1 (Y : Type) [Group Y] : Prop :=
  NativeSporadic.IsSporadic Y .M11 ∨ NativeSporadic.IsSporadic Y .M12 ∨ NativeSporadic.IsSporadic Y .M22 ∨
    NativeSporadic.IsSporadic Y .M23 ∨ NativeSporadic.IsSporadic Y .J2 ∨ NativeSporadic.IsSporadic Y .J3

@[expose] def CF67Spor : Prop := CF67Fam FSporNJ1
@[expose] def CF67McLy : Prop := CF67Fam FMcLy
@[expose] def CF67Two : Prop := CF67Fam FTwo
@[expose] def CF67L2 : Prop := CF67Fam FL2
@[expose] def CF67L3 : Prop := CF67Fam FL3
@[expose] def CF67U3 : Prop := CF67Fam FU3
@[expose] def CF67Sp4 : Prop := CF67Fam FSp4
@[expose] def CF67G2 : Prop := CF67Fam FG2
@[expose] def CF67D4 : Prop := CF67Fam FD4
@[expose] def CF67L4 : Prop := CF67Fam FL4
@[expose] def CF67U4 : Prop := CF67Fam FU4
@[expose] def CF67L5 : Prop := CF67Fam FL5
@[expose] def CF67U5 : Prop := CF67Fam FU5
@[expose] def CF67Ree : Prop := CF67Fam FRee

theorem cf67NonAltJ1_of_families (hSpor : CF67Spor) (hMcLy : CF67McLy) (hTwo : CF67Two)
    (hL2 : CF67L2) (hL3 : CF67L3) (hU3 : CF67U3) (hSp4 : CF67Sp4) (hG2 : CF67G2) (hD4 : CF67D4)
    (hL4 : CF67L4) (hU4 : CF67U4) (hL5 : CF67L5) (hU5 : CF67U5) (hRee : CF67Ree) :
    CF67NonAltJ1 := by
  intro N _ _ J hJ hGH halt hj1 r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  have hcases := ghList_cases hGH
  have hnoAlt : ¬ FAlt (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨n, hn7, hn11, h⟩
    exact halt n hn7 hn11 h
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact absurd h hnoAlt
  · have hs : FSporNJ1 (↥J ⧸ Subgroup.center ↥J) := by
      rcases h with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact absurd h hj1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    exact hSpor N J hJ hs r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hMcLy N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hTwo N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hL2 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hL3 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hU3 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hSp4 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hG2 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hD4 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hL4 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hU4 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hL5 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hU5 N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  · exact hRee N J hJ h r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3

end CFSG.GH74.GLS.Stage2.Bender.Thm1
