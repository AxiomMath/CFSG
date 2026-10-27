module

public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.CGT.Stroth77.Stroth31Fusion
public import CFSG.CGT.Stroth77.Stroth31Cases

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

theorem stroth_3_1 {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A)
    (C : Subgroup G) (hCR : C ≤ strothR (F.toAmbient hH) D)
    (hmin : IsMinimalLModuleMod (h.toDatum hH).dataD C)
    (hno4 : ((h.toDatum hH).D.subgroupOf C).index ≠ 4) :
    Nat.card C = 2 * Nat.card D :=
  stroth_3_1'_of_no_index_four (F.toAmbient hH) (h.toDatum hH) rfl C
    hmin.d_lt.le hCR hmin hno4

theorem no_index_four_of_four_cases {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A)
    (C : Subgroup G) (hCR : C ≤ strothR (F.toAmbient hH) D)
    (hmin : IsMinimalLModuleMod (h.toDatum hH).dataD C)
    (hr : ∃ r : G, r ∈ C ∧ r ∉ D ∧
      strothConj r (dD.uv : G) = (dD.uv : G) ∧
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) ∧
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)))
    (hcover : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      (strothConj r (strothCab dD) = strothCab dD ∨
       strothConj r (strothCab dD) = strothCab dD * (strothAB dD) ^ (2 ^ m) ∨
       strothConj r (strothCab dD) = (strothCab dD)⁻¹ ∨
       strothConj r (strothCab dD) = (strothCab dD)⁻¹ * (strothAB dD) ^ (2 ^ m)))
    (hcase1 : (D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (strothCab dD) = strothCab dD → False)
    (hcase2 : (D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (strothCab dD) = strothCab dD * (strothAB dD) ^ (2 ^ m) → False)
    (hcase3 : (D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (strothCab dD) = (strothCab dD)⁻¹ → False)
    (hcase4 : (D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (strothCab dD) = (strothCab dD)⁻¹ * (strothAB dD) ^ (2 ^ m) → False) :
    ((h.toDatum hH).D.subgroupOf C).index ≠ 4 := by
  intro h4
  exact CFSG.CGT.Stroth77.no_index_four_of_four_cases (F.toAmbient hH) (h.toDatum hH) rfl C
    hmin.d_lt.le hCR hmin h4 hr hcover hcase1 hcase2 hcase3 hcase4

end StrothFrame.IsD

end CFSG.CGT.Stroth77
