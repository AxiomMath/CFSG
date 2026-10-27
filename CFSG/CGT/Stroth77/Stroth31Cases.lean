module

public import CFSG.CGT.Stroth77.Stroth31Proof

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def strothCab {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) : G :=
  (dD.c : G) * (dD.a : G) * (dD.b : G)

@[expose] noncomputable def strothAB {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) : G :=
  (dD.a : G) * (dD.b : G)

@[simp] theorem strothCab_def {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) :
    strothCab dD = (dD.c : G) * (dD.a : G) * (dD.b : G) := rfl

@[simp] theorem strothAB_def {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) :
    strothAB dD = (dD.a : G) * (dD.b : G) := rfl

@[expose] def strothConj (r x : G) : G := r⁻¹ * x * r

@[simp] theorem strothConj_def (r x : G) : strothConj r x = r⁻¹ * x * r := rfl

theorem sq_mem_D_of_minimal {X : StrothAmbient G} (Z : StrothDatum X)
    (C : Subgroup G)
    (hDC : Z.D ≤ C) (hCR : C ≤ strothR X Z.D)
    (hmin : IsMinimalLModuleMod Z.dataD C) {r : G} (hrC : r ∈ C) :
    r * r ∈ Z.D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hCN : C ≤ Subgroup.normalizer (Z.D : Set G) :=
    hCR.trans (strothR_le_normalizer X Z.D)
  haveI hN : (Z.D.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hCN
  have hLD : ∀ l ∈ Z.dataD.L, l ∈ Subgroup.normalizer (Z.D : Set G) := by
    intro l hl
    rw [Z.hL] at hl
    exact Z.L_le_normalizer hl
  have hEA : IsElementaryAbelian 2 (C ⧸ Z.D.subgroupOf C) :=
    isElementaryAbelian_quotient_of_minimal hDC hCR hmin hLD
  let q : C ⧸ Z.D.subgroupOf C :=
    QuotientGroup.mk' (Z.D.subgroupOf C) ⟨r, hrC⟩
  have hq2 : q ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (C ⧸ Z.D.subgroupOf C)) q
  have hqeq : QuotientGroup.mk' (Z.D.subgroupOf C) ((⟨r, hrC⟩ : C) ^ 2) = 1 := by
    rw [map_pow]
    exact hq2
  have hsub : (⟨r, hrC⟩ : C) ^ 2 ∈ Z.D.subgroupOf C := by
    simpa using hqeq
  have hmem : ((⟨r, hrC⟩ : C) ^ 2 : G) ∈ Z.D :=
    Subgroup.mem_subgroupOf.mp hsub
  simpa [pow_two] using hmem

theorem no_index_four_of_four_cases (X : StrothAmbient G) {m : ℕ} (Z : StrothDatum X)
    (hτ : Z.τ = StrothTypeIndex.t100 m) (C : Subgroup G)
    (hDC : Z.D ≤ C) (hCR : C ≤ strothR X Z.D)
    (hmin : IsMinimalLModuleMod Z.dataD C)
    (h4 : (Z.D.subgroupOf C).index = 4)
    (hr : ∃ r : G, r ∈ C ∧ r ∉ Z.D ∧
      strothConj r (Z.dataD.uv : G) = (Z.dataD.uv : G) ∧
      (∃ d ∈ Z.D, strothConj r (Z.dataD.t : G) = d * (Z.dataD.t : G)) ∧
      (∃ d ∈ Z.D, strothConj r (Z.dataD.u : G) = d * (Z.dataD.u : G)))
    (hcover : ∀ r : G, r ∈ C → r ∉ Z.D → r * r ∈ Z.D →
      strothConj r (Z.dataD.uv : G) = (Z.dataD.uv : G) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.t : G) = d * (Z.dataD.t : G)) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.u : G) = d * (Z.dataD.u : G)) →
      (strothConj r (strothCab Z.dataD) = strothCab Z.dataD ∨
       strothConj r (strothCab Z.dataD) =
         strothCab Z.dataD * (strothAB Z.dataD) ^ (2 ^ m) ∨
       strothConj r (strothCab Z.dataD) = (strothCab Z.dataD)⁻¹ ∨
       strothConj r (strothCab Z.dataD) =
         (strothCab Z.dataD)⁻¹ * (strothAB Z.dataD) ^ (2 ^ m)))
    (hcase1 : (Z.D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ Z.D → r * r ∈ Z.D →
      strothConj r (Z.dataD.uv : G) = (Z.dataD.uv : G) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.t : G) = d * (Z.dataD.t : G)) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.u : G) = d * (Z.dataD.u : G)) →
      strothConj r (strothCab Z.dataD) = strothCab Z.dataD → False)
    (hcase2 : (Z.D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ Z.D → r * r ∈ Z.D →
      strothConj r (Z.dataD.uv : G) = (Z.dataD.uv : G) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.t : G) = d * (Z.dataD.t : G)) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.u : G) = d * (Z.dataD.u : G)) →
      strothConj r (strothCab Z.dataD) =
        strothCab Z.dataD * (strothAB Z.dataD) ^ (2 ^ m) → False)
    (hcase3 : (Z.D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ Z.D → r * r ∈ Z.D →
      strothConj r (Z.dataD.uv : G) = (Z.dataD.uv : G) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.t : G) = d * (Z.dataD.t : G)) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.u : G) = d * (Z.dataD.u : G)) →
      strothConj r (strothCab Z.dataD) = (strothCab Z.dataD)⁻¹ → False)
    (hcase4 : (Z.D.subgroupOf C).index = 4 → ∀ r : G, r ∈ C → r ∉ Z.D → r * r ∈ Z.D →
      strothConj r (Z.dataD.uv : G) = (Z.dataD.uv : G) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.t : G) = d * (Z.dataD.t : G)) →
      (∃ d ∈ Z.D, strothConj r (Z.dataD.u : G) = d * (Z.dataD.u : G)) →
      strothConj r (strothCab Z.dataD) =
        (strothCab Z.dataD)⁻¹ * (strothAB Z.dataD) ^ (2 ^ m) → False) :
    False := by
  obtain ⟨r, hrC, hrD, huv, ht, hu⟩ := hr
  have hrsq : r * r ∈ Z.D := sq_mem_D_of_minimal Z C hDC hCR hmin hrC
  rcases hcover r hrC hrD hrsq huv ht hu with h1 | h2 | h3 | h4c
  · exact hcase1 h4 r hrC hrD hrsq huv ht hu h1
  · exact hcase2 h4 r hrC hrD hrsq huv ht hu h2
  · exact hcase3 h4 r hrC hrD hrsq huv ht hu h3
  · exact hcase4 h4 r hrC hrD hrsq huv ht hu h4c

end CFSG.CGT.Stroth77
