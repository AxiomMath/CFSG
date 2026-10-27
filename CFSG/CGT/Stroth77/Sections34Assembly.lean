module

public import CFSG.CGT.Stroth77.Sections34AssemblyAux
public import CFSG.CGT.Stroth77.Section42CoreSplit
public import CFSG.CGT.Stroth77.Section42CoreT101
public import CFSG.CGT.Stroth77.Section43Gold
public import CFSG.CGT.Stroth77.Stroth34Defs
public import CFSG.CGT.Timmesfeld75.GoldschmidtMilestone
public import CFSG.CGT.Stroth77.Section41
public import CFSG.CGT.Stroth77.Section43C
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)
open CFSG.OddStandard.HigherRank.YamadaG23 (IsQuotIso LitStrothType LitPSLU4S HasPSL6Sylow
  StrothSigma6)

theorem stroth_4_3_hA_of_core :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
      F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      ((∃ m, τ = .t100 m) ∨ ∃ s, τ = .t101 s) → False := by
  intro G _ _ F D τ dD h hns hmax hSN hnc h11 hS hτ
  rcases hτ with ⟨m, rfl⟩ | ⟨s, rfl⟩
  · have hm := h.two_le_of_t100_of_dvd h11
    exact h.false_of_split (j := m - 1) (by omega) (show m = m - 1 + 1 by omega) hnc hS
      (dD.t100_h1 hm) (dD.t100_h2 hm) (dD.t100_h3 hm) (dD.t100_h4 hm) dD.t100_h5
      (dD.t100_h6 hm) (dD.t100_h6' hm) (dD.t100_h7 hm) (dD.t100_h8 hm) (dD.t100_h9 hm)
  · have hs := h.one_le_of_t101_of_dvd h11
    exact h.false_of_split (j := s) hs rfl hnc hS dD.t101_h1 dD.t101_h2 dD.t101_h3
      (dD.t101_h4 hs) dD.mul_self_mem_or (dD.t101_h6 hs) (dD.t101_h6' hs) dD.t101_h7
      (dD.t101_h8 hs) dD.t101_h9

section Goldschmidt

theorem stroth_4_3_he_of_core
    (hcoreII : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)) {e : G}, 2 ≤ m →
      e ∈ Subgroup.normalizer (D : Set G) →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      e⁻¹ * (dD.c : G) * e = dD.c → e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m →
      e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m →
      e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) →
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
        (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 ∧
      e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
        y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
          y ^ 2 ^ m ≠ (dD.c : G) ^ 2 ^ (m - 1)) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y * y ∈ D ∨ y * y * dD.uv ∈ D) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → y * y ≠ 1) ∧
      (∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
        ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ m ≠ 1) ∧
      (∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D))
    (hcoreIII : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)) {e : G}, 2 ≤ m →
      e ∈ Subgroup.normalizer (D : Set G) →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ → e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ →
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ → e * e = 1 →
      (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e}).relIndex
        (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 ∧
      (dD.c : G) ∉
        Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} ∧
      (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
        (dD.c : G) * e}).relIndex
        (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 ∧
      (dD.c : G) * dD.a * dD.uv ∉
        Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
        (dD.c : G) * e} ∧
      (∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e},
        y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
          y ^ 2 ^ (m - 1) ≠ (dD.c : G) ^ 2 ^ (m - 1)) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y * y ∈ D ∨ y * y * dD.uv ∈ D) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} →
        ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ (m - 1) ≠ 1) ∧
      (∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y * y = 1 → y ≠ 1 → y ≠ (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m →
          ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
            q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) =
          (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m * y) ∧
      (∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e},
        y * dD.uv ∈ D → y * y = 1 →
          ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
            q⁻¹ * y * q = dD.uv) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} →
        y * y = 1 → IsConj y ((dD.c : G) * dD.a * dD.uv) ∨ IsConj y ((dD.c : G) * e) ∨
          IsConj y ((dD.c : G) * dD.u * e)) ∧
      (∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e},
        y * y = 1 → y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
          IsConj y ((dD.a : G) ^ 2 ^ m) ∨ IsConj y dD.uv ∨ IsConj y dD.u ∨
          IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∨ IsConj y e ∨ IsConj y (dD.u * e)) ∧
      (∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
        (dD.c : G) * e},
        y * y = 1 → y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
          IsConj y ((dD.a : G) ^ 2 ^ m) ∨ IsConj y dD.uv ∨ IsConj y dD.u ∨
          IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∨ IsConj y ((dD.c : G) * e) ∨
          IsConj y ((dD.c : G) * dD.u * e)) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y * e ∈ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
          ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
            q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * y) ∧
      (∀ E : Subgroup G, E ≤ D ⊔ Subgroup.zpowers dD.u → (∀ y ∈ E, y * y = 1) →
        Nat.card E = 8 → (dD.c : G) ^ 2 ^ (m - 1) ∈ E) ∧
      (∀ y₁ ∈ D ⊔ Subgroup.zpowers dD.u, ∀ y₂ ∈ D ⊔ Subgroup.zpowers dD.u,
        y₁ * y₁ = 1 → y₂ * y₂ = 1 → (y₁ * y₂) ^ 2 ^ (m + 1) = 1) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
          y ∈ D ⊔ Subgroup.zpowers dD.u ∨ y * e ∈ D ⊔ Subgroup.zpowers dD.u) ∧
      (dD.c : G) * dD.a * dD.uv * ((dD.c : G) * dD.a * dD.uv) = 1 ∧
      (dD.c : G) * dD.a * dD.uv * (dD.u * e) = dD.u * e * ((dD.c : G) * dD.a * dD.uv) ∧
      (dD.t * dD.a)⁻¹ * ((dD.c : G) * dD.a * dD.uv * (dD.u * e)) * (dD.t * dD.a) =
        (dD.c : G) * dD.u * e ∧
      (Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t} ≤
          Subgroup.centralizer {(dD.c : G) * dD.a * dD.uv} ∧
        (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t}, y * y = 1) ∧
        Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t}) = 8) ∧
      ((dD.c : G) ^ 2 ^ (m - 1) * dD.u * (dD.u * e) =
          dD.u * e * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∧
        ((dD.c : G) * dD.a * dD.uv * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u)) ^ 2 ^ (m + 1) ≠ 1))
    (hcoreIV : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)) {e : G}, 2 ≤ m →
      e ∈ Subgroup.normalizer (D : Set G) →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ →
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m →
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m →
      e * e = (dD.c : G) ^ 2 ^ (m - 1) →
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
        (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 ∧
      e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y * y ∈ D ∨ y * y * dD.uv ∈ D) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → y * y ≠ 1) ∧
      (∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16) ∧
      (∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D) ∧
      (∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
        y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
          y * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * y))
    (hfusIII : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)) {e : G},
      F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      2 ≤ m → e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ → e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ →
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ → e * e = 1 →
      (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.uv, dD.t},
        y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ m)) ∧
      IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)) ∧
      IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ m))
    (hscIV : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)) {e : G},
      F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      2 ≤ m → e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ →
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m →
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m →
      e * e = (dD.c : G) ^ 2 ^ (m - 1) →
      ∀ g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        ∀ y ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2)), g⁻¹ * y * g ∈ (F.S : Subgroup G) →
          g⁻¹ * y * g ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2))) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
      F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      ∀ m e, τ = .t100 m → e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) → False := by
  have hGold : CFSG.CGT.Timmesfeld75.Goldschmidt1974 :=
    CFSG.CGT.Timmesfeld75.goldschmidt1974_of_milestone
  intro G _ _ F D τ dD h hns hmax hSN hnc h11 m e hτ heN hS huv ht hu hcases
  subst hτ
  have hm := h.two_le_of_t100_of_dvd h11
  have h3 := dD.t100_h3 hm
  have h6 := dD.t100_h6 hm
  rcases hcases with ⟨hc, ha, hb, hee⟩ | ⟨hc, ha, hb, hee⟩ | ⟨hc, ha, hb, hee⟩
  · obtain ⟨h1, h2, h4, h5, h6', h7, h8, h9⟩ := hcoreII dD hm heN huv ht hu hc ha hb hee
    exact h.false_of_t100_ii hm hnc heN hee hS h1 h2 h3 h4 h5 h6 h6' h7 h8 h9
  · obtain ⟨hE, hu', hzu⟩ :=
      hfusIII F dD h hns hmax hSN hnc h11 hm heN hS huv ht hu hc ha hb hee
    obtain ⟨h1, h2, h1', h2', h4, h5, h8, h9, hC2, hC2c, hC4, hC6, hC7, hC10, hC11, hC13,
      hC14, hC15, hr2, hrue, hrta, hF, hM⟩ := hcoreIII dD hm heN huv ht hu hc ha hb hee
    exact h.false_of_t100_iii hm hnc heN hee hc hu hS hE hu' hzu h1 h2 h1' h2' h3 h4 h5 h8 h9
      hC2 hC2c hC4 hC6 hC7 hC10 hC11 hC13 hC14 hC15 hr2 hrue hrta hF hM
  · obtain ⟨h1, h2, h5, h6', h7, h9, hc₂⟩ := hcoreIV dD hm heN huv ht hu hc ha hb hee
    exact h.false_of_t100_iv hGold hm hnc heN hc hee hS h1 h2 h3 h5 h6 h6' h7 h9 hc₂
      (hscIV F dD h hns hmax hSN hnc h11 hm heN hS huv ht hu hc ha hb hee)

end Goldschmidt

theorem stroth_4_7_of_parts
    (h34 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD → 1 ≤ m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨
          Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
          Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)) ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.closure {e, f} ∧
        Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
        f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
      (2 ≤ m ∧ ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers f ∧
        (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3)))
    (hfus200 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (h47R : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
      1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ⊔
          Subgroup.closure {dD.uv, dD.t, dD.u} →
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨
          Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
          Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)) ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.closure {e, f} ∧
        Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
        f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
      (2 ≤ m ∧ ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers f ∧
        (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3))) →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u}) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G) (m : ℕ)
      (dD : StrothWeakTypeData D (.t200 m)),
      1 ≤ m → F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} := by
  intro G _ _ F D m dD hm h hns hmax hSN hnc h11
  have hncD : (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) := by
    obtain ⟨x, hx, y, hy, hox, hoy, hxy⟩ := hnc
    rw [← h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, hox, y, hy, hoy, hxy⟩
  exact h47R F hm dD h hSN (h.eq_sup_closure hSN) (h34 F dD h hm hns (hfus200 F dD h hncD)) hncD

end CFSG.CGT.Stroth77
