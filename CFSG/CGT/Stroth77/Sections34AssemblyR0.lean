module

public import CFSG.CGT.Stroth77.Section41
public import CFSG.CGT.Stroth77.Section44
public import CFSG.CGT.Stroth77.Stroth34Defs

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem stroth_4_4_of_parts'
    (h34b' : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t201 m)), F.IsD D dD → 1 ≤ m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        Rel34i dD e (2 ^ (m + 1))) ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34inv dD e 0 1 2 ∨ Rel34inv dD e (2 ^ (m + 1)) 1 2))
    (hfus201 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t201 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (hR0 : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
      {dD : StrothWeakTypeData D (.t201 m)}, F.IsD D dD → 1 ≤ m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      (∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) →
      ∀ {e : G}, e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
        Rel34i dD e (2 ^ (m + 1)) →
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e)
    (hA44 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G}
      {m : ℕ} (dD : StrothWeakTypeData D (.t201 m)),
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
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → False)
    (hii44 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G}
      {m : ℕ} (dD : StrothWeakTypeData D (.t201 m)),
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
      ∀ e, e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv → e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t →
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = dD.c →
      e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1) →
      e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1) → e * e = (dD.c : G)⁻¹ → False)
    (hiii44 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G}
      {m : ℕ} (dD : StrothWeakTypeData D (.t201 m)),
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
      ∀ e, e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv → e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t →
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ →
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ → e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ →
      e * e = 1 → False) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G) (m : ℕ)
      (dD : StrothWeakTypeData D (.t201 m)),
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
      ∃ e ∈ (F.S : Subgroup G),
        (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, e} ∧
        e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
        e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) ∧
        e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) ∧
        e * e = 1 ∧ e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t ∧ e⁻¹ * dD.u * e = dD.u := by
  intro G _ _ F D m dD hm h hns hmax hSN hnc h11
  have hncD : (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) := by
    obtain ⟨x, hx, y, hy, hox, hoy, hxy⟩ := hnc
    rw [← h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, hox, y, hy, hoy, hxy⟩
  have hfus := hfus201 F dD h hncD
  refine h.stroth_4_4 (h.eq_sup_closure hSN) ?_ (hA44 F dD hm h hns hmax hSN hnc h11)
    (hii44 F dD hm h hns hmax hSN hnc h11) (hiii44 F dD hm h hns hmax hSN hnc h11)
  rcases h34b' F dD h hm hns hfus with hR | ⟨e, heR, hrel⟩ | ⟨e, heR, hRe, hrel⟩
  · exact Or.inl hR
  ·
    have hRe := hR0 h hm hns hmax hSN hnc h11 hfus heR hrel
    obtain ⟨hc, ha, hb, he2, huv, ht, hu⟩ := hrel
    exact Or.inr ⟨e, heR, hRe, huv, by rw [inv_pow]; exact ht, hu, Or.inl ⟨hc, ha, hb, he2⟩⟩
  · refine Or.inr ⟨e, heR, hRe, ?_⟩
    rcases hrel with ⟨hc, ha, hb, he2, huv, ht, hu⟩ | ⟨hc, ha, hb, he2, huv, ht, hu⟩
    · rw [pow_zero, mul_one] at ha hb
      exact ⟨huv, by rw [inv_pow]; exact ht, hu, Or.inr (Or.inl ⟨hc, ha, hb, he2⟩)⟩
    · exact ⟨huv, by rw [inv_pow]; exact ht, hu, Or.inr (Or.inr ⟨hc, ha, hb, he2⟩)⟩

end CFSG.CGT.Stroth77
