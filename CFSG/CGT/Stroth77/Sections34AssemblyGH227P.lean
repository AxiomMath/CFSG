module

public import CFSG.CGT.Stroth77.Sections34AssemblyV2
public import CFSG.CGT.Stroth77.Section228HuvAll
public import CFSG.CGT.Stroth77.Section310Global
public import CFSG.CGT.Stroth77.Section223X
public import CFSG.CGT.Stroth77.Section223ExtStepProof
public import CFSG.CGT.Stroth77.Sections34ConsumersH227P

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)
open CFSG.OddStandard.HigherRank.YamadaG23 (IsQuotIso LitStrothType LitPSLU4S HasPSL6Sylow
  StrothSigma6)

theorem strothSigma6_of_sections_g_h227p
    (h223 : ∀ {G : Type} [Group G] [Finite G], StrothFrame G →
      ∃ (F : StrothFrame G) (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
        F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (h223Xp : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ') (X : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      IsMulCommutative X → F.A ≤ X →
      X ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ X, x⁻¹ * F.dA.uv * x * F.dA.uv⁻¹ ∈ D' ∧ x⁻¹ * F.dA.t * x * F.dA.t⁻¹ ∈ D') →
      F.dA.L ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) →
      (∀ Y : Subgroup G, Y ≤ X ⊔ D' → IsMulCommutative Y → Nat.card Y = Nat.card X → Y = X) →
      ∃ (F₁ : StrothFrame G) (D₁ : Subgroup G) (τ₁ : StrothTypeIndex)
        (dD₁ : StrothWeakTypeData D₁ τ₁), F₁.IsD D₁ dD₁ ∧
          IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
            ((F₁.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧
          Nat.card X ≤ Nat.card D₁)
    (h226p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ') (B : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n)
    (h227p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n)
    (h228 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      (∃ x : G, x ∈ omegaIn 1 D ∧ orderOf x = 2 ∧
        ∃ y : G, y ∈ omegaIn 1 D ∧ orderOf y = 2 ∧ ∀ g : G, y ≠ g * x * g⁻¹) →
      (∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
        (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n)
    (hcharB : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'), F.IsD D' dD' → τ'.m ≠ τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (h32 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ m, τ = .t100 m → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t ∧ e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))))
    (he : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
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
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) → False)
    (h44 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G) (m : ℕ)
      (dD : StrothWeakTypeData D (.t201 m)), 1 ≤ m → F.IsD D dD →
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
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t ∧ e⁻¹ * dD.u * e = dD.u)
    (h47 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G) (m : ℕ)
      (dD : StrothWeakTypeData D (.t200 m)), 1 ≤ m → F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u})
    (hMason : ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G, Nonempty (↥P ≃* L4Sylow.L4Model n) → LitPSLU4S G) :
    StrothSigma6 := by
  have hGH : CFSG.ComponentClassification.HSFLit.GorensteinHarrisInput :=
    CFSG.ComponentClassification.GHarris.gorensteinHarrisInput_of
      CFSG.ComponentClassification.GHarris.gorensteinHaradaThmCInput_holds
      CFSG.Quasithin.HSType.statementI48_holds
  refine strothSigma6_of_abstract ?_
  intro G _ _ E hG hE hQ hsyl
  obtain ⟨-, φ, hφ, hker⟩ := hQ
  obtain ⟨F₀, -⟩ := exists_strothFrame hG hE φ hφ hker hsyl (stroth15 hG hE φ hφ hker hsyl)
  obtain ⟨F, D, τ, dD, h, hns, hmaxg, hR, hSN⟩ := StrothFrame.stroth_3_10_global (h223 F₀)
    (fun F => h223Xp F) (fun F => hcharB F) (fun F => h226p F)
  have hmax : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D :=
    fun D' τ' dD' h' hns' => hmaxg F D' τ' dD' h' hns'
  have hnonab : ∃ a b : G, a * b ≠ b * a := Stroth42.frame_exists_mul_ne F
  have := F.simple
  have hMasonG : ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G,
      Nonempty (↥P ≃* L4Sylow.L4Model n) → LitPSLU4S G :=
    fun hn P hP => hMason hnonab hn P hP
  by_cases hall : ∀ x ∈ omegaIn 1 F.A, ∀ y ∈ omegaIn 1 F.A, orderOf x = 2 → orderOf y = 2 →
      IsConj x y
  ·
    exact Or.inl (h.isSporadic_HS_of_stroth41_all hGH hSN hR (h227p F D τ dD h hns) hall)
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    push Not at hall
    exact hall
  by_cases h11 : 2 ^ 11 ∣ Nat.card G
  swap
  ·
    exact Or.inr (Or.inl (Stroth76.frame_arch76Lemma3 F h11 (F.not_isConj_w_xy_sq hnc) hMasonG))
  have hSR' := h.eq_sup_closure hSN
  have h228' := h228 F D τ dD h (by
    obtain ⟨x, hx, y, hy, hox, hoy, hxy⟩ := hnc
    rw [← h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, hox, y, hy, hoy, fun g hg => hxy (isConj_iff.mpr ⟨g, hg.symm⟩)⟩)
  have h42' : ∀ n, τ ≠ .t300 n := by
    rintro n rfl
    have hmn : (StrothTypeIndex.t300 n).m = (StrothTypeIndex.t300 n).n := rfl
    have hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
      have h' := hSR'
      rw [hR hmn] at h'
      exact h'
    have hn := dD.three_le_of_t300_of_dvd F.S hS h11
    exact h.stroth_4_2 hn hnc (hR hmn) hSR' (dD.t300_h1 hn) (dD.t300_h2 hn) (dD.t300_h3 hn)
      (dD.t300_h4 hn) dD.t300_h5 (dD.t300_h6 hn) (dD.t300_h6' hn) (dD.t300_h7 hn)
      (dD.t300_h8 hn) (dD.t300_h9 hn)
  have h33' : ∀ s, τ = .t101 s → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D := by
    rintro s rfl
    exact h.stroth_3_3 (h.one_le_of_t101_of_dvd h11)
  rcases StrothFrame.IsD.stroth_4_3 (F := F) (dD := dD) h228' h42' hSR' h33'
      (h32 F D τ dD h hns) (stroth_4_3_hA_of_core F D τ dD h hns hmax hSN hnc h11)
      (he F D τ dD h hns hmax hSN hnc h11) with ⟨m, rfl⟩ | ⟨m, rfl⟩
  ·
    have hm := h.one_le_of_t200
    have h47' := h47 F D m dD hm h hns hmax hSN hnc h11
    have hS : D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} = (F.S : Subgroup G) := by
      rw [h.uv_eq, h.t_eq, h.u_eq, h47']
    exact litStrothType_of_stroth47 hm F dD hS.symm hMasonG
  ·
    obtain ⟨e, -, hS, hec, hea, heb, he2, heuv, het, heu⟩ :=
      h44 F D m dD h.one_le_of_t201 h hns hmax hSN hnc h11
    exact Or.inr (Or.inr (h.hasPSL6Sylow_of_stroth44 hec hea heb he2 heuv het heu hS))

theorem strothSigma6_of_sections_v3_r0_h32_h228_hcharB_g_h227p
    (h226p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ') (B : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n)
    (h227p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n)
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
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u})
    (hMason : ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G, Nonempty (↥P ≃* L4Sylow.L4Model n) → LitPSLU4S G) :
    StrothSigma6 :=
  strothSigma6_of_sections_g_h227p stroth_2_23_frame (StrothFrame.h223X_plus strothExtStep) h226p
    h227p (@StrothFrame.IsD.stroth_2_28_frame_unconditional)
    (stroth_3_10_hcharB_of_plus_h227p h226p h227p
      (@StrothFrame.IsD.stroth_2_28_frame_unconditional) (stroth_3_2_frame_of_h227p h227p))
    (stroth_3_2_frame_of_h227p h227p) stroth_4_3_he_holds
    (stroth_4_4_of_fusion stroth_4_4_hfus201 (@StrothFrame.IsD.eq_sup_zpowers_of_rel34i)
      (@fun _ _ _ _ _ _ _ _ h _ _ _ _ _ => h.t201_fusion))
    (stroth_4_7_of_parts @stroth_3_4 @stroth_4_7_hfus200 h47R) hMason

end CFSG.CGT.Stroth77
