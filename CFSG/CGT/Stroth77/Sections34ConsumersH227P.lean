module

public import CFSG.CGT.Stroth77.Stroth32Frame
public import CFSG.CGT.Stroth77.Section310CharBT100
public import CFSG.CGT.Stroth77.Section310CharBT101
public import CFSG.CGT.Stroth77.Section310CharBOneT
public import CFSG.CGT.Stroth77.Stroth34T200
public import CFSG.CGT.Stroth77.Section34T201R0
public import CFSG.CGT.Stroth77.Section44Fus
public import CFSG.CGT.Stroth77.Section47Fus

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem stroth_3_2_frame_of_fus100_h227p
    (h227p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n)
    (hfus100 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
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
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) := by
  intro G _ _ F D τ dD h hns m hτ
  subst hτ
  have hncD : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y := by
    by_contra hall
    have hmn := h227p F D _ dD h hns fun x hx hox y hy hoy => by
      by_contra hxy
      exact hall ⟨x, hx, hox, y, hy, hoy, fun hc => hxy (by
        obtain ⟨g, hg⟩ := isConj_iff.mp hc
        exact ⟨g, hg.symm⟩)⟩
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k] at hmn
  have hm := h.t100_two_le hncD
  have hfus := hfus100 F dD h hncD
  exact h.t100_classify_R (h.setting hns) (by omega) hfus fun e he =>
    h.t100_proj_rho_mul_inv_mem (h.setting hns) hm hfus he

theorem stroth_3_2_frame_of_h227p
    (h227p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
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
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) :=
  stroth_3_2_frame_of_fus100_h227p h227p @stroth_3_2_hfus100

theorem stroth_3_10_hcharB_of_plus_h227p
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
            e * e = (dD.c : G) ^ 2 ^ (m - 1)))) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'), F.IsD D' dD' → τ'.m ≠ τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer ((omegaIn 1 D' : Subgroup G) : Set G) := by
  intro G _ _ F D τ dD h hτ hns g hgS hgN
  have hnc : ∃ x : G, x ∈ omegaIn 1 D ∧ orderOf x = 2 ∧
      ∃ y : G, y ∈ omegaIn 1 D ∧ orderOf y = 2 ∧ ∀ g : G, y ≠ g * x * g⁻¹ := by
    by_contra hno
    push Not at hno
    exact hτ (h227p F D τ dD h hns hno)
  have hnc' : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y := by
    obtain ⟨x, hx, hx2, y, hy, hy2, hxy⟩ := hnc
    refine ⟨x, hx, hx2, y, hy, hy2, fun hc => ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    exact hxy c hc.symm
  have h226' := fun B => h226p F D τ dD B h hns
  rcases h228 F D τ dD h hnc with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨s, rfl⟩ | ⟨n, rfl⟩
  ·
    have hm1 : 1 ≤ m := h.one_le_of_t200
    rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl : m = 1 := by omega
      exact h.mem_normalizer_omegaIn_t200_one rfl h226'
        (stroth_3_4 F dD h hm1 hns (stroth_4_7_hfus200 F dD h hnc')) hgN
    · exact h.mem_normalizer_omegaIn_t200 hm h226'
        (stroth_3_4 F dD h hm1 hns (stroth_4_7_hfus200 F dD h hnc')) hgN
  ·
    have hm1 : 1 ≤ m := Stroth44.one_le h
    have hfus := stroth_4_4_hfus201 F dD h hnc'
    have hR0 : ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        Rel34i dD e (2 ^ (m + 1)) → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) =
            D ⊔ Subgroup.zpowers e := by
      intro e heR he
      have hS := h.setting hns
      have hR1 := h.t201_R1_eq_of_rel34i hS hm1 hfus heR he
      have hle : hS.R1 dD.uv dD.t ≤ hS.R := fun f hf => hf.1
      have key : hS.R1 dD.uv dD.t = hS.R := by
        by_contra hne
        exact StrothFrame.IsD.false_of_R1_lt h hS hm1 heR he hR1 (lt_of_le_of_ne hle hne)
      show hS.R = _
      rw [← key, hR1]
    have h34 : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨ Rel34inv dD e 0 1 2 ∨
          Rel34inv dD e (2 ^ (m + 1)) 1 2) := by
      rcases stroth_3_4_t201 F dD h hm1 hns hfus with hRD | ⟨e, heR, he⟩ | ⟨e, heR, hRe, he⟩
      · exact Or.inl hRD
      · exact Or.inr ⟨e, heR, hR0 e heR he, Or.inl he⟩
      · exact Or.inr ⟨e, heR, hRe, Or.inr he⟩
    rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl : m = 1 := by omega
      exact h.mem_normalizer_omegaIn_t201_one rfl h226' h34 hgN
    · exact h.mem_normalizer_omegaIn_t201 hm h226' h34 hgN
  ·
    exact h.mem_normalizer_omegaIn_t100 h226' (h32 F D _ dD h hns m rfl) hgS hgN
  ·
    exact h.mem_normalizer_omegaIn_t101 h226' hgS hgN
  ·
    exact absurd rfl hτ

end CFSG.CGT.Stroth77
