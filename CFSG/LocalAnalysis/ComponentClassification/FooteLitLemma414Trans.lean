module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Omega

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem omega_eq_of_le {D T₁ A A₂ : Subgroup G} (hT₁ : IsSylowOf 2 T₁ D)
    (hA : IsOmegaOneOf A T₁) (hAA₂ : A ≤ A₂) (hA₂D : A₂ ≤ D) (hA₂ : ∀ x ∈ A₂, x ^ 2 = 1) :
    A₂ = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 A₂ := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hA₂ x x.2)⟩
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hT₁ hA₂D hp
  have hle : conjugate A₂ c ≤ A := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := hc _ hx
    rw [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at h1
    refine hA.2.2 x h1 ?_
    have h2 := hA₂ _ hx
    rwa [conj_pow, mul_inv_eq_one, mul_eq_left] at h2
  have hcard : Nat.card A₂ ≤ Nat.card A := by
    rw [← card_conjugate_eq_card A₂ c]
    exact card_le_of_le hle
  exact (eq_of_le_of_card_ge hAA₂ hcard).symm

@[expose] def FooteAConj (M A : Subgroup G) (a b : G) : Prop :=
  ∃ n ∈ normalizer (M : Set G), n ∈ normalizer (A : Set G) ∧ n * a * n⁻¹ = b

omit [Finite G] in
theorem FooteAConj.refl (M A : Subgroup G) (a : G) : FooteAConj M A a a :=
  ⟨1, one_mem _, one_mem _, by group⟩

omit [Finite G] in
theorem FooteAConj.symm {M A : Subgroup G} {a b : G} (h : FooteAConj M A a b) :
    FooteAConj M A b a := by
  obtain ⟨n, hnM, hnA, rfl⟩ := h
  exact ⟨n⁻¹, inv_mem hnM, inv_mem hnA, by group⟩

omit [Finite G] in
theorem FooteAConj.trans {M A : Subgroup G} {a b c : G} (h₁ : FooteAConj M A a b)
    (h₂ : FooteAConj M A b c) : FooteAConj M A a c := by
  obtain ⟨n, hnM, hnA, rfl⟩ := h₁
  obtain ⟨m, hmM, hmA, rfl⟩ := h₂
  exact ⟨m * n, mul_mem hmM hnM, mul_mem hmA hnA, by group⟩

omit [Finite G] in
theorem mul_ne_one_of_ne {x y : G} (hxy : x ≠ y) (hy2 : y ^ 2 = 1) : x * y ≠ 1 := by
  intro h1
  apply hxy
  calc x = x * y * y := by rw [mul_assoc, ← sq, hy2, mul_one]
    _ = y := by rw [h1, one_mul]

theorem exists_mem_ne_ne {F : Subgroup G} (hF : 4 ≤ Nat.card F) (a b : G) :
    ∃ x ∈ F, x ≠ 1 ∧ x ≠ a ∧ x ≠ b := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (F : Set G) ⊆ {1, a, b} := fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = a
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (hcon x hx h1 h2))
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 : ({1, a, b} : Set G).ncard ≤ 3 := by
    calc ({1, a, b} : Set G).ncard ≤ ({a, b} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ ({b} : Set G).ncard + 1 + 1 := by
          have := Set.ncard_insert_le a ({b} : Set G)
          omega
      _ = 3 := by rw [Set.ncard_singleton]
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h3
  omega

theorem exists_omega_transitive
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {t₁ t₂ : G}
    (ht₁ : FooteInCC M t₁) (ht₂ : FooteInCC M t₂) (ht₂K : t₂ ∈ footeK L t₁) (hne : t₂ ≠ t₁) :
    ∃ T A : Subgroup G, IsSylowOf 2 T (coreActionKernel M ⊓ centralizer ({t₁} : Set G)) ∧
      IsOmegaOneOf A T ∧ t₁ ∈ A ∧ t₂ ∈ A ∧ 8 ≤ Nat.card A ∧
      ∀ a ∈ A, a ≠ 1 → FooteAConj M A t₁ a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hC
  set K₁ := footeK L t₁ with hK₁
  set K₂ := footeK L t₂ with hK₂
  have ht₁' := ht₁
  obtain ⟨ht₁2, ht₁C, hCt₁⟩ := ht₁'
  have ht₂' := ht₂
  obtain ⟨ht₂2, ht₂C, -⟩ := ht₂'
  obtain ⟨-, -, hB₁t, -⟩ := foote_lemma_4_9_core h h47 hST hM ht₁2 ht₁C hCt₁
  obtain ⟨hK₁B, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht₁2 ht₁C hCt₁
  have hK₁t : K₁ ≤ centralizer ({t₁} : Set G) := hK₁B.trans hB₁t
  have ht₂2' : t₂ ^ 2 = 1 := by rw [← ht₂2]; exact pow_orderOf_eq_one t₂
  have ht₁2' : t₁ ^ 2 = 1 := by rw [← ht₁2]; exact pow_orderOf_eq_one t₁
  have ht₁1 : t₁ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht₁2; omega
  have ht₂1 : t₂ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht₂2; omega
  have ht₂D : t₂ ∈ C ⊓ centralizer ({t₁} : Set G) := mem_inf.mpr ⟨ht₂C, hK₁t ht₂K⟩
  obtain ⟨T₁, hT₁, hT₁t₂⟩ := exists_isSylowOf_ge_of_le (zpowers_le.mpr ht₂D)
    (isPGroup_two_zpowers_of_sq_eq_one ht₂2')
  obtain ⟨A, hA, ht₁A, hA8, hB₁, hS₁, htr₁⟩ :=
    exists_omega_of_footeInCC h h47 hST hAsc h2An hM ht₁ hT₁
  have ht₂A : t₂ ∈ A := hA.2.2 t₂ (hT₁t₂ (mem_zpowers t₂)) ht₂2'
  have hAD₂ : A ≤ C ⊓ centralizer ({t₂} : Set G) := fun a ha =>
    mem_inf.mpr ⟨(hA.1.trans (hT₁.le.trans inf_le_left)) ha,
      mem_centralizer_singleton_iff.mpr (commute_of_sq_eq_one hA.2.1 ha ht₂A)⟩
  have hAp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hA.2.1 x x.2)⟩
  obtain ⟨T₂, hT₂, hAT₂⟩ := exists_isSylowOf_ge_of_le hAD₂ hAp
  obtain ⟨A₂, hA₂, -, -, hB₂, hS₂, htr₂⟩ :=
    exists_omega_of_footeInCC h h47 hST hAsc h2An hM ht₂ hT₂
  have hA₂eq : A₂ = A := by
    refine omega_eq_of_le hT₁ hA (fun a ha => hA₂.2.2 a (hAT₂ ha) (hA.2.1 a ha)) ?_ hA₂.2.1
    intro x hx
    refine mem_inf.mpr ⟨(hA₂.1.trans (hT₂.le.trans inf_le_left)) hx,
      mem_centralizer_singleton_iff.mpr ?_⟩
    exact commute_of_sq_eq_one hA₂.2.1 hx (hA₂.2.2 t₁ (hAT₂ ht₁A) ht₁2')
  subst hA₂eq
  refine ⟨T₁, A₂, hT₁, hA, ht₁A, ht₂A, hA8, ?_⟩
  have R₁ : ∀ x ∈ A₂, ∀ y ∈ A₂, x ≠ 1 → y ≠ 1 → x ≠ t₁ → y ≠ t₁ → (x ∈ K₁ ↔ y ∈ K₁) →
      FooteAConj M A₂ x y := fun x hx y hy h1 h2 h3 h4 h5 => by
    obtain ⟨m, hmN, hmA, -, hm⟩ := htr₁ x hx y hy h1 h2 h3 h4 h5
    exact ⟨m, hmN, hmA, hm⟩
  have R₂ : ∀ x ∈ A₂, ∀ y ∈ A₂, x ≠ 1 → y ≠ 1 → x ≠ t₂ → y ≠ t₂ → (x ∈ K₂ ↔ y ∈ K₂) →
      FooteAConj M A₂ x y := fun x hx y hy h1 h2 h3 h4 h5 => by
    obtain ⟨m, hmN, hmA, -, hm⟩ := htr₂ x hx y hy h1 h2 h3 h4 h5
    exact ⟨m, hmN, hmA, hm⟩
  have hA4 : 4 ≤ Nat.card A₂ := by omega
  intro a ha ha1
  by_cases hat : a = t₁
  · rw [hat]
    exact FooteAConj.refl M A₂ t₁
  by_cases ht₁K : t₁ ∈ K₁
  ·
    have hAK₁ := hS₁ ht₁K
    obtain ⟨b, hbA, hb1, hbt₁, hbt₂, hb⟩ : ∃ b ∈ A₂, b ≠ 1 ∧ b ≠ t₁ ∧ b ≠ t₂ ∧
        FooteAConj M A₂ t₁ b := by
      by_cases ht₂K₂ : t₂ ∈ K₂
      · have hAK₂ := hS₂ ht₂K₂
        obtain ⟨b, hbA, hb1, hbt₁, hbt₂⟩ := exists_mem_ne_ne hA4 t₁ t₂
        exact ⟨b, hbA, hb1, hbt₁, hbt₂, R₂ t₁ ht₁A b hbA ht₁1 hb1 hne.symm hbt₂
          ⟨fun _ => hAK₂ hbA, fun _ => hAK₂ ht₁A⟩⟩
      · obtain ⟨hdec, h4⟩ := hB₂ ht₂K₂
        by_cases ht₁K₂ : t₁ ∈ K₂
        · obtain ⟨b, hb, hb1, hbt₁, hbt₂⟩ := exists_mem_ne_ne h4 t₁ t₂
          exact ⟨b, (mem_inf.mp hb).1, hb1, hbt₁, hbt₂, R₂ t₁ ht₁A b (mem_inf.mp hb).1 ht₁1 hb1
            hne.symm hbt₂ ⟨fun _ => (mem_inf.mp hb).2, fun _ => ht₁K₂⟩⟩
        · obtain ⟨f, hf, hf1, hft, -⟩ := exists_mem_ne_ne h4 (t₁ * t₂) 1
          have hfA := (mem_inf.mp hf).1
          have hfK := (mem_inf.mp hf).2
          have hbK : f * t₂ ∉ K₂ := fun h1 => ht₂K₂ (by
            have h2 := mul_mem (inv_mem hfK) h1
            rwa [inv_mul_cancel_left] at h2)
          have hb1 : f * t₂ ≠ 1 := fun h1 => hbK (h1 ▸ one_mem K₂)
          have hbt₂ : f * t₂ ≠ t₂ := fun h1 => hf1 (by
            calc f = f * t₂ * t₂⁻¹ := by group
              _ = 1 := by rw [h1, mul_inv_cancel])
          have hbt₁ : f * t₂ ≠ t₁ := fun h1 => hft (by
            calc f = f * t₂ * t₂ := by rw [mul_assoc, ← sq, ht₂2', mul_one]
              _ = t₁ * t₂ := by rw [h1])
          exact ⟨f * t₂, mul_mem hfA ht₂A, hb1, hbt₁, hbt₂, R₂ t₁ ht₁A _ (mul_mem hfA ht₂A)
            ht₁1 hb1 hne.symm hbt₂ ⟨fun h1 => absurd h1 ht₁K₂, fun h1 => absurd h1 hbK⟩⟩
    exact hb.trans (R₁ b hbA a ha hb1 ha1 hbt₁ hat ⟨fun _ => hAK₁ ha, fun _ => hAK₁ hbA⟩)
  ·
    obtain ⟨hdec₁, h4₁⟩ := hB₁ ht₁K
    obtain ⟨f, hf, hf1, hft₂, -⟩ := exists_mem_ne_ne h4₁ t₂ 1
    have hfA := (mem_inf.mp hf).1
    have hfK₁ := (mem_inf.mp hf).2
    have hft₁ : f ≠ t₁ := fun h1 => ht₁K (h1 ▸ hfK₁)
    have ht₂t₁ : t₂ ≠ t₁ := hne
    by_cases ht₂K₂ : t₂ ∈ K₂
    ·
      have hAK₂ := hS₂ ht₂K₂
      have h1 : FooteAConj M A₂ t₁ f :=
        R₂ t₁ ht₁A f hfA ht₁1 hf1 hne.symm hft₂ ⟨fun _ => hAK₂ hfA, fun _ => hAK₂ ht₁A⟩
      by_cases hat₂ : a = t₂
      · rw [hat₂]
        exact h1.trans (R₁ f hfA t₂ ht₂A hf1 ht₂1 hft₁ ht₂t₁ ⟨fun _ => ht₂K, fun _ => hfK₁⟩)
      · exact R₂ t₁ ht₁A a ha ht₁1 ha1 hne.symm hat₂ ⟨fun _ => hAK₂ ha, fun _ => hAK₂ ht₁A⟩
    ·
      obtain ⟨hdec₂, -⟩ := hB₂ ht₂K₂
      obtain ⟨x, hxA, hx1, hxK₁, hxK₂⟩ : ∃ x ∈ A₂, x ≠ 1 ∧ x ∈ K₁ ∧ x ∈ K₂ := by
        rcases hdec₂ f hfA with hfK₂ | hftK₂
        · exact ⟨f, hfA, hf1, hfK₁, hfK₂⟩
        · exact ⟨f * t₂, mul_mem hfA ht₂A, mul_ne_one_of_ne hft₂ ht₂2', mul_mem hfK₁ ht₂K,
            hftK₂⟩
      have hxt₁ : x ≠ t₁ := fun h1 => ht₁K (h1 ▸ hxK₁)
      have hxt₂ : x ≠ t₂ := fun h1 => ht₂K₂ (h1 ▸ hxK₂)
      set y := x * t₂ with hy
      have hyA : y ∈ A₂ := mul_mem hxA ht₂A
      have hyK₁ : y ∈ K₁ := mul_mem hxK₁ ht₂K
      have hyK₂ : y ∉ K₂ := fun h1 => ht₂K₂ (by
        have h2 := mul_mem (inv_mem hxK₂) h1
        rwa [hy, inv_mul_cancel_left] at h2)
      have hy1 : y ≠ 1 := mul_ne_one_of_ne hxt₂ ht₂2'
      have hyt₂ : y ≠ t₂ := fun h1 => hx1 (by
        calc x = x * t₂ * t₂⁻¹ := by group
          _ = 1 := by rw [← hy, h1, mul_inv_cancel])
      have hyt₁ : y ≠ t₁ := fun h1 => ht₁K (h1 ▸ hyK₁)
      have hx : FooteAConj M A₂ t₂ x :=
        R₁ t₂ ht₂A x hxA ht₂1 hx1 ht₂t₁ hxt₁ ⟨fun _ => hxK₁, fun _ => ht₂K⟩
      have hy' : FooteAConj M A₂ t₂ y :=
        R₁ t₂ ht₂A y hyA ht₂1 hy1 ht₂t₁ hyt₁ ⟨fun _ => hyK₁, fun _ => ht₂K⟩
      have hall : ∀ b ∈ A₂, b ≠ 1 → FooteAConj M A₂ t₂ b := by
        intro b hb hb1
        by_cases hbt₂ : b = t₂
        · rw [hbt₂]
          exact FooteAConj.refl M A₂ t₂
        by_cases hbK₂ : b ∈ K₂
        · exact hx.trans (R₂ x hxA b hb hx1 hb1 hxt₂ hbt₂ ⟨fun _ => hbK₂, fun _ => hxK₂⟩)
        · exact hy'.trans (R₂ y hyA b hb hy1 hb1 hyt₂ hbt₂
            ⟨fun h1 => absurd h1 hyK₂, fun h1 => absurd h1 hbK₂⟩)
      exact (hall t₁ ht₁A ht₁1).symm.trans (hall a ha ha1)

end CFSG.ComponentClassification.FooteLit
