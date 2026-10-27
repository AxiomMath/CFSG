module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenY
public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEL

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

@[expose] def AltChildAt (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin n)) →
      Nonempty (rankTwoX A ≃* alternatingGroup (Fin (n + 4))) ∨
        (n = 5 ∧ NativeSporadic.IsSporadic (rankTwoX A) .J2) ∨
        (n = 5 ∧ NativeSporadic.IsSporadic (rankTwoX A) .M12 ∧ rankTwoX A ≠ ⊤)

@[expose] def AltRootFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R T : Subgroup G) (g : G) (n : ℕ)
    (Φ : alternatingGroup (Fin (n + 4)) →* G), AltGenSetting A R T g n Φ → 9 ≤ n →
    (∀ m, 5 ≤ m → m < n → AltChildAt m) →
    ∀ (π : alternatingGroup (Fin (n + 4))) (x : G), π * π = 1 → π ≠ 1 →
      x * Φ π * x⁻¹ ∈ centralizer (A : Set G) → (π : Perm (Fin (n + 4))).cycleType = {2, 2}

@[expose] def AltTypeTwoFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R T : Subgroup G) (g : G) (n : ℕ)
    (Φ : alternatingGroup (Fin (n + 4)) →* G), AltGenSetting A R T g n Φ → 9 ≤ n →
    (∀ m, 5 ≤ m → m < n → AltChildAt m) →
    ∀ (π σ : alternatingGroup (Fin (n + 4))) (x : G),
      (π : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2} → σ * σ = 1 →
      x * Φ π * x⁻¹ = Φ σ → (σ : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2}

@[expose] def AltTypeTwoCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R T : Subgroup G) (g : G) (n : ℕ)
    (Φ : alternatingGroup (Fin (n + 4)) →* G), AltGenSetting A R T g n Φ → 9 ≤ n →
    (∀ m, 5 ≤ m → m < n → AltChildAt m) →
    ∀ π : alternatingGroup (Fin (n + 4)), (π : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2} →
      centralizer ({Φ π} : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G)

section Local

variable {G : Type} [Group G] {n : ℕ}

@[expose] def RootFusionAt (A : Subgroup G) (Φ : alternatingGroup (Fin (n + 4)) →* G) : Prop :=
  ∀ (π : alternatingGroup (Fin (n + 4))) (x : G), π * π = 1 → π ≠ 1 →
    x * Φ π * x⁻¹ ∈ centralizer (A : Set G) → (π : Perm (Fin (n + 4))).cycleType = {2, 2}

@[expose] def TypeTwoFusionAt (Φ : alternatingGroup (Fin (n + 4)) →* G) : Prop :=
  ∀ (π σ : alternatingGroup (Fin (n + 4))) (x : G),
    (π : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2} → σ * σ = 1 →
    x * Φ π * x⁻¹ = Φ σ → (σ : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2}

@[expose] def TypeTwoCentralizerAt (Φ : alternatingGroup (Fin (n + 4)) →* G) : Prop :=
  ∀ π : alternatingGroup (Fin (n + 4)), (π : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2} →
    centralizer ({Φ π} : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G)

end Local

section Thm33

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem commute_of_sq_eq_one' {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have hab := hE2 _ (mul_mem ha hb)
  have ha2 := hE2 a ha
  have hb2 := hE2 b hb
  rw [sq] at hab ha2 hb2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hai, hbi]

open CFSG.ComponentClassification.AschbacherStrongEmbedding CFSG.ShultStronglyClosedTI in
theorem fusionStronglyEmbedded_of_four
    (hs : IsSimpleGroup X) {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE4 : Nat.card E = 4)
    {H : Subgroup X} {z : X} (hz : orderOf z = 2) (hH : H ≠ ⊤)
    (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (hP : ProductUniqueContainment H z) : fusionStronglyEmbedded H := by
  have := hs
  obtain ⟨h12, h23, -⟩ := theorem_3_3 not_minimalInvolutionPointLocalFailure
    benderDoubleCoverRigidity H z hz hH huniq
  have h3 := h23 (h12 hP)
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz; omega
  have hhull : involutionPointHull z = ⊤ := by
    rcases (minimalLocalFailure_hull_normal z).eq_bot_or_eq_top with h | h
    · exfalso
      apply hz1
      have h1 : z ∈ involutionPointHull z :=
        subset_closure ⟨1, by simp [BenderSuzuki.PFAppendixIII.rightConjugateElem]⟩
      rw [h, mem_bot] at h1
      exact h1
    · exact h
  have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rcases (commutator_normal (⊤ : Subgroup X) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      have hcen : ∀ g : X, g * z = z * g := fun g => by
        have h1 : g * z * g⁻¹ * z⁻¹ ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
          commutator_mem_commutator (mem_top g) (mem_top z)
        rw [h, mem_bot, mul_inv_eq_one] at h1
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [h1]
      have hn : (zpowers z).Normal :=
        normal_of_le_center (zpowers_le.mpr (mem_center_iff.mpr hcen))
      rcases hn.eq_bot_or_eq_top with h' | h'
      · have h1 := mem_zpowers z
        rw [h', mem_bot] at h1
        exact hz1 h1
      · have h1 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
        rw [h', card_top] at h1
        have h2 := E.card_le_card_group
        omega
    · exact h
  rcases h3 with hr | ⟨u, -, -, -, -, hse, -⟩
  · exfalso
    set K := involutionPointHull z with hK
    have hEK : E ≤ K := hhull ▸ le_top
    have hel : IsElemAbelian 2 (E.subgroupOf K) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
      · exact commute_of_sq_eq_one' hE2 a.2 b.2
      · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE2 _ ha
    have hcard : Nat.card (E.subgroupOf K) = 2 ^ 2 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hEK).symm.toEquiv, hE4]
      norm_num
    have h4 := SectionRank.le_pRank one_lt_two (le_top : E.subgroupOf K ≤ ⊤) hel hcard
    have h5 : twoRank ↥K ≤ 1 := hr
    unfold twoRank at h5
    omega
  · rw [hhull, hcomm] at hse
    have hmap := hse.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
    have himage : (H.subgroupOf (⊤ : Subgroup X)).map
        (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom = H := by
      change (H.subgroupOf (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype = H
      rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
    rwa [himage] at hmap

end Thm33

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G}

namespace AltGenCore

variable (s : AltGenCore A R T g n Φ)
include s

theorem conj_rootLast_mem_iff_of
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) (x : G) :
    x * Φ (rootLast n) * x⁻¹ ∈ Φ.range ⊔ centralizer (Φ.range : Set G) ↔
      x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  have hzY : Φ (rootLast n) ∈ Φ.range ⊔ centralizer (Φ.range : Set G) :=
    mem_sup_left ⟨rootLast n, rfl⟩
  constructor
  · intro hw
    have hw2 : x * Φ (rootLast n) * x⁻¹ * (x * Φ (rootLast n) * x⁻¹) = 1 := by
      calc x * Φ (rootLast n) * x⁻¹ * (x * Φ (rootLast n) * x⁻¹) =
          x * (Φ (rootLast n) * Φ (rootLast n)) * x⁻¹ := by group
        _ = 1 := by rw [map_rootLast_mul_self, mul_one, mul_inv_cancel]
    obtain ⟨σ, hσ⟩ := s.mem_of_mem_sup_of_mul_self hw hw2
    have hσ2 : σ * σ = 1 := s.injective (by rw [map_mul, hσ, hw2, map_one])
    have hσ1 : σ ≠ 1 := by
      intro h1
      rw [h1, map_one] at hσ
      apply s.map_rootLast_ne_one
      calc Φ (rootLast n) = x⁻¹ * (x * Φ (rootLast n) * x⁻¹) * x := by group
        _ = 1 := by rw [← hσ, mul_one, inv_mul_cancel]
    have hroot := hF σ x⁻¹ hσ2 hσ1 (by
      rw [hσ, inv_inv]
      have : x⁻¹ * (x * Φ (rootLast n) * x⁻¹) * x = Φ (rootLast n) := by group
      rw [this]
      exact s.rootLast_mem_centralizer)
    obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq (σ := rootLast n) (τ := σ)
      (by rw [cycleType_rootLast, hroot]) rootLast_mul_rootLast rootLast_ne_one
    have hc : (Φ β)⁻¹ * x ∈ centralizer ({Φ (rootLast n)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      symm
      have h1 : Φ β * Φ (rootLast n) * (Φ β)⁻¹ = x * Φ (rootLast n) * x⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, hβ, hσ]
      calc Φ (rootLast n) * ((Φ β)⁻¹ * x) =
          (Φ β)⁻¹ * (Φ β * Φ (rootLast n) * (Φ β)⁻¹) * x := by group
        _ = (Φ β)⁻¹ * (x * Φ (rootLast n) * x⁻¹) * x := by rw [h1]
        _ = (Φ β)⁻¹ * x * Φ (rootLast n) := by group
    have h2 := mul_mem (mem_sup_left ⟨β, rfl⟩ : Φ β ∈ Φ.range ⊔ centralizer (Φ.range : Set G))
      (s.centralizer_rootLast_le_of hN hc)
    rwa [mul_inv_cancel_left] at h2
  · intro hx
    exact mul_mem (mul_mem hx hzY) (inv_mem hx)

theorem conj_typeTwo_mem_iff_of (hF2 : TypeTwoFusionAt Φ) (hF3 : TypeTwoCentralizerAt Φ)
    {π : alternatingGroup (Fin (n + 4))}
    (hπ : (π : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2}) (x : G) :
    x * Φ π * x⁻¹ ∈ Φ.range ⊔ centralizer (Φ.range : Set G) ↔
      x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  obtain ⟨hπ2, hπ1⟩ := mul_self_of_cycleType_two_four hπ
  have heY : Φ π ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := mem_sup_left ⟨π, rfl⟩
  constructor
  · intro hw
    have hw2 : x * Φ π * x⁻¹ * (x * Φ π * x⁻¹) = 1 := by
      calc x * Φ π * x⁻¹ * (x * Φ π * x⁻¹) = x * Φ (π * π) * x⁻¹ := by rw [map_mul]; group
        _ = 1 := by rw [hπ2, map_one, mul_one, mul_inv_cancel]
    obtain ⟨σ, hσ⟩ := s.mem_of_mem_sup_of_mul_self hw hw2
    have hσ2 : σ * σ = 1 := s.injective (by rw [map_mul, hσ, hw2, map_one])
    have hσt := hF2 π σ x hπ hσ2 hσ.symm
    obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq (σ := π) (τ := σ) (by rw [hπ, hσt]) hπ2 hπ1
    have hc : (Φ β)⁻¹ * x ∈ centralizer ({Φ π} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      symm
      have h1 : Φ β * Φ π * (Φ β)⁻¹ = x * Φ π * x⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, hβ, hσ]
      calc Φ π * ((Φ β)⁻¹ * x) = (Φ β)⁻¹ * (Φ β * Φ π * (Φ β)⁻¹) * x := by group
        _ = (Φ β)⁻¹ * (x * Φ π * x⁻¹) * x := by rw [h1]
        _ = (Φ β)⁻¹ * x * Φ π := by group
    have h2 := mul_mem (mem_sup_left ⟨β, rfl⟩ : Φ β ∈ Φ.range ⊔ centralizer (Φ.range : Set G))
      (hF3 π hπ hc)
    rwa [mul_inv_cancel_left] at h2
  · intro hx
    exact mul_mem (mul_mem hx heY) (inv_mem hx)

theorem rankTwoX_eq_of
    (h34 : Asc08Lemma34)
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) (hF2 : TypeTwoFusionAt Φ) (hF3 : TypeTwoCentralizerAt Φ) :
    rankTwoX A = A ⊔ rightConjugate A g := by
  have h5 := s.five_le
  set Yp : Subgroup G := Φ.range ⊔ centralizer (Φ.range : Set G) with hYp
  have hYX : Φ.range ≤ rankTwoX A := by
    rw [s.range_eq]
    refine sup_le le_normalClosure fun b hb => ?_
    rw [mem_rightConjugate_iff] at hb
    have h1 := (normalClosure_normal (s := (A : Set G))).conj_mem _ (le_normalClosure hb) g⁻¹
    have h2 : b = g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ := by group
    rw [h2]
    exact h1
  rw [← s.range_eq]
  refine le_antisymm ?_ hYX
  by_contra hXY
  obtain ⟨hXF, hXs⟩ := h34 G A s.sec3.hyp
  have hXsimple : IsSimpleGroup ↥(rankTwoX A) := by
    show IsSimpleGroup ↥(normalClosure (A : Set G))
    rw [hXF]
    exact hXs
  set X := rankTwoX A with hXdef
  set H : Subgroup ↥X := Yp.subgroupOf X with hH
  have hzX : Φ (rootLast n) ∈ X := hYX ⟨rootLast n, rfl⟩
  set z : ↥X := ⟨Φ (rootLast n), hzX⟩ with hzdef
  have hz : orderOf z = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => s.map_rootLast_ne_one ?_
    · rw [SubgroupClass.coe_pow, sq, map_rootLast_mul_self]
      rfl
    · exact congrArg Subtype.val h1
  have hYpN : Yp ≤ normalizer (Φ.range : Set G) :=
    sup_le le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hN : (Φ.range.subgroupOf X).Normal := ⟨fun y hy x => by
      have hxYp : (x : G) ∈ Yp := by
        have := htop ▸ mem_top x
        exact mem_subgroupOf.mp this
      rw [mem_subgroupOf] at hy ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mem_normalizer_iff.mp (hYpN hxYp) _).mp hy⟩
    rcases hN.eq_bot_or_eq_top with h | h
    · apply s.map_rootLast_ne_one
      have h1 : z ∈ Φ.range.subgroupOf X := mem_subgroupOf.mpr ⟨rootLast n, rfl⟩
      rw [h, mem_bot] at h1
      exact congrArg Subtype.val h1
    · apply hXY
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥X) ∈ Φ.range.subgroupOf X := h ▸ mem_top _
      exact mem_subgroupOf.mp h1
  have huniq : ∀ h : ↥X, z ∈ rightConjugate H h ↔ h ∈ H := by
    intro h
    rw [mem_rightConjugate_iff, mem_subgroupOf, mem_subgroupOf]
    exact s.conj_rootLast_mem_iff_of hN hF h
  have hP : AschbacherStrongEmbedding.ProductUniqueContainment H z := by
    rintro t ⟨k, rfl⟩ hzt hne h
    simp only [BenderSuzuki.PFAppendixIII.rightConjugateElem] at hzt hne ⊢
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    set t' : G := (k : G)⁻¹ * Φ (rootLast n) * k with ht'
    have hzt' : Φ (rootLast n) * t' = t' * Φ (rootLast n) := congrArg Subtype.val hzt.eq
    have hne' : t' ≠ Φ (rootLast n) := fun h' => hne (Subtype.ext h')
    have htC : t' ∈ centralizer ({Φ (rootLast n)} : Set G) :=
      mem_centralizer_singleton_iff.mpr hzt'.symm
    have ht2 : t' * t' = 1 := by
      rw [ht']
      calc (k : G)⁻¹ * Φ (rootLast n) * k * ((k : G)⁻¹ * Φ (rootLast n) * k) =
          (k : G)⁻¹ * (Φ (rootLast n) * Φ (rootLast n)) * k := by group
        _ = 1 := by rw [map_rootLast_mul_self, mul_one, inv_mul_cancel]
    obtain ⟨σ, hσ⟩ := s.mem_of_mem_sup_of_mul_self (s.centralizer_rootLast_le_of hN htC) ht2
    have hσ2 : σ * σ = 1 := s.injective (by rw [map_mul, hσ, ht2, map_one])
    have hσ1 : σ ≠ 1 := by
      intro h1
      rw [h1, map_one, ht'] at hσ
      apply s.map_rootLast_ne_one
      calc Φ (rootLast n) = (k : G) * ((k : G)⁻¹ * Φ (rootLast n) * k) * (k : G)⁻¹ := by group
        _ = 1 := by rw [← hσ, mul_one, mul_inv_cancel]
    have hroot := hF σ k hσ2 hσ1 (by
      rw [hσ, ht']
      have : (k : G) * ((k : G)⁻¹ * Φ (rootLast n) * k) * (k : G)⁻¹ = Φ (rootLast n) := by group
      rw [this]
      exact s.rootLast_mem_centralizer)
    have hcomm : rootLast n * σ = σ * rootLast n :=
      s.injective (by rw [map_mul, map_mul, hσ, hzt'])
    have hneσ : rootLast n ≠ σ := fun h' => hne' (by rw [← hσ, ← h'])
    have hzt'' : Φ (rootLast n) * t' = Φ (rootLast n * σ) := by rw [map_mul, hσ]
    rw [hzt'']
    rcases cycleType_mul_of_commute cycleType_rootLast hroot
        (congrArg Subtype.val hcomm) (fun h' => hneσ (Subtype.ext h')) with h22 | h2222
    ·
      obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq (σ := rootLast n) (τ := rootLast n * σ)
        (by rw [cycleType_rootLast, Subgroup.coe_mul, h22]) rootLast_mul_rootLast
        rootLast_ne_one
      rw [← hβ, map_mul, map_mul, map_inv]
      have h1 := s.conj_rootLast_mem_iff_of hN hF ((h : G)⁻¹ * Φ β)
      have hβY : Φ β ∈ Yp := mem_sup_left ⟨β, rfl⟩
      have h2 : (h : G)⁻¹ * (Φ β * Φ (rootLast n) * (Φ β)⁻¹) * h =
          (h : G)⁻¹ * Φ β * Φ (rootLast n) * ((h : G)⁻¹ * Φ β)⁻¹ := by group
      rw [h2, h1]
      constructor
      · intro h3
        have h4 := mul_mem h3 (inv_mem hβY)
        rw [mul_inv_cancel_right] at h4
        exact inv_mem_iff.mp h4
      · intro h3
        exact mul_mem (inv_mem h3) hβY
    ·
      have h1 := s.conj_typeTwo_mem_iff_of hF2 hF3 (by rw [Subgroup.coe_mul]; exact h2222)
        (h : G)⁻¹
      rw [inv_inv] at h1
      rw [h1]
      exact inv_mem_iff
  set E : Subgroup ↥X := ((rootV (n + 4)).map Φ).subgroupOf X with hE
  have hEX : (rootV (n + 4)).map Φ ≤ X := (map_le_range Φ _).trans hYX
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    rw [mem_subgroupOf] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    obtain ⟨k, hk, hkv⟩ := (mem_rootV_iff (by omega) v).mp hv
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hvx, ← map_pow, sq]
    have hvv : v * v = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← hkv, ← map_mul, mul_self_of_mem_kleinFour hk, map_one]
      rfl)
    rw [hvv, map_one]
    rfl
  have hE4 : Nat.card E = 4 := by
    rw [hE, ← Nat.card_congr (subgroupOfEquivOfLe hEX).symm.toEquiv,
      Subgroup.card_map_of_injective s.injective, nat_card_rootV (by omega)]
  have hse := fusionStronglyEmbedded_of_four hXsimple hE2 hE4 hz hHtop huniq hP
  obtain ⟨hπ2, hπ1⟩ := mul_self_of_cycleType_two_four (cycleType_rootFirst_mul_rootLast
    (by omega : 4 ≤ n))
  have heX : Φ (rootFirst n * rootLast n) ∈ X := hYX ⟨_, rfl⟩
  have he : orderOf (⟨Φ (rootFirst n * rootLast n), heX⟩ : ↥X) = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => hπ1 (s.injective ?_)
    · rw [SubgroupClass.coe_pow, sq]
      show Φ (rootFirst n * rootLast n) * Φ (rootFirst n * rootLast n) = 1
      rw [← map_mul, hπ2, map_one]
    · rw [map_one]
      exact congrArg Subtype.val h1
  obtain ⟨c, hc⟩ := isConj_iff.mp (Timmesfeld.Bridge.isConj_of_orderOf_eq_two hse hz he)
  have hc' : (c : G) * Φ (rootLast n) * (c : G)⁻¹ = Φ (rootFirst n * rootLast n) :=
    congrArg Subtype.val hc
  have hroot := hF (rootFirst n * rootLast n) (c : G)⁻¹ hπ2 hπ1 (by
    rw [inv_inv, ← hc']
    have : (c : G)⁻¹ * ((c : G) * Φ (rootLast n) * (c : G)⁻¹) * c = Φ (rootLast n) := by group
    rw [this]
    exact s.rootLast_mem_centralizer)
  rw [cycleType_rootFirst_mul_rootLast (by omega)] at hroot
  have h1 := congrArg Multiset.card hroot
  simp at h1

end AltGenCore

namespace AltGenSetting

variable (s : AltGenSetting A R T g n Φ)
include s

theorem rootFusionAt (hF : AltRootFusion) (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) : RootFusionAt A Φ :=
  fun π x => hF G A R T g n Φ s hn IH π x

theorem typeTwoFusionAt (hF2 : AltTypeTwoFusion) (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) : TypeTwoFusionAt Φ :=
  fun π σ x => hF2 G A R T g n Φ s hn IH π σ x

theorem typeTwoCentralizerAt (hF3 : AltTypeTwoCentralizer) (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) : TypeTwoCentralizerAt Φ :=
  fun π => hF3 G A R T g n Φ s hn IH π

theorem conj_rootLast_mem_iff (hF : AltRootFusion) (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) (x : G) :
    x * Φ (rootLast n) * x⁻¹ ∈ Φ.range ⊔ centralizer (Φ.range : Set G) ↔
      x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) :=
  s.conj_rootLast_mem_iff_of (s.normalizer_le (by omega)) (s.rootFusionAt hF hn IH) x

theorem rankTwoX_eq
    (h34 : Asc08Lemma34) (hF : AltRootFusion) (hF2 : AltTypeTwoFusion)
    (hF3 : AltTypeTwoCentralizer) (hn : 9 ≤ n) (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) :
    rankTwoX A = A ⊔ rightConjugate A g :=
  s.rankTwoX_eq_of h34 (s.normalizer_le (by omega)) (s.rootFusionAt hF hn IH)
    (s.typeTwoFusionAt hF2 hn IH) (s.typeTwoCentralizerAt hF3 hn IH)

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
