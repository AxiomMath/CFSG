module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Defs
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.Asc76
open scoped commutatorElement Pointwise

section Basic

variable {G : Type} [Group G] {Γ : Set G}

theorem mem_fusionGen_of_conj_mem {x g : G} (hx : x ∈ Γ) (hg : g⁻¹ * x * g ∈ Γ) :
    g ∈ fusionGen Γ :=
  subset_closure ⟨x, hx, hg⟩

theorem mem_fusionGen_of_conj_mem_sylow {S : Subgroup G} (hcl : fusionStronglyClosed Γ S)
    {x g : G} (hx : x ∈ Γ) (hg : g⁻¹ * x * g ∈ S) : g ∈ fusionGen Γ :=
  mem_fusionGen_of_conj_mem hx (hcl x hx g hg)

theorem centralizer_le_fusionGen {x : G} (hx : x ∈ Γ) :
    centralizer ({x} : Set G) ≤ fusionGen Γ := by
  intro c hc
  apply mem_fusionGen_of_conj_mem hx
  rw [mem_centralizer_singleton_iff] at hc
  rwa [mul_assoc, ← hc, inv_mul_cancel_left]

theorem mem_fusionGen_of_mem {x : G} (hx : x ∈ Γ) : x ∈ fusionGen Γ :=
  centralizer_le_fusionGen hx (mem_centralizer_singleton_iff.mpr rfl)

theorem le_fusionGen {S : Subgroup G} (hcl : fusionStronglyClosed Γ S) (hΓS : Γ ⊆ S)
    (hne : Γ.Nonempty) : S ≤ fusionGen Γ := by
  obtain ⟨x, hx⟩ := hne
  intro s hs
  exact mem_fusionGen_of_conj_mem_sylow hcl hx
    (S.mul_mem (S.mul_mem (S.inv_mem hs) (hΓS hx)) hs)

theorem exists_conj_mem_of_le [Finite G] {S K : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hSK : S ≤ K)
    {y : G} (hyK : y ∈ K) (hy : IsPGroup 2 (zpowers y)) : ∃ c ∈ K, c⁻¹ * y * c ∈ S := by
  obtain ⟨c, hcK, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
    (hS.of_le hSK le_top) hy (zpowers_le.mpr hyK)
  refine ⟨c, hcK, hle ?_⟩
  rw [mem_rightConjugate_iff]
  have : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
  rw [this]
  exact mem_zpowers y

theorem isPGroup_zpowers_conj {S : Subgroup G} (hS : IsPGroup 2 S) {x : G} (hx : x ∈ S) (g : G) :
    IsPGroup 2 (zpowers (g * x * g⁻¹)) := by
  have h : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [← h]
  exact (hS.to_le (zpowers_le.mpr hx)).map _

theorem mem_rightConjugate_fusionGen_iff [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hcl : fusionStronglyClosed Γ S) (hΓS : Γ ⊆ S) {x : G} (hx : x ∈ Γ) (g : G) :
    x ∈ rightConjugate (fusionGen Γ) g ↔ g ∈ fusionGen Γ := by
  rw [mem_rightConjugate_iff]
  constructor
  · intro hgx
    obtain ⟨c, hcH, hc⟩ := exists_conj_mem_of_le hS (le_fusionGen hcl hΓS ⟨x, hx⟩) hgx
      (isPGroup_zpowers_conj hS.isPGroup (hΓS hx) g)
    have h1 : (g⁻¹ * c)⁻¹ * x * (g⁻¹ * c) ∈ S := by
      have : (g⁻¹ * c)⁻¹ * x * (g⁻¹ * c) = c⁻¹ * (g * x * g⁻¹) * c := by group
      rwa [this]
    have h2 : g⁻¹ * c ∈ fusionGen Γ := mem_fusionGen_of_conj_mem_sylow hcl hx h1
    have h3 : g⁻¹ ∈ fusionGen Γ := by
      have := (fusionGen Γ).mul_mem h2 ((fusionGen Γ).inv_mem hcH)
      rwa [mul_inv_cancel_right] at this
    exact (fusionGen Γ).inv_mem_iff.mp h3
  · intro hg
    exact (fusionGen Γ).mul_mem ((fusionGen Γ).mul_mem hg (mem_fusionGen_of_mem hx))
      ((fusionGen Γ).inv_mem hg)

theorem fusionGen_eq_top_of_normal [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hcl : fusionStronglyClosed Γ S) (hΓS : Γ ⊆ S) {Y : Subgroup G} (hY : Y.Normal)
    (hYH : Y ≤ fusionGen Γ) {x : G} (hx : x ∈ Γ) (hxY : x ∈ Y) : fusionGen Γ = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [← mem_rightConjugate_fusionGen_iff hS hcl hΓS hx g, mem_rightConjugate_iff]
  exact hYH (hY.conj_mem x hxY g)

theorem fusionGen_eq_top_of_mem_center [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hcl : fusionStronglyClosed Γ S) (hΓS : Γ ⊆ S) {x : G} (hx : x ∈ Γ)
    (hxZ : x ∈ center G) : fusionGen Γ = ⊤ := by
  refine fusionGen_eq_top_of_normal hS hcl hΓS (Y := zpowers x)
    (normal_of_le_center (zpowers_le.mpr hxZ))
    (zpowers_le.mpr (mem_fusionGen_of_mem hx)) hx (mem_zpowers x)

end Basic

section Family

variable {G : Type} [Group G]

@[expose] def memberSet (𝒯 : Set (Subgroup G)) : Set G :=
  {x | x ≠ 1 ∧ ∃ T ∈ 𝒯, x ∈ T}

theorem gammaSet_eq_memberSet (S : Subgroup G) (Δ : Set (Subgroup G)) :
    gammaSet S Δ = memberSet {T | T ∈ Δ ∧ T ≤ S} := by
  ext x
  simp only [gammaSet, memberSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, T, hT, hTS, hx⟩
    exact ⟨h1, T, ⟨hT, hTS⟩, hx⟩
  · rintro ⟨h1, T, ⟨hT, hTS⟩, hx⟩
    exact ⟨h1, T, hT, hTS, hx⟩

structure HypCore (S : Subgroup G) (𝒯 : Set (Subgroup G)) : Prop where
  sylow : IsSylowOf 2 S ⊤
  le : ∀ T ∈ 𝒯, T ≤ S
  closed : fusionStronglyClosed (memberSet 𝒯) S
  comm : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥

@[expose] def IsBig [Finite G] (R : Subgroup G) : Prop :=
  1 < Open.pRank 2 R ∧ ¬ IsElemAbelian 2 R

variable {S : Subgroup G} {𝒯 : Set (Subgroup G)}

theorem memberSet_subset (h : HypCore S 𝒯) : memberSet 𝒯 ⊆ S := by
  rintro x ⟨-, T, hT, hx⟩
  exact h.le T hT hx

theorem mem_memberSet {T : Subgroup G} (hT : T ∈ 𝒯) {x : G} (hx : x ∈ T) (hx1 : x ≠ 1) :
    x ∈ memberSet 𝒯 :=
  ⟨hx1, T, hT, hx⟩

theorem commute_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) {a b : G} (ha : a ∈ A)
    (hb : b ∈ B) : a * b = b * a := by
  have hc : ⁅a, b⁆ ∈ ⁅A, B⁆ := commutator_mem_commutator ha hb
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

end Family

section Induction

variable {G : Type} [Group G]

structure SylowShapeT (P : Type*) [Group P] : Prop where
  inv_center : ∀ x : P, x ^ 2 = 1 → x ∈ center P
  center_sq : ∀ z ∈ center P, z ^ 2 = 1
  card_center : 4 ≤ Nat.card (center P)
  not_comm : ¬ IsMulCommutative P

abbrev SylowShape (R : Subgroup G) : Prop := SylowShapeT R

theorem SylowShapeT.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (h : SylowShapeT P)
    (e : P ≃* Q) : SylowShapeT Q := by
  have hc : ∀ x : Q, x ∈ center Q ↔ e.symm x ∈ center P := by
    intro x
    simp only [mem_center_iff]
    constructor
    · intro hx y
      apply e.injective
      simp [map_mul, hx (e y)]
    · intro hx y
      apply e.symm.injective
      simp [map_mul, hx (e.symm y)]
  refine ⟨fun x hx => ?_, fun z hz => ?_, ?_, fun hcomm => h.not_comm ?_⟩
  · rw [hc]
    exact h.inv_center _ (by rw [← map_pow, hx, map_one])
  · apply e.symm.injective
    rw [map_pow, map_one]
    exact h.center_sq _ ((hc z).mp hz)
  · have hmap : (center P).map e.toMonoidHom = center Q := by
      ext x
      rw [hc]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨e.symm x, hx, by simp⟩
    rw [← hmap, card_map_of_injective e.injective]
    exact h.card_center
  · exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm' (e a) (e b)])⟩⟩

omit [Group G] in
theorem pRank_eq_open {G : Type} [Group G] [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p H = CFSG.Open.pRank p H := CFSG.SectionRank.pRank_coe_eq_openPRank p H

omit [Group G] in
theorem pRank_eq_of_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ}
    (hp : 1 < p) {A : Subgroup G} {B : Subgroup G'} (e : A ≃* B) :
    CFSG.pRank p A = CFSG.pRank p B := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp e]

omit [Group G] in
theorem isElemAbelian_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {p : ℕ} {A : Subgroup G}
    {B : Subgroup G'} (e : A ≃* B) (hA : IsElemAbelian p A) : IsElemAbelian p B := by
  have := hA.1
  refine ⟨⟨⟨fun a b => e.symm.injective ?_⟩⟩, fun y hy => ?_⟩
  · rw [map_mul, map_mul, mul_comm' (e.symm a) (e.symm b)]
  · have h1 := hA.2 _ (e.symm ⟨y, hy⟩).2
    have h2 : (e.symm ⟨y, hy⟩) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h1)
    have h3 : (⟨y, hy⟩ : B) ^ p = 1 := by
      rw [← e.apply_symm_apply ⟨y, hy⟩, ← map_pow, h2, map_one]
    have h4 := congrArg Subtype.val h3
    rwa [Subgroup.coe_pow] at h4

omit [Group G] in
theorem IsBig.of_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {A : Subgroup G} {B : Subgroup G'} (h : IsBig A) (e : A ≃* B) : IsBig B := by
  have h1 : Open.pRank 2 A = Open.pRank 2 B := by
    rw [← pRank_eq_open, ← pRank_eq_open]
    exact pRank_eq_of_mulEquiv one_lt_two e
  exact ⟨h1 ▸ h.1, fun hB => h.2 (isElemAbelian_of_mulEquiv e.symm hB)⟩

structure Hyp26 [Finite G] (S : Subgroup G) (𝒯 : Set (Subgroup G)) (R : Subgroup G) : Prop
    extends HypCore S 𝒯 where
  mem : R ∈ 𝒯
  big : IsBig R
  conj : ∀ g : G, rightConjugate R g ≤ S → rightConjugate R g ∈ 𝒯

@[expose] def Concl26 [Finite G] (𝒯 : Set (Subgroup G)) (R : Subgroup G) : Prop :=
  fusionGen (memberSet 𝒯) = ⊤ ∨
    ((∀ R' ∈ 𝒯, IsBig R' → R' = R) ∧ IsSylowOf 2 R (normalClosure (R : Set G)) ∧
      IsSzOrU3 (↥(normalClosure (R : Set G)) ⧸
        CFSG.Assembly.oddCore ↥(normalClosure (R : Set G))) ∧ SylowShape R)

@[expose] def Statement26 (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ (S : Subgroup G) (𝒯 : Set (Subgroup G)) (R : Subgroup G), Hyp26 S 𝒯 R → Concl26 𝒯 R

structure Hyp27 (S : Subgroup G) (𝒯 : Set (Subgroup G)) : Prop extends HypCore S 𝒯 where
  cyclic : ∀ T ∈ 𝒯, IsCyclic T ∧ Nat.card T = 4
  four : ∃ V : Subgroup G, Nat.card V = 4 ∧ IsElemAbelian 2 V ∧
    ∀ v ∈ V, v ≠ 1 → v ∈ memberSet 𝒯

@[expose] def Statement27 (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ (S : Subgroup G) (𝒯 : Set (Subgroup G)), Hyp27 S 𝒯 → fusionGen (memberSet 𝒯) = ⊤

theorem asc76Lemma26_of (h : ∀ n, Statement26 n) : Asc76Lemma26 := by
  intro G _ _ S Δ hS _ hinv hcl hcomm R hR hRS hrank hΦ
  set 𝒯 : Set (Subgroup G) := {T | T ∈ Δ ∧ T ≤ S} with h𝒯
  have hΓ : gammaSet S Δ = memberSet 𝒯 := gammaSet_eq_memberSet S Δ
  have hyp : Hyp26 S 𝒯 R :=
    { sylow := hS
      le := fun T hT => hT.2
      closed := hΓ ▸ hcl
      comm := fun T₁ hT₁ T₂ hT₂ hne => hcomm T₁ hT₁.1 T₂ hT₂.1 hT₁.2 hT₂.2 hne
      mem := ⟨hR, hRS⟩
      big := ⟨hrank, hΦ⟩
      conj := fun g hg => ⟨hinv R hR g, hg⟩ }
  rcases h (Nat.card G) G le_rfl S 𝒯 R hyp with htop | ⟨huniq, hsyl, hsz, -⟩
  · exact Or.inl (hΓ ▸ htop)
  · exact Or.inr ⟨fun R' hR' hR'S h1 h2 => huniq R' ⟨hR', hR'S⟩ ⟨h1, h2⟩, hsyl, hsz⟩

theorem asc76Lemma27_of (h : ∀ n, Statement27 n) : Asc76Lemma27 := by
  intro G _ _ S Δ hS hcyc _ hcl hcomm hV
  set 𝒯 : Set (Subgroup G) := {T | T ∈ Δ ∧ T ≤ S} with h𝒯
  have hΓ : gammaSet S Δ = memberSet 𝒯 := gammaSet_eq_memberSet S Δ
  rw [hΓ]
  exact h (Nat.card G) G le_rfl S 𝒯
    { sylow := hS
      le := fun T hT => hT.2
      closed := hΓ ▸ hcl
      comm := fun T₁ hT₁ T₂ hT₂ hne => hcomm T₁ hT₁.1 T₂ hT₂.1 hT₁.2 hT₂.2 hne
      cyclic := fun T hT => hcyc T hT.1
      four := by
        obtain ⟨V, hV4, hVe, hVΓ⟩ := hV
        exact ⟨V, hV4, hVe, fun v hv hv1 => hΓ ▸ hVΓ v hv hv1⟩ }

end Induction

section Conj

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}
  {R : Subgroup G}

omit [Finite G] in
theorem rightConjugate_mono {A B : Subgroup G} (h : A ≤ B) (y : G) :
    rightConjugate A y ≤ rightConjugate B y :=
  map_mono h

omit [Finite G] in
theorem rightConjugate_inv (A : Subgroup G) (y : G) :
    rightConjugate (rightConjugate A y) y⁻¹ = A := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem IsBig.rightConjugate {A : Subgroup G} (h : IsBig A) (y : G) :
    IsBig (rightConjugate A y) :=
  h.of_mulEquiv (equivMapOfInjective A (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective)

end Conj

section Sub

variable {G : Type} [Group G] (Y : Subgroup G)

abbrev subFamily (𝒯 : Set (Subgroup G)) : Set (Subgroup Y) :=
  (fun T => T.subgroupOf Y) '' 𝒯

variable {Y} {𝒯 : Set (Subgroup G)}

theorem mem_memberSet_subFamily (x : Y) :
    x ∈ memberSet (subFamily Y 𝒯) ↔ (x : G) ∈ memberSet 𝒯 := by
  constructor
  · rintro ⟨hx1, _, ⟨T, hT, rfl⟩, hx⟩
    exact ⟨fun h => hx1 (Subtype.ext h), T, hT, hx⟩
  · rintro ⟨hx1, T, hT, hx⟩
    exact ⟨fun h => hx1 (by rw [h]; rfl), _, ⟨T, hT, rfl⟩, hx⟩

theorem fusionGen_subFamily_le :
    (fusionGen (memberSet (subFamily Y 𝒯))).map Y.subtype ≤ fusionGen (memberSet 𝒯) := by
  rw [fusionGen, MonoidHom.map_closure, closure_le]
  rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
  rw [mem_memberSet_subFamily] at hx hgx
  exact mem_fusionGen_of_conj_mem hx (by simpa using hgx)

theorem le_fusionGen_of_subFamily (h : fusionGen (memberSet (subFamily Y 𝒯)) = ⊤) :
    Y ≤ fusionGen (memberSet 𝒯) := by
  have := fusionGen_subFamily_le (Y := Y) (𝒯 := 𝒯)
  rwa [h, ← MonoidHom.range_eq_map, range_subtype] at this

theorem rightConjugate_subgroupOf (A : Subgroup G) (g : Y) :
    rightConjugate (A.subgroupOf Y) g = (rightConjugate A (g : G)).subgroupOf Y := by
  ext x
  rw [mem_rightConjugate_iff, mem_subgroupOf, mem_subgroupOf, mem_rightConjugate_iff]
  rfl

theorem commutator_subgroupOf_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) :
    ⁅A.subgroupOf Y, B.subgroupOf Y⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  exact Subtype.ext (commute_of_commutator_eq_bot h ha hb).symm

theorem hypCore_subFamily [Finite G] {S' : Subgroup G} (hS'Y : S' ≤ Y)
    (hsyl : IsSylowOf 2 S' Y) (hle : ∀ T ∈ 𝒯, T ≤ S')
    (hcl : ∀ x ∈ memberSet 𝒯, ∀ y ∈ Y, y⁻¹ * x * y ∈ S' → y⁻¹ * x * y ∈ memberSet 𝒯)
    (hcomm : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥) :
    HypCore (S'.subgroupOf Y) (subFamily Y 𝒯) where
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← isSylowOf_map_subtype_iff Y, subgroupOf_map_subtype, inf_eq_left.mpr hS'Y,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hsyl
  le := by
    rintro _ ⟨T, hT, rfl⟩
    exact fun x hx => mem_subgroupOf.mpr (hle T hT (mem_subgroupOf.mp hx))
  closed := by
    intro x hx g hg
    rw [mem_memberSet_subFamily] at hx ⊢
    rw [mem_subgroupOf] at hg
    simpa using hcl _ hx g g.2 (by simpa using hg)
  comm := by
    rintro _ ⟨T₁, hT₁, rfl⟩ _ ⟨T₂, hT₂, rfl⟩ hne
    exact commutator_subgroupOf_eq_bot (hcomm T₁ hT₁ T₂ hT₂ fun h => hne (by rw [h]))

theorem rightConjugate_le_of_mem {R : Subgroup G} (hRY : R ≤ Y) {g : G} (hg : g ∈ Y) :
    rightConjugate R g ≤ Y := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h := Y.mul_mem (Y.mul_mem (Y.inv_mem hg) (hRY hx)) hg
  simpa [mul_assoc] using h

theorem concl26_of_sub [Finite G] {n : ℕ} (IH : Statement26 n) {S' R : Subgroup G}
    (hYn : Nat.card Y ≤ n) (hS'Y : S' ≤ Y) (hsyl : IsSylowOf 2 S' Y) (hle : ∀ T ∈ 𝒯, T ≤ S')
    (hcl : ∀ x ∈ memberSet 𝒯, ∀ y ∈ Y, y⁻¹ * x * y ∈ S' → y⁻¹ * x * y ∈ memberSet 𝒯)
    (hcomm : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥) (hR : R ∈ 𝒯) (hbig : IsBig R)
    (hconj : ∀ y ∈ Y, rightConjugate R y ≤ S' → rightConjugate R y ∈ 𝒯) :
    Y ≤ fusionGen (memberSet 𝒯) ∨ ((∀ R' ∈ 𝒯, IsBig R' → R' = R) ∧ SylowShape R) := by
  have hRY : R ≤ Y := (hle R hR).trans hS'Y
  have hyp : Hyp26 (S'.subgroupOf Y) (subFamily Y 𝒯) (R.subgroupOf Y) :=
    { toHypCore := hypCore_subFamily hS'Y hsyl hle hcl hcomm
      mem := ⟨R, hR, rfl⟩
      big := hbig.of_mulEquiv (subgroupOfEquivOfLe hRY).symm
      conj := by
        intro g hg
        rw [rightConjugate_subgroupOf] at hg ⊢
        have hle' : rightConjugate R g ≤ S' := by
          intro x hx
          have hxY : x ∈ Y := rightConjugate_le_of_mem hRY g.2 hx
          exact hg (show (⟨x, hxY⟩ : Y) ∈ (rightConjugate R g).subgroupOf Y from hx)
        exact ⟨_, hconj g g.2 hle', rfl⟩ }
  rcases IH Y hYn _ _ _ hyp with htop | ⟨huniq, -, -, hshape⟩
  · exact Or.inl (le_fusionGen_of_subFamily htop)
  · right
    refine ⟨fun R' hR' hbig' => ?_, hshape.of_mulEquiv (subgroupOfEquivOfLe hRY)⟩
    have hR'Y : R' ≤ Y := (hle R' hR').trans hS'Y
    have h := huniq _ ⟨R', hR', rfl⟩ (hbig'.of_mulEquiv (subgroupOfEquivOfLe hR'Y).symm)
    rw [subgroupOf_inj, inf_eq_left.mpr hR'Y, inf_eq_left.mpr hRY] at h
    exact h

theorem le_fusionGen_of_sub27 [Finite G] {n : ℕ} (IH : Statement27 n) {S' : Subgroup G}
    (hYn : Nat.card Y ≤ n) (hS'Y : S' ≤ Y) (hsyl : IsSylowOf 2 S' Y) (hle : ∀ T ∈ 𝒯, T ≤ S')
    (hcl : ∀ x ∈ memberSet 𝒯, ∀ y ∈ Y, y⁻¹ * x * y ∈ S' → y⁻¹ * x * y ∈ memberSet 𝒯)
    (hcomm : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥)
    (hcyc : ∀ T ∈ 𝒯, IsCyclic T ∧ Nat.card T = 4) {V : Subgroup G} (hVY : V ≤ Y)
    (hV4 : Nat.card V = 4) (hVe : IsElemAbelian 2 V) (hVΓ : ∀ v ∈ V, v ≠ 1 → v ∈ memberSet 𝒯) :
    Y ≤ fusionGen (memberSet 𝒯) := by
  apply le_fusionGen_of_subFamily
  refine IH Y hYn (S'.subgroupOf Y) (subFamily Y 𝒯)
    { toHypCore := hypCore_subFamily hS'Y hsyl hle hcl hcomm
      cyclic := ?_
      four := ⟨V.subgroupOf Y, ?_, ?_, ?_⟩ }
  · rintro _ ⟨T, hT, rfl⟩
    have hTY : T ≤ Y := (hle T hT).trans hS'Y
    obtain ⟨hTc, hT4⟩ := hcyc T hT
    have e := subgroupOfEquivOfLe hTY
    exact ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective,
      (Nat.card_congr e.toEquiv).trans hT4⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe hVY).toEquiv).trans hV4
  · exact isElemAbelian_of_mulEquiv (subgroupOfEquivOfLe hVY).symm hVe
  · intro v hv hv1
    rw [mem_memberSet_subFamily]
    exact hVΓ _ hv (fun h => hv1 (Subtype.ext h))

end Sub

section Quot

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal]

theorem map_rightConjugate {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G) (g : G) :
    (rightConjugate A g).map f = rightConjugate (A.map f) (f g) := by
  ext x
  simp only [mem_map, mem_rightConjugate_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨g * a * g⁻¹, ha, by simp [map_mul, map_inv]⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨g⁻¹ * a * g, by simpa [mul_assoc] using ha, ?_⟩
    simp only [map_mul, map_inv, hax]
    group

@[expose] def SylowLift (S N : Subgroup G) : Prop :=
  ∀ A : Subgroup G, IsPGroup 2 A → ∀ g : G, rightConjugate A g ≤ S ⊔ N →
    ∃ o ∈ N, rightConjugate A (g * o) ≤ S

theorem sylowLift [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) : SylowLift S N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hA g hg
  have hSSN : IsSylowOf 2 S (S ⊔ N) := hS.of_le le_sup_left le_top
  have hAg : IsPGroup 2 (rightConjugate A g) := hA.map _
  obtain ⟨k, hk, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hSSN hAg hg
  rw [rightConjugate_mul] at hle
  have hk' : k ∈ (N : Set G) * (S : Set G) := by
    rw [← Subgroup.normal_mul]
    rwa [sup_comm] at hk
  obtain ⟨o, ho, s, hs, rfl⟩ := hk'
  refine ⟨o, ho, ?_⟩
  have h1 := rightConjugate_mono hle s⁻¹
  rw [rightConjugate_mul, mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at h1
  refine h1.trans ?_
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  simpa [mul_assoc] using S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs)

variable [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}

abbrev quotFamily (N : Subgroup G) [N.Normal] (𝒯 : Set (Subgroup G)) :
    Set (Subgroup (G ⧸ N)) :=
  (fun T => T.map (QuotientGroup.mk' N)) '' 𝒯

omit [Finite G] in
noncomputable def equivMapMk {A : Subgroup G} (hA : A ⊓ N = ⊥) :
    A ≃* A.map (QuotientGroup.mk' N) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap A)
    ⟨fun a b hab => by
      have h1 : QuotientGroup.mk' N (a : G) = QuotientGroup.mk' N b := congrArg Subtype.val hab
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have h2 : (a : G)⁻¹ * b ∈ A ⊓ N := mem_inf.mpr ⟨A.mul_mem (A.inv_mem a.2) b.2, h1⟩
      rw [hA, mem_bot] at h2
      exact Subtype.ext (inv_mul_eq_one.mp h2),
     (QuotientGroup.mk' N).subgroupMap_surjective A⟩

omit [Finite G] in
theorem memberSet_quotFamily (hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥) :
    memberSet (quotFamily N 𝒯) = QuotientGroup.mk' N '' memberSet 𝒯 := by
  ext x
  constructor
  · rintro ⟨hx1, _, ⟨T, hT, rfl⟩, ⟨t, ht, rfl⟩⟩
    exact ⟨t, ⟨fun h => hx1 (by rw [h, map_one]), T, hT, ht⟩, rfl⟩
  · rintro ⟨t, ⟨ht1, T, hT, ht⟩, rfl⟩
    refine ⟨fun h => ht1 ?_, _, ⟨T, hT, rfl⟩, ⟨t, ht, rfl⟩⟩
    have : t ∈ T ⊓ N := mem_inf.mpr ⟨ht, (QuotientGroup.eq_one_iff t).mp h⟩
    rwa [hN T hT, mem_bot] at this

omit [Finite G] in
theorem comap_map_mk (A : Subgroup G) :
    (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A ⊔ N := by
  rw [comap_map_eq, QuotientGroup.ker_mk']

theorem exists_conj_lift (h : HypCore S 𝒯) {t : G} (ht : t ∈ memberSet 𝒯) {g : G}
    (hg : (QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N t * QuotientGroup.mk' N g ∈
      S.map (QuotientGroup.mk' N)) :
    ∃ o ∈ N, (g * o)⁻¹ * t * (g * o) ∈ memberSet 𝒯 := by
  have hgt : g⁻¹ * t * g ∈ S ⊔ N := by
    rw [← comap_map_mk, mem_comap]
    simpa [map_mul, map_inv] using hg
  have hA : IsPGroup 2 (zpowers t) :=
    h.sylow.isPGroup.to_le (zpowers_le.mpr (memberSet_subset h ht))
  have hle : rightConjugate (zpowers t) g ≤ S ⊔ N := by
    rw [rightConjugate, MonoidHom.map_zpowers]
    exact zpowers_le.mpr (by simpa [MulAut.conj_apply] using hgt)
  obtain ⟨o, ho, hS⟩ := sylowLift h.sylow (zpowers t) hA g hle
  refine ⟨o, ho, h.closed t ht _ (hS ?_)⟩
  rw [mem_rightConjugate_iff]
  have : (g * o) * ((g * o)⁻¹ * t * (g * o)) * (g * o)⁻¹ = t := by group
  rw [this]
  exact mem_zpowers t

theorem HypCore.quot (h : HypCore S 𝒯) (hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥) :
    HypCore (S.map (QuotientGroup.mk' N)) (quotFamily N 𝒯) where
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [isSylowOf_iff]
    refine ⟨le_top, h.sylow.isPGroup.map _, fun hdvd => ?_⟩
    rw [relIndex_top_right] at hdvd
    have h1 := (isSylowOf_iff.mp h.sylow).2.2
    rw [relIndex_top_right] at h1
    exact h1 (hdvd.trans (index_map_dvd _ (QuotientGroup.mk'_surjective N)))
  le := by
    rintro _ ⟨T, hT, rfl⟩
    exact map_mono (h.le T hT)
  closed := by
    rw [memberSet_quotFamily hN]
    rintro _ ⟨t, ht, rfl⟩ gbar hg
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    obtain ⟨o, ho, hgo⟩ := exists_conj_lift h ht hg
    refine ⟨_, hgo, ?_⟩
    have ho1 : QuotientGroup.mk' N o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    simp [map_mul, map_inv, ho1]
  comm := by
    rintro _ ⟨T₁, hT₁, rfl⟩ _ ⟨T₂, hT₂, rfl⟩ hne
    rw [← map_commutator, h.comm T₁ hT₁ T₂ hT₂ (fun h' => hne (by rw [h'])), Subgroup.map_bot]

theorem fusionGen_quot_le (h : HypCore S 𝒯) (hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥) :
    fusionGen (memberSet (quotFamily N 𝒯)) ≤
      (fusionGen (memberSet 𝒯)).map (QuotientGroup.mk' N) := by
  rw [fusionGen, closure_le]
  rintro gbar ⟨xbar, hx, hgx⟩
  rw [memberSet_quotFamily hN] at hx hgx
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
  have hS : (QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N t * QuotientGroup.mk' N g ∈
      S.map (QuotientGroup.mk' N) := by
    obtain ⟨t', ht', heq⟩ := hgx
    rw [← heq]
    exact ⟨t', memberSet_subset h ht', rfl⟩
  obtain ⟨o, ho, hgo⟩ := exists_conj_lift h ht hS
  refine ⟨g * o, mem_fusionGen_of_conj_mem ht hgo, ?_⟩
  have ho1 : QuotientGroup.mk' N o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  simp [map_mul, ho1]

theorem fusionGen_eq_top_of_quot (h : HypCore S 𝒯) (hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥)
    (hNH : N ≤ fusionGen (memberSet 𝒯)) (htop : fusionGen (memberSet (quotFamily N 𝒯)) = ⊤) :
    fusionGen (memberSet 𝒯) = ⊤ := by
  have h1 := fusionGen_quot_le h hN
  rw [htop, top_le_iff] at h1
  have h2 := comap_map_mk (N := N) (fusionGen (memberSet 𝒯))
  rw [h1, comap_top, sup_eq_left.mpr hNH] at h2
  exact h2.symm

theorem Hyp26.quot {R : Subgroup G} (h : Hyp26 S 𝒯 R) (hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥) :
    Hyp26 (S.map (QuotientGroup.mk' N)) (quotFamily N 𝒯) (R.map (QuotientGroup.mk' N)) where
  toHypCore := h.toHypCore.quot hN
  mem := ⟨R, h.mem, rfl⟩
  big := h.big.of_mulEquiv (equivMapMk (hN R h.mem))
  conj := by
    intro gbar hg
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    rw [← map_rightConjugate] at hg ⊢
    have hle : rightConjugate R g ≤ S ⊔ N := by
      rw [← comap_map_mk]
      exact map_le_iff_le_comap.mp hg
    obtain ⟨o, ho, hS⟩ := sylowLift h.sylow R (h.sylow.isPGroup.to_le (h.le R h.mem)) g hle
    refine ⟨_, h.conj _ hS, ?_⟩
    have ho1 : QuotientGroup.mk' N o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    change (rightConjugate R (g * o)).map (QuotientGroup.mk' N) = _
    rw [map_rightConjugate, map_rightConjugate, map_mul, ho1, mul_one]

theorem Hyp27.quot (h : Hyp27 S 𝒯) (hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥) :
    Hyp27 (S.map (QuotientGroup.mk' N)) (quotFamily N 𝒯) where
  toHypCore := h.toHypCore.quot hN
  cyclic := by
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨hTc, hT4⟩ := h.cyclic T hT
    have e := equivMapMk (hN T hT)
    exact ⟨isCyclic_of_surjective e.toMonoidHom e.surjective,
      (Nat.card_congr e.toEquiv).symm.trans hT4⟩
  four := by
    obtain ⟨V, hV4, hVe, hVΓ⟩ := h.four
    have hVN : V ⊓ N = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hvV, hvN⟩ := mem_inf.mp hv
      by_contra hv1
      obtain ⟨-, T, hT, hvT⟩ := hVΓ v hvV hv1
      have : v ∈ T ⊓ N := mem_inf.mpr ⟨hvT, hvN⟩
      rw [hN T hT, mem_bot] at this
      exact hv1 this
    have e := equivMapMk hVN
    refine ⟨V.map (QuotientGroup.mk' N), (Nat.card_congr e.toEquiv).symm.trans hV4,
      isElemAbelian_of_mulEquiv e hVe, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ hv1
    rw [memberSet_quotFamily hN]
    exact ⟨v, hVΓ v hv (fun h' => hv1 (by rw [h', map_one])), rfl⟩

theorem fusionGen_eq_top_of_quot27 {n : ℕ} (IH : Statement27 n) (h : Hyp27 S 𝒯)
    (hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥) (hNH : N ≤ fusionGen (memberSet 𝒯))
    (hcard : Nat.card (G ⧸ N) ≤ n) : fusionGen (memberSet 𝒯) = ⊤ :=
  fusionGen_eq_top_of_quot h.toHypCore hN hNH (IH _ hcard _ _ (h.quot hN))

end Quot

end CFSG.ComponentClassification.Asc76.L26
