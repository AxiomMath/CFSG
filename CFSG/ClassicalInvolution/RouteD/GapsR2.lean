module

public import CFSG.ClassicalInvolution.RouteD.GapsLocal
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

abbrev locMk (Ω : Set (Subgroup G)) (x : G) : ↥(locLayer Ω x) →* locQuot Ω x :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))

abbrev compFund {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (i : Fin D.card) :
    Set (Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K) :=
  fundamentalSubgroups (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D

@[expose] def compMembers (Ω : Set (Subgroup G)) (x : G)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card) : Set (Subgroup G) :=
  {N | N ∈ centralizingMembers Ω {x} ∧ locImg Ω x N ≤ (D.hom i).range}

@[expose] def FundPerfect (t : StatedLieTag) {K : Type} [Group K] (D : UniversalRootDatum K) :
    Prop :=
  ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆

@[expose] def Corr (Ω : Set (Subgroup G)) (x : G)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card) (N : Subgroup G)
    (R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K) : Prop :=
  N ∈ centralizingMembers Ω {x} ∧ R ∈ compFund D i ∧ locImg Ω x N = R.map (D.hom i)

theorem subgroupOf_le_commutator {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) :
    L.subgroupOf (locLayer Ω x) ≤ ⁅L.subgroupOf (locLayer Ω x), L.subgroupOf (locLayer Ω x)⁆ := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  exact (commutator_eq_of_isClassicalMember (hz.subgroupOf p f (le_centralizingLayer hL))).ge

theorem locImg_le_commutator {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) :
    locImg Ω x L ≤ ⁅locImg Ω x L, locImg Ω x L⁆ := by
  have h := Subgroup.map_mono (f := locMk Ω x) (subgroupOf_le_commutator hΩ hL)
  rwa [Subgroup.map_commutator] at h

theorem locImg_ne_bot [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) :
    locImg Ω x L ≠ ⊥ := by
  intro h
  have hc := card_locImg hΩ hex hL
  rw [h, Subgroup.card_bot] at hc
  have hsub : Subsingleton SL(2, GaloisField p f) := (Nat.card_eq_one_iff_unique.mp hc.symm).1
  let a : SL(2, GaloisField p f) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h1 := congrArg (fun g : SL(2, GaloisField p f) => g.1 0 1) (Subsingleton.elim a 1)
  simp [a] at h1

theorem locImg_not_commutative [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) :
    ¬ ∀ a ∈ locImg Ω x N, ∀ b ∈ locImg Ω x N, a * b = b * a := by
  intro hab
  have hbot : locImg Ω x N = ⊥ := by
    rw [eq_bot_iff]
    refine (locImg_le_commutator hΩ hN).trans (Subgroup.commutator_le.mpr ?_)
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_def, hab a ha b hb]
    group
  exact locImg_ne_bot hΩ hex hN hbot

theorem eq_of_locImg_le_range [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i j : Fin D.card} {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x})
    (hi : locImg Ω x N ≤ (D.hom i).range) (hj : locImg Ω x N ≤ (D.hom j).range) : i = j := by
  by_contra hij
  exact locImg_not_commutative hΩ hex hN fun a ha b hb => commutes_range D hij a (hi ha) b (hj hb)

theorem exists_corr_left [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card} {N : Subgroup G} (hN : N ∈ compMembers Ω x D i) :
    ∃ R, Corr Ω x D i N R := by
  obtain ⟨hNm, hi⟩ := hN
  obtain ⟨j, R, hR, hRN⟩ := D.fundamental _ (mem_locFamily_iff.mpr ⟨N, hNm, rfl⟩)
  have hj : locImg Ω x N ≤ (D.hom j).range := hRN ▸ Subgroup.map_le_range _ _
  have hij := eq_of_locImg_le_range hΩ hex D hNm hj hi
  subst hij
  exact ⟨R, hNm, hR, hRN⟩

theorem eq_of_map_eq_of_central {K X : Type*} [Group K] [Group X] (φ : K →* X)
    (hker : φ.ker ≤ Subgroup.center K) {R R' : Subgroup K} (hR : R ≤ ⁅R, R⁆)
    (hR' : R' ≤ ⁅R', R'⁆) (h : R.map φ = R'.map φ) : R = R' := by
  have key : ∀ A B : Subgroup K, A.map φ = B.map φ → A ≤ B ⊔ φ.ker := by
    intro A B hAB a ha
    have : φ a ∈ B.map φ := hAB ▸ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := this
    have hmem : b⁻¹ * a ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hmem)
  exact le_antisymm (le_of_perfect_of_le_sup_center hker hR (key R R' h))
    (le_of_perfect_of_le_sup_center hker hR' (key R' R h.symm))

theorem corr_unique_left {Ω : Set (Subgroup G)} {x : G}
    {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card}
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {N : Subgroup G} {R R' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (h : Corr Ω x D i N R) (h' : Corr Ω x D i N R') : R = R' :=
  eq_of_map_eq_of_central (D.hom i) (D.ker_le_center i) (hperf R h.2.1) (hperf R' h'.2.1)
    (h.2.2.symm.trans h'.2.2)

theorem corr_unique_right [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card} {N N' : Subgroup G}
    {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (h : Corr Ω x D i N R) (h' : Corr Ω x D i N' R) : N = N' :=
  locImg_injOn hΩ hP1 h.1 h'.1 (h.2.2.trans h'.2.2.symm)

theorem locImg_conjSub_layer {Ω : Set (Subgroup G)} {x : G} (N : Subgroup G)
    (y : ↥(locLayer Ω x)) :
    locImg Ω x (conjSub (y : G) N) =
      (locImg Ω x N).map (MulAut.conj (locMk Ω x y)).toMonoidHom := by
  unfold locImg
  rw [← conjSub_subgroupOf (locLayer Ω x) y N]
  show ((N.subgroupOf (locLayer Ω x)).map (MulAut.conj y).toMonoidHom).map (locMk Ω x) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem exists_corr_right {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hR : R ∈ compFund D i) : ∃ N, Corr Ω x D i N R := by
  obtain ⟨R₁, hR₁, hmem⟩ := D.meets i
  obtain ⟨N₁, hN₁, hN₁R⟩ := mem_locFamily_iff.mp hmem
  obtain ⟨g, hg⟩ := hsc R₁ hR₁ R hR
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (D.hom i g)
  have hyx : (y : G) ∈ Subgroup.centralizer ({x} : Set G) :=
    centralizingLayer_le_centralizer Ω {x} y.2
  refine ⟨conjSub (y : G) N₁, ⟨hΩ.conjInvariant _ N₁ hN₁.1, fun a ha => ?_⟩, ?_, ?_⟩
  · rw [mem_conjSub_iff] at ha
    have hx' := hN₁.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  · exact hR
  · rw [locImg_conjSub_layer, hN₁R, show locMk Ω x y = D.hom i g from hy, hg]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp

theorem corr_commutes [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card}
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {N N' : Subgroup G} {R R' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (h : Corr Ω x D i N R) (h' : Corr Ω x D i N' R') : Commutes N N' ↔ Commutes R R' := by
  rw [commutes_iff_locImg hΩ hP1 h.1 h'.1, h.2.2, h'.2.2]
  constructor
  · intro hc
    exact commutes_of_commutes_map (D.hom i) (D.ker_le_center i)
      (Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb))
        (hperf R h.2.1))) hc
  · intro hc
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]

theorem exists_compMembersEquiv [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D) :
    ∃ e : compMembers Ω x D i ≃ compFund D i, ∀ N : compMembers Ω x D i,
      Corr Ω x D i N.1 (e N).1 := by
  choose g hg using fun N : compMembers Ω x D i => exists_corr_left hΩ hex D N.2
  have hinj : Function.Injective (fun N : compMembers Ω x D i => (⟨g N, (hg N).2.1⟩ : compFund D i)) := by
    intro N N' h
    have h1 : g N = g N' := congrArg Subtype.val h
    exact Subtype.ext (corr_unique_right hΩ hP1 (hg N) (h1 ▸ hg N'))
  have hsurj : Function.Surjective
      (fun N : compMembers Ω x D i => (⟨g N, (hg N).2.1⟩ : compFund D i)) := by
    rintro ⟨R, hR⟩
    obtain ⟨N, hN⟩ := exists_corr_right hΩ D hsc hR
    refine ⟨⟨N, hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩, Subtype.ext ?_⟩
    exact corr_unique_left hperf (hg ⟨N, hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩) hN
  exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun N => hg N⟩

theorem fundamentalSingleClass_of_ne {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (h1 : D.tag i ≠ .G2)
    (h2 : D.tag i ≠ .trialityD4) :
    FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D :=
  CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ (D.isFundTag i)
    (D.admissible i) h1 h2

theorem exists_unique_comp [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) : ∃! i, N ∈ compMembers Ω x D i := by
  obtain ⟨i, hi⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  exact ⟨i, ⟨hN, hi⟩, fun j hj => eq_of_locImg_le_range hΩ hex D hN hj.2 hi⟩

theorem commutes_of_ne_comp [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i j : Fin D.card} (hij : i ≠ j) {N N' : Subgroup G} (hN : N ∈ compMembers Ω x D i)
    (hN' : N' ∈ compMembers Ω x D j) : Commutes N N' :=
  commutes_of_commutes_locImg hΩ hP1 hN.1 hN'.1 fun a ha b hb =>
    commutes_range D hij a (hN.2 ha) b (hN'.2 hb)

theorem exists_pair [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {K₀ Kβ : Subgroup G}
    (h0 : K₀ ∈ centralizingMembers Ω {x}) (hβ : Kβ ∈ centralizingMembers Ω {x})
    (hnc : ¬ Commutes K₀ Kβ) :
    ∃ i, K₀ ∈ compMembers Ω x D i ∧ Kβ ∈ compMembers Ω x D i ∧
      ∀ N ∈ centralizingMembers Ω {x}, ¬ Commutes N Kβ → N ∈ compMembers Ω x D i := by
  obtain ⟨i, h0i, hβi, -⟩ := attached_in_same_component hΩ hP1 D h0 hβ h0 hnc hnc
  refine ⟨i, ⟨h0, h0i⟩, ⟨hβ, hβi⟩, fun N hN hatt => ?_⟩
  obtain ⟨i', -, hβi', hNi'⟩ := attached_in_same_component hΩ hP1 D h0 hβ hN hnc hatt
  have := eq_of_locImg_le_range hΩ hex D hβ hβi' hβi
  subst this
  exact ⟨hN, hNi'⟩

theorem r2_correspondence [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hsc : ∀ i, FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : ∀ i, FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K₀ Kβ : Subgroup G} (h0 : K₀ ∈ centralizingMembers Ω {x})
    (hβ : Kβ ∈ centralizingMembers Ω {x}) (hnc : ¬ Commutes K₀ Kβ) :
    ∃ i, ∃ R₀ Rβ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K,
      Corr Ω x D i K₀ R₀ ∧ Corr Ω x D i Kβ Rβ ∧ ¬ Commutes R₀ Rβ ∧
      (∀ N ∈ centralizingMembers Ω {x}, ¬ Commutes N Kβ → N ∈ compMembers Ω x D i) ∧
      ∃ e : compMembers Ω x D i ≃ compFund D i, ∀ N : compMembers Ω x D i,
        Corr Ω x D i N.1 (e N).1 ∧ (Commutes N.1 K₀ ↔ Commutes (e N).1 R₀) ∧
          (Commutes N.1 Kβ ↔ Commutes (e N).1 Rβ) := by
  obtain ⟨i, h0i, hβi, hatt⟩ := exists_pair hΩ hex hP1 D h0 hβ hnc
  obtain ⟨R₀, hR₀⟩ := exists_corr_left hΩ hex D h0i
  obtain ⟨Rβ, hRβ⟩ := exists_corr_left hΩ hex D hβi
  obtain ⟨e, he⟩ := exists_compMembersEquiv hΩ hex hP1 D (hsc i) (hperf i)
  refine ⟨i, R₀, Rβ, hR₀, hRβ, ?_, hatt, e, fun N => ⟨he N, ?_, ?_⟩⟩
  · rw [← corr_commutes hΩ hP1 (hperf i) hR₀ hRβ]
    exact hnc
  · exact corr_commutes hΩ hP1 (hperf i) (he N) hR₀
  · exact corr_commutes hΩ hP1 (hperf i) (he N) hRβ

theorem commutes_symm {H : Type*} [Group H] {A B : Subgroup H} (h : Commutes A B) :
    Commutes B A := fun a ha b hb => (h b hb a ha).symm

theorem le_centralizer_iff_locImg [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (y : ↥(locLayer Ω x)) :
    L ≤ Subgroup.centralizer ({(y : G)} : Set G) ↔
      locImg Ω x L ≤ Subgroup.centralizer ({locMk Ω x y} : Set (locQuot Ω x)) := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h hb))
  · intro h l hl
    obtain ⟨z, hz⟩ := hΩ.classical L hL.1
    have hperf := (hz.subgroupOf p f (le_centralizingLayer hL)).perfect
    have hc : Commutes ((L.subgroupOf (locLayer Ω x)).map (locMk Ω x))
        ((Subgroup.zpowers y).map (locMk Ω x)) := by
      rw [MonoidHom.map_zpowers]
      intro a ha b hb
      have : Subgroup.zpowers (locMk Ω x y) ≤ Subgroup.centralizer (locImg Ω x L : Set _) := by
        rw [Subgroup.zpowers_le]
        intro a' ha'
        exact Subgroup.mem_centralizer_singleton_iff.mp (h ha')
      exact Subgroup.mem_centralizer_iff.mp (this hb) a ha
    have := commutes_of_commutes_oddQuotient hP1 hperf hc
    have hly : (⟨l, le_centralizingLayer hL hl⟩ : ↥(locLayer Ω x)) * y =
        y * ⟨l, le_centralizingLayer hL hl⟩ :=
      this _ (Subgroup.mem_subgroupOf.mpr hl) y (Subgroup.mem_zpowers y)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hly

theorem le_centralizer_iff_map {K X : Type*} [Group K] [Group X] (φ : K →* X)
    (hker : φ.ker ≤ Subgroup.center K) {R : Subgroup K} (hR : R ≤ ⁅R, R⁆) (k : K) :
    R ≤ Subgroup.centralizer ({k} : Set K) ↔
      R.map φ ≤ Subgroup.centralizer ({φ k} : Set X) := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (h hb)]
  · intro h r hr
    have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr (le_antisymm
      (Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) hR)
    have hc : Commutes (R.map φ) ((Subgroup.zpowers k).map φ) := by
      rw [MonoidHom.map_zpowers]
      intro a ha b hb
      have : Subgroup.zpowers (φ k) ≤ Subgroup.centralizer (R.map φ : Set X) := by
        rw [Subgroup.zpowers_le]
        intro a' ha'
        exact Subgroup.mem_centralizer_singleton_iff.mp (h ha')
      exact Subgroup.mem_centralizer_iff.mp (this hb) a ha
    have := commutes_of_commutes_map φ hker hperf hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact this r hr k (Subgroup.mem_zpowers k)

theorem corr_le_centralizer_iff [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card}
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {N : Subgroup G} {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (h : Corr Ω x D i N R) (y : ↥(locLayer Ω x))
    (k : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
    (hk : D.hom i k = locMk Ω x y) :
    N ≤ Subgroup.centralizer ({(y : G)} : Set G) ↔ R ≤ Subgroup.centralizer ({k} : Set _) := by
  rw [le_centralizer_iff_locImg hΩ hP1 h.1, h.2.2, ← hk]
  exact (le_centralizer_iff_map (D.hom i) (D.ker_le_center i) (hperf R h.2.1) k).symm

theorem commutes_iff_le_centralizer {Ω : Set (Subgroup G)} [Finite G] (hMFZ : FundNoncentral p)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {t : G} (hP1 : LocalOddCentral Ω {t})
    (D : LieSystemData p f (locQuot Ω t) (locFamily Ω t)) {K₀ Kβ N : Subgroup G}
    (hKβ : Kβ ∈ Ω) (ht : IsClassicalMember p f Kβ t) (hN : N ∈ Ω) (hN0 : Commutes N K₀)
    (hnc : ¬ Commutes K₀ Kβ) :
    Commutes N Kβ ↔ N ≤ Subgroup.centralizer ({t} : Set G) := by
  constructor
  · intro h n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h n hn t ht.mem
  · intro h
    have hKβt : Kβ ∈ centralizingMembers Ω {t} := ⟨hKβ, le_centralizer_of_isClassicalMember ht⟩
    rcases commutes_or_eq_of_involution hMFZ hΩ hex hP1 D hKβt ⟨hN, h⟩ ht with hc | rfl
    · exact commutes_symm hc
    · exact absurd (commutes_symm hN0) hnc

theorem ncard_eq_of_equiv {α β : Type*} {A : Set α} {B : Set β} (e : A ≃ B) (P : α → Prop)
    (Q : β → Prop) (h : ∀ a : A, P a.1 ↔ Q (e a).1) :
    Set.ncard {a | a ∈ A ∧ P a} = Set.ncard {b | b ∈ B ∧ Q b} := by
  refine Set.ncard_congr (fun a ha => (e ⟨a, ha.1⟩).1) (fun a ha => ⟨(e _).2, ?_⟩) ?_ ?_
  · exact (h ⟨a, ha.1⟩).mp ha.2
  · intro a b ha hb hab
    have := e.injective (Subtype.ext hab)
    exact congrArg Subtype.val this
  · intro b hb
    refine ⟨(e.symm ⟨b, hb.1⟩).1, ⟨(e.symm ⟨b, hb.1⟩).2, ?_⟩, ?_⟩
    · have := (h (e.symm ⟨b, hb.1⟩)).mpr
      rw [Equiv.apply_symm_apply] at this
      exact this hb.2
    · have : e ⟨(e.symm ⟨b, hb.1⟩).1, (e.symm ⟨b, hb.1⟩).2⟩ = ⟨b, hb.1⟩ :=
        e.apply_symm_apply ⟨b, hb.1⟩
      exact congrArg Subtype.val this

theorem r2_ncard [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {x : G} (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hsc : ∀ i, FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : ∀ i, FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K₀ Kβ : Subgroup G} (h0 : K₀ ∈ centralizingMembers Ω {x})
    (hβ : Kβ ∈ centralizingMembers Ω {x}) (hnc : ¬ Commutes K₀ Kβ) :
    ∃ i, ∃ R₀ Rβ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K,
      Corr Ω x D i K₀ R₀ ∧ Corr Ω x D i Kβ Rβ ∧
      Set.ncard {N | N ∈ compMembers Ω x D i ∧ Commutes N K₀} =
        Set.ncard {R | R ∈ compFund D i ∧ Commutes R R₀} ∧
      Set.ncard {N | N ∈ compMembers Ω x D i ∧ Commutes N K₀ ∧ ¬ Commutes N Kβ} =
        Set.ncard {R | R ∈ compFund D i ∧ Commutes R R₀ ∧ ¬ Commutes R Rβ} := by
  obtain ⟨i, R₀, Rβ, hR₀, hRβ, -, -, e, he⟩ := r2_correspondence hΩ hex hP1 D hsc hperf h0 hβ hnc
  exact ⟨i, R₀, Rβ, hR₀, hRβ, ncard_eq_of_equiv e _ _ fun N => (he N).2.1,
    ncard_eq_of_equiv e _ _ fun N => and_congr (he N).2.1 (not_congr (he N).2.2)⟩

theorem exists_attached_member [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hsc : ∀ i, FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : ∀ i, FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K₀ Kβ : Subgroup G} (h0 : K₀ ∈ centralizingMembers Ω {x})
    (hβ : Kβ ∈ centralizingMembers Ω {x}) (hnc : ¬ Commutes K₀ Kβ) (hne : K₀ ≠ Kβ)
    (hMN : ∀ i, K₀ ∈ compMembers Ω x D i →
      ∀ R₀ ∈ compFund D i, ∀ Rβ ∈ compFund D i, R₀ ≠ Rβ → ¬ Commutes R₀ Rβ →
        ∃ R ∈ compFund D i, Commutes R R₀ ∧ ¬ Commutes R Rβ) :
    ∃ N ∈ centralizingMembers Ω {x}, Commutes N K₀ ∧ ¬ Commutes N Kβ := by
  obtain ⟨i, R₀, Rβ, hR₀, hRβ, hnc', -, -⟩ := r2_correspondence hΩ hex hP1 D hsc hperf h0 hβ hnc
  have h0i : K₀ ∈ compMembers Ω x D i := ⟨h0, hR₀.2.2 ▸ Subgroup.map_le_range _ _⟩
  have hRne : R₀ ≠ Rβ := by
    intro h
    subst h
    exact hne (corr_unique_right hΩ hP1 hR₀ hRβ)
  obtain ⟨R, hR, hc, hnc''⟩ := hMN i h0i R₀ hR₀.2.1 Rβ hRβ.2.1 hRne hnc'
  obtain ⟨N, hN⟩ := exists_corr_right hΩ D (hsc i) hR
  refine ⟨N, hN.1, ?_, ?_⟩
  · exact (corr_commutes hΩ hP1 (hperf i) hN hR₀).mpr hc
  · rw [corr_commutes hΩ hP1 (hperf i) hN hRβ]
    exact hnc''

end CFSG.ClassicalInvolution.RouteD.Gaps
