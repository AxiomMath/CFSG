module

public import CFSG.ClassicalInvolution.Generic.InductionLocal
public import CFSG.ClassicalInvolution.Generic.Generation.Layer

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic

section Perfect

variable {Y : Type*} [Group Y]

theorem le_of_perfect_of_le_sup_center {A B Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y)
    (hA : A ≤ ⁅A, A⁆) (h : A ≤ B ⊔ Z) : A ≤ B := by
  have hZc : ∀ z ∈ Z, ∀ h ∈ (⊤ : Subgroup Y), z * h = h * z := fun z hz h _ =>
    (Subgroup.mem_center_iff.mp (hZ hz) h).symm
  refine hA.trans (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_)
  obtain ⟨a, ha, z, hz, rfl⟩ :=
    exists_mul_of_mem_sup_central (H := ⊤) (A := B) le_top hZc (h hg₁)
  obtain ⟨b, hb, w, hw, rfl⟩ :=
    exists_mul_of_mem_sup_central (H := ⊤) (A := B) le_top hZc (h hg₂)
  rw [commutator_mul_of_central (H := ⊤) trivial trivial trivial (hZc z hz) (hZc w hw)]
  rw [commutatorElement_def]
  exact B.mul_mem (B.mul_mem (B.mul_mem ha hb) (B.inv_mem ha)) (B.inv_mem hb)

theorem eq_of_map_mk_eq_of_central {O : Subgroup Y} [O.Normal] (hO : O ≤ Subgroup.center Y)
    {A B : Subgroup Y} (hA : A ≤ ⁅A, A⁆) (hB : B ≤ ⁅B, B⁆)
    (h : A.map (QuotientGroup.mk' O) = B.map (QuotientGroup.mk' O)) : A = B := by
  have key : ∀ A B : Subgroup Y, A.map (QuotientGroup.mk' O) = B.map (QuotientGroup.mk' O) →
      A ≤ B ⊔ O := by
    intro A B hAB a ha
    have : QuotientGroup.mk' O a ∈ B.map (QuotientGroup.mk' O) := hAB ▸ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := this
    have hmem : b⁻¹ * a ∈ O := QuotientGroup.eq.mp hba
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hmem)
  exact le_antisymm (le_of_perfect_of_le_sup_center hO hA (key A B h))
    (le_of_perfect_of_le_sup_center hO hB (key B A h.symm))

end Perfect

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

abbrev locLayer (Ω : Set (Subgroup G)) (x : G) : Subgroup G :=
  centralizingLayer Ω {x}

abbrev locQuot (Ω : Set (Subgroup G)) (x : G) : Type :=
  ↥(locLayer Ω x) ⧸ classicalInvolutionOddCore ↥(locLayer Ω x)

@[expose] def locImg (Ω : Set (Subgroup G)) (x : G) (L : Subgroup G) :
    Subgroup (locQuot Ω x) :=
  (L.subgroupOf (locLayer Ω x)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)))

@[expose] def locFamily (Ω : Set (Subgroup G)) (x : G) : Set (Subgroup (locQuot Ω x)) :=
  oddQuotientFamily (restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}))

theorem mem_locFamily_iff {Ω : Set (Subgroup G)} {x : G} {K : Subgroup (locQuot Ω x)} :
    K ∈ locFamily Ω x ↔ ∃ L ∈ centralizingMembers Ω {x}, locImg Ω x L = K := by
  constructor
  · rintro ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact ⟨L, hL, rfl⟩
  · rintro ⟨L, hL, rfl⟩
    exact ⟨L.subgroupOf (locLayer Ω x), ⟨L, hL, le_centralizingLayer hL, rfl⟩, rfl⟩

theorem locFamily_eq_image (Ω : Set (Subgroup G)) (x : G) :
    locFamily Ω x = locImg Ω x '' centralizingMembers Ω {x} := by
  ext K
  rw [mem_locFamily_iff]
  exact ⟨fun ⟨L, hL, h⟩ => ⟨L, hL, h⟩, fun ⟨L, hL, h⟩ => ⟨L, hL, h⟩⟩

theorem commutator_eq_of_isClassicalMember {L : Subgroup G} {z : G}
    (h : IsClassicalMember p f L z) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp h.perfect

theorem le_centralizer_of_isClassicalMember {L : Subgroup G} {z : G}
    (h : IsClassicalMember p f L z) : L ≤ Subgroup.centralizer ({z} : Set G) :=
  CFSG.ClassicalInvolution.isSubnormal_le h.subnormal

theorem locImg_injOn [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) : Set.InjOn (locImg Ω x) (centralizingMembers Ω {x}) := by
  have hperf : ∀ L ∈ centralizingMembers Ω {x},
      L.subgroupOf (locLayer Ω x) ≤ ⁅L.subgroupOf (locLayer Ω x), L.subgroupOf (locLayer Ω x)⁆ := by
    intro L hL
    obtain ⟨z, hz⟩ := hΩ.classical L hL.1
    exact (commutator_eq_of_isClassicalMember (hz.subgroupOf p f (le_centralizingLayer hL))).ge
  intro L hL L' hL' h
  have h1 := eq_of_map_mk_eq_of_central (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (hperf L hL) (hperf L' hL') h
  have h2 := (Subgroup.subgroupOf_inj).mp h1
  rwa [inf_eq_left.mpr (le_centralizingLayer hL), inf_eq_left.mpr (le_centralizingLayer hL')]
    at h2

theorem ncard_centralizingMembers_eq [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    {x : G} (hP1 : LocalOddCentral Ω {x}) :
    (centralizingMembers Ω {x}).ncard = (locFamily Ω x).ncard := by
  rw [locFamily_eq_image, (locImg_injOn hΩ hP1).ncard_image]

theorem centralizingMembers_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G) :
    centralizingMembers Ω {g * x * g⁻¹} = conjSub g '' centralizingMembers Ω {x} := by
  ext L
  constructor
  · rintro ⟨hL, hLC⟩
    refine ⟨conjSub g⁻¹ L, ⟨hΩ g⁻¹ L hL, fun y hy => ?_⟩, conjSub_conjSub_inv g L⟩
    rw [mem_conjSub_iff] at hy
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hLC hy)
    rw [inv_inv] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = x * y := by group
  · rintro ⟨L', ⟨hL', hL'C⟩, rfl⟩
    refine ⟨hΩ g L' hL', fun y hy => ?_⟩
    rw [mem_conjSub_iff] at hy
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hL'C hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = (g * x * g⁻¹) * y := by group

theorem ncard_centralizingMembers_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G) :
    (centralizingMembers Ω {g * x * g⁻¹}).ncard = (centralizingMembers Ω {x}).ncard := by
  rw [centralizingMembers_conj hΩ, Set.ncard_image_of_injective _ (conjSub_injective g)]

@[expose] def LocalShapeA (p f m : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), D.card = 2 ∧
    ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧ D.tag i₁ = .PSL ∧
      D.rank i₁ = m + 1

end Local

end CFSG.ClassicalInvolution.RouteD
