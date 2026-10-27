module

public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)

section Act

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

@[expose] noncomputable def actX (c : G) (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G)) :
    MulAut (locQuot Ω x) :=
  QuotientGroup.congr (classicalInvolutionOddCore ↥(locLayer Ω x))
    (classicalInvolutionOddCore ↥(locLayer Ω x))
    (conjOnNormalizer (locLayer Ω x) ⟨c, hc⟩)
    (CFSG.ComponentClassification.OddCore.equiv_invariant _)

theorem actX_mk (c : G) (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G))
    (y : ↥(locLayer Ω x)) :
    actX c hc (locMk Ω x y) = locMk Ω x (conjOnNormalizer (locLayer Ω x) ⟨c, hc⟩ y) := rfl

theorem actX_congr {c c' : G} (h : c = c') (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G))
    (hc' : c' ∈ Subgroup.normalizer (locLayer Ω x : Set G)) :
    actX (Ω := Ω) (x := x) c hc = actX c' hc' := by
  subst h
  rfl

theorem actX_mul (c₁ c₂ : G) (h₁ : c₁ ∈ Subgroup.normalizer (locLayer Ω x : Set G))
    (h₂ : c₂ ∈ Subgroup.normalizer (locLayer Ω x : Set G))
    (h₃ : c₁ * c₂ ∈ Subgroup.normalizer (locLayer Ω x : Set G)) :
    actX (Ω := Ω) (x := x) (c₁ * c₂) h₃ = actX c₁ h₁ * actX c₂ h₂ := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  show actX (c₁ * c₂) h₃ (locMk Ω x y) = actX c₁ h₁ (actX c₂ h₂ (locMk Ω x y))
  rw [actX_mk, actX_mk, actX_mk]
  congr 1
  apply Subtype.ext
  show c₁ * c₂ * (y : G) * (c₁ * c₂)⁻¹ = c₁ * (c₂ * (y : G) * c₂⁻¹) * c₁⁻¹
  group

theorem actX_one (h : (1 : G) ∈ Subgroup.normalizer (locLayer Ω x : Set G)) :
    actX (Ω := Ω) (x := x) 1 h = 1 := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  show actX 1 h (locMk Ω x y) = locMk Ω x y
  rw [actX_mk]
  congr 1
  apply Subtype.ext
  show 1 * (y : G) * (1 : G)⁻¹ = y
  group

end Act

section Perfect

variable {X : Type} [Group X]

theorem eq_of_perfect_of_central {P : Subgroup X} (hP : P ≤ ⁅P, P⁆) (β : MulAut X)
    (h : ∀ y ∈ P, y⁻¹ * β y ∈ Subgroup.center X) : ∀ y ∈ P, β y = y := by
  have : Group.IsPerfect ↥P := perfect_of_le_commutator hP
  let φ : ↥P →* Subgroup.center X :=
    { toFun := fun y => ⟨(y : X)⁻¹ * β y, h y y.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun y₁ y₂ => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h y₁ y₁.2) (y₂ : X)⁻¹
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc (y₂ : X)⁻¹ * (y₁ : X)⁻¹ * (β y₁ * β y₂)
            = (y₂ : X)⁻¹ * ((y₁ : X)⁻¹ * β y₁) * β y₂ := by group
          _ = ((y₁ : X)⁻¹ * β y₁) * (y₂ : X)⁻¹ * β y₂ := by rw [← hc]
          _ = ((y₁ : X)⁻¹ * β y₁) * ((y₂ : X)⁻¹ * β y₂) := by group }
  have hker : commutator ↥P ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥P) ∈ commutator ↥P := by
    rw [Group.IsPerfect.commutator_eq_top]; trivial
  have h1 : φ ⟨y, hy⟩ = 1 := hker hmem
  have h2 : y⁻¹ * β y = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.mp h2).symm

end Perfect

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem subgroupOf_inf_oddCore_eq_bot (hex : ExactMembers Ω) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) :
    N.subgroupOf (locLayer Ω x) ⊓ classicalInvolutionOddCore ↥(locLayer Ω x) = ⊥ := by
  have hNY := le_centralizingLayer hN
  let e := Subgroup.subgroupOfEquivOfLe hNY
  have hO : classicalInvolutionOddCore (N.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (N.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥N := CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex N hN.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  exact inf_oddCore_eq_bot hO

theorem centralizes_of_actX_fix (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) {c : G} (hcx : c * x = x * c)
    (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x})
    (hfix : ∀ (n : G) (hn : n ∈ N), actX c hc (locMk Ω x ⟨n, le_centralizingLayer hN hn⟩) =
      locMk Ω x ⟨n, le_centralizingLayer hN hn⟩) :
    N ≤ Subgroup.centralizer ({c} : Set G) := by
  have hcx' : c * x * c⁻¹ = x := by rw [hcx]; group
  have hN' : conjSub c N ∈ centralizingMembers Ω {x} := by
    have := centralizingMembers_conj hΩ.conjInvariant c x
    rw [hcx'] at this
    rw [this]
    exact ⟨N, hN, rfl⟩
  have hmk : ∀ (n : G) (hn : n ∈ N),
      locMk Ω x ⟨c * n * c⁻¹, le_centralizingLayer hN' (conj_mem_conjSub hn)⟩ =
        locMk Ω x ⟨n, le_centralizingLayer hN hn⟩ := fun n hn => hfix n hn
  have himg : locImg Ω x (conjSub c N) = locImg Ω x N := by
    ext q
    constructor
    · rintro ⟨⟨m, hmY⟩, hm, rfl⟩
      have hm' : m ∈ conjSub c N := Subgroup.mem_subgroupOf.mp hm
      have hn : c⁻¹ * m * c ∈ N := mem_conjSub_iff.mp hm'
      have hme : m = c * (c⁻¹ * m * c) * c⁻¹ := by group
      refine ⟨⟨c⁻¹ * m * c, le_centralizingLayer hN hn⟩, Subgroup.mem_subgroupOf.mpr hn, ?_⟩
      show locMk Ω x ⟨c⁻¹ * m * c, _⟩ = locMk Ω x ⟨m, hmY⟩
      have h2 := hmk (c⁻¹ * m * c) hn
      rw [← h2]
      congr 1
      apply Subtype.ext
      exact hme.symm
    · rintro ⟨⟨n, hnY⟩, hn, rfl⟩
      have hn' : n ∈ N := Subgroup.mem_subgroupOf.mp hn
      refine ⟨⟨c * n * c⁻¹, le_centralizingLayer hN' (conj_mem_conjSub hn')⟩,
        Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub hn'), ?_⟩
      exact hmk n hn'
  have hNeq : conjSub c N = N := locImg_injOn hΩ hP1 hN' hN himg
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcn : c * n * c⁻¹ ∈ N := hNeq ▸ conj_mem_conjSub hn
  have hnY := le_centralizingLayer hN hn
  have hkernel : (⟨n⁻¹ * (c * n * c⁻¹), N.mul_mem (N.inv_mem hn) hcn |>
        fun h => le_centralizingLayer hN h⟩ : ↥(locLayer Ω x)) ∈
      N.subgroupOf (locLayer Ω x) ⊓ classicalInvolutionOddCore ↥(locLayer Ω x) := by
    refine ⟨Subgroup.mem_subgroupOf.mpr (N.mul_mem (N.inv_mem hn) hcn), ?_⟩
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show locMk Ω x ⟨n⁻¹ * (c * n * c⁻¹), _⟩ = 1
    have h2 := hmk n hn
    have e : (⟨n⁻¹ * (c * n * c⁻¹), _⟩ : ↥(locLayer Ω x)) =
        (⟨n, hnY⟩ : ↥(locLayer Ω x))⁻¹ *
          ⟨c * n * c⁻¹, le_centralizingLayer hN' (conj_mem_conjSub hn)⟩ := rfl
    rw [e, map_mul, map_inv, h2, inv_mul_cancel]
  rw [subgroupOf_inf_oddCore_eq_bot hex hN, Subgroup.mem_bot] at hkernel
  have h3 : n⁻¹ * (c * n * c⁻¹) = 1 := congrArg Subtype.val hkernel
  have h4 : c * n * c⁻¹ = n := by
    have := congrArg (fun w => n * w) h3
    simpa using this
  calc n * c = c * n * c⁻¹ * c := by rw [h4]
    _ = c * n := by group

end Members

end CFSG.ClassicalInvolution.RouteD.TWZ
