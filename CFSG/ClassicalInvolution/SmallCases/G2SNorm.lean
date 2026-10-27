module

public import CFSG.ClassicalInvolution.SmallCases.G2SLemA2
public import CFSG.ClassicalInvolution.AschTight.S1911P3a
public import CFSG.ClassicalInvolution.AschTight.S1911P3d
public import CFSG.ClassicalInvolution.AschTight.S1911SecG
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.ClassicalInvolution.SmallCases.G2SFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)
open scoped commutatorElement

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem le_of_perfect_of_cover {P Y Z H : Subgroup G} (hPY : P ≤ Y) (hZY : Z ≤ Y)
    (hZ : ∀ z ∈ Z, ∀ g ∈ Y, z * g = g * z) (hP : P ≤ ⁅P, P⁆)
    (hcov : ∀ x ∈ P, ∃ h ∈ H, h⁻¹ * x ∈ Z) : P ≤ H := by
  refine hP.trans (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_)
  obtain ⟨h₁, hh₁, hc₁⟩ := hcov g₁ hg₁
  obtain ⟨h₂, hh₂, hc₂⟩ := hcov g₂ hg₂
  have hhY : ∀ {g h : G}, g ∈ P → h⁻¹ * g ∈ Z → h ∈ Y := fun {g h} hg hc => by
    have e : h = g * (h⁻¹ * g)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (hPY hg) (Subgroup.inv_mem _ (hZY hc))
  have e : ⁅g₁, g₂⁆ = ⁅h₁ * (h₁⁻¹ * g₁), h₂ * (h₂⁻¹ * g₂)⁆ := by
    simp only [mul_inv_cancel_left]
  rw [e, commutator_mul_of_central (H := Y) (hZY hc₂) (hhY hg₁ hc₁) (hhY hg₂ hc₂) (hZ _ hc₁)
    (hZ _ hc₂), commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem at_member {K : Subgroup G} {z : G} (C : Ctx p f (𝒞 K) K z) {M : Subgroup G}
    (hM : M ∈ 𝒞 K) {t : G} (ht : IsClassicalMember p f M t) : Ctx p f (𝒞 K) M t := by
  obtain ⟨g, rfl⟩ := hM
  have h := C.conj g
  have e : t = g * z * g⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.odd C.five ht).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.odd C.five (C.cls.conj g))
  rw [e]
  exact h

theorem oddCore_central (C : Ctx p f Ω L w) :
    ∀ z ∈ Asc77.oddCoreOf (locLayer Ω w), ∀ g ∈ locLayer Ω w, z * g = g * z := by
  intro z hz g hg
  obtain ⟨hzY, hzO⟩ := Asc77.mem_oddCoreOf_iff.mp hz
  have := Subgroup.mem_center_iff.mp (C.p1 hzO) ⟨g, hg⟩
  exact (congrArg Subtype.val this).symm

theorem mem_normalizer_layer_of_cent (C : Ctx p f Ω L w) {c : G} (hc : c * w * c⁻¹ = w) :
    c ∈ Subgroup.normalizer (layer Ω L : Set G) := by
  have h1 : conjSub c (layer Ω L) = layer Ω L := by
    rw [conjSub_layer C.inClass.conjInvariant, C.conjSub_eq_of_cent hc]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1

theorem nbhd_eq_of_cent {K : Subgroup G} {z : G} (C : Ctx p f (𝒞 K) K z) {M M' : Subgroup G}
    (hM : M ∈ nbhd (𝒞 K) K) (hM' : M' ∈ nbhd (𝒞 K) K) (hne : M ≠ M') {s : G}
    (hs : IsClassicalMember p f M' s) (hsc : ∀ x ∈ layer (𝒞 K) M, s * x = x * s) :
    nbhd (𝒞 K) M = nbhd (𝒞 K) M' := by
  have C' := C.at_member hM'.1 hs
  have hsub : nbhd (𝒞 K) M ⊆ nbhd (𝒞 K) M' := by
    intro N hN
    have hNc : N ∈ centralizingMembers (𝒞 K) {s} :=
      ⟨hN.1, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (hsc x (le_layer hN hx)).symm⟩
    rw [C'.omega_eq] at hNc
    rcases hNc with rfl | hN'
    · exact absurd hN.2.2 (C.nbhd_noncommuting hM hM' hne)
    · exact hN'
  obtain ⟨g₁, hg₁⟩ := hM.1
  obtain ⟨g₂, hg₂⟩ := hM'.1
  have hg : M' = conjSub (g₂ * g₁⁻¹) M := by
    rw [← hg₂, ← hg₁]
    show conjSub g₂ K = conjSub (g₂ * g₁⁻¹) (conjSub g₁ K)
    rw [← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hcard : (nbhd (𝒞 K) M').ncard ≤ (nbhd (𝒞 K) M).ncard := by
    refine Set.ncard_le_ncard_of_injOn (conjSub (g₂ * g₁⁻¹)⁻¹) ?_ ?_ (Set.toFinite _)
    · intro N hN
      have := nbhd_conj C.inClass.conjInvariant (g₂ * g₁⁻¹)⁻¹ hN
      rwa [hg, conjSub_inv_conjSub] at this
    · exact fun a _ b _ h => conjSub_injective _ h
  exact Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S
