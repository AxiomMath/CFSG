module

public import CFSG.ClassicalInvolution.SmallCases.G2SAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem mem_oddCoreOf_of_mk_eq {Ω : Set (Subgroup G)} {x : G} {u v : G} (hu : u ∈ locLayer Ω x)
    (hv : v ∈ locLayer Ω x)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv⟩) :
    u * v⁻¹ ∈ Asc77.oddCoreOf (locLayer Ω x) := by
  have h1 := QuotientGroup.eq_iff_div_mem.mp h
  have hm : u * v⁻¹ ∈ locLayer Ω x := Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hv)
  refine Asc77.mem_oddCoreOf_iff.mpr ⟨hm, ?_⟩
  have e : (⟨u * v⁻¹, hm⟩ : ↥(locLayer Ω x)) = ⟨u, hu⟩ / ⟨v, hv⟩ :=
    Subtype.ext (by simp [div_eq_mul_inv])
  rw [e]
  exact h1

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem layer_le_locLayer (C : Ctx p f Ω L w) : layer Ω L ≤ locLayer Ω w := by
  show layer Ω L ≤ centralizingLayer Ω {w}
  rw [C.layer_eq]
  exact le_sup_right

theorem lift_trivial (C : Ctx p f Ω L w) {n : G}
    (hn : ∀ x ∈ layer Ω L, n * x * n⁻¹ * x⁻¹ ∈ Asc77.oddCoreOf (locLayer Ω w)) :
    ∀ x ∈ layer Ω L, n * x = x * n := by
  have hZ : ∀ z ∈ Asc77.oddCoreOf (locLayer Ω w), ∀ g ∈ locLayer Ω w, z * g = g * z := by
    intro z hz g hg
    obtain ⟨hzY, hzO⟩ := Asc77.mem_oddCoreOf_iff.mp hz
    have := Subgroup.mem_center_iff.mp (C.p1 hzO) ⟨g, hg⟩
    exact (congrArg Subtype.val this).symm
  have hc := centralizes_of_perfect C.layer_le_locLayer (Asc77.oddCoreOf_le_self _) hZ
    C.layer_le_commutator hn
  intro x hx
  have h := hc x hx
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem mk_mem_range_of_mem_layer (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card) (hcard : D.card = 2)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) {x : G} (hx : x ∈ layer Ω L)
    (hxY : x ∈ locLayer Ω w) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨x, hxY⟩ ∈
      (D.hom i₁).range := by
  set T : Subgroup G := ((D.hom i₁).range.comap
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)))).map
      (locLayer Ω w).subtype with hT
  have hle : layer Ω L ≤ T := by
    refine iSup₂_le fun N hN x hx => ?_
    have hxY' : x ∈ locLayer Ω w :=
      le_centralizingLayer (C.nbhd_mem_centralizingMembers hN) hx
    refine ⟨⟨x, hxY'⟩, ?_, rfl⟩
    exact (C.nbhd_mem_compMembers D i₁ hcard htag hrest hN).2
      ⟨⟨x, hxY'⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hxY⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S
