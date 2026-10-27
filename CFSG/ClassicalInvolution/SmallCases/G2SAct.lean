module

public import CFSG.ClassicalInvolution.Asc77.AscS24G2A
public import CFSG.ClassicalInvolution.SmallCases.G2SGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem centralizes_of_perfect {P Y Z : Subgroup G} (hPY : P ≤ Y) (hZY : Z ≤ Y)
    (hZ : ∀ z ∈ Z, ∀ g ∈ Y, z * g = g * z) (hP : P ≤ ⁅P, P⁆) {n : G}
    (hn : ∀ x ∈ P, n * x * n⁻¹ * x⁻¹ ∈ Z) : ∀ x ∈ P, n * x * n⁻¹ = x := by
  have hle : ⁅P, P⁆ ≤ Subgroup.centralizer ({n} : Set G) := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : ∀ x ∈ P, n * x * n⁻¹ = x * (n * x * n⁻¹ * x⁻¹) := fun x hx => by
      have h := hZ _ (hn x hx) x (hPY hx)
      calc n * x * n⁻¹ = (n * x * n⁻¹ * x⁻¹) * x := by group
        _ = x * (n * x * n⁻¹ * x⁻¹) := h
    have hc : n * ⁅g₁, g₂⁆ * n⁻¹ = ⁅n * g₁ * n⁻¹, n * g₂ * n⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have h1 : ⁅n * g₁ * n⁻¹, n * g₂ * n⁻¹⁆ = ⁅g₁, g₂⁆ := by
      rw [e g₁ hg₁, e g₂ hg₂]
      exact commutator_mul_of_central (H := Y) (hZY (hn g₂ hg₂)) (hPY hg₁) (hPY hg₂)
        (hZ _ (hn g₁ hg₁)) (hZ _ (hn g₂ hg₂))
    have h2 : n * ⁅g₁, g₂⁆ * n⁻¹ = ⁅g₁, g₂⁆ := hc.trans h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  intro x hx
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle (hP hx))
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem conjSub_sup (g : G) (A B : Subgroup G) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B :=
  Subgroup.map_sup _ _ _

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem layer_le_commutator (C : Ctx p f Ω L w) :
    layer Ω L ≤ ⁅layer Ω L, layer Ω L⁆ := by
  refine iSup₂_le fun N hN => ?_
  obtain ⟨u, hu⟩ := C.inClass.classical N hN.1
  have h := (commutator_eq_of_isClassicalMember hu).ge
  exact h.trans (Subgroup.commutator_mono (le_layer hN) (le_layer hN))

theorem conjSub_eq_of_cent (C : Ctx p f Ω L w) {s : G} (hs : s * w * s⁻¹ = w) :
    conjSub s L = L := by
  have h1 := C.cls.conj s
  rw [hs] at h1
  exact C.uniq _ (C.inClass.conjInvariant s L C.mem) L C.mem w h1 C.cls

theorem mem_normalizer_of_cent (C : Ctx p f Ω L w) {s : G} (hs : s * w * s⁻¹ = w) :
    s ∈ Subgroup.normalizer (locLayer Ω w : Set G) := by
  have h1 : conjSub s (centralizingLayer Ω {w}) = centralizingLayer Ω {w} := by
    rw [C.layer_eq, conjSub_sup, C.conjSub_eq_of_cent hs,
      conjSub_layer C.inClass.conjInvariant, C.conjSub_eq_of_cent hs]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1

end Ctx

@[expose] noncomputable def actQuot (Ω : Set (Subgroup G)) (w : G) (s : G)
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) : MulAut (locQuot Ω w) :=
  Asc77.S24.quotAct (locLayer Ω w) ⟨s, hs⟩

theorem actQuot_mk (Ω : Set (Subgroup G)) (w : G) {s : G}
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) (y : ↥(locLayer Ω w)) :
    actQuot Ω w s hs (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) y) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))
        ⟨s * y * s⁻¹, Asc77.S24.conj_mem_of_mem_normalizer _ hs y.2⟩ :=
  Asc77.S24.quotAct_mk (locLayer Ω w) ⟨s, hs⟩ y

theorem actQuot_sq (Ω : Set (Subgroup G)) (w : G) {s : G}
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) (hs2 : s * s = 1)
    (x : locQuot Ω w) : actQuot Ω w s hs (actQuot Ω w s hs x) = x := by
  have h1 : (⟨s, hs⟩ : ↥(Subgroup.normalizer (locLayer Ω w : Set G))) * ⟨s, hs⟩ = 1 :=
    Subtype.ext hs2
  have h2 := map_mul (Asc77.S24.quotAct (locLayer Ω w)) ⟨s, hs⟩ ⟨s, hs⟩
  rw [h1, map_one] at h2
  have h3 := DFunLike.congr_fun h2 x
  unfold actQuot
  simpa [MulAut.one_apply, MulAut.mul_apply] using h3.symm

theorem actQuot_mk_of_comm (Ω : Set (Subgroup G)) (w : G) {s : G}
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) {y : G} (hy : y ∈ locLayer Ω w)
    (hsy : s * y = y * s) :
    actQuot Ω w s hs (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨y, hy⟩) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨y, hy⟩ := by
  rw [actQuot_mk]
  congr 1
  apply Subtype.ext
  show s * y * s⁻¹ = y
  rw [mul_inv_eq_iff_eq_mul]
  exact hsy

end CFSG.ClassicalInvolution.NDB.G2S
