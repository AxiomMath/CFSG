module

public import CFSG.ClassicalInvolution.RouteD.NoG2D4Local

public section

namespace CFSG.ClassicalInvolution.RouteD.G2D4

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem eq_involution_of_commuting_pair [Finite G] (hSI : G2D4SharedInvolution p) (hp2 : p ≠ 2)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {i : Fin D.card}
    (ht : D.tag i = .G2 ∨ D.tag i = .trialityD4) {c b : Subgroup G} {w₀ w₁ : G}
    (hc : c ∈ Gaps.compMembers Ω x D i) (hb : b ∈ Gaps.compMembers Ω x D i)
    (hw₀ : IsClassicalMember p f c w₀) (hw₁ : IsClassicalMember p f b w₁)
    (cb : Commutes c b) : w₀ = w₁ := by
  have hinj : Function.Injective (D.hom i) :=
    injective_of_ker_le_center hp2 ht (D.rank i) (D.admissible i).2.1 (D.hom i)
      (D.ker_le_center i)
  obtain ⟨hw₀Y, hw₀m, hw₀sq, hw₀1, -⟩ := image_involution_facts hc.1 hw₀
  obtain ⟨hw₁Y, hw₁m, hw₁sq, hw₁1, hw₁c⟩ := image_involution_facts hb.1 hw₁
  have hperf : ⁅locImg Ω x b, locImg Ω x b⁆ = locImg Ω x b := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b' hb' => ?_)
      (Gaps.locImg_le_commutator hΩ hb.1)
    exact (locImg Ω x b).mul_mem ((locImg Ω x b).mul_mem ((locImg Ω x b).mul_mem ha hb')
      ((locImg Ω x b).inv_mem ha)) ((locImg Ω x b).inv_mem hb')
  have e := eq_of_central_involutions hSI hp2 ht (D.admissible i) (D.hom i) hinj hb.2 hperf
    (hc.2 hw₀m) hw₀sq hw₀1 (fun y hy => commutes_locImg_of_commutes cb _ hw₀m y hy) hw₁m hw₁1
    hw₁c
  have osq : ∀ {N : Subgroup G} {w : G}, IsClassicalMember p f N w → w * w = 1 := by
    intro N w hw
    have h2 : w ^ 2 = 1 := by rw [← hw.orderOf_eq_two]; exact pow_orderOf_eq_one w
    simpa [pow_two] using h2
  exact eq_of_mk_eq_of_involutions hP1 hw₀Y hw₁Y (osq hw₀) (osq hw₁) e.symm

end CFSG.ClassicalInvolution.RouteD.G2D4
