module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaOuterA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.LeCommutator

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.exists_swapAut [Finite C] (hC : AschbacherHyp C Q) (e : C ⧸ Q ≃* A5WrTwo)
    (θ : ↥(commutator C) →* A5 × A5) (hθs : Function.Surjective θ)
    (hθb : ∀ l : ↥(commutator C), A5WrTwo.baseEmb (θ l) = e (QuotientGroup.mk (l : C)))
    {x : C} (hx : x ∉ commutator C) (hx2 : x ^ 2 = 1) :
    ∃ x₀ : A5, ∀ l : ↥(commutator C), θ (MulAut.conjNormal x l) = swapAut x₀ (θ l) := by
  classical
  let u : A5WrTwo := e (QuotientGroup.mk x)
  have hu2 : u ^ 2 = 1 := by
    have h : u = e (QuotientGroup.mk' Q x) := rfl
    rw [h, ← map_pow, show (QuotientGroup.mk' Q x : C ⧸ Q) ^ 2 =
      QuotientGroup.mk' Q (x ^ 2) from (map_pow (QuotientGroup.mk' Q) x 2).symm, hx2]
    simp
  have hu : u ∉ commutator A5WrTwo := by
    rw [← A5WrTwo.range_baseEmb]
    rintro ⟨g, hg⟩
    obtain ⟨l, hl⟩ := hθs g
    have heq : e (QuotientGroup.mk (l : C)) = e (QuotientGroup.mk x) := by
      rw [← hθb l, hl, hg]
    have hmk : (QuotientGroup.mk (l : C) : C ⧸ Q) = QuotientGroup.mk x := e.injective heq
    have hmem : (l : C)⁻¹ * x ∈ Q := QuotientGroup.eq.mp hmk
    have hxL : x ∈ commutator C := by
      have h1 : (l : C) * ((l : C)⁻¹ * x) ∈ commutator C :=
        (commutator C).mul_mem l.2 (hC.le_commutator hmem)
      simpa using h1
    exact hx hxL
  obtain ⟨x₀, hx₀⟩ := A5WrTwo.exists_conj_baseEmb hu hu2
  refine ⟨x₀, fun l => ?_⟩
  apply A5WrTwo.baseEmb_injective
  have hΦ : e (QuotientGroup.mk (x * (l : C) * x⁻¹)) = u * e (QuotientGroup.mk (l : C)) * u⁻¹ := by
    have hq : (QuotientGroup.mk (x * (l : C) * x⁻¹) : C ⧸ Q) =
        QuotientGroup.mk x * QuotientGroup.mk (l : C) * (QuotientGroup.mk x)⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hq, map_mul, map_mul, map_inv]
  have h1 : A5WrTwo.baseEmb (θ (MulAut.conjNormal x l)) =
      u * A5WrTwo.baseEmb (θ l) * u⁻¹ := by
    rw [hθb, hθb, MulAut.conjNormal_apply]
    exact hΦ
  rw [h1, swapAut_apply]
  simpa using hx₀ (θ l).1 (θ l).2

end CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz
