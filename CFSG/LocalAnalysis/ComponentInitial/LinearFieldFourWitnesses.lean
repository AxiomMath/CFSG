module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourCover
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourConjugacy

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFour

open Subgroup Matrix LinearFlag CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

theorem pslModel_eq_range_toPGL (n p f : ℕ) [Fact p.Prime] :
    Assembly.ComponentType.pslModel n p f =
      (SpecialLinearGroup.toPGL :
        SpecialLinearGroup (Fin n) (GaloisField p f) →* ProjGenLinGroup (Fin n) _).range := by
  rw [Assembly.ComponentType.pslModel, PGLModel.projSL, PGLModel.projImage,
    SpecialLinearGroup.toPGL, MonoidHom.range_comp, SpecialLinearGroup.range_toGL_eq_ker_det]

@[expose] def pslModelEquivProjectiveSL (n p f : ℕ) [Fact p.Prime] :
    Assembly.ComponentType.pslModel n p f ≃* projectiveSL n (GaloisField p f) :=
  ((QuotientGroup.quotientMulEquivOfEq
      (by rw [SpecialLinearGroup.toPGL_ker, scalars_eq_center] :
        scalars n (GaloisField p f) = (SpecialLinearGroup.toPGL :
          SpecialLinearGroup (Fin n) (GaloisField p f) →* ProjGenLinGroup (Fin n) _).ker)).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (pslModel_eq_range_toPGL n p f).symm))).symm

theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num


theorem field_four_linear_three_full_cover_inner_involution_fixed_witnesses (A : Type) [Group A]
    [Finite A] (hA : CFSG.IsQuasisimple A)
    (hQ : Assembly.ComponentType.ClassicalModel (A ⧸ center A) .PSL 3 2 2)
    (γ : MulAut A) (hγ : orderOf γ = 2)
    (hinner : ∃ y : A ⧸ center A, PerfectAutomorphisms.centerQuotientHom A γ = MulAut.conj y) :
    ∃ t s x : A, orderOf t = 2 ∧ orderOf s = 2 ∧ t ∉ center A ∧ s ∉ center A ∧
      (∀ a : A, γ a = t * a * t⁻¹) ∧ ⁅t, s⁆ = 1 ∧ ⁅t, x⁆ = 1 ∧ ⁅s, x⁆ ≠ 1 ∧
      (t ∈ fixedSubgroup γ ∧ ∀ c ∈ fixedSubgroup γ, c * t = t * c) ∧
      (s ∈ fixedSubgroup γ ∧ ∃ c ∈ fixedSubgroup γ, c * s ≠ s * c) := by
  obtain ⟨hperf, hsimple, hnab⟩ := hA
  have : Group.IsPerfect A := hperf
  obtain ⟨-, ⟨e₀⟩⟩ := hQ
  have hK := card_galoisField_two_two
  have := charP_two_of_card_eq_four hK
  let f : A ⧸ center A ≃* projectiveSL 3 (GaloisField 2 2) :=
    e₀.trans (pslModelEquivProjectiveSL 3 2 2)
  obtain ⟨y₀, hy₀⟩ := hinner
  have hZQ : center (A ⧸ center A) = ⊥ := by
    rcases (inferInstance : (center (A ⧸ center A)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (mem_center_iff.mp (h ▸ mem_top a) b).symm hab
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    have h1 : γ = 1 := PerfectAutomorphisms.centerQuotientHom_injective A (by rw [hy₀, map_one,
      map_one])
    rw [h1, orderOf_one] at hγ
    exact absurd hγ (by norm_num)
  have hy₀2 : y₀ * y₀ = 1 := by
    have hγ2 : γ * γ = 1 := by rw [← sq, ← hγ, pow_orderOf_eq_one]
    have h : MulAut.conj (y₀ * y₀) = 1 := by rw [map_mul, ← hy₀, ← map_mul, hγ2, map_one]
    have hc : y₀ * y₀ ∈ center (A ⧸ center A) := mem_center_iff.mpr fun g => by
      have h1 := congrArg (fun φ : MulAut (A ⧸ center A) => φ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * (y₀ * y₀) = y₀ * y₀ * g * (y₀ * y₀)⁻¹ * (y₀ * y₀) := by rw [h1]
        _ = y₀ * y₀ * g := by group
    rwa [hZQ, mem_bot] at hc
  obtain ⟨g, hg⟩ := exists_conj_eq_wP_one (f y₀) (by rw [← map_mul, hy₀2, map_one])
    (fun h => hy₀1 (f.injective (h.trans (map_one f).symm)))
  let η : A →* projectiveSL 3 (GaloisField 2 2) :=
    ((MulAut.conj (proj 3 (GaloisField 2 2) g)).toMonoidHom.comp f.toMonoidHom).comp
      (QuotientGroup.mk' (center A))
  have hη_apply : ∀ a, η a =
      MulAut.conj (proj 3 (GaloisField 2 2) g) (f (QuotientGroup.mk' (center A) a)) :=
    fun a => rfl
  have hηsurj : Function.Surjective η :=
    (MulAut.conj _).surjective.comp (f.surjective.comp (QuotientGroup.mk'_surjective _))
  have hηker : ∀ z, η z = 1 ↔ z ∈ center A := fun z => by
    rw [hη_apply, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  obtain ⟨t, s, x, ht2, hs2, hηt, hηs, hts, htx, hsx⟩ :=
    exists_cover_witnesses hK η hηsurj fun z hz => (hηker z).mp hz
  have hmk : QuotientGroup.mk' (center A) t = y₀ := by
    apply f.injective
    apply (MulAut.conj (proj 3 (GaloisField 2 2) g)).injective
    rw [← hη_apply, hηt, ← hg, MulAut.conj_apply]
  have hγt : MulAut.conj t = γ := PerfectAutomorphisms.centerQuotientHom_injective A (by
    rw [OuterAutomorphisms.centerQuotient_conj, hmk, hy₀])
  have hγa : ∀ a, γ a = t * a * t⁻¹ := fun a => by rw [← hγt, MulAut.conj_apply]
  have ht1 : t ∉ center A := fun h => by
    have h' := (hηker t).mpr h
    rw [hηt, wP_eq_one_iff] at h'
    exact one_ne_zero h'
  have hs1 : s ∉ center A := fun h => hηs ((hηker s).mpr h)
  have hot : orderOf t = 2 :=
    orderOf_eq_prime (by rw [sq, ht2]) fun h => ht1 (h ▸ one_mem _)
  have hos : orderOf s = 2 :=
    orderOf_eq_prime (by rw [sq, hs2]) fun h => hs1 (h ▸ one_mem _)
  have hfix : ∀ c, c ∈ fixedSubgroup γ ↔ c * t = t * c := fun c => by
    change γ c = c ↔ _
    rw [hγa, mul_inv_eq_iff_eq_mul, eq_comm]
  refine ⟨t, s, x, hot, hos, ht1, hs1, hγa, hts, htx, hsx,
    ⟨(hfix t).mpr rfl, fun c hc => (hfix c).mp hc⟩,
    ⟨(hfix s).mpr (commutatorElement_eq_one_iff_mul_comm.mp hts).symm, x,
      (hfix x).mpr (commutatorElement_eq_one_iff_mul_comm.mp htx).symm, fun h => hsx ?_⟩⟩
  exact commutatorElement_eq_one_iff_mul_comm.mpr h.symm

end LinearFieldFour

end CFSG.LocalAnalysis.ComponentInitial
