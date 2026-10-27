module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLift

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem l34CoverInvolutionFact :
    HarrisLit.L34CoverInvolutionFact := by
  intro G _ _ J x hJ hL hcard hxN hx2 hcomp
  have h16 : Nat.card (center (Jhat J)) = 16 := by
    have h1 := card_center_jhat J
    rw [hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  obtain ⟨F, hFe, hFZ, hFfix, hF16, hF8⟩ : ∃ F : Subgroup (Jhat J), IsElemTwo F ∧
      Nat.card ↥(F ⊓ center (Jhat J)) = 4 ∧ (∀ e ∈ F, betaHat J hxN e = e) ∧
      (x ∈ withKernel J → Nat.card F = 16) ∧ (x ∉ withKernel J → Nat.card F = 8) := by
    by_cases hxW : x ∈ withKernel J
    · obtain ⟨e₀, he₀⟩ := exists_inner hxW hxN
      have he₀2 : e₀ * e₀ ∈ center (Jhat J) := by
        rw [mem_center_iff]
        intro g
        have h1 := betaHat_betaHat J hxN hx2 g
        rw [he₀, he₀] at h1
        calc g * (e₀ * e₀) = (e₀ * e₀) * (e₀⁻¹ * (e₀⁻¹ * g * e₀) * e₀) := by group
          _ = (e₀ * e₀) * g := by rw [h1]
      obtain ⟨q, l, hQ, hq⟩ := exists_inner_frame hJ hL he₀2
      obtain ⟨F, hFe, hF16, hFK, hFc⟩ := hQ.exists_inner_F (by rw [hQ.ker, h16]) hq
      refine ⟨F, hFe, by rw [← hQ.ker]; exact hFK, fun e he => ?_, fun _ => hF16,
        fun h => absurd hxW h⟩
      rw [he₀, mul_assoc, ← hFc e he, ← mul_assoc, inv_mul_cancel, one_mul]
    · obtain ⟨q, hqS, hqsurj, hqker, h3, ρ, hρ, hβ⟩ :=
        exists_outer_realization hJ hL hxN hx2 hxW
      rcases hρ with rfl | rfl | rfl
      · exact absurd hcomp
          (not_isPGroup_of_field_graph hxN hx2 hqS hqsurj hqker (Or.inl rfl) hβ)
      · exact absurd hcomp
          (not_isPGroup_of_field_graph hxN hx2 hqS hqsurj hqker (Or.inr rfl) hβ)
      · obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) q hqS hqsurj
          (hqker ▸ le_refl _)
        have hU : IsUSetting q l (betaHat J hxN) := ⟨hqS, hqsurj, hqker, h3, hl, hls, hβ⟩
        have hcyc : ¬ IsCyclic q.ker := not_isCyclic_of_card (by rw [hqker, h16])
          (fun z => Subtype.ext (by
            rw [Subgroup.coe_pow, hU.pow_four_of_ker z.2]
            rfl))
        obtain ⟨hK4, hsq, -⟩ := hU.noncyclic_case hcyc
        refine ⟨fixT0 q (betaHat J hxN), ⟨fun u hu v hv => comm_of_mul_self (hsq u hu)
          (hsq v hv) (hsq _ (mul_mem hu hv)), hsq⟩, by rw [← hqker]; exact hK4,
          fun e he => he.2, fun h => absurd h hxW, fun _ => hU.card_fixT0⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : IsPGroup 2 F := fun f => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hFe.2 _ f.2)⟩
  obtain ⟨E, hEJ, θ, hθ⟩ := exists_lift_fixed hxN hx2 hF2 hFfix
  have hEe : IsElemTwo E := by
    refine ⟨fun u hu v hv => ?_, fun u hu => ?_⟩
    · have h1 := hFe.1 _ (θ ⟨u, hu⟩).2 _ (θ ⟨v, hv⟩).2
      have h2 : θ (⟨u, hu⟩ * ⟨v, hv⟩) = θ (⟨v, hv⟩ * ⟨u, hu⟩) := by
        rw [map_mul, map_mul]
        exact Subtype.ext h1
      exact congrArg Subtype.val (θ.injective h2)
    · have h1 := hFe.2 _ (θ ⟨u, hu⟩).2
      have h2 : θ (⟨u, hu⟩ * ⟨u, hu⟩) = θ 1 := by
        rw [map_mul, map_one]
        exact Subtype.ext h1
      exact congrArg Subtype.val (θ.injective h2)
  have hEcard : Nat.card E = Nat.card F := Nat.card_congr θ.toEquiv
  have hEZ : Nat.card ↥(E ⊓ zStarIn J) = Nat.card ↥(F ⊓ center (Jhat J)) := by
    have hfw : ∀ u : ↥(E ⊓ zStarIn J),
        ((θ ⟨u, (mem_inf.mp u.2).1⟩ : ↥F) : Jhat J) ∈ F ⊓ center (Jhat J) := fun u =>
      mem_inf.mpr ⟨(θ _).2, by rw [hθ]; exact (mem_zStarIn_iff _).1 (mem_inf.mp u.2).2⟩
    have hbw : ∀ f : ↥(F ⊓ center (Jhat J)),
        ((θ.symm ⟨f, (mem_inf.mp f.2).1⟩ : ↥E) : G) ∈ E ⊓ zStarIn J := fun f => by
      refine mem_inf.mpr ⟨(θ.symm _).2, ?_⟩
      have h1 := hθ (θ.symm ⟨f, (mem_inf.mp f.2).1⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [mem_zStarIn_iff (hEJ (θ.symm _).2).1, ← h1]
      exact (mem_inf.mp f.2).2
    exact Nat.card_congr
      { toFun := fun u => ⟨_, hfw u⟩
        invFun := fun f => ⟨_, hbw f⟩
        left_inv := fun u => Subtype.ext (by simp)
        right_inv := fun f => Subtype.ext (by simp) }
  exact ⟨E, hEJ, hEe, hEZ.trans hFZ, fun h => hEcard.trans (hF16 h),
    fun h => hEcard.trans (hF8 h)⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
