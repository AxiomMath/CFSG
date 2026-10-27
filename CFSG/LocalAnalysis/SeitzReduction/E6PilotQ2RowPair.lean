module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapPair
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwoExceptional
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Graph


variable {K : Type} [Field K]

theorem exists_twoSubgroup_le_centralizer_F4_of_finite [Finite K] [CharP K 2]
    {w : adjointGroup .F4 K} (hw : orderOf w = 2) :
    ∃ Q : Subgroup (adjointGroup .F4 K), Q ≤ centralizer ({w} : Set (adjointGroup .F4 K)) ∧
      IsPGroup 2 Q ∧ Nat.card Q = Nat.card K ^ 20 := by
  obtain ⟨g, hg⟩ := F4Pilot.ClassReps.exists_conj_mem_frameReps hw
  have hU := F4Pilot.u0_subgroupOf_le_centralizer_frameRep hg
  refine ⟨((F4Pilot.ClassReps.u0 K).subgroupOf (adjointGroup .F4 K)).map
      (MulAut.conj g⁻¹).toMonoidHom, ?_, F4Pilot.isPGroup_u0_subgroupOf.map _, by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      F4Pilot.natCard_u0_subgroupOf]⟩
  rintro _ ⟨x, hx, rfl⟩
  have h := mem_centralizer_singleton_iff.1 (hU hx)
  rw [mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc g⁻¹ * x * g * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [h]
    _ = w * (g⁻¹ * x * g) := by group

theorem exists_twoSubgroup_le_graphFixed_centralizer_E6_of_finite [Finite K] [CharP K 2] :
    ∃ R : Subgroup (adjointGroup TwistTag.E6.tag K), IsPGroup 2 R ∧
      Nat.card R = Nat.card K ^ 20 ∧
      (∀ x ∈ R, (x : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) ∧
      ∀ x ∈ R, x * ⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, pinnedX_mem_adjointGroup _ _⟩ =
        ⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, pinnedX_mem_adjointGroup _ _⟩ * x := by
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  set Γ := twistedFixedGroup TwistTag.E6 K (RingHom.id K) with hΓ
  have htΓ : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ Γ :=
    E6SecondGraphFixed.pinnedX_e6HighestRoot_mem_twistedFixedGroup hK2
  obtain ⟨-, -, -, -, ⟨Ψ, -⟩, -⟩ := even_E6_pure_graph_fixed_group_exact_F4 K hK2
  have hΓC : Γ ≤ adjointGroup TwistTag.E6.tag K := twistedFixedGroup_le_adjointGroup _ _ _
  have hxr : orderOf (⟨_, htΓ⟩ : Γ) = 2 := by
    rw [Subgroup.orderOf_mk,
      ← orderOf_pinnedX_one_adjointGroup (τ := TwistTag.E6.tag) (K := K) e6HighestRoot,
      Subgroup.orderOf_mk]
  have hw : orderOf (Ψ ⟨_, htΓ⟩) = 2 := by rw [MulEquiv.orderOf_eq, hxr]
  obtain ⟨R, hRw, hR, hRcard⟩ := exists_twoSubgroup_le_centralizer_F4_of_finite hw
  set ι : adjointGroup Tag.F4 K →* adjointGroup TwistTag.E6.tag K :=
    (Subgroup.inclusion hΓC).comp Ψ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (Subgroup.inclusion_injective hΓC).comp Ψ.symm.injective
  refine ⟨R.map ι, hR.map ι, by rw [card_map_of_injective hιinj, hRcard], ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (Ψ.symm x).2
  · rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 (hRw hx)
    have h1 := congrArg Ψ.symm hxw
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg (fun y : Γ => (y : ModGL TwistTag.E6.tag K)) h1
    simp only [Subgroup.coe_mul] at h2
    have hιx : ((ι x : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
        ((Ψ.symm x : Γ) : ModGL TwistTag.E6.tag K) := by
      simp [hι, Subgroup.coe_inclusion]
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hιx]
    exact h2

theorem card_pow_twenty_dvd_card_fixSubgroup_graph_E6_of_finite [Finite K] [CharP K 2]
    (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) :
    Nat.card K ^ 20 ∣ Nat.card (fixSubgroup η) ∧
      ∀ ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K,
        Nat.card K ^ 20 ∣ Nat.card (fixSubgroup
          (MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag K) * η)) := by
  obtain ⟨R, -, hRcard, hRΓ, hRt⟩ := exists_twoSubgroup_le_graphFixed_centralizer_E6_of_finite
    (K := K)
  have hRη : R ≤ fixSubgroup η := fun x hx => by
    rw [fixSubgroup_graph_eq η hη]
    exact Subgroup.mem_subgroupOf.2 (hRΓ x hx)
  refine ⟨hRcard ▸ card_dvd_of_le hRη, fun ht => hRcard ▸ card_dvd_of_le fun x hx => ?_⟩
  have hx1 : η x = x := hRη hx
  have hx2 := hRt x hx
  change (MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag K) * η) x = x
  rw [MulAut.mul_apply, hx1, MulAut.conj_apply]
  rw [← hx2, mul_inv_cancel_right]

end Graph

section Pair


variable {K : Type} [Field K]

theorem le_factorization_card_fixedSubgroup_E6_two (hK : Nat.card K = 2)
    {θ : MulAut (adjointGroup .E6 K)} (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) :
    20 ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  have hpos : Nat.card (fixedSubgroup θ) ≠ 0 := Nat.card_pos.ne'
  have key : 2 ^ 20 ∣ Nat.card (fixedSubgroup θ) := by
    by_cases hin : θ ∈ OuterAutomorphisms.inner (adjointGroup .E6 K)
    · obtain ⟨w, rfl⟩ := hin
      have hZ := center_adjointGroup_eq_bot_field .E6 K
      have hw2 : w * w = 1 := by
        have h1 : MulAut.conj (w * w) = 1 := by rw [map_mul]; exact hθ
        have hc : w * w ∈ center (adjointGroup .E6 K) := by
          rw [mem_center_iff]
          intro g
          have h2 : w * w * g * (w * w)⁻¹ = g := by
            have := congrArg (fun φ : MulAut (adjointGroup .E6 K) => φ g) h1
            simpa only [MulAut.conj_apply, MulAut.one_apply] using this
          calc g * (w * w) = w * w * g * (w * w)⁻¹ * (w * w) := by rw [h2]
            _ = w * w * g := by group
        rw [hZ, mem_bot] at hc
        exact hc
      have hw1 : w ≠ 1 := by
        rintro rfl
        exact hθ1 (map_one _)
      have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
      have hdvd := two_pow_dvd_card_centralizer_E6 hK' hwo
      change 2 ^ 20 ∣ Nat.card (fixedSubgroup (MulAut.conj w))
      rw [E8Pilot.fixedSubgroup_conj_eq_centralizer]
      exact (pow_dvd_pow 2 (by norm_num)).trans hdvd
    · have hθ2 : θ ^ 2 = 1 := by rw [sq]; exact hθ
      have hgraph : ∀ β₀ : MulAut (adjointGroup .E6 K),
          (∃ φ, φ * θ * φ⁻¹ = β₀) → Nat.card K ^ 20 ∣ Nat.card (fixSubgroup β₀) →
          2 ^ 20 ∣ Nat.card (fixedSubgroup θ) := by
        rintro β₀ ⟨φ, rfl⟩ hdvd
        have hc := card_fixSubgroup_conj φ θ
        rw [hc, hK] at hdvd
        exact hdvd
      rcases outer_involution_cases_E6 le_rfl K hK' θ hθ2 hin with
        ⟨η, hη, ⟨φ, hφ⟩ | ⟨ht', φ, hφ⟩⟩ | ⟨σ, -, hσ1, -⟩
      · exact hgraph η ⟨φ, hφ⟩ (card_pow_twenty_dvd_card_fixSubgroup_graph_E6_of_finite η hη).1
      · exact hgraph _ ⟨φ, hφ⟩
          ((card_pow_twenty_dvd_card_fixSubgroup_graph_E6_of_finite η hη).2 ht')
      · exact absurd (SeitzQ2.ringEquiv_eq_refl_of_card_eq_two hK σ) hσ1
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 key

theorem factorization_two_mul_card_mulAut_E6_two_le (hK : Nat.card K = 2) :
    (2 * Nat.card (MulAut (adjointGroup .E6 K))).factorization 2 ≤ 38 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  obtain ⟨hfin, hOut⟩ := SeitzQ2.card_outer_le_two_of_mulEquiv_E6_two hK
    (MulEquiv.refl (adjointGroup .E6 K))
  have hO0 : Nat.card (OuterAutomorphisms.Outer (adjointGroup .E6 K)) ≠ 0 := Nat.card_pos.ne'
  have hO2 : Nat.card (OuterAutomorphisms.Outer (adjointGroup .E6 K)) ∣ 2 := by
    rcases (by omega : Nat.card (OuterAutomorphisms.Outer (adjointGroup .E6 K)) = 1 ∨
      Nat.card (OuterAutomorphisms.Outer (adjointGroup .E6 K)) = 2) with h | h <;> rw [h]
    exact one_dvd 2
  have h2 := card_mulAut_dvd_card_mul_card_outer (adjointGroup .E6 K)
  have hC0 : Nat.card (adjointGroup .E6 K) ≠ 0 := Nat.card_pos.ne'
  have h4 : 2 * Nat.card (MulAut (adjointGroup .E6 K)) ∣ 4 * Nat.card (adjointGroup .E6 K) := by
    have h3 : Nat.card (MulAut (adjointGroup .E6 K)) ∣ Nat.card (adjointGroup .E6 K) * 2 :=
      h2.trans (Nat.mul_dvd_mul_left _ hO2)
    calc 2 * Nat.card (MulAut (adjointGroup .E6 K)) ∣ 2 * (Nat.card (adjointGroup .E6 K) * 2) :=
          Nat.mul_dvd_mul_left 2 h3
      _ = 4 * Nat.card (adjointGroup .E6 K) := by ring
  have hA0 : 2 * Nat.card (MulAut (adjointGroup .E6 K)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero fun h0 => ?_
    have : Finite (MulAut (adjointGroup .E6 K)) := inferInstance
    exact Nat.card_pos.ne' h0
  have h5 := (Nat.factorization_le_iff_dvd hA0 (mul_ne_zero (by norm_num) hC0)).2 h4 2
  rw [Nat.factorization_mul (by norm_num) hC0, Finsupp.add_apply,
    factorization_card_adjointGroup hK', CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E6,
    show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same] at h5
  omega

theorem swapPairExclusion_adjointGroup_E6_two (hK : Nat.card K = 2) :
    SeitzQ2.SwapPairExclusion (adjointGroup .E6 K) := by
  intro θ θ' hθ hθ1 hθ' hθ'1 h2 _
  have h1 := le_factorization_card_fixedSubgroup_E6_two hK hθ hθ1
  have h1' := le_factorization_card_fixedSubgroup_E6_two hK hθ' hθ'1
  have hA := factorization_two_mul_card_mulAut_E6_two_le hK
  omega

end Pair

end CFSG.SeitzReduction.E6Pilot
