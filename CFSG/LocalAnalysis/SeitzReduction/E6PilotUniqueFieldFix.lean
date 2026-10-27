module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueField
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)

theorem not_ordTwistedE6_dvd_ordE6 {f : ℕ} (hf : 1 ≤ f) :
    ¬ ordTwistedE6 (2 ^ f) ∣ ordE6 (2 ^ f) := by
  intro hdvd
  have hk : 0 < 18 * f := by omega
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 18 * f) (by omega)
    (by omega)
  set q := 2 ^ f with hq
  have hsub : ∀ i : ℕ, 0 < i → i < 18 → ¬ p ∣ q ^ i - 1 := by
    intro i hi0 hi
    rw [hq, ← pow_mul, hp.dvd_sub_one_iff hk]
    intro h
    have := Nat.le_of_dvd (by positivity) h
    nlinarith
  have hp2 : p ≠ 2 := hp.ne_two hk
  have hq36 : ¬ p ∣ q ^ 36 := by
    rw [hq, ← pow_mul]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).1
      (hp.prime.dvd_of_dvd_pow h))
  have hp3 : ¬ p ∣ 3 := fun h => by
    have := hp.eq_two_of_dvd_three hk h
    omega
  have h9 : p ∣ q ^ 9 + 1 := by
    rw [hq, ← pow_mul, hp.dvd_add_one_iff hk]
    refine ⟨⟨1, by ring⟩, fun h => ?_⟩
    have := Nat.le_of_dvd (by positivity) h
    omega
  set N := q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
    (q ^ 2 - 1) with hN
  set N' := q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
    (q ^ 2 - 1) with hN'
  have hE : ordE6 q ∣ N := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 (q - 1) |>.trans
    (Dvd.dvd.mul_left (Nat.sub_one_dvd_pow_sub_one q 2) _))
  have hg' : Nat.gcd 3 (q + 1) ∣ N' := (Nat.gcd_dvd_right 3 (q + 1)).trans (by
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left ?_ _) _) _) _) _
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 9))
  have h2E : ordTwistedE6 q * Nat.gcd 3 (q + 1) = N' := Nat.div_mul_cancel hg'
  have hN'3N : N' ∣ N * 3 := by
    rw [← h2E]
    exact Nat.mul_dvd_mul (hdvd.trans hE) (Nat.gcd_dvd_left 3 (q + 1))
  have hpN' : p ∣ N' := by
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left h9 _) _) _) _) _
  have hpN3 := hpN'.trans hN'3N
  rcases hp.prime.dvd_mul.1 hpN3 with h | h
  · rcases hp.prime.dvd_mul.1 h with h | h
    · rcases hp.prime.dvd_mul.1 h with h | h
      · rcases hp.prime.dvd_mul.1 h with h | h
        · rcases hp.prime.dvd_mul.1 h with h | h
          · rcases hp.prime.dvd_mul.1 h with h | h
            · rcases hp.prime.dvd_mul.1 h with h | h
              · exact hq36 h
              · exact hsub 12 (by norm_num) (by norm_num) h
            · exact hsub 9 (by norm_num) (by norm_num) h
          · exact hsub 8 (by norm_num) (by norm_num) h
        · exact hsub 6 (by norm_num) (by norm_num) h
      · exact hsub 5 (by norm_num) (by norm_num) h
    · exact hsub 2 (by norm_num) (by norm_num) h
  · exact hp3 h

theorem four_dvd_ordE6_two_pow {f : ℕ} (hf : 1 ≤ f) : 4 ∣ ordE6 (2 ^ f) := by
  obtain ⟨r, -, hr⟩ := (CFSG.Timmesfeld.Orders.profile_ordE6 hf).two
  rw [hr, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _

theorem four_dvd_ordTwistedE6_two_pow {f : ℕ} (hf : 1 ≤ f) : 4 ∣ ordTwistedE6 (2 ^ f) := by
  obtain ⟨r, -, hr⟩ := (CFSG.Timmesfeld.Orders.profile_ordTwistedE6 hf).two
  rw [hr, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _

section Conj

variable {C : Type*} [Group C]

theorem map_fixSubgroup_conj (φ α : MulAut C) :
    (fixSubgroup α).map φ.toMonoidHom = fixSubgroup (φ * α * φ⁻¹) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    change (φ * α * φ⁻¹) (φ x) = φ x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hx']
  · intro hy
    have hy' : φ (α (φ⁻¹ y)) = y := hy
    refine ⟨φ⁻¹ y, ?_, by simp⟩
    change α (φ⁻¹ y) = φ⁻¹ y
    calc α (φ⁻¹ y) = φ⁻¹ (φ (α (φ⁻¹ y))) := by simp
      _ = φ⁻¹ y := by rw [hy']

theorem card_fixSubgroup_conj (φ α : MulAut C) :
    Nat.card (fixSubgroup (φ * α * φ⁻¹)) = Nat.card (fixSubgroup α) := by
  rw [← map_fixSubgroup_conj, card_map_of_injective φ.injective]

theorem map_commutator_fixSubgroup_conj (φ α : MulAut C) :
    ⁅fixSubgroup α, fixSubgroup α⁆.map φ.toMonoidHom =
      ⁅fixSubgroup (φ * α * φ⁻¹), fixSubgroup (φ * α * φ⁻¹)⁆ := by
  rw [map_commutator, map_fixSubgroup_conj]

theorem commutator_subgroupOf_of_isSimpleGroup {G : Type*} [Group G] {J C : Subgroup G}
    (hJC : J ≤ C) (hJ : IsSimpleGroup J) (h4 : 4 ∣ Nat.card J) :
    ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := by
  have hperf := F4Pilot.commutator_eq_top_of_isSimpleGroup_of_four_dvd hJ h4
  have hJJ : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map, range_subtype]
  exact CFSG.SeitzReduction.commutator_subgroupOf_eq_self hJC hJJ

end Conj


section Graph

variable {K : Type} [Field K]

theorem fixSubgroup_graph_eq (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) :
    fixSubgroup η = (twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subgroupOf
      (adjointGroup TwistTag.E6.tag K) := by
  rw [twistedFixedGroup_subgroupOf]
  unfold fixSubgroup
  congr 1
  refine MonoidHom.ext fun g => Subtype.ext ?_
  rw [MulEquiv.coe_toMonoidHom, hη, coe_twistC, twistHom_apply]
  congr 2
  exact (Units.ext (entrywise_id _)).symm

theorem exists_twoSubgroup_le_graphFixed_centralizer_E6
    [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
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
  obtain ⟨P, R, -, hPw, hRP, hR, hRcard⟩ :=
    F4Pilot.exists_perfect_twoSubgroup_le_centralizer_F4 hq hw
  set ι : adjointGroup Tag.F4 K →* adjointGroup TwistTag.E6.tag K :=
    (Subgroup.inclusion hΓC).comp Ψ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (Subgroup.inclusion_injective hΓC).comp Ψ.symm.injective
  refine ⟨R.map ι, hR.map ι, by rw [card_map_of_injective hιinj, hRcard], ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (Ψ.symm x).2
  · rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 (hPw (hRP hx))
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

theorem card_pow_twenty_dvd_card_fixSubgroup_graph_E6 [Finite K]
    [CharP K 2] (hq : 4 ≤ Nat.card K) (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) :
    Nat.card K ^ 20 ∣ Nat.card (fixSubgroup η) ∧
      ∀ ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K,
        Nat.card K ^ 20 ∣ Nat.card (fixSubgroup
          (MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag K) * η)) := by
  obtain ⟨R, -, hRcard, hRΓ, hRt⟩ := exists_twoSubgroup_le_graphFixed_centralizer_E6 hq
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

section FieldClasses

variable {K : Type} [Field K]

theorem field_involution_facts_E6 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ (2 * f))
    (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    (∀ c, σ c = c ^ (2 ^ f)) ∧ Nat.card (fixSubfield σ) = 2 ^ f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  obtain ⟨-, -, -, -, -, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨-, hσc, hcardk⟩ := hfield 2 (2 * f) Nat.prime_two (by omega) hK σ hσ2 hσ1
  have h2f : 2 * f / 2 = f := by omega
  refine ⟨fun c => by rw [hσc, h2f], ?_⟩
  rw [← h2f, ← hcardk]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => Iff.rfl)

theorem commutator_fixSubgroup_field_E6
    {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ (2 * f))
    (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ⁅fixSubgroup (entrywiseAdjointAut TwistTag.E6.tag σ),
        fixSubgroup (entrywiseAdjointAut TwistTag.E6.tag σ)⁆ =
      (fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K) ∧
    ⁅(fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K),
        (fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K)⁆ =
      (fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K) ∧
    Nat.card ((fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K)) =
      ordE6 (2 ^ f) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  obtain ⟨hσ, hk⟩ := field_involution_facts_E6 hf hK σ hσ2 hσ1
  have := F4Pilot.finite_of_natCard_eq_two_pow hk
  obtain ⟨⟨-, hJC, hcomm, -, hsimple, -⟩, -⟩ :=
    even_E6_canonical_field_graph_field_derived_fixed_subgroups hf K hK σ hσ
  rw [pow_zero, one_mul] at hcomm
  have hJcard : Nat.card (fixedFieldImage TwistTag.E6.tag σ) = ordE6 (2 ^ f) := by
    rw [← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv]
    rw [show TwistTag.E6.tag = Tag.E6 from rfl,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6,
      hk]
  refine ⟨hcomm, commutator_subgroupOf_of_isSimpleGroup hJC hsimple
    (hJcard ▸ four_dvd_ordE6_two_pow hf), ?_⟩
  rw [card_subgroupOf_of_le hJC, hJcard]

theorem commutator_fixSubgroup_graphField_E6
    {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ (2 * f)) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ⁅fixSubgroup (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ),
        fixSubgroup (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ)⁆ =
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
        (adjointGroup TwistTag.E6.tag K) ∧
    ⁅(graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf (adjointGroup TwistTag.E6.tag K),
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
          (adjointGroup TwistTag.E6.tag K)⁆ =
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
        (adjointGroup TwistTag.E6.tag K) ∧
    Nat.card ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
        (adjointGroup TwistTag.E6.tag K)) = ordTwistedE6 (2 ^ f) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  obtain ⟨hσ, -⟩ := field_involution_facts_E6 hf hK σ hσ2 hσ1
  obtain ⟨-, ⟨-, hJC, hcomm, -, hsimple, -⟩⟩ :=
    even_E6_canonical_field_graph_field_derived_fixed_subgroups hf K hK σ hσ
  rw [pow_one] at hcomm
  have hK' : Nat.card K = (2 ^ f) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hJcard : Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ordTwistedE6 (2 ^ f) :=
    CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two hf hK' σ.toRingHom hσ
  refine ⟨hcomm, commutator_subgroupOf_of_isSimpleGroup hJC hsimple
    (hJcard ▸ four_dvd_ordTwistedE6_two_pow hf), ?_⟩
  rw [card_subgroupOf_of_le hJC, hJcard]

end FieldClasses

end CFSG.SeitzReduction.E6Pilot
