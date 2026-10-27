module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Gen
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

theorem twistedChevalleyModel_of_lieModel {Y : Type} [Group Y] {ℓ f : ℕ}
    (hm : LieModel Y .trialityD4 0 ℓ f) : TwistedChevalleyModel Y .D4 (ℓ ^ f) := by
  rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact h.2
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)


section C0

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem d4_fieldActor_map_U (δ : K ≃+* K) :
    ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map (fieldActor σ δ).toMonoidHom =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have h := (normalActor_mem (t := TwistTag.D4) σ 1 δ).1
  rwa [normalActor_one_left] at h

omit [Finite K] in
theorem d4_U_ne_bot :
    (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≠ ⊥ := by
  intro h
  have h1 : fixedOrbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ 1 ∈
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Subgroup.mem_subgroupOf.2 (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom _ 1)
  rw [h, Subgroup.mem_bot] at h1
  exact orbitX_one_ne_one ⟨0, by decide⟩ (congrArg Subtype.val h1)

theorem d4_fieldActor_fixesInvolution_two [CharP K 2] (δ : K ≃+* K) :
    FixesInvolution (fieldActor (t := TwistTag.D4) σ δ) := by
  set a : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
  have h2 : (1 + 1 : orbitField TwistTag.D4 K σ.toRingHom a) = 0 := Subtype.ext (by
    rw [AddMemClass.coe_add, OneMemClass.coe_one, ZeroMemClass.coe_zero]
    exact CharTwo.add_self_eq_zero (1 : K))
  refine ⟨fixedOrbitX TwistTag.D4 K σ.toRingHom a 1, orderOf_eq_prime ?_ ?_, ?_⟩
  · apply Subtype.ext
    have e := congrArg Subtype.val (orbitX_add σ.toRingHom a 1 1)
    rw [h2, orbitX_zero] at e
    rw [pow_two]
    exact e.symm
  · intro h
    exact orbitX_one_ne_one a (congrArg Subtype.val h)
  · rw [fieldActor_fixedOrbitX, map_one]

theorem d4_fieldActor_fixesInvolution_odd {q : ℕ} (hq : Odd q) (hK : Nat.card K = q ^ 3)
    (hσ : ∀ c, σ c = c ^ q) (h21 : (2 : K) ≠ 0) (δ : K ≃+* K) :
    FixesInvolution (fieldActor (t := TwistTag.D4) σ δ) := by
  set u : (a : Fin TwistTag.D4.foldedTag.rank) → (orbitField TwistTag.D4 K σ.toRingHom a)ˣ :=
    fun _ => -1 with hu
  obtain ⟨t, ht⟩ := exists_conj_eq_compatDiagAutHom_D4 hq hK σ hσ u
  have hinj := mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial
    TwistTag.D4 K σ)
  have hu2 : u * u = 1 := by
    funext a
    change (-1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) * -1 = 1
    rw [neg_one_mul, neg_neg]
  refine ⟨t, orderOf_eq_prime ?_ ?_, ?_⟩
  · apply hinj
    rw [pow_two, map_mul, ht, ← map_mul, hu2, map_one, map_one]
  · intro h1
    set a0 : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
    have e := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
      φ (fixedOrbitX TwistTag.D4 K σ.toRingHom a0 1)) ht
    simp only [h1, map_one, MulAut.one_apply, compatDiagAutHom_fixedOrbitX] at e
    have e2 := congrArg (fun x : orbitField TwistTag.D4 K σ.toRingHom a0 => (x : K))
      (fixedOrbitX_injective _ e)
    have h3 : ((((-1 : (orbitField TwistTag.D4 K σ.toRingHom a0)ˣ) :
        orbitField TwistTag.D4 K σ.toRingHom a0) * 1 : orbitField TwistTag.D4 K σ.toRingHom a0) :
          K) = -1 := by
      rw [mul_one, Units.val_neg, Units.val_one, NegMemClass.coe_neg, OneMemClass.coe_one]
    have e3 : (1 : K) = -1 := e2.trans h3
    apply h21
    linear_combination e3
  · apply hinj
    have h1 := mulAut_mul_conj (fieldActor (t := TwistTag.D4) σ δ) t
    have h2 := fieldActor_mul_compatDiagAutHom (t := TwistTag.D4) σ δ u
    have hu' : orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ δ) u = u := by
      funext a
      refine Units.ext (Subtype.ext ?_)
      change δ ((((-1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) :
        orbitField TwistTag.D4 K σ.toRingHom a) : K)) = (((-1 : (orbitField TwistTag.D4 K
          σ.toRingHom a)ˣ) : orbitField TwistTag.D4 K σ.toRingHom a) : K)
      rw [Units.val_neg, Units.val_one, NegMemClass.coe_neg, OneMemClass.coe_one, map_neg,
        map_one]
    rw [ht, h2, hu', ← ht] at h1
    exact (mul_right_cancel h1).symm

theorem d4_fieldActor_fixesInvolution {ℓ f : ℕ} (hℓ : ℓ.Prime) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hf : 1 ≤ f) (δ : K ≃+* K) :
    FixesInvolution (fieldActor (t := TwistTag.D4) σ δ) := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  rcases hℓ.eq_two_or_odd' with rfl | hodd
  · exact d4_fieldActor_fixesInvolution_two σ δ
  · refine d4_fieldActor_fixesInvolution_odd σ hodd.pow hK hσ (fun h0 => ?_) δ
    have h2 : ℓ ∣ 2 := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h0)
    have h22 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
    rw [h22] at hodd
    exact absurd hodd (by decide)

end C0

theorem d4_core {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : orderOf α = p)
    (hout : α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    NormalizesPSub ℓ α ∧ FixesInvolution α := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      ∀ β g δ, β = MulAut.conj g * fieldActor σ δ → Θ β = δ := by
    rcases eq_or_ne ℓ 2 with rfl | hℓ2
    · obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
      exact ⟨Θ, hΘ⟩
    · obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ :=
        odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
      exact ⟨Θ, hΘ⟩
  obtain ⟨-, -, ⟨h, hh⟩, -⟩ := triality_noninner_large_prime_field_descent_and_local_core_trivial
    hℓ hf K hK σ hσ Θ hΘ hp hp3 ⊤ le_top ⟨α, Subgroup.mem_top α⟩ hout
    (by rw [Subgroup.orderOf_mk]; exact hα)
  refine ⟨normalizesPSub_of_conj (MulAut.conj h) ?_, fixesInvolution_of_conj (MulAut.conj h) ?_⟩
  · rw [hh]
    exact ⟨_, d4_U_ne_bot σ, isPGroup_graphFixedPosUnipotent_subgroupOf ℓ,
      d4_fieldActor_map_U σ _⟩
  · rw [hh]
    exact d4_fieldActor_fixesInvolution σ hℓ hK hσ hf _

theorem d4_ordP_noninner_of_twisted {Y : Type} [Group Y] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hm : TwistedChevalleyModel Y .D4 (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (α : MulAut Y) (hα : orderOf α = p) (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    NormalizesPSub ℓ α ∧ FixesInvolution α := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hm
  obtain ⟨h1, h2⟩ := d4_core hℓ hf K hK σ hσ hp hp3 (MulAut.congr e α)
    (by rw [orderOf_congr, hα]) (congr_not_mem_range_conj e hout)
  exact ⟨normalizesPSub_of_congr e h1, fixesInvolution_of_congr e h2⟩

theorem d4_ordP_noninner {Y : Type} [Group Y] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hm : LieModel Y .trialityD4 0 ℓ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (α : MulAut Y)
    (hα : orderOf α = p) (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    NormalizesPSub ℓ α ∧ FixesInvolution α :=
  d4_ordP_noninner_of_twisted hℓ hf (twistedChevalleyModel_of_lieModel hm) hp hp3 α hα hout

end CFSG.OddStandard.GH71.S55
