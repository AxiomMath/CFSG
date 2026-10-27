module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers

public section

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial

theorem eq_zero_or_eq_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hU : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hU).1
  by_cases hx : x = 0
  · exact .inl hx
  · exact .inr (congrArg Units.val (Subsingleton.elim (Units.mk0 x hx) 1))

theorem subsingleton_units_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Subsingleton Kˣ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hU : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.mp hU).1

theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) (σ : K ≃+* K) :
    σ = 1 := by
  refine RingEquiv.ext fun x => ?_
  rcases eq_zero_or_eq_one_of_card_two hK x with rfl | rfl
  · rw [map_zero]
    rfl
  · rw [map_one]
    rfl

theorem allInner_statedProjSp_of_card_two {r : ℕ} (hr : 3 ≤ r) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ g, α = MulAut.conj g := by
  have : NeZero r := ⟨by omega⟩
  have := subsingleton_units_of_card_two hK
  intro α
  obtain ⟨A, σ, rfl⟩ := (SymplecticHigher.automorphism_generation hr).2 α
  rw [ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one]
  have hA : (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    have h1 : A ∈ (SymplecticHigher.multiplier r K).ker := Subsingleton.elim _ _
    rw [SymplecticHigher.ker_multiplier] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  refine ⟨SymplecticFlag.proj r K ⟨A, hA⟩, ?_⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) x
  rw [MulAut.conj_apply, SymplecticHigher.conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem allInner_of_mulEquiv {T U : Type*} [Group T] [Group U] (e : T ≃* U)
    (h : ∀ α : MulAut U, ∃ g : U, α = MulAut.conj g) :
    ∀ α : MulAut T, ∃ g : T, α = MulAut.conj g := by
  intro α
  obtain ⟨s, hs⟩ := h ((e.symm.trans α).trans e)
  refine ⟨e.symm s, MulEquiv.ext fun t => ?_⟩
  have h1 := congrArg (fun β : MulAut U => e.symm (β (e t))) hs
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem allInner_of_lieModel_PSp_two {D : Type} [Group D] {r : ℕ} (hr : 3 ≤ r)
    (h : LieModel D .PSp r 2 1) : ∀ α : MulAut D, ∃ g : D, α = MulAut.conj g := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := F4Pilot.statedClassicalModel_of_lieModel_psp h
  exact allInner_of_mulEquiv e (allInner_statedProjSp_of_card_two hr (by rw [hK]; norm_num))

theorem exists_involution_centralizing_of_index_two {H : Type*} [Group H] {D : Subgroup H}
    (hD2 : D.index = 2) (hZ : center D = ⊥)
    (hinn : ∀ α : MulAut D, ∃ g : D, α = MulAut.conj g) :
    ∃ z : H, z ∉ D ∧ z ^ 2 = 1 ∧ ∀ d ∈ D, z * d = d * z := by
  have hN : D.Normal := Subgroup.normal_of_index_eq_two hD2
  obtain ⟨h, hh⟩ : ∃ h : H, h ∉ D := by
    by_contra hall
    push Not at hall
    have htop : D = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at hD2
    norm_num at hD2
  obtain ⟨d, hd⟩ := hinn (MulAut.conjNormal h)
  have hconj : ∀ x ∈ D, h * x * h⁻¹ = (d : H) * x * (d : H)⁻¹ := by
    intro x hx
    have h1 := congrArg (fun β : MulAut D => ((β ⟨x, hx⟩ : D) : H)) hd
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    exact h1
  obtain ⟨z, hzc, hzD⟩ : ∃ z : H, (∀ x ∈ D, z * x = x * z) ∧ z ∉ D := by
    refine ⟨(d : H)⁻¹ * h, fun x hx => ?_, fun hzD => hh ?_⟩
    · have h1 := hconj x hx
      calc (d : H)⁻¹ * h * x = (d : H)⁻¹ * (h * x * h⁻¹) * h := by group
        _ = (d : H)⁻¹ * ((d : H) * x * (d : H)⁻¹) * h := by rw [h1]
        _ = x * ((d : H)⁻¹ * h) := by group
    · have : h = (d : H) * ((d : H)⁻¹ * h) := by group
      rw [this]
      exact D.mul_mem d.2 hzD
  refine ⟨z, hzD, ?_, hzc⟩
  have hz2D : z ^ 2 ∈ D := Subgroup.sq_mem_of_index_two hD2 z
  have hcen : (⟨z ^ 2, hz2D⟩ : D) ∈ center D := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h1 := hzc g g.2
    calc (g : H) * z ^ 2 = (g * z) * z := by rw [pow_two, mul_assoc]
      _ = (z * g) * z := by rw [h1]
      _ = z * (g * z) := by group
      _ = z * (z * g) := by rw [h1]
      _ = z ^ 2 * g := by rw [pow_two, mul_assoc]
  rw [hZ, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem not_fixedCentralizerTwoFree_of_index_two {S : Type} [Group S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)} (hD2 : D.index = 2) (hZ : center D = ⊥)
    (hinn : ∀ α : MulAut D, ∃ g : D, α = MulAut.conj g) :
    ¬ F4Pilot.FixedCentralizerTwoFree σ D := by
  intro hfree
  obtain ⟨z, hzD, hz2, hzc⟩ := exists_involution_centralizing_of_index_two hD2 hZ hinn
  have hz1 : (z : S) ≠ 1 := by
    intro h
    apply hzD
    rw [show z = 1 from Subtype.ext h]
    exact D.one_mem
  have hzo : orderOf (z : S) = 2 := by
    refine orderOf_eq_prime ?_ hz1
    rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 (zpowers (z : S)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hle1 : zpowers (z : S) ≤
      centralizer ((D.map (fixedSubgroup σ).subtype : Subgroup S) : Set S) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := hzc y hy
    exact (congrArg Subtype.val this).symm
  have hle2 : zpowers (z : S) ≤ fixedSubgroup σ := by
    rw [zpowers_le]
    exact z.2
  have hbot := hfree _ hU hle1 hle2
  apply hz1
  have : (z : S) ∈ zpowers (z : S) := mem_zpowers _
  rw [hbot, mem_bot] at this
  exact this

end CFSG.SeitzReduction.SporadicRefine
