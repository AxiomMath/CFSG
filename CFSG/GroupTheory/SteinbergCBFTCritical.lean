module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.CriticalDefinition

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

theorem fixingSubgroup_isPGroup (hP : IsPGroup p P) {C : Subgroup P} [C.Normal]
    (hcen : centralizer (C : Set P) ≤ C) : IsPGroup p (fixingSubgroup (MulAut P) (C : Set P)) := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  intro α
  refine ⟨k, Subtype.ext ?_⟩
  have hfix : ∀ c ∈ C, (α : MulAut P) c = c := fun c hc => α.2 ⟨c, hc⟩
  have hz : ∀ x : P, (α : MulAut P) x * x⁻¹ ∈ C := by
    intro x
    refine hcen (mem_centralizer_iff.2 fun c hc => ?_)
    have h1 : x⁻¹ * c * x ∈ C := by
      have := (inferInstance : C.Normal).conj_mem c hc x⁻¹
      simpa using this
    have h2 := hfix _ h1
    rw [map_mul, map_mul, map_inv, hfix c hc] at h2
    calc c * ((α : MulAut P) x * x⁻¹)
        = (α : MulAut P) x * ((α : MulAut P) x)⁻¹ * c * (α : MulAut P) x * x⁻¹ := by group
      _ = (α : MulAut P) x * (x⁻¹ * c * x) * x⁻¹ := by rw [← h2]; group
      _ = (α : MulAut P) x * x⁻¹ * c := by group
  have hpow : ∀ (n : ℕ) (x : P), ((α : MulAut P) ^ n) x = ((α : MulAut P) x * x⁻¹) ^ n * x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix _ (hz x), pow_succ, mul_assoc,
        inv_mul_cancel_right]
  apply MulEquiv.ext
  intro x
  rw [Subgroup.coe_pow, hpow, ← hk, pow_card_eq_one', one_mul]
  rfl

theorem ft_lemma_8_2 (hP : IsPGroup p P) :
    ∃ C : Subgroup P, C.Characteristic ∧
      (C.lowerCentralSeries 2 = ⊥ ∧ CFSG.IsElementaryAbelian p (C ⧸ center C)) ∧
      IsPGroup p (fixingSubgroup (MulAut P) (C : Set P)) ∧
      ⁅(⊤ : Subgroup P), C⁆ ≤ (center C).map C.subtype ∧
        centralizer (C : Set P) = (center C).map C.subtype := by
  obtain ⟨⟨C, hC⟩, -⟩ := thompson_critical_subgroup hP
  obtain ⟨hchar, hΦ, hcomm, hcen⟩ := (thompsonCritical_iff C).1 hC
  have : C.Characteristic := hchar
  have : C.Normal := inferInstance
  have hCp : IsPGroup p C := hP.to_subgroup C
  have hΦ' : frattini C ≤ center C := (map_le_map_iff_of_injective C.subtype_injective).1 hΦ
  have hcen' : centralizer (C : Set P) ≤ C := by
    rw [hcen]
    exact map_subtype_le _
  refine ⟨C, hchar, ⟨?_, ?_⟩, fixingSubgroup_isPGroup hP hcen', hcomm, hcen⟩
  ·
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero, eq_bot_iff, commutator_le]
    intro w hw y hy
    have hwZ : w ∈ (center C).map C.subtype := by
      refine (commutator_le.2 fun x hx z hz => ?_) hw
      exact hΦ ⟨⁅(⟨x, hx⟩ : C), ⟨z, hz⟩⁆, commutator_mem_frattini hCp _ _, rfl⟩
    obtain ⟨w', hw', rfl⟩ := hwZ
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val (mem_center_iff.1 hw' ⟨y, hy⟩)).symm
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · induction a using QuotientGroup.induction_on with | H x =>
      induction b using QuotientGroup.induction_on with | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h := hΦ' (commutator_mem_frattini hCp y⁻¹ x⁻¹)
      rw [commutatorElement_def, inv_inv, inv_inv] at h
      simpa [mul_assoc] using h
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      induction a using QuotientGroup.induction_on with | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hΦ' (pow_mem_frattini hCp x)

end CFSG.GroupTheory.FT63ChII
