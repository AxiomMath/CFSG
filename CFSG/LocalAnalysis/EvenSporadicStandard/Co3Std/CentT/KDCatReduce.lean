module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.NFDCReduce
public import CFSG.Adapters.LieModelSimple
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.CenterQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint
open scoped commutatorElement
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Bar

variable {K : Type} [Group K]

@[expose] noncomputable def toBar (D : Subgroup K) : ↥D →* K ⧸ center K :=
  (QuotientGroup.mk' (center K)).comp D.subtype

theorem toBar_apply (D : Subgroup K) (d : ↥D) :
    toBar D d = ((d : K) : K ⧸ center K) :=
  rfl

theorem toBar_ker {D : Subgroup K} (hZD : ∀ d : ↥D, d ∈ center ↥D → (d : K) ∈ center K) :
    (toBar D).ker = center ↥D := by
  ext d
  rw [MonoidHom.mem_ker, toBar_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h ⊢
    intro g
    exact Subtype.ext (h (g : K))
  · exact hZD d

noncomputable def toBarEquiv {D : Subgroup K}
    (hZD : ∀ d : ↥D, d ∈ center ↥D → (d : K) ∈ center K) :
    ↥D ⧸ center ↥D ≃* ↥(toBar D).range :=
  (QuotientGroup.quotientMulEquivOfEq (toBar_ker hZD).symm).trans
    (QuotientGroup.quotientKerEquivRange (toBar D))

theorem lieModel_toBar_range {D : Subgroup K} {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hZD : ∀ d : ↥D, d ∈ center ↥D → (d : K) ∈ center K)
    (h : LieModel (↥D ⧸ center ↥D) t n p f) : LieModel ↥(toBar D).range t n p f :=
  LieModel.of_mulEquiv (toBarEquiv hZD) h

theorem toBar_range_le_fixed {ζ : MulAut K} {D : Subgroup K} (hD : D ≤ fixedSubgroup ζ) :
    (toBar D).range ≤ fixedSubgroup (centerQuotAut ζ) := by
  rintro _ ⟨d, rfl⟩
  have hd : ζ (d : K) = (d : K) := hD d.2
  change centerQuotAut ζ ((d : K) : K ⧸ center K) = ((d : K) : K ⧸ center K)
  rw [centerQuotAut_mk, hd]

theorem map_fixed_le (ζ : MulAut K) :
    (fixedSubgroup ζ).map (QuotientGroup.mk' (center K)) ≤ fixedSubgroup (centerQuotAut ζ) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : ζ y = y := hy
  change centerQuotAut ζ ((y : K) : K ⧸ center K) = ((y : K) : K ⧸ center K)
  rw [centerQuotAut_mk, hy']

theorem conj_mem_fixed {ζ : MulAut K} {y x : K} (hy : ζ y = y)
    (hx : centerQuotAut ζ (x : K ⧸ center K) = (x : K ⧸ center K)) :
    ζ (x * y * x⁻¹) = x * y * x⁻¹ := by
  rw [centerQuotAut_mk] at hx
  have hw : (ζ x)⁻¹ * x ∈ center K := QuotientGroup.eq.1 hx
  set w := (ζ x)⁻¹ * x with hwdef
  have hαx : ζ x = x * w⁻¹ := by rw [hwdef]; group
  have hcomm : y * w⁻¹ = w⁻¹ * y := Subgroup.mem_center_iff.1 (inv_mem hw) y
  calc ζ (x * y * x⁻¹) = ζ x * ζ y * (ζ x)⁻¹ := by simp only [map_mul, map_inv]
    _ = x * w⁻¹ * y * (x * w⁻¹)⁻¹ := by rw [hαx, hy]
    _ = x * (w⁻¹ * y * w) * x⁻¹ := by group
    _ = x * y * x⁻¹ := by rw [← hcomm]; group

theorem conj_mem_map_fixed (ζ : MulAut K) {q c : K ⧸ center K}
    (hq : q ∈ (fixedSubgroup ζ).map (QuotientGroup.mk' (center K)))
    (hc : c ∈ fixedSubgroup (centerQuotAut ζ)) :
    c * q * c⁻¹ ∈ (fixedSubgroup ζ).map (QuotientGroup.mk' (center K)) := by
  obtain ⟨y, hy, rfl⟩ := hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) c
  refine ⟨x * y * x⁻¹, ?_, by simp⟩
  exact conj_mem_fixed (ζ := ζ) hy hc

end Bar

theorem isQuasisimple_of_isSimpleGroup_nonab {X : Type} [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have : a ∈ center X := by rw [h]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.1 this b).symm)
  have hperf : Group.IsPerfect X := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have hmem : ⁅a, b⁆ ∈ commutator X := commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h] at hmem
      have h1 : ⁅a, b⁆ = 1 := Subgroup.mem_bot.1 hmem
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact Group.isPerfect_def.mpr h
  have e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

theorem exists_noncomm_of_perfect_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hQ : commutator Q = ⊤) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcon
  have h : ∀ a b : Q, a * b = b * a := fun a b => by
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  have hle : commutator Q ≤ ⊥ := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  have hxtop : x ∈ commutator Q := by rw [hQ]; exact Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.1 (hle hxtop))

variable {K : Type} [Group K] [Finite K]

theorem orderOf_centerQuotAut {ζ : MulAut K} (hK : commutator K = ⊤) (hζ : orderOf ζ = 2) :
    orderOf (centerQuotAut ζ) = 2 := by
  have h1 : ζ * ζ = 1 := by rw [← sq, ← hζ, pow_orderOf_eq_one]
  have h2 : centerQuotAut ζ * centerQuotAut ζ = 1 := by
    rw [← centerQuotAut_mul, h1, centerQuotAut_one]
  have h3 : centerQuotAut ζ ≠ 1 := by
    intro h
    have : ζ = 1 := centerQuotAut_injective hK (h.trans centerQuotAut_one.symm)
    rw [this, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  exact orderOf_eq_prime (by rw [sq]; exact h2) h3

theorem kd_reduce (hK : CFSG.Open.IsQuasisimple K) {ζ : MulAut K} (hζ : orderOf ζ = 2)
    {D : Subgroup K} (hDle : D ≤ fixedSubgroup ζ) (hDidx : D.relIndex (fixedSubgroup ζ) ≤ 2)
    (hD : IsTwoSp62 ↥D) (hZD : ∀ d : ↥D, d ∈ center ↥D → (d : K) ∈ center K) :
    orderOf (centerQuotAut ζ) = 2 ∧ (toBar D).range ≤ fixedSubgroup (centerQuotAut ζ) ∧
      CFSG.IsComponent ((toBar D).range.subgroupOf (fixedSubgroup (centerQuotAut ζ))) ∧
      LieModel ↥(toBar D).range .PSp 3 2 1 := by
  have hmodel : LieModel ↥(toBar D).range .PSp 3 2 1 := lieModel_toBar_range hZD hD.2.2
  have hle : (toBar D).range ≤ fixedSubgroup (centerQuotAut ζ) := toBar_range_le_fixed hDle
  refine ⟨orderOf_centerQuotAut hK.1 hζ, hle, ?_, hmodel⟩
  have hnorm : (D.subgroupOf (fixedSubgroup ζ)).Normal := by
    have h0 : (D.subgroupOf (fixedSubgroup ζ)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle2 : (D.subgroupOf (fixedSubgroup ζ)).index ≤ 2 := hDidx
    have : (D.subgroupOf (fixedSubgroup ζ)).index = 1 ∨
        (D.subgroupOf (fixedSubgroup ζ)).index = 2 := by omega
    rcases this with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have hDn : ∀ y ∈ fixedSubgroup ζ, ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro y hy d hd
    have := hnorm.conj_mem ⟨d, hDle hd⟩ (Subgroup.mem_subgroupOf.2 hd) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hAB : (toBar D).range ≤ (fixedSubgroup ζ).map (QuotientGroup.mk' (center K)) := by
    rintro _ ⟨d, rfl⟩
    exact ⟨(d : K), hDle d.2, rfl⟩
  have hsub : ((toBar D).range.subgroupOf (fixedSubgroup (centerQuotAut ζ))).IsSubnormal := by
    refine CFSG.ComponentClassification.CatFC.nfdc_isSubnormal_subgroupOf hAB (map_fixed_le ζ)
      ?_ fun q c hq hc => conj_mem_map_fixed ζ hq hc
    rintro a q ⟨d, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨⟨y * (d : K) * y⁻¹, hDn y hy d d.2⟩, ?_⟩
    simp [toBar_apply]
  have hsimple : IsSimpleGroup ↥(toBar D).range :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmodel
  have e : ↥((toBar D).range.subgroupOf (fixedSubgroup (centerQuotAut ζ))) ≃* ↥(toBar D).range :=
    Subgroup.subgroupOfEquivOfLe hle
  haveI : IsSimpleGroup ↥((toBar D).range.subgroupOf (fixedSubgroup (centerQuotAut ζ))) :=
    MulEquiv.isSimpleGroup e
  haveI : Group.IsPerfect ↥D := Group.isPerfect_def.mpr hD.1
  haveI : Group.IsPerfect ↥(toBar D).range :=
    Group.IsPerfect.ofSurjective (f := (toBar D).rangeRestrict) (toBar D).rangeRestrict_surjective
  have hna : ∃ a b : ↥(toBar D).range, a * b ≠ b * a :=
    exists_noncomm_of_perfect_simple Group.IsPerfect.commutator_eq_top
  have hnaD : ∃ a b : ↥((toBar D).range.subgroupOf (fixedSubgroup (centerQuotAut ζ))),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  exact ⟨isQuasisimple_of_isSimpleGroup_nonab hnaD, hsub⟩

end CFSG.EvenSporadicStandard.Co3Std.CentT
