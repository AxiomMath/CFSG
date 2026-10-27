module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreSylow
import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

omit [Finite F] in
theorem forall_comm_of_mk_mem_center {K : Subgroup F} {a : F} (haK : a ∈ K)
    (h : (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : OddQuot K) ∈ Subgroup.center (OddQuot K)) :
    ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K :=
  CFSG.ClassicalInvolution.Uniform.U4.forall_comm_of_mk_mem_center haK h

theorem oddQuot_eq_one_or_eq {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    {w : OddQuot K} (hw : w * w = 1) :
    w = 1 ∨ w = (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) := by
  obtain ⟨π, z', hcov, hcen⟩ := exists_cover_of_witness hK.witness
  have hz' : (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) = z' :=
    ((hcen _).mp (mk_mem_center hK)).resolve_left (mk_ne_one hK)
  rw [hz']
  exact hcov.eq_one_or_eq_z_of_sq_eq_one hw

theorem eq_of_mk_eq {K R : Subgroup F} (hR2 : IsPGroup 2 R) {x y : F} (hxR : x ∈ R)
    (hyR : y ∈ R) (hxK : x ∈ K) (hyK : y ∈ K)
    (h : (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : OddQuot K) = QuotientGroup.mk (⟨y, hyK⟩ : ↥K)) :
    x = y := by
  rw [QuotientGroup.eq] at h
  have hmem : x⁻¹ * y ∈ oddCoreOf K :=
    mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.inv_mem hxK) hyK, h⟩
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
    (hR2.to_le (Subgroup.zpowers_le.mpr (R.mul_mem (R.inv_mem hxR) hyR)))
  exact (inv_mul_eq_one.mp h1)

theorem exists_fixed_of_inner {K R : Subgroup F} {z t u : F} (hK : IsClassical2A7 ⊤ K z)
    (hR2 : IsPGroup 2 R) (hRK : IsSylow2In (R ⊓ K) K) (htR : t ∈ R) (ht2 : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (K : Set F)) (huK : u ∈ K)
    (hact : ∀ y ∈ K, t * y * t⁻¹ * (u * y * u⁻¹)⁻¹ ∈ oddCoreOf K)
    (hnc : ¬ ∀ y ∈ K, ⁅u, y⁆ ∈ oddCoreOf K) :
    ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
  classical
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hN
  set h : OddQuot K := QuotientGroup.mk (⟨u, huK⟩ : ↥K) with hh
  have htm : ∀ y : F, y ∈ K → t * y * t⁻¹ ∈ K := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp htN y).mp hy
  have hconj : ∀ y : ↥K, (QuotientGroup.mk (⟨t * y * t⁻¹, htm y y.2⟩ : ↥K) : OddQuot K) =
      h * (QuotientGroup.mk y : OddQuot K) * h⁻¹ := by
    intro y
    obtain ⟨hm, hmo⟩ := mem_oddCoreOf_iff.mp (hact y y.2)
    rw [hh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_iff_div_mem]
    convert hmo using 1
    rw [div_eq_mul_inv]
    rfl
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hh2c : h * h ∈ Subgroup.center (OddQuot K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := hconj ⟨t * y * t⁻¹, htm y y.2⟩
    rw [hconj y] at h1
    have e : (⟨t * (t * (y : F) * t⁻¹) * t⁻¹, htm _ (htm y y.2)⟩ : ↥K) = y := by
      apply Subtype.ext
      show t * (t * (y : F) * t⁻¹) * t⁻¹ = y
      rw [hti]
      calc t * (t * (y : F) * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [ht2]; group
    rw [e] at h1
    calc (QuotientGroup.mk y : OddQuot K) * (h * h)
        = (h * (h * (QuotientGroup.mk y : OddQuot K) * h⁻¹) * h⁻¹) * (h * h) := by rw [← h1]
      _ = h * h * (QuotientGroup.mk y : OddQuot K) := by group
  have hhnc : h ∉ Subgroup.center (OddQuot K) := fun hc =>
    hnc (forall_comm_of_mk_mem_center huK hc)
  have hh2 : h * h = (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) := by
    rcases (mem_center_oddQuot_iff hK _).mp hh2c with h1 | h1
    · exfalso
      rcases oddQuot_eq_one_or_eq hK h1 with h2 | h2
      · exact hhnc (by rw [h2]; exact Subgroup.one_mem _)
      · exact hhnc (by rw [h2]; exact mk_mem_center hK)
    · exact h1
  have hzz : (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) *
      QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨z, hK.mem⟩ : ↥K) * ⟨z, hK.mem⟩ = 1 := Subtype.ext hK.mul_self
    rw [this, QuotientGroup.mk_one]
  let P₀ : Sylow 2 ↥K := AscL62.sylowOfIsSylow2In'' hRK
  let P : Sylow 2 (OddQuot K) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) P₀
  have hPcoe : (P : Subgroup (OddQuot K)) = (P₀ : Subgroup ↥K).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective _ P₀
  have hP₀ : ∀ y : ↥K, y ∈ (P₀ : Subgroup ↥K) ↔ (y : F) ∈ R := fun y =>
    ⟨fun hy => (show (y : F) ∈ R ⊓ K from hy).1, fun hy => (show (y : F) ∈ R ⊓ K from ⟨hy, y.2⟩)⟩
  have hnormP : h ∈ Subgroup.normalizer ((P : Subgroup (OddQuot K)) : Set (OddQuot K)) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have hs' : s ∈ (P : Subgroup (OddQuot K)) := hs
    rw [hPcoe] at hs'
    obtain ⟨y, hy, rfl⟩ := hs'
    have hty : t * (y : F) * t⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem htR ((hP₀ y).mp hy)) (R.inv_mem htR)
    have h1 : (QuotientGroup.mk (⟨t * y * t⁻¹, htm y y.2⟩ : ↥K) : OddQuot K) ∈
        (P : Subgroup (OddQuot K)) := by
      rw [hPcoe]
      exact ⟨_, (hP₀ _).mpr hty, rfl⟩
    rw [hconj y] at h1
    exact h1
  have hhP : h ∈ (P : Subgroup (OddQuot K)) := by
    have h2 : IsPGroup 2 (Subgroup.zpowers h) := by
      exact AscFusion.isPGroup_zpowers_of_sq_eq hzz hh2
    have hsup := IsPGroup.to_sup_of_normal_right' h2 P.isPGroup' (Subgroup.zpowers_le.mpr hnormP)
    have := P.is_maximal' hsup le_sup_right
    rw [← this]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  rw [hPcoe] at hhP
  obtain ⟨a', ha', hφa'⟩ := hhP
  have haR : (a' : F) ∈ R := (hP₀ a').mp ha'
  have hzV : z ∈ R ⊓ K := mem_of_isSylow2In (isUniqueInvolution hK) hRK
    (isQuatSub_of_isSylow2In hK hRK)
  refine ⟨(a' : F), ⟨haR, a'.2⟩, ?_, ?_⟩
  · refine eq_of_mk_eq hR2 (R.mul_mem haR haR) hzV.1 (K.mul_mem a'.2 a'.2) hK.mem ?_
    rw [← hh2, ← hφa']
    rfl
  · have h1 : t * (a' : F) * t⁻¹ = a' := by
      refine eq_of_mk_eq hR2 (R.mul_mem (R.mul_mem htR haR) (R.inv_mem htR)) haR
        (htm _ a'.2) a'.2 ?_
      rw [hconj a']
      have e : (QuotientGroup.mk a' : OddQuot K) = h := hφa'
      rw [e]
      group
    calc t * (a' : F) = (t * (a' : F) * t⁻¹) * t := by group
      _ = (a' : F) * t := by rw [h1]

end CFSG.ClassicalInvolution.A7Core
