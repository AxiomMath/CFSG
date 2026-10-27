module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeU43
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeExtra
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBCheck
public import Certificates.Certificate25301

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Th (wordG)
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.TwoGen (img2)
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem fi24C_twoBModel :
    TwoBModel (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C) fi24Rho fi24K fi24N :=
  fi24TwoBModel fi24_twoBKCheck fi24_twoBJCheck

theorem fi24C_shapeFacts : Fi24ShapeFacts :=
  fi24ShapeCheck_facts (fi24TwoBKCheck_parts fi24_twoBKCheck).1 Certificates.certificate25301

@[expose] def fi24RhoK : ↥fi24C →* ↥fi24K :=
  fi24Rho.codRestrict fi24K fun c => by
    rw [← (fi24Rho_range_card).1]
    exact ⟨c, rfl⟩

theorem fi24RhoK_surjective : Function.Surjective fi24RhoK := by
  intro k
  have : (k : Equiv.Perm (Fin 504)) ∈ fi24Rho.range := by
    rw [(fi24Rho_range_card).1]
    exact k.2
  obtain ⟨c, hc⟩ := this
  exact ⟨c, Subtype.ext hc⟩

theorem card_ker_fi24RhoK : Nat.card fi24RhoK.ker = 2 := by
  have : fi24RhoK.ker = fi24Rho.ker := by
    ext c
    simp [MonoidHom.mem_ker, fi24RhoK]
  rw [this]
  exact (fi24Rho_range_card).2

theorem card_fi24C : Nat.card fi24C = 160526499840 := (fi24R2_centralizer_structure).1

@[expose] def fi24Psi : ↥fi24C →* Equiv.Perm (Fin 378) := fi24Phi.comp fi24RhoK

@[expose] def fi24QC : Subgroup ↥fi24C := fi24N.comap fi24Rho

theorem fi24QC_eq : fi24QC = (fi24Phi.ker).comap fi24RhoK := by
  have hK := fi24_twoBKCheck
  ext c
  show fi24Rho c ∈ fi24N ↔ fi24RhoK c ∈ fi24Phi.ker
  rw [← fi24N_subgroupOf_eq_ker hK, Subgroup.mem_subgroupOf]
  rfl

@[expose] def fi24K1 : Subgroup ↥fi24C := (fi24Kd.subgroupOf fi24K).comap fi24RhoK

@[expose] def fi24NtC : Subgroup ↥fi24C := fi24NtK.comap fi24RhoK

theorem fi24C_finite : Finite ↥fi24C :=
  Nat.finite_of_card_ne_zero (by rw [card_fi24C]; norm_num)

theorem fi24QC_normal : fi24QC.Normal := by
  refine ⟨fun q hq c => ?_⟩
  show fi24Rho (c * q * c⁻¹) ∈ fi24N
  rw [map_mul, map_mul, map_inv]
  exact fi24C_twoBModel.normal _ (fi24C_twoBModel.mem_K c) _ hq

theorem fi24RhoK_range_top : fi24RhoK.range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _ fi24RhoK_surjective

theorem card_fi24QC : Nat.card fi24QC = 2 ^ 13 := by
  rw [fi24QC_eq, card_comap_of_le_range _ _ (by rw [fi24RhoK_range_top]; exact le_top),
    card_ker_fi24RhoK, card_ker_fi24Phi fi24_twoBKCheck]
  norm_num

theorem fi24K1_index : fi24K1.index = 2 := by
  rw [fi24K1, Subgroup.index_comap_of_surjective _ fi24RhoK_surjective]
  exact fi24KdK_index (fi24TwoBKCheck_parts fi24_twoBKCheck).1

theorem fi24QC_le_NtC : fi24QC ≤ fi24NtC := by
  rw [fi24QC_eq]
  exact Subgroup.comap_mono ker_le_fi24NtK

theorem fi24NtC_le_K1 : fi24NtC ≤ fi24K1 :=
  Subgroup.comap_mono (fi24NtK_le fi24_twoBKCheck fi24C_shapeFacts)

theorem card_fi24NtC : Nat.card fi24NtC = 3 * Nat.card fi24QC := by
  rw [fi24NtC, card_comap_of_le_range _ _ (by rw [fi24RhoK_range_top]; exact le_top),
    card_ker_fi24RhoK, card_fi24NtK fi24_twoBKCheck fi24C_shapeFacts, card_fi24QC]
  norm_num

theorem fi24NtC_normal : fi24NtC.Normal :=
  haveI := fi24NtK_normal (fi24TwoBKCheck_parts fi24_twoBKCheck).1 fi24C_shapeFacts
  Subgroup.Normal.comap inferInstance _

theorem fi24QC_centralizer : Subgroup.centralizer (fi24QC : Set ↥fi24C) ≤ fi24QC := by
  intro x hx
  refine fi24C_twoBModel.faithful x fun q hq => ?_
  have h1 : ⁅x, q⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hx q hq).symm
  rw [h1]
  exact Subgroup.one_mem _

theorem fi24C_noncentral : ∀ h : ↥fi24C, h ∉ fi24K1 → ∃ n ∈ fi24NtC, ⁅h, n⁆ ∉ fi24QC := by
  intro h hh
  have hc := (fi24TwoBKCheck_parts fi24_twoBKCheck).1
  obtain ⟨cz, hcz⟩ := fi24RhoK_surjective (fi24KW fi24ShapeZ)
  refine ⟨cz, ?_, fun hq => ?_⟩
  · show fi24Phi (fi24RhoK cz) ∈ Subgroup.zpowers fi24Zeta
    rw [hcz, fi24Phi_KW]
    exact Subgroup.mem_zpowers _
  · rw [fi24QC_eq, Subgroup.mem_comap, MonoidHom.mem_ker, map_commutatorElement, hcz,
      map_commutatorElement, fi24Phi_KW, commutatorElement_eq_one_iff_mul_comm] at hq
    exact fi24Phi_not_comm hc fi24C_shapeFacts hh hq

theorem fi24K1_card : Nat.card fi24K1 = 80263249920 := by
  have h := card_comap_mul_card_of_surjective fi24RhoK fi24RhoK_surjective
    (fi24Kd.subgroupOf fi24K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (fi24Kd_le_fi24K (fi24TwoBKCheck_parts fi24_twoBKCheck).1)).toEquiv,
    card_fi24Kd (fi24TwoBKCheck_parts fi24_twoBKCheck).1, card_fi24K, card_fi24C] at h
  have h' : Nat.card fi24K1 * 80263249920 = 80263249920 * 80263249920 := by
    rw [fi24K1]
    linarith
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem fi24C_hom : ∃ π : ↥fi24K1 →* CFSG.LieType.Multipliers.U43.X₀, Function.Surjective π ∧
    π.ker = fi24NtC.subgroupOf fi24K1 := by
  have hF := fi24C_shapeFacts
  have hc := (fi24TwoBKCheck_parts fi24_twoBKCheck).1
  have := fi24C_finite
  have := fi24NtC_normal
  obtain ⟨cx, hcx⟩ := fi24RhoK_surjective (fi24KW fi24ShapeX)
  obtain ⟨cy, hcy⟩ := fi24RhoK_surjective (fi24KW fi24ShapeY)
  have hxK1 : cx ∈ fi24K1 := by
    show fi24RhoK cx ∈ fi24Kd.subgroupOf fi24K
    rw [hcx]
    exact hF.x_mem
  have hyK1 : cy ∈ fi24K1 := by
    show fi24RhoK cy ∈ fi24Kd.subgroupOf fi24K
    rw [hcy]
    exact hF.y_mem
  have hpx : fi24Psi cx = fi24PX := by
    show fi24Phi (fi24RhoK cx) = _
    rw [hcx, fi24Phi_KW]
    rfl
  have hpy : fi24Psi cy = fi24PY := by
    show fi24Phi (fi24RhoK cy) = _
    rw [hcy, fi24Phi_KW]
    rfl
  refine exists_hom_X₀ (fi24NtC.subgroupOf fi24K1) ⟨cx, hxK1⟩ ⟨cy, hyK1⟩ ?_ ?_ ?_
  · intro v hv
    rw [Subgroup.mem_subgroupOf, CFSG.Sporadic.Bridge.coe_wordProd]
    have e : (fun i => (((img2 (⟨cx, hxK1⟩ : ↥fi24K1) ⟨cy, hyK1⟩ i : ↥fi24K1)) : ↥fi24C)) =
        img2 cx cy := by
      funext i
      unfold img2
      split_ifs <;> rfl
    rw [e]
    show fi24Phi (fi24RhoK _) ∈ Subgroup.zpowers fi24Zeta
    change fi24Psi _ ∈ Subgroup.zpowers fi24Zeta
    rw [CFSG.Sporadic.Bridge.map_wordProd]
    have e2 : (fun i => fi24Psi (img2 cx cy i)) = img2 fi24PX fi24PY := by
      funext i
      unfold img2
      split_ifs
      · exact hpx
      · exact hpy
    rw [e2, mem_zpowers_fi24Zeta_iff hF]
    exact hF.rels v hv
  · intro hx
    have hx' : fi24Psi cx ∈ Subgroup.zpowers fi24Zeta := hx
    rw [hpx, mem_zpowers_fi24Zeta_iff hF] at hx'
    obtain ⟨h1, h2, h3⟩ := hF.x_not
    rcases hx' with h | h | h
    exacts [h1 h, h2 h, h3 h]
  · rw [fi24K1_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi24NtC_le_K1).toEquiv,
      card_fi24NtC, card_fi24QC]
    norm_num

theorem fi24QC_extraspecial : CFSG.IsExtraspecial 2 ↥fi24QC := by
  have hm := fi24C_twoBModel
  have := fi24C_finite
  have := fi24QC_normal
  have hz1 : (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C) ≠ 1 := fun h =>
    fi24R2_ne_one (congrArg Subtype.val h)
  have hzz : (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C) * ⟨fi24R2, fi24R2_mem_C⟩ = 1 := by
    rcases (hm.ker _).1 (by rw [map_mul, hm.rho_z, one_mul]) with h | h
    · exact h
    · exact absurd (mul_left_cancel (a := (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C))
        (by rw [mul_one]; exact h)) hz1
  have hker : ∀ c : ↥fi24C, fi24Rho c = 1 →
      c ∈ Subgroup.zpowers (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C) := fun c hc => by
    rcases (hm.ker c).1 hc with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  refine isExtraspecial_two_of_central_data fi24QC ⟨fi24R2, fi24R2_mem_C⟩ ?_ hz1 hzz
    hm.central ?_ ?_ ?_ ?_
  · show fi24Rho _ ∈ fi24N
    rw [hm.rho_z]
    exact Subgroup.one_mem _
  · intro q hq
    apply hker
    rw [map_mul]
    exact hm.sq _ hq
  · intro q hq r hr
    apply hker
    show fi24Rho ⁅q, r⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm_of_mul_self hm.sq hq hr
  · obtain ⟨q₁, q₂, h₁, h₂, hne⟩ := hm.noncomm
    exact ⟨q₁, h₁, q₂, h₂, hne⟩
  · intro M hM hinv
    exact hm.irreducible M hM fun p _ y hy => hinv p y hy

theorem fi24C_parrottData : ParrottData ↥fi24C CFSG.LieType.Multipliers.U43.X₀ fi24QC fi24NtC
    fi24K1 where
  normal_Q := fi24QC_normal
  normal_Nt := fi24NtC_normal
  card_Q := card_fi24QC
  extraspecial_Q := fi24QC_extraspecial
  centralizer_Q := fi24QC_centralizer
  index_K := fi24K1_index
  Q_le := fi24QC_le_NtC
  Nt_le := fi24NtC_le_K1
  card_Nt := card_fi24NtC
  hom := fi24C_hom
  noncentral := fi24C_noncentral

end CFSG.EvenSporadicStandard.TwoFi22.DS81
