module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Data
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace E6

theorem eq_of_sylow_le {G : Type*} [Group G] {S Y Q : Subgroup G}
    (hS : ∃ P : Sylow 2 ↥Y, (P : Subgroup ↥Y) = S.subgroupOf Y) (hSQ : S ≤ Q) (hQY : Q ≤ Y)
    (hQ : IsPGroup 2 Q) : Q = S := by
  obtain ⟨P, hP⟩ := hS
  have hp : IsPGroup 2 (Q.subgroupOf Y) := hQ.of_equiv (subgroupOfEquivOfLe hQY).symm
  have hle : (P : Subgroup ↥Y) ≤ Q.subgroupOf Y := by
    rw [hP]
    exact fun x hx => mem_subgroupOf.mpr (hSQ (mem_subgroupOf.mp hx))
  have heq := P.is_maximal' hp hle
  refine le_antisymm (fun q hq => ?_) hSQ
  have hq' : (⟨q, hQY hq⟩ : ↥Y) ∈ (P : Subgroup ↥Y) := by
    rw [← heq]
    exact mem_subgroupOf.mpr hq
  rw [hP] at hq'
  exact mem_subgroupOf.mp hq'

theorem exists_sylow_map {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁] (f : G₁ →* G₂)
    (R : Sylow 2 G₁) : ∃ P : Sylow 2 ↥f.range,
      (P : Subgroup ↥f.range) = ((R : Subgroup G₁).map f).subgroupOf f.range := by
  refine ⟨R.mapSurjective f.rangeRestrict_surjective, ?_⟩
  ext x
  rw [Sylow.coe_mapSurjective, mem_map, mem_subgroupOf, mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, hrx⟩
    exact ⟨r, hr, Subtype.ext hrx⟩

end E6

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

noncomputable abbrev psiW (H₁ : h.L81Hyp) : ↥h.W →* MulAut (h.K ⧸ pPrimeCore 2 h.K) :=
  (Eight.oddBarAction h.K).comp (inclusion H₁.kloc.normalizer_le_normalizer_K)

variable {H₁ : h.L81Hyp}

theorem psiW_eq_rho {m : H} (hm : m ∈ h.M3) :
    H₁.psiW ⟨m, h.toHyp52.M3_le_normalizer hm⟩ = H₁.kloc.rho ⟨m, hm⟩ := rfl

theorem psiW_mem_innA {m : H} (hm : m ∈ h.M3) :
    H₁.psiW ⟨m, h.toHyp52.M3_le_normalizer hm⟩ ∈
      Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA := by
  rw [psiW_eq_rho]
  have h1 : H₁.kloc.rho ⟨m, hm⟩ ∈ H₁.kloc.rho.range := ⟨_, rfl⟩
  rw [H₁.kloc.rho_range_eq] at h1
  exact h1

namespace Data

variable (d : Data H₁)

theorem comm_b_of_mem_W {w : H} (hw : w ∈ h.W) : w * d.b = d.b * w :=
  comm_of_mem_normalizer_zpowers d.b_ord (d.B_eq ▸ hw)

theorem mem_B_of_psiW {T : Subgroup H} (hT2 : IsPGroup 2 T) (hTW : T ≤ h.W) (hBT : h.B ≤ T)
    {t : H} (ht : t ∈ T) (h1 : H₁.psiW ⟨t, hTW ht⟩ = 1) : t ∈ h.B := by
  have hC : t ∈ coreActionKernel h.K := Eight.mem_ker_oddBarAction.mp h1
  obtain ⟨hBV, R, hR⟩ := H₁.B_sylow_kernel
  have hV := H₁.kloc.V_eq_K
  have hCV : t ∈ coreActionKernel h.V := hV ▸ hC
  have hE := E6.eq_of_sylow_le ⟨R, hR⟩ (le_inf hBT hBV) inf_le_right
    (hT2.to_le inf_le_left : IsPGroup 2 ↥(T ⊓ coreActionKernel h.V))
  rw [← hE]
  exact mem_inf.mpr ⟨ht, hCV⟩

theorem exists_T (hT₀ : ∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H)) :
    ∃ T : Sylow 2 H, (T : Subgroup H) ≤ h.W ∧ h.B ≤ T ∧ h.a ∈ (T : Subgroup H) ∧
      ∃ R : Sylow 2 ↥h.M3, (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := hT₀
  have hT₀W : (T₀ : Subgroup H) ≤ h.W := hT₀.trans (centralizer_le_normalizer _)
  have haM2 : h.aM * h.aM = 1 := Subtype.ext (Six.a_mul_a_self h.toHyp52)
  obtain ⟨R₀, hR₀a⟩ := (isPGroup_zpowers_of_mul_self haM2).exists_le_sylow
  set R₀' : Subgroup H := (R₀ : Subgroup ↥h.M3).map h.M3.subtype with hR₀'
  have hR₀'M : R₀' ≤ h.M3 := map_subtype_le _
  have hR₀'W : R₀' ≤ h.W := hR₀'M.trans h.toHyp52.M3_le_normalizer
  have hE2 : IsPGroup 2 ↥(R₀' ⊔ h.B) :=
    IsPGroup.to_sup_of_normal_right' (R₀.isPGroup'.map _) h.toHyp52.sec8_isPGroup_B hR₀'W
  have hEW : R₀' ⊔ h.B ≤ h.W := sup_le hR₀'W le_normalizer
  obtain ⟨w, hw, hwE⟩ := exists_conjugate_le_of_sylow
    ⟨T₀.subtype hT₀W, by rw [Sylow.coe_subtype]⟩ hEW hE2
  have hmem : ∀ y : H, y ∈ ((w • T₀ : Sylow 2 H) : Subgroup H) ↔ w⁻¹ * y * w ∈ T₀ := by
    intro y
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv]
    rfl
  have hET : R₀' ⊔ h.B ≤ ((w • T₀ : Sylow 2 H) : Subgroup H) := by
    intro e he
    rw [hmem]
    apply hwE
    rw [mem_conjugate_iff, show w * (w⁻¹ * e * w) * w⁻¹ = e by group]
    exact he
  refine ⟨w • T₀, fun y hy => ?_, le_sup_right.trans hET,
    hET (mem_sup_left ⟨h.aM, hR₀a (mem_zpowers _), rfl⟩), R₀, ?_⟩
  · rw [hmem] at hy
    have h1 := mul_mem (mul_mem hw (hT₀W hy)) (inv_mem hw)
    rwa [show w * (w⁻¹ * y * w) * w⁻¹ = y by group] at h1
  · have hle : (R₀ : Subgroup ↥h.M3) ≤ ((w • T₀ : Sylow 2 H) : Subgroup H).subgroupOf h.M3 :=
      fun r hr => mem_subgroupOf.mpr (hET (mem_sup_left ⟨r, hr, rfl⟩))
    exact (R₀.is_maximal' ((w • T₀).isPGroup'.comap_subtype) hle).symm

variable {d}

theorem exists_mem_T_M3 (T : Sylow 2 H) (hTW : (T : Subgroup H) ≤ h.W) (hBT : h.B ≤ T)
    (R : Sylow 2 ↥h.M3) (hR : (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3) {t : H}
    (ht : t ∈ T)
    (hψ : H₁.psiW ⟨t, hTW ht⟩ ∈ Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA) :
    ∃ r ∈ (T : Subgroup H) ⊓ h.M3, r⁻¹ * t ∈ h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA with hN
  set S : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K)) :=
    (((T : Subgroup H).subgroupOf h.W) ⊓ N.comap H₁.psiW).map H₁.psiW with hS
  have hS2 : IsPGroup 2 S :=
    ((T.isPGroup'.comap_subtype (K := h.W)).to_le inf_le_left).map _
  have hSr : S ≤ H₁.kloc.rho.range := by
    rw [H₁.kloc.rho_range_eq]
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_inf.mp hx).2
  have hRS : (R : Subgroup ↥h.M3).map H₁.kloc.rho ≤ S := by
    rintro _ ⟨r, hr, rfl⟩
    have hrT : (r : H) ∈ (T : Subgroup H) := by
      rw [hR] at hr
      exact hr
    refine ⟨⟨r, h.toHyp52.M3_le_normalizer r.2⟩, mem_inf.mpr ⟨hrT, ?_⟩, rfl⟩
    exact psiW_mem_innA r.2
  have hSeq := E6.eq_of_sylow_le (E6.exists_sylow_map H₁.kloc.rho R) hRS hSr hS2
  have htS : H₁.psiW ⟨t, hTW ht⟩ ∈ S := ⟨_, mem_inf.mpr ⟨ht, hψ⟩, rfl⟩
  rw [hSeq] at htS
  obtain ⟨r, hr, hrt⟩ := htS
  have hrT : (r : H) ∈ (T : Subgroup H) := by
    rw [hR] at hr
    exact hr
  refine ⟨r, mem_inf.mpr ⟨hrT, r.2⟩, ?_⟩
  have hrtT : (r : H)⁻¹ * t ∈ (T : Subgroup H) := mul_mem (inv_mem hrT) ht
  apply Data.mem_B_of_psiW T.isPGroup' hTW hBT hrtT
  have h1 : (⟨(r : H)⁻¹ * t, hTW hrtT⟩ : ↥h.W) =
      (⟨r, h.toHyp52.M3_le_normalizer r.2⟩ : ↥h.W)⁻¹ * ⟨t, hTW ht⟩ := rfl
  have h2 : H₁.psiW ⟨(r : H), h.toHyp52.M3_le_normalizer r.2⟩ = H₁.kloc.rho r :=
    psiW_eq_rho r.2
  rw [h1, map_mul, map_inv, h2, hrt, inv_mul_cancel]


end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
