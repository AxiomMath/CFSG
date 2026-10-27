module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec79_Y_sylow [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    IsSylow2Of (S ⊓ centralizer (B : Set G)) (centralizer (ASub S B : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := centralizer ({t} : Set G)
  let A : Subgroup G := ASub S B
  let Y : Subgroup G := S ⊓ centralizer (B : Set G)
  let C : Subgroup G := centralizer (A : Set G)
  change IsSylow2Of Y C
  have hA : A = zpowers t ⊔ B := h78 G t L S z g B hc
  have htA : t ∈ A := by
    rw [hA]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hCH : C ≤ H := by
    change centralizer (A : Set G) ≤ centralizer ({t} : Set G)
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htA)
  have hYC : Y ≤ C := by
    intro y hy
    change y ∈ centralizer (A : Set G)
    have hyS : y ∈ S := hy.1
    have hyB : y ∈ centralizer (B : Set G) := hy.2
    have hyt : t * y = y * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.sylow.1 hyS)).symm
    have hAC : A ≤ centralizer ({y} : Set G) := by
      rw [hA]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hyt
      · intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hyB b hb)
    exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hAC ha)
  have hY2 : IsPGroup 2 Y :=
    hc.ctx.sylow.2.1.to_le (show Y ≤ S from inf_le_left)
  obtain ⟨Q, hYQ⟩ :=
    (hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYC).symm).exists_le_sylow
  let Y' : Subgroup G := (Q : Subgroup ↥C).map C.subtype
  have hY'sylow : IsSylow2Of Y' C := isSylow2Of_map_sylow Q
  have hYY' : Y ≤ Y' := by
    intro y hy
    change C.subtype ⟨y, hYC hy⟩ ∈ (Q : Subgroup ↥C).map C.subtype
    exact Subgroup.mem_map_of_mem C.subtype (hYQ (Subgroup.mem_subgroupOf.mpr hy))
  have hY'Y : Y' ≤ Y := by
    intro x hx
    change x ∈ (Q : Subgroup ↥C).map C.subtype at hx
    obtain ⟨x₀, hx₀Q, rfl⟩ := Subgroup.mem_map.mp hx
    have hx₀Y' : (x₀ : G) ∈ Y' := by
      change C.subtype x₀ ∈ (Q : Subgroup ↥C).map C.subtype
      exact Subgroup.mem_map_of_mem C.subtype hx₀Q
    have hxH : (x₀ : G) ∈ H := hCH x₀.2
    have hxB : ∀ b ∈ B, (x₀ : G) * b = b * (x₀ : G) := by
      intro b hb
      have hbA : b ∈ A := by rw [hA]; exact Subgroup.mem_sup_right hb
      exact (Subgroup.mem_centralizer_iff.mp x₀.2 b hbA).symm
    obtain ⟨s, hsS, hscL⟩ := hP.cent_B_sylow G L hc.ctx.isOm6P H S hc.ctx.le_centralizer
      (fun c hcH => hc.ctx.cent_le_normalizer h36 c hcH) hc.ctx.sylow B hc.normalE16
      (x₀ : G) hxH hxB
    have hxBc : (x₀ : G) ∈ centralizer (B : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb => (hxB b hb).symm
    have hBL : B ≤ L := le_trans hc.normalE16.1 inf_le_right
    have hcB : s⁻¹ * (x₀ : G) ∈ centralizer (B : Set G) :=
      Subgroup.centralizer_le hBL hscL
    have hsB : s ∈ centralizer (B : Set G) := by
      have heq : s = (x₀ : G) * (s⁻¹ * (x₀ : G))⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ hxBc (Subgroup.inv_mem _ hcB)
    have hsY : s ∈ Y := ⟨hsS, hsB⟩
    have hsY' : s ∈ Y' := hYY' hsY
    have hcxY' : s⁻¹ * (x₀ : G) ∈ Y' :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hsY') hx₀Y'
    have hcH : s⁻¹ * (x₀ : G) ∈ H :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hc.ctx.sylow.1 hsS)) (hCH x₀.2)
    have hzp2 : IsPGroup 2 (Subgroup.zpowers (s⁻¹ * (x₀ : G))) :=
      hY'sylow.2.1.to_le (Subgroup.zpowers_le.mpr hcxY')
    have hzpH : Subgroup.zpowers (s⁻¹ * (x₀ : G)) ≤ H :=
      Subgroup.zpowers_le.mpr hcH
    obtain ⟨d, hdH, hdconj⟩ := exists_conj_le_of_isSylow2Of hc.ctx.sylow hzp2 hzpH
    have hdcS : d * (s⁻¹ * (x₀ : G)) * d⁻¹ ∈ S :=
      hdconj (s⁻¹ * (x₀ : G)) (Subgroup.mem_zpowers _)
    have hdn : d ∈ Subgroup.normalizer (L : Set G) := hc.ctx.cent_le_normalizer h36 d hdH
    have hdcL : d * (s⁻¹ * (x₀ : G)) * d⁻¹ ∈ centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have hdl : d⁻¹ * l * d ∈ L := (Subgroup.mem_normalizer_iff''.mp hdn l).mp hl
      have hcl := Subgroup.mem_centralizer_iff.mp hscL (d⁻¹ * l * d) hdl
      calc l * (d * (s⁻¹ * (x₀ : G)) * d⁻¹)
          = d * ((d⁻¹ * l * d) * (s⁻¹ * (x₀ : G))) * d⁻¹ := by group
        _ = d * ((s⁻¹ * (x₀ : G)) * (d⁻¹ * l * d)) * d⁻¹ := by rw [hcl]
        _ = (d * (s⁻¹ * (x₀ : G)) * d⁻¹) * l := by group
    have h76' : Subgroup.zpowers t = S ⊓ centralizer (L : Set G) := h76 G t L S z hc.ctx
    have hdc_zp : d * (s⁻¹ * (x₀ : G)) * d⁻¹ ∈ Subgroup.zpowers t := by
      rw [h76']
      exact ⟨hdcS, hdcL⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdc_zp
    have hcomm : Commute t d := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hdH).symm
    have hc_tk : s⁻¹ * (x₀ : G) = t ^ k := by
      have h1 : s⁻¹ * (x₀ : G)
          = d⁻¹ * (d * (s⁻¹ * (x₀ : G)) * d⁻¹) * d := by group
      rw [← hk] at h1
      rw [h1]
      calc d⁻¹ * t ^ k * d = d⁻¹ * (t ^ k * d) := by group
        _ = d⁻¹ * (d * t ^ k) := by rw [(hcomm.zpow_left k).eq]
        _ = t ^ k := by group
    have htY : t ∈ Y := by
      refine ⟨hc.ctx.t_mem_S, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
        Subgroup.mem_centralizer_singleton_iff.mp
          (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)
    have hcY : s⁻¹ * (x₀ : G) ∈ Y :=
      Subgroup.zpowers_le.mpr htY (by rw [hc_tk]; exact Subgroup.zpow_mem_zpowers t k)
    have hx_eq : C.subtype x₀ = s * (s⁻¹ * C.subtype x₀) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem _ hsY hcY
  have hYY : Y = Y' := le_antisymm hYY' hY'Y
  simpa [hYY] using hY'sylow

end CFSG.OddStandard.SmallF3.Omega
