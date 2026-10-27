module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Fusion
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5_i4m_le [Finite G] (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a) (hO : Asc82Outside)
    (tab : Asc82Tab5) {t : G} {L S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hne : g⁻¹ * t * g ≠ t)
    (hk : Kind5 L (g⁻¹ * t * g) 1) : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g := by
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [orderOf_conjugate_eq]
    exact h.involution
  have hOm : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 h.toSec3SettingLB (g⁻¹ * t * g) hsC
  obtain ⟨hcomp, -⟩ := tab.layer_i4m G L hOm (g⁻¹ * t * g) hs2 hsN hk
  have hle : layerCent L (g⁻¹ * t * g) ≤ twoPrimeRes (layerCent L (g⁻¹ * t * g)) :=
    le_twoPrimeRes_of_isQuasisimple hcomp.isQuasisimple
  have hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic ↥P :=
    fun P hP => sec5_isCyclic_of_isSylow2Of (h52a G t L h.toSec5Setting) hP
  exact hle.trans (hO.thm2L G t L h.toSec3SettingLB hcyc
    (asc82OddInnerOm6_holds G L (Or.inl hOm)) (-1) g hsC hne
    (layerCent L (g⁻¹ * t * g)) (Or.inl rfl))

private theorem sec5_i4m_J [Finite G] (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a)
    (hO : Asc82Outside) (tab : Asc82Tab5) {t : G} {L S : Subgroup G} {z : G}
    (h : Sec5Ctx G t L S z) {g : G} (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hne : g⁻¹ * t * g ≠ t) (hk : Kind5 L (g⁻¹ * t * g) 1) :
    IsComponentIn (layerCent L (g⁻¹ * t * g))
      (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) := by
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [orderOf_conjugate_eq]
    exact h.involution
  have hOm : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 h.toSec3SettingLB (g⁻¹ * t * g) hsC
  obtain ⟨hcomp, -⟩ := tab.layer_i4m G L hOm (g⁻¹ * t * g) hs2 hsN hk
  have hXLg : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g :=
    sec5_i4m_le h36 h52a hO tab h hsC hne hk
  have hXL : layerCent L (g⁻¹ * t * g) ≤ L := hcomp.le.trans inf_le_left
  have hXCt : layerCent L (g⁻¹ * t * g) ≤ centralizer ({t} : Set G) :=
    hXL.trans h.component.le
  have hXc : IsComponentIn (layerCent L (g⁻¹ * t * g))
      (centralizer ({t} : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G)) :=
    IsComponentIn.of_normal_inf_centralizer (N := centralizer ({t} : Set G)) h.component.le
      (conjugate_eq_self_of_lemma36 h36 h.toSec3SettingLB) hcomp
  refine hXc.mono (le_inf hXLg hXCt) ?_
  rintro x ⟨hxg, hxt⟩
  exact ⟨hxt, (h.toSec5Setting.conjugate g).component.le hxg⟩

theorem sec5_i4m_kind [Finite G] (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (hO : Asc82Outside)
    (tab : Asc82Tab5) {t : G} {L S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hne : g⁻¹ * t * g ≠ t)
    (hk : Kind5 L (g⁻¹ * t * g) 1) : Kind5 (CFSG.conjugate L g) t 1 := by
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [orderOf_conjugate_eq]
    exact h.involution
  have hOm : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 h.toSec3SettingLB (g⁻¹ * t * g) hsC
  obtain ⟨hcomp, hX29⟩ := tab.layer_i4m G L hOm (g⁻¹ * t * g) hs2 hsN hk
  have hJ := sec5_i4m_J h36 h52a hO tab h hsC hne hk
  have htCs : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have htN : t ∈ normalizer ((CFSG.conjugate L g) : Set G) :=
    sec4_mem_normalizer h36 (h.toSec5Setting.conjugate g).toSec3SettingLB t htCs
  refine tab.i4m_of_comp G (CFSG.conjugate L g) (isOm6Z2_conjugate hOm g) t h.involution htN
    (layerCent L (g⁻¹ * t * g)) hJ hX29 ?_
  intro u hu hu2 hpockg
  have huL : u ∈ L := (hcomp.le hu).1
  obtain ⟨hnpL, hnc⟩ := tab.i4m_inv G L hOm (g⁻¹ * t * g) hs2 hsN hk u hu hu2
  have hut : u ≠ t := by
    intro hut
    exact hnc (hut ▸ sec5_t_mem_centerIn h52b h.toSec5Setting)
  obtain ⟨a, haL, hua⟩ := sec5_nonpocket_class h52b tab h huL hu2 hut hnpL
  obtain ⟨b, hbJ, hub⟩ := sec5_pocket_class h52b tab (h.conjugate g) hpockg
  have hEq : a * (t * z) * a⁻¹ = b * (g⁻¹ * z * g) * b⁻¹ := by
    rw [← hua, hub]
  have key : (g * b⁻¹ * a)⁻¹ * z * (g * b⁻¹ * a) = t * z := by
    calc (g * b⁻¹ * a)⁻¹ * z * (g * b⁻¹ * a)
        = a⁻¹ * (b * (g⁻¹ * z * g) * b⁻¹) * a := by group
      _ = a⁻¹ * (a * (t * z) * a⁻¹) * a := by rw [hEq]
      _ = t * z := by group
  exact sec5_tz_not_conj_z h36 h37 h52b h53 tab h (g * b⁻¹ * a) key

theorem sec5_case_i4m [Finite G] (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (h54 : Asc82Lemma54)
    (hO : Asc82Outside) (tab : Asc82Tab5) {t : G} {L S : Subgroup G} {z : G}
    (h : Sec5Ctx G t L S z) {g : G} (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hne : g⁻¹ * t * g ≠ t) (hk : Kind5 L (g⁻¹ * t * g) 1) : False := by
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [orderOf_conjugate_eq]
    exact h.involution
  have hOm : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have hOm' : IsOm6Z2 (CFSG.conjugate L g) := isOm6Z2_conjugate hOm g
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 h.toSec3SettingLB (g⁻¹ * t * g) hsC
  obtain ⟨hcomp, -⟩ := tab.layer_i4m G L hOm (g⁻¹ * t * g) hs2 hsN hk
  have hJ := sec5_i4m_J h36 h52a hO tab h hsC hne hk
  obtain ⟨u, huX, hu2⟩ := exists_involution_of_isComponentIn hcomp
  have huLt : u ∈ layerCent (CFSG.conjugate L g) t := (IsComponentIn.le_layer hJ) huX
  have hk' : Kind5 (CFSG.conjugate L g) t 1 :=
    sec5_i4m_kind h36 h37 h52a h52b h53 hO tab h hsC hne hk
  have htCs : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have htN : t ∈ normalizer ((CFSG.conjugate L g) : Set G) :=
    sec4_mem_normalizer h36 (h.toSec5Setting.conjugate g).toSec3SettingLB t htCs
  have hwK : Kind5 (CFSG.conjugate L g) (t * u) 1 :=
    tab.prod_i4m G (CFSG.conjugate L g) hOm' t h.involution htN hk' u huLt hu2
  have huL : u ∈ L := (hcomp.le huX).1
  obtain ⟨hnpL, hnc⟩ := tab.i4m_inv G L hOm (g⁻¹ * t * g) hs2 hsN hk u huX hu2
  have hut : u ≠ t := by
    intro hut
    exact hnc (hut ▸ sec5_t_mem_centerIn h52b h.toSec5Setting)
  obtain ⟨a, haL, hua⟩ := sec5_nonpocket_class h52b tab h huL hu2 hut hnpL
  have ht2 : t * t = 1 := by rw [← pow_two, ← h.involution, pow_orderOf_eq_one]
  have hat : a * t = t * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.component.le haL)
  have hwa : t * u = a * z * a⁻¹ := by
    rw [hua]
    calc t * (a * (t * z) * a⁻¹)
        = (t * a) * (t * z) * a⁻¹ := by group
      _ = (a * t) * (t * z) * a⁻¹ := by rw [← hat]
      _ = a * (t * t) * z * a⁻¹ := by group
      _ = a * z * a⁻¹ := by rw [ht2]; group
  have hw2 : orderOf (t * u) = 2 := by
    rw [hwa]
    have hconj : a * z * a⁻¹ = (a⁻¹)⁻¹ * z * a⁻¹ := by group
    rw [hconj, orderOf_conjugate_eq, h.pocket.1]
  have huCs : u ∈ centralizer ({g⁻¹ * t * g} : Set G) := (hcomp.le huX).2
  have hwC : t * u ∈ centralizer ({g⁻¹ * t * g} : Set G) := mul_mem htCs huCs
  have hwN : t * u ∈ normalizer ((CFSG.conjugate L g) : Set G) :=
    sec4_mem_normalizer h36 (h.toSec5Setting.conjugate g).toSec3SettingLB (t * u) hwC
  have heq : (g⁻¹ * a⁻¹)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * a⁻¹) = t * u := by
    rw [hwa]
    group
  have hC' : (g⁻¹ * a⁻¹)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * a⁻¹) ∈
      centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [heq]
    exact hwC
  have h54res := h54 G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
    (g⁻¹ * z * g) (h.conjugate g) (g⁻¹ * a⁻¹) hC'
  rw [heq] at h54res
  rcases h54res with hcl | ⟨α, hα⟩
  · obtain ⟨b, hbJ, hwb⟩ := hcl
    have hpock : IsI4PlusIn (CFSG.conjugate L g) (t * u) := by
      rw [hwb]
      exact sec5_isI4PlusIn_conj (h.conjugate g).pocket (Subgroup.le_normalizer hbJ)
    have h0 : Kind5 (CFSG.conjugate L g) (t * u) 0 :=
      tab.pocket_kind G (CFSG.conjugate L g) hOm' (t * u) hpock
    exact (tab.excl G (CFSG.conjugate L g) hOm' (t * u) hw2 hwN 0 1
      (by norm_num) (by norm_num) (by norm_num) h0) hwK
  · have h3 : Kind5 (CFSG.conjugate L g) (t * u) 3 := ⟨α, hα⟩
    exact (tab.excl G (CFSG.conjugate L g) hOm' (t * u) hw2 hwN 3 1
      (by norm_num) (by norm_num) (by norm_num) h3) hwK

end CFSG.OddStandard.SmallF3.Omega
