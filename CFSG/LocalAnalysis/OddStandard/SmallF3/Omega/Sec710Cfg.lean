module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec710_inf_M_eq [Finite G] (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    L ⊓ MSub S B = L ⊓ normalizer (B : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxL, hxM⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
    have hBA : B ≤ ASub S B := sec79_B_le_A hc
    have hBM : B ≤ MSub S B := hBA.trans (by rw [MSub]; exact Subgroup.le_normalizer)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hBM).mp
      (h710c G t L S z g B hc).2.2) hxM
  · intro hx
    obtain ⟨hxL, hxNB⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
    have hxNt : x ∈ normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.normalizer_le_normalizer_closure {t}
        (Subgroup.centralizer_le_normalizer {t} (hc.ctx.le_centralizer hxL))
    have hxNsup : x ∈ normalizer (((Subgroup.zpowers t) ⊔ B : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup (Subgroup.zpowers t) B ⟨hxNt, hxNB⟩
    have hxNA : x ∈ normalizer (ASub S B : Set G) := by
      rw [h78 G t L S z g B hc]
      exact hxNsup
    exact hxNA

theorem sec710_wt4_mem_class [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P)
    (hF : Asc82AutFacts) (hP7 : Asc82Tab7P) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤) (i : Fin 5) :
    φ (wt4 i) ∈ conjClassIn L z := by
  have hL : IsOm6P L := hc.ctx.isOm6P
  have htype : IsI4PlusIn L (φ (wt4 i)) :=
    (hP7.aut_B_types G L hL (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16 φ hφ).2
      (wt4 i) (isEvenVec_wt4 i) (vecWeight_wt4 i)
  have hmemL : φ (wt4 i) ∈ L := hc.normalE16.1 (sec710_wt4_mem hφ i) |>.2
  have hz := sec7_z_type hF hc.ctx
  exact hP.i4_one_class G L hL z (φ (wt4 i)) hc.ctx.z_mem_L hmemL hz.1
    ((hF.pocket_P G L hL (φ (wt4 i)) hmemL).mp htype).1 hz.2
    ((hF.pocket_P G L hL (φ (wt4 i)) hmemL).mp htype).2

theorem sec710_M_perm [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (hP7 : Asc82Tab7P) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b) (h710c : Asc82Lemma710c)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    {φ : (Fin 5 → ZMod 2) → G}
    (hφ : IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤) :
    ∀ m ∈ MSub S B, ∀ i : Fin 5, ∃ j : Fin 5, m * φ (wt4 i) * m⁻¹ = φ (wt4 j) := by
  intro m hm i
  have hL : IsOm6P L := hc.ctx.isOm6P
  have hxclass : φ (wt4 i) ∈ conjClassIn L z :=
    sec710_wt4_mem_class h36 hP hF hP7 hc hφ i
  have hxIsConj : IsConj z (φ (wt4 i)) := isConj_of_mem_conjClassIn hxclass
  have hxA : φ (wt4 i) ∈ ASub S B := sec79_B_le_A hc (sec710_wt4_mem hφ i)
  have hyA : m * φ (wt4 i) * m⁻¹ ∈ ASub S B :=
    (Subgroup.mem_normalizer_iff.mp hm (φ (wt4 i))).mp hxA
  have hyIsConj : IsConj z (m * φ (wt4 i) * m⁻¹) :=
    hxIsConj.trans (isConj_iff.mpr ⟨m, rfl⟩)
  have hA_le_S : ASub S B ≤ S := by
    rw [ASub, omega1]
    exact (Subgroup.closure_le S).2 fun y hy => hy.1.1
  have hyC : m * φ (wt4 i) * m⁻¹ ∈ centralizer ({t} : Set G) :=
    (hA_le_S.trans hc.ctx.sylow.1) hyA
  have hyclass : m * φ (wt4 i) * m⁻¹ ∈ conjClassIn L z := by
    rw [← h710b G t L S z g B hc]
    exact ⟨hyIsConj, hyC⟩
  obtain ⟨h, hhL, hyh⟩ := hyclass
  have hyL : m * φ (wt4 i) * m⁻¹ ∈ L := by
    rw [hyh]
    exact L.mul_mem (L.mul_mem hhL hc.ctx.z_mem_L) (L.inv_mem hhL)
  have hI4 : IsI4PlusIn L (m * φ (wt4 i) * m⁻¹) := by
    rw [hyh]
    exact IsI4PlusIn.conj_of_mem hc.ctx.pocket hhL
  have hy2 : orderOf (m * φ (wt4 i) * m⁻¹) = 2 :=
    ((hF.pocket_P G L hL _ hyL).mp hI4).1
  have hytype : InducesTypeSome L (m * φ (wt4 i) * m⁻¹) 6 1 4 1 :=
    ((hF.pocket_P G L hL _ hyL).mp hI4).2
  have hyN : m * φ (wt4 i) * m⁻¹ ∈ normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hyB : m * φ (wt4 i) * m⁻¹ ∈ B := by
    rw [(h710c G t L S z g B hc).1]
    exact ⟨hyA, hyL⟩
  obtain ⟨v, hv, hφv⟩ := (hφ.2.2.1 _).mp hyB
  have hv0 : v ≠ 0 := by
    intro hv0
    have h1 : φ v = 1 := by rw [hv0]; exact sec710_map_zero hφ
    rw [hφv] at h1
    rw [h1, orderOf_one] at hy2
    norm_num at hy2
  have hw2 : vecWeight v ≠ 2 := by
    intro hw
    have hk1 : KindP L (m * φ (wt4 i) * m⁻¹) 1 := by
      have hh := (hP7.aut_B_types G L hL (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16
        φ hφ).1 v hv hw
      rw [hφv] at hh
      exact hh
    have hk0 : KindP L (m * φ (wt4 i) * m⁻¹) 0 := hytype
    exact (hP.excl G L hL (m * φ (wt4 i) * m⁻¹) hy2 hyN 0 1
      (by norm_num) (by norm_num) (by norm_num)) hk0 hk1
  have h4 : vecWeight v = 4 := by
    rcases sec710_weight_cases hv with h | h | h
    · exact absurd h hv0
    · exact absurd h hw2
    · exact h
  obtain ⟨j, hj⟩ := eq_wt4_of_weight_four hv h4
  exact ⟨j, by rw [← hφv, hj]⟩

end CFSG.OddStandard.SmallF3.Omega
