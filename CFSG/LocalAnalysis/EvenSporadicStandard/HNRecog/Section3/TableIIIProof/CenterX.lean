module

public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.QzBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.SmallGroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem t3_orderOf_eq_of_isConj {x y : G} (hxy : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  rw [← hg]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g) x).symm

private theorem t3_pow_two_eq_one_of_isConj {x y : G} (hy : orderOf y = 2)
    (hxy : IsConj y x) : x ^ 2 = 1 := by
  have hx : orderOf x = 2 := (t3_orderOf_eq_of_isConj hxy).symm.trans hy
  simpa [hx] using pow_orderOf_eq_one x

private theorem t3_isConj_congr_left {x y t : G} (hxy : IsConj x y) :
    (IsConj y t ↔ IsConj x t) :=
  ⟨fun h => hxy.trans h, fun h => hxy.symm.trans h⟩

theorem tableIII_mem_pCore_derived [Finite G] {a z a' t : G} (hF2 : Vert Fusion2Facts a z)
    (hX : XStruct a z a') (ha' : IsConj a a') (htQ : t ∈ Qz z) (htX : t ∈ Gxy a' z)
    (ht2 : t ^ 2 = 1) (hiff : IsConj a t ↔ ¬ IsConj a (a' * t)) :
    t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) := by
  have hF2' : Fusion2Facts a' z := hF2 a' z ha' (IsConj.refl z)
  have htGa' : t ∈ Gx a' := (mem_Gxy.mp htX).1
  have hRHS : IsConj a' t ↔ ¬ IsConj a' (a' * t) := by
    simp only [t3_isConj_congr_left ha']
    exact hiff
  have htD : t ∈ derivedOf (Gx a') := (hF2'.mem_derived_iff t htGa' ht2).mpr hRHS
  set Y : Subgroup G := Gxy a' z ⊓ derivedOf (Gx a') with hY
  have htY : t ∈ Y := by rw [hY]; exact ⟨htX, htD⟩
  have hYle : Y ≤ Gxy a' z := by rw [hY]; exact inf_le_left
  have hYgz : Y ≤ Gx z := fun y hy => (mem_Gxy.mp (hYle hy)).2
  have hYnorm : Y ≤ Subgroup.normalizer (Qz z) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact tableIII_conj_mem_Qz (hYgz hy) hq
    · intro hq
      have h := tableIII_conj_mem_Qz ((Gx z).inv_mem (hYgz hy)) hq
      convert h using 1
      group
  have hNnormal : ((Qz z).subgroupOf Y).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYnorm
  have hNpg : IsPGroup 2 ((Qz z).subgroupOf Y) := by
    rw [← Subgroup.comap_subtype (Qz z) Y]
    exact (tableIII_isPGroup_Qz z).comap_subtype
  have htNY : (⟨t, htY⟩ : ↥Y) ∈ (Qz z).subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    exact htQ
  have htNcore : (⟨t, htY⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
    have hle : (Qz z).subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
      rw [CFSG.pCore]
      exact le_sSup ⟨hNnormal, hNpg⟩
    exact hle htNY
  have htCore : t ∈ CFSG.Open.pCoreOf 2 Y := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.mem_map.mpr ⟨⟨t, htY⟩, htNcore, rfl⟩
  rw [hX.pCore_derived.2.1, ← hY]
  exact htCore

theorem tableIII_mem_pCore_2B (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hF2 : Vert Fusion2Facts a z) (hX : XStruct a z a') (ha'Q : a' ∈ Qz z)
    (ha' : IsConj a a') (hc : c ∈ tab3Set a z a' 1) :
    c ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) := by
  have hc' : c ∈ tab3Base a z a' ∧ IsConj z (a' * c) := hc
  obtain ⟨hcBase, hcz⟩ := hc'
  simp only [tab3Base, Set.mem_setOf_eq] at hcBase
  obtain ⟨hcQ, hcA, _hca', _hcaz⟩ := hcBase
  have hc2 : c ^ 2 = 1 := t3_pow_two_eq_one_of_isConj h.orderOf_a hcA
  have ha'2 : a' ^ 2 = 1 := t3_pow_two_eq_one_of_isConj h.orderOf_a ha'
  have hzc2 : (a' * c) ^ 2 = 1 := t3_pow_two_eq_one_of_isConj h.orderOf_z hcz
  have hcomm : a' * c = c * a' := comm_of_sq_mul ha'2 hc2 hzc2
  have hcX : c ∈ Gxy a' z := mem_Gxy.mpr ⟨mem_Gx.mpr hcomm, tableIII_Qz_le z hcQ⟩
  have hnot : ¬ IsConj a (a' * c) := fun hcon =>
    not_isConj_of_isF5Type hI h (hcon.trans hcz.symm)
  have hiff : IsConj a c ↔ ¬ IsConj a (a' * c) := ⟨fun _ => hnot, fun _ => hcA⟩
  exact tableIII_mem_pCore_derived hF2 hX ha' hcQ hcX hc2 hiff

theorem tableIII_not_mem_center_2B (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hF2 : Vert Fusion2Facts a z) (hX : XStruct a z a') (ha'Q : a' ∈ Qz z)
    (ha' : IsConj a a') (hc : c ∈ tab3Set a z a' 1) : c ∉ centerOf (derivedOf (Gxy a' z)) := by
  obtain ⟨ha'2, ha'1, ha'z_ne, ha'z_comm, hz2, hz1, ha'zQ, ha'zA⟩ :=
    tableIII_basic hI h ha'Q ha'
  have hc' : c ∈ tab3Base a z a' ∧ IsConj z (a' * c) := hc
  obtain ⟨hcBase, _hcz⟩ := hc'
  simp only [tab3Base, Set.mem_setOf_eq] at hcBase
  obtain ⟨_hcQ, hcA, hca', hcaz⟩ := hcBase
  have hc2 : c ^ 2 = 1 := t3_pow_two_eq_one_of_isConj h.orderOf_a hcA
  have hnotAz : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have ha'X : a' ∈ Gxy a' z := mem_Gxy.mpr ⟨self_mem_Gx a', mem_Gx.mpr ha'z_comm.symm⟩
  have hnotA1 : ¬ IsConj a (1 : G) := by
    intro hcon
    have ha1 : a = 1 := isConj_one_left.mp hcon
    have hao := h.orderOf_a
    rw [ha1, orderOf_one] at hao
    norm_num at hao
  have ha'iff : IsConj a a' ↔ ¬ IsConj a (a' * a') := by
    have hsq : a' * a' = 1 := by rw [← pow_two]; exact ha'2
    rw [hsq]
    exact ⟨fun _ => hnotA1, fun _ => ha'⟩
  have ha'core : a' ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) :=
    tableIII_mem_pCore_derived hF2 hX ha' ha'Q ha'X ha'2 ha'iff
  have ha'X' : a' ∈ derivedOf (Gxy a' z) :=
    (CFSG.openPCoreOf_le 2 (derivedOf (Gxy a' z))) ha'core
  have ha'cent : a' ∈ Subgroup.centralizer (derivedOf (Gxy a' z) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdX : d ∈ Gxy a' z := derivedOf_le (Gxy a' z) hd
    exact (mem_Gx.mp (mem_Gxy.mp hdX).1).symm
  have ha'C : a' ∈ centerOf (derivedOf (Gxy a' z)) := by
    rw [centerOf]
    exact ⟨ha'X', ha'cent⟩
  have hzQ : z ∈ Qz z := by
    have hmem : (a' * z) * a'⁻¹ ∈ Qz z := (Qz z).mul_mem ha'zQ ((Qz z).inv_mem ha'Q)
    have heq : (a' * z) * a'⁻¹ = z := by
      calc (a' * z) * a'⁻¹ = a' * z * a' := by
            rw [inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha'2)]
        _ = a' * (z * a') := by group
        _ = a' * (a' * z) := by rw [← ha'z_comm]
        _ = (a' * a') * z := by group
        _ = z := by rw [← pow_two, ha'2, one_mul]
    rwa [heq] at hmem
  have hzX : z ∈ Gxy a' z := mem_Gxy.mpr ⟨mem_Gx.mpr ha'z_comm, self_mem_Gx z⟩
  have hziff : IsConj a z ↔ ¬ IsConj a (a' * z) :=
    ⟨fun hz => absurd hz hnotAz, fun hn => absurd ha'zA hn⟩
  have hzcore : z ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) :=
    tableIII_mem_pCore_derived hF2 hX ha' hzQ hzX hz2 hziff
  have hzX' : z ∈ derivedOf (Gxy a' z) :=
    (CFSG.openPCoreOf_le 2 (derivedOf (Gxy a' z))) hzcore
  have hzcent : z ∈ Subgroup.centralizer (derivedOf (Gxy a' z) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdX : d ∈ Gxy a' z := derivedOf_le (Gxy a' z) hd
    exact (mem_Gx.mp (mem_Gxy.mp hdX).2).symm
  have hzC : z ∈ centerOf (derivedOf (Gxy a' z)) := by
    rw [centerOf]
    exact ⟨hzX', hzcent⟩
  intro hcC
  obtain ⟨e⟩ := hX.center.2
  have hcases : c = 1 ∨ c = a' ∨ c = z ∨ c = a' * z :=
    tableIII_eq_of_mulEquiv_Z2Z4 e ha'C hzC hcC ha'2 hz2 hc2 ha'1 hz1 ha'z_ne
  rcases hcases with hc1 | ha'c | hzc | hcaz'
  · have ha1 : a = 1 := isConj_one_left.mp (hc1 ▸ hcA)
    have hao := h.orderOf_a
    rw [ha1, orderOf_one] at hao
    norm_num at hao
  · exact hca' ha'c
  · exact hnotAz (hzc ▸ hcA)
  · exact hcaz hcaz'

end CFSG.EvenSporadicStandard.HNRecog.Section3
