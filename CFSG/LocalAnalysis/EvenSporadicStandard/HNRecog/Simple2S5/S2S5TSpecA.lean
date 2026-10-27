module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog

theorem tmuOne_spec {k : Nat} (h : tmuOne k = true) : TFacts k := by
  unfold tmuOne at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hb6⟩, hb7⟩, hb8⟩, hb9⟩, hb10⟩,
    hb11⟩, hb12⟩, hb13⟩, hb14⟩, hb15⟩ := h
  rw [Bool.not_eq_true'] at hb12 hb14 hb15
  have hwordAZ : elemW wordAZ = elemA * elemZ := by
    simp only [elemW, elemA, elemZ, wordAZ, TwoHS.wordVal, List.map_append, List.prod_append]
  have hg : gensOK = true := (enumW_gens_words hb5).1
  have hrep_t0 : Rep 1408 (tabW wordAZ) (elemA * elemZ) := by
    rw [← hwordAZ]
    exact rep_elemW_of_gensOK hg hb1
  have hrep_u : Rep 1408 (tabW (uWord k)) (uElt k) := rep_elemW_of_gensOK hg hb4
  have hrep_y0 : Rep 1408 (tabW (yWord k 0)) (yOne k) := rep_elemW_of_gensOK hg hb2
  have hrep_y1 : Rep 1408 (tabW (yWord k 1)) (yTwo k) := rep_elemW_of_gensOK hg hb3
  have hTl : IsEnumSet 1408 (subgroupList 1000 (tWords k)) (tSub k : Set _) := by
    simpa only [tSub, wSub] using (enumW_spec hb5).2
  have hMl : IsEnumSet 1408 (subgroupList 1000 (mWords k)) (mSub k : Set _) := by
    simpa only [mSub, wSub] using (enumW_spec hb6).2
  have hcardT : Nat.card ↥(tSub k) = 16 := by
    simpa only [tSub, wSub] using (enumW_spec hb5).1
  have hcardM : Nat.card ↥(mSub k) = 8 := by
    simpa only [mSub, wSub] using (enumW_spec hb6).1
  have hMle : mSub k ≤ tSub k := by
    rw [mSub, wSub, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hwok : wordOK w = true := List.all_eq_true.1 (enumW_gens_words hb6).2 w hw
    have hrepw : Rep 1408 (tabW w) (elemW w) := rep_elemW_of_gensOK hg hwok
    have hmem : memT 1408 (subgroupList 1000 (tWords k)) (tabW w) = true :=
      List.all_eq_true.1 hb9 (tabW w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    exact (hTl.memT_iff hrepw).1 hmem
  refine
    { card_T := hcardT
      t₀_mem := (hTl.memT_iff hrep_t0).1 hb7
      cen := ?_
      M_le := hMle
      relIndex_M := ?_
      inv_M := ?_
      u_mem := (hTl.memT_iff hrep_u).1 hb11
      u_not_M := notMem_of_memT_false hMl hrep_u hb12
      u_ord := orderOf_eq_two_of_involOK (by norm_num) hrep_u hb13
      u_ne := ne_of_tblEq_false hrep_u hrep_t0 hb14
      nonab := ?_ }
  · intro x hx hxcomm
    obtain ⟨i, hi, hrep_i⟩ := hTl.cov x hx
    let xt := (subgroupList 1000 (tWords k))[i]!
    have hmem_xt : xt ∈ subgroupList 1000 (tWords k) := getElem!_mem_array hi
    have hxi : (tblEq 1408 xt (idT 1408) || tblEq 1408 xt (tabW wordAZ) ||
        !((tabsW (tWords k)).all (commTT 1408 xt))) = true :=
      (Array.all_eq_true'.1 hb8) xt hmem_xt
    rw [Bool.or_eq_true, Bool.or_eq_true] at hxi
    rcases hxi with (h1 | h2) | h3
    · left
      exact (tblEq_idT_iff (by norm_num) hrep_i).1 h1
    · right
      exact (tblEq_iff_eq hrep_i hrep_t0).1 h2
    · exfalso
      rw [Bool.not_eq_true'] at h3
      obtain ⟨w, hw, hwfalse⟩ := List.all_eq_false.1 h3
      simp only [tabsW, List.mem_map] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      have hwok : wordOK w' = true := List.all_eq_true.1 (enumW_gens_words hb5).2 w' hw'
      have hrepw : Rep 1408 (tabW w') (elemW w') := rep_elemW_of_gensOK hg hwok
      have hmemw : elemW w' ∈ tSub k := Subgroup.subset_closure ⟨w', hw', rfl⟩
      have hcomm : x * elemW w' = elemW w' * x := hxcomm (elemW w') hmemw
      have htrue : commTT 1408 xt (tabW w') = true := (commTT_iff hrep_i hrepw).2 hcomm
      have hfalse_eq : commTT 1408 xt (tabW w') = false :=
        Bool.eq_false_of_not_eq_true hwfalse
      rw [hfalse_eq] at htrue
      exact Bool.false_ne_true htrue
  · have hcard_sub : Nat.card ↥((mSub k).subgroupOf (tSub k)) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMle).toEquiv, hcardM]
    have h := Subgroup.card_mul_index (H := (mSub k).subgroupOf (tSub k))
    rw [hcard_sub, hcardT] at h
    have hidx : ((mSub k).subgroupOf (tSub k)).index = 2 := by omega
    unfold Subgroup.relIndex
    exact hidx
  · intro x hx hxord
    obtain ⟨i, hi, hrep_i⟩ := hMl.cov x hx
    let xt := (subgroupList 1000 (mWords k))[i]!
    have hmem_xt : xt ∈ subgroupList 1000 (mWords k) := getElem!_mem_array hi
    have hxi : (tblEq 1408 xt (idT 1408) || tblEq 1408 xt (tabW wordAZ) ||
        !invoOK 1408 xt) = true :=
      (Array.all_eq_true'.1 hb10) xt hmem_xt
    rw [Bool.or_eq_true, Bool.or_eq_true] at hxi
    rcases hxi with (h1 | h2) | h3
    · have hx1 : x = 1 := (tblEq_idT_iff (by norm_num) hrep_i).1 h1
      rw [hx1, orderOf_one] at hxord
      exact absurd hxord (by norm_num)
    · exact (tblEq_iff_eq hrep_i hrep_t0).1 h2
    · rw [Bool.not_eq_true'] at h3
      have hinvol := involOK_of_orderOf (by norm_num) hrep_i hxord
      simp only [involOK, Bool.and_eq_true] at hinvol
      rw [hinvol.1] at h3
      exact absurd h3 (by decide)
  · intro hcomm
    have htrue := (commTT_iff hrep_y0 hrep_y1).2 hcomm
    rw [hb15] at htrue
    exact Bool.false_ne_true htrue

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
