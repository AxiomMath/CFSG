module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TSpecA
public import Certificates.Certificate442203

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog

private theorem tmuOne_wordAZ {k : Nat} (h : tmuOne k = true) : wordOK wordAZ = true := by
  unfold tmuOne at h
  simp only [Bool.and_eq_true] at h
  tauto

private theorem tmuOne_uWord {k : Nat} (h : tmuOne k = true) : wordOK (uWord k) = true := by
  unfold tmuOne at h
  simp only [Bool.and_eq_true] at h
  tauto

private theorem tmuOne_tWords {k : Nat} (h : tmuOne k = true) :
    enumW 1000 16 (tWords k) = true := by
  unfold tmuOne at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem c8Check_spec (hT : enumW 1000 16 (tWords 0) = true) (hu : wordOK (uWord 0) = true)
    (hAZ : wordOK wordAZ = true) (h : c8Check = true) :
    ∀ v ∈ tSub 0, orderOf v = 2 → v ≠ elemA * elemZ →
      ∃ x ∈ tSub 0, x * v * x⁻¹ = uElt 0 ∨ x * v * x⁻¹ = elemA * elemZ * uElt 0 := by
  have hg : gensOK = true := (enumW_gens_words hT).1
  have hTl : IsEnumSet 1408 (subgroupList 1000 (tWords 0)) (tSub 0 : Set _) := by
    simpa only [tSub, wSub] using (enumW_spec hT).2
  have hrepU : Rep 1408 (tabW (uWord 0)) (uElt 0) := rep_elemW_of_gensOK hg hu
  have hrepAZ : Rep 1408 (tabW wordAZ) (elemA * elemZ) := by
    have h1 : elemW wordAZ = elemA * elemZ := by
      simp only [elemW, TwoHS.wordVal, wordAZ, elemA, elemZ, List.map_append, List.prod_append]
    rw [← h1]
    exact rep_elemW_of_gensOK hg hAZ
  unfold c8Check at h
  simp only [Array.all_eq_true'] at h
  intro v hv hv2 hvne
  obtain ⟨i, hi, hrepv⟩ := hTl.cov v hv
  have hvtmem : (subgroupList 1000 (tWords 0))[i]! ∈ subgroupList 1000 (tWords 0) :=
    getElem!_mem_array hi
  have hall := h ((subgroupList 1000 (tWords 0))[i]!) hvtmem
  have hinv : involOK 1408 ((subgroupList 1000 (tWords 0))[i]!) = true :=
    involOK_of_orderOf (by norm_num) hrepv hv2
  have htbl : tblEq 1408 ((subgroupList 1000 (tWords 0))[i]!) (tabW wordAZ) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    exact hvne ((tblEq_iff_eq hrepv hrepAZ).1 hh)
  have hany : ((subgroupList 1000 (tWords 0)).any fun x =>
      tblEq 1408 (compT 1408 x ((subgroupList 1000 (tWords 0))[i]!))
          (compT 1408 (tabW (uWord 0)) x) ||
        tblEq 1408 (compT 1408 x ((subgroupList 1000 (tWords 0))[i]!))
          (compT 1408 (compT 1408 (tabW wordAZ) (tabW (uWord 0))) x)) = true := by
    have hh := hall
    simp only [hinv, htbl, Bool.not_true, Bool.false_or] at hh
    exact hh
  have hb : ∀ (y : Table) (g : Equiv.Perm (Fin 1408)), Rep 1408 y g →
      ((tblEq 1408 (compT 1408 y ((subgroupList 1000 (tWords 0))[i]!))
            (compT 1408 (tabW (uWord 0)) y) ||
          tblEq 1408 (compT 1408 y ((subgroupList 1000 (tWords 0))[i]!))
            (compT 1408 (compT 1408 (tabW wordAZ) (tabW (uWord 0))) y)) = true ↔
        (g * v = uElt 0 * g ∨ g * v = (elemA * elemZ * uElt 0) * g)) := by
    intro y g hy
    have h1 := tblEq_iff_eq (Rep.compT hy hrepv) (Rep.compT hrepU hy)
    have h2 := tblEq_iff_eq (Rep.compT hy hrepv) (Rep.compT (Rep.compT hrepAZ hrepU) hy)
    rw [Bool.or_eq_true, h1, h2]
  obtain ⟨x, hx, hxv⟩ := (hTl.exists_iff
    (fun y => tblEq 1408 (compT 1408 y ((subgroupList 1000 (tWords 0))[i]!))
          (compT 1408 (tabW (uWord 0)) y) ||
        tblEq 1408 (compT 1408 y ((subgroupList 1000 (tWords 0))[i]!))
          (compT 1408 (compT 1408 (tabW wordAZ) (tabW (uWord 0))) y))
    (fun g => g * v = uElt 0 * g ∨ g * v = (elemA * elemZ * uElt 0) * g) hb).1 hany
  rcases hxv with hxv | hxv
  · exact ⟨x, hx, Or.inl (mul_inv_eq_iff_eq_mul.2 hxv)⟩
  · exact ⟨x, hx, Or.inr (mul_inv_eq_iff_eq_mul.2 hxv)⟩

theorem fixCheck_spec (hg : gensOK = true) (hu : wordOK (uWord 1) = true)
    (hAZ : wordOK wordAZ = true) (h : fixCheck = true) :
    (∀ p : Fin 1408, uElt 1 p ≠ p) ∧ ∃ p : Fin 1408, (elemA * elemZ) p = p := by
  have hrepU : Rep 1408 (tabW (uWord 1)) (uElt 1) := rep_elemW_of_gensOK hg hu
  have hrepAZ : Rep 1408 (tabW wordAZ) (elemA * elemZ) := by
    have h1 : elemW wordAZ = elemA * elemZ := by
      simp only [elemW, TwoHS.wordVal, wordAZ, elemA, elemZ, List.map_append, List.prod_append]
    rw [← h1]
    exact rep_elemW_of_gensOK hg hAZ
  unfold fixCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro p hpp
    have hp := (allIn_eq_true.1 h1) p.val (Nat.zero_le _) p.isLt
    simp only [bne_iff_ne] at hp
    apply hp
    have hgi : ap (tabW (uWord 1)) p.val = (uElt 1 p).val := by
      rw [hrepU p.val p.isLt, idx_of_lt _ p.isLt, Equiv.Perm.smul_def]
    rw [hgi]
    exact congrArg Fin.val hpp
  · rw [List.any_eq_true] at h2
    obtain ⟨p, hp, hpe⟩ := h2
    rw [List.mem_range] at hp
    rw [beq_iff_eq] at hpe
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Fin.ext
    have hgi : ap (tabW wordAZ) p = ((elemA * elemZ) ⟨p, hp⟩).val := by
      rw [hrepAZ p hp, idx_of_lt _ hp, Equiv.Perm.smul_def]
    rw [← hgi]
    exact hpe

theorem tmuCheck_spec (h : tmuCheck = true) : TMUFacts := by
  unfold tmuCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h8⟩, hf⟩ := h
  exact
    { k0 := tmuOne_spec h0
      k1 := tmuOne_spec h1
      c8 := c8Check_spec (tmuOne_tWords h0) (tmuOne_uWord h0) (tmuOne_wordAZ h0) h8
      fpf := (fixCheck_spec (enumW_gens_words (tmuOne_tWords h1)).1 (tmuOne_uWord h1)
        (tmuOne_wordAZ h1) hf).1
      fix := (fixCheck_spec (enumW_gens_words (tmuOne_tWords h1)).1 (tmuOne_uWord h1)
        (tmuOne_wordAZ h1) hf).2 }

section Cert


theorem tmuFacts_of_cert : TMUFacts :=
  tmuCheck_spec Certificates.certificate442203

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
