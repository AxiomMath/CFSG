module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBJ2Cert
public import Certificates.Certificate22401
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdx

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

@[expose] def vE (k : ℕ) : Equiv.Perm (Fin 315) := tp 315 vTbls[k]!

@[expose] def u0 : Equiv.Perm (Fin 315) := tp 315 u0Tbl

section Facts


theorem vT_facts : ∀ i < 128, ∀ j < 128, vT i j < 128 ∧ vE (vT i j) = vE i * vE j :=
  Certificates.certificate22401.1.1

theorem vI_facts : ∀ i < 128, vI i < 128 ∧ vE (vI i) = (vE i)⁻¹ :=
  Certificates.certificate22401.1.2.1

theorem vE_zero : vE 0 = 1 := Certificates.certificate22401.1.2.2.1

theorem vE_inj : ∀ i < 128, ∀ j < 128, vE i = vE j → i = j :=
  Certificates.certificate22401.1.2.2.2.2.1

theorem vCu_facts : ∀ k < 128, vCu k < 128 ∧ u0 * vE k * u0⁻¹ = vE (vCu k) :=
  Certificates.certificate22401.1.2.2.2.2.2.2.1

theorem vUsq_lt : vUsq < 128 := Certificates.certificate22401.1.2.2.2.2.2.2.2.1

theorem vIndex_facts :
    (∀ i < 128, vT i (vI i) = 0) ∧
      (∀ i < 128, (∀ j < 128, vT i j = vT j i) → i = 0 ∨ i = 1) ∧
      (∀ j < 128, vT 1 j = vT j 1) ∧
      (∀ c ∈ vComm, ∀ c' ∈ vComm, vT c c' ∈ vComm) ∧
      (∀ i < 128, i ∈ ivList ↔ ∀ c ∈ vComm, ci vT vI i c = 0 ∨ ci vT vI i c = 1) ∧
      (∀ i ∈ ivList, i < 128) ∧ ivList.Nodup ∧
      (∀ i < 128, (∀ l ∈ ivList, vT i l = vT l i) → i = 0 ∨ i = 1) ∧
      (quads (ivSq 0) (ivSq 1) (ivSq 2) (ivSq 3)).countP (sigIdx vT vI 0 1 sqPat cmPat) = 1920 ∧
      ci vT vI 7 8 = 1 ∧
      (∀ v < 128, vT v (vT (vCu v) vUsq) = 0 →
        16 ≤ (List.range 128).countP (fun d => vAc v d == d) →
        ∃ w < 128, vAc v w = vT w 1 ∧ (vT w w = 0 ∨ vT w w = 1) ∧
          ∀ d < 128, vAc v d = d → ci vT vI w d = 0 ∨ ci vT vI w d = 1) := by
  have h := Certificates.certificate22401.2
  simp only [subIndexCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem,
    List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hinv, hcen⟩, hz⟩, hcomm⟩, hiv⟩, hivlt⟩, hnd⟩, hciv⟩, hsig⟩, h78⟩, hf4⟩ := h
  refine ⟨hinv, fun i hi hc => ?_, hz, hcomm, fun i hi => ?_, hivlt, hnd, fun i hi hc => ?_, hsig,
    h78, fun v hv hsq hcnt => ?_⟩
  · have hall : ((List.range 128).all fun j => vT i j == vT j i) = true := by
      rw [List.all_eq_true]
      intro j hj
      rw [beq_iff_eq]
      exact hc j (List.mem_range.mp hj)
    rcases hcen i hi with (h1 | h1) | h1
    · rw [hall] at h1
      exact absurd h1 (by decide)
    · exact Or.inl h1
    · exact Or.inr h1
  · rw [← List.contains_iff_mem, hiv i hi, List.all_eq_true]
    simp only [Bool.or_eq_true, beq_iff_eq]
  · have hall : (ivList.all fun l => vT i l == vT l i) = true := by
      rw [List.all_eq_true]
      intro l hl
      rw [beq_iff_eq]
      exact hc l hl
    rcases hciv i hi with (h1 | h1) | h1
    · rw [hall] at h1
      exact absurd h1 (by decide)
    · exact Or.inl h1
    · exact Or.inr h1
  · rcases hf4 v hv with h1 | ⟨w, hw, ⟨hw1, hw2⟩, hw3⟩
    · rw [Bool.and_eq_false_iff] at h1
      rcases h1 with h1 | h1
      · rw [hsq] at h1
        exact absurd h1 (by decide)
      · rw [decide_eq_false_iff_not] at h1
        exact absurd hcnt h1
    · refine ⟨w, hw, hw1, hw2, fun d hd hdd => ?_⟩
      rcases hw3 d hd with (h1 | h1) | h1
      · rw [hdd] at h1
        exact absurd h1 (by simp)
      · exact Or.inl h1
      · exact Or.inr h1

theorem vModel : IdxModel 128 vE vT vI 0 :=
  ⟨fun i hi j hj => (vT_facts i hi j hj).1, fun i hi j hj => (vT_facts i hi j hj).2,
    fun i hi => (vI_facts i hi).1, fun i hi => (vI_facts i hi).2, by norm_num, vE_zero,
    fun i hi j hj hij => vE_inj i hi j hj hij⟩

theorem vE_one : vE 1 = permTwoA := Certificates.certificate22401.1.2.2.2.1

theorem vTbls_eq {k : ℕ} (hk : k < 128) : vTbls[k]! = wordTbl 315 c2AGens vWords[k]! := by
  have hl : vWords.length = 128 := by decide +kernel
  simp only [vTbls, List.getElem!_toArray]
  rw [getElem!_pos _ k (by simp [hl, hk]), getElem!_pos _ k (by simp [hl, hk])]
  simp

theorem vE_mem {k : ℕ}
    (hk : k < 128) : vE k ∈ centralizerIn P permTwoA :=
  Certificates.certificate22401.1.2.2.2.2.2.1 k hk

theorem u0_facts :
    u0 ∈ centralizerIn R permTwoA ∧ u0 ∉ P ∧
      (∀ k < 128, u0 * vE k * u0⁻¹ = vE (vCu k)) ∧ u0 * u0 = vE vUsq := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have hsz : 3 ≤ crTStrong.size := by decide
  have h0 : CFSG.Sporadic.Th.Rep 315 (arrTable 315 crTStrong[0]!)
      (CFSG.Monster.B.Co2.permOfArr 315 crTStrong[0]!) :=
    rep_arrTable_chain crT_parts.1 (by omega)
  have h2 : CFSG.Sporadic.Th.Rep 315 (arrTable 315 crTStrong[2]!)
      (CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]!) :=
    rep_arrTable_chain crT_parts.1 (by omega)
  have hT : u0Tbl = compT 315 (compT 315 (idT 315) (arrTable 315 crTStrong[0]!))
      (arrTable 315 crTStrong[2]!) := by
    simp only [u0Tbl, wordTbl, List.foldl_cons, List.foldl_nil, crTGens, Nat.sub_self,
      show (3 : ℕ) - 1 = 0 + 1 + 1 from rfl, List.getD_cons_zero, List.getD_cons_succ]
  have hw : CFSG.Sporadic.Th.Rep 315 u0Tbl ((1 : Equiv.Perm (Fin 315)) *
      CFSG.Monster.B.Co2.permOfArr 315 crTStrong[0]! *
      CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]!) := by
    rw [hT]
    exact Rep.compT (Rep.compT (Rep.idT hn) h0) h2
  have he : u0 = CFSG.Monster.B.Co2.permOfArr 315 crTStrong[0]! *
      CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]! := by
    rw [← one_mul (CFSG.Monster.B.Co2.permOfArr 315 crTStrong[0]!)]
    exact CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (co2Rep_natArr_iff.2 hw)
  have hmemT : ∀ j < 3, CFSG.Monster.B.Co2.permOfArr 315 crTStrong[j]! ∈
      centralizerIn R permTwoA := fun j hj => by
    rw [← genOf_crTGens, ← tp_arrTable_chain crT_parts.1 (by omega)]
    exact tp_mem_genOf (by rw [crTGens_eq]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  have hu0 : u0 ∈ centralizerIn R permTwoA := by
    rw [he]
    exact mul_mem (hmemT 0 (by norm_num)) (hmemT 2 (by norm_num))
  refine ⟨hu0, fun hP => ?_, fun k hk => (vCu_facts k hk).2,
    Certificates.certificate22401.1.2.2.2.2.2.2.2.2⟩
  ·
    have hc2 : CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]! ∈ P := by
      have : CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]! =
          (CFSG.Monster.B.Co2.permOfArr 315 crTStrong[0]!)⁻¹ * u0 := by
        rw [he, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact mul_mem (inv_mem crT_gen0_mem) hP
    apply permU_not_mem
    have : permU = (CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]!)⁻¹ *
        (CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]! * permU) := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact mul_mem (inv_mem hc2) crT_gen2_outer

theorem eq_of_centralizes_basis
    {r : Equiv.Perm (Fin 315)} (hr : r ∈ R)
    (hc : ∀ k ∈ vBasis, r * vE k = vE k * r) : r = 1 ∨ r = permTwoA := by
  have hL : vBasis.map (fun k => vTbls[k]!) = [[1, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 1],
      [1, 1, 2, 2, 1, 1, 2, 2], [1, 2, 2, 1, 1, 2, 2, 1]].map (wordTbl 315 c2AGens) := by
    simp only [vBasis, List.map_cons, List.map_nil, vTbls_eq (by norm_num : 7 < 128),
      vTbls_eq (by norm_num : 8 < 128), vTbls_eq (by norm_num : 19 < 128),
      vTbls_eq (by norm_num : 23 < 128)]
    rfl
  have hcard : Nat.card ↥(genOf 315 crTGens ⊓ centralizer
      (genOf 315 (vBasis.map (fun k => vTbls[k]!)) : Set (Equiv.Perm (Fin 315)))) = 2 := by
    rw [genOf_crTGens, hL]
    exact Certificates.certificate22400.2.2.2
  have hgen : ∀ k ∈ vBasis, tp 315 vTbls[k]! = vE k := fun k _ => rfl
  have hcentr : ∀ x : Equiv.Perm (Fin 315), (∀ k ∈ vBasis, x * vE k = vE k * x) →
      x ∈ centralizer (genOf 315 (vBasis.map (fun k => vTbls[k]!)) :
        Set (Equiv.Perm (Fin 315))) := by
    intro x hx
    rw [centralizer_closure, mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ vBasis.map (fun k => vTbls[k]!) := by simpa using hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg'
    exact (hx k hk).symm
  have h78 := vIndex_facts.2.2.2.2.2.2.2.2.2.1
  have hz : permTwoA = ⁅vE 7, vE 8⁆ := by
    rw [← vE_one, ← h78, vModel.e_ci (by norm_num) (by norm_num)]
  have hrz : r * permTwoA = permTwoA * r := by
    have h7 : Commute r (vE 7) := hc 7 (by simp [vBasis])
    have h8 : Commute r (vE 8) := hc 8 (by simp [vBasis])
    rw [hz, commutatorElement_def]
    exact (((h7.mul_right h8).mul_right h7.inv_right).mul_right h8.inv_right).eq
  have hrC : r ∈ genOf 315 crTGens ⊓ centralizer (genOf 315 (vBasis.map (fun k => vTbls[k]!)) :
      Set (Equiv.Perm (Fin 315))) := by
    refine mem_inf.mpr ⟨?_, hcentr r hc⟩
    rw [genOf_crTGens]
    exact mem_centralizerIn.mpr ⟨hr, hrz⟩
  have hzC : permTwoA ∈ genOf 315 crTGens ⊓ centralizer (genOf 315
      (vBasis.map (fun k => vTbls[k]!)) : Set (Equiv.Perm (Fin 315))) := by
    refine mem_inf.mpr ⟨?_, hcentr _ fun k hk => ?_⟩
    · rw [genOf_crTGens]
      exact mem_centralizerIn.mpr ⟨P_le_R permTwoA_mem, rfl⟩
    · have hk' : k < 128 := by
        simp only [vBasis, List.mem_cons, List.not_mem_nil, or_false] at hk
        omega
      rw [← vE_one, ← vModel.e_T 1 (by norm_num) k hk', ← vModel.e_T k hk' 1 (by norm_num),
        vIndex_facts.2.2.1 k hk']
  have hz1 : permTwoA ≠ 1 := by
    intro h
    have := orderOf_permTwoA
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  by_cases h1 : r = 1
  · exact Or.inl h1
  · exact Or.inr (eq_of_card_eq_two hcard hrC hzC h1 hz1)

end Facts

end CFSG.ComponentClassification.HarrisLit.EndB
