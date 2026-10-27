module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.Sporadic.Schreier.MathieuOddCoreTransport
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem cent_chain_facts {S : Array (Array ℕ)} {hk : 2 ≤ S.size} {base : List (Fin 315)}
    {hb : base.Nodup} {W : Array (List ℤ)} {B : Array ℕ} (hB : (base.map Fin.val).toArray = B)
    {r : Equiv.Perm (Fin 315)} {rt : Array ℕ} (hr : Rep 315 rt r) {m N : ℕ}
    (hc : rawChainOK 315 (S.extract 0 2) S B W 4 = true) (hN : (rawOrbitSizes 315 S B).prod = N)
    (hP0 : inP S[0]! = true) (hP1 : inP S[1]! = true)
    (hc0 : commA S[0]! rt = true) (hc1 : commA S[1]! rt = true)
    (hw : oddWitnessOK 315 m (filterProducts 315 allTrue (chainTables 315 S B) (idT 315) []) =
      true) :
    (RawSchreierDatum.ofArrays 315 (by norm_num) S 2 hk base hb W).originalSubgroup ≤
        centralizerIn P r ∧
      Nat.card (RawSchreierDatum.ofArrays 315 (by norm_num) S 2 hk base hb W).originalSubgroup =
        N ∧
      OddWitness (RawSchreierDatum.ofArrays 315 (by norm_num) S 2 hk base hb W).originalSubgroup
        m := by
  subst hB
  have hQ := ofArrays_valid (hn := by norm_num) (hk := hk) (hb := hb) (by norm_num : 0 < 4) hc
  refine ⟨?_, by rw [ofArrays_card (by norm_num) hc, hN], ?_⟩
  · rw [ofArrays_originalSubgroup, Subgroup.closure_le]
    rintro g ⟨i, hi, rfl⟩
    have hrep := rep_permOfArr_of_chainOK hc (by omega : i < S.size)
    rw [SetLike.mem_coe, mem_centralizerIn]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact ⟨(mem_P_iff hrep).1 hP0, eq_of_eqA (rep_compA hrep hr) (rep_compA hr hrep) hc0⟩
    · exact ⟨(mem_P_iff hrep).1 hP1, eq_of_eqA (rep_compA hrep hr) (rep_compA hr hrep) hc1⟩
  · refine oddWitness_of_oddWitnessOK (by norm_num) _ hQ ?_
    rw [allTables, ofArrays_levelTables hc]
    exact hw

@[expose] noncomputable def cent2BChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) cent2BStrong 2 (by decide) [0, 3] (by decide)
    cent2BWords

@[expose] noncomputable def cent2AChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) cent2AStrong 2 (by decide) [0, 1, 2] (by decide)
    cent2AWords

@[expose] noncomputable def centOuterChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) centOuterStrong 2 (by decide) [0, 3] (by decide)
    centOuterWords

@[expose] noncomputable def permTwoA : Equiv.Perm (Fin 315) := perm twoAArr

theorem rep_permTwoA : Rep 315 twoAArr permTwoA :=
  (rep_permOfArr (isInvA_of_invoList inv_check.2.2.1)).1

theorem permTwoA_inv : permTwoA⁻¹ = permTwoA :=
  ((rep_permOfArr (isInvA_of_invoList inv_check.2.2.1)).2).unique rep_permTwoA

theorem permTwoA_mem : permTwoA ∈ P := (mem_P_iff rep_permTwoA).1 classes_check.1

theorem orderOf_permTwoA : orderOf permTwoA = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [sq, ← mul_inv_cancel permTwoA, permTwoA_inv]
  · have h1 := eqA_idA_of_movesList inv_check.2.2.2
    rw [(eqA_iff rep_permTwoA rep_idA).2 h] at h1
    exact Bool.noConfusion h1

theorem orderOf_permU : orderOf permU = 2 := orderOf_eq_prime permU_sq permU_ne_one

theorem cent2B_facts : cent2BChain.originalSubgroup ≤ centralizerIn P permA ∧
    Nat.card cent2BChain.originalSubgroup = 240 ∧ OddWitness cent2BChain.originalSubgroup 15 := by
  obtain ⟨hc, hN, hP0, hP1, hc0, hc1, hw⟩ := cent2B_check
  exact cent_chain_facts (B := cent2BBase) rfl rep_permA hc (by rw [hN]; rfl) hP0 hP1 hc0 hc1 hw

theorem cent2A_facts : cent2AChain.originalSubgroup ≤ centralizerIn P permTwoA ∧
    Nat.card cent2AChain.originalSubgroup = 1920 ∧ OddWitness cent2AChain.originalSubgroup 15 := by
  obtain ⟨hc, hN, hP0, hP1, hc0, hc1, hw⟩ := cent2A_check
  exact cent_chain_facts (B := cent2ABase) rfl rep_permTwoA hc (by rw [hN]; rfl) hP0 hP1 hc0 hc1
    hw

theorem centOuter_facts : centOuterChain.originalSubgroup ≤ centralizerIn P permU ∧
    Nat.card centOuterChain.originalSubgroup = 336 ∧
      OddWitness centOuterChain.originalSubgroup 21 := by
  obtain ⟨hc, hN, hP0, hP1, hc0, hc1, hw⟩ := centOuter_check
  exact cent_chain_facts (B := centOuterBase) rfl rep_permU hc (by rw [hN]; rfl) hP0 hP1 hc0 hc1
    hw

theorem toTable_one : toTable (1 : Equiv.Perm (Fin 315)) = idT 315 := rfl

theorem cosetOrderTables_one :
    cosetOrderTables autChain 1 2 = orderTablesOf (idT 315) 2 := by
  rw [cosetOrderTables, levelTables_autChain, toTable_one]
  rfl

theorem cosetOrderTables_permU :
    cosetOrderTables autChain permU 2 = orderTablesOf tblU 2 := by
  rw [cosetOrderTables, levelTables_autChain, toTable_eq_arrTable rep_permU]
  rfl

theorem toTable_permA : toTable permA = tblA := toTable_eq_arrTable rep_permA

theorem toTable_permTwoA : toTable permTwoA = tblTwoA := toTable_eq_arrTable rep_permTwoA

theorem toTable_permU : toTable permU = tblU := toTable_eq_arrTable rep_permU

theorem inner_reps :
    repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (cosetOrderTables autChain 1 2)
        [toTable permA, toTable permTwoA] 4000 = true ∧
      (conjClosure 315 #[tblA, tblB] #[tblAInv, tblBInv] (toTable permA) 4000).1.size = 2520 ∧
      (conjClosure 315 #[tblA, tblB] #[tblAInv, tblBInv] (toTable permTwoA) 4000).1.size = 315 := by
  obtain ⟨-, hok, hsz, -, -⟩ := classes_check
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [cosetOrderTables_one, toTable_permA, toTable_permTwoA]
  exact ⟨hok, hsz.1, hsz.2⟩

theorem outer_reps :
    repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (cosetOrderTables autChain permU 2)
        [toTable permU] 4000 = true ∧
      (conjClosure 315 #[tblA, tblB] #[tblAInv, tblBInv] (toTable permU) 4000).1.size = 1800 := by
  obtain ⟨-, -, -, hok, hsz⟩ := classes_check
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [cosetOrderTables_permU, toTable_permU]
  exact ⟨hok, hsz⟩

theorem one_inv_conj_mem : ∀ h ∈ autChain.originalSubgroup,
    (1 : Equiv.Perm (Fin 315))⁻¹ * h * 1 ∈ autChain.originalSubgroup := fun h hh => by
  simpa using hh

theorem permU_inv_conj_mem : ∀ h ∈ autChain.originalSubgroup,
    permU⁻¹ * h * permU ∈ autChain.originalSubgroup := by
  rw [autChain_originalSubgroup]
  exact permU_conj_mem'

theorem inner_classes :
    (∀ t ∈ P, orderOf t = 2 → ∃ r ∈ [permA, permTwoA], ∃ c ∈ P, t = c * r * c⁻¹) ∧
      (conjClass P permA).ncard = 2520 ∧ centralizerIn P permA = cent2BChain.originalSubgroup ∧
      (conjClass P permTwoA).ncard = 315 ∧
      centralizerIn P permTwoA = cent2AChain.originalSubgroup := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, h1, h2⟩ := inner_reps
  have hreps : ∀ r ∈ [permA, permTwoA], (1 : Equiv.Perm (Fin 315))⁻¹ * r ∈
      autChain.originalSubgroup ∧ orderOf r = 2 := by
    intro r hr
    rw [autChain_originalSubgroup]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨by simpa using permA_mem, orderOf_permA⟩
    · exact ⟨by simpa using permTwoA_mem, orderOf_permTwoA⟩
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn autChain autChain_valid genTables_spec 1
    one_inv_conj_mem (by norm_num) [permA, permTwoA] hreps 4000 hok
  rw [autChain_originalSubgroup] at hcov hsize
  obtain ⟨hK1, hK1c, -⟩ := cent2B_facts
  obtain ⟨hK2, hK2c, -⟩ := cent2A_facts
  have hc1 := hsize permA (by simp)
  have hc2 := hsize permTwoA (by simp)
  rw [h1] at hc1
  rw [h2] at hc2
  have he1 := centralizerIn_eq_of_le P permA hK1 hc1 (by rw [hK1c, card_P])
  have he2 := centralizerIn_eq_of_le P permTwoA hK2 hc2 (by rw [hK2c, card_P])
  have hcl1 := ncard_conjClass_mul_card P permA
  have hcl2 := ncard_conjClass_mul_card P permTwoA
  rw [he1, hK1c, card_P] at hcl1
  rw [he2, hK2c, card_P] at hcl2
  refine ⟨fun t ht ho => hcov t (by simpa using ht) ho, ?_, he1, ?_, he2⟩
  · exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 240) (hcl1.trans (by norm_num))
  · exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1920) (hcl2.trans (by norm_num))

theorem outer_classes :
    (∀ t, permU⁻¹ * t ∈ P → orderOf t = 2 → ∃ c ∈ P, t = c * permU * c⁻¹) ∧
      (conjClass P permU).ncard = 1800 ∧
      centralizerIn P permU = centOuterChain.originalSubgroup := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, h1⟩ := outer_reps
  have hreps : ∀ r ∈ [permU], permU⁻¹ * r ∈ autChain.originalSubgroup ∧ orderOf r = 2 := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    rw [inv_mul_cancel]
    exact ⟨one_mem _, orderOf_permU⟩
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn autChain autChain_valid genTables_spec permU
    permU_inv_conj_mem (by norm_num) [permU] hreps 4000 hok
  rw [autChain_originalSubgroup] at hcov hsize
  obtain ⟨hK, hKc, -⟩ := centOuter_facts
  have hc := hsize permU (by simp)
  rw [h1] at hc
  have he := centralizerIn_eq_of_le P permU hK hc (by rw [hKc, card_P])
  have hcl := ncard_conjClass_mul_card P permU
  rw [he, hKc, card_P] at hcl
  refine ⟨fun t ht ho => ?_, ?_, he⟩
  · obtain ⟨r, hr, c, hc, rfl⟩ := hcov t ht ho
    rw [List.mem_singleton] at hr
    exact ⟨c, hc, by rw [hr]⟩
  · exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 336) (hcl.trans (by norm_num))

theorem inner_witness : ∀ t ∈ P, orderOf t = 2 → ∃ mu vu : ℕ,
    Nat.card (centralizerIn P t) = 2 ^ vu * mu ∧ OddWitness (centralizerIn P t) mu := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, h1, h2⟩ := inner_reps
  obtain ⟨hK1, hK1c, hK1w⟩ := cent2B_facts
  obtain ⟨hK2, hK2c, hK2w⟩ := cent2A_facts
  rw [← autChain_originalSubgroup]
  intro t ht ho
  refine centralizer_witness_of_reps hn autChain autChain_valid genTables_spec 1 one_inv_conj_mem
    [(permA, cent2BChain.originalSubgroup, 15, 4), (permTwoA, cent2AChain.originalSubgroup, 15, 7)]
    ?_ 4000 hok ?_ t (by simpa using ht) ho
  · intro d hd
    rw [autChain_originalSubgroup]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨by simpa using permA_mem, orderOf_permA⟩
    · exact ⟨by simpa using permTwoA_mem, orderOf_permTwoA⟩
  · intro d hd
    rw [autChain_originalSubgroup, card_P]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hK1, by rw [h1, hK1c], by rw [hK1c]; rfl, hK1w⟩
    · exact ⟨hK2, by rw [h2, hK2c], by rw [hK2c]; rfl, hK2w⟩

theorem outer_witness : ∀ t, permU⁻¹ * t ∈ P → orderOf t = 2 → ∃ mu vu : ℕ,
    Nat.card (centralizerIn P t) = 2 ^ vu * mu ∧ OddWitness (centralizerIn P t) mu := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, h1⟩ := outer_reps
  obtain ⟨hK, hKc, hKw⟩ := centOuter_facts
  rw [← autChain_originalSubgroup]
  intro t ht ho
  refine centralizer_witness_of_reps hn autChain autChain_valid genTables_spec permU
    permU_inv_conj_mem [(permU, centOuterChain.originalSubgroup, 21, 4)] ?_ 4000 hok ?_ t ht ho
  · intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact ⟨by rw [inv_mul_cancel]; exact one_mem _, orderOf_permU⟩
  · intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    rw [autChain_originalSubgroup, card_P]
    exact ⟨hK, by rw [h1, hKc], by rw [hKc]; rfl, hKw⟩

theorem mem_P_or_coset {t : Equiv.Perm (Fin 315)} (ht : t ∈ R) : t ∈ P ∨ permU⁻¹ * t ∈ P := by
  rcases (mem_R_iff t).1 ht with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have e : permU⁻¹ * t = permU * (t * permU) * permU⁻¹ := by
      rw [show permU * (t * permU) * permU⁻¹ = permU * t * (permU * permU⁻¹) by group,
        mul_inv_cancel, mul_one, permU_inv]
    rw [e]
    exact permU_conj_mem _ h

theorem fixed_points_reps :
    Nat.card {i : Fin 315 // permA i = i} = 15 ∧ Nat.card {i : Fin 315 // permTwoA i = i} = 11 ∧
      Nat.card {i : Fin 315 // permU i = i} = 21 := by
  obtain ⟨h1, h2, h3⟩ := fixed_check
  exact ⟨(card_fixed_eq_fixedCount rep_permA).trans h1,
    (card_fixed_eq_fixedCount rep_permTwoA).trans h2,
    (card_fixed_eq_fixedCount rep_permU).trans h3⟩

@[expose] noncomputable def sylowChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) sylowStrong 3 (by decide) [1, 3] (by decide)
    sylowWords

@[expose] noncomputable def sylowS : Subgroup (Equiv.Perm (Fin 315)) := sylowChain.originalSubgroup

theorem sylowBase_eq : (([1, 3] : List (Fin 315)).map Fin.val).toArray = sylowBase := rfl

theorem sylowChain_ok : rawChainOK 315 (sylowStrong.extract 0 3) sylowStrong
    (([1, 3] : List (Fin 315)).map Fin.val).toArray sylowWords 4 = true := by
  rw [sylowBase_eq]
  exact sylow_check.1

theorem sylowS_le_R : sylowS ≤ R := by
  obtain ⟨-, -, h0, h1, h2⟩ := sylow_check
  rw [sylowS, sylowChain, ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro g ⟨i, hi, rfl⟩
  have hi5 : i < sylowStrong.size := by
    have : sylowStrong.size = 5 := rfl
    omega
  have hrep := rep_permOfArr_of_chainOK (j := i) sylowChain_ok hi5
  have hP : inP (compA 315 sylowStrong[i]! outerArr) = true := by
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    · exact h0
    · exact h1
    · exact h2
  rw [SetLike.mem_coe, mem_R_iff]
  exact Or.inr ((mem_P_iff (rep_compA hrep rep_permU)).1 hP)

theorem card_sylowS : Nat.card sylowS = 256 := by
  rw [sylowS, sylowChain, ofArrays_card (by norm_num) sylowChain_ok, sylowBase_eq,
    sylow_check.2.1]
  rfl

theorem card_sylowS_subgroupOf : Nat.card (sylowS.subgroupOf R) = 2 ^ 8 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowS_le_R).toEquiv, card_sylowS]
  norm_num

theorem index_sylowS : (sylowS.subgroupOf R).index = 4725 := by
  have h := (sylowS.subgroupOf R).card_mul_index
  rw [card_sylowS_subgroupOf, card_R] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 8) (h.trans (by norm_num))

@[expose] noncomputable def sylowR : Sylow 2 R :=
  (IsPGroup.of_card card_sylowS_subgroupOf).toSylow (by rw [index_sylowS]; decide)

theorem sylowR_coe : (sylowR : Subgroup R) = sylowS.subgroupOf R := rfl

theorem ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial :
    sylowS ≤ R ∧ Nat.card sylowS = 256 ∧ (sylowR : Subgroup R) = sylowS.subgroupOf R ∧
      permA ∈ P ∧ permTwoA ∈ P ∧ permU ∉ P ∧ orderOf permA = 2 ∧ orderOf permTwoA = 2 ∧
      orderOf permU = 2 ∧ Nat.card {i : Fin 315 // permA i = i} = 15 ∧
      Nat.card {i : Fin 315 // permTwoA i = i} = 11 ∧ Nat.card {i : Fin 315 // permU i = i} = 21 ∧
      (∀ t ∈ R, orderOf t = 2 → ∃ r ∈ [permA, permTwoA, permU], ∃ c ∈ P, t = c * r * c⁻¹) ∧
      (conjClass P permA).ncard = 2520 ∧ Nat.card (centralizerIn P permA) = 240 ∧
      (conjClass P permTwoA).ncard = 315 ∧ Nat.card (centralizerIn P permTwoA) = 1920 ∧
      (conjClass P permU).ncard = 1800 ∧ Nat.card (centralizerIn P permU) = 336 ∧
      ∀ t ∈ R, orderOf t = 2 → CFSG.oddCore (centralizerIn P t) = ⊥ := by
  obtain ⟨hcovI, hcl1, he1, hcl2, he2⟩ := inner_classes
  obtain ⟨hcovO, hcl3, he3⟩ := outer_classes
  obtain ⟨hf1, hf2, hf3⟩ := fixed_points_reps
  refine ⟨sylowS_le_R, card_sylowS, sylowR_coe, permA_mem, permTwoA_mem, permU_not_mem,
    orderOf_permA, orderOf_permTwoA, orderOf_permU, hf1, hf2, hf3, fun t ht ho => ?_, hcl1,
    by rw [he1]; exact cent2B_facts.2.1, hcl2, by rw [he2]; exact cent2A_facts.2.1, hcl3,
    by rw [he3]; exact centOuter_facts.2.1, fun t ht ho => ?_⟩
  · rcases mem_P_or_coset ht with h | h
    · obtain ⟨r, hr, c, hc, e⟩ := hcovI t h ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, c, hc, e⟩
      · exact ⟨_, by simp, c, hc, e⟩
    · obtain ⟨c, hc, e⟩ := hcovO t h ho
      exact ⟨permU, by simp, c, hc, e⟩
  · rcases mem_P_or_coset ht with h | h
    · obtain ⟨mu, vu, hcard, hw⟩ := inner_witness t h ho
      exact oddCore_eq_bot_of_oddWitness hcard hw
    · obtain ⟨mu, vu, hcard, hw⟩ := outer_witness t h ho
      exact oddCore_eq_bot_of_oddWitness hcard hw

theorem P_inner_oddCore (t : P) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set P)) = ⊥ :=
  inner_oddCore_eq_bot P inner_witness t ht

theorem permU_outer : ∀ g ∈ P, ¬∀ h ∈ P, permU * g * h = h * (permU * g) := by
  intro g hg hall
  have hc : permU * g ∈ Subgroup.centralizer (P : Set (Equiv.Perm (Fin 315))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hall h hh).symm
  rw [centralizer_P, Subgroup.mem_bot] at hc
  apply permU_not_mem
  rw [show permU = g⁻¹ by rw [← mul_eq_one_iff_eq_inv]; exact hc]
  exact P.inv_mem hg

theorem P_outer_oddCore (α : MulAut P) (hα2 : α * α = 1) (hα : α ∉ inner P) :
    CFSG.oddCore (fixSub α) = ⊥ := by
  refine outer_oddCore_eq_bot P permU permU_conj_mem (by rw [permU_mul_self]; exact P.one_mem)
    center_P permU_outer ?_ outer_witness α hα2 hα
  rw [card_mulAut_P, card_P]

theorem j2_inner_oddCore (t : NativeSporadic.J2) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set NativeSporadic.J2)) = ⊥ := by
  have h := inner_of_equiv (G := NativeSporadic.J2) (H := P) nativeEquivP P_inner_oddCore
  exact h t ht

theorem j2_mulAut_card : Nat.card (MulAut NativeSporadic.J2) = 2 * Nat.card NativeSporadic.J2 := by
  rw [Nat.card_congr mulAutEquivP, Nat.card_congr nativeEquivP.toEquiv, card_mulAut_P, card_P]

theorem j2_outer_oddCore (α : MulAut NativeSporadic.J2) (hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.J2) : CFSG.oddCore (fixSub (G := NativeSporadic.J2) α) = ⊥ := by
  have h := outer_of_equiv (G := NativeSporadic.J2) (H := P) nativeEquivP P_outer_oddCore
  exact h α hα2 hα

theorem ctuc_j2_almost_simple_involution_centralizer_odd_core_trivial {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (ψ : S ≃* NativeSporadic.J2)
    (hC : Subgroup.centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have hP : Nat.card (MulAut P) ≤ 2 * Nat.card P := by rw [card_mulAut_P, card_P]
  exact oddCore_centralizer_eq_bot_of_normal P_inner_oddCore hP P_outer_oddCore S
    (ψ.trans nativeEquivP) hC t ht

end CFSG.ComponentClassification.J2Cover
