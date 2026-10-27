module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6Cert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcHyp
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcSp6

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Certificates
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native

structure CensusChecks : Prop where
  arr : censusArrCheck = true
  chain : censusChainCheck = true
  cover : censusCoverCheck = true
  fusion : censusFusionCheck = true
  deriv : censusDerivCheck = true

theorem fixCount_eq_ncard (g : Equiv.Perm (Fin 276)) :
    fixCount g = {p : Fin 276 | g p = p}.ncard := by
  rw [fixCount, List.countP_eq_length_filter]
  set l := (List.finRange 276).filter fun p => decide (g p = p) with hl
  have hnd : l.Nodup := (List.nodup_finRange 276).filter _
  have hset : {p : Fin 276 | g p = p} = ↑l.toFinset := by
    ext p
    simp [hl]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem fixCount_conj (c g : Equiv.Perm (Fin 276)) : fixCount (c * g * c⁻¹) = fixCount g := by
  rw [fixCount_eq_ncard, fixCount_eq_ncard]
  have h : {p : Fin 276 | (c * g * c⁻¹) p = p} = c '' {p | g p = p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, Equiv.Perm.mul_apply]
    constructor
    · intro h
      refine ⟨c⁻¹ p, ?_, by simp⟩
      have h' := congrArg (fun x => c⁻¹ x) h
      simpa using h'
    · rintro ⟨q, hq, rfl⟩
      simp [hq]
  rw [h, Set.ncard_image_of_injective _ c.injective]

theorem arr_facts (hC : CensusChecks) :
    (∀ k < 7, isInvA 276 co3MArrs[k]! (invCand 276 co3MArrs[k]!) = true ∧
      isInvA 276 (invCand 276 co3MArrs[k]!) co3MArrs[k]! = true) ∧
    (∀ k < 8, isInvA 276 co3TArrs[k]! (invCand 276 co3TArrs[k]!) = true ∧
      isInvA 276 (invCand 276 co3TArrs[k]!) co3TArrs[k]! = true) ∧
    (isInvA 276 co3ZArr (invCand 276 co3ZArr) = true ∧
      isInvA 276 (invCand 276 co3ZArr) co3ZArr = true) := by
  have h := hC.arr
  simp only [censusArrCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem zC_eq (hC : CensusChecks) : zC = co3Z :=
  permOrId_eq_permOfArr (arr_facts hC).2.2

theorem closure_mGens (hC : CensusChecks) : Subgroup.closure {g | g ∈ mGens} = co3M := by
  rw [co3M_eq]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_range, mGens, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, (permOrId_eq_permOfArr ((arr_facts hC).1 k hk)).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, permOrId_eq_permOfArr ((arr_facts hC).1 k k.2)⟩

theorem closure_tGens (hC : CensusChecks) : Subgroup.closure {g | g ∈ tGens} = co3T := by
  rw [co3T_eq]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_range, tGens, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, (permOrId_eq_permOfArr ((arr_facts hC).2.1 k hk)).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, permOrId_eq_permOfArr ((arr_facts hC).2.1 k k.2)⟩

theorem mGens_mem (hC : CensusChecks) : ∀ g ∈ mGens, g ∈ co3M := fun g hg => by
  rw [← closure_mGens hC]
  exact Subgroup.subset_closure hg

theorem tGens_mem (hC : CensusChecks) : ∀ g ∈ tGens, g ∈ co3T := fun g hg => by
  rw [← closure_tGens hC]
  exact Subgroup.subset_closure hg

theorem tQ_eq (hC : CensusChecks) : tQ.originalSubgroup = co3T := by
  rw [tQ, certificate_originalSubgroup, closure_tGens hC]

theorem chain_facts (hC : CensusChecks) :
    ValidSchreier tQ ∧ tQ.orderCertificate = 1024 ∧ ValidSchreier saQ ∧
      saQ.orderCertificate = 512 ∧ ValidSchreier sbQ ∧ sbQ.orderCertificate = 128 ∧
      (∀ g ∈ tGens, g * zC = zC * g) ∧ (∀ g ∈ saGens, g * xa = xa * g) ∧
      ∀ g ∈ sbGens, g * xb = xb * g := by
  have h := hC.chain
  simp only [censusChainCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    schreierPermEq_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem z_comm_co3M
    {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3M) :
    g * co3Z = co3Z * g := by
  rw [co3M_eq_centralizer] at hg
  exact Subgroup.mem_centralizer_singleton_iff.1 hg.2

theorem co3T_le_co3M
    (hC : CensusChecks) : co3T ≤ co3M := by
  rw [co3M_eq_centralizer]
  refine le_inf co3T_le_P ?_
  rw [← closure_tGens hC, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← zC_eq hC]
  exact (chain_facts hC).2.2.2.2.2.2.1 g hg

theorem exists_conj_le_T
    (hC : CensusChecks) {Q : Subgroup (Equiv.Perm (Fin 276))}
    (hQM : Q ≤ co3M) (hQ : IsPGroup 2 Q) : ∃ g ∈ co3M, ∀ q ∈ Q, g * q * g⁻¹ ∈ co3T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM := co3T_le_co3M hC
  have hcardT : Nat.card (co3T.subgroupOf co3M) = 1024 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, card_co3T]
  have hT2 : IsPGroup 2 (co3T.subgroupOf co3M) :=
    IsPGroup.of_card (n := 10) (by rw [hcardT]; norm_num)
  have hidx : ¬ 2 ∣ (co3T.subgroupOf co3M).index := by
    have h := (co3T.subgroupOf co3M).card_mul_index
    rw [hcardT, card_co3M] at h
    have h2 : (co3T.subgroupOf co3M).index = 2835 := by omega
    rw [h2]
    norm_num
  let S' : Sylow 2 co3M := hT2.toSylow hidx
  have hQ' : IsPGroup 2 (Q.subgroupOf co3M) :=
    hQ.comap_of_injective co3M.subtype co3M.subtype_injective
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq co3M R S'
  refine ⟨g, g.2, fun q hq => ?_⟩
  have h2 : g * ⟨q, hQM hq⟩ * g⁻¹ ∈ ((g • R : Sylow 2 co3M) : Subgroup co3M) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hR (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  rw [hg] at h2
  have h3 : g * ⟨q, hQM hq⟩ * g⁻¹ ∈ co3T.subgroupOf co3M := by simpa [S'] using h2
  rw [Subgroup.mem_subgroupOf] at h3
  simpa using h3

abbrev tSize (r : Equiv.Perm (Fin 276)) : ℕ :=
  (conjClosure 276 (listTables tGens) (listTables (tGens.map (·⁻¹))) (toTable r) 600).1.size

theorem cover_facts (hC : CensusChecks) :
    (∀ u ∈ co3T, orderOf u = 2 → ∃ r ∈ tReps, ∃ c ∈ co3T, u = c * r * c⁻¹) ∧
      (∀ r ∈ tReps, tSize r ≤ (conjClass co3T r).ncard) ∧
      (∀ u ∈ saQ.originalSubgroup, orderOf u = 2 →
        ∃ r ∈ raReps, ∃ c ∈ saQ.originalSubgroup, u = c * r * c⁻¹) ∧
      ∀ u ∈ sbQ.originalSubgroup, orderOf u = 2 →
        ∃ r ∈ rbReps, ∃ c ∈ sbQ.originalSubgroup, u = c * r * c⁻¹ := by
  have h := hC.cover
  simp only [censusCoverCheck, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hn : (276 : ℕ) < 2 ^ 32 := by norm_num
  have hord : ∀ g : Equiv.Perm (Fin 276), ordTest 276 2 (toTable g) = true → orderOf g = 2 :=
    fun g hg => (ordTest_iff perm_faithful (rep_toTable hn g) (by norm_num)).1 hg
  have hT := chain_facts hC
  have htG : ∀ g ∈ tGens, g ∈ tQ.originalSubgroup := fun g hg => by
    rw [tQ, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  have haG : ∀ g ∈ saGens, g ∈ saQ.originalSubgroup := fun g hg => by
    rw [saQ, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  have hbG : ∀ g ∈ sbGens, g ∈ sbQ.originalSubgroup := fun g hg => by
    rw [sbQ, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  have htR : ∀ r ∈ tReps, r ∈ tQ.originalSubgroup ∧ orderOf r = 2 := fun r hr => by
    refine ⟨?_, hord r (h2 r hr)⟩
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    rw [tab_eq]
    exact evalCodes_mem _ htG w
  have hT1 := CFSG.EvenSmallLie.UnitarySix.exists_conj_of_repsOK_normalizing hn tQ hT.1
    tQ.originalSubgroup
    (fun c hc h hh => tQ.originalSubgroup.mul_mem (tQ.originalSubgroup.mul_mem hc hh)
      (tQ.originalSubgroup.inv_mem hc))
    (listTables_spec hn htG) (by norm_num) tReps htR 600 h1
  rw [tQ_eq hC] at hT1
  have hA := CFSG.EvenSmallLie.UnitarySix.exists_conj_of_repsOK_normalizing hn saQ hT.2.2.1
    saQ.originalSubgroup
    (fun c hc h hh => saQ.originalSubgroup.mul_mem (saQ.originalSubgroup.mul_mem hc hh)
      (saQ.originalSubgroup.inv_mem hc))
    (listTables_spec hn haG) (by norm_num) raReps (fun r hr => ⟨by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
      exact evalCodes_mem _ haG w, hord r (h4 r hr)⟩) 600 h3
  have hB := CFSG.EvenSmallLie.UnitarySix.exists_conj_of_repsOK_normalizing hn sbQ hT.2.2.2.2.1
    sbQ.originalSubgroup
    (fun c hc h hh => sbQ.originalSubgroup.mul_mem (sbQ.originalSubgroup.mul_mem hc hh)
      (sbQ.originalSubgroup.inv_mem hc))
    (listTables_spec hn hbG) (by norm_num) rbReps (fun r hr => ⟨by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
      exact evalCodes_mem _ hbG w, hord r (h6 r hr)⟩) 600 h5
  exact ⟨hT1.1, hT1.2, hA.1, hB.1⟩

theorem fusion_facts (hC : CensusChecks) :
    fixCount co3Z = 36 ∧ fixCount xa = 36 ∧ fixCount xb = 12 ∧ xa ≠ co3Z ∧
      (∀ r ∈ tReps, r = co3Z ∨ (∃ g ∈ co3M, g * r * g⁻¹ = xa) ∨ ∃ g ∈ co3M, g * r * g⁻¹ = xb) ∧
      ∀ r ∈ tReps, (fixCount r = 12 → 8 ≤ tSize r) ∧
        (fixCount r = 36 → r ≠ co3Z → 2 ≤ tSize r) := by
  have h := hC.fusion
  rw [← zC_eq hC]
  simp only [censusFusionCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlen, hz⟩, ha⟩, hb⟩, hne⟩, -⟩, -⟩, hfus⟩, hsz⟩ := h
  refine ⟨hz, ha, hb, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, (schreierPermEq_eq_true_iff _ _).2 rfl] at hne
    exact Bool.noConfusion hne
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hi2 : i < fusion.length := by rw [hlen]; exact hi
    have hpair : (tReps[i], fusion[i]) ∈ tReps.zip fusion := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [hlen, hi], by rw [List.getElem_zip]; rfl⟩
    have hmem := List.all_eq_true.1 hfus _ hpair
    generalize fusion[i] = f at hmem
    obtain ⟨t, w⟩ := f
    dsimp only at hmem
    have hg : tab (evalCodes mGens w) ∈ co3M := by
      rw [tab_eq]
      exact evalCodes_mem _ (mGens_mem hC) _
    by_cases h0 : t = 0
    · subst h0
      simp only [↓reduceIte, schreierPermEq_eq_true_iff] at hmem
      exact Or.inl hmem
    · by_cases h1 : t = 1
      · subst h1
        simp only [one_ne_zero, ↓reduceIte, schreierPermEq_eq_true_iff] at hmem
        exact Or.inr (Or.inl ⟨_, hg, hmem⟩)
      · simp only [h0, h1, ↓reduceIte, schreierPermEq_eq_true_iff] at hmem
        exact Or.inr (Or.inr ⟨_, hg, hmem⟩)
  · have e : tReps.zip (repSizes 276 (listTables tGens) (listTables (tGens.map (·⁻¹)))
        (tReps.map toTable) 600) = tReps.map fun r => (r, tSize r) := by
      rw [repSizes, List.map_map, ExcU6.zip_map_self]
      rfl
    rw [e, List.all_map, List.all_eq_true] at hsz
    intro r hr
    have := hsz r hr
    simp only [Function.comp, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq, schreierPermEq_eq_true_iff] at this
    refine ⟨fun h12 => this.1.resolve_left (not_not.2 h12), fun h36 hrz => ?_⟩
    rcases this.2 with (h | h) | h
    · exact absurd h36 h
    · exact absurd h hrz
    · exact h

theorem conj_classes
    (hC : CensusChecks) {y : Equiv.Perm (Fin 276)} (hy : y ∈ co3M)
    (ho : orderOf y = 2) (hyz : y ≠ co3Z) :
    (fixCount y = 36 ∧ ∃ g ∈ co3M, g * y * g⁻¹ = xa) ∨
      (fixCount y = 12 ∧ ∃ g ∈ co3M, g * y * g⁻¹ = xb) := by
  have hz : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho]; norm_num)
  obtain ⟨g, hg, hgT⟩ := exists_conj_le_T hC ((Subgroup.zpowers_le).2 hy) hz
  have hgy : g * y * g⁻¹ ∈ co3T := hgT y (Subgroup.mem_zpowers y)
  have hgo : orderOf (g * y * g⁻¹) = 2 := (MulEquiv.orderOf_eq (MulAut.conj g) y).trans ho
  obtain ⟨r, hr, s, hs, hsr⟩ := (cover_facts hC).1 _ hgy hgo
  obtain ⟨-, fa, fb, -, hfus, -⟩ := fusion_facts hC
  have hsM : s ∈ co3M := co3T_le_co3M hC hs
  have hfy : fixCount y = fixCount r := by
    rw [← fixCount_conj g y, hsr, fixCount_conj]
  rcases hfus r hr with h | ⟨u, hu, hur⟩ | ⟨u, hu, hur⟩
  · exfalso
    apply hyz
    have e1 : g * y * g⁻¹ = co3Z := by
      rw [hsr, h, z_comm_co3M hsM, mul_inv_cancel_right]
    have e2 : y = g⁻¹ * co3Z * g := by rw [← e1]; group
    rw [e2, mul_assoc, ← z_comm_co3M hg, ← mul_assoc, inv_mul_cancel, one_mul]
  · refine Or.inl ⟨by rw [hfy, ← fixCount_conj u r, hur, fa], u * s⁻¹ * g,
      co3M.mul_mem (co3M.mul_mem hu (co3M.inv_mem hsM)) hg, ?_⟩
    rw [← hur]
    have : r = s⁻¹ * (g * y * g⁻¹) * s := by rw [hsr]; group
    rw [this]
    group
  · refine Or.inr ⟨by rw [hfy, ← fixCount_conj u r, hur, fb], u * s⁻¹ * g,
      co3M.mul_mem (co3M.mul_mem hu (co3M.inv_mem hsM)) hg, ?_⟩
    rw [← hur]
    have : r = s⁻¹ * (g * y * g⁻¹) * s := by rw [hsr]; group
    rw [this]
    group

theorem maskProd_mem {X : Subgroup (Equiv.Perm (Fin 276))} :
    ∀ (cur : List (Equiv.Perm (Fin 276))) (m : ℕ), (∀ g ∈ cur, g ∈ X) → maskProd cur m ∈ X
  | [], _, _ => X.one_mem
  | g :: gs, m, h => by
    rw [maskProd]
    refine X.mul_mem ?_ (maskProd_mem gs (m / 2) fun x hx => h x (List.mem_cons_of_mem _ hx))
    split_ifs
    · exact h g List.mem_cons_self
    · exact X.one_mem

theorem badState_eq_false (hC : CensusChecks) {X : Subgroup (Equiv.Perm (Fin 276))}
    (hX : Hyp212In co3M {co3Z} X) {forbid : List ℕ} (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ∉ forbid)
    {cur : List (Equiv.Perm (Fin 276))} (hcur : ∀ g ∈ cur, g ∈ X) :
    badState forbid cur = false := by
  have h1 : ∀ g ∈ cur, schreierPermEq (g * g) 1 = true := fun g hg => by
    rw [schreierPermEq_eq_true_iff, ← sq]
    exact hX.sq_eq_one g (hcur g hg)
  have h2 : ∀ g ∈ cur, ∀ h ∈ cur, schreierPermEq (g * h) (h * g) = true := fun g hg h hh => by
    rw [schreierPermEq_eq_true_iff]
    exact hX.mul_comm (hcur g hg) (hcur h hh)
  have h3 : ∀ m, (!schreierPermEq (tab (maskProd cur m)) 1 &&
      (schreierPermEq (tab (maskProd cur m)) zC ||
        forbid.contains (fixCount (tab (maskProd cur m))))) = false := fun m => by
    rw [tab_eq]
    by_cases hp1 : maskProd cur m = 1
    · rw [hp1]
      have : schreierPermEq (1 : Equiv.Perm (Fin 276)) 1 = true :=
        (schreierPermEq_eq_true_iff _ _).2 rfl
      rw [this]
      rfl
    · have hp := maskProd_mem cur m hcur
      have hz : schreierPermEq (maskProd cur m) zC = false := by
        rw [Bool.eq_false_iff, ne_eq, schreierPermEq_eq_true_iff, zC_eq hC]
        intro h
        exact hX.not_mem co3Z rfl (h ▸ hp)
      have := hf _ hp hp1
      simp [hz, this]
  unfold badState
  rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.any_eq_false]
    intro g hg
    simp [h1 g hg]
  · rw [List.any_eq_false]
    intro g hg
    rw [Bool.not_eq_true, List.any_eq_false]
    intro h hh
    simp [h2 g hg h hh]
  · rw [List.any_eq_false]
    intro m _
    rw [h3 m]
    exact Bool.false_ne_true

theorem derivCheck_eq_false (hC : CensusChecks) {X : Subgroup (Equiv.Perm (Fin 276))}
    (hX : Hyp212In co3M {co3Z} X) {forbid : List ℕ}
    (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ∉ forbid) :
    ∀ (steps : List (ℕ × List ℤ × ℕ)) (cur : List (Equiv.Perm (Fin 276))),
      (∀ g ∈ cur, g ∈ X) → derivCheck forbid cur steps = false
  | [], cur, hcur => by
    rw [derivCheck]
    exact badState_eq_false hC hX hf hcur
  | (m, w, i) :: rest, cur, hcur => by
    rw [derivCheck, badState_eq_false hC hX hf hcur, Bool.false_or]
    dsimp only
    simp only [Bool.and_eq_false_iff]
    by_cases h1 : schreierPermEq (tab (maskProd cur m)) 1 = true
    · exact Or.inl (Or.inl (Or.inl (by simp [h1])))
    by_cases h2 : schreierPermEq (tab (evalCodes mGens w) * tab (maskProd cur m))
        (tab (maskProd cur m) * tab (evalCodes mGens w)) = true
    · by_cases h3 : i < cur.length
      · refine Or.inr (derivCheck_eq_false hC hX hf rest _ fun g hg => ?_)
        rcases List.mem_append.1 hg with hg | hg
        · exact hcur g hg
        · rw [List.mem_singleton] at hg
          rw [hg]
          simp only [tab_eq] at h1 h2 ⊢
          have hp := maskProd_mem cur m hcur
          have hp1 : maskProd cur m ≠ 1 := fun h => h1 (by rw [h, schreierPermEq_eq_true_iff])
          have hc : evalCodes mGens w ∈ co3M := evalCodes_mem _ (mGens_mem hC) w
          have hcw := (schreierPermEq_eq_true_iff _ _).1 h2
          have hb : cur.getD i 1 ∈ X := by
            rw [List.getD_eq_getElem _ _ h3]
            exact hcur _ (List.getElem_mem h3)
          exact hX.conj_mem _ hp hp1 _ hc hcw _ hb
      · exact Or.inl (Or.inr (by simpa using h3))
    · exact Or.inl (Or.inl (Or.inr (by simpa using h2)))

theorem exists_deriv_of_zip {reps : List (Equiv.Perm (Fin 276))}
    {ds : List (List (ℕ × List ℤ × ℕ))} {x : Equiv.Perm (Fin 276)} {forbid : List ℕ}
    (hlen : ds.length = reps.length)
    (hall : (reps.zip ds).all (fun p => schreierPermEq p.1 x || derivCheck forbid [x, p.1] p.2) =
      true) :
    ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck forbid [x, r] st = true := by
  intro r hr hrx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < (reps.zip ds).length := by simp [hlen, hi]
  have h := List.all_eq_true.1 hall _ (List.getElem_mem hi')
  rw [List.getElem_zip] at h
  have hne : schreierPermEq reps[i] x = false := by
    rw [Bool.eq_false_iff, ne_eq, schreierPermEq_eq_true_iff]
    exact hrx
  rw [hne, Bool.false_or] at h
  exact ⟨_, h⟩

theorem deriv_facts (hC : CensusChecks) :
    (∀ r ∈ raReps, r ≠ xa → ∃ st, derivCheck [12] [xa, r] st = true) ∧
      ∀ r ∈ rbReps, r ≠ xb → ∃ st, derivCheck [] [xb, r] st = true := by
  have h := hC.deriv
  simp only [censusDerivCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨exists_deriv_of_zip h1 h3, exists_deriv_of_zip h2 h4⟩

theorem sa_le_T (hC : CensusChecks) : saQ.originalSubgroup ≤ co3T := by
  rw [saQ, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  rw [SetLike.mem_coe, tab_eq]
  exact evalCodes_mem _ (tGens_mem hC) w

theorem sb_le_T (hC : CensusChecks) : sbQ.originalSubgroup ≤ co3T := by
  rw [sbQ, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  rw [SetLike.mem_coe, tab_eq]
  exact evalCodes_mem _ (tGens_mem hC) w

theorem sa_le_centralizer (hC : CensusChecks) :
    saQ.originalSubgroup ≤ Subgroup.centralizer {xa} := by
  rw [saQ, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (chain_facts hC).2.2.2.2.2.2.2.1 g hg

theorem sb_le_centralizer (hC : CensusChecks) :
    sbQ.originalSubgroup ≤ Subgroup.centralizer {xb} := by
  rw [sbQ, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (chain_facts hC).2.2.2.2.2.2.2.2 g hg

theorem card_sa (hC : CensusChecks) : Nat.card saQ.originalSubgroup = 512 := by
  rw [← saQ.orderCertificate_eq_card (chain_facts hC).2.2.1, (chain_facts hC).2.2.2.1]

theorem card_sb (hC : CensusChecks) : Nat.card sbQ.originalSubgroup = 128 := by
  rw [← sbQ.orderCertificate_eq_card (chain_facts hC).2.2.2.2.1, (chain_facts hC).2.2.2.2.2.1]

theorem exists_conj_le_of_card_le' {K S X : Subgroup (Equiv.Perm (Fin 276))} (hSK : S ≤ K)
    (hS : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup (Equiv.Perm (Fin 276)), R ≤ K → IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    (hXK : X ≤ K) (hX : IsPGroup 2 X) : ∃ c ∈ K, ∀ x ∈ X, c * x * c⁻¹ ∈ S := by
  have hS' : IsPGroup 2 (S.subgroupOf K) := hS.comap_of_injective K.subtype K.subtype_injective
  have hX' : IsPGroup 2 (X.subgroupOf K) := hX.comap_of_injective K.subtype K.subtype_injective
  have hcardS : Nat.card (S.subgroupOf K) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
  have hmax' : ∀ R : Subgroup K, IsPGroup 2 R → Nat.card R ≤ Nat.card (S.subgroupOf K) := by
    intro R hR
    rw [hcardS, ← Subgroup.card_map_of_injective K.subtype_injective]
    exact hmax _ (by rintro _ ⟨y, -, rfl⟩; exact y.2) (hR.map K.subtype)
  obtain ⟨c, hc⟩ := ExcU6.exists_conj_le_of_card_le hS' hmax' hX'
  refine ⟨c, c.2, fun x hx => ?_⟩
  have := hc ⟨x, hXK hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem card_le_of_commute
    (hC : CensusChecks) {x : Equiv.Perm (Fin 276)} (hx : x ∈ co3M)
    (hxo : orderOf x = 2) (hxz : x ≠ co3Z) {R : Subgroup (Equiv.Perm (Fin 276))}
    (hRM : R ≤ co3M) (hRx : ∀ r ∈ R, r * x = x * r) (hR : IsPGroup 2 R) {m : ℕ}
    (hm : ∀ r ∈ tReps, fixCount r = fixCount x → r ≠ co3Z → m ≤ tSize r) :
    Nat.card R * m ≤ 1024 := by
  have hz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hcomm : ∀ r ∈ R, ∀ k : ℤ, r * x ^ k * r⁻¹ = x ^ k := fun r hr k => by
    have hc : Commute r x := hRx r hr
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  have hnorm : R ≤ Subgroup.normalizer (Subgroup.zpowers x : Set (Equiv.Perm (Fin 276))) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact Subgroup.mem_zpowers_iff.2 ⟨k, (hcomm r hr k).symm⟩
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      calc x ^ k = r⁻¹ * (r * x ^ k * r⁻¹) * r := by group
        _ = r⁻¹ * x ^ k * r := by rw [hcomm r hr k]
        _ = r⁻¹ * (r * y * r⁻¹) * r := by rw [hk]
        _ = y := by group
  have hQ := IsPGroup.to_sup_of_normal_right' hR hz hnorm
  have hQM : R ⊔ Subgroup.zpowers x ≤ co3M := sup_le hRM ((Subgroup.zpowers_le).2 hx)
  obtain ⟨g, hg, hgQ⟩ := exists_conj_le_T hC hQM hQ
  set y := g * x * g⁻¹ with hy
  have hyT : y ∈ co3T := hgQ x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hyo : orderOf y = 2 := (MulEquiv.orderOf_eq (MulAut.conj g) x).trans hxo
  have hyz : y ≠ co3Z := by
    intro h
    apply hxz
    have e : x = g⁻¹ * co3Z * g := by rw [← h, hy]; group
    rw [e, mul_assoc, ← z_comm_co3M hg, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨hcov, hsize, -, -⟩ := cover_facts hC
  obtain ⟨r, hr, c, hc, hyr⟩ := hcov y hyT hyo
  have hcM : c ∈ co3M := co3T_le_co3M hC hc
  have hrz : r ≠ co3Z := by
    intro h
    apply hyz
    rw [hyr, h, z_comm_co3M hcM, mul_inv_cancel_right]
  have hfr : fixCount r = fixCount x := by
    rw [← fixCount_conj c r, ← hyr, hy, fixCount_conj]
  have hmr := (hm r hr hfr hrz).trans (hsize r hr)
  have hcls : conjClass co3T y = conjClass co3T r := by
    rw [hyr]
    exact conjClass_conj co3T hc r
  have hcard := ncard_conjClass_mul_card co3T y
  rw [card_co3T, hcls] at hcard
  have hle : Nat.card R ≤ Nat.card (centralizerIn co3T y) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizerIn]
    refine ⟨hgQ q (Subgroup.mem_sup_left hq), ?_⟩
    change g * q * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * q * g⁻¹)
    have := hRx q hq
    calc g * q * g⁻¹ * (g * x * g⁻¹) = g * (q * x) * g⁻¹ := by group
      _ = g * (x * q) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * q * g⁻¹) := by group
  calc Nat.card R * m ≤ Nat.card (centralizerIn co3T y) * (conjClass co3T r).ncard :=
        Nat.mul_le_mul hle hmr
    _ = 1024 := by rw [mul_comm]; exact hcard

theorem false_of_pair
    (hC : CensusChecks) {x : Equiv.Perm (Fin 276)}
    {S : Subgroup (Equiv.Perm (Fin 276))} {reps : List (Equiv.Perm (Fin 276))} {forbid : List ℕ}
    (hS : S ≤ co3M ⊓ Subgroup.centralizer {x}) (hS2 : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup (Equiv.Perm (Fin 276)), R ≤ co3M ⊓ Subgroup.centralizer {x} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    (hcov : ∀ u ∈ S, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ S, u = c * r * c⁻¹)
    (hder : ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck forbid [x, r] st = true)
    {X : Subgroup (Equiv.Perm (Fin 276))} (hX : Hyp212In co3M {co3Z} X) (hx : x ∈ X)
    (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ∉ forbid) : False := by
  have hZc : ∀ g ∈ co3M, ∀ z ∈ ({co3Z} : Set (Equiv.Perm (Fin 276))), g * z * g⁻¹ = z := by
    rintro g hg z rfl
    rw [z_comm_co3M hg, mul_inv_cancel_right]
  have hXC : X ≤ co3M ⊓ Subgroup.centralizer {x} := fun y hy =>
    ⟨hX.le hy, Subgroup.mem_centralizer_singleton_iff.2 (hX.mul_comm hy hx)⟩
  have hX2 : IsPGroup 2 X := by
    refine IsPGroup.of_exponent_dvd_pow (n := 1) (Monoid.exponent_dvd_of_forall_pow_eq_one ?_)
    intro g
    rw [pow_one]
    exact Subtype.ext (hX.sq_eq_one g g.2)
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_card_le' hS hS2 hmax hXC hX2
  have hcx : c * x * c⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hcC.2, mul_inv_cancel_right]
  have hX₂ := hX.conj hcC.1 (hZc c hcC.1)
  have hx₂ : x ∈ X.map (MulAut.conj c).toMonoidHom := ⟨x, hx, hcx⟩
  have hX₂S : X.map (MulAut.conj c).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  have hf₂ : ∀ y ∈ X.map (MulAut.conj c).toMonoidHom, y ≠ 1 → fixCount y ∉ forbid := by
    rintro _ ⟨y, hy, rfl⟩ hy1
    change fixCount (c * y * c⁻¹) ∉ forbid
    rw [fixCount_conj]
    exact hf y hy fun h => hy1 (by rw [h, map_one])
  obtain ⟨y, hy, hy1, hyx⟩ : ∃ y ∈ X.map (MulAut.conj c).toMonoidHom, y ≠ 1 ∧ y ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : ((X.map (MulAut.conj c).toMonoidHom : Subgroup (Equiv.Perm (Fin 276))) :
        Set (Equiv.Perm (Fin 276))) ⊆ {1, x} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hcon y hy h1)
    have h4 := hX₂.four_le
    have h2 : ({1, x} : Set (Equiv.Perm (Fin 276))).ncard ≤ 2 := by
      calc ({1, x} : Set (Equiv.Perm (Fin 276))).ncard
          ≤ ({x} : Set (Equiv.Perm (Fin 276))).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq] at h3
    change Nat.card (X.map (MulAut.conj c).toMonoidHom) ≤ _ at h3
    omega
  have hyo : orderOf y = 2 := orderOf_eq_prime (hX₂.sq_eq_one y hy) hy1
  obtain ⟨r, hr, s, hs, hysr⟩ := hcov y (hX₂S hy) hyo
  have hsM : s ∈ co3M := (hS hs).1
  have hsx : s⁻¹ * x * s⁻¹⁻¹ = x := by
    have e := Subgroup.mem_centralizer_singleton_iff.1 (hS hs).2
    calc s⁻¹ * x * s⁻¹⁻¹ = s⁻¹ * (x * s) := by group
      _ = s⁻¹ * (s * x) := by rw [e]
      _ = x := by group
  have hsx' : s * x * s⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (hS hs).2, mul_inv_cancel_right]
  have hX₃ := hX₂.conj (co3M.inv_mem hsM) (hZc _ (co3M.inv_mem hsM))
  have hx₃ : x ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
    ⟨x, hx₂, hsx⟩
  have hr₃ : r ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by
    refine ⟨y, hy, ?_⟩
    change s⁻¹ * y * s⁻¹⁻¹ = r
    rw [hysr]
    group
  have hf₃ : ∀ z ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom,
      z ≠ 1 → fixCount z ∉ forbid := by
    rintro _ ⟨z, hz, rfl⟩ hz1
    change fixCount (s⁻¹ * z * s⁻¹⁻¹) ∉ forbid
    rw [fixCount_conj]
    exact hf₂ z hz fun h => hz1 (by rw [h, map_one])
  have hrx : r ≠ x := fun h => hyx (by rw [hysr, h, hsx'])
  obtain ⟨st, hst⟩ := hder r hr hrx
  have hfalse := derivCheck_eq_false hC hX₃ hf₃ st [x, r] (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hx₃
    · exact hr₃)
  rw [hst] at hfalse
  exact Bool.noConfusion hfalse

theorem x_facts
    (hC : CensusChecks) :
    xa ∈ co3M ∧ orderOf xa = 2 ∧ xa ≠ co3Z ∧ xb ∈ co3M ∧ orderOf xb = 2 ∧ xb ≠ co3Z := by
  have h := hC.fusion
  simp only [censusFusionCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hoa⟩, hob⟩, -⟩, -⟩ := h
  obtain ⟨hz36, -, hb12, hxaz, -, -⟩ := fusion_facts hC
  have hn : (276 : ℕ) < 2 ^ 32 := by norm_num
  have hxa : xa ∈ co3T := by rw [xa, tab_eq]; exact evalCodes_mem _ (tGens_mem hC) _
  have hxb : xb ∈ co3T := by rw [xb, tab_eq]; exact evalCodes_mem _ (tGens_mem hC) _
  refine ⟨co3T_le_co3M hC hxa, (ordTest_iff perm_faithful (rep_toTable hn xa) (by norm_num)).1 hoa,
    hxaz, co3T_le_co3M hC hxb, (ordTest_iff perm_faithful (rep_toTable hn xb) (by norm_num)).1 hob,
    fun h => ?_⟩
  rw [h, hz36] at hb12
  exact absurd hb12 (by norm_num)

theorem false_of_xa
    (hC : CensusChecks) {X : Subgroup (Equiv.Perm (Fin 276))}
    (hX : Hyp212In co3M {co3Z} X) (hx : xa ∈ X) (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ≠ 12) :
    False := by
  obtain ⟨hxM, hxo, hxz, -, -, -⟩ := x_facts hC
  obtain ⟨-, fa, -, -, -, hsz⟩ := fusion_facts hC
  have hmax : ∀ R : Subgroup (Equiv.Perm (Fin 276)), R ≤ co3M ⊓ Subgroup.centralizer {xa} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card saQ.originalSubgroup := by
    intro R hR hR2
    have h := card_le_of_commute (m := 2) hC hxM hxo hxz (fun r hr => (hR hr).1)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hR hr).2) hR2
      (fun r hr hfr hrz => (hsz r hr).2 (hfr.trans fa) hrz)
    rw [card_sa hC]
    omega
  exact false_of_pair (forbid := [12]) hC
    (fun s hs => ⟨co3T_le_co3M hC (sa_le_T hC hs), sa_le_centralizer hC hs⟩)
    (IsPGroup.of_card (n := 9) (by rw [card_sa hC]; norm_num)) hmax (cover_facts hC).2.2.1
    (deriv_facts hC).1 hX hx fun y hy hy1 => by simpa using hf y hy hy1

theorem false_of_xb
    (hC : CensusChecks) {X : Subgroup (Equiv.Perm (Fin 276))}
    (hX : Hyp212In co3M {co3Z} X) (hx : xb ∈ X) : False := by
  obtain ⟨-, -, -, hxM, hxo, hxz⟩ := x_facts hC
  obtain ⟨-, -, fb, -, -, hsz⟩ := fusion_facts hC
  have hmax : ∀ R : Subgroup (Equiv.Perm (Fin 276)), R ≤ co3M ⊓ Subgroup.centralizer {xb} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card sbQ.originalSubgroup := by
    intro R hR hR2
    have h := card_le_of_commute (m := 8) hC hxM hxo hxz (fun r hr => (hR hr).1)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hR hr).2) hR2
      (fun r hr hfr _ => (hsz r hr).1 (hfr.trans fb))
    rw [card_sb hC]
    omega
  exact false_of_pair (forbid := []) hC
    (fun s hs => ⟨co3T_le_co3M hC (sb_le_T hC hs), sb_le_centralizer hC hs⟩)
    (IsPGroup.of_card (n := 7) (by rw [card_sb hC]; norm_num)) hmax (cover_facts hC).2.2.2
    (deriv_facts hC).2 hX hx fun _ _ _ => List.not_mem_nil

theorem not_hyp212In_co3M
    (hC : CensusChecks) (X : Subgroup (Equiv.Perm (Fin 276))) :
    ¬ Hyp212In co3M {co3Z} X := by
  intro hX
  have hZc : ∀ g ∈ co3M, ∀ z ∈ ({co3Z} : Set (Equiv.Perm (Fin 276))), g * z * g⁻¹ = z := by
    rintro g hg z rfl
    rw [z_comm_co3M hg, mul_inv_cancel_right]
  have hinv : ∀ y ∈ X, y ≠ 1 → y ∈ co3M ∧ orderOf y = 2 ∧ y ≠ co3Z := fun y hy hy1 =>
    ⟨hX.le hy, orderOf_eq_prime (hX.sq_eq_one y hy) hy1, fun h => hX.not_mem co3Z rfl (h ▸ hy)⟩
  have hconj_ne : ∀ {g z : Equiv.Perm (Fin 276)}, g * z * g⁻¹ ≠ 1 → z ≠ 1 := fun h hz =>
    h (by rw [hz, mul_one, mul_inv_cancel])
  by_cases hb : ∃ y ∈ X, y ≠ 1 ∧ fixCount y = 12
  · obtain ⟨y, hy, hy1, hfy⟩ := hb
    obtain ⟨hyM, hyo, hyz⟩ := hinv y hy hy1
    rcases conj_classes hC hyM hyo hyz with ⟨h, -⟩ | ⟨-, g, hg, hgy⟩
    · rw [hfy] at h
      exact absurd h (by norm_num)
    · exact false_of_xb hC (hX.conj hg (hZc g hg)) ⟨y, hy, hgy⟩
  push Not at hb
  have hne : X ≠ ⊥ := by
    intro h
    have h4 := hX.four_le
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨hyM, hyo, hyz⟩ := hinv y hy hy1'
  rcases conj_classes hC hyM hyo hyz with ⟨-, g, hg, hgy⟩ | ⟨h, -⟩
  · refine false_of_xa hC (hX.conj hg (hZc g hg)) ⟨y, hy, hgy⟩ ?_
    rintro _ ⟨z, hz, rfl⟩ hz1
    change fixCount (g * z * g⁻¹) ≠ 12
    rw [fixCount_conj]
    exact hb z hz (hconj_ne hz1)
  · exact hb y hy hy1' h

end CFSG.ComponentClassification.RankTwoClassical.ExcSp6

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.RankThree.PerfectCover CFSG.Sporadic.Schreier.Co3

theorem exc213_PSp_three_of
    (hC : ExcSp6.CensusChecks) : Exc213 .PSp 3 := by
  intro H _ _ hq heven hL P hP
  have hperf : Group.IsPerfect H := Group.isPerfect_def.2 hq.1
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.EvenSmallLie.SympSix.multiplier_PSp_three_two_one _ hL
  have hZ2 : Nat.card (center H) = 2 := by
    let q : H →* H ⧸ center H := QuotientGroup.mk' (center H)
    have hq' : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hker : q.ker = center H := QuotientGroup.ker_mk' _
    have hmap := map_hopfMultiplier_hopfLift q hq' hker.le
    have hdvd : Nat.card (center H) ∣ 2 := by
      have h := Subgroup.card_map_dvd (H := hopfMultiplier (H ⧸ center H))
        (hopfLift q hq' hker.le)
      rw [hmap, hker, ← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv,
        Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
      exact h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · rw [h] at heven
      exact absurd heven (by decide)
    · exact h
  obtain ⟨θ, hθ⟩ := CFSG.EvenSmallLie.SympSix.sp62_double_cover_unique H hq.1 hZ2 hL
  refine ExcSp6.not_hyp212In_co3M hC _ (hP.hyp212In_map θ.symm ?_)
  rintro z rfl
  refine ⟨co3Z_mem_M, co3Z_ne_one, ?_⟩
  rw [MulEquiv.symm_symm, hθ]
  exact Subgroup.mem_zpowers _

theorem exc213_PSp_three :
    Exc213 .PSp 3 :=
  exc213_PSp_three_of ⟨ExcSp6.census_arr_check, ExcSp6.census_chain_check,
    ExcSp6.census_cover_check, ExcSp6.census_fusion_check, ExcSp6.census_deriv_check⟩

end CFSG.ComponentClassification.RankTwoClassical
