module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge

public section

namespace CFSG.ComponentClassification.J2Cover.External

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem chainCheck_parts :
    rawChainOK 315 (fixCStrong.extract 0 2) fixCStrong fixCBase fixCWords 4 = true ∧
    rawOrbitSizes 315 fixCStrong fixCBase = [21, 16] ∧
    inP fixCStrong[0]! = true ∧ inP fixCStrong[1]! = true ∧
    commA fixCStrong[0]! Models.bArr = true ∧ commA fixCStrong[1]! Models.bArr = true ∧
    rawChainOK 315 (fixDStrong.extract 0 2) fixDStrong fixDBase fixDWords 4 = true ∧
    rawOrbitSizes 315 fixDStrong fixDBase = [168] ∧
    inC fixDStrong[0]! = true ∧ inC fixDStrong[1]! = true ∧
    rawChainOK 315 (fixWStrong.extract 0 2) fixWStrong fixWBase fixWWords 4 = true ∧
    rawOrbitSizes 315 fixWStrong fixWBase = [8] ∧
    inD fixWStrong[0]! = true ∧ inD fixWStrong[1]! = true := by
  have h := chainCheck_eq
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem tableCheck_parts :
    ordTest 315 2 tblX = true ∧ ordTest 315 3 tblY = true ∧
    pairTest 315 7 4 2 3 tblX tblY = true ∧
    (dOrderTables 2).length = 21 ∧ (dOrderTables 2).all (fun T => tblFix T == 11) = true ∧
    pairCount (dOrderTables 2) (dOrderTables 3) (fun x y => ordW 315 [x, y] 7) = 336 ∧
    pairCount (dOrderTables 2) (dOrderTables 3) (pairTest 315 7 4 2 3) = 336 ∧
    countProducts 315 (commAll 315 [tblX, tblY]) (chainTables 315 fixCStrong fixCBase)
      (idT 315) = 1 := by
  have h := tableCheck_eq
  simp only [tableCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem elemCheck_parts :
    ordTest 315 4 (arrTable 315 fixWStrong[0]!) = true ∧
    ordTest 315 2 (arrTable 315 fixWStrong[1]!) = true ∧
    isInvA 315 fixWStrong[0]! (invCand 315 fixWStrong[0]!) = true ∧
    eqA 315 (compA 315 fixWStrong[1]! (compA 315 fixWStrong[0]! fixWStrong[1]!))
      (invCand 315 fixWStrong[0]!) = true ∧
    eqA 315 fixWStrong[1]! (compA 315 fixWStrong[0]! fixWStrong[0]!) = false ∧
    invoList 315 fusionArr = true ∧ movesList 315 fusionArr = true ∧
    fixedCount 315 fusionArr = 15 ∧ inC fusionArr = true ∧ inD fusionArr = false ∧
    (∀ k < 4, isInvA 315 commArrs[k]! (invCand 315 commArrs[k]!) = true ∧
      inD commArrs[k]! = true) ∧
    eqA 315 fixDStrong[0]! (commArr commArrs[0]! commArrs[1]!) = true ∧
    eqA 315 fixDStrong[1]! (commArr commArrs[2]! commArrs[3]!) = true := by
  have h := elemCheck_eq
  simp only [elemCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', allLt_iff,
    and_assoc] at h
  exact h

theorem lamCheck_parts :
    (∀ i < 4725, fusionP[i]! < 128 ∧ fusionI[i]! < 4725 ∧
      eqA 315 (compA 315 Models.repArrs[i]! fusionArr)
        (compA 315 Models.eltArrs[fusionP[i]!]! Models.repArrs[fusionI[i]!]!) = true) ∧
    Models.xorFold 4725 fusionBit = true := by
  have h := lamCheck_eq
  simp only [lamCheck, Bool.and_eq_true, allLt_iff, decide_eq_true_eq, and_assoc] at h
  exact h

@[expose] noncomputable def chainC : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) fixCStrong 2 (by decide) [0, 1] (by decide)
    fixCWords

@[expose] noncomputable def chainD : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) fixDStrong 2 (by decide) [1] (by decide) fixDWords

@[expose] noncomputable def chainW : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) fixWStrong 2 (by decide) [1] (by decide) fixWWords

theorem fixCBase_eq : (([0, 1] : List (Fin 315)).map Fin.val).toArray = fixCBase := rfl

theorem fixDBase_eq : (([1] : List (Fin 315)).map Fin.val).toArray = fixDBase := rfl

theorem fixWBase_eq : (([1] : List (Fin 315)).map Fin.val).toArray = fixWBase := rfl

theorem chainC_ok : rawChainOK 315 (fixCStrong.extract 0 2) fixCStrong
    (([0, 1] : List (Fin 315)).map Fin.val).toArray fixCWords 4 = true := by
  rw [fixCBase_eq]
  exact chainCheck_parts.1

theorem chainD_ok : rawChainOK 315 (fixDStrong.extract 0 2) fixDStrong
    (([1] : List (Fin 315)).map Fin.val).toArray fixDWords 4 = true := by
  rw [fixDBase_eq]
  exact chainCheck_parts.2.2.2.2.2.2.1

theorem chainW_ok : rawChainOK 315 (fixWStrong.extract 0 2) fixWStrong
    (([1] : List (Fin 315)).map Fin.val).toArray fixWWords 4 = true := by
  rw [fixWBase_eq]
  exact chainCheck_parts.2.2.2.2.2.2.2.2.2.2.1

theorem chainC_valid : ValidSchreier chainC := ofArrays_valid (by norm_num) chainC_ok

theorem chainD_valid : ValidSchreier chainD := ofArrays_valid (by norm_num) chainD_ok

theorem chainW_valid : ValidSchreier chainW := ofArrays_valid (by norm_num) chainW_ok

theorem card_QC : Nat.card chainC.originalSubgroup = 336 := by
  rw [chainC, ofArrays_card (by norm_num) chainC_ok, fixCBase_eq, chainCheck_parts.2.1]
  rfl

theorem card_QD : Nat.card chainD.originalSubgroup = 168 := by
  rw [chainD, ofArrays_card (by norm_num) chainD_ok, fixDBase_eq,
    chainCheck_parts.2.2.2.2.2.2.2.1]
  rfl

theorem card_QW : Nat.card chainW.originalSubgroup = 8 := by
  rw [chainW, ofArrays_card (by norm_num) chainW_ok, fixWBase_eq,
    chainCheck_parts.2.2.2.2.2.2.2.2.2.2.2.1]
  rfl

theorem mem_QC_iff {t : Array ℕ} {g : Equiv.Perm (Fin 315)} (h : Rep 315 t g) :
    inC t = true ↔ g ∈ chainC.originalSubgroup := by
  have key := ofArrays_mem_iff (hn := by norm_num) (hk := by decide) (hb := by decide)
    (by norm_num) chainC_ok h
  rw [fixCBase_eq] at key
  exact key

theorem mem_QD_iff {t : Array ℕ} {g : Equiv.Perm (Fin 315)} (h : Rep 315 t g) :
    inD t = true ↔ g ∈ chainD.originalSubgroup := by
  have key := ofArrays_mem_iff (hn := by norm_num) (hk := by decide) (hb := by decide)
    (by norm_num) chainD_ok h
  rw [fixDBase_eq] at key
  exact key

theorem levelTables_chainC : levelTables chainC = chainTables 315 fixCStrong fixCBase := by
  rw [chainC, ofArrays_levelTables chainC_ok, fixCBase_eq]

theorem levelTables_chainD : levelTables chainD = chainTables 315 fixDStrong fixDBase := by
  rw [chainD, ofArrays_levelTables chainD_ok, fixDBase_eq]

theorem orderTables_chainD (m : ℕ) : orderTables chainD m = dOrderTables m := by
  rw [orderTables, levelTables_chainD]
  rfl

theorem ofArrays_two {hn : 1 ≤ 315} {S : Array (Array ℕ)} {hk : 2 ≤ S.size} {base : List (Fin 315)}
    {hb : base.Nodup} {W : Array (List ℤ)} :
    (RawSchreierDatum.ofArrays 315 hn S 2 hk base hb W).originalSubgroup =
      Subgroup.closure {permOfArr 315 S[0]!, permOfArr 315 S[1]!} := by
  rw [ofArrays_originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

@[expose] noncomputable def permX : Equiv.Perm (Fin 315) := permOfArr 315 fixDStrong[0]!

@[expose] noncomputable def permY : Equiv.Perm (Fin 315) := permOfArr 315 fixDStrong[1]!

@[expose] noncomputable def permR : Equiv.Perm (Fin 315) := permOfArr 315 fixWStrong[0]!

@[expose] noncomputable def permS : Equiv.Perm (Fin 315) := permOfArr 315 fixWStrong[1]!

@[expose] noncomputable def permC : Equiv.Perm (Fin 315) := permOfArr 315 fusionArr

@[expose] noncomputable def permK (k : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 commArrs[k]!

theorem rep_permX : Rep 315 fixDStrong[0]! permX :=
  rep_permOfArr_of_chainOK chainD_ok (j := 0) (by decide)

theorem rep_permY : Rep 315 fixDStrong[1]! permY :=
  rep_permOfArr_of_chainOK chainD_ok (j := 1) (by decide)

theorem rep_permR : Rep 315 fixWStrong[0]! permR :=
  rep_permOfArr_of_chainOK chainW_ok (j := 0) (by decide)

theorem rep_permS : Rep 315 fixWStrong[1]! permS :=
  rep_permOfArr_of_chainOK chainW_ok (j := 1) (by decide)

theorem rep_permC : Rep 315 fusionArr permC :=
  (rep_permOfArr (isInvA_of_invoList elemCheck_parts.2.2.2.2.2.1)).1

theorem rep_permK {k : ℕ} (hk : k < 4) : Rep 315 commArrs[k]! (permK k) :=
  (rep_permOfArr (elemCheck_parts.2.2.2.2.2.2.2.2.2.2.1 k hk).1).1

theorem rep_permK_inv {k : ℕ} (hk : k < 4) : Rep 315 (invCand 315 commArrs[k]!) (permK k)⁻¹ :=
  (rep_permOfArr (elemCheck_parts.2.2.2.2.2.2.2.2.2.2.1 k hk).1).2

theorem chainC_eq : chainC.originalSubgroup =
    Subgroup.closure {permOfArr 315 fixCStrong[0]!, permOfArr 315 fixCStrong[1]!} := ofArrays_two

theorem chainD_eq : chainD.originalSubgroup = Subgroup.closure {permX, permY} := ofArrays_two

theorem chainW_eq : chainW.originalSubgroup = Subgroup.closure {permR, permS} := ofArrays_two

theorem rep_strongC {j : ℕ} (hj : j < 2) :
    Rep 315 fixCStrong[j]! (permOfArr 315 fixCStrong[j]!) :=
  rep_permOfArr_of_chainOK chainC_ok (by
    have : fixCStrong.size = 4 := rfl
    omega)

theorem QC_le_P : chainC.originalSubgroup ≤ P := by
  rw [chainC_eq, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact (mem_P_iff (rep_strongC (j := 0) (by norm_num))).1 chainCheck_parts.2.2.1
  · exact (mem_P_iff (rep_strongC (j := 1) (by norm_num))).1 chainCheck_parts.2.2.2.1

theorem QD_le_QC : chainD.originalSubgroup ≤ chainC.originalSubgroup := by
  rw [chainD_eq, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact (mem_QC_iff rep_permX).1 chainCheck_parts.2.2.2.2.2.2.2.2.1
  · exact (mem_QC_iff rep_permY).1 chainCheck_parts.2.2.2.2.2.2.2.2.2.1

theorem QW_le_QD : chainW.originalSubgroup ≤ chainD.originalSubgroup := by
  rw [chainW_eq, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact (mem_QD_iff rep_permR).1 chainCheck_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact (mem_QD_iff rep_permS).1 chainCheck_parts.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem QC_le_centralizerIn :
    chainC.originalSubgroup ≤ centralizerIn P (permB * permU * permB⁻¹) := by
  rw [chainC_eq, Subgroup.closure_le, ← Models.bOut_eq_permU]
  rintro g (rfl | rfl)
  · refine mem_centralizerIn.2
      ⟨(mem_P_iff (rep_strongC (j := 0) (by norm_num))).1 chainCheck_parts.2.2.1, ?_⟩
    exact eq_of_eqA (rep_compA (rep_strongC (j := 0) (by norm_num)) Models.rep_bArr)
      (rep_compA Models.rep_bArr (rep_strongC (j := 0) (by norm_num))) chainCheck_parts.2.2.2.2.1
  · refine mem_centralizerIn.2
      ⟨(mem_P_iff (rep_strongC (j := 1) (by norm_num))).1 chainCheck_parts.2.2.2.1, ?_⟩
    exact eq_of_eqA (rep_compA (rep_strongC (j := 1) (by norm_num)) Models.rep_bArr)
      (rep_compA Models.rep_bArr (rep_strongC (j := 1) (by norm_num)))
      chainCheck_parts.2.2.2.2.2.1

theorem card_centralizerIn_b : Nat.card (centralizerIn P (permB * permU * permB⁻¹)) = 336 := by
  rw [centralizerIn_conj P permB_mem permU,
    Subgroup.card_map_of_injective (MulAut.conj permB).injective, outer_classes.2.2]
  exact centOuter_facts.2.1

theorem QC_eq_centralizerIn :
    chainC.originalSubgroup = centralizerIn P (permB * permU * permB⁻¹) :=
  Subgroup.eq_of_le_of_card_ge QC_le_centralizerIn (by rw [card_centralizerIn_b, card_QC])

theorem permK_mem_QD {k : ℕ} (hk : k < 4) : permK k ∈ chainD.originalSubgroup :=
  (mem_QD_iff (rep_permK hk)).1 (elemCheck_parts.2.2.2.2.2.2.2.2.2.2.1 k hk).2

theorem rep_commArr {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    Rep 315 (commArr commArrs[i]! commArrs[j]!) ⁅permK i, permK j⁆ := by
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  exact rep_compA (rep_permK hi) (rep_compA (rep_permK hj)
    (rep_compA (rep_permK_inv hi) (rep_permK_inv hj)))

theorem permX_eq : permX = ⁅permK 0, permK 1⁆ :=
  eq_of_eqA rep_permX (rep_commArr (by norm_num) (by norm_num))
    elemCheck_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem permY_eq : permY = ⁅permK 2, permK 3⁆ :=
  eq_of_eqA rep_permY (rep_commArr (by norm_num) (by norm_num))
    elemCheck_parts.2.2.2.2.2.2.2.2.2.2.2.2

theorem commutator_QD : ⁅chainD.originalSubgroup, chainD.originalSubgroup⁆ =
    chainD.originalSubgroup := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  conv_lhs => rw [chainD_eq]
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · rw [permX_eq]
    exact Subgroup.commutator_mem_commutator (permK_mem_QD (by norm_num))
      (permK_mem_QD (by norm_num))
  · rw [permY_eq]
    exact Subgroup.commutator_mem_commutator (permK_mem_QD (by norm_num))
      (permK_mem_QD (by norm_num))

theorem commutator_le_of_index_two {G : Type*} [Group G] {C D : Subgroup G}
    (hidx : (D.subgroupOf C).index = 2) : ⁅C, C⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have key : ⁅(⟨g, hg⟩ : C), ⟨h, hh⟩⁆ ∈ D.subgroupOf C := by
    rw [commutatorElement_def, mul_assoc _ (⟨g, hg⟩ : C)⁻¹,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  rwa [Subgroup.mem_subgroupOf] at key

theorem index_QD_QC : (chainD.originalSubgroup.subgroupOf chainC.originalSubgroup).index = 2 := by
  have h := (chainD.originalSubgroup.subgroupOf chainC.originalSubgroup).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QD_le_QC).toEquiv, card_QD, card_QC] at h
  omega

theorem commutator_QC : ⁅chainC.originalSubgroup, chainC.originalSubgroup⁆ =
    chainD.originalSubgroup :=
  le_antisymm (commutator_le_of_index_two index_QD_QC)
    (commutator_QD.symm.le.trans (Subgroup.commutator_mono QD_le_QC QD_le_QC))

theorem eq_one_of_countProducts {Q : RawSchreierDatum 315} (hQ : ValidSchreier Q)
    {a b : Equiv.Perm (Fin 315)}
    (h : countProducts 315 (commAll 315 [toTable a, toTable b]) (levelTables Q) (idT 315) = 1)
    {g : Equiv.Perm (Fin 315)} (hg : g ∈ Q.originalSubgroup) (hga : g * a = a * g)
    (hgb : g * b = b * g) : g = 1 := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have hspec := countProducts_spec
    (P := fun y : Equiv.Perm (Fin 315) => y * a = a * y ∧ y * b = b * y)
    (f := commAll 315 [toTable a, toTable b]) (fun T y hT => by
      simp only [commAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      rw [commT_iff hT (rep_toTable hn a), commT_iff hT (rep_toTable hn b)])
    (forall₂_levelTables hn Q) (CFSG.Sporadic.Th.Rep.idT hn)
  rw [h] at hspec
  simp only [one_mul, List.map_id'] at hspec
  change 1 = (enumeration Q).countP _ at hspec
  rw [List.countP_eq_length_filter, eq_comm, List.length_eq_one_iff] at hspec
  obtain ⟨w, hw⟩ := hspec
  have h1 : (1 : Equiv.Perm (Fin 315)) ∈ (enumeration Q).filter
      (fun y => decide (y * a = a * y ∧ y * b = b * y)) :=
    List.mem_filter.2 ⟨(mem_enumeration_iff Q hQ 1).2 (one_mem _), by simp⟩
  have h2 : g ∈ (enumeration Q).filter (fun y => decide (y * a = a * y ∧ y * b = b * y)) :=
    List.mem_filter.2 ⟨(mem_enumeration_iff Q hQ g).2 hg, by simp [hga, hgb]⟩
  rw [hw, List.mem_singleton] at h1 h2
  rw [h2, h1]

theorem countProducts_QC : countProducts 315 (commAll 315 [toTable permX, toTable permY])
    (levelTables chainC) (idT 315) = 1 := by
  rw [toTable_eq_arrTable rep_permX, toTable_eq_arrTable rep_permY, levelTables_chainC]
  exact tableCheck_parts.2.2.2.2.2.2.2

theorem permX_mem_QD : permX ∈ chainD.originalSubgroup := by
  rw [chainD_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem permY_mem_QD : permY ∈ chainD.originalSubgroup := by
  rw [chainD_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem centralizer_QD_inf_QC :
    Subgroup.centralizer (chainD.originalSubgroup : Set (Equiv.Perm (Fin 315))) ⊓
      chainC.originalSubgroup = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_iff] at hg1
  rw [Subgroup.mem_bot]
  exact eq_one_of_countProducts chainC_valid countProducts_QC hg2 (hg1 _ permX_mem_QD).symm
    (hg1 _ permY_mem_QD).symm

theorem orderOf_permX : orderOf permX = 2 :=
  (ordTest_iff perm_faithful (rep_arrTable (by norm_num) rep_permX) (by norm_num)).1
    tableCheck_parts.1

theorem orderOf_permY : orderOf permY = 3 :=
  (ordTest_iff perm_faithful (rep_arrTable (by norm_num) rep_permY) (by norm_num)).1
    tableCheck_parts.2.1

theorem orderOf_permX_mul_permY :
    orderOf (permX * permY) = 7 ∧ orderOf (permX * permY * permX⁻¹ * permY⁻¹) = 4 :=
  (pairTest_iff perm_faithful (rep_arrTable (by norm_num) rep_permX)
    (rep_arrTable (by norm_num) rep_permY) (by norm_num) (by norm_num) orderOf_permX
    orderOf_permY (by norm_num) (by norm_num)).1 tableCheck_parts.2.2.1

theorem card_pairs_eq {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {mx my r : ℕ} (hmx : 0 < mx) (hmy : 0 < my) (hr : 0 < r) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r} =
      pairCount (orderTables Q mx) (orderTables Q my) (fun x y => ordW n [x, y] r) := by
  set L := enumeration Q
  have hcoe : ∀ p : Q.originalSubgroup × Q.originalSubgroup,
      (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r) ↔
      (orderOf (p.1 : Equiv.Perm (Fin n)) = mx ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = my ∧
        orderOf ((p.1 : Equiv.Perm (Fin n)) * p.2) = r) := fun p => by
    simp only [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
    card_pairs_eq_sum Q.originalSubgroup L (enumeration_nodup Q hQ) (mem_enumeration_iff Q hQ)
      (fun h => orderOf h = mx) (fun h => orderOf h = my) (fun x y => orderOf (x * y) = r),
    pairCount_spec (forall₂_orderTables hn Q hmx) (forall₂_orderTables hn Q hmy)
      (R := fun x y => orderOf (x * y) = r) ?_,
    List.map_reverse, List.sum_reverse]
  · congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [List.countP_reverse]
  · intro x xg y yg hx hy _ _
    rw [ordW_iff perm_faithful (List.Forall₂.cons hx (List.Forall₂.cons hy List.Forall₂.nil)) hr]
    simp

theorem card_pairs_QD : Nat.card {p : chainD.originalSubgroup × chainD.originalSubgroup //
    orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 7} = 336 := by
  rw [card_pairs_eq (by norm_num) chainD chainD_valid (by norm_num) (by norm_num) (by norm_num),
    orderTables_chainD, orderTables_chainD]
  exact tableCheck_parts.2.2.2.2.2.1

theorem card_pairs_QD' : Nat.card {p : chainD.originalSubgroup × chainD.originalSubgroup //
    orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 7 ∧
      orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 4} = 336 := by
  rw [card_image_pairs_eq (by norm_num) chainD chainD_valid (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), orderTables_chainD, orderTables_chainD]
  exact tableCheck_parts.2.2.2.2.2.2.1

theorem card_involutions_QD :
    Nat.card {x : chainD.originalSubgroup // orderOf x = 2} = 21 := by
  rw [card_orderOf_eq (by norm_num) chainD chainD_valid (by norm_num), orderTables_chainD]
  exact tableCheck_parts.2.2.2.1

theorem tblFix_eq {T : Table} {g : Equiv.Perm (Fin 315)} (h : CFSG.Sporadic.Th.Rep 315 T g) :
    tblFix T = Models.fixCount g := by
  rw [tblFix, Models.fixCount, ← Nat.card_eq_fintype_card, List.countP_eq_length_filter]
  refine (card_eq_length _ Fin.val Fin.val_injective _ (List.nodup_range.filter _)
    fun b => ?_).symm
  simp only [List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨hb, hfix⟩
    refine ⟨⟨b, hb⟩, Fin.ext ?_, rfl⟩
    rw [h b hb, CFSG.Sporadic.Th.idx_of_lt _ hb] at hfix
    exact hfix
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, ?_⟩
    rw [h a a.2, CFSG.Sporadic.Th.idx_of_lt _ a.2]
    exact congrArg Fin.val ha

theorem exists_mem_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons hab hl, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := exists_mem_of_forall₂ hl hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem fixCount_of_mem_QD {g : Equiv.Perm (Fin 315)} (hg : g ∈ chainD.originalSubgroup)
    (h2 : orderOf g = 2) : Models.fixCount g = 11 := by
  have hf := forall₂_orderTables (by norm_num) chainD (m := 2) (by norm_num)
  rw [orderTables_chainD] at hf
  have hmem : g ∈ ((enumeration chainD).filter fun h => decide (orderOf h = 2)).reverse := by
    rw [List.mem_reverse, List.mem_filter]
    exact ⟨(mem_enumeration_iff _ chainD_valid g).2 hg, by simp [h2]⟩
  obtain ⟨T, hT, hTg⟩ := exists_mem_of_forall₂ hf hmem
  have := List.all_eq_true.1 tableCheck_parts.2.2.2.2.1 T hT
  rw [beq_iff_eq] at this
  rw [← tblFix_eq hTg, this]

theorem orderOf_permR : orderOf permR = 4 :=
  (ordTest_iff perm_faithful (rep_arrTable (by norm_num) rep_permR) (by norm_num)).1
    elemCheck_parts.1

theorem orderOf_permS : orderOf permS = 2 :=
  (ordTest_iff perm_faithful (rep_arrTable (by norm_num) rep_permS) (by norm_num)).1
    elemCheck_parts.2.1

theorem permS_inv : permS⁻¹ = permS := by
  rw [inv_eq_iff_mul_eq_one, ← sq, ← orderOf_permS, pow_orderOf_eq_one]

theorem permS_conj_permR : permS * permR * permS⁻¹ = permR⁻¹ := by
  rw [permS_inv, mul_assoc]
  exact eq_of_eqA (rep_compA rep_permS (rep_compA rep_permR rep_permS))
    (rep_inv_of_isInvA rep_permR elemCheck_parts.2.2.1) elemCheck_parts.2.2.2.1

theorem permS_ne : permS ≠ permR * permR := by
  intro h
  have h' := (eqA_iff rep_permS (rep_compA rep_permR rep_permR)).2 h
  rw [elemCheck_parts.2.2.2.2.1] at h'
  exact Bool.noConfusion h'

theorem permS_not_mem_zpowers : permS ∉ Subgroup.zpowers permR := by
  rw [Subgroup.mem_zpowers_iff]
  rintro ⟨k, hk⟩
  rw [← zpow_mod_orderOf, orderOf_permR] at hk
  have hk0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hk4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hS2 := orderOf_permS
  obtain h | h | h | h : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨
      k % ((4 : ℕ) : ℤ) = 2 ∨ k % ((4 : ℕ) : ℤ) = 3 := by omega
  · rw [h, zpow_zero] at hk
    rw [← hk, orderOf_one] at hS2
    exact absurd hS2 (by norm_num)
  · rw [h, zpow_one] at hk
    rw [← hk, orderOf_permR] at hS2
    exact absurd hS2 (by norm_num)
  · rw [h, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, sq] at hk
    exact permS_ne hk.symm
  · rw [h, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast] at hk
    rw [← hk, orderOf_pow' _ (by norm_num), orderOf_permR] at hS2
    exact absurd hS2 (by norm_num)

theorem permC_inv : permC⁻¹ = permC :=
  ((rep_permOfArr (isInvA_of_invoList elemCheck_parts.2.2.2.2.2.1)).2).unique rep_permC

theorem permC_ne_one : permC ≠ 1 := by
  intro h
  have h1 := eqA_idA_of_movesList elemCheck_parts.2.2.2.2.2.2.1
  rw [(eqA_iff rep_permC rep_idA).2 h] at h1
  exact Bool.noConfusion h1

theorem orderOf_permC : orderOf permC = 2 := by
  refine orderOf_eq_prime ?_ permC_ne_one
  rw [sq, ← mul_inv_cancel permC, permC_inv]

theorem fixCount_permC : Models.fixCount permC = 15 := by
  rw [Models.fixCount, ← Nat.card_eq_fintype_card, card_fixed_eq_fixedCount rep_permC]
  exact elemCheck_parts.2.2.2.2.2.2.2.1

theorem permC_mem_QC : permC ∈ chainC.originalSubgroup :=
  (mem_QC_iff rep_permC).1 elemCheck_parts.2.2.2.2.2.2.2.2.1

theorem permC_not_mem_QD : permC ∉ chainD.originalSubgroup := fun h => by
  have h' := (mem_QD_iff rep_permC).2 h
  rw [elemCheck_parts.2.2.2.2.2.2.2.2.2.1] at h'
  exact Bool.noConfusion h'

end CFSG.ComponentClassification.J2Cover.External
