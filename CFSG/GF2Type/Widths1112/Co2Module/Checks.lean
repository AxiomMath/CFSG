module

public import CFSG.GF2Type.Widths1112.Co2Module.Words
public import CFSG.GF2Type.Widths1112.Co2Module.Gluing
public import Certificates.Certificate38956
public import Certificates.Certificate38957
public import Certificates.Certificate38958
public import Certificates.Certificate38959

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open CFSG.GF2W1112


noncomputable def ee (i : Fin 4) : G2 := gen i.val

private theorem checks1_eqs :
    ∀ q ∈ w12UOrdEqs () ++ w12UCommEqs () ++ w12UConjEqs (), evalE q.1 = evalE q.2 := by
  have h : w12UEqCheck (w12URows ())
      (w12UOrdEqs () ++ w12UCommEqs () ++ w12UConjEqs ()) = true := by
    have h0 := Certificates.certificate38957
    unfold w12UCheck1 at h0
    simp only [Bool.and_eq_true] at h0
    exact h0.1
  exact eqCheck_sound h

private theorem mem_ordEqs {i : ℕ} (hi : i < 33) :
    (([(i, w12UOrd i)], []) : List (ℕ × ℕ) × List (ℕ × ℕ)) ∈ w12UOrdEqs () := by
  unfold w12UOrdEqs
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem ord_gen (i : ℕ) : gen i ^ w12UOrd i = 1 := by
  by_cases hi : i < 33
  · have hmem : (([(i, w12UOrd i)], []) : List (ℕ × ℕ) × List (ℕ × ℕ)) ∈
        w12UOrdEqs () ++ w12UCommEqs () ++ w12UConjEqs () :=
      List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (mem_ordEqs hi))))
    have h := checks1_eqs (([(i, w12UOrd i)], []) : List (ℕ × ℕ) × List (ℕ × ℕ)) hmem
    simp only [evalE_cons, evalE_nil, mul_one] at h
    exact h
  · have hle : w12UWords.size ≤ i := by
      have hsz : w12UWords.size = 33 := rfl
      omega
    have hw : w12UWords.getD i "" = "" := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle, Option.getD_none]
    have hg : gen i = 1 := by
      unfold gen
      rw [hw]
      rfl
    rw [hg, one_pow]

theorem ord_pos_all (i : ℕ) : 0 < w12UOrd i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hpos, _⟩ := Certificates.certificate38956
  by_cases hi : i < 33
  · exact hpos ⟨i, hi⟩
  · have hle : w12UOrds.size ≤ i := by
      have hsz : w12UOrds.size = 33 := rfl
      omega
    have h1 : w12UOrd i = 1 := by
      unfold w12UOrd
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle, Option.getD_none]
    rw [h1]
    exact Nat.one_pos

theorem ee_comm (i j : Fin 4) : Commute (ee i) (ee j) := by
  have hmem : (([(i.val, 1), (j.val, 1)], [(j.val, 1), (i.val, 1)]) :
      List (ℕ × ℕ) × List (ℕ × ℕ)) ∈ w12UCommEqs () := by
    unfold w12UCommEqs
    exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt,
      List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩⟩
  have hmem' : (([(i.val, 1), (j.val, 1)], [(j.val, 1), (i.val, 1)]) :
      List (ℕ × ℕ) × List (ℕ × ℕ)) ∈ w12UOrdEqs () ++ w12UCommEqs () ++ w12UConjEqs () :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hmem)))
  have h := checks1_eqs
    (([(i.val, 1), (j.val, 1)], [(j.val, 1), (i.val, 1)]) : List (ℕ × ℕ) × List (ℕ × ℕ)) hmem'
  simp only [evalE_cons, evalE_nil, pow_one, mul_one] at h
  exact h

theorem ee_cube (i : Fin 4) : ee i ^ 3 = 1 := by
  have h3 : w12UOrd i.val = 3 := by
    fin_cases i <;> decide
  have h := ord_gen i.val
  rw [h3] at h
  exact h

noncomputable def iotaE : AddChar F3Vec G2 := commutingChar ee ee_comm ee_cube

theorem iotaE_single (i : Fin 4) : iotaE (Pi.single i 1) = ee i := by
  rw [iotaE, commutingChar_single]

theorem ee_eq (i : Fin 4) : ee i = gen i.val := by
  unfold ee
  rfl

theorem iotaE_apply (c : ℕ) : iotaE (uVec c) = evalE (w12UIota c) := by
  have hv : ∀ i : Fin 4, (uVec c i).val = c / 3 ^ i.val % 3 := by
    intro i
    simp only [uVec]
    rw [ZMod.val_natCast, Nat.mod_mod]
  have f0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have f1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have f2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have f3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [iotaE, commutingChar_apply, hv 0, hv 1, hv 2, hv 3]
  simp only [evalE, w12UIota, ee, f0, f1, f2, f3, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, pow_zero, pow_one, Nat.div_one, Nat.reducePow]

theorem conjAct_gen {k : ℕ} (hk : k ∈ w12UNormIdx) : ConjAct iotaE (gen k) (uA k) := by
  obtain ⟨hinv, _, _, _, _, _, _, _, _, _, _, hvec⟩ := Certificates.certificate38956
  refine ConjAct.ofBasis (isUnit_of_mul_eq_one_matrix (hinv k hk)) (fun i => ?_)
  have hi : i.val ∈ List.range 4 := List.mem_range.mpr i.isLt
  have hmemC : w12UConjEq k i.val ∈ w12UConjEqs () := by
    unfold w12UConjEqs
    exact List.mem_flatMap.mpr ⟨k, hk, List.mem_map.mpr ⟨i.val, hi, rfl⟩⟩
  have h := checks1_eqs (w12UConjEq k i.val) (List.mem_append.mpr (Or.inr hmemC))
  simp only [w12UConjEq, evalE_append, evalE_cons, evalE_nil, pow_one, mul_one] at h
  have e2 : (uA k).mulVec (Pi.single i 1) = uVec (w12UConjCode k i.val) := by
    rw [hvec k hk i]
    funext r
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [iotaE_single, e2, iotaE_apply, mul_inv_eq_iff_eq_mul]
  exact h

noncomputable def ppE (k : Fin 8) (i : Fin 10) (j : Fin 2) : G2 :=
  evalE ((w12UDecP.getD (k.val * 20 + i.val * 2 + j.val) []).map fun q => (17 + q.1 % 5, q.2))

private theorem gen_pow_mem_closure_p (q : ℕ × ℕ) :
    gen (17 + q.1 % 5) ^ q.2 ∈ Subgroup.closure (Set.range fun j : Fin 5 => gen (17 + j.val)) := by
  apply Subgroup.pow_mem
  apply Subgroup.subset_closure
  exact ⟨⟨q.1 % 5, Nat.mod_lt _ (by norm_num)⟩, rfl⟩

theorem ppE_mem (k : Fin 8) (i : Fin 10) (j : Fin 2) :
    ppE k i j ∈ Subgroup.closure (Set.range fun j : Fin 5 => gen (17 + j.val)) := by
  unfold ppE evalE
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 ha
  exact gen_pow_mem_closure_p b

private theorem iotaE_uV0 : iotaE uV0 = gen 1 := by
  have h3 : w12UIota 3 = [(0, 0), (1, 1), (2, 0), (3, 0)] := rfl
  show iotaE (uVec 3) = gen 1
  rw [iotaE_apply, h3]
  simp only [evalE_cons, evalE_nil, pow_zero, pow_one, mul_one, one_mul]

private theorem decEq_mem {m i j : ℕ} (hm : m < 8) (hi : i < 10) (hj : j < 2) :
    w12UDecEq m i j ∈ w12UDecEqs () := by
  unfold w12UDecEqs
  exact List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, List.mem_flatMap.2
    ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩⟩

private theorem decEq_fst (m i j : ℕ) :
    evalE (w12UDecEq m i j).1 =
      gen (w12UIdxM m) * gen (6 + i) * gen 1 ^ j := by
  have e1 : (w12UDecEq m i j).1 =
      [(w12UIdxM m, 1), (6 + i, 1), (1, j)] := rfl
  rw [e1]
  simp only [evalE_cons, evalE_nil, pow_one, mul_one, mul_assoc]

private theorem decEq_snd (m i j : ℕ) :
    evalE (w12UDecEq m i j).2 =
      gen (6 + w12UDecSigma.getD (m * 10 + i) 0 % 10) *
        iotaE (uVec (w12UDecU.getD (m * 20 + i * 2 + j) 0)) *
        gen 16 ^ w12UDecEps.getD (m * 20 + i * 2 + j) 0 *
        evalE ((w12UDecP.getD (m * 20 + i * 2 + j) []).map
          fun q => (17 + q.1 % 5, q.2)) := by
  have e1 : (w12UDecEq m i j).2 =
      [(6 + w12UDecSigma.getD (m * 10 + i) 0 % 10, 1)] ++
        w12UIota (w12UDecU.getD (m * 20 + i * 2 + j) 0) ++
        [(16, w12UDecEps.getD (m * 20 + i * 2 + j) 0)] ++
        (w12UDecP.getD (m * 20 + i * 2 + j) []).map fun q => (17 + q.1 % 5, q.2) := by
    simp only [w12UDecEq, Array.getElem!_eq_getD] <;> rfl
  rw [e1, evalE_append, evalE_append, evalE_append, ← iotaE_apply]
  simp only [evalE_cons, evalE_nil, pow_one, mul_one]

theorem dec_spec (k : Fin 8) (i : Fin 10) (j : Fin 2) :
    gen (w12UIdxM k.val) * gen (6 + i.val) * iotaE uV0 ^ (j : ℕ) =
      gen (6 + (uSigma k i).val) * iotaE (uU k i j) * gen 16 ^ uEps k i j * ppE k i j := by
  have h2 : w12UEqCheck (w12URows ()) (w12UDecEqs ()) = true :=
    Certificates.certificate38958
  have hdec := eqCheck_sound h2 _ (decEq_mem k.isLt i.isLt j.isLt)
  rw [decEq_fst, decEq_snd] at hdec
  rw [iotaE_uV0]
  simp only [uSigma, uU, uEps, ppE]
  exact hdec

noncomputable def NinfE : Subgroup G2 :=
  Subgroup.closure (Set.range fun i : Fin 2 => gen (29 + i.val))

private theorem glueEqs_sound : ∀ q ∈ w12UGlueEqs (), evalE q.1 = evalE q.2 := by
  have h3 : w12UCheck3 () = true := Certificates.certificate38959
  simp only [w12UCheck3, Bool.and_eq_true] at h3
  exact eqCheck_sound h3.1

private theorem tauPows_sound : ∀ q ∈ w12UTauPows (), evalE q.1 ^ q.2 = 1 := by
  have h3 : w12UCheck3 () = true := Certificates.certificate38959
  simp only [w12UCheck3, Bool.and_eq_true] at h3
  exact powCheck_sound h3.2

private theorem evalE_single (i : ℕ) : evalE [(i, 1)] = gen i := by
  simp [evalE]

private theorem yWords_lt : ∀ k : Fin 3, ∀ q ∈ w12UYWords[k.val]!, q.1 < 2 := by
  decide

private theorem zWords_lt : ∀ k : Fin 3, ∀ q ∈ w12UZWords[k.val]!, q.1 < 2 := by
  decide

private theorem pairWords_lt : ∀ i : Fin 2, ∀ q ∈ w12UPerf[i.val]!,
    (∀ x ∈ (w12UPairs[q.1]!).1, x.1 < 2) ∧ (∀ x ∈ (w12UPairs[q.1]!).2, x.1 < 2) := by
  decide

private theorem normIdx_29 : ∀ i : Fin 2, 29 + i.val ∈ w12UNormIdx := by
  decide

private theorem seedA_idx : ∀ q ∈ w12UMapNG w12USeedA, q.1 = 4 ∨ q.1 = 5 ∨ q.1 = 28 := by
  decide

private theorem seedB_idx : ∀ q ∈ w12UMapNG w12USeedB, q.1 = 4 ∨ q.1 = 5 ∨ q.1 = 28 := by
  decide

private theorem tauWords_getD :
    ∀ j : Fin 8, w12UTauWords.getD j.val [] = w12UTauWords[j.val]! := by
  decide

private theorem tauOrd_getD : ∀ j : Fin 8, uKk j = w12UTauOrd[j.val]! := by
  decide

private theorem gen_mem_NinfE (i : Fin 2) : gen (29 + i.val) ∈ NinfE :=
  Subgroup.subset_closure ⟨i, rfl⟩

private theorem evalE_mapS_mem (L : List (ℕ × ℕ)) (hL : ∀ q ∈ L, q.1 < 2) :
    evalE (w12UMapS L) ∈ NinfE := by
  unfold evalE w12UMapS
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact Subgroup.pow_mem _ (gen_mem_NinfE ⟨p.1, hL p hp⟩) _

private theorem mem_glueA (k : ℕ) (hk : k < 3) :
    (([(22 + k, 1)] : List (ℕ × ℕ)), w12UMapS (w12UYWords[k]!)) ∈ w12UGlueEqs () := by
  unfold w12UGlueEqs
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inl ?_)
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

private theorem mem_glueB (k : ℕ) (hk : k < 3) :
    (([(25 + k, 1)] : List (ℕ × ℕ)), w12UMapS (w12UZWords[k]!)) ∈ w12UGlueEqs () := by
  unfold w12UGlueEqs
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inr ?_)
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

private theorem mem_glueC (k : ℕ) (hk : k < 2) : w12UPerfEq k ∈ w12UGlueEqs () := by
  unfold w12UGlueEqs
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inr ?_)
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

private theorem mem_glueD (k : ℕ) (hk : k < 3) :
    (([(28, 1), (22 + k, 1)] : List (ℕ × ℕ)), [(25 + k, 1), (28, 1)]) ∈ w12UGlueEqs () := by
  unfold w12UGlueEqs
  refine List.mem_append.2 (Or.inl ?_)
  refine List.mem_append.2 (Or.inr ?_)
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

private theorem mem_glueE31 :
    (([(31, 1)] : List (ℕ × ℕ)), w12UMapNG w12USeedA) ∈ w12UGlueEqs () := by
  unfold w12UGlueEqs
  refine List.mem_append.2 (Or.inr ?_)
  simp

private theorem mem_glueE32 :
    (([(32, 1)] : List (ℕ × ℕ)), w12UMapNG w12USeedB) ∈ w12UGlueEqs () := by
  unfold w12UGlueEqs
  refine List.mem_append.2 (Or.inr ?_)
  simp

private theorem mem_tauPows (j : Fin 8) :
    (w12UMapN (w12UTauWords[j.val]!) ++ [(28, 1)], w12UTauOrd[j.val]!) ∈ w12UTauPows () := by
  unfold w12UTauPows
  exact List.mem_map.2 ⟨j.val, List.mem_range.2 j.isLt, rfl⟩

private theorem evalE_flatMap_mem (K : Subgroup G2) (f : ℕ × ℕ → List (ℕ × ℕ))
    (L : List (ℕ × ℕ)) (h : ∀ q ∈ L, evalE (f q) ∈ K) : evalE (L.flatMap f) ∈ K := by
  induction L with
  | nil =>
    rw [List.flatMap_nil, evalE_nil]
    exact K.one_mem
  | cons a L ih =>
    rw [List.flatMap_cons, evalE_append]
    exact K.mul_mem (h a (by simp)) (ih fun q hq => h q (by simp [hq]))

private theorem evalE_comm_mem (u v : List (ℕ × ℕ)) (hu : ∀ q ∈ u, q.1 < 2)
    (hv : ∀ q ∈ v, q.1 < 2) :
    evalE (w12UComm (w12UMapS u) (w12UMapS v)) ∈ ⁅NinfE, NinfE⁆ := by
  have hU : evalE (w12UMapS u) ∈ NinfE := evalE_mapS_mem u hu
  have hV : evalE (w12UMapS v) ∈ NinfE := evalE_mapS_mem v hv
  unfold w12UComm
  rw [evalE_append, evalE_append, evalE_append, evalE_inv ord_gen ord_pos_all,
    evalE_inv ord_gen ord_pos_all]
  exact Subgroup.commutator_mem_commutator hU hV

private theorem evalE_pairEx_mem (pk d : ℕ) (h1 : ∀ x ∈ (w12UPairs[pk]!).1, x.1 < 2)
    (h2 : ∀ x ∈ (w12UPairs[pk]!).2, x.1 < 2) :
    evalE (w12UPairEx pk d) ∈ ⁅NinfE, NinfE⁆ := by
  dsimp only [w12UPairEx]
  split
  · exact evalE_comm_mem _ _ h1 h2
  · exact evalE_comm_mem _ _ h2 h1

private theorem gen_perf (i : Fin 2) : gen (29 + i.val) ∈ ⁅NinfE, NinfE⁆ := by
  have h : evalE [(29 + i.val, 1)] =
      evalE ((w12UPerf[i.val]!).flatMap fun q : ℕ × ℕ => w12UPairEx q.1 q.2) :=
    glueEqs_sound (([(29 + i.val, 1)] : List (ℕ × ℕ)),
      (w12UPerf[i.val]!).flatMap fun q : ℕ × ℕ => w12UPairEx q.1 q.2) (mem_glueC i.val i.isLt)
  rw [evalE_single] at h
  rw [h]
  exact evalE_flatMap_mem _ (fun q : ℕ × ℕ => w12UPairEx q.1 q.2) (w12UPerf[i.val]!)
    fun q hq => evalE_pairEx_mem q.1 q.2 (pairWords_lt i q hq).1 (pairWords_lt i q hq).2

private theorem gen31_eq : gen 31 = genA2 := by
  have h : w12UWords.getD 31 "" = "a" := by decide
  have hp : w12UParse "a" = [true] := by decide
  unfold gen
  rw [h, hp]
  simp [wd]

private theorem gen32_eq : gen 32 = genB2 := by
  have h : w12UWords.getD 32 "" = "b" := by decide
  have hp : w12UParse "b" = [false] := by decide
  unfold gen
  rw [h, hp]
  simp [wd]

private theorem evalE_mem_closure (S : Set G2) (L : List (ℕ × ℕ))
    (h : ∀ q ∈ L, gen q.1 ∈ Subgroup.closure S) : evalE L ∈ Subgroup.closure S := by
  unfold evalE
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.pow_mem _ (h q hq) _

private theorem gen_mem_S (n : ℕ) (hn : n = 4 ∨ n = 5 ∨ n = 28) :
    gen n ∈ Subgroup.closure ({gen 4, gen 5, gen 28} : Set G2) :=
  Subgroup.subset_closure (by rcases hn with rfl | rfl | rfl <;> simp)

private theorem evalE_mapN_eq (L : List (ℕ × ℕ)) :
    evalE (w12UMapN L) = wordProd (fun s : Fin 2 => gen (4 + s.val))
      (L.map fun q => ((⟨q.1 % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2), q.2)) := by
  unfold evalE w12UMapN wordProd
  simp only [List.map_map, Function.comp_def]

private theorem wordProd_uTw (j : Fin 8) :
    wordProd (fun s : Fin 2 => gen (4 + s.val)) (uTw j)
      = evalE (w12UMapN (w12UTauWords[j.val]!)) := by
  rw [evalE_mapN_eq]
  unfold uTw
  rw [tauWords_getD j]

theorem NinfE_norm : NinfE ≤ normSubgroup iotaE := by
  unfold NinfE
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact (mem_normSubgroup iotaE).2 ⟨uA (29 + i.val), conjAct_gen (normIdx_29 i)⟩

theorem NinfE_perf : NinfE ≤ ⁅NinfE, NinfE⁆ :=
  CFSG.Monster.GMS.Griess13.closure_le_commutator
    (S := Set.range fun i : Fin 2 => gen (29 + i.val))
    (by rintro _ ⟨i, rfl⟩; exact gen_perf i)

theorem y_mem (k : Fin 3) : gen (22 + k.val) ∈ NinfE := by
  have h : evalE [(22 + k.val, 1)] = evalE (w12UMapS (w12UYWords[k.val]!)) :=
    glueEqs_sound (([(22 + k.val, 1)] : List (ℕ × ℕ)), w12UMapS (w12UYWords[k.val]!))
      (mem_glueA k.val k.isLt)
  rw [evalE_single] at h
  rw [h]
  exact evalE_mapS_mem _ (yWords_lt k)

theorem z_mem (k : Fin 3) : gen (25 + k.val) ∈ NinfE := by
  have h : evalE [(25 + k.val, 1)] = evalE (w12UMapS (w12UZWords[k.val]!)) :=
    glueEqs_sound (([(25 + k.val, 1)] : List (ℕ × ℕ)), w12UMapS (w12UZWords[k.val]!))
      (mem_glueB k.val k.isLt)
  rw [evalE_single] at h
  rw [h]
  exact evalE_mapS_mem _ (zWords_lt k)

theorem glue_eq (k : Fin 3) : gen 28 * gen (22 + k.val) = gen (25 + k.val) * gen 28 := by
  have h : evalE [(28, 1), (22 + k.val, 1)] = evalE [(25 + k.val, 1), (28, 1)] :=
    glueEqs_sound (([(28, 1), (22 + k.val, 1)] : List (ℕ × ℕ)), [(25 + k.val, 1), (28, 1)])
      (mem_glueD k.val k.isLt)
  simp only [evalE_cons, evalE_nil, pow_one, mul_one] at h
  exact h

theorem closure_n1_n2_g : Subgroup.closure ({gen 4, gen 5, gen 28} : Set G2) = ⊤ := by
  apply top_le_iff.1
  rw [← closure_genAB]
  apply (Subgroup.closure_le _).2
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have h0 : evalE [(31, 1)] = evalE (w12UMapNG w12USeedA) :=
      glueEqs_sound (([(31, 1)] : List (ℕ × ℕ)), w12UMapNG w12USeedA) mem_glueE31
    rw [evalE_single] at h0
    rw [← gen31_eq, h0]
    exact evalE_mem_closure ({gen 4, gen 5, gen 28} : Set G2) _ fun q hq =>
      gen_mem_S q.1 (seedA_idx q hq)
  · have h0 : evalE [(32, 1)] = evalE (w12UMapNG w12USeedB) :=
      glueEqs_sound (([(32, 1)] : List (ℕ × ℕ)), w12UMapNG w12USeedB) mem_glueE32
    rw [evalE_single] at h0
    rw [← gen32_eq, h0]
    exact evalE_mem_closure ({gen 4, gen 5, gen 28} : Set G2) _ fun q hq =>
      gen_mem_S q.1 (seedB_idx q hq)

theorem rel_tau (j : Fin 8) :
    (wordProd (fun s : Fin 2 => gen (4 + s.val)) (uTw j) * gen 28) ^ uKk j = 1 := by
  have hpow : evalE (w12UMapN (w12UTauWords[j.val]!) ++ [(28, 1)]) ^ w12UTauOrd[j.val]! = 1 :=
    tauPows_sound (w12UMapN (w12UTauWords[j.val]!) ++ [(28, 1)], w12UTauOrd[j.val]!)
      (mem_tauPows j)
  rw [evalE_append, evalE_single] at hpow
  rw [tauOrd_getD j, wordProd_uTw j]
  exact hpow

end CFSG.GF2Type.Widths1112.Co2Module
