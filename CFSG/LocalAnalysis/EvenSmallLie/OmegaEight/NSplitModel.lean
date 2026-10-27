module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitDeriv
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Lin
public import CFSG.Certificates.NativeSchreierCard
public import Mathlib.Algebra.CharP.Pi
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem genCode_invol (ε : Eps) {i v : ℕ} (hi : i < 7) (hv : v < 64) :
    genCode ε i (genCode ε i v) = v ∧ genCode ε i v < 64 := by
  have h : ∀ ε : Eps, ((List.range 7).all fun i => (List.range 64).all fun v =>
      genCode ε i (genCode ε i v) == v && decide (genCode ε i v < 64)) = true := by
    intro ε; cases ε <;> decide +kernel
  have := h ε
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  exact this i hi v hv

@[expose] def sFun (ε : Eps) (i : ℕ) (v : V6) : V6 := toVec 6 (genCode ε i (vecBits v))

theorem vecBits_sFun (ε : Eps) {i : ℕ} (hi : i < 7) (v : V6) :
    vecBits (sFun ε i v) = genCode ε i (vecBits v) :=
  vecBits_toVec (genCode_invol ε hi (vecBits_lt v)).2

theorem sFun_sFun (ε : Eps) {i : ℕ} (hi : i < 7) (v : V6) : sFun ε i (sFun ε i v) = v := by
  rw [sFun, vecBits_sFun ε hi, (genCode_invol ε hi (vecBits_lt v)).1, toVec_vecBits]

@[expose] def sPerm (ε : Eps) (i : Fin 7) : Equiv.Perm V6 where
  toFun := sFun ε i
  invFun := sFun ε i
  left_inv v := sFun_sFun ε i.2 v
  right_inv v := sFun_sFun ε i.2 v

theorem sPerm_apply (ε : Eps) (i : Fin 7) (v : V6) : sPerm ε i v = sFun ε i v := rfl

theorem sPerm_mul_self (ε : Eps) (i : Fin 7) : sPerm ε i * sPerm ε i = 1 :=
  Equiv.ext fun v => sFun_sFun ε i.2 v

theorem sPerm_inv (ε : Eps) (i : Fin 7) : (sPerm ε i)⁻¹ = sPerm ε i :=
  inv_eq_of_mul_eq_one_right (sPerm_mul_self ε i)

section Cert


theorem genFacts (ε : Eps) {i v w : ℕ} (hi : i < 7) (hv : v < 64) (hw : w < 64) :
    qfB ε (genCode ε i v) = qfB ε v ∧
      genCode ε i (v ^^^ w) = genCode ε i v ^^^ genCode ε i w ^^^ genCode ε i 0 := by
  have h : nsGenCheck ε = true := by cases ε; exact nsGenCheck_plus; exact nsGenCheck_minus
  simp only [nsGenCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact ⟨(h i hi v hv).1.2, (h i hi v hv).2 w hw⟩

theorem qfV_sFun (ε : Eps) {i : ℕ} (hi : i < 7) (v : V6) : qfV ε (sFun ε i v) = qfV ε v := by
  rw [qfV, vecBits_sFun ε hi, (genFacts ε hi (vecBits_lt v) (vecBits_lt 0)).1, qfV]

theorem sFun_add (ε : Eps) {i : ℕ} (hi : i < 7) (v w : V6) :
    sFun ε i (v + w) = sFun ε i v + sFun ε i w + sFun ε i 0 := by
  have h := (genFacts ε hi (vecBits_lt v) (vecBits_lt w)).2
  rw [← vecBits_add] at h
  simp only [sFun, h, toVec_xor, vecBits_zero]

theorem sPerm_mem (ε : Eps) (i : Fin 7) : sPerm ε i ∈ affGroup ε := by
  refine ⟨fun v => qfV_sFun ε i.2 v, fun a b c => ?_⟩
  simp only [sPerm_apply]
  rw [sFun_add ε i.2, sFun_add ε i.2 a]
  have h0 : sFun ε i 0 + sFun ε i 0 = 0 := CharTwo.add_self_eq_zero _
  calc sFun ε i a + sFun ε i b + sFun ε i 0 + sFun ε i c + sFun ε i 0
      = sFun ε i a + sFun ε i b + sFun ε i c + (sFun ε i 0 + sFun ε i 0) := by abel
    _ = sFun ε i a + sFun ε i b + sFun ε i c := by rw [h0, add_zero]

@[expose] def sGen (ε : Eps) (i : Fin 7) : affGroup ε := ⟨sPerm ε i, sPerm_mem ε i⟩

end Cert

section Pres

open CFSG.CosetTable


theorem finite_card_PG_le : Finite (PG 7 relPG) ∧ Nat.card (PG 7 relPG) ≤ 1451520 :=
  nsCosetCheck_true

end Pres

section Chain

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem card_closure_permOfArr {n : ℕ} (hn : 1 ≤ n) {O S : Array (Array ℕ)}
    {W : Array (List ℤ)} {base : List (Fin n)} (hb : base.Nodup) {chunks : ℕ} (hc : 0 < chunks)
    (hOS : O.size ≤ S.size) (hSO : ∀ i < O.size, S[i]! = O[i]!)
    (h : rawChainOK n (S.extract 0 O.size) S (base.map Fin.val).toArray W chunks = true) :
    Nat.card (Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g} :
      Subgroup (Equiv.Perm (Fin n))) = (rawOrbitSizes n S (base.map Fin.val).toArray).prod := by
  have hF := chainCheckFacts h
  have hA := chainArrays_ofArrays (hn := hn) (k := O.size) (hk := hOS) (hb := hb) (W := W)
    hF.strong_inv
  have hcard := card_originalSubgroup_of_chainOK hA hc h
  have hQ : (RawSchreierDatum.ofArrays n hn S O.size hOS base hb W).originalSubgroup =
      Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g} := by
    unfold RawSchreierDatum.originalSubgroup
    congr 1
    ext g
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
  rw [← hQ]
  exact hcard

@[expose] def e64 : V6 ≃ Fin 64 where
  toFun v := ⟨vecBits v, vecBits_lt v⟩
  invFun i := toVec 6 i
  left_inv v := toVec_vecBits v
  right_inv i := Fin.ext (vecBits_toVec i.2)

theorem isInvA_genArr (ε : Eps) {i : ℕ} (hi : i < 7) :
    isInvA 64 (genArr ε i) (genArr ε i) = true := by
  rw [isInvA, allLt_iff]
  intro v hv
  have hg : (genArr ε i)[v]! = genCode ε i v := by
    rw [genArr, getElem!_pos _ _ (by simpa using hv)]
    simp
  have h1 := genCode_invol ε hi hv
  have hg' : (genArr ε i)[genCode ε i v]! = genCode ε i (genCode ε i v) := by
    rw [genArr, getElem!_pos _ _ (by simpa using h1.2)]
    simp
  rw [hg, hg', h1.1]
  simp [h1.2]

theorem permOfArr_genArr (ε : Eps) (i : Fin 7) :
    permOfArr 64 (genArr ε i) = e64.permCongr (sPerm ε i) := by
  have hrep := (rep_permOfArr (isInvA_genArr ε i.2)).1
  ext x
  rw [← hrep x]
  simp only [Equiv.permCongr_apply, e64, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, sPerm_apply,
    sFun]
  rw [vecBits_toVec (genCode_invol ε i.2 (vecBits_lt (toVec 6 x))).2, vecBits_toVec x.2, genArr,
    getElem!_pos _ _ (by simp)]
  simp

theorem genArrs_size (ε : Eps) : (genArrs ε).size = 7 := Array.size_ofFn

theorem genArrs_get (ε : Eps) {k : ℕ} (hk : k < 7) : (genArrs ε)[k]! = genArr ε k := by
  rw [getElem!_pos (genArrs ε) k (by rw [genArrs_size]; exact hk)]
  simp [genArrs]

@[expose] def chainBaseF (ε : Eps) : List (Fin 64) := (chainBase ε).map (Fin.ofNat 64)

theorem chainBaseF_val (ε : Eps) : (chainBaseF ε).map Fin.val = chainBase ε := by
  cases ε <;> decide

theorem chainBaseF_nodup (ε : Eps) : (chainBaseF ε).Nodup := by
  cases ε <;> decide


theorem card_closure_sPerm (ε : Eps) :
    Nat.card (Subgroup.closure (Set.range (sPerm ε))) = 1451520 := by
  have h : nsChainCheck ε = true := by
    cases ε; exact nsChainCheck_plus; exact nsChainCheck_minus
  simp only [nsChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hc, hprod⟩ := h
  have hsz : (genArrs ε).size = 7 := genArrs_size ε
  have hOS : (genArrs ε).size ≤ (strong ε).size := by
    rw [strong, Array.size_append]; omega
  have hSO : ∀ i < (genArrs ε).size, (strong ε)[i]! = (genArrs ε)[i]! := by
    intro i hi
    have hi' : i < (strong ε).size := lt_of_lt_of_le hi hOS
    rw [getElem!_pos (strong ε) i hi', getElem!_pos (genArrs ε) i hi]
    simp only [strong]
    rw [Array.getElem_append_left hi]
  have hc' : rawChainOK 64 ((strong ε).extract 0 (genArrs ε).size) (strong ε)
      ((chainBaseF ε).map Fin.val).toArray (chainWords ε) 1 = true := by
    rw [hsz, chainBaseF_val]; exact hc
  have hcard := card_closure_permOfArr (by norm_num) (chainBaseF_nodup ε) (by norm_num) hOS hSO hc'
  rw [chainBaseF_val, hprod] at hcard
  rw [← hcard]
  have hset : {g | ∃ k < (genArrs ε).size, permOfArr 64 (genArrs ε)[k]! = g} =
      (e64.permCongrHom : Equiv.Perm V6 →* Equiv.Perm (Fin 64)) '' Set.range (sPerm ε) := by
    ext g
    rw [hsz]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨sPerm ε ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, ?_⟩
      show e64.permCongr (sPerm ε ⟨k, hk⟩) = _
      rw [← permOfArr_genArr, genArrs_get ε hk]
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, i.2, ?_⟩
      show _ = e64.permCongr (sPerm ε i)
      rw [← permOfArr_genArr, genArrs_get ε i.2]
  rw [hset, ← MonoidHom.map_closure]
  exact (Subgroup.card_map_of_injective (e64.permCongrHom.injective)).symm

end Chain

section Gen

theorem card_zeroSet (ε : Eps) : (zeroSet ε).card = mOf ε := by
  have h := card_filter_vecBits (fun x => !qfB ε x)
  have hs : zeroSet ε = Finset.univ.filter fun v : V6 => (!qfB ε (vecBits v)) = true := by
    ext v
    simp [zeroSet, qfV_eq_zero_iff]
  rw [hs, h]
  cases ε <;> decide


theorem closure_sPerm_le (ε : Eps) : Subgroup.closure (Set.range (sPerm ε)) ≤ affGroup ε :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact sPerm_mem ε i)


theorem closure_sPerm_eq (ε : Eps) : Subgroup.closure (Set.range (sPerm ε)) = affGroup ε := by
  apply Subgroup.eq_of_le_of_card_ge (closure_sPerm_le ε)
  rw [card_closure_sPerm]
  have h := card_affGroup_le ε
  rw [card_zeroSet] at h
  cases ε <;> simpa [mOf, oBound] using h

theorem card_affGroup (ε : Eps) : Nat.card (affGroup ε) = 1451520 := by
  rw [← closure_sPerm_eq, card_closure_sPerm]

theorem closure_sGen (ε : Eps) : Subgroup.closure (Set.range (sGen ε)) = ⊤ := by
  apply Subgroup.map_injective (affGroup ε).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
  exact closure_sPerm_eq ε

end Gen

section Presentation

open CFSG.CosetTable

@[expose] def rels7 : List (List (Fin 7)) := relWords.map (List.map (Fin.ofNat 7))

theorem lift_mk_true {H : Type*} [Group H] {k : ℕ} (f : Fin k → H) (w : List (Fin k)) :
    FreeGroup.lift f (FreeGroup.mk (w.map fun i => (i, true))) = wordProd f w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have h1 : FreeGroup.mk ((i, true) :: w.map fun i => (i, true)) =
        FreeGroup.of i * FreeGroup.mk (w.map fun i => (i, true)) := by
      rw [FreeGroup.of, FreeGroup.mul_mk]; rfl
    rw [List.map_cons, h1, map_mul, ih, wordProd_cons, FreeGroup.lift_apply_of]

theorem relPG_eq : relPG = rels7.map fun w => w.map fun i => (i, true) := by
  simp only [relPG, rels7, List.map_map]
  rfl

theorem relWords_lt : ∀ w ∈ relWords, ∀ i ∈ w, i < 7 := by decide

theorem wordCode_lt (ε : Eps) {w : List ℕ} (hw : ∀ i ∈ w, i < 7) {v : ℕ} (hv : v < 64) :
    wordCode ε w v < 64 := by
  induction w with
  | nil => exact hv
  | cons i w ih =>
    exact (genCode_invol ε (hw i List.mem_cons_self)
      (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))).2

theorem wordProd_sPerm_apply (ε : Eps) {w : List ℕ} (hw : ∀ i ∈ w, i < 7) (v : V6) :
    wordProd (sPerm ε) (w.map (Fin.ofNat 7)) v = toVec 6 (wordCode ε w (vecBits v)) := by
  induction w with
  | nil => simp [wordProd, wordCode, toVec_vecBits]
  | cons i w ih =>
    have hi : i < 7 := hw i List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 7 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, wordProd_cons, Equiv.Perm.mul_apply, ih hw', sPerm_apply, sFun,
      vecBits_toVec (wordCode_lt ε hw' (vecBits_lt v)), wordCode]
    congr 2
    simp [Fin.ofNat, Nat.mod_eq_of_lt hi]


theorem wordProd_sPerm (ε : Eps) {w : List (Fin 7)} (hw : w ∈ rels7) :
    wordProd (sPerm ε) w = 1 := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
  have hc : nsRelCheck ε = true := by
    cases ε; exact nsRelCheck_plus; exact nsRelCheck_minus
  simp only [nsRelCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  ext1 v
  rw [wordProd_sPerm_apply ε (relWords_lt u hu), hc u hu _ (vecBits_lt v), toVec_vecBits]
  rfl

theorem wordProd_sGen (ε : Eps) {w : List (Fin 7)} (hw : w ∈ rels7) : wordProd (sGen ε) w = 1 := by
  apply Subtype.ext
  rw [← Subgroup.coe_subtype, map_wordProd]
  exact wordProd_sPerm ε hw

@[expose] noncomputable def pgHom (ε : Eps) : PG 7 relPG →* affGroup ε :=
  PresentedGroup.toGroup (f := sGen ε) (by
    rintro r hr
    rw [relPG_eq, List.map_map] at hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    simp only [Function.comp_apply]
    rw [lift_mk_true]
    exact wordProd_sGen ε hw)


theorem pgHom_bijective (ε : Eps) : Function.Bijective (pgHom ε) := by
  obtain ⟨hfin, hcard⟩ := finite_card_PG_le
  have hsurj : Function.Surjective (pgHom ε) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_sGen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  refine (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, le_antisymm ?_ ?_⟩
  · rw [card_affGroup]; exact hcard
  · exact Nat.card_le_card_of_surjective _ hsurj

theorem exists_hom_of_rels (ε : Eps) {H : Type*} [Group H] (h : Fin 7 → H)
    (hh : ∀ w ∈ rels7, wordProd h w = 1) : ∃ σ : affGroup ε →* H, ∀ i, σ (sGen ε i) = h i := by
  have hr : ∀ r ∈ {r : FreeGroup (Fin 7) | r ∈ relPG.map FreeGroup.mk}, FreeGroup.lift h r = 1 := by
    rintro r hr
    rw [Set.mem_ofPred_eq, relPG_eq, List.map_map] at hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    simp only [Function.comp_apply]
    rw [lift_mk_true]
    exact hh w hw
  let e := MulEquiv.ofBijective (pgHom ε) (pgHom_bijective ε)
  refine ⟨(PresentedGroup.toGroup hr).comp e.symm.toMonoidHom, fun i => ?_⟩
  have he : e.symm (sGen ε i) = PresentedGroup.of i := by
    rw [MulEquiv.symm_apply_eq]
    show sGen ε i = pgHom ε (PresentedGroup.of i)
    rw [pgHom, PresentedGroup.toGroup.of]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, he]
  exact PresentedGroup.toGroup.of _

end Presentation

end CFSG.EvenSmallLie.OmegaEight.NSplit
