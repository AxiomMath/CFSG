module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentTree
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentTree
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
public import Certificates.Certificate3093
public import Certificates.Certificate3089
public import Certificates.Certificate2151
public import Certificates.Certificate2152
public import Certificates.Certificate2154

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

theorem rep_letArr (l : Fin 7 × Bool) :
    Rep 276 (letArr l) (FreeGroup.lift (fun i : Fin 7 => gp i) (FreeGroup.mk [l])) := by
  obtain ⟨i, b⟩ := l
  have hi : (i : ℕ) < 7 := i.2
  cases b
  · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
      FreeGroup.lift_apply_of]
    exact rep_inv_of_isInvA (rep_gp hi) (gen_check.1 i hi)
  · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
    exact rep_gp hi

theorem rep_wordArr : ∀ w : List (Fin 7 × Bool),
    Rep 276 (wordArr w) (FreeGroup.lift (fun i : Fin 7 => gp i) (FreeGroup.mk w))
  | [] => by
    rw [show (FreeGroup.mk ([] : List (Fin 7 × Bool))) = 1 from rfl, map_one]
    exact rep_idA
  | l :: w => by
    rw [wordArr, show l :: w = [l] ++ w from rfl, lift_mk_append]
    exact rep_compA (rep_letArr l) (rep_wordArr w)

theorem rep_posArr (l : List (Fin 7)) : Rep 276 (posArr l)
    (wordOf (fun i : Fin 7 => gp i) l) := by
  rw [posArr, ← lift_mk_pos]
  exact rep_wordArr _

theorem mem_mLetters {i : Fin 7} (h : i ≠ 3) : (i : ℕ) ∈ mLetters := by
  revert i
  decide

theorem coe_mWord
    {l : List (Fin 7)}
    (hl : ∀ i ∈ l, i ≠ 3) :
    ((mWord l : co3M) : Equiv.Perm (Fin 276)) = wordOf (fun i : Fin 7 => gp i) l := by
  have h := wordOf_map co3M.subtype mGen l
  rw [mWord, ← coe_subtype, ← h]
  exact wordOf_congr fun i hi => coe_mGen (mem_mLetters (hl i hi))

theorem rep_mWord
    {l : List (Fin 7)}
    (hl : ∀ i ∈ l, i ≠ 3) :
    Rep 276 (posArr l) ((mWord l : co3M) : Equiv.Perm (Fin 276)) := by
  rw [coe_mWord hl]
  exact rep_posArr l

theorem mWord_append
    (l l' : List (Fin 7)) : mWord
    (l ++ l') = mWord l * mWord l' := by
  simp [mWord, wordOf]

theorem edgeFirst_letters (k : ℕ) : ∀ i ∈ edgeFirst k, i ≠ 3 := by
  intro i hi
  rcases Nat.lt_or_ge k 6 with hk | hk
  · have hmem : edgePairs.getD k ([], []) ∈ edgePairs := by
      rw [List.getD_eq_getElem _ _ (by simpa [edgePairs] using hk)]
      exact List.getElem_mem _
    exact (edgePairs_letters _ hmem).1 i hi
  · rw [edgeFirst, List.getD_eq_default _ _ (by simpa [edgePairs] using hk)] at hi
    simp at hi

theorem gLetters_letters (i : ℕ) : ∀ j ∈ gLetters i, j ≠ 3 := by
  intro j hj
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hj
  exact edgeFirst_letters k j hk

theorem mWord_gLetters
    (i : ℕ) :
    mWord (gLetters i) = ((gPaths.getD i []).map fun k => mWord (edgeFirst k)).prod := by
  rw [gLetters]
  induction gPaths.getD i [] with
  | nil => rfl
  | cons k p ih => rw [List.flatMap_cons, mWord_append, ih, List.map_cons, List.prod_cons]

@[expose] def edgeSet :
    Set co3M :=
    {x | ∃ p ∈ edgePairs, mWord p.1 = x}

theorem mWord_edgeFirst_mem_closure
    (k : ℕ) : mWord (edgeFirst k) ∈
    closure edgeSet := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · apply Subgroup.subset_closure
    refine ⟨edgePairs.getD k ([], []), ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ (by simpa [edgePairs] using hk)]
    exact List.getElem_mem _
  · rw [edgeFirst, List.getD_eq_default _ _ (by simpa [edgePairs] using hk)]
    exact (closure edgeSet).one_mem

theorem mWord_gLetters_mem_closure
    (i : ℕ) : mWord (gLetters i) ∈
    closure edgeSet := by
  rw [mWord_gLetters]
  exact list_prod_mem fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact mWord_edgeFirst_mem_closure k

theorem rep_gArrs :
    ∀ i < gArrs.size,
    Rep 276 gArrs[i]! ((mWord (gLetters i) : co3M) : Equiv.Perm (Fin 276)) := by
  intro i hi
  have hi3 : i < 3 := by simpa [gArrs] using hi
  rw [gArrs, getElem!_pos _ i (by simpa using hi3), Array.getElem_ofFn]
  exact rep_mWord (gLetters_letters i)

@[expose] def hPos : Array ℕ := hBFS.2.2.2

@[expose] def hIdx (t : Array ℕ) : ℕ := hPos[hKey t]! - 1

theorem model_enum_check :
    treeTabOK 276 gArrs hPar hLab hList 4608 = true ∧ keysOK [0, 1] hList 4608 = true ∧
    (∀ i < 7, isInvA 276 mGenArrs[i]! (invCand 276 mGenArrs[i]!) = true) ∧
    conjTabOK 276 mGenArrs (mGenArrs.map (invCand 276)) cBFS.2.1 cBFS.2.2 cBFS.1 (genArr 0)
      630 = true ∧
    keysOK [0, 1, 2, 3] cBFS.1 630 = true ∧
    (∀ k < 6, commutesA 276 (posArr (edgeFirst k)) (genArr 0) = true) :=
  Certificates.certificate3093

theorem mWord_edgeFirst_mem
    (k : ℕ) :
    mWord (edgeFirst k) ∈ edgeGroup
    := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [coe_mul, coe_mul, coe_ma]
    exact eq_of_eqA (rep_compA (rep_mWord (edgeFirst_letters k)) rep_g0)
      (rep_compA rep_g0 (rep_mWord (edgeFirst_letters k))) (model_enum_check.2.2.2.2.2 k hk)
  · rw [edgeFirst, List.getD_eq_default _ _ (by simpa [edgePairs] using hk)]
    exact edgeGroup.one_mem

theorem closure_edgeSet_le :
    closure
    edgeSet ≤ edgeGroup := by
  rw [closure_le]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have := mWord_edgeFirst_mem k
  rwa [edgeFirst, List.getD_eq_getElem _ _ hk] at this

@[expose] noncomputable def gH
    (i : ℕ)
    : edgeGroup :=
  ⟨mWord (gLetters i), closure_edgeSet_le (mWord_gLetters_mem_closure i)⟩

@[expose] noncomputable def eltH
    (j : ℕ) : edgeGroup := treeEval hPar
    hLab gH j

noncomputable abbrev perm
    (x : edgeGroup) : Equiv.Perm
    (Fin 276) := ((x : co3M) : _)

@[expose] noncomputable def permHom :
    edgeGroup →* Equiv.Perm
    (Fin 276) :=
  co3M.subtype.comp edgeGroup.subtype

theorem permHom_apply
    (x : edgeGroup) : permHom x = perm
    x := rfl

theorem perm_injective :
    Function.Injective perm := fun _
    _ h => Subtype.ext (Subtype.ext h)

theorem perm_eltH
    (j : ℕ) : perm
    (eltH j) = treeEval hPar hLab
    (fun i => perm (gH i)) j := by
  rw [← permHom_apply, eltH, map_treeEval]
  rfl

theorem rep_eltH
    {j : ℕ}
    (hj : j < 4608) : Rep 276 hList[j]!
    (perm (eltH j)) := by
  rw [perm_eltH]
  exact rep_treeTab model_enum_check.1 rep_gArrs j hj

theorem eltH_injOn
    {i j : ℕ}
    (hi : i < 4608) (hj : j < 4608)
    (h : eltH i = eltH j) : i = j :=
  eq_of_rep_of_keysOK (by decide) model_enum_check.2.1 hi hj (rep_eltH hi)
    (h ▸ rep_eltH hj)

theorem le_card_edgeGroup :
    4608 ≤
    Nat.card edgeGroup := by
  have hinj : Function.Injective fun j : Fin 4608 => eltH j :=
    fun i j h => Fin.ext (eltH_injOn i.2 j.2 h)
  simpa using Nat.card_le_card_of_injective _ hinj

theorem mGenArrs_getElem {k : ℕ} (hk : k < 7) : mGenArrs[k]! = co3MArrs[k]! := by
  rw [mGenArrs, getElem!_pos _ k (by simp [co3MArrs_size]; omega),
    getElem!_pos _ k (by rw [co3MArrs_size]; omega), Array.getElem_extract]
  simp

@[expose] noncomputable def mG (k : ℕ) : co3M :=
  if hk : k < 7 then ⟨permOfArr 276 co3MArrs[k]!, by
    rw [co3M_eq]; exact subset_closure ⟨⟨k, hk⟩, rfl⟩⟩ else 1

theorem rep_mG {k : ℕ} (hk : k < 7) :
    Rep 276 mGenArrs[k]! ((mG k : co3M) : _) := by
  simp only [mG, hk, ↓reduceDIte]
  rw [mGenArrs_getElem hk]
  exact rep_co3MArr (by omega)

theorem rep_conjTab {n : ℕ} {G Gi : Array (Array ℕ)} {par lab : Array ℕ}
    {T : Array (Array ℕ)} {t₀ : Array ℕ} {N : ℕ} (h : conjTabOK n G Gi par lab T t₀ N = true)
    {x : ℕ → Equiv.Perm (Fin n)} {g₀ : Equiv.Perm (Fin n)} (hx : ∀ i < G.size, Rep n G[i]! (x i))
    (hxi : ∀ i < G.size, Rep n Gi[i]! (x i)⁻¹) (h₀ : Rep n t₀ g₀) :
    ∀ j < N, Rep n T[j]! ((treeEval par lab x j)⁻¹ * g₀ * treeEval par lab x j) := by
  unfold conjTabOK at h
  rw [Bool.and_eq_true, allLt_iff] at h
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [treeEval_zero, inv_one, one_mul, mul_one]
      exact Rep.of_eqA h₀ h.1
    · have := h.2 j hj
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with h0 | ⟨⟨hp, hl⟩, he⟩
      · omega
      rw [treeEval_of_lt par lab x hj0 hp]
      have hr := rep_compA (hxi _ hl) (rep_compA (ih _ hp (by omega)) (hx _ hl))
      refine Rep.of_eqA ?_ he
      convert hr using 1
      group

theorem mGenArrs_size : mGenArrs.size = 7 := by simp [mGenArrs, co3MArrs_size]

theorem rep_mG_inv {k : ℕ}
    (hk : k < 7) :
    Rep 276 (mGenArrs.map (invCand 276))[k]! ((mG k : co3M) : Equiv.Perm (Fin 276))⁻¹ := by
  rw [getElem!_pos _ k (by rw [Array.size_map, mGenArrs_size]; exact hk), Array.getElem_map,
    ← getElem!_pos mGenArrs k (by rw [mGenArrs_size]; exact hk)]
  exact rep_inv_of_isInvA (rep_mG hk) (model_enum_check.2.2.1 k hk)

@[expose] noncomputable def conjM (j : ℕ) : co3M := treeEval cBFS.2.1 cBFS.2.2 mG j

theorem coe_conjM (j : ℕ) : ((conjM j : co3M) : Equiv.Perm (Fin 276)) =
    treeEval cBFS.2.1 cBFS.2.2 (fun k => ((mG k : co3M) : Equiv.Perm (Fin 276))) j := by
  rw [conjM, ← coe_subtype, map_treeEval]

theorem rep_conjM
    {j : ℕ} (hj : j < 630) :
    Rep 276 cBFS.1[j]! (((conjM j)⁻¹ * ma * conjM j : co3M) : Equiv.Perm (Fin 276)) := by
  have h := rep_conjTab model_enum_check.2.2.2.1 (x := fun k => ((mG k : co3M) : _))
    (fun i hi => rep_mG (by rwa [mGenArrs_size] at hi))
    (fun i hi => rep_mG_inv (by rwa [mGenArrs_size] at hi)) rep_g0 j hj
  have e : (((conjM j)⁻¹ * ma * conjM j : co3M) : Equiv.Perm (Fin 276)) =
      (treeEval cBFS.2.1 cBFS.2.2 (fun k => ((mG k : co3M) : Equiv.Perm (Fin 276))) j)⁻¹ *
        gp 0 * treeEval cBFS.2.1 cBFS.2.2 (fun k => ((mG k : co3M) : Equiv.Perm (Fin 276))) j := by
    rw [coe_mul, coe_mul, coe_inv, coe_ma, coe_conjM]
  rw [e]
  exact h

theorem le_card_classA :
    630 ≤ Nat.card classA := by
  let f : Fin 630 → classA := fun j =>
    ⟨(conjM j)⁻¹ * ma * conjM j, isConj_iff.2 ⟨(conjM j)⁻¹, by group⟩⟩
  have hinj : Function.Injective f := by
    intro i j h
    have h' := congrArg (fun x : classA => ((x : co3M) : Equiv.Perm (Fin 276))) h
    exact Fin.ext (eq_of_rep_of_keysOK (by decide) model_enum_check.2.2.2.2.1 i.2 j.2
      (rep_conjM i.2) (h' ▸ rep_conjM j.2))
  simpa using Nat.card_le_card_of_injective f hinj

theorem card_edgeGroup_mul :
    Nat.card edgeGroup * Nat.card
    classA = 2903040 := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct co3M) ma)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
  have horb : MulAction.orbit (ConjAct co3M) ma = classA := by
    ext x
    rw [ConjAct.mem_orbit_conjAct]
    exact isConj_comm
  rw [horb, ← Nat.card_coe_set_eq] at h1
  rw [h1, ← card_co3M]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem card_edgeGroup_classA :
    Nat.card edgeGroup = 4608 ∧ Nat.card
    classA = 630 := by
  have h := card_edgeGroup_mul
  have h1 := le_card_edgeGroup
  have h2 := le_card_classA
  constructor <;> nlinarith

theorem exists_eltH
    (x : edgeGroup) :
    ∃ j < 4608, eltH j = x := by
  have hinj : Function.Injective fun j : Fin 4608 => eltH j :=
    fun i j h => Fin.ext (eltH_injOn i.2 j.2 h)
  obtain ⟨j, hj⟩ := (hinj.bijective_of_nat_card_le
    (by rw [card_edgeGroup_classA.1, Nat.card_fin])).2 x
  exact ⟨j, j.2, hj⟩

theorem exists_hList
    (x : edgeGroup) :
    ∃ j < 4608, Rep 276 hList[j]!
    (perm x) := by
  obtain ⟨j, hj, rfl⟩ := exists_eltH x
  exact ⟨j, hj, rep_eltH hj⟩

end CFSG.EvenSmallLie.SympSix.Co3Ident
