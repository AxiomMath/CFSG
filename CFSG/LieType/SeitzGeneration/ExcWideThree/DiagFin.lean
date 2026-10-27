module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFinLists
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHighThree

section Cols


@[expose] def rfCols (w : WeylGroup Tag.E6) : List (List ℤ) :=
  List.ofFn fun j : Fin Tag.E6.rank => List.ofFn (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))

theorem rf_smul_apply (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    (w • v) i = ∑ j, v j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [smul_def, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  rfl

theorem rf_map_range_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn fun i : Fin n => f i := by
  apply List.ext_getElem <;> simp

theorem rf_cols_row (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank) :
    (rfCols w).map (fun b => b.getD i 0) =
      List.ofFn fun j : Fin Tag.E6.rank => (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i := by
  unfold rfCols
  rw [List.map_ofFn]
  congr 1
  funext j
  simp [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_ofFn]

@[expose] def rfLincombZ (v : List ℤ) (β : List (List ℤ)) : List ℤ :=
  (List.range 6).map fun i => rfDotL v (β.map fun b => b.getD i 0)

theorem rfLincombZ_cols (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    rfLincombZ (List.ofFn v) (rfCols w) = List.ofFn (w • v) := by
  unfold rfLincombZ
  show (List.range Tag.E6.rank).map _ = _
  rw [rf_map_range_eq_ofFn]
  congr 1
  funext i
  rw [rf_cols_row, rfDotL_ofFn, rf_smul_apply]

theorem rfMt_cols (w : WeylGroup Tag.E6) (l : Fin Tag.E6.rank → ℤ) :
    rfMt (List.ofFn l) (rfCols w) =
      List.ofFn fun j : Fin Tag.E6.rank =>
        ∑ i, l i * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i := by
  unfold rfMt rfCols
  rw [List.map_ofFn]
  congr 1

theorem rf_ofFn_getD {n : ℕ} (N : List ℤ) (h : N.length = n) :
    List.ofFn (fun i : Fin n => N.getD i 0) = N := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]

theorem exists_fixed_of_rfHasFix (w : WeylGroup Tag.E6) (h : rfHasFix (rfCols w) = true) :
    ∃ l : Fin Tag.E6.rank → ℤ, l ≠ 0 ∧
      ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (w • v) i = ∑ i, l i * v i := by
  unfold rfHasFix at h
  rw [List.any_eq_true] at h
  obtain ⟨j, -, hjt⟩ := h
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hjt
  obtain ⟨hN0, hNfix⟩ := hjt
  set e := rfUnit j with he
  set l1 := rfMt e (rfCols w) with hl1
  set l2 := rfMt l1 (rfCols w) with hl2
  set N := List.zipWith (· + ·) e (List.zipWith (· + ·) l1 l2) with hN
  have hcols : (rfCols w).length = 6 := by
    unfold rfCols
    rw [List.length_ofFn]
    rfl
  have hlen6 : N.length = 6 := by
    simp [hN, he, hl1, hl2, rfUnit, rfMt, hcols]
  have hlen : N.length = Tag.E6.rank := hlen6
  set Nf : Fin Tag.E6.rank → ℤ := fun i => N.getD i 0 with hNf
  have hNofn : List.ofFn Nf = N := rf_ofFn_getD N hlen
  have hfixj : ∀ j' : Fin Tag.E6.rank,
      ∑ i, Nf i * (w • (Pi.single j' 1 : Fin Tag.E6.rank → ℤ)) i = Nf j' := by
    have h2 := hNfix
    rw [← hNofn, rfMt_cols] at h2
    intro j'
    exact congrFun (List.ofFn_injective h2) j'
  refine ⟨Nf, ?_, fun v => ?_⟩
  · intro h0
    apply hN0
    rw [← hNofn, h0]
    show List.ofFn (fun _ : Fin Tag.E6.rank => (0 : ℤ)) = List.replicate 6 0
    rw [List.ofFn_const]
    rfl
  · calc ∑ i, Nf i * (w • v) i
        = ∑ i, Nf i * ∑ j, v j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i := by
          exact Finset.sum_congr rfl fun i _ => by rw [rf_smul_apply w v i]
      _ = ∑ j, v j * ∑ i, Nf i * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ j, v j * Nf j := by simp only [hfixj]
      _ = ∑ i, Nf i * v i := Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem rf_getD_map_res3 : ∀ (b : List ℤ) (i : ℕ),
    (b.map rfRes3).getD i 0 = rfRes3 (b.getD i 0)
  | [], i => by simp [rfRes3]
  | x :: b, 0 => by simp
  | x :: b, i + 1 => by simpa using rf_getD_map_res3 b i

theorem rf_getD_range_map {α : Type*} [Inhabited α] (f : ℕ → α) (d : α) (n i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem rfLincomb3_getD_cast (m : List ℕ) (β : List (List ℤ)) (i : ℕ) (hi : i < 6) :
    (((rfLincomb3 m (β.map (·.map rfRes3))).getD i 0 : ℕ) : ℤ) =
      rfDotL (m.map (fun x : ℕ => (x : ℤ))) (β.map fun b => b.getD i 0) % 3 := by
  unfold rfLincomb3
  rw [rf_getD_range_map _ _ 6 i hi]
  have h1 : (β.map (·.map rfRes3)).map (fun b => b.getD i 0) =
      (β.map fun b => b.getD i 0).map rfRes3 := by
    rw [List.map_map, List.map_map]
    congr 1
    funext b
    exact rf_getD_map_res3 b i
  rw [h1, Int.natCast_mod, ← rfDotN_res3]
  push_cast
  rfl

@[expose] def rfLamZ : Fin Tag.E6.rank → ℤ := ![4, 3, 5, 6, 4, 2]

theorem rfLamN_getD : ∀ i : Fin Tag.E6.rank, ((rfLamN.getD i 0 : ℕ) : ℤ) = rfLamZ i := by
  decide +kernel

theorem three_dvd_cartan_rfLamZ : ∀ j : Fin Tag.E6.rank,
    (3 : ℤ) ∣ ∑ k, Tag.E6.cartan j k * rfLamZ k := by
  decide +kernel

theorem three_dvd_smul_rfLamZ_sub (w : WeylGroup Tag.E6) :
    ∀ i, (3 : ℤ) ∣ (w • rfLamZ) i - rfLamZ i := by
  refine (coxeterSystem Tag.E6).simple_induction_left
    (p := fun w => ∀ i, (3 : ℤ) ∣ (w • rfLamZ) i - rfLamZ i) w ?_ ?_
  · intro i
    simp
  · intro w j ih i
    rw [mul_smul]
    change (3 : ℤ) ∣ (simple Tag.E6 j • w • rfLamZ) i - rfLamZ i
    rw [simple_smul, reflect]
    have hsum : (3 : ℤ) ∣ ∑ k, Tag.E6.cartan j k * (w • rfLamZ) k := by
      have e : ∑ k, Tag.E6.cartan j k * (w • rfLamZ) k =
          ∑ k, Tag.E6.cartan j k * rfLamZ k +
            ∑ k, Tag.E6.cartan j k * ((w • rfLamZ) k - rfLamZ k) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e]
      exact dvd_add (three_dvd_cartan_rfLamZ j)
        (Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (ih k) _)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e : (w • rfLamZ) i - (∑ k, Tag.E6.cartan j k * (w • rfLamZ) k) *
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ) i - rfLamZ i =
        ((w • rfLamZ) i - rfLamZ i) - (∑ k, Tag.E6.cartan j k * (w • rfLamZ) k) *
          (Pi.single j 1 : Fin Tag.E6.rank → ℤ) i := by ring
    rw [e]
    exact dvd_sub (ih i) (Dvd.dvd.mul_right hsum _)

theorem rfCCond_rfCols (w : WeylGroup Tag.E6) :
    rfCCond ((rfCols w).map (·.map rfRes3)) = true := by
  unfold rfCCond
  have hlen : (rfLincomb3 rfLamN ((rfCols w).map (·.map rfRes3))).length = rfLamN.length := by
    simp [rfLincomb3, rfLamN]
  refine (rfModEq3_iff _ _ hlen).2 fun i => ?_
  by_cases hi : i < 6
  · have h1 := rfLincomb3_getD_cast rfLamN (rfCols w) i hi
    have hlist : rfLamN.map (fun x : ℕ => (x : ℤ)) = List.ofFn rfLamZ := by decide +kernel
    have hrow := rf_cols_row w ⟨i, hi⟩
    rw [hlist, hrow, rfDotL_ofFn] at h1
    have h2 : ∑ j, rfLamZ j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ⟨i, hi⟩ =
        (w • rfLamZ) ⟨i, hi⟩ := (rf_smul_apply w rfLamZ ⟨i, hi⟩).symm
    rw [h2] at h1
    have h3 := three_dvd_smul_rfLamZ_sub w ⟨i, hi⟩
    have h4 : ((rfLamN.getD i 0 : ℕ) : ℤ) = rfLamZ ⟨i, hi⟩ := rfLamN_getD ⟨i, hi⟩
    omega
  · have h6 : ¬ i < rfLamN.length := by simpa [rfLamN] using hi
    have h7 : ¬ i < (rfLincomb3 rfLamN ((rfCols w).map (·.map rfRes3))).length := by
      rw [hlen]; exact h6
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 h6),
      List.getElem?_eq_none (not_lt.1 h7)]

theorem rf_cartan_symm (i j : Fin Tag.E6.rank) : Tag.E6.cartan i j = Tag.E6.cartan j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem rf_map_cast_eq_ofFn (mL : List ℕ) (h : mL.length = Tag.E6.rank) :
    mL.map (fun x : ℕ => (x : ℤ)) =
      List.ofFn (fun l : Fin Tag.E6.rank => ((mL.getD l 0 : ℕ) : ℤ)) := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    have hi : i < mL.length := by simpa using h1
    simp [List.getD_eq_getElem?_getD, hi]

theorem rfMOf_length (κ : List ℕ) : (rfMOf κ).length = Tag.E6.rank := by
  simp [rfMOf, rfAdjN]
  rfl

theorem exists_lift_of_rfCls0 (w : WeylGroup Tag.E6) {κs : List (List ℕ)}
    (hκs : ∀ κ ∈ κs, κ.length = Tag.E6.rank)
    (h : rfCls0 ((rfCols w).map (·.map rfRes3)) κs = true) :
    ∀ κ ∈ κs, ∃ m : Fin Tag.E6.rank → ℤ,
      (∀ j : Fin Tag.E6.rank, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m l) - (κ.getD j 0 : ℤ)) ∧
      ∀ i, (3 : ℤ) ∣ (w • m) i - m i := by
  intro κ hκ
  have h' := List.all_eq_true.1 h κ hκ
  simp only [Bool.and_eq_true] at h'
  obtain ⟨hA, hW⟩ := h'
  set mL := rfMOf κ with hmL
  have hmlen : mL.length = Tag.E6.rank := rfMOf_length κ
  have hmcast := rf_map_cast_eq_ofFn mL hmlen
  refine ⟨fun l => ((mL.getD l 0 : ℕ) : ℤ), ?_, ?_⟩
  · intro j
    have hlen : (rfCartanMod3.map fun row => rfDotN row mL).length = κ.length := by
      rw [hκs κ hκ]; simp [rfCartanMod3]; rfl
    have h1 := (rfModEq3_iff _ _ hlen).1 hA j
    have hrow : (rfCartanMod3.map fun row => rfDotN row mL).getD j 0 =
        rfDotN ((List.ofFn (fun l : Fin Tag.E6.rank => Tag.E6.cartan j l)).map rfRes3) mL := by
      rw [rfCartanMod3_eq, rfCartanL_eq, List.map_ofFn, List.map_ofFn, List.getD_eq_getElem?_getD]
      simp [List.getElem?_ofFn]
    rw [hrow] at h1
    rw [rfDotN_comm (List.map rfRes3 _) mL] at h1
    have h2 := rfDotN_res3 mL (List.ofFn fun l : Fin Tag.E6.rank => Tag.E6.cartan j l)
    rw [hmcast, rfDotL_ofFn] at h2
    have h3 : ∑ l : Fin Tag.E6.rank, ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) * Tag.E6.cartan j l =
        ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) :=
      Finset.sum_congr rfl fun l _ => by rw [mul_comm (Tag.E6.cartan l j), rf_cartan_symm l j]
    rw [h3] at h2
    show (3 : ℤ) ∣ ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) -
      ((κ.getD (j : ℕ) 0 : ℕ) : ℤ)
    omega
  · intro i
    have hlen : (rfLincomb3 mL ((rfCols w).map (·.map rfRes3))).length = mL.length := by
      rw [hmlen]; simp [rfLincomb3]; rfl
    have h1 := (rfModEq3_iff _ _ hlen).1 hW i
    by_cases hi : i.val < 6
    · have h2 := rfLincomb3_getD_cast mL (rfCols w) i.val hi
      have hrow := rf_cols_row w i
      rw [hmcast, hrow, rfDotL_ofFn] at h2
      have h3 : ∑ j : Fin Tag.E6.rank, ((mL.getD (j : ℕ) 0 : ℕ) : ℤ) *
          (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i =
          (w • fun l : Fin Tag.E6.rank => ((mL.getD (l : ℕ) 0 : ℕ) : ℤ)) i :=
        (rf_smul_apply w _ i).symm
      rw [h3] at h2
      show (3 : ℤ) ∣ (w • fun l : Fin Tag.E6.rank => ((mL.getD (l : ℕ) 0 : ℕ) : ℤ)) i -
        ((mL.getD (i : ℕ) 0 : ℕ) : ℤ)
      omega
    · exact absurd i.2 hi

@[expose] def RfValidFrom (cs : List (List (List ℤ × List ℤ))) :
    List (List ℤ) → List (List ℤ) → Prop
  | _, [] => True
  | sel, r :: rest =>
    (r, rfCartanL.map fun row => rfDotL row r) ∈ cs.getD sel.length [] ∧
      rfGramOK sel (r, rfCartanL.map fun row => rfDotL row r) = true ∧
      RfValidFrom cs (sel ++ [r]) rest

theorem mem_rfLeaves (cs : List (List (List ℤ × List ℤ))) :
    ∀ (rest sel : List (List ℤ)), RfValidFrom cs sel rest →
      sel ++ rest ∈ rfLeaves cs rest.length sel
  | [], sel, _ => by simp [rfLeaves]
  | r :: rest, sel, ⟨h1, h2, h3⟩ => by
    rw [List.length_cons, rfLeaves, List.mem_flatMap]
    refine ⟨(r, rfCartanL.map fun row => rfDotL row r), List.mem_filter.2 ⟨h1, h2⟩, ?_⟩
    have := mem_rfLeaves cs rest (sel ++ [r]) h3
    simpa using this

theorem rfValidFrom_of_forall (cs : List (List (List ℤ × List ℤ))) :
    ∀ (rest sel : List (List ℤ)),
      (∀ (t : ℕ) (ht : t < rest.length),
        (rest[t], rfCartanL.map fun row => rfDotL row rest[t]) ∈ cs.getD (sel.length + t) [] ∧
        rfGramOK (sel ++ rest.take t) (rest[t], rfCartanL.map fun row => rfDotL row rest[t]) =
          true) → RfValidFrom cs sel rest
  | [], sel, _ => trivial
  | r :: rest, sel, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, List.append_nil, Nat.add_zero] at h0
    refine ⟨h0.1, h0.2, rfValidFrom_of_forall cs rest (sel ++ [r]) ?_⟩
    intro t ht
    have h1 := h (t + 1) (by simpa using ht)
    have e1 : sel ++ (r :: rest).take (t + 1) = (sel ++ [r]) ++ rest.take t := by simp
    have e2 : sel.length + (t + 1) = (sel ++ [r]).length + t := by simp; omega
    simp only [List.getElem_cons_succ] at h1
    rw [e1, e2] at h1
    exact h1

@[expose] def RfFixes (w : WeylGroup Tag.E6) (κ : List ℕ) : Prop :=
  ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
    (∑ i : Fin Tag.E6.rank, ((κ.getD (i : ℕ) 0 : ℕ) : ℤ) *
      (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - ((κ.getD (t : ℕ) 0 : ℕ) : ℤ)

theorem rfCols_getElem (w : WeylGroup Tag.E6) (t : Fin Tag.E6.rank) :
    (rfCols w)[(t : ℕ)]'(by simp [rfCols]) =
      List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) := by
  simp [rfCols]

theorem ofFn_smul_mem_e6ArtifactRoots (w : WeylGroup Tag.E6) (t : Fin Tag.E6.rank) :
    List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) ∈ e6ArtifactRoots := by
  have h : IsRoot Tag.E6 (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) :=
    IsRoot.smul (IsRoot.basis t) w
  exact isRoot_iff_mem_artifactRoots.1 h

theorem rf_residue_cond (w : WeylGroup Tag.E6) {κ : List ℕ} (hκ : κ.length = Tag.E6.rank)
    (hf : RfFixes w κ) (t : Fin Tag.E6.rank) :
    rfDotN ((List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ))).map rfRes3) κ % 3 =
      κ.getD (t : ℕ) 0 % 3 := by
  have h1 := rfDotN_res3 κ (List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)))
  rw [rf_map_cast_eq_ofFn κ hκ, rfDotL_ofFn] at h1
  rw [rfDotN_comm]
  have h2 := hf t
  omega

theorem rfCartanL_getD (i t : Fin Tag.E6.rank) :
    (rfCartanL.getD (i : ℕ) []).getD (t : ℕ) 0 = Tag.E6.cartan i t := by
  rw [rfCartanL_eq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]

theorem rf_dot_cartan_cols (w : WeylGroup Tag.E6) (i t : Fin Tag.E6.rank) :
    rfDotL (List.ofFn (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)))
      (rfCartanL.map fun row =>
        rfDotL row (List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)))) =
      Tag.E6.cartan i t := by
  have h1 := rfIform_ofFn (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
    (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ))
  rw [iform_smul, iform_single_left] at h1
  have h2 : Tag.E6.symmetrizer i i = 1 := by
    simp [Tag.symmetrizer]
  rw [h2, one_mul] at h1
  have h3 : ∑ j, Tag.E6.cartan i j * (Pi.single t 1 : Fin Tag.E6.rank → ℤ) j =
      Tag.E6.cartan i t := by
    simp [Pi.single_apply]
  rw [h3] at h1
  exact h1

theorem rf_gram_cols (w : WeylGroup Tag.E6) (t : Fin Tag.E6.rank) :
    rfGramOK ((rfCols w).take t)
      (List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)),
        rfCartanL.map fun row =>
          rfDotL row (List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)))) = true := by
  have hcl : (rfCols w).length = Tag.E6.rank := by simp [rfCols]
  have htake : ((rfCols w).take t).length = t := by
    rw [List.length_take, hcl]; exact min_eq_left t.2.le
  unfold rfGramOK
  rw [htake]
  simp only [List.all_eq_true, beq_iff_eq]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  have hi' : i < t := by
    have h0 := hi
    simp only [List.length_zip, htake, List.length_map] at h0
    exact lt_of_lt_of_le (lt_min_iff.1 h0).1 le_rfl
  have hi6 : i < Tag.E6.rank := lt_trans hi' t.2
  simp only [List.getElem_zip, List.getElem_take, List.getElem_map]
  rw [rfCols_getElem w ⟨i, hi6⟩]
  have h1 := rf_dot_cartan_cols w ⟨i, hi6⟩ t
  have h2 := rfCartanL_getD ⟨i, hi6⟩ t
  rw [h1, ← h2]
  have hlen : i < rfCartanL.length := show i < 6 from hi6
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]

theorem rfCols_validFrom (w : WeylGroup Tag.E6) {κ₁ κ₂ : List ℕ}
    (h₁ : κ₁.length = Tag.E6.rank) (h₂ : κ₂.length = Tag.E6.rank)
    (hf₁ : RfFixes w κ₁) (hf₂ : RfFixes w κ₂) :
    RfValidFrom ((List.range 6).map (rfCands κ₁ κ₂)) [] (rfCols w) := by
  apply rfValidFrom_of_forall
  intro t ht
  have hcl : (rfCols w).length = Tag.E6.rank := by simp [rfCols]
  have ht6 : t < Tag.E6.rank := hcl ▸ ht
  set tf : Fin Tag.E6.rank := ⟨t, ht6⟩ with htf
  have hget : (rfCols w)[t]'ht = List.ofFn (w • (Pi.single tf 1 : Fin Tag.E6.rank → ℤ)) :=
    rfCols_getElem w tf
  simp only [List.length_nil, zero_add, List.nil_append]
  rw [hget]
  refine ⟨?_, ?_⟩
  · rw [rf_getD_range_map _ _ 6 t ht6]
    unfold rfCands
    rw [List.mem_map]
    refine ⟨List.ofFn (w • (Pi.single tf 1 : Fin Tag.E6.rank → ℤ)), ?_, rfl⟩
    rw [List.mem_map]
    refine ⟨(List.ofFn (w • (Pi.single tf 1 : Fin Tag.E6.rank → ℤ)),
      (List.ofFn (w • (Pi.single tf 1 : Fin Tag.E6.rank → ℤ))).map rfRes3), ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold rfRoots
      rw [List.mem_map]
      exact ⟨_, ofFn_smul_mem_e6ArtifactRoots w tf, rfl⟩
    · simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨rf_residue_cond w h₁ hf₁ tf, rf_residue_cond w h₂ hf₂ tf⟩
  · have hg := rf_gram_cols w tf
    simpa using hg

theorem rfPlaneCheck_sound (w : WeylGroup Tag.E6) {κ₁ κ₂ : List ℕ}
    (h₁ : κ₁.length = Tag.E6.rank) (h₂ : κ₂.length = Tag.E6.rank)
    (hf₁ : RfFixes w κ₁) (hf₂ : RfFixes w κ₂) (hchk : rfPlaneCheck κ₁ κ₂ = true) :
    (∃ l : Fin Tag.E6.rank → ℤ, l ≠ 0 ∧
        ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (w • v) i = ∑ i, l i * v i) ∨
      rfCls0 ((rfCols w).map (·.map rfRes3)) (rfPlaneVecs κ₁ κ₂) = true := by
  have hmem := mem_rfLeaves ((List.range 6).map (rfCands κ₁ κ₂)) (rfCols w) []
    (rfCols_validFrom w h₁ h₂ hf₁ hf₂)
  have hcl : (rfCols w).length = 6 := by
    unfold rfCols; rw [List.length_ofFn]; rfl
  rw [List.nil_append, hcl] at hmem
  have hok := List.all_eq_true.1 hchk _ hmem
  unfold rfLeafOK at hok
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
  rcases hok with (hc | hcls) | hfix
  · exact absurd (rfCCond_rfCols w) (by simp [hc])
  · exact Or.inr hcls
  · exact Or.inl (exists_fixed_of_rfHasFix w hfix)

end Cols

end CFSG.LieType.SeitzGeneration.ExcWideThree
