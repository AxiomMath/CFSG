module

public import CFSG.GH74.QTGen4.U42.ModelExtLattice
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Cover

public section

namespace CFSG.GH74.QTGen4.U42.ModelExtLatticeB

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.GH74.QTGen4.U42.ModelExtLattice


theorem invL_repL {l : PL} {σ : Equiv.Perm (Fin 45)} (h : RepL l σ) : RepL (invL l) σ⁻¹ := by
  refine ⟨by simp [invL], fun i => ?_⟩
  have hσ : σ (σ⁻¹ i) = i := by simp
  have hp : (l.getD ((σ⁻¹ i : Fin 45) : ℕ) 0 == (i : ℕ)) = true := by
    rw [beq_iff_eq, h.2 (σ⁻¹ i), hσ]
  have hmem : ((σ⁻¹ i : Fin 45) : ℕ) ∈ List.range 45 := List.mem_range.2 (σ⁻¹ i).2
  obtain ⟨a, ha⟩ : ∃ a, (List.range 45).find? (fun j => l.getD j 0 == (i : ℕ)) = some a := by
    rcases hfs : (List.range 45).find? (fun j => l.getD j 0 == (i : ℕ)) with _ | a
    · exfalso
      have := List.find?_eq_none.1 hfs _ hmem
      exact this hp
    · exact ⟨a, rfl⟩
  have ha45 : a < 45 := List.mem_range.1 (List.mem_of_find?_eq_some ha)
  have hpa : (l.getD a 0 == (i : ℕ)) = true := by
    simpa using List.find?_some ha
  have hpa' : l.getD a 0 = (i : ℕ) := beq_iff_eq.1 hpa
  have hsa : σ ⟨a, ha45⟩ = i := Fin.ext ((h.2 ⟨a, ha45⟩).symm.trans hpa')
  have hfix : (⟨a, ha45⟩ : Fin 45) = σ⁻¹ i := Equiv.Perm.eq_inv_iff_eq.2 hsa
  have hget : (invL l).getD (i : ℕ) 0 = ((List.range 45).find? (fun j => l.getD j 0 == (i : ℕ))).getD 0 := by
    simp [invL, List.getD_eq_getElem?_getD, i.2]
  rw [hget, ha]
  exact congrArg Fin.val hfix

@[expose] def letterY (r : Y) (i : ℕ) : Y :=
  if i < 5 then gTY i else if i = 5 then r else if i = 6 then r⁻¹ else (gTY (i - 7))⁻¹

theorem letter_repL {r : Y} {rL : PL} (hr : RepL rL ((r : Y) : P45)) (i : ℕ) :
    RepL (letterL rL i) ((letterY r i : Y) : P45) := by
  unfold letterL letterY
  split_ifs with h1 h2 h3
  · exact repL_gTY i
  · exact hr
  · exact invL_repL hr
  · exact invL_repL (repL_gTY (i - 7))

theorem foldl_repL {r : Y} {rL : PL} (hr : RepL rL ((r : Y) : P45)) (w : List ℕ) (acc : PL) (a : Y)
    (ha : RepL acc ((a : Y) : P45)) :
    RepL (w.foldl (fun x i => comp x (letterL rL i)) acc)
      ((w.foldl (fun x i => x * letterY r i) a : Y) : P45) := by
  induction w generalizing acc a with
  | nil => simpa using ha
  | cons i w ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (repL_mul ha (letter_repL hr i))

theorem c3pow_repL (n : ℕ) : RepL (c3pow n) ((c3Y ^ n : Y) : P45) := by
  induction n with
  | zero => exact repL_one 45
  | succ n ih =>
    have e : ((c3Y ^ (n + 1) : Y) : P45) = (c3Y : P45) * ((c3Y ^ n : Y) : P45) := by
      rw [pow_succ']
      rfl
    rw [e]
    exact repL_mul repL_c3 ih

@[expose] def latTLetters : Bool := latTData.all fun x => x.2.2.2.all fun i => decide (i < 12)

theorem latTLetters_true : latTLetters = true := by decide +kernel

theorem latT_letters {x : Nat × Nat × Nat × List Nat} (hx : x ∈ latTData) {i : Nat}
    (hi : i ∈ x.2.2.2) : i < 12 := by
  have h := latTLetters_true
  simp only [latTLetters, List.all_eq_true, decide_eq_true_eq] at h
  exact h x hx i hi

@[expose] def latTCov : Bool :=
  (List.range 8).all fun j => (List.range 3).all fun a => (List.range 3).all fun b =>
    decide (j < 2) || latTData.any fun x => x.1 == j && x.2.1 == a && x.2.2.1 == b

theorem latTCov_true : latTCov = true := by decide +kernel

theorem latT_cov {j a b : ℕ} (hj : 2 ≤ j) (hj8 : j < 8) (ha : a < 3) (hb : b < 3) :
    ∃ x ∈ latTData, x.1 = j ∧ x.2.1 = a ∧ x.2.2.1 = b := by
  have h := latTCov_true
  simp only [latTCov, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h j hj8 a ha b hb with h1 | ⟨x, hx, h2⟩
  · omega
  · exact ⟨x, hx, h2.1.1, h2.1.2, h2.2⟩

theorem latT_row {j a b : ℕ} {w : List ℕ} (hx : (j, a, b, w) ∈ latTData) :
    wordL (comp (comp (c3pow a) (DL j)) (c3pow b)) w = c3L := by
  have h := chkLatT_true
  simp only [chkLatT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact (h.2 _ hx).2

theorem mem_T_of_lt5 {i : ℕ} (hi : i < 5) : gTY i ∈ T :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem letterY_mem {K : Subgroup Y} (hT : T ≤ K) {r : Y} (hrK : r ∈ K) {i : ℕ} (hi : i < 12) :
    letterY r i ∈ K := by
  unfold letterY
  split_ifs with h1 h2 h3
  · exact hT (mem_T_of_lt5 h1)
  · exact hrK
  · exact K.inv_mem hrK
  · exact K.inv_mem (hT (mem_T_of_lt5 (by omega)))

theorem foldl_mem {K : Subgroup Y} (hT : T ≤ K) {r : Y} (hrK : r ∈ K) {w : List ℕ}
    (hw : ∀ i ∈ w, i < 12) (a : Y) (ha : a ∈ K) :
    w.foldl (fun x i => x * letterY r i) a ∈ K := by
  induction w generalizing a with
  | nil => simpa using ha
  | cons i w ih =>
    simp only [List.foldl_cons]
    exact ih (fun k hk => hw k (by simp [hk])) _
      (K.mul_mem ha (letterY_mem hT hrK (hw i (by simp))))

theorem c3_mem_of_row {K : Subgroup Y} (hT : T ≤ K) {j a b : ℕ} {w : List ℕ}
    (hx : (j, a, b, w) ∈ latTData) {r : Y} (hr : r = c3Y ^ a * Dj j * c3Y ^ b) (hrK : r ∈ K) :
    c3Y ∈ K := by
  have hw : ∀ i ∈ w, i < 12 := fun i hi => latT_letters hx hi
  have hW := latT_row hx
  have hr1 : RepL (comp (c3pow a) (DL j)) ((c3Y ^ a * Dj j : Y) : P45) :=
    repL_mul (c3pow_repL a) (repL_Dj j)
  have hrL : RepL (comp (comp (c3pow a) (DL j)) (c3pow b)) ((r : Y) : P45) := by
    rw [hr]
    exact repL_mul hr1 (c3pow_repL b)
  have hid : RepL idL ((1 : Y) : P45) := repL_one 45
  have hfold := foldl_repL hrL w idL 1 hid
  have hc : RepL c3L ((w.foldl (fun x i => x * letterY r i) 1 : Y) : P45) := by
    rw [← hW]
    exact hfold
  have heq : c3Y = w.foldl (fun x i => x * letterY r i) 1 :=
    Subtype.ext (eq_of_repL repL_c3 hc)
  rw [heq]
  exact foldl_mem hT hrK hw 1 K.one_mem

end CFSG.GH74.QTGen4.U42.ModelExtLatticeB
