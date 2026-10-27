module

public import Certificates.Data.Kernel.WEMK
public import CFSG.LocalAnalysis.StandardType.GGWitExcModelRows
public import CFSG.LocalAnalysis.StandardType.GGWitExcModelAbs
public import CFSG.Certificates.Kernel.TWLK6Sound

public section

namespace CFSG.StandardType.ZS.WEMK

open Certificates.ExcModel Certificates.WEMK Certificates.TWLK CFSG.StandardType.ZS

@[expose] def toM (n : ℕ) (A : NMat) : Mat n := Matrix.of fun i j => (((A.getD i []).getD j 0 : ℕ) : ZMod 13)

@[expose] def vecN (n : ℕ) (v : List ℕ) : Fin n → ZMod 13 := fun i => ((v.getD i 0 : ℕ) : ZMod 13)

@[expose] def WF (n : ℕ) (A : NMat) : Prop := A.length = n ∧ ∀ r ∈ A, r.length = n

def Red (n : ℕ) (A : NMat) : Prop := WF n A ∧ ∀ r ∈ A, ∀ x ∈ r, x < 13

theorem getD_map0 (f : ℕ → ℕ) (hf : f 0 = 0) (l : List ℕ) (i : ℕ) : (l.map f).getD i 0 = f (l.getD i 0) := by
  have := List.getD_map (f := f) (l := l) (n := i) (d := 0)
  rwa [hf] at this

theorem ndot_cast (r v : List ℕ) :
    ((ndot r v : ℕ) : ZMod 13) = ∑ j : Fin r.length, ((r.getD j 0 : ℕ) : ZMod 13) * ((v.getD j 0 : ℕ) : ZMod 13) := by
  induction r generalizing v with
  | nil => cases v <;> simp [ndot]
  | cons a l ih =>
    cases v with
    | nil => simp [ndot]
    | cons b w => simp [ndot, Fin.sum_univ_succ, ih]

theorem nlin_spec (n : ℕ) (b : List ℕ) (B : NMat) (hB : ∀ r ∈ B, r.length = n) :
    (nlin n b B).length = n ∧ ∀ j < n, (((nlin n b B).getD j 0 : ℕ) : ZMod 13) =
      ∑ i : Fin B.length, ((b.getD i 0 : ℕ) : ZMod 13) * (((B.getD i []).getD j 0 : ℕ) : ZMod 13) := by
  induction B generalizing b with
  | nil =>
    cases b <;> simp [nlin, List.getD_eq_getElem?_getD]
  | cons r B ih =>
    have hr : r.length = n := hB r (by simp)
    have hB' : ∀ r ∈ B, r.length = n := fun r' h' => hB r' (by simp [h'])
    cases b with
    | nil => simp [nlin, List.getD_eq_getElem?_getD]
    | cons a b =>
      obtain ⟨ih1, ih2⟩ := ih b hB'
      refine ⟨by simp [nlin, hr, ih1], fun j hj => ?_⟩
      have hl : j < (nlin n (a :: b) (r :: B)).length := by simp [nlin, hr, ih1, hj]
      rw [List.getD_eq_getElem _ _ hl]
      simp only [nlin, List.getElem_zipWith, Nat.cast_add, Nat.cast_mul, Fin.sum_univ_succ, List.length_cons]
      have e1 := ih2 j hj
      rw [List.getD_eq_getElem _ _ (by rw [ih1]; exact hj)] at e1
      rw [e1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hr ▸ hj : j < r.length)]

theorem toM_apply (n : ℕ) (A : NMat) (i j : Fin n) : toM n A i j = (((A.getD i []).getD j 0 : ℕ) : ZMod 13) := rfl

theorem ndot_cast' (n : ℕ) (r v : List ℕ) (hr : r.length = n) :
    ((ndot r v : ℕ) : ZMod 13) = ∑ j : Fin n, ((r.getD j 0 : ℕ) : ZMod 13) * ((v.getD j 0 : ℕ) : ZMod 13) := by
  subst hr
  exact ndot_cast r v

theorem vecN_nmv (n : ℕ) (A : NMat) (hA : WF n A) (v : List ℕ) :
    vecN n (nmv A v) = Matrix.mulVec (toM n A) (vecN n v) := by
  funext i
  have hi : (i : ℕ) < A.length := by rw [hA.1]; exact i.2
  have hr : (A.getD i []).length = n := hA.2 _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  simp only [vecN, nmv]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, ZMod.natCast_mod,
    ← List.getD_eq_getElem _ [] hi, ndot_cast' n _ _ hr]
  simp only [Matrix.mulVec, dotProduct, toM_apply, vecN]

theorem vecN_nvm (n : ℕ) (B : NMat) (hB : WF n B) (v : List ℕ) :
    vecN n (nvm n v B) = Matrix.vecMul (vecN n v) (toM n B) := by
  obtain ⟨hl, hrows⟩ := hB
  subst hl
  funext j
  obtain ⟨h1, h2⟩ := nlin_spec B.length v B hrows
  simp only [vecN, nvm]
  rw [getD_map0 _ (by simp), ZMod.natCast_mod, h2 j j.2]
  simp only [Matrix.vecMul, dotProduct, toM_apply, vecN]

theorem toM_nmul (n : ℕ) (A B : NMat) (hA : A.length = n) (hB : WF n B) :
    toM n (nmul n A B) = toM n A * toM n B := by
  ext i j
  have hi : (i : ℕ) < A.length := by rw [hA]; exact i.2
  have e : (nmul n A B).getD i [] = nvm n (A.getD i []) B := by
    rw [List.getD_eq_getElem _ _ (by simpa [nmul] using hi), List.getD_eq_getElem _ _ hi]
    simp [nmul]
  have := congrFun (vecN_nvm n B hB (A.getD i [])) j
  simp only [vecN] at this
  rw [toM_apply, e, this, Matrix.mul_apply]
  simp only [Matrix.vecMul, dotProduct, toM_apply, vecN]

theorem cast_aux (d t : ℕ) : (((d + 13 - t % 13) % 13 : ℕ) : ZMod 13) = (d : ZMod 13) - (t : ZMod 13) := by
  rw [ZMod.natCast_mod, Nat.add_sub_assoc (Nat.mod_lt _ (by norm_num)).le, Nat.cast_add,
    Nat.cast_sub (Nat.mod_lt _ (by norm_num)).le, ZMod.natCast_mod, ZMod.natCast_self]
  ring

theorem mat_spec (n : ℕ) (q : KPair) :
    toM n (mat n q) = 1 - Matrix.vecMulVec (vecN n q.1) (vecN n q.2) := by
  ext i j
  rw [toM_apply]
  simp only [mat, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2, List.getElem?_range j.2,
    Option.map_some, Option.getD_some]
  rw [cast_aux]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, vecN, Fin.ext_iff,
    List.getD_eq_getElem?_getD, Nat.cast_mul]
  split_ifs <;> simp

theorem idN_spec (n : ℕ) : toM n (idN n) = 1 := by
  ext i j
  rw [toM_apply]
  simp only [idN, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2, List.getElem?_range j.2,
    Option.map_some, Option.getD_some, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> simp

theorem wf_mat (n : ℕ) (q : KPair) : Red n (mat n q) := by
  refine ⟨⟨by simp [mat], ?_⟩, ?_⟩
  · intro r hr
    simp only [mat, List.mem_map, List.mem_range] at hr
    obtain ⟨i, -, rfl⟩ := hr
    simp
  · intro r hr x hx
    simp only [mat, List.mem_map, List.mem_range] at hr
    obtain ⟨i, -, rfl⟩ := hr
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact Nat.mod_lt _ (by norm_num)

theorem wf_idN (n : ℕ) : Red n (idN n) := by
  refine ⟨⟨by simp [idN], ?_⟩, ?_⟩
  · intro r hr
    simp only [idN, List.mem_map, List.mem_range] at hr
    obtain ⟨i, -, rfl⟩ := hr
    simp
  · intro r hr x hx
    simp only [idN, List.mem_map, List.mem_range] at hr
    obtain ⟨i, -, rfl⟩ := hr
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    split_ifs <;> norm_num

theorem wf_nmul (n : ℕ) (A B : NMat) (hA : A.length = n) (hB : WF n B) : Red n (nmul n A B) := by
  refine ⟨⟨by simp [nmul, hA], ?_⟩, ?_⟩
  · intro r hr
    simp only [nmul, List.mem_map] at hr
    obtain ⟨a, -, rfl⟩ := hr
    simp [nvm, (nlin_spec n a B hB.2).1]
  · intro r hr x hx
    simp only [nmul, List.mem_map] at hr
    obtain ⟨a, -, rfl⟩ := hr
    simp only [nvm, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact Nat.mod_lt _ (by norm_num)

theorem toM_inj (n : ℕ) {A B : NMat} (hA : Red n A) (hB : Red n B) (h : toM n A = toM n B) : A = B := by
  apply List.ext_getElem (by rw [hA.1.1, hB.1.1])
  intro i hi hi'
  have hiA : i < n := hA.1.1 ▸ hi
  have hra := hA.1.2 _ (List.getElem_mem hi)
  have hrb := hB.1.2 _ (List.getElem_mem hi')
  apply List.ext_getElem (by rw [hra, hrb])
  intro j hj hj'
  have hjn : j < n := hra ▸ hj
  have e := congrFun (congrFun h ⟨i, hiA⟩) ⟨j, hjn⟩
  simp only [toM_apply] at e
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hi',
    List.getD_eq_getElem _ _ hj'] at e
  have h1 := hA.2 _ (List.getElem_mem hi) _ (List.getElem_mem hj)
  have h2 := hB.2 _ (List.getElem_mem hi') _ (List.getElem_mem hj')
  have := congrArg ZMod.val e
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

theorem fnz_lt : ∀ l : List ℕ, fnz l < 13
  | [] => by simp [fnz]
  | x :: l => by
    unfold fnz
    split_ifs
    · exact fnz_lt l
    · exact Nat.mod_lt _ (by norm_num)

theorem fnz_zero : ∀ l : List ℕ, fnz l = 0 → ∀ i, ((l.getD i 0 : ℕ) : ZMod 13) = 0
  | [], _, i => by simp
  | x :: l, h, i => by
    unfold fnz at h
    split_ifs at h with hx
    · cases i with
      | zero =>
        simp only [List.getD_cons_zero]
        rw [← ZMod.natCast_mod, hx, Nat.cast_zero]
      | succ i => simpa using fnz_zero l h i
    · exact absurd h hx

theorem ninv_mul (c : ℕ) (hc : c < 13) (h0 : c ≠ 0) : ((ninv c : ℕ) : ZMod 13) * (c : ZMod 13) = 1 := by
  have key : ∀ c < 13, c ≠ 0 → ninv c * c % 13 = 1 := by decide
  rw [← Nat.cast_mul, ← ZMod.natCast_mod, key c hc h0, Nat.cast_one]

theorem normP_spec (n : ℕ) (q : KPair) : toM n (mat n (normP q)) = toM n (mat n q) := by
  rw [mat_spec, mat_spec]
  congr 1
  ext i j
  simp only [normP, Matrix.vecMulVec_apply, vecN]
  rw [getD_map0 _ (by simp), getD_map0 _ (by simp), ZMod.natCast_mod, ZMod.natCast_mod]
  by_cases h : fnz q.1 = 0
  · push_cast
    simp only [fnz_zero _ h i, h, Nat.cast_zero, mul_zero, zero_mul]
  · push_cast
    have := ninv_mul _ (fnz_lt q.1) h
    linear_combination ((q.1.getD i 0 : ℕ) : ZMod 13) * ((q.2.getD j 0 : ℕ) : ZMod 13) * this

theorem conjP_spec (n : ℕ) (s : NMat) (hs : WF n s) (hss : toM n s * toM n s = 1) (q : KPair) :
    toM n s * toM n (mat n q) * toM n s = toM n (mat n (conjP n s q)) := by
  rw [conjP, normP_spec, mat_spec, mat_spec, vecN_nmv n s hs, vecN_nvm n s hs, mul_sub, sub_mul, mul_one, hss,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

@[expose] def Lm (n : ℕ) (V : List KPair) (i : ℕ) : Mat n := toM n (mat n (V.getD i kP0))

theorem tab_sound {n : ℕ} {S : List NMat} {V : List KPair} {tab : List (List ℕ)} (h : kTab n S V tab = true)
    (hS : ∀ s ∈ S, WF n s ∧ toM n s * toM n s = 1) {i s : ℕ} (hi : i < V.length) (hs : s < S.length) :
    (tab.getD i []).getD s 0 < V.length ∧
      toM n (S.getD s []) * Lm n V i * toM n (S.getD s []) = Lm n V ((tab.getD i []).getD s 0) := by
  simp only [kTab, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, not_le] at h
  have hsS : S.getD s [] ∈ S := by rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs
  obtain ⟨hw, hss⟩ := hS _ hsS
  have hx : ∀ i < V.length, ((tab.getD i []).getD s 0 < V.length ∧
      (tab.getD ((tab.getD i []).getD s 0) []).getD s 0 = i) ∧ ((tab.getD i []).getD s 0 < i ∨
      conjP n (S.getD s []) (V.getD i kP0) = V.getD ((tab.getD i []).getD s 0) kP0) :=
    fun i hi => (h.2 i hi).2 s hs
  have direct : ∀ i < V.length, i ≤ (tab.getD i []).getD s 0 →
      toM n (S.getD s []) * Lm n V i * toM n (S.getD s []) = Lm n V ((tab.getD i []).getD s 0) := by
    intro i hi hle
    rcases (hx i hi).2 with h4 | h4
    · omega
    · rw [Lm, Lm, conjP_spec n _ hw hss, h4]
  obtain ⟨⟨hj, hback⟩, -⟩ := hx i hi
  refine ⟨hj, ?_⟩
  by_cases hle : i ≤ (tab.getD i []).getD s 0
  · exact direct i hi hle
  · set j := (tab.getD i []).getD s 0
    have hji : j ≤ (tab.getD j []).getD s 0 := by rw [hback]; omega
    have e := direct j hj hji
    rw [hback] at e
    rw [← e, ← mul_assoc, ← mul_assoc, hss, one_mul, mul_assoc, hss, mul_one]

theorem par_sound {S : List NMat} {V : List KPair} {tab : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : kPar S V tab par = true) : ∀ i < V.length, i ≠ 0 → (par.getD i (0, 0)).1 < i ∧
      (par.getD i (0, 0)).2 < S.length ∧ (tab.getD (par.getD i (0, 0)).1 []).getD (par.getD i (0, 0)).2 0 = i := by
  simp only [kPar, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  intro i hi hi0
  rcases h i hi with h | h
  · exact absurd h hi0
  · exact ⟨h.1.1, h.1.2, h.2⟩

theorem wit_sound {n : ℕ} {S : List NMat} {V : List KPair} {tab : List (List ℕ)} {wd : List (List ℕ)} {x0 : ℕ}
    (h : kWit n S V tab wd x0 = true) : x0 < V.length ∧ ∀ i < V.length,
      a2N n (mat n (V.getD 0 kP0)) (mat n (V.getD i kP0)) = true →
        (∀ s ∈ wd.getD i [], s < S.length) ∧ walk tab (0, x0) (wd.getD i []) = (0, i) := by
  simp only [kWit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨h.1, fun i hi ha => ?_⟩
  rcases h.2 i hi with h' | h'
  · rw [ha] at h'
    exact absurd h' (by decide)
  · exact h'

theorem a2N_of (n : ℕ) (A B : NMat) (hA : Red n A) (hB : Red n B) (h1 : toM n A * toM n B ≠ 1)
    (h3 : toM n A * toM n B * (toM n A * toM n B) * (toM n A * toM n B) = 1) : a2N n A B = true := by
  simp only [a2N, isOneN, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  have hp := wf_nmul n A B hA.1.1 hB.1
  have ep := toM_nmul n A B hA.1.1 hB.1
  have hpp := wf_nmul n _ _ hp.1.1 hp.1
  refine ⟨fun e => h1 (by rw [← ep, e, idN_spec]), ?_⟩
  apply toM_inj n (wf_nmul n _ _ hpp.1.1 hp.1) (wf_idN n)
  rw [toM_nmul n _ _ hpp.1.1 hp.1, toM_nmul n _ _ hp.1.1 hp.1, ep, idN_spec]
  exact h3

theorem getD_prop {α : Type*} (P : α → Prop) (l : List α) (d : α) (i : ℕ) (hl : ∀ x ∈ l, P x) (hd : P d) :
    P (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hd
  | some x =>
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
    exact hl _ (List.getElem_mem hi)

theorem replay_sound (n : ℕ) (G : List NMat) (T : Set (Mat n))
    (hG : ∀ g ∈ G, Red n g ∧ toM n g ∈ Submonoid.closure T) (tr : List (ℕ × ℕ)) :
    ∀ e ∈ kReplay n G tr, Red n e ∧ toM n e ∈ Submonoid.closure T := by
  have hI : Red n (idN n) ∧ toM n (idN n) ∈ Submonoid.closure T := ⟨wf_idN n, by rw [idN_spec]; exact one_mem _⟩
  unfold kReplay
  refine owEm_foldl_inv (fun E : List NMat => ∀ e ∈ E, Red n e ∧ toM n e ∈ Submonoid.closure T) _ tr [idN n] ?_ ?_
  · intro e he
    rw [List.mem_singleton] at he
    rw [he]
    exact hI
  · intro E x _ hE e he
    rcases List.mem_append.mp he with he | he
    · exact hE e he
    · rw [List.mem_singleton] at he
      rw [he]
      have h1 := getD_prop (fun e => Red n e ∧ toM n e ∈ Submonoid.closure T) E (idN n) x.1 hE hI
      have h2 := getD_prop (fun e => Red n e ∧ toM n e ∈ Submonoid.closure T) G (idN n) x.2 hG hI
      refine ⟨wf_nmul n _ _ h1.1.1.1 h2.1.1, ?_⟩
      rw [toM_nmul n _ _ h1.1.1.1 h2.1.1]
      exact mul_mem h1.2 h2.2

theorem big_sound {n : ℕ} {V : List KPair} {x0 t0 : ℕ} {tr : List (ℕ × ℕ)} {ord : List ℕ}
    (h : kBig n V x0 t0 tr ord = true) : t0 < V.length ∧
      ¬ (Lm n V t0 * Lm n V 0 = Lm n V 0 * Lm n V t0 ∧ Lm n V t0 * Lm n V x0 = Lm n V x0 * Lm n V t0) ∧
      ∃ E : List (Mat n), E.length = 49 ∧ E.Nodup ∧
        ∀ e ∈ E, e ∈ Submonoid.closure ({Lm n V 0, Lm n V x0, Lm n V t0} : Set (Mat n)) := by
  simp only [kBig, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ht0, hnc⟩, hlen⟩, hinc⟩ := h
  rw [decide_eq_true_eq] at ht0 hlen
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hnc
  have red := fun i => wf_mat n (V.getD i kP0)
  refine ⟨ht0, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    rcases hnc with hc | hc
    · apply hc
      apply toM_inj n (wf_nmul n _ _ (red _).1.1 (red _).1) (wf_nmul n _ _ (red _).1.1 (red _).1)
      rw [toM_nmul n _ _ (red _).1.1 (red _).1, toM_nmul n _ _ (red _).1.1 (red _).1]
      exact h1
    · apply hc
      apply toM_inj n (wf_nmul n _ _ (red _).1.1 (red _).1) (wf_nmul n _ _ (red _).1.1 (red _).1)
      rw [toM_nmul n _ _ (red _).1.1 (red _).1, toM_nmul n _ _ (red _).1.1 (red _).1]
      exact h2
  · set T : Set (Mat n) := {Lm n V 0, Lm n V x0, Lm n V t0}
    set R := kReplay n [mat n (V.getD 0 kP0), mat n (V.getD x0 kP0), mat n (V.getD t0 kP0)] tr
    have hR : ∀ e ∈ R, Red n e ∧ toM n e ∈ Submonoid.closure T := by
      refine replay_sound n _ T ?_ tr
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨red _, Submonoid.subset_closure (by simp [T, Lm])⟩
      · exact ⟨red _, Submonoid.subset_closure (by simp [T, Lm])⟩
      · exact ⟨red _, Submonoid.subset_closure (by simp [T, Lm])⟩
    have hI : Red n (idN n) ∧ toM n (idN n) ∈ Submonoid.closure T := ⟨wf_idN n, by rw [idN_spec]; exact one_mem _⟩
    set Ml := ord.map fun k => R.getD k (idN n)
    have hMl : ∀ e ∈ Ml, Red n e ∧ toM n e ∈ Submonoid.closure T := by
      intro e he
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp he
      exact getD_prop _ R _ k hR hI
    have hk := CFSG.StandardType.TWLK.kIncr_pairwise _ hinc
    have hkm : Ml.map (kVKey 13) = ord.map fun k => kVKey 13 (R.getD k (idN n)) := by
      rw [List.map_map]
      rfl
    have hnd : (Ml.map (kVKey 13)).Nodup := by
      rw [hkm]
      exact hk.imp Nat.ne_of_lt
    refine ⟨Ml.map (toM n), by simp [Ml, hlen], ?_, ?_⟩
    · refine (List.Nodup.of_map _ hnd).map_on ?_
      intro a ha b hb hab
      exact toM_inj n (hMl a ha).1 (hMl b hb).1 hab
    · intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact (hMl a ha).2

theorem card_big {n : ℕ} (a b c : owEm_GL n) (E : List (Mat n)) (hl : E.length = 49) (hnd : E.Nodup)
    (hE : ∀ e ∈ E, e ∈ Submonoid.closure ({(a : Mat n), (b : Mat n), (c : Mat n)} : Set (Mat n))) :
    48 < Nat.card (Subgroup.closure ({a, b, c} : Set (owEm_GL n))) := by
  have hsub : ∀ e ∈ Submonoid.closure ({(a : Mat n), (b : Mat n), (c : Mat n)} : Set (Mat n)),
      ∃ u ∈ Subgroup.closure ({a, b, c} : Set (owEm_GL n)), (u : Mat n) = e := by
    intro e he
    induction he using Submonoid.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨a, Subgroup.subset_closure (by simp), rfl⟩
      · exact ⟨b, Subgroup.subset_closure (by simp), rfl⟩
      · exact ⟨c, Subgroup.subset_closure (by simp), rfl⟩
    | one => exact ⟨1, one_mem _, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u * v, mul_mem hu hv, Units.val_mul u v⟩
  have hs : (E.toFinset : Set (Mat n)) ⊆
      (Units.val : owEm_GL n → Mat n) '' (Subgroup.closure ({a, b, c} : Set (owEm_GL n)) : Set _) := by
    intro y hy
    rw [Finset.mem_coe, List.mem_toFinset] at hy
    obtain ⟨u, hu, hu'⟩ := hsub y (hE y hy)
    exact ⟨u, hu, hu'⟩
  calc 48 < E.length := by omega
    _ = E.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = (E.toFinset : Set (Mat n)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ ((Units.val : owEm_GL n → Mat n) '' (Subgroup.closure ({a, b, c} : Set (owEm_GL n)) : Set _)).ncard :=
        Set.ncard_le_ncard hs ((Set.toFinite _).image _)
    _ ≤ (Subgroup.closure ({a, b, c} : Set (owEm_GL n)) : Set (owEm_GL n)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card (Subgroup.closure ({a, b, c} : Set (owEm_GL n))) := (Nat.card_coe_set_eq _).symm

theorem walk_sound {n : ℕ} (H : Subgroup (owEm_GL n)) (gu : ℕ → owEm_GL n) (k N : ℕ) (Xm : ℕ → Mat n)
    (tab : List (List ℕ)) (hgu : ∀ s < k, gu s ∈ H ∧ (gu s)⁻¹ = gu s)
    (htab : ∀ i < N, ∀ s < k, (tab.getD i []).getD s 0 < N ∧
      (gu s : Mat n) * Xm i * (gu s : Mat n) = Xm ((tab.getD i []).getD s 0)) :
    ∀ (w : List ℕ) (u v : ℕ), u < N → v < N → (∀ s ∈ w, s < k) → ∃ m ∈ H,
      (m : Mat n) * Xm u * ((m⁻¹ : owEm_GL n) : Mat n) = Xm (walk tab (u, v) w).1 ∧
      (m : Mat n) * Xm v * ((m⁻¹ : owEm_GL n) : Mat n) = Xm (walk tab (u, v) w).2
  | [], u, v, _, _, _ => ⟨1, one_mem _, by simp [walk], by simp [walk]⟩
  | s :: w, u, v, hu, hv, hw => by
    have hs := hw s (by simp)
    obtain ⟨hu', eu⟩ := htab u hu s hs
    obtain ⟨hv', ev⟩ := htab v hv s hs
    obtain ⟨m, hm, e1, e2⟩ :=
      walk_sound H gu k N Xm tab hgu htab w _ _ hu' hv' (fun s' h' => hw s' (by simp [h']))
    have hw' : walk tab (u, v) (s :: w) =
        walk tab ((tab.getD u []).getD s 0, (tab.getD v []).getD s 0) w := rfl
    refine ⟨m * gu s, mul_mem hm (hgu s hs).1, ?_, ?_⟩
    · rw [hw', ← e1, ← eu, mul_inv_rev, (hgu s hs).2]
      simp only [Units.val_mul, mul_assoc]
    · rw [hw', ← e2, ← ev, mul_inv_rev, (hgu s hs).2]
      simp only [Units.val_mul, mul_assoc]

theorem par_conj {n : ℕ} (H : Subgroup (owEm_GL n)) (gu : ℕ → owEm_GL n) (k N : ℕ) (Xm : ℕ → Mat n)
    (tab : List (List ℕ)) (par : List (ℕ × ℕ)) (r0 : owEm_GL n) (h0 : (r0 : Mat n) = Xm 0)
    (hgu : ∀ s < k, gu s ∈ H ∧ (gu s)⁻¹ = gu s)
    (htab : ∀ i < N, ∀ s < k, (tab.getD i []).getD s 0 < N ∧
      (gu s : Mat n) * Xm i * (gu s : Mat n) = Xm ((tab.getD i []).getD s 0))
    (hpar : ∀ i < N, i ≠ 0 → (par.getD i (0, 0)).1 < i ∧ (par.getD i (0, 0)).2 < k ∧
      (tab.getD (par.getD i (0, 0)).1 []).getD (par.getD i (0, 0)).2 0 = i) :
    ∀ i < N, ∃ m ∈ H, ((m * r0 * m⁻¹ : owEm_GL n) : Mat n) = Xm i := by
  intro i
  refine Nat.strong_induction_on i ?_
  intro i ih hi
  by_cases hi0 : i = 0
  · subst hi0
    exact ⟨1, one_mem _, by simp [h0]⟩
  · obtain ⟨hp, hs, he⟩ := hpar i hi hi0
    obtain ⟨m, hm, e⟩ := ih _ hp (by omega)
    obtain ⟨-, et⟩ := htab (par.getD i (0, 0)).1 (by omega) (par.getD i (0, 0)).2 hs
    refine ⟨gu (par.getD i (0, 0)).2 * m, mul_mem (hgu _ hs).1 hm, ?_⟩
    have ev : ((gu (par.getD i (0, 0)).2 * m * r0 * (gu (par.getD i (0, 0)).2 * m)⁻¹ : owEm_GL n) : Mat n) =
        (gu (par.getD i (0, 0)).2 : Mat n) * ((m * r0 * m⁻¹ : owEm_GL n) : Mat n) *
          (gu (par.getD i (0, 0)).2 : Mat n) := by
      rw [mul_inv_rev, (hgu _ hs).2]
      simp only [Units.val_mul, mul_assoc]
    rw [ev, e, et, he]

theorem kRow_wit {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ}
    (S : List NMat) (V : List KPair) (tab : List (List ℕ)) (par : List (ℕ × ℕ)) (wd : List (List ℕ))
    (x0 t0 : ℕ) (tr : List (ℕ × ℕ)) (ord : List ℕ) (h : kCore n S V tab par wd x0 t0 tr ord = true)
    (hS0 : 0 < S.length) (gens : Set (Mat n)) (hSg : ∀ s < S.length, toM n (S.getD s []) ∈ gens)
    (hgX : ∀ g ∈ gens, ∃ i < V.length, Lm n V i = g)
    (hrefl : ∀ g : owEm_GL n, (g : Mat n) = toM n (S.getD 0 []) → (g : Mat n) * g = 1 → IsReflMat g)
    (f : ↥(glClosure gens) ≃* ↥A)
    (hf : ∀ g : ↥(glClosure gens), IsReflMat (g : owEm_GL n) ↔ IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) : ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  simp only [kCore, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hinv⟩, hV0⟩, h0⟩, htab⟩, hpar⟩, hwit⟩, hbig⟩ := h
  rw [decide_eq_true_eq] at hV0 h0
  have hSf : ∀ s ∈ S, WF n s ∧ toM n s * toM n s = 1 := by
    intro s hs
    have w := List.all_eq_true.mp hwf s hs
    simp only [wfM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at w
    have i := List.all_eq_true.mp hinv s hs
    simp only [isOneN, decide_eq_true_eq] at i
    refine ⟨⟨w.1, w.2⟩, ?_⟩
    rw [← toM_nmul n s s w.1 ⟨w.1, w.2⟩, i, idN_spec]
  have hSi : ∀ s < S.length, toM n (S.getD s []) * toM n (S.getD s []) = 1 := fun s hs =>
    (hSf _ (by rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs)).2
  let gu : ℕ → owEm_GL n := fun s => if hs : s < S.length then owEm_unit _ (hSi s hs) else 1
  let H : Subgroup (owEm_GL n) := Subgroup.closure {g | ∃ s < S.length, g = gu s}
  have hguv : ∀ s < S.length, (gu s : Mat n) = toM n (S.getD s []) := fun s hs => by simp [gu, hs, owEm_unit]
  have hgu : ∀ s < S.length, gu s ∈ H ∧ (gu s)⁻¹ = gu s := fun s hs =>
    ⟨Subgroup.subset_closure ⟨s, hs, rfl⟩, by simp only [gu, hs, dif_pos, owEm_unit_inv]⟩
  have htab' : ∀ i < V.length, ∀ s < S.length, (tab.getD i []).getD s 0 < V.length ∧
      (gu s : Mat n) * Lm n V i * (gu s : Mat n) = Lm n V ((tab.getD i []).getD s 0) := by
    intro i hi s hs
    rw [hguv s hs]
    exact tab_sound htab hSf hi hs
  let r0 := gu 0
  have hr0 : (r0 : Mat n) = Lm n V 0 := by
    change (gu 0 : Mat n) = _
    rw [hguv 0 hS0, Lm, h0]
  have hr0H : r0 ∈ H := (hgu 0 hS0).1
  have hconj := par_conj H gu S.length V.length (Lm n V) tab par r0 hr0 hgu htab' (par_sound hpar)
  have hM : glClosure gens = H := by
    apply le_antisymm
    · unfold glClosure
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨i, hi, hig⟩ := hgX _ hg
      obtain ⟨m, hm, e⟩ := hconj i hi
      have : g = m * r0 * m⁻¹ := Units.ext (by rw [e, hig])
      rw [this]
      exact mul_mem (mul_mem hm hr0H) (inv_mem hm)
    · unfold glClosure
      rw [Subgroup.closure_le]
      rintro g ⟨s, hs, rfl⟩
      apply Subgroup.subset_closure
      change (gu s : Mat n) ∈ gens
      rw [hguv s hs]
      exact hSg s hs
  let X : Set (owEm_GL n) := {x | ∃ i < V.length, (x : Mat n) = Lm n V i}
  have hgen : ∀ s < S.length, ∀ x ∈ X, gu s * x * gu s ∈ X := by
    rintro s hs x ⟨i, hi, hx⟩
    obtain ⟨hj, e⟩ := htab' i hi s hs
    exact ⟨_, hj, by rw [← e, ← hx]; simp only [Units.val_mul]⟩
  have hcl : ∀ m ∈ H, ∀ x ∈ X, m * x * m⁻¹ ∈ X ∧ m⁻¹ * x * m ∈ X := by
    intro m hm
    induction hm using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨s, hs, rfl⟩ := hg
      intro x hx
      rw [(hgu s hs).2]
      exact ⟨hgen s hs x hx, hgen s hs x hx⟩
    | one => intro x hx; simpa using hx
    | mul a b _ _ iha ihb =>
      intro x hx
      refine ⟨?_, ?_⟩
      · have := (iha _ (ihb x hx).1).1
        simpa [mul_assoc] using this
      · have := (ihb _ (iha x hx).2).2
        simpa [mul_assoc] using this
    | inv a _ iha =>
      intro x hx
      have := iha x hx
      rw [inv_inv]
      exact ⟨this.2, this.1⟩
  obtain ⟨hx0, hwd⟩ := wit_sound hwit
  obtain ⟨ht0, hnc, E, hEl, hEnd, hEc⟩ := big_sound hbig
  refine owEm_transfer (glClosure gens) f hf hone r0 (by rw [hM]; exact hr0H) (hrefl r0 (hguv 0 hS0)
    (by change (gu 0 : Mat n) * (gu 0 : Mat n) = 1; rw [hguv 0 hS0]; exact hSi 0 hS0))
    X ⟨0, hV0, hr0⟩ ?_ ?_ ?_
  · rintro x ⟨i, hi, hx⟩
    obtain ⟨m, hm, e⟩ := hconj i hi
    exact ⟨m, by rw [hM]; exact hm, Units.ext (by rw [hx, e])⟩
  · intro m hm x hx
    exact (hcl m (by rw [← hM]; exact hm) x hx).1
  · rintro x ⟨i, hi, hx⟩ hord
    have h1 : r0 * x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    have h3 : (r0 * x) ^ 3 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    have h1' : (r0 : Mat n) * x ≠ 1 := fun h' => h1 (Units.ext (by simpa using h'))
    have h3' : (r0 : Mat n) * x * ((r0 : Mat n) * x) * ((r0 : Mat n) * x) = 1 := by
      have := congrArg (fun u : owEm_GL n => (u : Mat n)) h3
      simpa [pow_succ, mul_assoc] using this
    rw [hr0, hx] at h1' h3'
    have ha := a2N_of n _ _ (wf_mat n _) (wf_mat n _) h1' h3'
    obtain ⟨hw, hwalk⟩ := hwd i hi ha
    obtain ⟨m, hm, em0, emx⟩ := walk_sound H gu S.length V.length (Lm n V) tab hgu htab' (wd.getD i []) 0 x0
      hV0 hx0 hw
    rw [hwalk] at em0 emx
    obtain ⟨m1, hm1, e1⟩ := hconj x0 hx0
    obtain ⟨m2, hm2, e2⟩ := hconj t0 ht0
    generalize hx0d : m1 * r0 * m1⁻¹ = x0' at e1
    generalize ht0d : m2 * r0 * m2⁻¹ = t0' at e2
    have hfix : m * r0 * m⁻¹ = r0 := Units.ext (by simp only [Units.val_mul]; rw [hr0, em0])
    have hxe : m * x0' * m⁻¹ = x := Units.ext (by simp only [Units.val_mul]; rw [e1, emx, hx])
    have ht0X : t0' ∈ X := ⟨t0, ht0, e2⟩
    refine ⟨m * t0' * m⁻¹, (hcl m hm t0' ht0X).1, ?_, ?_⟩
    · rintro ⟨c1, c2⟩
      have c1' : Commute (m * t0' * m⁻¹) (m * r0 * m⁻¹) := by rw [hfix]; exact c1
      have c2' : Commute (m * t0' * m⁻¹) (m * x0' * m⁻¹) := by rw [hxe]; exact c2
      have d1 := congrArg Units.val ((Commute.conj_iff m).mp c1').eq
      have d2 := congrArg Units.val ((Commute.conj_iff m).mp c2').eq
      simp only [Units.val_mul] at d1 d2
      rw [e2, hr0] at d1
      rw [e2, e1] at d2
      exact hnc ⟨d1, d2⟩
    · intro hd
      have himg : ({r0, x, m * t0' * m⁻¹} : Set (owEm_GL n)) =
          (fun y => m * y * m⁻¹) '' ({r0, x0', t0'} : Set (owEm_GL n)) := by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hfix, hxe]
      rw [himg, owEm_card_closure_conj] at hd
      have hbig' := card_big r0 x0' t0' E hEl hEnd (by
        intro e he
        have := hEc e he
        rwa [hr0, e1, e2])
      exact absurd (Nat.le_of_dvd (by norm_num) hd) (not_le.mpr hbig')

theorem toM_toN {n : ℕ} (A : M13 n) : toM n (toN A) = A.val := by
  ext i j
  simp [toM_apply, toN, List.getD_eq_getElem?_getD, ZMod.natCast_zmod_val]

theorem kCovN_sound {n : ℕ} {S G : List NMat} {V : List KPair} {cov : List ℕ} (h : kCovN n S G V cov = true) :
    S = G ∧ ∀ j < S.length, ∃ i < V.length, Lm n V i = toM n (S.getD j []) := by
  simp only [kCovN, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hSG, -⟩, hj⟩ := h
  exact ⟨hSG, fun j hjl => ⟨_, (hj j hjl).1, by rw [Lm, (hj j hjl).2]⟩⟩

theorem kCovK_sound {n : ℕ} {S : List NMat} {roots V : List KPair} {cov sidx : List ℕ}
    (h : kCovK n S roots V cov sidx = true) :
    (∀ j < roots.length, ∃ i < V.length, Lm n V i = toM n (mat n (rootP (roots.getD j kP0)))) ∧
      ∀ j < S.length, ∃ c < roots.length, toM n (S.getD j []) = toM n (mat n (rootP (roots.getD c kP0))) := by
  simp only [kCovK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨-, hr⟩, -⟩, hs⟩ := h
  refine ⟨fun j hj => ⟨_, (hr j hj).1, by rw [Lm, (hr j hj).2]⟩, fun j hj => ⟨_, (hs j hj).1, ?_⟩⟩
  rw [(hs j hj).2, ← (hr _ (hs j hj).1).2]

theorem ninv_cast (x : ℕ) : ((ninv x : ℕ) : ZMod 13) = ((x : ℕ) : ZMod 13)⁻¹ := by
  have key : ∀ y : Fin 13, ((ninv y : ℕ) : ZMod 13) = ((y : ℕ) : ZMod 13)⁻¹ := by decide +kernel
  have h1 : ninv x = ninv (x % 13) := by simp [ninv, Nat.mod_mod]
  rw [h1, key ⟨x % 13, Nat.mod_lt _ (by norm_num)⟩, ZMod.natCast_mod]

theorem vecN_pairN (w : (Fin 6 → ZMod 13) × (Fin 6 → ZMod 13)) :
    vecN 6 (pairN w).1 = w.1 ∧ vecN 6 (pairN w).2 = w.2 := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩ <;> fin_cases i <;>
    simp [vecN, pairN, List.getD_eq_getElem?_getD, ZMod.natCast_zmod_val]

theorem rootP_spec (w : (Fin 6 → ZMod 13) × (Fin 6 → ZMod 13)) :
    toM 6 (mat 6 (rootP (pairN w))) = herRefl w.1 w.2 := by
  rw [rootP, normP_spec, mat_spec]
  obtain ⟨h1, h2⟩ := vecN_pairN w
  have hd : ((ndot (pairN w).1 (pairN w).2 : ℕ) : ZMod 13) = ∑ i, w.1 i * w.2 i := by
    rw [ndot_cast' 6 _ _ (by simp [pairN])]
    exact Finset.sum_congr rfl fun i _ => by rw [← congrFun h1 i, ← congrFun h2 i]; rfl
  ext i j
  simp only [herRefl, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  congr 1
  simp only [vecN]
  rw [getD_map0 _ (by simp), ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ninv_cast, hd]
  have e1 : (((pairN w).1.getD i 0 : ℕ) : ZMod 13) = w.1 i := congrFun h1 i
  have e2 : (((pairN w).2.getD j 0 : ℕ) : ZMod 13) = w.2 j := congrFun h2 j
  rw [e1, e2, div_eq_mul_inv]
  push_cast
  ring

theorem kCovK_gens {S : List NMat} {V : List KPair} {cov sidx : List ℕ}
    (L : List ((Fin 6 → ZMod 13) × (Fin 6 → ZMod 13))) (h : kCovK 6 S (L.map pairN) V cov sidx = true) :
    (∀ w ∈ L, ∃ i < V.length, Lm 6 V i = herRefl w.1 w.2) ∧
      ∀ j < S.length, ∃ w ∈ L, toM 6 (S.getD j []) = herRefl w.1 w.2 := by
  obtain ⟨hr, hs⟩ := kCovK_sound h
  have hget : ∀ c (hc : c < L.length), (L.map pairN).getD c kP0 = pairN (L[c]'hc) := fun c hc => by
    rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map]
  refine ⟨fun w hw => ?_, fun j hj => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hw
    obtain ⟨i, hi, e⟩ := hr c (by simpa using hc)
    exact ⟨i, hi, by rw [e, hget c hc, rootP_spec]⟩
  · obtain ⟨c, hc, e⟩ := hs j hj
    have hc' : c < L.length := by simpa using hc
    exact ⟨L[c], List.getElem_mem hc', by rw [e, hget c hc', rootP_spec]⟩

end CFSG.StandardType.ZS.WEMK

end
