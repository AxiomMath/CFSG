
module

public import CFSG.Certificates.Kernel.SporSch.HNArr
public import CFSG.Sporadic.HNSchreier.Seeds
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs

public section

namespace CFSG.KS.HNArr

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.Sporadic.He.Native CFSG.Sporadic.He Matrix

theorem matJ_mul (g h : JH) : matJ (g * h) = matJ g * matJ h := rfl

theorem matJ_one : matJ 1 = 1 := rfl

theorem progRegsM_mat : ∀ (prog : List (ℕ × ℕ × ℕ)) (regs : Array (Array (Array ℕ))) (G : ℕ → JH),
    (∀ t ∈ prog, t.1 < 11 ∧ t.2.1 < 11 ∧ t.2.2 < 11) → regs.size = 11 →
    (∀ k < 11, toMat 5 133 regs[k]! = matJ (G k)) →
      ∀ k < 11, toMat 5 133 (progRegsM regs prog)[k]! = matJ (runProg G prog k)
  | [], _, _, _, _, hg => hg
  | (a, b, c) :: rest, regs, G, hp, hs, hg => by
    obtain ⟨ha, hb, hc⟩ := hp (a, b, c) List.mem_cons_self
    rw [progRegsM, runProg]
    refine progRegsM_mat rest _ _ (fun t ht => hp t (List.mem_cons_of_mem _ ht)) (by simp [hs])
      fun k hk => ?_
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ k (by simp [hs]; exact hk),
      Array.getElem_setIfInBounds (by simp [hs]; exact hk)]
    by_cases e : c = k
    · subst e
      rw [ite_eq_left rfl, Function.update_self, toMat_mulM, hg a ha, hg b hb, matJ_mul]
    · rw [ite_eq_right e, Function.update_of_ne (Ne.symm e), ← getElem!_pos regs k (by omega),
        hg k hk]

theorem initRegsM_mat {k : ℕ} (hk : k < 11) :
    toMat 5 133 (initRegsM rowsA rowsB)[k]! = matJ (initJ k) := by
  rw [initRegsM, regs11_get _ _ _ hk, initJ]
  split_ifs
  · rw [toMat_rowsA, mat_aJ]
  · rw [toMat_rowsB, mat_bJ]
  · rw [toMat_idM, matJ_one]

theorem initRegsM_size : (initRegsM rowsA rowsB).size = 11 := by simp [initRegsM]

theorem runProg_mat {prog : List (ℕ × ℕ × ℕ)}
    (hp : ∀ t ∈ prog, t.1 < 11 ∧ t.2.1 < 11 ∧ t.2.2 < 11) {k : ℕ} (hk : k < 11) :
    matJ (runProg initJ prog k) = toMat 5 133 (progRegsM (initRegsM rowsA rowsB) prog)[k]! :=
  (progRegsM_mat prog _ _ hp initRegsM_size (fun _ hk' => initRegsM_mat hk') k hk).symm

theorem toVec_rootVec : toVec 5 133 rootVec = fixedVector := by
  funext j
  rw [toVec_apply, rootVec, getElem!_ofFn _ j.isLt]
  rfl

theorem PK_seedWordIdx :
    ∀ (w : List ℕ), (∀ l ∈ w, l = 1 ∨ l = 2) → ∀ {x : ℕ}, x < nPts → ∀ (v : Array ℕ),
      PK x = toVec 5 133 v →
      seedWordIdx (arrJ aJ) (arrJ bJ) w x < nPts ∧
        PK (seedWordIdx (arrJ aJ) (arrJ bJ) w x) = toVec 5 133 (seedWordVec rowsA rowsB w v)
  | [], _, _, hx, _, hv => ⟨hx, hv⟩
  | l :: w, hw, x, hx, v, hv => by
    obtain ⟨hlt, he⟩ := PK_seedWordIdx w (fun z hz => hw z (List.mem_cons_of_mem l hz)) hx v hv
    have e1 : seedWordIdx (arrJ aJ) (arrJ bJ) (l :: w) x =
        (if l = 1 then arrJ aJ else arrJ bJ)[seedWordIdx (arrJ aJ) (arrJ bJ) w x]! := rfl
    have e2 : seedWordVec rowsA rowsB (l :: w) v =
        mulVec 5 133 (seedSel rowsA rowsB l) (seedWordVec rowsA rowsB w v) := by
      simp only [seedWordVec, List.foldr_cons]
    rw [e1, e2, toVec_mulVec]
    rcases hw l List.mem_cons_self with rfl | rfl
    · rw [ite_eq_left rfl, arrJ_get _ hlt, seedSel, ite_eq_left rfl, toMat_rowsA, ← mat_aJ, ← he,
        ← PK_gi _ hlt]
      exact ⟨gi_lt _ hlt, rfl⟩
    · rw [ite_eq_right (by decide), arrJ_get _ hlt, seedSel, ite_eq_right (by decide),
        ite_eq_left rfl, toMat_rowsB, ← mat_bJ, ← he, ← PK_gi _ hlt]
      exact ⟨gi_lt _ hlt, rfl⟩

theorem mword_mat {S Si : Array (Array (Array ℕ))} {gs : ℕ → JH} {m : ℕ}
    (h : ∀ j < m, toMat 5 133 S[j]! = matJ (gs j) ∧ toMat 5 133 Si[j]! = matJ (gs j)⁻¹) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) → toMat 5 133 (mword S Si w) = matJ (wJ gs w)
  | [], _ => by rw [mword, toMat_idM]; rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    rw [mword, toMat_mulM, mword_mat h w fun z hz => hw z (List.mem_cons_of_mem l hz), wJ,
      matJ_mul]
    congr 1
    unfold mletter lJ
    split_ifs with hp
    · exact (h _ (by omega)).1
    · exact (h _ (by omega)).2

theorem mat_inv_of_mul {g : JH} {X : Matrix (Fin 133) (Fin 133) (ZMod 5)} (h : matJ g * X = 1) :
    X = matJ g⁻¹ := by
  have e : matJ g⁻¹ * matJ g = 1 := by rw [← matJ_mul, inv_mul_cancel, matJ_one]
  calc X = matJ g⁻¹ * matJ g * X := by rw [e, Matrix.one_mul]
    _ = matJ g⁻¹ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

@[expose] noncomputable def seedJ : List ℕ → JH
  | [] => 1
  | l :: w => (if l = 1 then aJ else bJ) * seedJ w

theorem seedWordIdx_gi :
    ∀ (w : List ℕ) {x : ℕ}, x < nPts → seedWordIdx (arrJ aJ) (arrJ bJ) w x = gi (seedJ w) x
  | [], _, hx => (gi_one hx).symm
  | l :: w, x, hx => by
    have e1 : seedWordIdx (arrJ aJ) (arrJ bJ) (l :: w) x =
        (if l = 1 then arrJ aJ else arrJ bJ)[seedWordIdx (arrJ aJ) (arrJ bJ) w x]! := rfl
    rw [e1, seedWordIdx_gi w hx, seedJ, gi_mul _ _ hx]
    split_ifs <;> exact arrJ_get _ (gi_lt _ hx)

theorem seedJ_mat :
    ∀ w : List ℕ, (∀ l ∈ w, l = 1 ∨ l = 2) → matJ (seedJ w) = toMat 5 133 (wordM (seedSel rowsA rowsB) w) := by
  intro w hw
  rw [toMat_wordM_seed w hw]
  induction w with
  | nil => rw [seedJ, matJ_one, List.map_nil, List.prod_nil]
  | cons l w ih =>
    rw [seedJ, matJ_mul, ih fun z hz => hw z (List.mem_cons_of_mem l hz), List.map_cons,
      List.prod_cons]
    congr 1
    rcases hw l List.mem_cons_self with rfl | rfl
    · rw [ite_eq_left rfl, mat_aJ]
      rfl
    · rw [ite_eq_right (by decide), mat_bJ]
      rfl

@[expose] def xStep (hS : Array (Array ℕ)) (acc : Array ℕ) (r : ℕ × ℕ) : Array ℕ :=
  acc.push (hS[r.2 - 1]!)[acc[r.1]!]!

theorem xStep_fold (hS : Array (Array ℕ)) : ∀ (l : List (ℕ × ℕ)) (acc : Array ℕ),
    (l.foldl (xStep hS) acc).size = acc.size + l.length ∧
      (∀ j < acc.size, (l.foldl (xStep hS) acc)[j]! = acc[j]!) ∧
      ∀ t < l.length, l[t]!.1 < acc.size + t → (l.foldl (xStep hS) acc)[acc.size + t]! =
        (hS[l[t]!.2 - 1]!)[(l.foldl (xStep hS) acc)[l[t]!.1]!]!
  | [], acc => ⟨by simp, fun _ _ => rfl, fun t ht => by simp at ht⟩
  | r :: l, acc => by
    obtain ⟨h1, h2, h3⟩ := xStep_fold hS l (xStep hS acc r)
    have hs : (xStep hS acc r).size = acc.size + 1 := by simp [xStep]
    have hpre : ∀ j < acc.size, (xStep hS acc r)[j]! = acc[j]! := fun j hj => by
      rw [xStep, getElem!_pos _ j (by simp; omega), Array.getElem_push_lt hj,
        ← getElem!_pos acc j hj]
    rw [List.foldl_cons]
    refine ⟨by rw [h1, hs, List.length_cons]; omega, fun j hj => by
      rw [h2 j (by omega), hpre j hj], fun t ht hlt => ?_⟩
    rcases t with _ | t
    · have e0 : (r :: l)[0]! = r := rfl
      rw [e0] at hlt ⊢
      rw [Nat.add_zero] at hlt ⊢
      rw [h2 acc.size (by omega), h2 r.1 (by omega), hpre r.1 hlt, xStep,
        getElem!_pos _ acc.size (by simp), Array.getElem_push_eq]
    · have e0 : (r :: l)[t + 1]! = l[t]! := rfl
      rw [e0] at hlt ⊢
      have := h3 t (by simp at ht; omega) (by omega)
      rw [hs, show acc.size + 1 + t = acc.size + (t + 1) by omega] at this
      exact this

theorem drop_one_get {recs : List (ℕ × ℕ)} (t : ℕ) : (recs.drop 1)[t]! = recs[t + 1]! := by
  rcases recs with _ | ⟨r, l⟩
  · rfl
  · rfl

theorem xIndex_spec (hS : Array (Array ℕ)) (root : ℕ) {recs : List (ℕ × ℕ)}
    (hlen : 1 ≤ recs.length) (hp : ∀ i, 1 ≤ i → i < recs.length → recs[i]!.1 < i) :
    (xIndex hS root recs).size = recs.length ∧ (xIndex hS root recs)[0]! = root ∧
      ∀ i, 1 ≤ i → i < recs.length → (xIndex hS root recs)[i]! =
        (hS[recs[i]!.2 - 1]!)[(xIndex hS root recs)[recs[i]!.1]!]! := by
  have e : xIndex hS root recs = (recs.drop 1).foldl (xStep hS) #[root] := rfl
  obtain ⟨h1, h2, h3⟩ := xStep_fold hS (recs.drop 1) #[root]
  rw [e]
  refine ⟨by rw [h1, List.length_drop]; simp; omega, h2 0 (by simp), fun i hi1 hi => ?_⟩
  have := h3 (i - 1) (by rw [List.length_drop]; omega) (by
    rw [drop_one_get, show i - 1 + 1 = i by omega]
    have := hp i hi1 hi
    have e1 : (#[root] : Array ℕ).size = 1 := rfl
    omega)
  rw [drop_one_get, show i - 1 + 1 = i by omega] at this
  simpa [show 1 + (i - 1) = i by omega] using this

end CFSG.KS.HNArr

end
