
module

public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public import CFSG.Certificates.Kernel.Spor.PWord
public import CFSG.Sporadic.Schreier.ONPermArr

public section

namespace CFSG.KS.HNArr

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.Sporadic.Th.Native CFSG.KS.PW CFSG.KS.TW Matrix

@[expose] noncomputable def gi (g : JH) (x : ℕ) : ℕ :=
  if h : x < nPts then (g • (⟨x, h⟩ : X)).val else x

@[expose] noncomputable def arrJ (g : JH) : Array ℕ := Array.ofFn (n := nPts) fun i => gi g i.val

theorem gi_of_lt (g : JH) {x : ℕ} (hx : x < nPts) : gi g x = (g • (⟨x, hx⟩ : X)).val := by
  rw [gi, dite_eq_left hx]

theorem gi_lt (g : JH) {x : ℕ} (hx : x < nPts) : gi g x < nPts := by
  rw [gi_of_lt g hx]
  exact (g • (⟨x, hx⟩ : X)).isLt

theorem gi_mul (g h : JH) {x : ℕ} (hx : x < nPts) : gi (g * h) x = gi g (gi h x) := by
  rw [gi_of_lt _ hx, gi_of_lt _ hx, gi_of_lt _ (h • (⟨x, hx⟩ : X)).isLt, mul_smul]

theorem gi_one {x : ℕ} (hx : x < nPts) : gi 1 x = x := by
  rw [gi_of_lt _ hx, one_smul]

theorem gi_inv (g : JH) {x : ℕ} (hx : x < nPts) : gi g⁻¹ (gi g x) = x := by
  rw [← gi_mul _ _ hx, inv_mul_cancel, gi_one hx]

theorem gi_inv' (g : JH) {x : ℕ} (hx : x < nPts) : gi g (gi g⁻¹ x) = x := by
  rw [← gi_mul _ _ hx, mul_inv_cancel, gi_one hx]

theorem arrJ_size (g : JH) : (arrJ g).size = nPts := by simp [arrJ]

theorem arrJ_get (g : JH) {x : ℕ} (hx : x < nPts) : (arrJ g)[x]! = gi g x :=
  ofFn_get' (f := gi g) hx

theorem arrJ_ext {a : Array ℕ} {g : JH} (hs : a.size = nPts) (h : ∀ x < nPts, a[x]! = gi g x) :
    a = arrJ g :=
  arr_ext hs h

theorem PK_gi (g : JH) {x : ℕ} (hx : x < nPts) :
    PK (gi g x) = matJ g *ᵥ PK x := by
  rw [gi_of_lt g hx]
  exact PK_smul g ⟨x, hx⟩

theorem gi_eq_of_PK {x y : ℕ} (hx : x < nPts) (hy : y < nPts)
    (h : PK x = PK y) : x = y :=
  PK_injective x hx y hy h

theorem pcomp_arrJ (g h : JH) : pcomp nPts (arrJ g) (arrJ h) = arrJ (g * h) := by
  refine arrJ_ext (by simp [pcomp]) fun x hx => ?_
  rw [pcomp_get' hx, arrJ_get h hx, arrJ_get g (gi_lt h hx), gi_mul g h hx]

theorem pid_arrJ : pid nPts = arrJ 1 :=
  arrJ_ext (by simp [pid]) fun x hx => by rw [pid_get' hx, gi_one hx]

theorem pinvCand_size (n : ℕ) (t : Array ℕ) : (pinvCand n t).size = n := by
  have heq : pinvCand n t =
      (List.range' 0 n).foldl (fun p i => p.set! t[i]! i) (Array.replicate n 0) := by
    unfold pinvCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [heq]
  have : ∀ (l : List ℕ) (p : Array ℕ), (l.foldl (fun p i => p.set! t[i]! i) p).size = p.size := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons a l ih => intro p; rw [List.foldl_cons, ih]; simp
  rw [this]
  simp

theorem pinvCand_arrJ (g : JH) : pinvCand nPts (arrJ g) = arrJ g⁻¹ := by
  refine arrJ_ext (pinvCand_size _ _) fun x hx => ?_
  exact CFSG.KS.CB.pinvCand_get (T := gi g) (U := gi g⁻¹) (fun y hy => gi_lt g hy)
    (fun y hy => gi_inv g hy) hx

theorem peq_refl (n : ℕ) (a : Array ℕ) : peq n a a = true :=
  CFSG.ONSchreier.allBelowN_iff.2 fun _ _ => beq_self_eq_true _

theorem pisInv_arrJ (g : JH) : pisInv nPts (arrJ g) (arrJ g⁻¹) = true := by
  refine CFSG.ONSchreier.allBelowN_iff.2 fun x hx => ?_
  rw [arrJ_get g hx, arrJ_get _ (gi_lt g hx), gi_inv g hx]
  simp [gi_lt g hx]

theorem pinvs_get {n : ℕ} {S : Array (Array ℕ)} {j : ℕ} (hj : j < S.size) :
    (pinvs n S)[j]! = pinvCand n S[j]! := by
  rw [pinvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem pinvs_size {n : ℕ} {S : Array (Array ℕ)} : (pinvs n S).size = S.size := by
  simp [pinvs]

@[expose] noncomputable def lJ (gs : ℕ → JH) (l : ℤ) : JH :=
  if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹

@[expose] noncomputable def wJ (gs : ℕ → JH) : List ℤ → JH
  | [] => 1
  | l :: w => lJ gs l * wJ gs w

theorem wJ_congr {gs hs : ℕ → JH} {m : ℕ} (h : ∀ j < m, gs j = hs j) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) → wJ gs w = wJ hs w
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    rw [wJ, wJ, wJ_congr h w fun z hz => hw z (List.mem_cons_of_mem l hz)]
    congr 1
    unfold lJ
    split_ifs with hp
    · rw [h _ (by omega)]
    · rw [h _ (by omega)]

@[expose] def ArrsOK (m : ℕ) (S Si : Array (Array ℕ)) (gs : ℕ → JH) : Prop :=
  ∀ j < m, S[j]! = arrJ (gs j) ∧ Si[j]! = arrJ (gs j)⁻¹

theorem pletter_arrJ {m : ℕ} {S Si : Array (Array ℕ)} {gs : ℕ → JH} (h : ArrsOK m S Si gs)
    {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ m) : pletter S Si l = arrJ (lJ gs l) := by
  unfold pletter lJ
  split_ifs with hp
  · exact (h _ (by omega)).1
  · exact (h _ (by omega)).2

theorem pword_arrJ {m : ℕ} {S Si : Array (Array ℕ)} {gs : ℕ → JH} (h : ArrsOK m S Si gs) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) → pword nPts S Si w = arrJ (wJ gs w)
  | [], _ => pid_arrJ
  | l :: w, hw => by
    rw [pword, wJ, pword_arrJ h w fun z hz => hw z (List.mem_cons_of_mem l hz),
      pletter_arrJ h (hw l List.mem_cons_self), pcomp_arrJ]

theorem foldr_GZ {m : ℕ} {gs : ℕ → JH} :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) → ∀ x < nPts,
      w.foldr (GZ (fun j => gi (gs j)) (fun j => gi (gs j)⁻¹)) x = gi (wJ gs w) x
  | [], _, x, hx => (gi_one hx).symm
  | l :: w, hw, x, hx => by
    have hl := hw l List.mem_cons_self
    rw [List.foldr_cons, foldr_GZ w (fun z hz => hw z (List.mem_cons_of_mem l hz)) x hx, wJ,
      gi_mul _ _ hx]
    unfold GZ lJ
    split_ifs <;> rfl

theorem plettersOK_iff {j : ℕ} {w : List ℤ} :
    plettersOK j w = true ↔ ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j := by
  simp [plettersOK, List.all_eq_true]

theorem progRegs_arrJ : ∀ (prog : List (ℕ × ℕ × ℕ)) (regs : Array (Array ℕ)) (G : ℕ → JH),
    (∀ t ∈ prog, t.1 < 11 ∧ t.2.1 < 11 ∧ t.2.2 < 11) → regs.size = 11 →
    (∀ k < 11, regs[k]! = arrJ (G k)) →
      (progRegs nPts regs prog).size = 11 ∧
        ∀ k < 11, (progRegs nPts regs prog)[k]! = arrJ (runProg G prog k)
  | [], regs, G, _, hs, hg => ⟨hs, hg⟩
  | (a, b, c) :: rest, regs, G, hp, hs, hg => by
    obtain ⟨ha, hb, hc⟩ := hp (a, b, c) List.mem_cons_self
    rw [progRegs, runProg]
    refine progRegs_arrJ rest _ _ (fun t ht => hp t (List.mem_cons_of_mem _ ht)) (by simp [hs])
      fun k hk => ?_
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ k (by simp [hs]; exact hk),
      Array.getElem_setIfInBounds (by simp [hs]; exact hk)]
    by_cases e : c = k
    · subst e
      rw [ite_eq_left rfl, Function.update_self, hg a ha, hg b hb, pcomp_arrJ]
    · rw [ite_eq_right e, Function.update_of_ne (Ne.symm e), ← getElem!_pos regs k (by omega), hg k hk]

@[expose] noncomputable def initJ (k : ℕ) : JH := if k = 1 then aJ else if k = 2 then bJ else 1

theorem regs11_get {α : Type} [Inhabited α] (c a b : α) {k : ℕ} (hk : k < 11) :
    (#[c, a, b] ++ Array.replicate 8 c)[k]! = if k = 1 then a else if k = 2 then b else c := by
  interval_cases k <;> rfl

theorem initRegs_get {a0 a1 : Array ℕ} (h0 : a0 = arrJ aJ) (h1 : a1 = arrJ bJ) :
    (initRegs nPts a0 a1).size = 11 ∧ ∀ k < 11, (initRegs nPts a0 a1)[k]! = arrJ (initJ k) := by
  refine ⟨by simp [initRegs], fun k hk => ?_⟩
  rw [initRegs, pid_arrJ, h0, h1, regs11_get _ _ _ hk, initJ]
  split_ifs <;> rfl

theorem natTab_get {t : Table} {i : ℕ} (hi : i < t.size) : (natTab t)[i]! = ap t i := by
  rw [natTab, getElem!_pos _ i (by simpa using hi), Array.getElem_map, ap,
    getElem!_pos t i hi]

theorem natTab_alpha : natTab alphaT = arrJ aJ := by
  have hs : alphaT.size = nPts := hnsBase.alpha_size
  refine arrJ_ext (by simp [natTab, hs]) fun x hx => ?_
  rw [natTab_get (by omega), gi_of_lt _ hx, aJ_smul, f0_eq hx]

theorem natTab_beta : natTab betaT = arrJ bJ := by
  have hs : betaT.size = nPts := hnsBase.beta_size
  refine arrJ_ext (by simp [natTab, hs]) fun x hx => ?_
  rw [natTab_get (by omega), gi_of_lt _ hx, bJ_smul, f1_eq hx]

@[expose] noncomputable def sJ (W : Array (List ℤ)) (g0 g1 : JH) (j : ℕ) : JH :=
  if j = 0 then g0 else if j = 1 then g1 else
    wJ (fun h => if h < j then sJ W g0 g1 h else 1) W[j]!
termination_by j
decreasing_by assumption

theorem sJ_two {W : Array (List ℤ)} {g0 g1 : JH} {j : ℕ} (hj : 2 ≤ j)
    (hw : ∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) : sJ W g0 g1 j = wJ (sJ W g0 g1) W[j]! := by
  rw [sJ, ite_eq_right (by omega), ite_eq_right (by omega)]
  exact wJ_congr (m := j) (fun h hh => ite_eq_left hh) _ hw

theorem extendStrong_arrJ {W : Array (List ℤ)} {g0 g1 : JH} {s : ℕ} (hs : W.size = s)
    (h2 : 2 ≤ s) (hW : ∀ j, 2 ≤ j → j < s → ∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) :
    extendStrong nPts #[arrJ g0, arrJ g1] W = Array.ofFn (n := s) fun j => arrJ (sJ W g0 g1 j) := by
  obtain ⟨hsz, hget⟩ := extendStrong_get (n := nPts) (m := 2) (orig := #[arrJ g0, arrJ g1])
    (F := fun j => gi (sJ W g0 g1 j)) (FI := fun j => gi (sJ W g0 g1 j)⁻¹) rfl hs h2
    (fun j hj => by
      interval_cases j
      · simp only [List.getElem!_toArray, List.getElem!_cons_zero]
        rw [sJ, ite_eq_left rfl]
        rfl
      · simp only [List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
        rw [sJ, ite_eq_right (by omega), ite_eq_left rfl]
        rfl)
    (fun j hj hjs => ⟨hW j hj hjs, fun x hx => by
      rw [foldr_GZ (m := j) _ (hW j hj hjs) x hx, sJ_two hj (hW j hj hjs)]⟩)
    (fun j _ x hx => ⟨gi_lt _ hx, gi_lt _ hx, gi_inv _ hx⟩)
  refine Array.ext (by rw [hsz, Array.size_ofFn]) fun j h1 h2' => ?_
  have hj : j < s := by simpa using h2'
  rw [← getElem!_pos _ j h1, hget j hj, Array.getElem_ofFn]
  rfl

theorem strong_get {W : Array (List ℤ)} {g0 g1 : JH} {s j : ℕ} (hj : j < s) :
    (Array.ofFn (n := s) fun j => arrJ (sJ W g0 g1 j))[j]! = arrJ (sJ W g0 g1 j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem strong_arrs {W : Array (List ℤ)} {g0 g1 : JH} {s : ℕ} :
    ArrsOK s (Array.ofFn (n := s) fun j => arrJ (sJ W g0 g1 j))
      (pinvs nPts (Array.ofFn (n := s) fun j => arrJ (sJ W g0 g1 j))) (sJ W g0 g1) := by
  intro j hj
  refine ⟨strong_get hj, ?_⟩
  rw [pinvs_get (by simpa using hj), strong_get hj, pinvCand_arrJ]

theorem strongOK_arrJ {W : Array (List ℤ)} {g0 g1 : JH} {s : ℕ} (hs : W.size = s) (h2 : 2 ≤ s)
    (hW : ∀ j, 2 ≤ j → j < s → ∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) :
    strongOK nPts (arrJ g0) (arrJ g1) (Array.ofFn (n := s) fun j => arrJ (sJ W g0 g1 j)) W =
      true := by
  unfold strongOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.size_ofFn]
  refine ⟨⟨⟨⟨⟨by omega, hs.symm⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [strong_get (by omega), sJ, ite_eq_left rfl]
    exact peq_refl _ _
  · rw [strong_get (by omega), sJ, ite_eq_right (by omega), ite_eq_left rfl]
    exact peq_refl _ _
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rw [pinvs_get (by simpa using hj), strong_get hj, pinvCand_arrJ]
    exact pisInv_arrJ _
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rcases Nat.lt_or_ge j 2 with h | h
    · simp [h]
    · have hw := hW j h hj
      rw [plettersOK_iff.2 hw, pword_arrJ strong_arrs W[j]! fun l hl =>
        ⟨(hw l hl).1, by have := (hw l hl).2; omega⟩, strong_get hj, ← sJ_two h hw]
      simp [peq_refl]

end CFSG.KS.HNArr

end
