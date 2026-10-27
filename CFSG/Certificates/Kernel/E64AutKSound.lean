module

public import Certificates.Data.Kernel.E64AutK
public import CFSG.Certificates.Kernel.WrTwinSound
public import CFSG.ClassicalInvolution.Q3.AE.PermElt
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Brg

public section

namespace CFSG.KC.E64AutK

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117 Certificates.E64Aut

variable {e pp : Nat}

theorem pm_enc (a b : Wr 7) : pm (enc a) (enc b) = enc (a * b) :=
  (enc_mul (by norm_num) a b).symm

theorem enc_inj {a b : Wr 7} (h : enc a = enc b) : a = b := enc_injective (by norm_num) h

theorem lvl_mul (σ τ : Equiv.Perm (Fin 7)) : pairMul (lvl σ) (lvl τ) = lvl (σ * τ) := by
  simp only [pairMul, lvl, pm_enc, ← mul_inv_rev, ofPerm_mul]

theorem prods_eq (he : enc (1 : Wr 7) = e) (L : List (List (Equiv.Perm (Fin 7)))) :
    prods e (L.map (·.map lvl)) = (chainProds L).map lvl := by
  induction L with
  | nil =>
    rw [List.map_nil, prods, chainProds, List.map_cons, List.map_nil, ← he]
    simp only [lvl, ofPerm_one, inv_one]
  | cons E L ih =>
    rw [List.map_cons, prods, chainProds, ih, List.flatMap_map, List.map_flatMap]
    congr 1
    funext σ
    simp only [List.map_map]
    exact List.map_congr_left fun τ _ => lvl_mul σ τ

theorem mem_allL : ∀ (n : Nat) (l : List (ZMod 2)), l.length = n → l ∈ allL n
  | 0, [], _ => List.mem_singleton_self _
  | n + 1, x :: l, h => by
    simp only [allL, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨l, mem_allL n l (by simpa using h), ?_⟩
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem vecL_ofFn (v : Fin 7 → ZMod 2) : vecL (List.ofFn v) = v := by
  funext i
  fin_cases i <;> rfl

theorem mem_V64 {v : Fin 7 → ZMod 2} (hv : v ∈ E64Data.evenFin ()) : enc (ofVec v) ∈ V64 := by
  simp only [E64Data.evenFin, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have h1 : vecL (List.ofFn v) ∈ vecs :=
    List.mem_map.2 ⟨_, mem_allL 7 (List.ofFn v) (List.length_ofFn), rfl⟩
  rw [vecL_ofFn] at h1
  exact List.mem_map.2 ⟨v, List.mem_filter.2 ⟨h1, decide_eq_true hv⟩, rfl⟩

theorem tab_cons (x : Wr 7) (L : List (Wr 7)) : tab (x :: L) = enc x :: enc x⁻¹ :: tab L := rfl

theorem tab_getD (he : enc (1 : Wr 7) = e) (L : List (Wr 7)) (k : Nat) :
    (tab L).getD k e = enc (if k % 2 = 0 then L.getD (k / 2) 1 else (L.getD (k / 2) 1)⁻¹) := by
  induction L generalizing k with
  | nil =>
    rw [List.getD_nil, inv_one, ite_self, he]
    rfl
  | cons x L ih =>
    rw [tab_cons]
    rcases k with _ | _ | k
    · rw [List.getD_cons_zero, if_pos (Nat.zero_mod 2), Nat.zero_div, List.getD_cons_zero]
    · have h1 : (0 + 1) % 2 ≠ 0 := by decide
      have h2 : (0 + 1) / 2 = 0 := rfl
      rw [List.getD_cons_succ, List.getD_cons_zero, if_neg h1, h2, List.getD_cons_zero]
    · have h1 : (k + 1 + 1) % 2 = k % 2 := by omega
      have h2 : (k + 1 + 1) / 2 = k / 2 + 1 := by omega
      rw [List.getD_cons_succ, List.getD_cons_succ, ih k, h1, h2, List.getD_cons_succ]

theorem tab_append (L L' : List (Wr 7)) : tab (L ++ L') = tab L ++ tab L' :=
  List.flatMap_append

theorem tab_single (x : Wr 7) : tab [x] = [enc x, enc x⁻¹] := rfl

theorem pw_eq (he : enc (1 : Wr 7) = e) (L : List (Wr 7)) (w : List Nat) :
    pw e (tab L) w = enc (evalG L w) := by
  have key : ∀ (w : List Nat) (acc : Wr 7),
      w.foldl (fun acc k => pm acc ((tab L).getD k e)) (enc acc) =
        enc (w.foldl (fun acc k =>
          acc * if k % 2 = 0 then L.getD (k / 2) 1 else (L.getD (k / 2) 1)⁻¹) acc) := by
    intro w
    induction w with
    | nil => intro acc; rfl
    | cons j w ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, tab_getD he, pm_enc, ih]
  cases w with
  | nil =>
    rw [← he]
    rfl
  | cons k w =>
    rw [pw, tab_getD he, key]
    simp only [evalG, List.foldl_cons, one_mul]

theorem evalG_perm {L L' : List (Wr 7)} (h : L.map Wr.perm = L'.map Wr.perm) (w : List Nat) :
    (evalG L w).perm = (evalG L' w).perm := by
  have h1 := TL4.Mdl117.evalG_map (permHom 7) L w
  have h2 := TL4.Mdl117.evalG_map (permHom 7) L' w
  have h3 : L.map (permHom 7) = L'.map (permHom 7) := h
  change permHom 7 (evalG L w) = permHom 7 (evalG L' w)
  rw [h1, h2, h3]

theorem eqPi_iff' {x y : Wr 7} : eqPi x y = true ↔ x = y ∨ x * allOnes 7 = y := by
  simp only [eqPi, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h, mul_assoc, allOnes_mul_self 7, mul_one])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h, mul_assoc, allOnes_mul_self 7, mul_one])

theorem eqPi_comm {x y : Wr 7} (h : eqPi x y = true) : eqPi y x = true := by
  rcases eqPi_iff'.1 h with h | h
  · exact eqPi_iff'.2 (Or.inl h.symm)
  · exact eqPi_iff'.2 (Or.inr (by rw [← h, mul_assoc, allOnes_mul_self 7, mul_one]))

theorem eqPi_perm' {x y : Wr 7} (h : eqPi x y = true) : x.perm = y.perm := by
  rcases eqPi_iff'.1 h with h | h
  · rw [h]
  · rw [← h, mul_perm]
    exact (mul_one _).symm

theorem inPi_perm' {x : Wr 7} (h : inPi x = true) : x.perm = 1 := by
  simp only [inPi, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> rfl

theorem inPiP_iff (he : enc (1 : Wr 7) = e) (hp : enc (allOnes 7) = pp) (x : Wr 7) :
    inPiP e pp (enc x) = true ↔ inPi x = true := by
  rw [← he, ← hp]
  simp only [inPiP, inPi, Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl (enc_inj h)
    · exact Or.inr (enc_inj h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem inModPi_iff (hp : enc (allOnes 7) = pp) (x : Wr 7) (B : List (Wr 7)) :
    inModPi pp (enc x) (B.map enc) = true ↔ ∃ y ∈ B, eqPi x y = true := by
  rw [← hp]
  simp only [inModPi, Bool.or_eq_true, List.any_map, List.any_eq_true, Function.comp_apply,
    Nat.beq_eq, pm_enc]
  constructor
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, hy, eqPi_iff'.2 (Or.inl (enc_inj h))⟩
    · exact ⟨y, hy, eqPi_iff'.2 (Or.inr (enc_inj h))⟩
  · rintro ⟨y, hy, h⟩
    rcases eqPi_iff'.1 h with h | h
    · exact Or.inl ⟨y, hy, by rw [h]⟩
    · exact Or.inr ⟨y, hy, by rw [h]⟩

theorem nib_enc_perm (a : Wr 7) (i : Nat) (hi : i < 7) :
    nib (enc a) (2 * i) / 2 = (a.perm ⟨i, hi⟩).val := by
  have h1 : nib (enc a) (2 * i) = img a (2 * i) := nib_enc (by norm_num) a (by omega)
  have h2 : img a (2 * i) =
      2 * (a.perm ⟨i, hi⟩).val + ((0 : ZMod 2) + a.vec (a.perm ⟨i, hi⟩)).val := by
    have := img_pt a ⟨i, hi⟩ 0
    rwa [ZMod.val_zero, add_zero] at this
  have h3 := ZMod.val_lt ((0 : ZMod 2) + a.vec (a.perm ⟨i, hi⟩))
  rw [h1, h2]
  omega

theorem samePerm_iff (a b : Wr 7) : samePerm (enc a) (enc b) = true ↔ a.perm = b.perm := by
  simp only [samePerm, List.all_eq_true, List.mem_range, Nat.beq_eq]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have := h i.val i.isLt
    rw [nib_enc_perm a i.val i.isLt, nib_enc_perm b i.val i.isLt] at this
    exact this
  · intro h i hi
    rw [nib_enc_perm a i hi, nib_enc_perm b i hi, h]

theorem ofVec_mul_ofPerm (a : Wr 7) : ofVec a.vec * ofPerm a.perm = a := by
  refine Wr.ext (funext fun i => ?_) (one_mul _)
  change a.vec i + 0 = a.vec i
  rw [add_zero]

theorem ofPerm_inv_mul_ofVec (a : Wr 7) : (ofPerm a.perm)⁻¹ * ofVec a.vec = a⁻¹ := by
  have hv : (ofVec a.vec)⁻¹ = ofVec a.vec := Wr.ext (funext fun _ => rfl) inv_one
  conv_rhs => rw [← ofVec_mul_ofPerm a]
  rw [mul_inv_rev, hv]

theorem lvl_fst (σ : Equiv.Perm (Fin 7)) : (lvl σ).1 = enc (ofPerm σ) := rfl

theorem lvl_snd (σ : Equiv.Perm (Fin 7)) : (lvl σ).2 = enc (ofPerm σ)⁻¹ := rfl

theorem pm_lvl (a : Wr 7) : pm (enc (ofVec a.vec)) (lvl a.perm).1 = enc a := by
  rw [lvl_fst, pm_enc, ofVec_mul_ofPerm]

theorem pm_lvl_inv (a : Wr 7) : pm (lvl a.perm).2 (enc (ofVec a.vec)) = enc a⁻¹ := by
  rw [lvl_snd, pm_enc, ofPerm_inv_mul_ofVec]

theorem centOK_sound (he : enc (1 : Wr 7) = e) (hp : enc (allOnes 7) = pp)
    {P : List (Nat × Nat)} {V : List Nat} {S : List (Wr 7)}
    (h : centOK e pp P V (S.map enc) = true) (a : Wr 7)
    (hP : lvl a.perm ∈ P) (hV : enc (ofVec a.vec) ∈ V)
    (hc : ∀ s ∈ S, eqPi (a * s) (s * a) = true) : eqPi a 1 = true := by
  have h1 := List.all_eq_true.1 h _ hP
  beta_reduce at h1
  have hA : ((S.map enc).all fun s => samePerm (pm (lvl a.perm).1 s) (pm s (lvl a.perm).1)) =
      true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [lvl_fst, pm_enc, pm_enc, samePerm_iff, mul_perm, mul_perm]
    have h3 : (a * s).perm = (s * a).perm := eqPi_perm' (hc s hs)
    rw [mul_perm, mul_perm] at h3
    change a.perm * s.perm = s.perm * a.perm
    exact h3
  rw [hA, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 _ hV
  beta_reduce at h2
  have hB : ((S.map enc).all fun s => inModPi pp (pm (pm (enc (ofVec a.vec)) (lvl a.perm).1) s)
      [pm s (pm (enc (ofVec a.vec)) (lvl a.perm).1)]) = true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [pm_lvl, pm_enc, pm_enc]
    exact (inModPi_iff hp (a * s) [s * a]).2 ⟨s * a, List.mem_singleton_self _, hc s hs⟩
  rw [hB, Bool.not_true, Bool.false_or, pm_lvl, inPiP_iff he hp] at h2
  rcases (by simpa only [inPi, Bool.or_eq_true, decide_eq_true_eq] using h2 :
    a = 1 ∨ a = allOnes 7) with h3 | h3
  · exact eqPi_iff'.2 (Or.inl h3)
  · exact eqPi_iff'.2 (Or.inr (by rw [h3, allOnes_mul_self 7]))

theorem solOK_sound (he : enc (1 : Wr 7) = e) (hp : enc (allOnes 7) = pp)
    {R : List (List Nat)} {P : List (Nat × Nat)} {V : List Nat} {W Cg : List (Wr 7)}
    (h : solOK e pp R P V (tab W) (Cg.map enc) = true) (a : Wr 7)
    (hP : lvl a.perm ∈ P) (hV : enc (ofVec a.vec) ∈ V)
    (hrel : ∀ r ∈ R, inPi (evalG (W ++ [a]) r) = true) : ∃ y ∈ Cg, eqPi a y = true := by
  have h1 := List.all_eq_true.1 h _ hP
  have htP : tab W ++ [(lvl a.perm).1, (lvl a.perm).2] = tab (W ++ [ofPerm a.perm]) := by
    rw [tab_append, tab_single]
    rfl
  have hA : (R.all fun r => samePerm (pw e (tab W ++ [(lvl a.perm).1, (lvl a.perm).2]) r) e) =
      true := by
    rw [List.all_eq_true]
    intro r hr
    have hperm : (W ++ [ofPerm a.perm]).map Wr.perm = (W ++ [a]).map Wr.perm := by
      rw [List.map_append, List.map_append]
      rfl
    rw [htP, pw_eq he, ← he, samePerm_iff, evalG_perm hperm r]
    exact inPi_perm' (hrel r hr)
  rw [hA, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 _ hV
  have hB : (R.all fun r => inPiP e pp (pw e (tab W ++
      [pm (enc (ofVec a.vec)) (lvl a.perm).1, pm (lvl a.perm).2 (enc (ofVec a.vec))]) r)) =
        true := by
    rw [List.all_eq_true]
    intro r hr
    rw [pm_lvl, pm_lvl_inv, ← tab_single, ← tab_append, pw_eq he, inPiP_iff he hp]
    exact hrel r hr
  rw [hB, Bool.not_true, Bool.false_or, pm_lvl, inModPi_iff hp] at h2
  exact h2

theorem memOK_sound (he : enc (1 : Wr 7) = e) (hp : enc (allOnes 7) = pp) {T Y : List (Wr 7)}
    (h : memOK e pp (tab T) (Y.map enc) = true) :
    ∀ y ∈ Y, ∃ w ∈ words0, eqPi (evalG T w) y = true := by
  intro y hy
  have h1 := List.all_eq_true.1 h _ (List.mem_map_of_mem hy)
  have hw : words0.map (pw e (tab T)) = (words0.map (evalG T)).map enc := by
    rw [List.map_map]
    exact List.map_congr_left fun w _ => pw_eq he T w
  rw [hw, inModPi_iff hp] at h1
  obtain ⟨_, hz, hyz⟩ := h1
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
  exact ⟨w, hw, eqPi_comm hyz⟩

theorem conjIn_sound (hp : enc (allOnes 7) = pp) {s : Wr 7} {A B : List (Wr 7)}
    (h : conjIn pp (enc s) (enc s⁻¹) (A.map enc) (B.map enc) = true) :
    ∀ x ∈ A, ∃ y ∈ B, eqPi (s * x * s⁻¹) y = true := by
  intro x hx
  have h1 := List.all_eq_true.1 h _ (List.mem_map_of_mem hx)
  rw [pm_enc, pm_enc, inModPi_iff hp] at h1
  exact h1

theorem memAtL_of {α : Finset (Fin 7)} {a b c d : Fin 7} (hα : α = [a, b, c, d].toFinset)
    (hn : [a, b, c, d].Nodup) (hp : [a, b, c, d].Pairwise (· ≤ ·)) (x : Bool) :
    memAtL α x = memLC a b c d x := by
  unfold memAtL
  rw [hα, (List.toFinset_sort (· ≤ ·) hn).2 hp]

theorem memAtL_c0 (x : Bool) : memAtL ({0, 1, 3} : Finset (Fin 7))ᶜ x = memQ (2, 4, 5, 6) x :=
  memAtL_of (by decide) (by decide) (by decide) x

theorem memAtL_c1 (x : Bool) : memAtL ({1, 2, 4} : Finset (Fin 7))ᶜ x = memQ (0, 3, 5, 6) x :=
  memAtL_of (by decide) (by decide) (by decide) x

theorem memAtL_c2 (x : Bool) : memAtL ({2, 3, 5} : Finset (Fin 7))ᶜ x = memQ (0, 1, 4, 6) x :=
  memAtL_of (by decide) (by decide) (by decide) x

theorem memAtL_c3 (x : Bool) : memAtL ({3, 4, 6} : Finset (Fin 7))ᶜ x = memQ (0, 1, 2, 5) x :=
  memAtL_of (by decide) (by decide) (by decide) x

theorem memAtL_c4 (x : Bool) : memAtL ({4, 5, 0} : Finset (Fin 7))ᶜ x = memQ (1, 2, 3, 6) x :=
  memAtL_of (by decide) (by decide) (by decide) x

theorem memAtL_c5 (x : Bool) : memAtL ({5, 6, 1} : Finset (Fin 7))ᶜ x = memQ (0, 2, 3, 4) x :=
  memAtL_of (by decide) (by decide) (by decide) x

theorem memAtL_c6 (x : Bool) : memAtL ({6, 0, 2} : Finset (Fin 7))ᶜ x = memQ (1, 3, 4, 5) x :=
  memAtL_of (by decide) (by decide) (by decide) x

theorem allMembers_eq : allMembers () = membersQ := by
  simp only [allMembers, membersQ, quads, twinQ, fanoLines, List.flatMap_cons, List.flatMap_nil,
    memAtL_c0, memAtL_c1, memAtL_c2, memAtL_c3, memAtL_c4, memAtL_c5, memAtL_c6]

end CFSG.KC.E64AutK

end
