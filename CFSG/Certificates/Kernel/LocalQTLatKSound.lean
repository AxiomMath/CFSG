
module

public import CFSG.Certificates.Kernel.LocalQTBfsKSound
public import CFSG.Certificates.Kernel.LocalQTLatSound
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.Certificates.Kernel.LocalQTListLemmas
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCertDefs

public section

namespace CFSG.KC.LQT.LK

open Equiv CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

theorem anyA_iff {α : Type} (l : List α) (f : α → Bool) :
    anyA l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp [anyA]
  | cons x l ih =>
    change CFSG.KC.Ord.orB (f x) (anyA l f) = true ↔ _
    rw [P.orB_iff, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem lenA_eq {α : Type} : ∀ l : List α, lenA l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenA_eq l)

theorem getO_eq {α : Type} : ∀ (l : List α) (i : ℕ), getO l i = l[i]?
  | [], _ => rfl
  | x :: l, i => by
    change Bool.rec (motive := fun _ => Option α) (getO l (Nat.sub i 1)) (some x) (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      change getO l (Nat.sub (i + 1) 1) = _
      rw [getO_eq l]
      rfl

theorem eqL_iff : ∀ l m : List ℕ, eqL l m = true ↔ l = m
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | x :: l, y :: m => by
    change CFSG.KC.Ord.andB (Nat.beq x y) (eqL l m) = true ↔ _
    rw [P.andB_iff, P.beq_iff, eqL_iff l m, List.cons.injEq]

theorem recMap {α β : Type} (f : α → β) : ∀ l : List α,
    List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l = l.map f
  | [] => rfl
  | x :: l => by
    change f x :: List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l = _
    rw [recMap f l, List.map_cons]

theorem code_eq_P : (CFSG.KC.LQT.S.code : Perm (Fin n) → ℕ) = P.code := rfl

theorem memK_iff (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) (σ : Perm (Fin n)) :
    memT (bfsK n (L.map P.code) d).t (P.code σ) = true ↔
      RN.enc σ ∈ elts (RN.enc : Perm (Fin n) → RN n) d L := by
  rw [← rnc_enc]
  exact rep_mem_iff (rnc_inj hn) (rep_bfsK hn L d) _

theorem sizeK_eq (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) :
    (bfsK n (L.map P.code) d).size = (elts (RN.enc : Perm (Fin n) → RN n) d L).size :=
  rep_size (rep_bfsK hn L d)

theorem closedK_iff (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) :
    closedK n (L.map P.code) (bfsK n (L.map P.code) d) =
      closedH (L.map RN.enc) (elts (RN.enc : Perm (Fin n) → RN n) d L) :=
  closedK_eq hn L d

theorem allK_iff (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) (f : ℕ → Bool) :
    P.allL (bfsK n (L.map P.code) d).elems f = true ↔
      ∀ r ∈ elts (RN.enc : Perm (Fin n) → RN n) d L, f (rnc r) = true :=
  rep_allL (rep_bfsK hn L d) f

theorem anyK_iff (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) (f : ℕ → Bool) :
    P.anyL (bfsK n (L.map P.code) d).elems f = true ↔
      ∃ r ∈ elts (RN.enc : Perm (Fin n) → RN n) d L, f (rnc r) = true :=
  rep_anyL (rep_bfsK hn L d) f

theorem memK_rnc (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) (r : RN n) :
    memT (bfsK n (L.map P.code) d).t (rnc r) = true ↔
      r ∈ elts (RN.enc : Perm (Fin n) → RN n) d L :=
  rep_mem_iff (rnc_inj hn) (rep_bfsK hn L d) r

theorem rnc_beq (hn : n ≤ 32) (a b : RN n) : Nat.beq (rnc a) (rnc b) = true ↔ a = b := by
  rw [P.beq_iff]
  exact (rnc_inj hn).eq_iff

theorem membersK_eq (n d : ℕ) (T : List (Perm (Fin n))) (lat : List (List (Perm (Fin n)))) :
    membersK n d (T.map P.code) (lat.map (List.map P.code)) =
      (T :: lat).map fun L => (L.map P.code, bfsK n (L.map P.code) d) := by
  unfold membersK
  refine (recMap (fun L => (L, bfsK n L d)) (T.map P.code :: lat.map (List.map P.code))).trans ?_
  simp only [List.map_cons, List.map_map, Function.comp_def]

theorem evalWK_code (hn : n ≤ 32) (A : List (Perm (Fin n))) (w : List ℕ) :
    CFSG.KC.LQT.W.evalWK n (A.map P.code) w = P.code (evalW A w) := by
  have hc : (CFSG.KC.LQT.W.codeP : Perm (Fin n) → ℕ) = P.code := rfl
  induction w with
  | nil => exact P.code_one
  | cons i w ih =>
    change P.mul n (CFSG.KC.LQT.W.genAt n (A.map P.code) i)
      (CFSG.KC.LQT.W.evalWK n (A.map P.code) w) = _
    have hg := CFSG.KC.LQT.W.genAt_map A i
    rw [hc] at hg
    rw [hg, ih, P.code_mul hn]
    rfl

noncomputable def zipK (n : ℕ) (A B : List ℕ) (ws : List (List ℕ)) : Bool :=
  List.rec (motive := fun _ => List (List ℕ) → Bool) (fun _ => true)
    (fun b _ ih ws => List.rec (motive := fun _ => Bool) true
      (fun w ws' _ => CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.W.evalWK n A w) b) (ih ws')) ws) B ws

theorem zipK_sound (A : List ℕ) : ∀ (B : List ℕ) (ws : List (List ℕ)), zipK n A B ws = true →
    ∀ p ∈ B.zip ws, CFSG.KC.LQT.W.evalWK n A p.2 = p.1
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | b :: B, w :: ws, h => by
    change CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.W.evalWK n A w) b) (zipK n A B ws) = true at h
    rw [P.andB_iff, P.beq_iff] at h
    intro p hp
    rw [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h.1
    · exact zipK_sound A B ws h.2 p hp

theorem eqK_sound (hn : n ≤ 32) (A B : List (Perm (Fin n))) (d : ℕ) (ws : List (List ℕ))
    {A' : List ℕ} (hA : A' = A.map P.code)
    (h : eqK n (bfsK n (B.map P.code) d) A' (B.map P.code) ws = true) :
    eqCert RN.enc (elts (RN.enc : Perm (Fin n) → RN n) d B) A B ws = true := by
  subst hA
  change CFSG.KC.Ord.andB _ (CFSG.KC.Ord.andB _ (zipK n (A.map P.code) (B.map P.code) ws)) = true
    at h
  rw [P.andB_iff, P.andB_iff, P.allL_map, P.beq_iff, lenA_eq, lenA_eq, List.length_map] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold eqCert
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨fun g hg => Std.HashSet.contains_iff_mem.2 ((memK_iff hn B d g).1 (h1 g hg)), h2⟩,
    fun p hp => ?_⟩
  obtain ⟨b, w⟩ := p
  have hb : b ∈ B := (List.of_mem_zip hp).1
  have hz : (P.code b, w) ∈ (B.map P.code).zip ws := by
    rw [List.zip_map_left, List.mem_map]
    exact ⟨(b, w), hp, rfl⟩
  have := zipK_sound _ _ _ h3 _ hz
  rw [evalWK_code hn, P.code_eq_iff hn] at this
  change evalW (A.map RN.enc) w = RN.enc b
  rw [← enc_evalW (rawIsEnc n), this]

theorem rec_ord {α : Type} (h : α → NT → NT) (hO : ∀ a t, OrdN t → OrdN (h a t)) :
    ∀ (l : List α) (t : NT), OrdN t →
      OrdN (List.rec (motive := fun _ => NT) t (fun a _ ih => h a ih) l)
  | [], _, ht => ht
  | a :: l, t, ht => hO a _ (rec_ord h hO l t ht)

theorem rec_mem {α : Type} (h : α → NT → NT) (Q : α → ℕ → Prop)
    (hM : ∀ a t x, memN (h a t) x ↔ Q a x ∨ memN t x) :
    ∀ (l : List α) (t : NT) (x : ℕ),
      memN (List.rec (motive := fun _ => NT) t (fun a _ ih => h a ih) l) x ↔
        (∃ a ∈ l, Q a x) ∨ memN t x
  | [], _, _ => by simp
  | a :: l, t, x => by
    change memN (h a (List.rec (motive := fun _ => NT) t (fun a _ ih => h a ih) l)) x ↔ _
    rw [hM, rec_mem h Q hM l t x]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem dcK_spec (n : ℕ) (ET : SetK) (reps : List (ℕ × ℕ × List (List ℕ))) :
    OrdN (dcK n ET reps) ∧ ∀ x, (memN (dcK n ET reps) x ↔
      ∃ r ∈ reps, ∃ e ∈ ET.elems, ∃ f ∈ ET.elems, x = P.mul n (P.mul n e r.1) f) := by
  have o2 : ∀ (r : ℕ × ℕ × List (List ℕ)) (e : ℕ) (t : NT), OrdN t →
      OrdN (List.rec (motive := fun _ => NT) t
        (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f)) ET.elems) := fun r e =>
    rec_ord (fun f t => insT t (P.mul n (P.mul n e r.1) f)) (fun _ _ ht => ord_insT _ ht) ET.elems
  have m2 : ∀ (r : ℕ × ℕ × List (List ℕ)) (e : ℕ) (t : NT) (x : ℕ),
      memN (List.rec (motive := fun _ => NT) t
        (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f)) ET.elems) x ↔
        (∃ f ∈ ET.elems, x = P.mul n (P.mul n e r.1) f) ∨ memN t x := fun r e =>
    rec_mem (fun f t => insT t (P.mul n (P.mul n e r.1) f))
      (fun f x => x = P.mul n (P.mul n e r.1) f) (fun _ _ _ => mem_insT _ _ _) ET.elems
  have o1 : ∀ (r : ℕ × ℕ × List (List ℕ)) (t : NT), OrdN t →
      OrdN (List.rec (motive := fun _ => NT) t (fun e _ ih2 => List.rec (motive := fun _ => NT) ih2
        (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f)) ET.elems) ET.elems) := fun r =>
    rec_ord (fun e t => List.rec (motive := fun _ => NT) t
      (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f)) ET.elems) (fun e t ht => o2 r e t ht)
      ET.elems
  have m1 : ∀ (r : ℕ × ℕ × List (List ℕ)) (t : NT) (x : ℕ),
      memN (List.rec (motive := fun _ => NT) t (fun e _ ih2 => List.rec (motive := fun _ => NT) ih2
        (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f)) ET.elems) ET.elems) x ↔
        (∃ e ∈ ET.elems, ∃ f ∈ ET.elems, x = P.mul n (P.mul n e r.1) f) ∨ memN t x := fun r =>
    rec_mem (fun e t => List.rec (motive := fun _ => NT) t
      (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f)) ET.elems)
      (fun e x => ∃ f ∈ ET.elems, x = P.mul n (P.mul n e r.1) f) (fun e t x => m2 r e t x) ET.elems
  have o0 : OrdN (dcK n ET reps) :=
    rec_ord (fun (r : ℕ × ℕ × List (List ℕ)) (t : NT) => List.rec (motive := fun _ => NT) t (fun e _ ih2 =>
      List.rec (motive := fun _ => NT) ih2 (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f))
        ET.elems) ET.elems) o1 reps NT.lf trivial
  have m0 : ∀ x, memN (dcK n ET reps) x ↔
      (∃ r ∈ reps, ∃ e ∈ ET.elems, ∃ f ∈ ET.elems, x = P.mul n (P.mul n e r.1) f) ∨
        memN NT.lf x :=
    rec_mem (fun (r : ℕ × ℕ × List (List ℕ)) (t : NT) => List.rec (motive := fun _ => NT) t (fun e _ ih2 =>
      List.rec (motive := fun _ => NT) ih2 (fun f _ ih3 => insT ih3 (P.mul n (P.mul n e r.1) f))
        ET.elems) ET.elems) _ m1 reps NT.lf
  refine ⟨o0, fun x => ?_⟩
  rw [m0]
  simp only [memN, or_false]

theorem closedOK_of (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : closedOKK n c.depth (c.mGens.map P.code) (c.tGens.map P.code) (c.lat.map (List.map P.code))
      = true) : c.closedOK RN.enc = true := by
  unfold closedOKK at h
  rw [P.andB_iff, closedK_iff hn, allA_eq_true, membersK_eq] at h
  unfold LatCert.closedOK LatCert.members
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨h.1, fun p hp => ?_⟩
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hp
  have := h.2 _ (List.mem_map_of_mem hL)
  dsimp only at this
  rwa [closedK_iff hn] at this

theorem tleOK_of (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : tleK n c.depth (c.mGens.map P.code) (c.tGens.map P.code) = true) :
    c.tleOK RN.enc = true := by
  unfold tleK at h
  rw [P.allL_map] at h
  unfold LatCert.tleOK
  rw [List.all_eq_true]
  exact fun g hg => Std.HashSet.contains_iff_mem.2 ((memK_iff hn c.mGens c.depth g).1 (h g hg))

theorem coverOK_of (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : coverK n c.depth (c.mGens.map P.code) (c.tGens.map P.code) (repsCode c) = true) :
    c.coverOK RN.enc = true := by
  unfold coverK at h
  rw [allK_iff hn] at h
  obtain ⟨ho, hm⟩ := dcK_spec n (bfsK n (c.tGens.map P.code) c.depth) (repsCode c)
  obtain ⟨-, -, E, -, hmem, hel, -⟩ := rep_bfsK hn c.tGens c.depth
  unfold LatCert.coverOK
  dsimp only
  rw [toList_all_iff]
  intro x hx
  obtain ⟨rp, hrp, e, he, f, hf, hx'⟩ := (hm _).1 ((memT_iff ho _).1 (h x hx))
  rw [hel] at he hf
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hf
  unfold repsCode at hrp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrp
  dsimp only at hx'
  rw [code_eq_P, ← rnc_enc, ← rnc_mul hn, ← rnc_mul hn] at hx'
  have hx'' := rnc_inj hn hx'
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_flatMap]
  refine ⟨r, hr, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨e', Std.HashSet.mem_toList.2 ((hmem e').2 he'), ?_⟩
  rw [List.mem_map]
  exact ⟨f', Std.HashSet.mem_toList.2 ((hmem f').2 hf'), hx''.symm⟩

theorem repsOK_of (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : repsK n (c.tGens.map P.code)
      (membersK n c.depth (c.tGens.map P.code) (c.lat.map (List.map P.code))) (repsCode c) = true) :
    c.repsOK RN.enc = true := by
  rw [membersK_eq] at h
  unfold repsK at h
  rw [allA_eq_true] at h
  unfold LatCert.repsOK LatCert.members
  dsimp only
  rw [List.all_eq_true]
  intro r hr
  have := h _ (by
    unfold repsCode
    exact List.mem_map_of_mem hr)
  dsimp only at this
  rw [getO_eq, List.getElem?_map] at this
  rw [List.getElem?_map]
  cases hj : (c.tGens :: c.lat)[r.2.1]? with
  | none =>
    rw [hj] at this
    exact absurd this (by simp)
  | some L =>
    rw [hj] at this
    simp only [Option.map_some] at this ⊢
    exact eqK_sound hn _ L c.depth r.2.2 (by rw [code_eq_P, List.map_append]; rfl) this

theorem joinsOK_of (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : joinsK n (membersK n c.depth (c.tGens.map P.code) (c.lat.map (List.map P.code))) c.joins
      = true) : c.joinsOK RN.enc = true := by
  rw [membersK_eq] at h
  unfold joinsK at h
  rw [P.andB_iff, P.allN_iff, allA_eq_true, lenA_eq, List.length_map] at h
  obtain ⟨h1, h2⟩ := h
  unfold LatCert.joinsOK LatCert.members
  dsimp only
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun a ha => ?_, fun j hj => ?_⟩
  · rw [List.length_map, List.mem_range] at ha
    have h1a := h1 a ha
    rw [P.allN_iff] at h1a
    rw [List.all_eq_true]
    intro b hb
    rw [List.length_map, List.mem_range] at hb
    have h1b := h1a b hb
    rw [anyA_iff] at h1b
    obtain ⟨j, hj, e⟩ := h1b
    rw [P.andB_iff, P.beq_iff, P.beq_iff] at e
    rw [List.any_eq_true]
    exact ⟨j, hj, by simp [e.1, e.2]⟩
  · have := h2 j hj
    rw [getO_eq, getO_eq, getO_eq, List.getElem?_map, List.getElem?_map, List.getElem?_map] at this
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_map]
    cases ha : (c.tGens :: c.lat)[j.1]? <;> cases hb : (c.tGens :: c.lat)[j.2.1]? <;>
      cases hc : (c.tGens :: c.lat)[j.2.2.1]? <;>
      simp only [ha, hb, hc, Option.map_some, Option.map_none, Bool.false_eq_true] at this ⊢
    rename_i La Lb Lc
    exact eqK_sound hn _ Lc c.depth j.2.2.2 (by rw [List.map_append]; rfl) this

theorem recSize (l : List (List ℕ × SetK)) :
    List.rec (motive := fun _ => List ℕ) [] (fun p _ ih => List.cons p.2.size ih) l =
      l.map fun p => p.2.size :=
  recMap _ l

theorem sizesOK_of (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : sizesK n c.depth (c.mGens.map P.code) (c.tGens.map P.code) (c.lat.map (List.map P.code))
      c.sizes c.msize = true) : c.sizesOK RN.enc = true := by
  unfold sizesK at h
  rw [P.andB_iff, eqL_iff, P.beq_iff, membersK_eq, recSize, List.map_map] at h
  unfold LatCert.sizesOK LatCert.members
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, List.map_map, ← h.1, ← h.2, sizeK_eq hn]
  refine ⟨List.map_congr_left fun L _ => ?_, rfl⟩
  exact (sizeK_eq hn L c.depth).symm

theorem lat_sound (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : latK n c.depth (c.mGens.map CFSG.KC.LQT.S.code) (c.tGens.map CFSG.KC.LQT.S.code)
      (c.lat.map (List.map CFSG.KC.LQT.S.code)) (repsCode c) c.joins c.sizes c.msize = true) :
    c.check RN.enc = true := by
  rw [code_eq_P] at h
  unfold latK at h
  simp only [P.andB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold LatCert.check
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨closedOK_of hn c h1, coverOK_of hn c h2⟩, repsOK_of hn c h3⟩, joinsOK_of hn c h4⟩,
    sizesOK_of hn c h5⟩, tleOK_of hn c h6⟩

theorem tle_sound (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (h : tleK n c.depth (c.mGens.map CFSG.KC.LQT.S.code) (c.tGens.map CFSG.KC.LQT.S.code) = true) :
    c.tleOK RN.enc = true := by
  rw [code_eq_P] at h
  exact tleOK_of hn c h

theorem signs_sound (hn : n ≤ 32) (L : List (Perm (Fin n)))
    (h : P.allL (L.map CFSG.KC.LQT.S.code) (P.even n) = true) : ∀ g ∈ L, Perm.sign g = 1 := by
  rw [code_eq_P, P.allL_map] at h
  exact fun g hg => (P.even_code hn g).1 (h g hg)

open CFSG.QuasithinUnique.L246C127 in
theorem ctK_sound (hn : n ≤ 32) (ct : CTCert (Perm (Fin n)))
    (h : ctK n ct.depth (ct.hGens.map P.code) (ct.nGens.map P.code) ct.expo = true) :
    ct.check RN.enc = true := by
  unfold ctK at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff, and_true] at h
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h
  rw [closedK_iff hn] at c1 c2
  rw [P.allL_map] at c3
  rw [allK_iff hn] at c4 c5
  rw [P.beq_iff, sizeK_eq hn] at c6
  unfold CTCert.check
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨c1, c2⟩, ?_⟩, ?_⟩, ?_⟩, c6⟩
  · rw [List.all_eq_true]
    exact fun g hg => Std.HashSet.contains_iff_mem.2 ((memK_iff hn _ _ g).1 (c3 g hg))
  · rw [toList_all_iff]
    intro r hr
    have h4 := c4 r hr
    rw [P.allL_map] at h4
    rw [List.all_eq_true]
    intro g hg
    have h4g := h4 g hg
    rw [anyK_iff hn] at h4g
    obtain ⟨r', hr', e⟩ := h4g
    rw [toList_any_iff]
    refine ⟨r', hr', ?_⟩
    rw [← rnc_enc, ← rnc_mul hn, ← rnc_mul hn, rnc_beq hn] at e
    rw [beq_iff_eq]
    exact e
  · rw [toList_all_iff]
    intro r hr
    have h5 := c5 r hr
    rw [P.orB_iff, P.notB_iff, P.allL_map, memK_rnc hn] at h5
    rw [Bool.or_eq_true]
    rcases h5 with h5 | h5
    · left
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hall
      apply h5
      intro g hg
      rw [List.all_eq_true] at hall
      have := hall g hg
      rw [beq_iff_eq] at this
      rw [← rnc_enc, ← rnc_mul hn, ← rnc_mul hn, rnc_beq hn]
      exact this
    · exact Or.inr (Std.HashSet.contains_iff_mem.2 h5)

open CFSG.QuasithinUnique.L246C127 in
theorem member_sound (hn : n ≤ 32) (c : LatCert (Perm (Fin n)))
    (cts : List (CTCert (Perm (Fin n))))
    (h : memberK n c.depth (c.tGens.map CFSG.KC.LQT.S.code) (c.lat.map (List.map CFSG.KC.LQT.S.code))
      c.msize (cts.map fun ct => (ct.depth, ct.hGens.map CFSG.KC.LQT.S.code,
        ct.nGens.map CFSG.KC.LQT.S.code, ct.expo)) = true) :
    memberOK c cts = true := by
  rw [code_eq_P] at h
  unfold memberK at h
  rw [allA_eq_true] at h
  unfold memberOK
  rw [List.all_eq_true]
  intro L hL
  have := h (L.map P.code) (by
    rcases List.mem_cons.1 hL with rfl | hL
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hL))
  rw [P.orB_iff, P.beq_iff, sizeK_eq hn, anyA_iff] at this
  rw [Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
  rcases this with e | ⟨ct', hct', e⟩
  · exact Or.inl e
  · obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hct'
    dsimp only at e
    rw [P.andB_iff, eqL_iff] at e
    obtain ⟨e1, e2⟩ := e
    have hHL : ct.hGens = L := List.map_injective_iff.2 (fun a b h => P.code_inj hn h) e1
    refine Or.inr ⟨ct, hct, ?_⟩
    rw [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hHL, ctK_sound hn ct e2⟩

end CFSG.KC.LQT.LK

end
