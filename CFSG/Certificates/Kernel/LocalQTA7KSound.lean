
module

public import CFSG.Certificates.Kernel.LocalQTBfsMSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.Certificates.Kernel.LocalQTLatKSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc
public import CFSG.Certificates.Kernel.LocalQTChainMSound

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.KC.LQT.S CFSG.KC.LQT.CM CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Unc25K1.Six

theorem bfsRun7_eq (gens : List Seven.R7) : ∀ (d : ℕ) (st : Std.HashSet Seven.R7 × List Seven.R7),
    Seven.bfsRun gens d st = PermLat.bfsRun gens d st
  | 0, _ => rfl
  | d + 1, st => by
    rw [Seven.bfsRun, PermLat.bfsRun]
    exact bfsRun7_eq gens d _

theorem bfsSet7_eq (gens : List Seven.R7) (d : ℕ) :
    Seven.bfsSet gens d = PermLat.bfsSet gens d := by
  unfold Seven.bfsSet PermLat.bfsSet
  rw [bfsRun7_eq]

theorem closedH7_eq (gens : List Seven.R7) (S : Std.HashSet Seven.R7) :
    Seven.closedH gens S = PermLat.closedH gens S := by
  unfold Seven.closedH PermLat.closedH
  rfl

@[expose] noncomputable def rc7 (r : Seven.R7) : ℕ :=
  P.ofFn 7 fun i => if h : i < 7 then (r.get ⟨i, h⟩ : ℕ) else 0

theorem rc7_lt (r : Seven.R7) : ∀ i < 7, (if h : i < 7 then (r.get ⟨i, h⟩ : ℕ) else 0) < 7 :=
  fun i hi => by
    simp only [hi, ↓reduceDIte]
    exact (r.get _).isLt

theorem img_rc7 (r : Seven.R7) {i : ℕ} (hi : i < 7) : P.img (rc7 r) i = r.get ⟨i, hi⟩ := by
  rw [rc7, img_ofFn (by norm_num) (rc7_lt r) hi]
  simp only [hi, ↓reduceDIte]

theorem fc_rc7 (r : Seven.R7) : FC 7 (rc7 r) := fc_ofFn (by norm_num) (rc7_lt r)

theorem get_mul7 (x y : Seven.R7) (i : Fin 7) : (x * y).get i = x.get (y.get i) := by
  fin_cases i <;> rfl

theorem get_one7 (i : Fin 7) : (1 : Seven.R7).get i = i := by
  fin_cases i <;> rfl

theorem ext7 {a b : Seven.R7} (h : ∀ i, a.get i = b.get i) : a = b := by
  cases a
  cases b
  simp only [Seven.R7.mk.injEq]
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩

theorem rc7_inj {a b : Seven.R7} (h : rc7 a = rc7 b) : a = b := by
  refine ext7 fun i => Fin.ext ?_
  have := img_rc7 a i.isLt
  rw [h, img_rc7 b i.isLt] at this
  exact this.symm

theorem rc7_mul (x y : Seven.R7) : rc7 (x * y) = P.mul 7 (rc7 x) (rc7 y) := by
  refine fc_ext (fc_rc7 _) (fc_mul (by norm_num) (fc_rc7 x) (fc_rc7 y)) fun i hi => ?_
  rw [img_mul (by norm_num) (fc_rc7 x) (fc_rc7 y) hi, img_rc7 _ hi, img_rc7 y hi,
    img_rc7 x (Fin.is_lt _), get_mul7]

theorem rc7_one : rc7 1 = P.one 7 := by
  refine fc_ext (fc_rc7 _) (fc_one (by norm_num)) fun i hi => ?_
  rw [img_rc7 _ hi, img_one (by norm_num) hi, get_one7]

theorem rc7_enc (σ : Seven.P7) : rc7 (Seven.R7.enc σ) = code σ := by
  refine fc_ext (fc_rc7 _) (fc_code (by norm_num) σ) fun i hi => ?_
  rw [img_rc7 _ hi, Seven.R7.get_enc]
  exact (P.img_code (by norm_num) σ ⟨i, hi⟩).symm

theorem map_code7 (G : List Seven.P7) : G.map code = (G.map Seven.R7.enc).map rc7 := by
  simp only [List.map_map, Function.comp_def, rc7_enc]

theorem idxInj7 {C : List Lvl} (hok : chainOK 7 C = true) (hI : chainInj 7 C = true) (F : ℕ) :
    IdxInj rc7 7 C F := fun a b hlt he =>
  rc7_inj (idxM_inj (by norm_num) hok hI (fc_rc7 a) (fc_rc7 b) hlt he)

theorem rep7 {C : List Lvl} (hok : chainOK 7 C = true) (hI : chainInj 7 C = true)
    (L : List Seven.R7) (d : ℕ) (hb : (bfsM 7 C (chainF C) (L.map rc7) d).ok = true) :
    RepM rc7 7 C (chainF C) (bfsM 7 C (chainF C) (L.map rc7) d) (PermLat.bfsSet L d) :=
  rep_bfsM (idxInj7 hok hI _) rc7_mul rc7_one L d hb

theorem ok_of_closedM {n F : ℕ} {C : List Lvl} {G : List ℕ} {S : SetM}
    (h : closedM n C F G S = true) : S.ok = true := (P.andB_iff.1 h).1

theorem closed7_sound (C : List Lvl) (hI : chainInj 7 C = true) (G : List Seven.P7) {d : ℕ}
    (h : closed7 C d (G.map code) = true) :
    Seven.closedH (G.map Seven.R7.enc) (Seven.bfsSet (G.map Seven.R7.enc) d) = true := by
  unfold closed7 at h
  rw [P.andB_iff, map_code7] at h
  obtain ⟨hok, hc⟩ := h
  have hb := ok_of_closedM hc
  rw [closedH7_eq, bfsSet7_eq]
  exact (closedM_iff (idxInj7 hok hI _) rc7_mul rc7_one _ (rep7 hok hI _ d hb) hb).1 hc

theorem sizes7_sound (C : List Lvl) (hI : chainInj 7 C = true) (Ls : List (List Seven.P7))
    {d : ℕ} {N : List ℕ} (h : sizes7 C d (Ls.map (List.map code)) N = true) :
    Ls.map (fun G => (Seven.bfsSet (G.map Seven.R7.enc) d).size) = N := by
  unfold sizes7 at h
  rw [P.andB_iff, P.andB_iff, LK.eqL_iff, allA_eq_true] at h
  obtain ⟨hok, hoks, he⟩ := h
  rw [← he, LK.recMap (fun G => (bfsM 7 C (chainF C) G d).size), List.map_map]
  refine List.map_congr_left fun G hG => ?_
  have hb := hoks _ (List.mem_map_of_mem hG)
  simp only [Function.comp]
  rw [map_code7] at hb ⊢
  rw [bfsSet7_eq]
  exact (repM_size (rep7 hok hI _ d hb)).symm

theorem setEq_of_setEqM {C : List Lvl} (hok : chainOK 7 C = true) (hI : chainInj 7 C = true)
    (L K : List Seven.R7) (d : ℕ)
    (h : setEqM (bfsM 7 C (chainF C) (L.map rc7) d) (bfsM 7 C (chainF C) (K.map rc7) d) = true) :
    Seven.setEq (Seven.bfsSet L d) (Seven.bfsSet K d) = true := by
  unfold setEqM at h
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff, P.beq_iff] at h
  obtain ⟨ha, hb, hs, hm⟩ := h
  have hA := rep7 hok hI L d ha
  have hB := rep7 hok hI K d hb
  have hmem := repM_mask_eq (idxInj7 hok hI _) hA hB hm
  unfold Seven.setEq
  rw [bfsSet7_eq, bfsSet7_eq, ← repM_size hA, ← repM_size hB, hs]
  simp only [decide_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
    Std.HashSet.mem_toList, Std.HashSet.contains_iff_mem]
  exact ⟨fun r hr => (hmem r).1 hr, fun r hr => (hmem r).2 hr⟩

theorem isLat7_sound (C : List Lvl) (hI : chainInj 7 C = true) (G : List Seven.P7)
    (Ls : List (List Seven.P7)) {d : ℕ}
    (h : isLat7 C d (G.map code) (Ls.map (List.map code)) = true) :
    (Seven.closedH (G.map Seven.R7.enc) (Seven.bfsSet (G.map Seven.R7.enc) d) &&
      (Ls.map fun Z => Seven.bfsSet (Z.map Seven.R7.enc) d).any fun Z =>
        Seven.setEq (Seven.bfsSet (G.map Seven.R7.enc) d) Z) = true := by
  unfold isLat7 at h
  rw [P.andB_iff, P.andB_iff, LK.anyA_iff] at h
  obtain ⟨hok, hc, Z', hZ', he⟩ := h
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hZ'
  rw [Bool.and_eq_true, List.any_eq_true]
  refine ⟨?_, ⟨_, List.mem_map_of_mem hZ, ?_⟩⟩
  · rw [map_code7] at hc
    have hb := ok_of_closedM hc
    rw [closedH7_eq, bfsSet7_eq]
    exact (closedM_iff (idxInj7 hok hI _) rc7_mul rc7_one _ (rep7 hok hI _ d hb) hb).1 hc
  · rw [map_code7, map_code7] at he
    exact setEq_of_setEqM hok hI _ _ d he

theorem addM_bit {n F : ℕ} {C : List Lvl} {S : SetM × List ℕ} {y i : ℕ}
    (hok : (addM n C F S y).1.ok = true) (h : (addM n C F S y).1.mask.testBit i = true) :
    S.1.mask.testBit i = true ∨ (idxM n C F y = i ∧ idxM n C F y < F) := by
  rw [addM_eq] at hok h
  split_ifs at hok h with hb
  · exact Or.inl h
  · change CFSG.KC.Ord.andB S.1.ok (Nat.blt (idxM n C F y) F) = true at hok
    change (S.1.mask ||| 2 ^ idxM n C F y).testBit i = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_iff] at h
    exact h.imp_right fun e => ⟨e, P.blt_iff.1 (P.andB_iff.1 hok).2⟩

abbrev DcInv (n F : ℕ) (C : List Lvl) (L : List ℕ) (r : ℕ) (st : SetM × List ℕ) : Prop :=
  st.1.ok = true → ∀ i, st.1.mask.testBit i = true →
    i < F ∧ ∃ e ∈ L, ∃ f ∈ L, idxM n C F (P.mul n (P.mul n e r) f) = i

theorem dcInv_inner {n F : ℕ} {C : List Lvl} {L : List ℕ} {r e : ℕ} (he : e ∈ L) :
    ∀ (fs : List ℕ), (∀ f ∈ fs, f ∈ L) → ∀ st, DcInv n F C L r st →
      DcInv n F C L r (List.rec (motive := fun _ => SetM × List ℕ) st
        (fun f _ ih2 => addM n C F ih2 (P.mul n (P.mul n e r) f)) fs)
  | [], _, _, h => h
  | f :: fs, hfs, st, h => by
    intro hok i hi
    change (addM n C F (List.rec (motive := fun _ => SetM × List ℕ) st
      (fun f _ ih2 => addM n C F ih2 (P.mul n (P.mul n e r) f)) fs)
      (P.mul n (P.mul n e r) f)).1.ok = true at hok
    change (addM n C F (List.rec (motive := fun _ => SetM × List ℕ) st
      (fun f _ ih2 => addM n C F ih2 (P.mul n (P.mul n e r) f)) fs)
      (P.mul n (P.mul n e r) f)).1.mask.testBit i = true at hi
    have ih := dcInv_inner he fs (fun f hf => hfs f (List.mem_cons_of_mem _ hf)) st h (ok_addM hok)
    rcases addM_bit hok hi with hb | ⟨e1, e2⟩
    · exact ih i hb
    · exact ⟨e1 ▸ e2, e, he, f, hfs f (List.mem_cons_self ..), e1⟩

theorem dcInv_outer {n F : ℕ} {C : List Lvl} {L : List ℕ} {r : ℕ} :
    ∀ (es : List ℕ), (∀ e ∈ es, e ∈ L) →
      DcInv n F C L r (List.rec (motive := fun _ => SetM × List ℕ) (Prod.mk (SetM.mk 0 0 [] true) [])
        (fun e _ ih => List.rec (motive := fun _ => SetM × List ℕ) ih
          (fun f _ ih2 => addM n C F ih2 (P.mul n (P.mul n e r) f)) L) es)
  | [], _ => fun _ i hi => by simp at hi
  | e :: es, hes => dcInv_inner (hes e (List.mem_cons_self ..)) L (fun _ hf => hf) _
      (dcInv_outer es fun e he => hes e (List.mem_cons_of_mem _ he))

theorem mem_dc7 {C : List Lvl} {ED : SetM} {r x : ℕ} (hok : (dc7 C ED r).ok = true)
    (h : memM 7 C (chainF C) (dc7 C ED r) x = true) :
    idxM 7 C (chainF C) x < chainF C ∧ ∃ e ∈ ED.elems, ∃ f ∈ ED.elems,
      idxM 7 C (chainF C) (P.mul 7 (P.mul 7 e r) f) = idxM 7 C (chainF C) x := by
  rw [memM_eq] at h
  exact dcInv_outer (n := 7) (F := chainF C) (C := C) (L := ED.elems) (r := r) ED.elems
    (fun _ he => he) hok _ h

theorem cover7_sound (C : List Lvl) (hI : chainInj 7 C = true) (D R : List Seven.P7) {d : ℕ}
    (h : cover7 C d (D.map code) (R.map code) = true) :
    ∀ x : Seven.P7, Perm.sign x = 1 → ∃ p ∈ R.map (fun r => (r, Std.HashSet.ofList
      ((Seven.bfsSet (D.map Seven.R7.enc) d).toList.flatMap fun a =>
        (Seven.bfsSet (D.map Seven.R7.enc) d).toList.map fun e => a * Seven.R7.enc r * e))),
      Seven.R7.enc x ∈ p.2 := by
  intro x hx
  unfold cover7 at h
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.allP_iff] at h
  obtain ⟨hok, hb, hr, hall⟩ := h
  have hx' := hall x
  beta_reduce at hx'
  rw [P.impB_iff, P.even_code (by norm_num), P.anyL_iff] at hx'
  obtain ⟨rc, hrc, hm⟩ := hx' hx
  obtain ⟨r, hrR, rfl⟩ := List.mem_map.1 hrc
  have hdok : (dc7 C (bfsM 7 C (chainF C) (D.map code) d) (code r)).ok = true :=
    (P.allL_iff _ _).1 hr _ hrc
  obtain ⟨hlt, e, he, f, hf, hidx⟩ := mem_dc7 hdok hm
  rw [map_code7] at hb he hf
  obtain ⟨E, -, hmem, hel, -, -, -⟩ := rep7 hok hI _ d hb
  rw [hel] at he hf
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
  obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hf
  have e1 : P.mul 7 (P.mul 7 (rc7 a) (code r)) (rc7 b) = rc7 (a * Seven.R7.enc r * b) := by
    rw [rc7_mul, rc7_mul, rc7_enc]
  have ex : P.code x = rc7 (Seven.R7.enc x) := (rc7_enc x).symm
  rw [e1, ex] at hidx
  rw [ex] at hlt
  have hlt' : idxM 7 C (chainF C) (rc7 (a * Seven.R7.enc r * b)) < chainF C := by
    rw [hidx]
    exact hlt
  have hxe : a * Seven.R7.enc r * b = Seven.R7.enc x := idxInj7 hok hI _ _ _ hlt' hidx
  refine ⟨_, List.mem_map_of_mem hrR, ?_⟩
  change Seven.R7.enc x ∈ Std.HashSet.ofList _
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_flatMap]
  refine ⟨a, ?_, ?_⟩
  · rw [Std.HashSet.mem_toList, bfsSet7_eq]
    exact (hmem a).2 ha
  · rw [List.mem_map]
    refine ⟨b, ?_, hxe⟩
    rw [Std.HashSet.mem_toList, bfsSet7_eq]
    exact (hmem b).2 hb'

theorem iffB_iff {a b : Bool} : iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [iffB, CFSG.KC.Ord.notB]

theorem memIff7_sound {C : List Lvl} (hI : chainInj 7 C = true) (G : List Seven.P7) {d : ℕ}
    {p : ℕ → Bool} (h : memIff7 C d (G.map code) p = true) :
    ∀ x : Seven.P7, Perm.sign x = 1 →
      ((Seven.bfsSet (G.map Seven.R7.enc) d).contains (Seven.R7.enc x) = true ↔
        p (code x) = true) := by
  intro x hx
  unfold memIff7 at h
  rw [P.andB_iff, P.andB_iff, P.allP_iff] at h
  obtain ⟨hok, hb, hall⟩ := h
  have hx' := hall x
  beta_reduce at hx'
  rw [P.impB_iff, P.even_code (by norm_num), iffB_iff] at hx'
  have hx'' : memM 7 C (chainF C) (bfsM 7 C (chainF C) (G.map code) d) (rc7 (Seven.R7.enc x)) =
      true ↔ p (code x) = true := by
    rw [rc7_enc]
    exact hx' hx
  rw [← hx'', map_code7, Std.HashSet.contains_iff_mem, bfsSet7_eq]
  rw [map_code7] at hb
  exact (repM_mem (idxInj7 hok hI _) (rep7 hok hI _ d hb) _).symm

theorem img7 (x : Seven.P7) (k : Fin 7) : P.img (code x) k = x k := P.img_code (by norm_num) x k

theorem fix7_sound (C : List Lvl) (hI : chainInj 7 C = true) (G : List Seven.P7) {d : ℕ}
    (k : Fin 7)
    (h : memIff7 C d (G.map code) (fun x => Nat.beq (CFSG.KC.LQT.P.img x k) k) = true) :
    ∀ x : Seven.P7, Perm.sign x = 1 →
      ((Seven.bfsSet (G.map Seven.R7.enc) d).contains (Seven.R7.enc x) = true ↔ x k = k) := by
  intro x hx
  rw [memIff7_sound hI G h x hx, img7, P.beq_iff, Fin.val_inj]

theorem pair7_sound (C : List Lvl) (hI : chainInj 7 C = true) (G : List Seven.P7) {d : ℕ}
    (a b : Fin 7)
    (h : memIff7 C d (G.map code) (fun x => CFSG.KC.Ord.andB
      (CFSG.KC.Ord.orB (Nat.beq (CFSG.KC.LQT.P.img x a) a) (Nat.beq (CFSG.KC.LQT.P.img x a) b))
      (CFSG.KC.Ord.orB (Nat.beq (CFSG.KC.LQT.P.img x b) a) (Nat.beq (CFSG.KC.LQT.P.img x b) b))) =
      true) :
    ∀ x : Seven.P7, Perm.sign x = 1 →
      ((Seven.bfsSet (G.map Seven.R7.enc) d).contains (Seven.R7.enc x) = true ↔
        (x a = a ∨ x a = b) ∧ (x b = a ∨ x b = b)) := by
  intro x hx
  rw [memIff7_sound hI G h x hx, P.andB_iff, P.orB_iff, P.orB_iff, img7, img7, P.beq_iff,
    P.beq_iff, P.beq_iff, P.beq_iff, Fin.val_inj, Fin.val_inj, Fin.val_inj, Fin.val_inj]

end CFSG.KC.LQT.L

end
