module

public import CFSG.Certificates.Kernel.H9Four.Masks
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.KC.H9Four.Sound

open CFSG.Quasithin.H13.H9Four CFSG.KC.H9Four CFSG.KC.H9Four.Codes CFSG.KC.Misc.Spec
  CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.H9Four.Masks

@[expose] def invAllOf (L : List ℕ) (S : List (ℕ × ℕ)) : List Elt :=
  L.map (fun k => ⟨Mat.ofCode k, Mat.ofCode k, false⟩) ++
    S.map fun p => ⟨Mat.ofCode p.1, Mat.ofCode p.2, true⟩

@[expose] def repsOf (R : List (List (ℕ × ℕ × Bool))) : List (List Elt) := R.map (·.map Elt.ofCodes)

@[expose] def checkInvOf (L : List ℕ) (S : List (ℕ × ℕ)) : Bool :=
  (invAllOf L S).all fun x => x.valid && x.mul x == Elt.one && x != Elt.one

@[expose] def repCheckOf (R : List (List (ℕ × ℕ × Bool))) : Bool :=
  (repsOf R).all fun gs => gs.all (fun g => g.valid && g.mul g == Elt.one && g != Elt.one) &&
    gs.all (fun g => gs.all (commutes g)) && decide (elems gs).Nodup

@[expose] def rankCheckOf (R : List (List (ℕ × ℕ × Bool))) : Bool :=
  (repsOf R).all fun gs => (elems gs).length ≤ 16

@[expose] def ffCheckOf (R : List (List (ℕ × ℕ × Bool))) : Bool :=
  (repsOf R).all fun gs => gs.isEmpty || decide ((elems gs).length * (fixPts gs).length < 256) ||
    (inL gs && (elems gs).length == 16)

@[expose] def commCheckOf (R : List (List (ℕ × ℕ × Bool))) : Bool :=
  (repsOf R).all fun gs => decide ((elems gs).length < 4) ||
    decide (8 ≤ (spanList (commPts (elems gs))).length)

@[expose] def centCheckOf (R : List (List (ℕ × ℕ × Bool))) : Bool :=
  (repsOf R).all fun gs => decide ((elems gs).length < 4) || decide (4 * (fixPts gs).length < 256)

@[expose] def axesCheckOf (R : List (List (ℕ × ℕ × Bool))) : Bool :=
  (repsOf R).all fun gs => !inL gs || decide ((elems gs).length < 4) || !constFix (elems gs) ||
    ((elems gs).length == 4 && (elems gs).all fun e => e == Elt.one ||
      ((fixPts₁ [e]).length == 4 && (fixPts₂ [e]).length == 4))

@[expose] def e16CheckOf (R : List (List (ℕ × ℕ × Bool))) : Bool :=
  let E0 := elems ((repsOf R).getD 28 [])
  let E1 := elems ((repsOf R).getD 26 [])
  let E2 := elems ((repsOf R).getD 27 [])
  let S2 := spanList (gam2Pts E2)
  (fixPts ((repsOf R).getD 28 [])).length == 16 && (spanList (gam2Pts E0)).length == 256 &&
    (fixPts ((repsOf R).getD 26 [])).length == 2 && (spanList (gam2Pts E1)).length == 64 &&
    (fixPts ((repsOf R).getD 27 [])).length == 4 && S2.length == 64 &&
    E2.all (fun e => e == Elt.one || S2.any fun w => e.act w != w) &&
    [E1, E2].all fun E => E.any (fun e => !e.b && (fixPts₁ [e]).length == 8) &&
      E.any (fun e => !e.b && e != Elt.one && (fixPts₁ [e]).length != 8) &&
      decide (128 ≤ (spanList (gam3Pts E)).length)

theorem recP_iff (S : List (ℕ × ℕ)) (f : ℕ → ℕ → Bool) :
    List.rec (motive := fun _ => Bool) true
      (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) f p) ih) S = true ↔
      ∀ p ∈ S, f p.1 p.2 = true := by
  induction S with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons p t ih =>
    change andB (f p.1 p.2) _ = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem memS_iff (k : ℕ) (S : List (ℕ × ℕ)) : memS k S = true ↔ ∃ p ∈ S, k = p.1 := by
  induction S with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | cons p t ih =>
    change orB (Nat.beq k p.1) (memS k t) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih, Nat.beq_eq]
    simp

theorem pkMat_zero : pkMat 4 0 = 0 := by
  ext i j
  simp [pkMat]

theorem pkMat_colV_ne : ∀ v < 16, 0 < v → pkMat 4 (colV v) ≠ 0 := by decide +kernel

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hb) h

theorem elems_cons' (g : Elt) (gs : List Elt) :
    elems (g :: gs) = elems gs ++ (elems gs).map (Elt.mul g) := rfl

theorem getD_eq' {α : Type} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem gensK_cons (p : ℕ × ℕ × Bool) (gs : List (ℕ × ℕ × Bool)) :
    gensK (p :: gs) = mkE p.1 p.2.1 (Bool.rec 0 1 p.2.2) :: gensK gs := rfl

theorem canonK_cons (p : ℕ × ℕ × Bool) (gs : List (ℕ × ℕ × Bool)) :
    canonK (p :: gs) = andB (andB (Nat.blt p.1 65536) (Nat.blt p.2.1 65536)) (canonK gs) := rfl

theorem gensK_spec : ∀ gs : List (ℕ × ℕ × Bool), canonK gs = true →
    (gensK gs).map decE = gs.map Elt.ofCodes ∧ ∀ t ∈ gensK gs, Canon t
  | [], _ => ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | p :: gs, h => by
    rw [canonK_cons, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq,
      Nat.blt_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := gensK_spec gs h3
    have hb : (Bool.rec 0 1 p.2.2 : ℕ) < 2 := by cases p.2.2 <;> decide
    refine ⟨?_, ?_⟩
    · rw [gensK_cons, List.map_cons, List.map_cons, ih1, decE_mkE h1 h2 hb]
      congr 1
      obtain ⟨a, ai, b⟩ := p
      cases b <;> rfl
    · intro t ht
      rw [gensK_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact canon_mkE h1 h2 hb
      · exact ih2 t ht

theorem elemsK_spec : ∀ G : List ℕ, (elemsK G).map decE = elems (G.map decE) ∧
    ∀ t ∈ elemsK G, Canon t
  | [] => ⟨by rw [elemsK, List.map_cons, List.map_nil, decE_oneE]; rfl,
      fun t ht => by
        rw [elemsK, List.mem_singleton] at ht
        exact ht ▸ canon_oneE⟩
  | g :: G => by
    obtain ⟨ih1, ih2⟩ := elemsK_spec G
    have e : elemsK (g :: G) = appL (elemsK G) (mapL (mulE g) (elemsK G)) := rfl
    rw [e, appL_eq, mapL_eq]
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, elems_cons', List.map_append, ih1, List.map_map, ← ih1, List.map_map]
      congr 1
      exact List.map_congr_left fun t _ => decE_mulE g t
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact ih2 t ht
      · obtain ⟨s, -, rfl⟩ := List.mem_map.mp ht
        exact canon_mulE g s

theorem decE_eq_iff {s t : ℕ} (hs : Canon s) (ht : Canon t) : decE s = decE t ↔ s = t :=
  ⟨decE_injective hs ht, fun h => h ▸ rfl⟩

theorem repOK_sound {gs : List (ℕ × ℕ × Bool)} (hc : canonK gs = true) {X : List ℕ}
    (h : repOK (gensK gs) X = true) :
    let es := gs.map Elt.ofCodes
    (∀ g ∈ es, g.valid = true ∧ g.mul g = Elt.one ∧ g ≠ Elt.one) ∧
      (∀ g ∈ es, ∀ h ∈ es, g.mul h = h.mul g) ∧ (elems es).Nodup ∧
      X.map eltX = elemsK (gensK gs) := by
  obtain ⟨hG1, hG2⟩ := gensK_spec gs hc
  unfold repOK at h
  simp only [andB_eq, Bool.and_eq_true, allL_iff, eqLN_iff, nodupN_iff, mapL_eq] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  intro es
  have hes : es = (gensK gs).map decE := hG1.symm
  refine ⟨fun g hg => ?_, fun g hg h hh => ?_, ?_, h3⟩
  · rw [hes] at hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    have h5 := h1 t ht
    unfold invoE at h5
    simp only [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h5
    obtain ⟨hv, hsq, hne⟩ := h5
    refine ⟨by rw [← validE_iff]; exact hv, by rw [← decE_mulE, hsq, decE_oneE], fun h6 => ?_⟩
    rw [← decE_oneE, decE_eq_iff (hG2 t ht) canon_oneE] at h6
    rw [h6] at hne
    exact absurd (Nat.beq_eq.mpr rfl) (by rw [hne]; decide)
  · rw [hes] at hg hh
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hh
    have h5 := h2 t ht u hu
    rw [Nat.beq_eq] at h5
    rw [← decE_mulE, ← decE_mulE, h5]
  · rw [hes, ← (elemsK_spec (gensK gs)).1]
    rw [h3] at h4
    exact h4.map_on fun s hs t ht hst =>
      decE_injective ((elemsK_spec _).2 s hs) ((elemsK_spec _).2 t ht) hst

theorem repsK_length (R : List (List (ℕ × ℕ × Bool))) : (repsK R).length = R.length := by
  induction R with
  | nil => rfl
  | cons gs R ih =>
    change (gensK gs :: repsK R).length = _
    rw [List.length_cons, ih, List.length_cons]

theorem repsK_getD (R : List (List (ℕ × ℕ × Bool))) (i : ℕ) :
    (repsK R).getD i [] = gensK (R.getD i []) := by
  induction R generalizing i with
  | nil => cases i <;> rfl
  | cons gs R ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem canonR_iff (R : List (List (ℕ × ℕ × Bool))) :
    canonR R = true ↔ ∀ gs ∈ R, canonK gs = true := by
  induction R with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons gs R ih =>
    change andB (canonK gs) (canonR R) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem pin_spec {R : List (List (ℕ × ℕ × Bool))} {RG RX : List (List ℕ)}
    (h : pinK R RG RX = true) :
    RG = repsK R ∧ RX.length = R.length ∧ ∀ i < R.length,
      canonK (R.getD i []) = true ∧ repOK (gensK (R.getD i [])) (RX.getD i []) = true := by
  unfold pinK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [eqLL_iff] at h2
  subst h2
  rw [Nat.beq_eq, lenLL_eq, lenLL_eq, repsK_length] at h3
  rw [allN_iff, lenLL_eq, repsK_length] at h4
  refine ⟨rfl, h3, fun i hi => ⟨?_, ?_⟩⟩
  · refine (canonR_iff R).mp h1 _ ?_
    rw [getD_eq' _ _ hi]
    exact List.getElem_mem hi
  · have h5 := h4 i hi
    rwa [nthK_eq, nthK_eq, repsK_getD] at h5

theorem invAllK_spec {L : List ℕ} {S : List (ℕ × ℕ)} (h : checkInvK L S = true) :
    (invAllK L S).map decE = invAllOf L S ∧ ∀ t ∈ invAllK L S, Canon t := by
  unfold checkInvK at h
  rw [andB_eq, Bool.and_eq_true, allL_iff] at h
  obtain ⟨hL, hS⟩ := h
  replace hS := (recP_iff S (fun a ai => andB (andB (Nat.blt a (nat_lit 65536))
    (Nat.blt ai (nat_lit 65536))) (andB (andB (Nat.beq (mul4 a ai) one4) (Nat.beq (mul4 ai a) one4))
      (andB (Nat.beq (mul4 a (tr4 ai)) one4) (Nat.beq (mul4 (tr4 a) ai) one4))))).mp hS
  have hSL : ∀ S' : List (ℕ × ℕ), (∀ p ∈ S', p.1 < 2 ^ 16 ∧ p.2 < 2 ^ 16) →
      (List.rec (motive := fun _ => List ℕ) List.nil (fun p _ ih => List.cons
        (Prod.rec (motive := fun _ => ℕ) (fun a ai => mkE a ai (nat_lit 1)) p) ih) S').map decE =
        S'.map (fun p => (⟨Mat.ofCode p.1, Mat.ofCode p.2, true⟩ : Elt)) ∧
      ∀ t ∈ (List.rec (motive := fun _ => List ℕ) List.nil (fun p _ ih => List.cons
        (Prod.rec (motive := fun _ => ℕ) (fun a ai => mkE a ai (nat_lit 1)) p) ih) S'), Canon t := by
    intro S' hS'
    induction S' with
    | nil => exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons p S' ih =>
      obtain ⟨ih1, ih2⟩ := ih fun q hq => hS' q (List.mem_cons_of_mem _ hq)
      obtain ⟨h1, h2⟩ := hS' p List.mem_cons_self
      refine ⟨?_, ?_⟩
      · change decE (mkE p.1 p.2 1) :: _ = _
        rw [ih1, decE_mkE h1 h2 (by norm_num), List.map_cons]
        rfl
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact canon_mkE h1 h2 (by norm_num)
        · exact ih2 t ht
  have hS2 : ∀ p ∈ S, p.1 < 2 ^ 16 ∧ p.2 < 2 ^ 16 := fun p hp => by
    have h1 := hS p hp
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h1
    exact ⟨h1.1.1, h1.1.2⟩
  have hL2 : ∀ k ∈ L, k < 2 ^ 16 := fun k hk => by
    have h1 := hL k hk
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h1
    exact h1.1
  obtain ⟨hs1, hs2⟩ := hSL S hS2
  unfold invAllK invAllOf
  rw [appL_eq, mapL_eq, List.map_append, List.map_map, hs1]
  refine ⟨?_, ?_⟩
  · congr 1
    exact List.map_congr_left fun k hk => by
      rw [Function.comp_apply, decE_mkE (hL2 k hk) (hL2 k hk) (by norm_num)]
      rfl
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
      exact canon_mkE (hL2 k hk) (hL2 k hk) (by norm_num)
    · exact hs2 t ht

theorem memX_iff (x : ℕ) (X : List ℕ) : memX x X = true ↔ x ∈ X.map eltX := by
  induction X with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons v X ih =>
    change orB (Nat.beq x (eltX v)) (memX x X) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih, Nat.beq_eq, List.map_cons, List.mem_cons]

theorem fa_mulE (s t : ℕ) : fa (mulE s t) = aMul s t := by
  unfold mulE aMul
  simp only [letN_eq]
  cases Nat.beq (fb s) 1
  · exact fa_mkE (mul4_lt _ _) _ _
  · exact fa_mkE (mul4_lt _ _) _ _

theorem closRow_cons (G X : List ℕ) (RX : List (List ℕ)) (x : ℕ) (I T : List ℕ) :
    closRowK G X RX (x :: I) T = Bool.rec (motive := fun _ => Bool) (closRowK G X RX I T)
      (List.rec (motive := fun _ => Bool) false
        (fun ent rest _ => andB (entK G X RX x ent) (closRowK G X RX I rest)) T)
      (liveK G X x) := rfl

theorem closRow_walk {G X : List ℕ} {RX : List (List ℕ)} :
    ∀ (I T : List ℕ), closRowK G X RX I T = true → ∀ x ∈ I, liveK G X x = true →
      ∃ ent, entK G X RX x ent = true
  | [], _, _, x, hx, _ => absurd hx List.not_mem_nil
  | z :: I, T, h, x, hx, hl => by
    rw [closRow_cons] at h
    cases hz : liveK G X z
    · rw [hz] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hz] at hl
        exact absurd hl Bool.false_ne_true
      · exact closRow_walk I T h x hx hl
    · rw [hz] at h
      cases T with
      | nil => exact absurd h Bool.false_ne_true
      | cons ent rest =>
        change andB (entK G X RX z ent) (closRowK G X RX I rest) = true at h
        rw [andB_eq, Bool.and_eq_true] at h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨ent, h.1⟩
        · exact closRow_walk I rest h.2 x hx hl

theorem repsOf_getD (R : List (List (ℕ × ℕ × Bool))) (i : ℕ) :
    (repsOf R).getD i [] = (R.getD i []).map Elt.ofCodes := by
  unfold repsOf
  induction R generalizing i with
  | nil => cases i <;> rfl
  | cons gs R ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem elems_length (es : List Elt) : (elems es).length = 2 ^ es.length := by
  induction es with
  | nil => rfl
  | cons g es ih =>
    rw [elems_cons', List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    ring

theorem walk_sound (L : List ℕ) (S : List (ℕ × ℕ))
    (h : ∀ c < 16, walkK L S (Nat.mul 4096 c) 4096 = true) :
    (∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.of A * Matrix.of A = 1 → Matrix.of A ≠ 1 →
      ∃ k ∈ L, (Mat.ofCode k).toMatrix = Matrix.of A) ∧
    (∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.transpose (Matrix.of A) = Matrix.of A →
      (Matrix.of A).det ≠ 0 → ∃ p ∈ S, (Mat.ofCode p.1).toMatrix = Matrix.of A) := by
  have hstep : ∀ k < 2 ^ 16, stepK L S k = true := by
    intro k hk
    have h1 := h (k / 4096) (by omega)
    unfold walkK at h1
    rw [allN_iff] at h1
    have h2 := h1 (k % 4096) (Nat.mod_lt _ (by norm_num))
    rw [letB_eq] at h2
    have e : Nat.add (Nat.mul 4096 (k / 4096)) (k % 4096) = k := by
      change 4096 * (k / 4096) + k % 4096 = k
      omega
    rwa [e] at h2
  refine ⟨fun A h1 h2 => ?_, fun A h1 h2 => ?_⟩
  · obtain ⟨k, hk, hkA⟩ := exists_code A
    have hs := hstep k hk
    unfold stepK at hs
    rw [andB_eq, Bool.and_eq_true] at hs
    have hsq : Nat.beq (mul4 k k) one4 = true := by
      rw [Nat.beq_eq, ← pkMat_eq_iff (mul4_lt _ _) one4_lt, pkMat_mul4, pkMat_one4, hkA]
      exact h1
    have hne : Nat.beq k one4 = false := beq_false_of_ne fun h3 => h2 (by rw [← hkA, h3, pkMat_one4])
    have hs1 := hs.1
    rw [hsq, hne] at hs1
    have hm : memN k L = true := hs1
    exact ⟨k, (memN_iff k L).mp hm, by rw [toMatrix_ofCode, hkA]⟩
  · obtain ⟨k, hk, hkA⟩ := exists_code A
    have hs := hstep k hk
    unfold stepK at hs
    rw [andB_eq, Bool.and_eq_true] at hs
    have htr : Nat.beq (tr4 k) k = true := by
      rw [Nat.beq_eq, ← pkMat_eq_iff (tr4_lt hk) hk, pkMat_tr4, hkA]
      exact h1
    have hs2 := hs.2
    rw [htr] at hs2
    have ho : orB (memS k S) (kerV k) = true := hs2
    rw [orB_eq, Bool.or_eq_true] at ho
    rcases ho with ho | ho
    · obtain ⟨p, hp, rfl⟩ := (memS_iff k S).mp ho
      exact ⟨p, hp, by rw [toMatrix_ofCode, hkA]⟩
    · exfalso
      unfold kerV at ho
      obtain ⟨v, hv, hv2⟩ := (anyN_iff _ _).mp ho
      rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hv2
      have hM : Matrix.of A * pkMat 4 (colV v) = 0 := by
        rw [← hkA, ← pkMat_mul4, hv2.2, pkMat_zero]
      have hd : (Matrix.of A).det = 1 := by
        revert h2
        generalize (Matrix.of A).det = d
        revert d
        decide
      have hu : IsUnit (Matrix.of A).det := by
        rw [hd]
        exact isUnit_one
      have h3 := Matrix.nonsing_inv_mul_cancel_left (Matrix.of A) (pkMat 4 (colV v)) hu
      rw [hM, Matrix.mul_zero] at h3
      exact pkMat_colV_ne v hv hv2.1 h3.symm

theorem checkInv_sound (L : List ℕ) (S : List (ℕ × ℕ)) (h : checkInvK L S = true) :
    checkInvOf L S = true := by
  unfold checkInvK at h
  rw [andB_eq, Bool.and_eq_true, allL_iff] at h
  obtain ⟨hL, hS⟩ := h
  replace hS := (recP_iff S (fun a ai => andB (andB (Nat.blt a (nat_lit 65536))
    (Nat.blt ai (nat_lit 65536))) (andB (andB (Nat.beq (mul4 a ai) one4) (Nat.beq (mul4 ai a) one4))
      (andB (Nat.beq (mul4 a (tr4 ai)) one4) (Nat.beq (mul4 (tr4 a) ai) one4))))).mp hS
  have one_ofCode : Mat.one = Mat.ofCode one4 := ofCode_one4.symm
  have key : ∀ {x y : ℕ}, Nat.beq (mul4 x y) one4 = true → Mat.mul (Mat.ofCode x) (Mat.ofCode y) =
      Mat.one := fun hxy => by rw [← ofCode_mul4, Nat.beq_eq.mp hxy, ofCode_one4]
  have keyM : ∀ {x y : ℕ}, Nat.beq (mul4 x y) one4 = true →
      (Mat.ofCode x).toMatrix * (Mat.ofCode y).toMatrix = 1 := fun hxy => by
    rw [toMatrix_ofCode, toMatrix_ofCode, ← pkMat_mul4, Nat.beq_eq.mp hxy, pkMat_one4]
  unfold checkInvOf invAllOf
  rw [List.all_eq_true]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have h1 := hL k hk
    rw [andB_eq, andB_eq, notB_eq, Bool.and_eq_true, Bool.and_eq_true] at h1
    obtain ⟨hk16, hsq, hne⟩ := h1
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold Elt.valid
      rw [keyM hsq]
      rfl
    · rw [beq_iff_eq]
      unfold Elt.mul Elt.one
      simp only [Bool.false_eq_true, if_false, key hsq, Bool.xor_self]
    · rw [bne_iff_ne]
      intro h3
      have h4 : Mat.ofCode k = Mat.ofCode one4 := by rw [← one_ofCode]; exact congrArg Elt.a h3
      have h5 := ofCode_injective (Nat.blt_eq.mp hk16) one4_lt h4
      rw [h5] at hne
      exact absurd hne (by decide)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have h1 := hS p hp
    simp only [andB_eq, Bool.and_eq_true] at h1
    obtain ⟨-, ⟨h2, h3⟩, h4, h5⟩ := h1
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold Elt.valid
      rw [keyM h2, keyM h3]
      rfl
    · rw [beq_iff_eq]
      unfold Elt.mul Elt.one
      simp only [if_true, ← ofCode_tr4, key h4, key h5, Bool.xor_self]
    · rw [bne_iff_ne]
      intro h3
      exact Bool.noConfusion (congrArg Elt.b h3)

theorem rep_sound (R : List (List (ℕ × ℕ × Bool))) (RG RX : List (List ℕ))
    (h : pinK R RG RX = true) : repCheckOf R = true := by
  obtain ⟨-, -, hR⟩ := pin_spec h
  unfold repCheckOf repsOf
  rw [List.all_eq_true]
  intro es hes
  obtain ⟨gs, hgs, rfl⟩ := List.mem_map.mp hes
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgs
  have hg : R.getD i [] = R[i] := getD_eq' _ _ hi
  obtain ⟨hc, hok⟩ := hR i hi
  rw [hg] at hc hok
  obtain ⟨h1, h2, h3, -⟩ := repOK_sound hc hok
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, commutes]
  exact ⟨⟨fun g hg => ⟨⟨(h1 g hg).1, (h1 g hg).2.1⟩, (h1 g hg).2.2⟩, h2⟩, h3⟩

theorem clos_sound (L : List ℕ) (S : List (ℕ × ℕ)) (I : List ℕ) (R : List (List (ℕ × ℕ × Bool)))
    (RG RX T : List (List ℕ)) (hck : checkInvK L S = true)
    (hI : CFSG.KC.Misc.eqLN I (invAllK L S) = true) (hpin : pinK R RG RX = true)
    (hrow : ∀ i < R.length, closRowK (nthK RG i) (nthK RX i) RX I (nthK T i) = true)
    {i : ℕ} (hi : i < (repsOf R).length) {y : Elt} (hy : y ∈ invAllOf L S)
    (hc : ((repsOf R).getD i []).all (commutes y) = true)
    (hn : (elems ((repsOf R).getD i [])).contains y = false) :
    ∃ j < (repsOf R).length, ∃ c : Elt, c.valid = true ∧
      ((repsOf R).getD j []).length = ((repsOf R).getD i []).length + 1 ∧
      ∀ g ∈ (repsOf R).getD i [] ++ [y], (c.mul g).mul c.inv ∈ elems ((repsOf R).getD j []) := by
  obtain ⟨rfl, hRX, hR⟩ := pin_spec hpin
  obtain ⟨hI1, hI2⟩ := invAllK_spec hck
  rw [eqLN_iff] at hI
  subst hI
  have hlenR : (repsOf R).length = R.length := List.length_map _
  rw [hlenR] at hi ⊢
  rw [repsOf_getD] at hc hn ⊢
  rw [← hI1] at hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have hxc := hI2 x hx
  obtain ⟨hci, hoki⟩ := hR i hi
  obtain ⟨-, -, -, hXi⟩ := repOK_sound hci hoki
  obtain ⟨hG1, hG2⟩ := gensK_spec _ hci
  set gs := R.getD i [] with hgs
  set G := gensK gs with hG
  set X := RX.getD i [] with hX
  have hrow := hrow i hi
  rw [nthK_eq, nthK_eq, nthK_eq, repsK_getD, ← hgs] at hrow
  have hlive : liveK G X x = true := by
    unfold liveK
    rw [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true', allL_iff]
    refine ⟨fun g hg => ?_, ?_⟩
    · have hgm : decE g ∈ gs.map Elt.ofCodes := hG1 ▸ List.mem_map_of_mem hg
      rw [List.all_eq_true] at hc
      have h1 := hc _ hgm
      simp only [commutes, beq_iff_eq] at h1
      rw [← decE_mulE, ← decE_mulE, decE_eq_iff (canon_mulE _ _) (canon_mulE _ _)] at h1
      unfold commE
      rw [Nat.beq_eq, ← fa_mulE, ← fa_mulE, h1]
    · cases hm : memX x X
      · rfl
      · exfalso
        rw [memX_iff, hXi] at hm
        have h1 : decE x ∈ elems (gs.map Elt.ofCodes) := by
          rw [← hG1, ← (elemsK_spec G).1]
          exact List.mem_map_of_mem hm
        rw [← List.contains_iff_mem, hn] at h1
        exact Bool.noConfusion h1
  obtain ⟨ent, hent⟩ := closRow_walk _ _ hrow x hx hlive
  unfold entK at hent
  simp only [letB_eq, andB_eq, Bool.and_eq_true, allL_iff, nthK_eq, Nat.beq_eq] at hent
  obtain ⟨hv, hlen, hmem⟩ := hent
  set j := Nat.land ent 255
  set c := Nat.shiftRight ent 8
  have hXlen : X.length = 2 ^ gs.length := by
    rw [← List.length_map (f := eltX), hXi, ← List.length_map (f := decE), (elemsK_spec G).1, hG1,
      elems_length, List.length_map]
  have hj : j < R.length := by
    by_contra hj
    have hd : RX.getD j [] = [] := by
      simp [List.getD_eq_getElem?_getD, show RX.length ≤ j by omega]
    rw [hd, lenK, lenN_eq, lenK, lenN_eq, hXlen] at hlen
    have := Nat.two_pow_pos gs.length
    change 0 = 2 * 2 ^ gs.length at hlen
    omega
  obtain ⟨hcj, hokj⟩ := hR j hj
  obtain ⟨-, -, -, hXj⟩ := repOK_sound hcj hokj
  obtain ⟨hGj1, -⟩ := gensK_spec _ hcj
  have hXjlen : (RX.getD j []).length = 2 ^ (R.getD j []).length := by
    rw [← List.length_map (f := eltX), hXj, ← List.length_map (f := decE), (elemsK_spec _).1, hGj1,
      elems_length, List.length_map]
  refine ⟨j, hj, decE c, by rw [← validE_iff]; exact hv, ?_, ?_⟩
  · rw [lenK, lenN_eq, lenK, lenN_eq, hXjlen, hXlen] at hlen
    change 2 ^ (R.getD j []).length = 2 * 2 ^ gs.length at hlen
    rw [← pow_succ'] at hlen
    rw [repsOf_getD, List.length_map, List.length_map]
    exact Nat.pow_right_injective (le_refl 2) hlen
  · intro g hg
    have hg' : ∃ g0 ∈ x :: G, decE g0 = g := by
      rcases List.mem_append.mp hg with hg | hg
      · rw [← hG1] at hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact ⟨g0, List.mem_cons_of_mem _ hg0, rfl⟩
      · rw [List.mem_singleton.mp hg]
        exact ⟨x, List.mem_cons_self, rfl⟩
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have h1 := hmem g0 hg0
    rw [memX_iff, hXj] at h1
    have h2 := List.mem_map_of_mem (f := decE) h1
    rw [(elemsK_spec _).1, hGj1, decE_mulE, decE_mulE, decE_invE] at h2
    rw [repsOf_getD]
    exact h2

theorem rank_sound (R : List (List (ℕ × ℕ × Bool))) (RG RX : List (List ℕ))
    (hpin : pinK R RG RX = true) (h : rankK RG = true) : rankCheckOf R = true := by
  obtain ⟨rfl, -, -⟩ := pin_spec hpin
  have hlen : ∀ es : List Elt, (elems es).length = 2 ^ es.length := by
    intro es
    induction es with
    | nil => rfl
    | cons g es ih =>
      rw [elems_cons', List.length_append, List.length_map, ih, List.length_cons, pow_succ]
      ring
  have hg : ∀ gs : List (ℕ × ℕ × Bool), (gensK gs).length = gs.length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons p gs ih => rw [gensK_cons, List.length_cons, ih, List.length_cons]
  have hall : ∀ G ∈ repsK R, G.length ≤ 4 := by
    have h1 : ∀ L : List (List ℕ), allLL L (fun G => Nat.ble (lenN G) 4) = true →
        ∀ G ∈ L, G.length ≤ 4 := by
      intro L
      induction L with
      | nil => exact fun _ _ h => absurd h List.not_mem_nil
      | cons G L ih =>
        intro hL
        change andB (Nat.ble (lenN G) 4) (allLL L _) = true at hL
        rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, lenN_eq] at hL
        exact List.forall_mem_cons.mpr ⟨hL.1, ih hL.2⟩
    exact h1 _ h
  unfold rankCheckOf repsOf
  rw [List.all_eq_true]
  intro es hes
  obtain ⟨gs, hgs, rfl⟩ := List.mem_map.mp hes
  have hmem : ∀ R' : List (List (ℕ × ℕ × Bool)), gs ∈ R' → gensK gs ∈ repsK R' := by
    intro R' hR'
    induction R' with
    | nil => exact absurd hR' List.not_mem_nil
    | cons g R' ih =>
      rcases List.mem_cons.mp hR' with rfl | hR'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hR')
  have h2 := hmem R hgs
  have h3 := hall _ h2
  rw [hg] at h3
  rw [decide_eq_true_iff, hlen, List.length_map]
  calc 2 ^ gs.length ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h3
    _ = 16 := by norm_num

theorem rep_pack {R : List (List (ℕ × ℕ × Bool))} {RG RX : List (List ℕ)}
    (hpin : pinK R RG RX = true) {i : ℕ} (hi : i < R.length) :
    ((nthK RX i).map eltX).map decE = elems ((R.getD i []).map Elt.ofCodes) ∧
    (∀ v ∈ nthK RX i, Canon (eltX v) ∧ maskX v = fixK (eltX v)) ∧
    (nthK RG i).map decE = (R.getD i []).map Elt.ofCodes := by
  obtain ⟨rfl, -, hR⟩ := pin_spec hpin
  obtain ⟨hc, hok⟩ := hR i hi
  obtain ⟨-, -, -, hX⟩ := repOK_sound hc hok
  obtain ⟨hG1, -⟩ := gensK_spec _ hc
  have hok' := hok
  unfold repOK at hok'
  simp only [andB_eq, Bool.and_eq_true, allL_iff] at hok'
  obtain ⟨-, -, -, -, hm⟩ := hok'
  rw [nthK_eq, nthK_eq, repsK_getD]
  refine ⟨by rw [hX, (elemsK_spec _).1, hG1], fun v hv => ⟨?_, Nat.beq_eq.mp (hm v hv)⟩, hG1⟩
  refine (elemsK_spec (gensK (R.getD i []))).2 _ ?_
  rw [← hX]
  exact List.mem_map_of_mem hv

theorem one_iff {t : ℕ} (ht : Canon t) : (decE t == Elt.one) = Nat.beq t oneE := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, ← decE_oneE, decE_eq_iff ht canon_oneE]

theorem eq_iff' {s t : ℕ} (hs : Canon s) (ht : Canon t) : (decE s == decE t) = Nat.beq s t := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, decE_eq_iff hs ht]

theorem notb_decE (t : ℕ) : (!(decE t).b) = Nat.beq (fb t) 0 := by
  change (!(Nat.beq (fb t) 1)) = _
  rcases lt_two (fb_lt t) with h | h <;> rw [h] <;> rfl

theorem allL_eq_all (l : List ℕ) (f : ℕ → Bool) : allL l f = l.all f := by
  rw [Bool.eq_iff_iff, allL_iff, List.all_eq_true]

theorem inL_eq {G : List ℕ} {es : List Elt} (h : G.map decE = es) : inL es = inLK G := by
  rw [inL, inLK, ← h, List.all_map, allL_eq_all]
  exact all_congr' fun g _ => notb_decE g

theorem mask1_eq {x y : ℕ} (h : fixPts₁ [decE x] = fixPts₁ [decE y]) :
    Nat.land (fixK x) w1M = Nat.land (fixK y) w1M := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [land_eq, land_eq, Nat.testBit_and, Nat.testBit_and, testBit_w1M]
  by_cases hn : n < 16
  · have e1 := mem_fixPts₁ x (show n < 256 by omega)
    have e2 := mem_fixPts₁ y (show n < 256 by omega)
    rw [h, e2] at e1
    have : (fixK x).testBit n = (fixK y).testBit n := by
      rw [Bool.eq_iff_iff]
      simpa [hn] using e1.symm
    rw [this]
  · simp [hn]

theorem mask2_eq {x y : ℕ} (h : fixPts₂ [decE x] = fixPts₂ [decE y]) :
    Nat.land (fixK x) w2M = Nat.land (fixK y) w2M := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [land_eq, land_eq, Nat.testBit_and, Nat.testBit_and, testBit_w2M]
  by_cases hn : n < 256 ∧ n % 16 = 0
  · have e1 := mem_fixPts₂ x hn.1
    have e2 := mem_fixPts₂ y hn.1
    rw [h, e2] at e1
    have : (fixK x).testBit n = (fixK y).testBit n := by
      rw [Bool.eq_iff_iff]
      simpa [hn.2] using e1.symm
    rw [this]
  · by_cases h1 : n < 256
    · have h2 : ¬ n % 16 = 0 := fun h2 => hn ⟨h1, h2⟩
      simp [h2]
    · simp [h1]

theorem constFix_imp {X : List ℕ} (hc : ∀ v ∈ X, Canon (eltX v) ∧ maskX v = fixK (eltX v))
    (h : constFix ((X.map eltX).map decE) = true) : constFixK X = true := by
  unfold constFix at h
  rw [List.map_map, List.all_map, List.all_eq_true] at h
  unfold constFixK
  rw [allL_iff]
  intro v hv
  rw [allL_iff]
  intro u hu
  have h1 := h v hv
  rw [Function.comp_apply, List.all_map, List.all_eq_true] at h1
  have h2 := h1 u hu
  obtain ⟨hcv, hmv⟩ := hc v hv
  obtain ⟨hcu, hmu⟩ := hc u hu
  simp only [Function.comp_apply, one_iff hcv, one_iff hcu, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h2
  simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true]
  rcases h2 with (h2 | h2) | ⟨h3, h4⟩
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [Nat.beq_eq, hmv, hmu]
      exact mask1_eq h3
    · rw [Nat.beq_eq, hmv, hmu]
      exact mask2_eq h4

theorem mem_ptsOf {U u : ℕ} (hu : u < 256) : ptOfCode u ∈ ptsOf U ↔ U.testBit u = true :=
  ⟨fun ⟨w, hw, h1, h2⟩ => (ptOfCode_eq_iff hw hu).mp h2 ▸ h1, fun h => ⟨u, hu, h, rfl⟩⟩

theorem mem_fixPts_pair {x y u : ℕ} (hu : u < 256) :
    ptOfCode u ∈ fixPts [decE x, decE y] ↔ ((fixK x).testBit u && (fixK y).testBit u) = true := by
  have e : [decE x, decE y] = [x, y].map decE := rfl
  rw [e, mem_fixPts hu, testBit_fixAllK _ hu]
  simp

theorem mem_fixPts_one {x u : ℕ} (hu : u < 256) :
    ptOfCode u ∈ fixPts [decE x] ↔ (fixK x).testBit u = true := by
  have e : [decE x] = [x].map decE := rfl
  rw [e, mem_fixPts hu, testBit_fixAllK _ hu]
  simp

theorem mem_gam2 {X : List ℕ} (hc : ∀ v ∈ X, Canon (eltX v) ∧ maskX v = fixK (eltX v))
    {u : ℕ} (hu : u < 256) :
    ptOfCode u ∈ gam2Pts ((X.map eltX).map decE) ↔ (gam2K X).testBit u = true := by
  rw [testBit_gam2K, List.any_eq_true, List.map_map]
  unfold gam2Pts
  rw [List.flatMap_map]
  simp only [List.mem_flatMap, List.flatMap_map, List.any_eq_true]
  refine exists_congr fun v => and_congr_right fun hv => exists_congr fun w =>
    and_congr_right fun hw => ?_
  obtain ⟨hcv, hmv⟩ := hc v hv
  obtain ⟨hcw, hmw⟩ := hc w hw
  rw [Function.comp_apply, Function.comp_apply, hmv, hmw]
  have hcond : (decE (eltX v) != Elt.one && decE (eltX w) != Elt.one &&
      decE (eltX v) != decE (eltX w)) = (!(Nat.beq (eltX v) oneE) &&
        (!(Nat.beq (eltX w) oneE) && !(Nat.beq (eltX v) (eltX w)))) := by
    simp only [bne, one_iff hcv, one_iff hcw, eq_iff' hcv hcw, Bool.and_assoc]
  rw [hcond]
  cases (!(Nat.beq (eltX v) oneE) && (!(Nat.beq (eltX w) oneE) && !(Nat.beq (eltX v) (eltX w))))
  · simp
  · rw [if_pos rfl, mem_fixPts_pair hu, Bool.true_and]

theorem mem_gam3 {X : List ℕ} (hc : ∀ v ∈ X, Canon (eltX v) ∧ maskX v = fixK (eltX v))
    {u : ℕ} (hu : u < 256) :
    ptOfCode u ∈ gam3Pts ((X.map eltX).map decE) ↔ (gam3K X).testBit u = true := by
  rw [testBit_gam3K, List.any_eq_true, List.map_map]
  unfold gam3Pts
  rw [List.flatMap_map]
  simp only [List.mem_flatMap]
  refine exists_congr fun v => and_congr_right fun hv => ?_
  obtain ⟨hcv, hmv⟩ := hc v hv
  rw [Function.comp_apply, hmv]
  have hcond : (decE (eltX v) != Elt.one) = !(Nat.beq (eltX v) oneE) := by
    simp only [bne, one_iff hcv]
  rw [hcond]
  cases (!(Nat.beq (eltX v) oneE))
  · simp
  · rw [if_pos rfl, mem_fixPts_one hu, Bool.true_and]

theorem closure_eq_of_mem {L : List Pt} {U : ℕ}
    (h : ∀ u < 256, ptOfCode u ∈ L ↔ U.testBit u = true) :
    Subgroup.closure {y | y ∈ L} = Subgroup.closure (ptsOf U) := by
  congr 1
  ext p
  obtain ⟨u, hu, rfl⟩ := exists_code_pt p
  rw [Set.mem_setOf_eq, mem_ptsOf hu, h u hu]

theorem span_gam2 {X : List ℕ} (hc : ∀ v ∈ X, Canon (eltX v) ∧ maskX v = fixK (eltX v)) :
    (spanList (gam2Pts ((X.map eltX).map decE))).length = pop256 (spanM (gam2K X)) :=
  spanList_length (closure_eq_of_mem fun _ hu => mem_gam2 hc hu) (isMask_spanM _)

theorem span_gam3 {X : List ℕ} (hc : ∀ v ∈ X, Canon (eltX v) ∧ maskX v = fixK (eltX v)) :
    (spanList (gam3Pts ((X.map eltX).map decE))).length = pop256 (spanM (gam3K X)) :=
  spanList_length (closure_eq_of_mem fun _ hu => mem_gam3 hc hu) (isMask_spanM _)

theorem lenK_eq {X : List ℕ} {E : List Elt} (h : (X.map eltX).map decE = E) : lenK X = E.length := by
  rw [lenK, lenN_eq, ← h, List.length_map, List.length_map]

theorem invar_one {X G : List ℕ} {es : List Elt} (hE : (X.map eltX).map decE = elems es)
    (hc : ∀ v ∈ X, Canon (eltX v) ∧ maskX v = fixK (eltX v)) (hG : G.map decE = es)
    (h1 : ffK G X = true) (h2 : commK X = true) (h3 : centK G X = true) (h4 : axesK G X = true) :
    (es.isEmpty || decide ((elems es).length * (fixPts es).length < 256) ||
      (inL es && (elems es).length == 16)) = true ∧
    (decide ((elems es).length < 4) ||
      decide (8 ≤ (spanList (commPts (elems es))).length)) = true ∧
    (decide ((elems es).length < 4) || decide (4 * (fixPts es).length < 256)) = true ∧
    (!inL es || decide ((elems es).length < 4) || !constFix (elems es) ||
      ((elems es).length == 4 && (elems es).all fun e => e == Elt.one ||
        ((fixPts₁ [e]).length == 4 && (fixPts₂ [e]).length == 4))) = true := by
  have hlen := lenK_eq hE
  have hfix : (fixPts es).length = pop256 (fixAllK G) := by
    rw [← hG]
    exact fixPts_length G
  have hinL := inL_eq hG
  have hGlen : lenN G = es.length := by rw [lenN_eq, ← hG, List.length_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ffK at h1
    simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h1
    rw [hlen, hGlen, ← hfix, ← hinL] at h1
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.isEmpty_iff, ← List.length_eq_zero_iff]
    rcases h1 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · unfold commK at h2
    simp only [orB_eq, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h2
    have hs : (spanList (commPts (elems es))).length = pop256 (spanCols X) :=
      spanList_length (by rw [← hE]; exact closure_commPts X) (isMask_spanCols X)
    rw [hlen, ← hs] at h2
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact h2
  · unfold centK at h3
    simp only [orB_eq, Bool.or_eq_true, Nat.blt_eq] at h3
    rw [hlen, ← hfix] at h3
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact h3
  · unfold axesK at h4
    simp only [orB_eq, andB_eq, notB_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq, Bool.not_eq_true'] at h4
    rw [hlen, ← hinL] at h4
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true']
    rcases h4 with h4 | h4 | h4 | ⟨h5, h6⟩
    · exact Or.inl (Or.inl (Or.inl h4))
    · exact Or.inl (Or.inl (Or.inr h4))
    · refine Or.inl (Or.inr ?_)
      cases hcf : constFix (elems es)
      · rfl
      · exfalso
        rw [← hE] at hcf
        rw [constFix_imp hc hcf] at h4
        exact Bool.noConfusion h4
    · refine Or.inr ⟨h5, ?_⟩
      rw [← hE, List.map_map, List.all_map, List.all_eq_true]
      rw [allL_iff] at h6
      intro v hv
      obtain ⟨hcv, hmv⟩ := hc v hv
      have h7 := h6 v hv
      simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h7
      simp only [Function.comp_apply, one_iff hcv, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        Nat.beq_eq, fixPts₁_length, fixPts₂_length, ← hmv]
      exact h7

theorem invar_sound (R : List (List (ℕ × ℕ × Bool))) (RG RX : List (List ℕ))
    (hpin : pinK R RG RX = true) (h : invarK RG RX = true) :
    ffCheckOf R = true ∧ commCheckOf R = true ∧ centCheckOf R = true ∧ axesCheckOf R = true := by
  have hRG := (pin_spec hpin).1
  have hone : ∀ i < R.length, _ := fun i hi => by
    unfold invarK at h
    rw [allN_iff] at h
    have h1 := h i (by rw [lenLL_eq, hRG, repsK_length]; exact hi)
    simp only [andB_eq, Bool.and_eq_true] at h1
    obtain ⟨hE, hc, hG⟩ := rep_pack hpin hi
    exact invar_one hE hc hG h1.1.1 h1.1.2 h1.2.1 h1.2.2
  have key : ∀ P : List Elt → Bool, (∀ i < R.length, P ((R.getD i []).map Elt.ofCodes) = true) →
      (repsOf R).all P = true := by
    intro P hP
    rw [List.all_eq_true]
    intro es hes
    obtain ⟨gs, hgs, rfl⟩ := List.mem_map.mp hes
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgs
    have h1 := hP i hi
    rwa [getD_eq' _ _ hi] at h1
  exact ⟨key _ fun i hi => (hone i hi).1, key _ fun i hi => (hone i hi).2.1,
    key _ fun i hi => (hone i hi).2.2.1, key _ fun i hi => (hone i hi).2.2.2⟩

theorem e16_sound (R : List (List (ℕ × ℕ × Bool))) (RG RX : List (List ℕ))
    (hpin : pinK R RG RX = true)
    (h : e16K (nthK RG 28) (nthK RX 28) (nthK RG 26) (nthK RX 26) (nthK RG 27) (nthK RX 27) =
      true) : e16CheckOf R = true := by
  obtain ⟨hRG, -, -⟩ := pin_spec hpin
  unfold e16K at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h0f, h0s⟩, ⟨h1f, h1s⟩, ⟨h2f, h2s⟩, h2a, hp1, hp2⟩ := h
  have hlen : 28 < R.length := by
    by_contra hc
    have e : nthK RG 28 = [] := by
      rw [nthK_eq, hRG, repsK_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [e] at h0f
    change pop256 fullM = 16 at h0f
    rw [pop256_fullM] at h0f
    exact absurd h0f (by norm_num)
  obtain ⟨hE0, hc0, hG0⟩ := rep_pack hpin (i := 28) hlen
  obtain ⟨hE1, hc1, hG1⟩ := rep_pack hpin (i := 26) (by omega)
  obtain ⟨hE2, hc2, hG2⟩ := rep_pack hpin (i := 27) (by omega)
  have hfix : ∀ {G : List ℕ} {es : List Elt}, G.map decE = es →
      (fixPts es).length = pop256 (fixAllK G) := fun hG => by
    rw [← hG]
    exact fixPts_length _
  unfold e16CheckOf
  simp only [repsOf_getD]
  rw [← hE0, ← hE1, ← hE2, hfix hG0, hfix hG1, hfix hG2, span_gam2 hc0, span_gam2 hc1,
    span_gam2 hc2, h0f, h0s, h1f, h1s, h2f, h2s]
  have hpair : ∀ {X : List ℕ}, (∀ v ∈ X, Canon (eltX v) ∧ maskX v = fixK (eltX v)) →
      e16PairK X = true →
      (((X.map eltX).map decE).any (fun e => !e.b && (fixPts₁ [e]).length == 8) &&
        ((X.map eltX).map decE).any (fun e => !e.b && e != Elt.one &&
          (fixPts₁ [e]).length != 8) &&
        decide (128 ≤ pop256 (spanM (gam3K X)))) = true := by
    intro X hc hX
    unfold e16PairK at hX
    simp only [andB_eq, Bool.and_eq_true, anyL_iff, Nat.ble_eq] at hX
    obtain ⟨⟨v, hv, hv1⟩, ⟨u, hu, hu1⟩, h3⟩ := hX
    simp only [Bool.and_eq_true, notB_eq, Bool.not_eq_true', Nat.beq_eq] at hv1 hu1
    rw [List.map_map, List.any_map, List.any_map]
    simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    obtain ⟨hcv, hmv⟩ := hc v hv
    obtain ⟨hcu, hmu⟩ := hc u hu
    refine ⟨⟨⟨v, hv, ?_⟩, ⟨u, hu, ?_⟩⟩, h3⟩
    · simp only [Function.comp_apply, notb_decE, fixPts₁_length, ← hmv, Bool.and_eq_true,
        Nat.beq_eq, beq_iff_eq]
      exact hv1
    · have hn : (decE (eltX u) != Elt.one) = true := by
        rw [bne, one_iff hcu, hu1.1.2]
        rfl
      simp only [Function.comp_apply, notb_decE, fixPts₁_length, ← hmu, Bool.and_eq_true,
        Nat.beq_eq, bne_iff_ne, ne_eq] at hn ⊢
      exact ⟨⟨hu1.1.1, hn⟩, Nat.ne_of_beq_eq_false hu1.2⟩
  have hall2 : (((nthK RX 27).map eltX).map decE).all (fun e => e == Elt.one ||
      (spanList (gam2Pts (((nthK RX 27).map eltX).map decE))).any fun w => e.act w != w) =
      true := by
    rw [allL_iff] at h2a
    rw [List.map_map, List.all_map, List.all_eq_true]
    intro v hv
    obtain ⟨hcv, hmv⟩ := hc2 v hv
    have h1 := h2a v hv
    simp only [orB_eq, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h1
    simp only [Function.comp_apply, one_iff hcv, Bool.or_eq_true, Nat.beq_eq]
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ?_
      obtain ⟨u, hu⟩ := exists_testBit_of_pos h1
      rw [land_eq, xor_eq, Nat.testBit_and, Nat.testBit_xor, testBit_fullM, Bool.and_eq_true] at hu
      obtain ⟨hu1, hu2⟩ := hu
      have hu256 : u < 256 := by
        by_contra hc
        simp only [hc, decide_false, Bool.false_xor, hmv] at hu2
        rw [testBit_fixK_high _ (by omega)] at hu2
        exact Bool.false_ne_true hu2
      rw [decide_eq_true hu256, Bool.true_xor, Bool.not_eq_true', hmv] at hu2
      rw [List.any_eq_true]
      refine ⟨ptOfCode u, ?_, ?_⟩
      · rw [mem_spanList, ← List.map_map, closure_eq_of_mem fun _ hw => mem_gam2 hc2 hw]
        exact (isMask_spanM _ u hu256).mp hu1
      · rw [testBit_fixK _ hu256, decide_eq_false_iff_not] at hu2
        rw [bne_iff_ne]
        exact hu2
  simp only [List.all_cons, List.all_nil, Bool.and_true, beq_self_eq_true, Bool.true_and,
    hall2, span_gam3 hc1, span_gam3 hc2, hpair hc1 hp1, hpair hc2 hp2]

end CFSG.KC.H9Four.Sound

end
