module

public import CFSG.Certificates.Kernel.TwoNodeSmall.WitKSound
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosClosed

public section

namespace CFSG.TwoNodeSmall.PosBK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def posBGrp (p N s : Nat) (o : Nat × Nat × Nat) : List SPt :=
  (allVecsP p 4).map fun fr =>
    let inJ := fun k => s ≤ k && k < s + (N - 3)
    let outs := (List.range (N - 1)).filter fun k => !(inJ k)
    let uv : Nat → Nat × Nat := fun k =>
      if inJ k then (if k - s = o.1 then (o.2.1, o.2.2) else (0, 0))
      else if outs.head? = some k then (fr.getD 0 0, fr.getD 1 0) else (fr.getD 2 0, fr.getD 3 0)
    ⟨{ p := p, D := N, nFrame := N - 1,
       gens := (List.range (N - 1)).map (fun k => (⟨cartanRowP p N k ++ [(uv k).1], unitP N k⟩ : Refl)) ++
         [⟨(List.range (N - 1)).map (fun k => (uv k).2) ++ [2], unitP N (N - 1)⟩],
       x := (List.range (N - 1)).map (· + 1) ++ [0], bound := posBound p N }, s⟩

theorem posBCell_eq (p N : Nat) : posBCell p N = [0, 1, 2].flatMap fun s =>
    (posOpts p N).flatMap fun o => posBGrp p N s o :=
  rfl

namespace GBS

open OKS LaneSound

noncomputable abbrev pkG (P : Pt) : List (Nat × Nat) := P.gens.map fun g => (pkP P.p P.D g.h, pkrP P.p P.D g.f)

structure PtFacts (F : Fd) (G : List (Nat × Nat)) (X N s bnd : Nat) (Q : SPt) : Prop where
  p357 : Q.pt.p = 3 ∨ Q.pt.p = 5 ∨ Q.pt.p = 7
  dN : Q.pt.D = N
  d1 : 5 ≤ N
  d10 : N ≤ 10
  fd : F = fdB Q.pt.p N
  gens : G = pkG Q.pt
  len : Q.pt.gens.length = N
  nF : Q.pt.nFrame = N - 1
  x : X = pkP Q.pt.p N Q.pt.x
  bound : Q.pt.bound = bnd
  sEq : Q.s = s
  s3 : s < 3

theorem laneOK_B {P : Pt} (hp : P.p = 3 ∨ P.p = 5 ∨ P.p = 7) (hD : P.D ≤ 10) :
    LaneOK (fdB P.p P.D) P := by
  rcases hp with hp | hp | hp
  · rw [hp]
    exact laneOK_three hp hD
  · rw [fdB_of_ne _ (by omega)]
    exact ⟨rfl, dotKP_pk rfl (by omega) (by omega) hD, appKP_pk rfl (Or.inl hp) hD,
      conjKP_pk rfl (Or.inl hp) hD⟩
  · rw [fdB_of_ne _ (by omega)]
    exact ⟨rfl, dotKP_pk rfl (by omega) (by omega) hD, appKP_pk rfl (Or.inr hp) hD,
      conjKP_pk rfl (Or.inr hp) hD⟩

theorem prime_of {p : Nat} (hp : p = 3 ∨ p = 5 ∨ p = 7) : p.Prime := by
  rcases hp with rfl | rfl | rfl <;> norm_num

theorem nthK_pkG {P : Pt} {j : Nat} (hj : j < P.gens.length) :
    nthK (0, 0) (pkG P) j = packR P (P.gens.getD j ⟨[], []⟩) := by
  rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj]
  rfl

theorem ltAll_wordOK {P : Pt} : ∀ w : List Nat, ltAll P.gens.length w = true → P.wordOK w = true
  | [], _ => rfl
  | j :: w, h => by
    change (Nat.blt j P.gens.length && ltAll P.gens.length w) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    exact (wordOK_cons P j w).mpr ⟨h.1, ltAll_wordOK w h.2⟩

theorem chainK_spec {P : Pt} [Fact P.p.Prime] {F : Fd} (hL : LaneOK F P) {k : Nat}
    (hk : k < P.gens.length) : ∀ w : List Nat, P.wordOK w = true →
      ∃ x : CE, x.2.1 = w ∧ x.2.2 = k ∧ Sem P x ∧ chainK F (pkG P) k w = packR P x.1
  | [], _ => ⟨(P.gens.getD k ⟨[], []⟩, [], k), rfl, rfl, ⟨rfl, hk, rfl, fun _ => rfl⟩,
      nthK_pkG hk⟩
  | j :: w, hw => by
    rw [wordOK_cons] at hw
    obtain ⟨x, hx1, hx2, hs, hc⟩ := chainK_spec hL hk w hw.2
    refine ⟨(conjR P (P.gens.getD j ⟨[], []⟩) x.1, j :: x.2.1, x.2.2), by rw [hx1], hx2,
      sem_step hs hw.1, ?_⟩
    change conjK F (nthK (0, 0) (pkG P) j) (chainK F (pkG P) k w) = _
    rw [hc, nthK_pkG hw.1]
    exact conj_pack hL _ _

theorem app_pack {P : Pt} {F : Fd} (hL : LaneOK F P) (r : Refl) (v : Vec) :
    appK F (packR P r) (pkP P.p P.D v) = pkP P.p P.D (P.applyRefl r v) :=
  hL.app r.h r.f v

theorem dot_pack {P : Pt} {F : Fd} (hL : LaneOK F P) (a b : Refl) :
    dotK F (packR P a).2 (packR P b).1 = P.dotv a.f b.h :=
  hL.dot a.f b.h

theorem dot_two {P : Pt} [Fact P.p.Prime] {F : Fd} (hL : LaneOK F P) {r : Refl}
    (h : reflOK F (packR P r) = true) : P.dot (P.vec r.f) (P.vec r.h) = 2 := by
  unfold reflOK at h
  rw [Nat.beq_eq, dot_pack hL] at h
  rw [← Pt.dotv_spec, h]
  norm_num

theorem two_ne {P : Pt} (hp3 : 3 ≤ P.p) : (2 : ZMod P.p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod P.p) = ((0 : ℕ) : ZMod P.p) := by rw [Nat.cast_ofNat, h, Nat.cast_zero]
  rw [ZMod.natCast_eq_natCast_iff', Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at h2
  omega

theorem ne_of_not_beq {x y : Nat} (h : (!Nat.beq x y) = true) : x ≠ y := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem vecNZ_of {P : Pt} {v : Vec} (h : P.vec v ≠ 0) : P.vecNZ v = true := by
  by_contra hc
  apply h
  funext i
  unfold Pt.vecNZ at hc
  have h1 := List.any_eq_false.mp (Bool.eq_false_iff.mpr hc) i.val (List.mem_range.mpr i.isLt)
  simp only [Pt.ent, bne_iff_ne, ne_eq, Decidable.not_not] at h1
  simp only [Pt.vec, Pi.zero_apply]
  rw [← ZMod.natCast_mod, h1, Nat.cast_zero]

theorem dotv_zero {P : Pt} [Fact P.p.Prime] {f v : Vec} (h : P.dot (P.vec f) (P.vec v) = 0) :
    P.dotv f v = 0 := by
  have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
  have h2 : ((P.dotv f v : ℕ) : ZMod P.p) = ((0 : ℕ) : ZMod P.p) := by
    rw [Pt.dotv_spec, h, Nat.cast_zero]
  rw [ZMod.natCast_eq_natCast_iff', Nat.zero_mod, Nat.mod_eq_of_lt (dotv_lt' P hp0 f v)] at h2
  exact h2

theorem dotv_eq_of {P : Pt} [Fact P.p.Prime] {a b c d : Vec}
    (h : P.dot (P.vec a) (P.vec b) = P.dot (P.vec c) (P.vec d)) : P.dotv a b = P.dotv c d := by
  have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
  have h2 := Pt.dotv_spec P a b
  rw [h, ← Pt.dotv_spec P c d, ZMod.natCast_eq_natCast_iff'] at h2
  rwa [Nat.mod_eq_of_lt (dotv_lt' P hp0 a b), Nat.mod_eq_of_lt (dotv_lt' P hp0 c d)] at h2

@[expose] def scV (P : Pt) (l : Nat) (v : Vec) : Vec :=
  (List.range P.D).map fun i => l * v.getD i 0 % P.p

@[expose] def combV (P : Pt) (a : Nat) (x y : Vec) : Vec :=
  (List.range P.D).map fun i => (x.getD i 0 + (P.p - (a * y.getD i 0) % P.p)) % P.p

theorem vec_scV {P : Pt} (l : Nat) (v : Vec) : P.vec (scV P l v) = (l : ZMod P.p) • P.vec v := by
  funext i
  simp only [Pt.vec, scV, getD_range_map _ _ i.isLt, Pi.smul_apply, smul_eq_mul,
    ZMod.natCast_mod, Nat.cast_mul]

theorem vec_combV {P : Pt} [Fact P.p.Prime] (a : Nat) (x y : Vec) :
    P.vec (combV P a x y) = P.vec x - (a : ZMod P.p) • P.vec y := by
  have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
  funext i
  simp only [Pt.vec, combV, getD_range_map _ _ i.isLt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [cast_refl _ _ _ hp0, Nat.cast_mul]

theorem smul_fw {p : Nat} (hp : p = 3 ∨ p = 5 ∨ p = 7) (D l : Nat) (hl : l < p)
    (x : Nat → Nat) (hx : ∀ i, x i ≤ p - 1) :
    smulK (fdB p D) l (fw D x) = fw D (fun i => l * x i % p) := by
  unfold smulK
  have e : Nat.mul l (fw D x) = fw D (fun i => l * x i) := by
    unfold fw
    rw [enc_map_mul]
    rfl
  rw [e]
  rcases hp with rfl | hp
  · rw [redF_eq, red_fw 7 (Or.inr rfl) D _ (fun i => by
      have := Nat.mul_le_mul (show l ≤ 2 by omega) (hx i)
      omega)]
  · rw [fdB_of_ne _ (by omega), red_fwP hp D _ (fun i => Nat.mul_le_mul (by omega) (hx i))]

theorem smul_rv {p : Nat} (hp : p = 3 ∨ p = 5 ∨ p = 7) (D l : Nat) (hl : l < p)
    (x : Nat → Nat) (hx : ∀ i, x i ≤ p - 1) :
    smulK (fdB p D) l (rv D x) = rv D (fun i => l * x i % p) := by
  unfold smulK
  have e : Nat.mul l (rv D x) = rv D (fun i => l * x i) := by
    unfold rv
    rw [enc_map_mul]
    rfl
  rw [e]
  rcases hp with rfl | hp
  · rw [redF_eq, red_rv 7 (Or.inr rfl) D _ (fun i => by
      have := Nat.mul_le_mul (show l ≤ 2 by omega) (hx i)
      omega)]
  · rw [fdB_of_ne _ (by omega), red_rvP hp D _ (fun i => Nat.mul_le_mul (by omega) (hx i))]

theorem smul_pkP {P : Pt} (hp : P.p = 3 ∨ P.p = 5 ∨ P.p = 7) {l : Nat} (hl : l < P.p) (v : Vec) :
    smulK (fdB P.p P.D) l (pkP P.p P.D v) = pkP P.p P.D (scV P l v) := by
  rw [LaneSound.pkP_fw, LaneSound.pkP_fw, smul_fw hp _ _ hl _ (lnp_le (by omega) v)]
  unfold fw
  apply enc_map_congr
  intro i hi
  rw [List.mem_range] at hi
  simp [lnp, scV, List.getD_eq_getElem?_getD, hi, Nat.mul_mod]

theorem smul_pkrP {P : Pt} (hp : P.p = 3 ∨ P.p = 5 ∨ P.p = 7) {l : Nat} (hl : l < P.p) (v : Vec) :
    smulK (fdB P.p P.D) l (pkrP P.p P.D v) = pkrP P.p P.D (scV P l v) := by
  rw [LaneSound.pkrP_rv, LaneSound.pkrP_rv, smul_rv hp _ _ hl _ (lnp_le (by omega) v)]
  unfold rv
  apply enc_map_congr
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  simp [lnp, scV, List.getD_eq_getElem?_getD, hi, Nat.mul_mod]

theorem vec_of_pkP {P : Pt} (hp : 0 < P.p) (hp' : P.p < 65536) {a b : Vec}
    (h : pkP P.p P.D a = pkP P.p P.D b) : P.vec a = P.vec b :=
  vec_of_vecEq P ((OKS.pkP_inj hp hp' a b).mp h)

theorem vec_of_pkrP {P : Pt} (hp : 0 < P.p) (hp' : P.p < 65536) {a b : Vec}
    (h : pkrP P.p P.D a = pkrP P.p P.D b) : P.vec a = P.vec b :=
  vec_of_vecEq P ((LaneSound.pkrP_inj rfl hp (by omega) a b).mp h)

theorem pkP_of_vec {P : Pt} (hp : 0 < P.p) (hp' : P.p < 65536) {a b : Vec}
    (h : P.vec a = P.vec b) : pkP P.p P.D a = pkP P.p P.D b :=
  (OKS.pkP_inj hp hp' a b).mpr (vecEq_of_vec P h)

theorem pkrP_of_vec {P : Pt} (hp : 0 < P.p) (hp' : P.p < 65536) {a b : Vec}
    (h : P.vec a = P.vec b) : pkrP P.p P.D a = pkrP P.p P.D b :=
  (LaneSound.pkrP_inj rfl hp (by omega) a b).mpr (vecEq_of_vec P h)

theorem vec_refl_congr {P : Pt} [Fact P.p.Prime] (r : Refl) {a b : Vec}
    (h : P.vec a = P.vec b) : P.vec (P.applyRefl r a) = P.vec (P.applyRefl r b) := by
  rw [vec_refl, vec_refl, h]

theorem verifyT_of {P : Pt} [Fact P.p.Prime] {W : Word} {u φ : Vec} (hw : P.wordOK W = true)
    (hu : P.vec u ≠ 0) (hφ : P.vec φ ≠ 0) (hφu : P.dot (P.vec φ) (P.vec u) = 0)
    (hact : ∀ v, P.vec (P.applyWord W v) = P.vec v + P.dot (P.vec φ) (P.vec v) • P.vec u) :
    verifyT P ⟨W, u, φ⟩ = true := by
  unfold verifyT
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨hw, vecNZ_of hu⟩, vecNZ_of hφ⟩, by rw [dotv_zero hφu]; rfl⟩, ?_⟩
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi j hj
  have h := congrFun (hact (P.unit i)) ⟨j, hj⟩
  rw [Pt.vec_unit P ⟨i, hi⟩, dot_single] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h
  simp only [Pt.ent]
  rw [← ZMod.natCast_eq_natCast_iff']
  simp only [Pt.vec] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : (⟨j, hj⟩ : Fin P.D) ≠ ⟨i, hi⟩ := fun e => hij (Fin.mk.inj e).symm
    simp [hij, hne]

theorem dot_zero_right (P : Pt) (f : P.V) : P.dot f 0 = 0 := by simp [Pt.dot]

theorem dot_zero_left (P : Pt) (v : P.V) : P.dot 0 v = 0 := by simp [Pt.dot]

theorem par_verify {P : Pt} [Fact P.p.Prime] (hp : P.p = 3 ∨ P.p = 5 ∨ P.p = 7) (hD : P.D ≤ 10)
    (hwf : P.WF) {r : ExclK.Rec} (h : parOK (fdB P.p P.D) (pkG P) P.gens.length r = true) :
    ∃ t, verifyT P t = true := by
  obtain ⟨kd, k1, w1, k2, w2, l⟩ := r
  have hL := laneOK_B hp hD
  have hp0 : 0 < P.p := by omega
  have hp' : P.p < 65536 := by omega
  have h2 := two_ne (P := P) (by omega)
  unfold parOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk1, hw1⟩, hk2⟩, hw2⟩, hl0⟩, hlp⟩, hs⟩, ht⟩, hk⟩ := h
  rw [hL.fp] at hlp
  obtain ⟨S, -, -, hSs, hSc⟩ := chainK_spec hL hk1 _ (ltAll_wordOK _ hw1)
  obtain ⟨T, -, -, hTs, hTc⟩ := chainK_spec hL hk2 _ (ltAll_wordOK _ hw2)
  rw [hSc, hTc] at hk
  rw [hSc] at hs
  rw [hTc] at ht
  simp only [packR] at hk
  have dS := dot_two hL hs
  have dT := dot_two hL ht
  have hW : P.wordOK (sw S ++ sw T) = true := by
    simp only [Pt.wordOK, List.all_append, Bool.and_eq_true]
    exact ⟨sw_ok hSs, sw_ok hTs⟩
  have act : ∀ v, P.vec (P.applyWord (sw S ++ sw T) v) =
      (P.vec v - P.dot (P.vec T.1.f) (P.vec v) • P.vec T.1.h) -
        P.dot (P.vec S.1.f) (P.vec v - P.dot (P.vec T.1.f) (P.vec v) • P.vec T.1.h) •
          P.vec S.1.h := by
    intro v
    rw [applyWord_append, sw_act hwf hSs, vec_refl, sw_act hwf hTs, vec_refl]
  cases h0 : Nat.beq kd 0
  · rw [h0, cond_false, Bool.and_eq_true] at hk
    obtain ⟨e1, e2⟩ := hk
    rw [Nat.beq_eq, smul_pkrP hp hlp] at e1
    have eT : P.vec T.1.f = (l : ZMod P.p) • P.vec S.1.f := by
      rw [vec_of_pkrP hp0 hp' e1, vec_scV]
    have neS : P.vec S.1.h ≠ (l : ZMod P.p) • P.vec T.1.h := by
      intro e
      rw [← vec_scV] at e
      rw [smul_pkP hp hlp, pkP_of_vec hp0 hp' e, Nat.beq_refl] at e2
      exact absurd e2 (by decide)
    have key : (l : ZMod P.p) * P.dot (P.vec S.1.f) (P.vec T.1.h) = 2 := by
      rw [← smul_dot, ← eT, dT]
    refine ⟨⟨sw S ++ sw T, combV P l S.1.h T.1.h, S.1.f⟩, verifyT_of hW ?_ ?_ ?_ ?_⟩
    · rw [vec_combV]
      exact fun e => neS (sub_eq_zero.mp e)
    · intro e
      rw [e] at dS
      exact h2 (dS.symm.trans (dot_zero_left P _))
    · rw [vec_combV, dot_sub, dot_smul, dS, key, sub_self]
    · intro v
      rw [act, vec_combV, eT]
      simp only [dot_sub, dot_smul, smul_dot]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (P.dot (P.vec S.1.f) (P.vec v) * P.vec S.1.h i) * key
  · rw [h0, cond_true, Bool.and_eq_true] at hk
    obtain ⟨e1, e2⟩ := hk
    rw [Nat.beq_eq, smul_pkP hp hlp] at e1
    have eT : P.vec T.1.h = (l : ZMod P.p) • P.vec S.1.h := by
      rw [vec_of_pkP hp0 hp' e1, vec_scV]
    have neS : P.vec S.1.f ≠ (l : ZMod P.p) • P.vec T.1.f := by
      intro e
      rw [← vec_scV] at e
      rw [smul_pkrP hp hlp, pkrP_of_vec hp0 hp' e, Nat.beq_refl] at e2
      exact absurd e2 (by decide)
    have key : (l : ZMod P.p) * P.dot (P.vec T.1.f) (P.vec S.1.h) = 2 := by
      rw [← dot_smul, ← eT, dT]
    refine ⟨⟨sw S ++ sw T, S.1.h, combV P 1 (scV P l T.1.f) S.1.f⟩, verifyT_of hW ?_ ?_ ?_ ?_⟩
    · intro e
      rw [e] at dS
      exact h2 (dS.symm.trans (dot_zero_right P _))
    · rw [vec_combV, vec_scV, Nat.cast_one, one_smul]
      intro e
      exact neS (sub_eq_zero.mp e).symm
    · rw [vec_combV, vec_scV, Nat.cast_one, one_smul, sub_dot, smul_dot, dS, key, sub_self]
    · intro v
      rw [act, vec_combV, vec_scV, Nat.cast_one, one_smul, eT]
      simp only [dot_sub, dot_smul, sub_dot, smul_dot, dS]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring

theorem cyc_verify {Q : SPt} [Fact Q.pt.p.Prime] (hp : Q.pt.p = 3 ∨ Q.pt.p = 5 ∨ Q.pt.p = 7)
    (hD : Q.pt.D ≤ 10) (hwf : Q.pt.WF) (hjn : Q.s + (Q.pt.nFrame - 2) ≤ Q.pt.gens.length)
    {r : ExclK.Rec}
    (h : cycOK (fdB Q.pt.p Q.pt.D) (pkG Q.pt) Q.pt.gens.length Q.s (Q.pt.nFrame - 2) Q.pt.D r =
      true) : ∃ c, verifyC Q c = true := by
  obtain ⟨kd, j, w, j', w2, l⟩ := r
  have hL := laneOK_B hp hD
  have hp0 : 0 < Q.pt.p := by omega
  have hp' : Q.pt.p < 65536 := by omega
  unfold cycOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h5, hsj⟩, hjm⟩, hsj'⟩, hj'm⟩, hne⟩, hw⟩, -⟩, hi⟩, hab⟩, hcm⟩ := h
  rw [hL.fp] at h5 hab
  have hj : j < Q.pt.gens.length := by omega
  have hj' : j' < Q.pt.gens.length := by omega
  obtain ⟨T, hT1, hT2, hTs, hTc⟩ := chainK_spec hL hj _ (ltAll_wordOK _ hw)
  rw [hTc, nthK_pkG hj, nthK_pkG hj'] at hab
  rw [hTc, nthK_pkG hj'] at hcm
  simp only [dot_pack hL] at hab
  have hh : Q.pt.vec T.1.h = Q.pt.vec (Q.pt.applyWord w (Q.pt.hK j)) := by
    rw [hTs.2.2.1, gk, hT1, hT2]
    rfl
  have hf : ∀ u, Q.pt.dot (Q.pt.vec T.1.f) (Q.pt.vec u) =
      Q.pt.dot (Q.pt.vec (Q.pt.gens.getD j ⟨[], []⟩).f) (Q.pt.vec (Q.pt.applyWord w.reverse u)) := by
    intro u
    rw [hTs.2.2.2 u, gk, hT1, hT2]
  have e1 : Q.pt.dotv (Q.pt.gens.getD j' ⟨[], []⟩).f T.1.h =
      Q.pt.alphaK j' (Q.pt.applyWord w (Q.pt.hK j)) := dotv_congr rfl hh
  have e2 : Q.pt.dotv T.1.f (Q.pt.gens.getD j ⟨[], []⟩).h =
      Q.pt.alphaK j (Q.pt.applyWord w.reverse (Q.pt.hK j)) := dotv_eq_of (hf _)
  have e3 : Q.pt.dotv T.1.f (Q.pt.gens.getD j' ⟨[], []⟩).h =
      Q.pt.alphaK j (Q.pt.applyWord w.reverse (Q.pt.hK j')) := dotv_eq_of (hf _)
  have e4 : Q.pt.dotv (Q.pt.gens.getD j ⟨[], []⟩).f T.1.h =
      Q.pt.alphaK j (Q.pt.applyWord w (Q.pt.hK j)) := dotv_congr rfl hh
  rw [e1, e2, e3, e4] at hab
  have hsw : sw T = w ++ [j] ++ w.reverse := by rw [sw, hT1, hT2]
  refine ⟨⟨w, j, j'⟩, ?_⟩
  simp only [verifyC, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h5, ltAll_wordOK _ hw⟩, hsj⟩, hjm⟩, hsj'⟩, hj'm⟩, ne_of_not_beq hne⟩,
    ne_of_not_beq hab⟩, ?_⟩
  rw [OKS.shiftLeft_unitP Q.pt (by omega) hi] at hcm
  simp only [app_pack hL] at hcm
  refine List.any_eq_true.mpr ⟨w2.headD 0, List.mem_range.mpr hi, ?_⟩
  rw [bne_iff_ne]
  intro heq
  apply ne_of_not_beq hcm
  apply pkP_of_vec hp0 hp'
  have h1 := congrArg Q.pt.vec heq
  rw [applyWord_append, applyWord_append Q.pt [j'], applyWord_single Q.pt hj',
    applyWord_single Q.pt hj', ← hsw, sw_act hwf hTs,
    vec_refl_congr (Q.pt.gens.getD j' ⟨[], []⟩) (sw_act hwf hTs _)] at h1
  exact h1

theorem recOK_verify {Q : SPt} (hp : Q.pt.p = 3 ∨ Q.pt.p = 5 ∨ Q.pt.p = 7) (hD : Q.pt.D ≤ 10)
    (hwf : wfCheck Q.pt = true) (hjn : Q.s + (Q.pt.nFrame - 2) ≤ Q.pt.gens.length)
    {r : ExclK.Rec}
    (h : recOK (fdB Q.pt.p Q.pt.D) (pkG Q.pt) Q.pt.gens.length Q.s (Q.pt.nFrame - 2) Q.pt.D r =
      true) :
    (∃ t, verifyT Q.pt t = true) ∨ ∃ c, verifyC Q c = true := by
  have : Fact Q.pt.p.Prime := ⟨prime_of hp⟩
  have hWF : Q.pt.WF := wfCheck_sound hwf
  unfold recOK at h
  cases h1 : Nat.blt r.1 2
  · rw [h1, cond_false] at h
    cases h2 : Nat.beq r.1 2
    · rw [h2, cond_false] at h
      exact absurd h Bool.false_ne_true
    · rw [h2, cond_true] at h
      exact Or.inr (cyc_verify hp hD hWF hjn h)
  · rw [h1, cond_true] at h
    exact Or.inl (par_verify hp hD hWF h)

theorem last_pk {P : Pt} (hlen : P.gens.length = P.D) (hnF : P.nFrame = P.D - 1) (h1 : 1 ≤ P.D) :
    nthK (0, 0) (pkG P) (P.D - 1) = (pkP P.p P.D P.lastRefl.h, pkrP P.p P.D P.lastRefl.f) := by
  have hi : P.D - 1 < P.gens.length := by omega
  rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, Pt.lastRefl,
    hnF, List.getD_eq_getElem _ _ hi]

theorem fixed_of {F : Fd} {G : List (Nat × Nat)} {X N s bnd : Nat} {Q : SPt}
    (hf : PtFacts F G X N s bnd Q) (h : dotK F (nthK (0, 0) G (N - 1)).2 X = 0) :
    verifyPos Q .fixed = true := by
  obtain ⟨hp, hD, h1, h10, hF, hG, hlen, hnF, hX, -, -, -⟩ := hf
  subst hF hG hX hD
  have hL := laneOK_B hp h10
  rw [last_pk hlen hnF (by omega), hL.dot] at h
  simp only [verifyPos, verifyF, h, beq_self_eq_true]

theorem wf_of {Q : SPt} (hp : Q.pt.p = 3 ∨ Q.pt.p = 5 ∨ Q.pt.p = 7) (hD : Q.pt.D ≤ 10)
    (h : (pkG Q.pt).all (reflOK (fdB Q.pt.p Q.pt.D)) = true) : wfCheck Q.pt = true := by
  have hL := laneOK_B hp hD
  unfold wfCheck
  rw [List.all_eq_true]
  intro r hr
  have h1 := List.all_eq_true.mp h _ (List.mem_map_of_mem hr)
  unfold reflOK at h1
  rw [hL.dot, Nat.beq_eq] at h1
  rw [h1, Nat.mod_eq_of_lt (by omega)]
  exact beq_self_eq_true 2

theorem eqL_eq : ∀ (a b : List Nat), eqL a b = true → a = b
  | [], b, h => by
    cases b with
    | nil => rfl
    | cons y ys =>
      change (y :: ys).isEmpty = true at h
      simp at h
  | x :: a, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | x :: a, y :: b, h => by
    change (Nat.beq x y && eqL a b) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, eqL_eq a b h.2]

theorem order_of {F : Fd} {G : List (Nat × Nat)} {X N s bnd : Nat} {Q : SPt}
    (hf : PtFacts F G X N s bnd Q) (hwf : wfCheck Q.pt = true) {o : ORec}
    (h : oK F N bnd G o = true) : ∃ w, verifyPos Q w = true := by
  obtain ⟨hp, hD, -, h10, hF, hG, -, -, -, hb, -, -⟩ := hf
  subst hF hG hD hb
  have hL := laneOK_B hp h10
  have hpr := prime_of hp
  have ⟨h0, h1⟩ := oK_verify hpr (by omega) (by omega) hL hwf h
  by_cases ht : o.2.1 = 0
  · obtain ⟨w, hw⟩ := h0 ht
    exact ⟨.order w, by simp only [verifyPos, hwf, hw, Bool.and_self]⟩
  · obtain ⟨c, hc⟩ := h1 ht
    exact ⟨.weyl c, by simp only [verifyPos, hwf, hc, Bool.and_self]⟩

theorem rec_of {F : Fd} {G : List (Nat × Nat)} {X N s bnd : Nat} {Q : SPt}
    (hf : PtFacts F G X N s bnd Q) (hwf : wfCheck Q.pt = true) {r : ExclK.Rec}
    (h : recOK F G N s (N - 3) N r = true) : ∃ w, verifyPos Q w = true := by
  obtain ⟨hp, hD, h5, h10, hF, hG, hlen, hnF, -, -, hs, hs3⟩ := hf
  subst hF hG hD hs
  have hm : Q.pt.D - 3 = Q.pt.nFrame - 2 := by omega
  rw [hm] at h
  have h' : recOK (fdB Q.pt.p Q.pt.D) (pkG Q.pt) Q.pt.gens.length Q.s (Q.pt.nFrame - 2) Q.pt.D r =
      true := by
    rw [hlen]
    exact h
  rcases recOK_verify hp h10 hwf (by omega) h' with ⟨t, ht⟩ | ⟨c, hc⟩
  · exact ⟨.transv t, by simp only [verifyPos, hwf, ht, Bool.and_self]⟩
  · exact ⟨.cycle c, by simp only [verifyPos, hwf, hc, Bool.and_self]⟩

theorem grpB_nil (F : Fd) (B : List (Nat × Nat)) (vb cN o0 o1 X N s : Nat) (rs : List ExclK.Rec)
    (os : List ORec) : grpB F B vb cN o0 o1 X N s [] rs os = (rs.isEmpty && os.isEmpty) := rfl

theorem grpB_cons (F : Fd) (B : List (Nat × Nat)) (vb cN o0 o1 X N s : Nat) (fr : List Nat)
    (frs : List (List Nat)) (rs : List ExclK.Rec) (os : List ORec) :
    grpB F B vb cN o0 o1 X N s (fr :: frs) rs os =
      (bif Nat.beq (dotK F (nthK (0, 0) (gensB B vb cN o0 o1 N fr) (N - 1)).2 X) 0 then
        grpB F B vb cN o0 o1 X N s frs rs os
      else List.rec (motive := fun _ => Bool) false
        (fun r rs' _ =>
          (gensB B vb cN o0 o1 N fr).all (reflOK F) &&
          bif Nat.blt r.1 3 then recOK F (gensB B vb cN o0 o1 N fr) N s (N - 3) N r &&
            grpB F B vb cN o0 o1 X N s frs rs' os
          else Nat.beq r.1 3 && List.rec (motive := fun _ => Bool) false
            (fun o os' _ => eqL o.1 fr && grpB F B vb cN o0 o1 X N s frs rs' os') os) rs) := rfl

theorem walk {F : Fd} {B : List (Nat × Nat)} {vb cN o0 o1 X N s bnd : Nat}
    (Qf : List Nat → SPt) (frs : List (List Nat))
    (hf : ∀ fr ∈ frs, PtFacts F (gensB B vb cN o0 o1 N fr) X N s bnd (Qf fr)) :
    ∀ (rs : List ExclK.Rec) (os : List ORec), grpB F B vb cN o0 o1 X N s frs rs os = true →
      (∀ o ∈ os, oK F N bnd (gensB B vb cN o0 o1 N o.1) o = true) →
      ∀ fr ∈ frs, ∃ w, verifyPos (Qf fr) w = true := by
  induction frs with
  | nil => intro _ _ _ _ fr hfr; simp at hfr
  | cons fr frs ih =>
    intro rs os h ho fr' hfr'
    have hf0 := hf fr List.mem_cons_self
    have hft := fun f (hm : f ∈ frs) => hf f (List.mem_cons_of_mem _ hm)
    rw [grpB_cons] at h
    cases hd : Nat.beq (dotK F (nthK (0, 0) (gensB B vb cN o0 o1 N fr) (N - 1)).2 X) 0 with
    | true =>
      rw [hd, cond_true] at h
      rcases List.mem_cons.mp hfr' with rfl | hm
      · exact ⟨.fixed, fixed_of hf0 (Nat.eq_of_beq_eq_true hd)⟩
      · exact ih hft rs os h ho fr' hm
    | false =>
      rw [hd, cond_false] at h
      cases rs with
      | nil => exact absurd h (by simp)
      | cons r rs' =>
        change ((gensB B vb cN o0 o1 N fr).all (reflOK F) &&
          bif Nat.blt r.1 3 then recOK F (gensB B vb cN o0 o1 N fr) N s (N - 3) N r &&
            grpB F B vb cN o0 o1 X N s frs rs' os
          else Nat.beq r.1 3 && List.rec (motive := fun _ => Bool) false
            (fun o os' _ => eqL o.1 fr && grpB F B vb cN o0 o1 X N s frs rs' os') os) = true at h
        rw [Bool.and_eq_true] at h
        obtain ⟨hall, h⟩ := h
        have hwf : wfCheck (Qf fr).pt = true := by
          obtain ⟨hp, hD, -, h10, hF, hG, -, -, -, -, -, -⟩ := hf0
          rw [hF, hG, ← hD] at hall
          exact wf_of hp (by omega) hall
        cases hk : Nat.blt r.1 3 with
        | true =>
          rw [hk, cond_true, Bool.and_eq_true] at h
          rcases List.mem_cons.mp hfr' with rfl | hm
          · exact rec_of hf0 hwf h.1
          · exact ih hft rs' os h.2 ho fr' hm
        | false =>
          rw [hk, cond_false, Bool.and_eq_true] at h
          cases os with
          | nil => exact absurd h.2 (by simp)
          | cons o os' =>
            have h2 : (eqL o.1 fr && grpB F B vb cN o0 o1 X N s frs rs' os') = true := h.2
            rw [Bool.and_eq_true] at h2
            rcases List.mem_cons.mp hfr' with rfl | hm
            · have hoK := ho o List.mem_cons_self
              rw [eqL_eq _ _ h2.1] at hoK
              exact order_of hf0 hwf hoK
            · exact ih hft rs' os' h2.2 (fun o' ho' => ho o' (List.mem_cons_of_mem _ ho')) fr' hm

@[expose] def uvB (N s : Nat) (o : Nat × Nat × Nat) (fr : List Nat) (k : Nat) : Nat × Nat :=
  if inJ N s k then (if k - s = o.1 then (o.2.1, o.2.2) else (0, 0))
  else if (outsOf N s).head? = some k then (fr.getD 0 0, fr.getD 1 0)
  else (fr.getD 2 0, fr.getD 3 0)

@[expose] def ptB (p N s : Nat) (o : Nat × Nat × Nat) (fr : List Nat) : SPt :=
  ⟨{ p := p, D := N, nFrame := N - 1,
     gens := (List.range (N - 1)).map
         (fun k => (⟨cartanRowP p N k ++ [(uvB N s o fr k).1], unitP N k⟩ : Refl)) ++
       [⟨(List.range (N - 1)).map (fun k => (uvB N s o fr k).2) ++ [2], unitP N (N - 1)⟩],
     x := (List.range (N - 1)).map (· + 1) ++ [0], bound := posBound p N }, s⟩

theorem posBGrp_eq (p N s : Nat) (o : Nat × Nat × Nat) :
    posBGrp p N s o = (allVecsP p 4).map (ptB p N s o) := rfl

theorem getD_lt_of_mem {p : Nat} (hp : 0 < p) :
    ∀ {n : Nat} {v : Vec}, v ∈ allVecsP p n → ∀ i, v.getD i 0 < p
  | 0, v, h, i => by
    simp only [allVecsP, List.mem_singleton] at h
    subst h
    simpa using hp
  | n + 1, v, h, i => by
    simp only [allVecsP, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨w, hw, a, ha, rfl⟩ := h
    cases i with
    | zero => simpa using ha
    | succ i => simpa using getD_lt_of_mem hp hw i

theorem getElem?_addAt (a : Nat) : ∀ (G : List (Nat × Nat)) (k i : Nat),
    (addAt a G k)[i]? = if i = k then G[i]?.map (fun g => (g.1, g.2 + a)) else G[i]?
  | [], k, i => by
    change ([] : List (Nat × Nat))[i]? = _
    simp
  | g :: gs, 0, 0 => by
    change (((g.1, g.2 + a) :: gs) : List (Nat × Nat))[0]? = _
    simp
  | g :: gs, 0, i + 1 => by
    change (((g.1, g.2 + a) :: gs) : List (Nat × Nat))[i + 1]? = _
    simp
  | g :: gs, k + 1, 0 => by
    change (g :: addAt a gs k)[0]? = _
    simp
  | g :: gs, k + 1, i + 1 => by
    change (g :: addAt a gs k)[i + 1]? = _
    simp [getElem?_addAt a gs k i]

theorem rv_congr {D : Nat} {x y : Nat → Nat} (h : ∀ i < D, x i = y i) : rv D x = rv D y := by
  unfold rv
  apply enc_map_congr
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  exact h i hi

theorem rv_add_lane : ∀ (D : Nat) (x : Nat → Nat) (k c : Nat), k < D →
    rv D x + c * laneR D k = rv D (fun i => if i = k then x i + c else x i)
  | 0, _, _, _, h => absurd h (by omega)
  | D + 1, x, k, c, hk => by
    rw [rv_succ_last, rv_succ_last]
    by_cases hkD : k = D
    · subst hkD
      have e : laneR (k + 1) k = 1 := by simp [laneR]
      rw [e, rv_congr (x := fun i => if i = k then x i + c else x i) (y := x)
        (fun i hi => by simp only [if_neg (show i ≠ k by omega)])]
      simp only [↓reduceIte]
      omega
    · have hk' : k < D := by omega
      have e : laneR (D + 1) k = 65536 * laneR D k := by
        unfold laneR
        rw [show 16 * (D + 1 - 1 - k) = 16 * (D - 1 - k) + 16 by omega, pow_add]
        ring
      have hDk : D ≠ k := Ne.symm hkD
      rw [e, ← rv_add_lane D x k c hk']
      simp only [hDk, ↓reduceIte]
      ring

theorem getD_snoc_lt (l : List Nat) (c : Nat) {i : Nat} (hi : i < l.length) :
    (l ++ [c]).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_len (l : List Nat) (c : Nat) : (l ++ [c]).getD l.length 0 = c := by
  simp [List.getD_eq_getElem?_getD]

theorem outs_facts {N s : Nat} (hN : N = 5 ∨ N = 6 ∨ N = 7) (hs : s < 3) :
    (outsOf N s).head? = some ((outsOf N s).getD 0 0) ∧
    (outsOf N s).getD 0 0 ≠ (outsOf N s).getD 1 0 ∧
    (outsOf N s).getD 0 0 < N - 1 ∧ (outsOf N s).getD 1 0 < N - 1 ∧
    inJ N s ((outsOf N s).getD 0 0) = false ∧ inJ N s ((outsOf N s).getD 1 0) = false ∧
    ∀ i < N - 1, inJ N s i = false → i = (outsOf N s).getD 0 0 ∨ i = (outsOf N s).getD 1 0 := by
  rcases hN with rfl | rfl | rfl <;> interval_cases s <;> decide

theorem getD_snoc_eq (l : List Nat) (c i : Nat) (h : l.length = i) : (l ++ [c]).getD i 0 = c := by
  rw [← h, getD_snoc_len]

theorem pkrP_snoc (p D : Nat) (r : Vec) (c : Nat) (hr : r.length + 1 = D) :
    pkrP p D (r ++ [c]) = c % p + 65536 * pkrP p (D - 1) r := by
  obtain rfl := hr
  rw [Nat.add_sub_cancel, LaneSound.pkrP_rv, LaneSound.pkrP_rv, rv_succ_last]
  congr 1
  · simp only [lnp]
    rw [getD_snoc_len]
  · congr 1
    apply rv_congr
    intro i hi
    simp only [lnp]
    rw [getD_snoc_lt _ _ (by omega)]

theorem uvB_o0 {N s : Nat} (hN : N = 5 ∨ N = 6 ∨ N = 7) (hs : s < 3) (o : Nat × Nat × Nat)
    (fr : List Nat) : uvB N s o fr ((outsOf N s).getD 0 0) = (fr.getD 0 0, fr.getD 1 0) := by
  obtain ⟨hh, -, -, -, hj0, -, -⟩ := outs_facts hN hs
  unfold uvB
  rw [if_neg (by rw [hj0]; exact Bool.false_ne_true), if_pos hh]

theorem uvB_o1 {N s : Nat} (hN : N = 5 ∨ N = 6 ∨ N = 7) (hs : s < 3) (o : Nat × Nat × Nat)
    (fr : List Nat) : uvB N s o fr ((outsOf N s).getD 1 0) = (fr.getD 2 0, fr.getD 3 0) := by
  obtain ⟨hh, hne, -, -, -, hj1, -⟩ := outs_facts hN hs
  unfold uvB
  rw [if_neg (by rw [hj1]; exact Bool.false_ne_true),
    if_neg (by rw [hh]; exact fun e => hne (Option.some.inj e))]

theorem uvB_in {N s k : Nat} (o : Nat × Nat × Nat) (fr : List Nat) (hJ : inJ N s k = true) :
    uvB N s o fr k = if k - s = o.1 then (o.2.1, o.2.2) else (0, 0) := by
  unfold uvB
  rw [if_pos hJ]

theorem pkG_ptB (p N s : Nat) (o : Nat × Nat × Nat) (fr : List Nat) :
    pkG (ptB p N s o fr).pt =
      (List.range (N - 1)).map (fun k => (pkP p N (unitP N k),
        pkrP p N (cartanRowP p N k ++ [(uvB N s o fr k).1]))) ++
      [(pkP p N (unitP N (N - 1)),
        pkrP p N ((List.range (N - 1)).map (fun k => (uvB N s o fr k).2) ++ [2]))] := by
  simp only [pkG, ptB, List.map_append, List.map_map, List.map_cons, List.map_nil]
  rfl

theorem gens_eq {p N s oi : Nat} (hp0 : 0 < p) (hN : N = 5 ∨ N = 6 ∨ N = 7) (hs : s < 3)
    {fr : List Nat} (hfr : ∀ i, fr.getD i 0 < p) :
    gensB (baseB p N s oi) (vbB p N s oi) (pkP p N (unitP N (N - 1))) ((outsOf N s).getD 0 0)
      ((outsOf N s).getD 1 0) N fr = pkG (ptB p N s (optOf p N oi) fr).pt := by
  obtain ⟨hh, hne, ho0, ho1, hj0, hj1, hall⟩ := outs_facts hN hs
  rw [pkG_ptB]
  apply List.ext_getElem?
  intro i
  unfold gensB
  rw [getElem?_addAt, getElem?_addAt]
  simp only [nthK_eq']
  rcases Nat.lt_trichotomy i (N - 1) with hi | hi | hi
  · have hl : i < (baseB p N s oi).length := by simp [baseB, hi]
    rw [List.getElem?_append_left hl, List.getElem?_append_left (by simpa using hi)]
    simp only [baseB, List.getElem?_map, List.getElem?_range hi, Option.map_some]
    have hc : (cartanRowP p N i).length + 1 = N := by simp [cartanRowP]; omega
    by_cases h0 : i = (outsOf N s).getD 0 0
    · have h1 : i ≠ (outsOf N s).getD 1 0 := by rw [h0]; exact hne
      have hJ : inJ N s i = false := by rw [h0]; exact hj0
      have hu : (uvB N s (optOf p N oi) fr i).1 = fr.getD 0 0 := by rw [h0, uvB_o0 hN hs]
      simp only [if_pos h0, if_neg h1, Option.map_some, hu, hJ, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq, true_and]
      rw [pkrP_snoc _ _ _ _ hc, pkrP_snoc _ _ _ _ hc, Nat.mod_eq_of_lt (hfr 0), Nat.zero_mod]
      omega
    · by_cases h1 : i = (outsOf N s).getD 1 0
      · have hJ : inJ N s i = false := by rw [h1]; exact hj1
        have hu : (uvB N s (optOf p N oi) fr i).1 = fr.getD 2 0 := by rw [h1, uvB_o1 hN hs]
        simp only [if_neg h0, if_pos h1, Option.map_some, hu, hJ, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq, true_and]
        rw [pkrP_snoc _ _ _ _ hc, pkrP_snoc _ _ _ _ hc, Nat.mod_eq_of_lt (hfr 2), Nat.zero_mod]
        omega
      · have hJ : inJ N s i = true := by
          cases hq : inJ N s i with
          | true => rfl
          | false => exact absurd (hall i hi hq) (by tauto)
        rw [if_neg h0, if_neg h1]
        simp only [uvB, hJ, ↓reduceIte]
        split_ifs <;> rfl
  · subst hi
    have hl : (baseB p N s oi).length = N - 1 := by simp [baseB]
    have h0 : N - 1 ≠ (outsOf N s).getD 0 0 := by omega
    have h1 : N - 1 ≠ (outsOf N s).getD 1 0 := by omega
    rw [if_neg h0, if_neg h1, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by simp), hl]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq, true_and]
    unfold vbB
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [LaneSound.pkrP_rv, LaneSound.pkrP_rv, ← Nat.add_assoc, rv_add_lane _ _ _ _ (by omega),
      rv_add_lane _ _ _ _ (by omega)]
    apply rv_congr
    intro i hi
    simp only [lnp]
    rcases Nat.lt_or_ge i (N - 1) with hi' | hi'
    · rw [getD_snoc_lt _ _ (by simpa using hi'), getD_snoc_lt _ _ (by simpa using hi')]
      simp only [getD_range_map _ _ hi']
      by_cases h0 : i = (outsOf N s).getD 0 0
      · subst h0
        simp only [uvB_o0 hN hs, hj0, if_neg hne, if_pos (rfl : (outsOf N s).getD 0 0 = _),
          Bool.false_eq_true, ↓reduceIte]
        rw [Nat.mod_eq_of_lt (hfr 1)]
        simp
      · by_cases h1 : i = (outsOf N s).getD 1 0
        · subst h1
          simp only [uvB_o1 hN hs, hj1, if_neg h0, if_pos (rfl : (outsOf N s).getD 1 0 = _),
            Bool.false_eq_true, ↓reduceIte]
          rw [Nat.mod_eq_of_lt (hfr 3)]
          simp
        · have hJ : inJ N s i = true := by
            cases hq : inJ N s i with
            | true => rfl
            | false => exact absurd (hall i hi' hq) (by tauto)
          simp only [uvB, hJ, h0, h1, ↓reduceIte]
          split_ifs <;> rfl
    · have he : i = N - 1 := by omega
      subst he
      have h0 : N - 1 ≠ (outsOf N s).getD 0 0 := by omega
      have h1 : N - 1 ≠ (outsOf N s).getD 1 0 := by omega
      simp only [h0, h1, ↓reduceIte]
      rw [getD_snoc_eq _ _ _ (by simp), getD_snoc_eq _ _ _ (by simp)]
  · rw [List.getElem?_eq_none (by simp [baseB]; omega), List.getElem?_eq_none (by simp; omega)]
    simp

theorem facts {p N s oi : Nat} (hpN : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7))
    (hs : s < 3) {fr : List Nat} (hfr : fr ∈ allVecsP p 4) :
    PtFacts (fdB p N) (gensB (baseB p N s oi) (vbB p N s oi) (pkP p N (unitP N (N - 1)))
      ((outsOf N s).getD 0 0) ((outsOf N s).getD 1 0) N fr) (xB p N) N s (posBound p N)
      (ptB p N s (optOf p N oi) fr) where
  p357 := by change p = 3 ∨ p = 5 ∨ p = 7; omega
  dN := rfl
  d1 := by omega
  d10 := by omega
  fd := rfl
  gens := gens_eq (by omega) (by omega) hs (getD_lt_of_mem (by omega) hfr)
  len := by simp only [ptB, List.length_append, List.length_map, List.length_range,
    List.length_singleton]; omega
  nF := rfl
  x := rfl
  bound := rfl
  sEq := rfl
  s3 := hs

end GBS

theorem grpAtB_verify {p N s oi : Nat} {rs : List ExclK.Rec} {os : List ORec}
    (_hpN : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7)) (_hs : s < 3)
    (_hoi : oi < (posOpts p N).length) (_h : grpAtB p N s oi rs os = true)
    (_ho : ∀ o ∈ os, oAtB p N s oi o = true) :
    ∀ Q ∈ posBGrp p N s (optOf p N oi), ∃ w, verifyPos Q w = true := by
  intro Q hQ
  rw [GBS.posBGrp_eq] at hQ
  obtain ⟨fr, hfr, rfl⟩ := List.mem_map.mp hQ
  exact GBS.walk (GBS.ptB p N s (optOf p N oi)) (allVecsP p 4) (fun fr hfr => GBS.facts _hpN _hs hfr)
    rs os _h _ho fr hfr

theorem grpAtB_closed
    {p N s oi : Nat} {rs : List ExclK.Rec} {os : List ORec}
    (hpN : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7)) (hs : s < 3)
    (hoi : oi < (posOpts p N).length) (h : grpAtB p N s oi rs os = true)
    (ho : ∀ o ∈ os, oAtB p N s oi o = true) :
    ∀ Q ∈ posBGrp p N s (optOf p N oi), ∀ [Fact Q.pt.p.Prime], Q.ClosedPosB := by
  intro Q hQ _
  obtain ⟨w, hw⟩ := grpAtB_verify hpN hs hoi h ho Q hQ
  exact verifyPos_elim hw Or.inl (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))
    (fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))) (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

@[expose] def parB (g : Nat) : Nat × Nat × Nat × Nat := (bpars ()).getD g (0, 0, 0, 0)

theorem ord_of_chunks {B n : Nat} {OS : List (List ORec)} (hB : 0 < B)
    (hn : (ochunks B OS).length = n) (hc : ∀ i < n, ochunkB B OS i = true) {g : Nat} (hg : g < 63) :
    ∀ o ∈ OS.getD g [], oAtB (parB g).1 (parB g).2.1 (parB g).2.2.1 (parB g).2.2.2 o = true := by
  intro o ho
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
  have hjB : j / B < ((OS.getD g []).length + B - 1) / B := by
    rw [Nat.lt_div_iff_mul_lt hB]
    have := Nat.div_mul_le_self j B
    omega
  have hmem : (g, j / B) ∈ ochunks B OS := by
    simp only [ochunks, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨g, hg, j / B, hjB, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have h := hc i (hn ▸ hi)
  simp only [ochunkB, List.getD_eq_getElem _ _ hi, hget, dropK_eq, Nat.mul_eq, List.all_eq_true]
    at h
  apply h
  have e := Nat.div_add_mod' j B
  have hm := Nat.mod_lt j hB
  rw [List.mem_iff_getElem]
  refine ⟨j % B, by simp only [List.length_take, List.length_drop]; omega, ?_⟩
  simp only [List.getElem_take, List.getElem_drop, e]

theorem cell_closed
    {RS : List (List ExclK.Rec)} {OS : List (List ORec)}
    (hg : ∀ g < 63, grpIdxB RS OS g = true)
    (ho : ∀ g < 63, ∀ o ∈ OS.getD g [],
      oAtB (parB g).1 (parB g).2.1 (parB g).2.2.1 (parB g).2.2.2 o = true)
    (p N off : Nat) (hpN : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7))
    (hpar : ∀ s < 3, ∀ oi < (posOpts p N).length, off + (posOpts p N).length * s + oi < 63 ∧
      parB (off + (posOpts p N).length * s + oi) = (p, N, s, oi)) :
    ∀ Q ∈ posBCell p N, ∀ [Fact Q.pt.p.Prime], Q.ClosedPosB := by
  intro Q hQ _
  rw [posBCell_eq] at hQ
  simp only [List.mem_flatMap] at hQ
  obtain ⟨s, hs, o, ho', hQ⟩ := hQ
  obtain ⟨oi, hoi, rfl⟩ := List.getElem_of_mem ho'
  have hs3 : s < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  obtain ⟨hi, hq⟩ := hpar s hs3 oi hoi
  have hopt : optOf p N oi = (posOpts p N)[oi] := by
    simp only [optOf, List.getD_eq_getElem _ _ hoi]
  rw [← hopt] at hQ
  generalize off + (posOpts p N).length * s + oi = gi at hi hq
  have h1 : grpAtB (parB gi).1 (parB gi).2.1 (parB gi).2.2.1 (parB gi).2.2.2 (RS.getD gi [])
      (OS.getD gi []) = true := hg gi hi
  have h2 := ho gi hi
  rw [hq] at h1 h2
  exact grpAtB_closed hpN hs3 hoi h1 h2 Q hQ

theorem posB_closed_of
    {RS : List (List ExclK.Rec)} {OS : List (List ORec)} {B n : Nat} (hB : 0 < B)
    (hg : ∀ g < 63, grpIdxB RS OS g = true) (hn : (ochunks B OS).length = n)
    (hc : ∀ i < n, ochunkB B OS i = true) :
    ∀ Q ∈ posBPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedPosB := by
  have ho := fun g (hg : g < 63) => ord_of_chunks hB hn hc hg
  intro Q hQ _
  simp only [posBPts, List.mem_append] at hQ
  rcases hQ with (hQ | hQ) | hQ
  · exact cell_closed hg ho 5 5 0 (Or.inl ⟨rfl, rfl⟩) (by decide) Q hQ
  · exact cell_closed hg ho 3 6 18 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by decide) Q hQ
  · exact cell_closed hg ho 7 7 39 (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by decide) Q hQ

end CFSG.TwoNodeSmall.PosBK

end
