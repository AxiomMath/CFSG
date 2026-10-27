module

public import Certificates.Data.Kernel.CentGenK
public import CFSG.Certificates.Kernel.SporSch.ChainKPack

public section

namespace CFSG.KC.CentGenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bA (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bN (c : Bool) : Bool.rec (motive := fun _ => Bool) true false c = !c := by
  cases c <;> rfl

theorem getR_eq (d : Nat) : ∀ (R : List Nat) (i : Nat), getR d R i = R.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: R, i + 1 => by
    change getR d R i = _
    rw [getR_eq d R i]
    rfl

theorem setR_eq (v : Nat) : ∀ (R : List Nat) (k : Nat), setR R k v = R.set k v
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: R, k + 1 => by
    change x :: setR R k v = _
    rw [setR_eq v R k]
    rfl

theorem repR_eq (d : Nat) : ∀ c, repR c d = List.replicate c d
  | 0 => rfl
  | c + 1 => by
    change d :: repR c d = _
    rw [repR_eq d c]
    rfl

theorem getR_setR {R : List Nat} {k : Nat} (hk : k < R.length) (d v r : Nat) :
    getR d (setR R k v) r = if k = r then v else getR d R r := by
  rw [getR_eq, getR_eq, setR_eq]
  by_cases h : k = r
  · subst h
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self hk]
    rfl
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem runK_cons (n w m nw idn nr : Nat) (H : List Nat) (r : Nat) (prog : List Nat)
    (K : List Nat → Bool) (R : List Nat) :
    runK n w m nw idn nr H (r :: prog) K R =
      (Nat.blt (opK r) nr &&
        Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool) false
              (permOK n w m nw (getR idn R (opA r)) (getR 0 H (opB r)) &&
                runK n w m nw idn nr H prog K (setR R (opK r) (getR 0 H (opB r))))
              (Nat.beq (opC r) 2))
            (runK n w m nw idn nr H prog K
              (setR R (opK r) (MOC.powK n w m idn (getR idn R (opA r)) (opB r))))
            (Nat.beq (opC r) 1))
          (runK n w m nw idn nr H prog K
            (setR R (opK r) (pcomp n w m (getR idn R (opA r)) (getR idn R (opB r)))))
          (Nat.beq (opC r) 0)) := by
  simp only [runK, sB, bA]

theorem neAll_succ (n w m f e c acc : Nat) :
    neAll n w m f e (c + 1) acc =
      (Bool.rec (motive := fun _ => Bool) true false (Nat.beq f acc) &&
        neAll n w m f e c (pcomp n w m e acc)) := by
  simp only [neAll, sB, bA]

section Abstract

variable {G : Type*} [Group G]

@[expose] noncomputable def stepA (R : ℕ → G) (r : ℕ) : ℕ → G :=
  Function.update R (opK r)
    (if opC r = 0 then R (opA r) * R (opB r) else if opC r = 1 then R (opA r) ^ opB r
      else (R (opA r))⁻¹)

@[expose] noncomputable def runA (R : ℕ → G) (prog : List ℕ) : ℕ → G := prog.foldl stepA R

@[expose] def initA (x y : G) : ℕ → G := fun r => if r = 0 then x else if r = 1 then y else 1

theorem runA_mem (S : Subgroup G) : ∀ (prog : List ℕ) {R : ℕ → G}, (∀ r, R r ∈ S) →
    ∀ r, runA R prog r ∈ S
  | [], _, hR => hR
  | r :: prog, R, hR => by
    refine runA_mem S prog (R := stepA R r) fun t => ?_
    unfold stepA
    rw [Function.update_apply]
    split_ifs
    · exact S.mul_mem (hR _) (hR _)
    · exact S.pow_mem (hR _) _
    · exact S.inv_mem (hR _)
    · exact hR t

theorem initA_mem (S : Subgroup G) {x y : G} (hx : x ∈ S) (hy : y ∈ S) : ∀ r, initA x y r ∈ S := by
  intro r
  unfold initA
  split_ifs
  · exact hx
  · exact hy
  · exact S.one_mem

end Abstract

@[expose, reducible] def PS (n w P : Nat) (g : Equiv.Perm (Fin n)) : Prop :=
  PRep n w P g ∧ P >>> (n * w) = 0

variable {n w : Nat}

theorem ps_one (hsz : szOK n w = true) : PS n w (pidn n w) 1 := by
  have hf := szOK_facts hsz
  exact ⟨prep_pidn hf.1 hf.2, PF.pidn_shr hf.1 hf.2⟩

theorem ps_mul (hsz : szOK n w = true) {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hP : PS n w P g)
    (hQ : PS n w Q h) : PS n w (pcomp n w (mask w) P Q) (g * h) :=
  ⟨prep_pcomp (MOC.szOK_lt hsz) hP.1 hQ.1,
    PF.pcomp_shr P Q (MOC.szOK_lt hsz) (PF.w_pos (szOK_facts hsz).2)⟩

theorem ps_pow (hsz : szOK n w = true) {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PS n w P g)
    (e : Nat) : PS n w (MOC.powK n w (mask w) (pidn n w) P e) (g ^ e) :=
  MOC.prep_powK hsz hP.1 e

theorem ps_inv {P Q : Nat} {g : Equiv.Perm (Fin n)} (hP : PS n w P g)
    (h : permOK n w (mask w) (n * w) P Q = true) : PS n w Q g⁻¹ :=
  ⟨MOC.prep_inv_of_permOK hP.1 h, (permOK_facts h).2.1⟩

theorem ps_beq (hsz : szOK n w = true) {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hP : PS n w P g)
    (hQ : PS n w Q h) : Nat.beq P Q = decide (g = h) :=
  MOC.beq_prep (PF.w_pos (szOK_facts hsz).2) hP.1 hQ.1 hP.2 hQ.2

theorem ps_update {R : List Nat} {R' : ℕ → Equiv.Perm (Fin n)} {k v : Nat}
    {g : Equiv.Perm (Fin n)} (d : Nat) (hk : k < R.length) (hv : PS n w v g)
    (hR : ∀ r, PS n w (getR d R r) (R' r)) :
    ∀ r, PS n w (getR d (setR R k v) r) (Function.update R' k g r) := by
  intro r
  rw [getR_setR hk, Function.update_apply]
  by_cases h : k = r
  · subst h
    simpa using hv
  · rw [if_neg h, if_neg (Ne.symm h)]
    exact hR r

theorem ps_init (hsz : szOK n w = true) {x y c : Nat} {X Y : Equiv.Perm (Fin n)}
    (hx : PS n w x X) (hy : PS n w y Y) :
    ∀ r, PS n w (getR (pidn n w) (initR x y c (pidn n w)) r) (initA X Y r) := by
  intro r
  rw [getR_eq, initR, repR_eq]
  rcases r with _ | _ | r
  · exact hx
  · exact hy
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem?_getD,
      List.getElem?_replicate]
    have e1 : initA X Y (r + 1 + 1) = 1 := by
      unfold initA
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e1]
    split_ifs <;> exact ps_one hsz

theorem runK_sim (hsz : szOK n w = true) (nr : Nat) (H : List Nat) (K : List Nat → Bool) :
    ∀ (prog R : List Nat) (R' : ℕ → Equiv.Perm (Fin n)), R.length = nr →
      (∀ r, PS n w (getR (pidn n w) R r) (R' r)) →
      runK n w (mask w) (n * w) (pidn n w) nr H prog K R = true →
      ∃ R2 : List Nat, R2.length = nr ∧
        (∀ r, PS n w (getR (pidn n w) R2 r) (runA R' prog r)) ∧ K R2 = true
  | [], R, _, hl, hR, h => ⟨R, hl, hR, h⟩
  | r :: prog, R, R', hl, hR, h => by
    rw [runK_cons, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hk, h⟩ := h
    have hk' : opK r < R.length := hl ▸ hk
    have hrun : runA R' (r :: prog) = runA (stepA R' r) prog := rfl
    rw [hrun]
    cases h0 : Nat.beq (opC r) 0
    · rw [h0] at h
      cases h1 : Nat.beq (opC r) 1
      · rw [h1] at h
        cases h2 : Nat.beq (opC r) 2
        · rw [h2] at h
          exact absurd h Bool.false_ne_true
        · rw [h2] at h
          change (_ && _) = true at h
          rw [Bool.and_eq_true] at h
          have hst : stepA R' r = Function.update R' (opK r) (R' (opA r))⁻¹ := by
            unfold stepA
            rw [if_neg (Nat.ne_of_beq_eq_false h0), if_neg (Nat.ne_of_beq_eq_false h1)]
          rw [hst]
          refine runK_sim hsz nr H K prog _ _ (by rw [setR_eq, List.length_set, hl])
            (ps_update _ hk' (ps_inv (hR (opA r)) h.1) hR) h.2
      · rw [h1] at h
        have hst : stepA R' r = Function.update R' (opK r) (R' (opA r) ^ opB r) := by
          unfold stepA
          rw [if_neg (Nat.ne_of_beq_eq_false h0), if_pos (Nat.eq_of_beq_eq_true h1)]
        rw [hst]
        exact runK_sim hsz nr H K prog _ _ (by rw [setR_eq, List.length_set, hl])
          (ps_update _ hk' (ps_pow hsz (hR (opA r)) _) hR) h
    · rw [h0] at h
      have hst : stepA R' r = Function.update R' (opK r) (R' (opA r) * R' (opB r)) := by
        unfold stepA
        rw [if_pos (Nat.eq_of_beq_eq_true h0)]
      rw [hst]
      exact runK_sim hsz nr H K prog _ _ (by rw [setR_eq, List.length_set, hl])
        (ps_update _ hk' (ps_mul hsz (hR (opA r)) (hR (opB r))) hR) h

theorem neAll_sound (hsz : szOK n w = true) {f e : Nat} {F E : Equiv.Perm (Fin n)}
    (hF : PS n w f F) (hE : PS n w e E) :
    ∀ (c acc : Nat) (A : Equiv.Perm (Fin n)), PS n w acc A →
      neAll n w (mask w) f e c acc = true → ∀ k < c, F ≠ E ^ k * A
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | c + 1, acc, A, hA, h, k, hk => by
    rw [neAll_succ, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases k with _ | k
    · rw [pow_zero, one_mul]
      intro e'
      rw [ps_beq hsz hF hA, decide_eq_true e'] at h1
      exact absurd h1 Bool.false_ne_true
    · rw [pow_succ, mul_assoc]
      exact neAll_sound hsz hF hE c _ (E * A) (ps_mul hsz hE hA) h2 k (by omega)

theorem cgK_spec {A B : Nat} {a b : Equiv.Perm (Fin n)} (hA : PRep n w A a) (hB : PRep n w B b)
    {D : CGK} (h : cgK n w A B D = true) :
    ∃ e f s₁ s₂ : Equiv.Perm (Fin n),
      s₁ ∈ Subgroup.closure {a, b} ∧ s₂ ∈ Subgroup.closure {a, b} ∧
      e ∈ Subgroup.closure {a, b} ∧ f ∈ Subgroup.closure {a, b} ∧
      e ^ D.p = 1 ∧ f ^ D.p = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < D.p, f ≠ e ^ k) ∧
      s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ ∧
      a ∈ Subgroup.closure {s₁, s₂} ∧ b ∈ Subgroup.closure {s₁, s₂} := by
  unfold cgK at h
  simp only [sB, bA, Bool.and_eq_true] at h
  obtain ⟨hsz, hA0, hB0, h⟩ := h
  have psA : PS n w A a := ⟨hA, Nat.eq_of_beq_eq_true hA0⟩
  have psB : PS n w B b := ⟨hB, Nat.eq_of_beq_eq_true hB0⟩
  have hlen : ∀ (x y c : Nat), (initR x y c (pidn n w)).length = Nat.add c 2 := by
    intro x y c
    simp [initR, repR_eq]
  obtain ⟨R1, -, hR1, hfin⟩ := runK_sim hsz _ D.hints _ D.prog1 _ (initA a b) (hlen A B D.nx1)
    (ps_init hsz psA psB) h
  unfold finK at hfin
  simp only [sB, bA, bN, Bool.and_eq_true] at hfin
  obtain ⟨he, hf, hef, he1, hne, h2⟩ := hfin
  set S1 := runA (initA a b) D.prog1 D.is1 with hS1
  set S2 := runA (initA a b) D.prog1 D.is2 with hS2
  have p1 := hR1 D.is1
  have p2 := hR1 D.is2
  have pe := ps_pow hsz p1 D.ke
  have pf := ps_pow hsz p2 D.kf
  rw [ps_beq hsz (ps_pow hsz pe D.p) (ps_one hsz), decide_eq_true_iff] at he
  rw [ps_beq hsz (ps_pow hsz pf D.p) (ps_one hsz), decide_eq_true_iff] at hf
  rw [ps_beq hsz (ps_mul hsz pe pf) (ps_mul hsz pf pe), decide_eq_true_iff] at hef
  rw [ps_beq hsz pe (ps_one hsz), Bool.not_eq_true', decide_eq_false_iff_not] at he1
  have hgen : ∀ r, initA a b r ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) :=
    initA_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hs1 : S1 ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) :=
    runA_mem _ D.prog1 hgen D.is1
  have hs2 : S2 ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) :=
    runA_mem _ D.prog1 hgen D.is2
  obtain ⟨R2, -, hR2, hfin2⟩ := runK_sim hsz _ D.hints _ D.prog2 _ (initA S1 S2)
    (hlen _ _ D.nx2) (ps_init hsz p1 p2) h2
  simp only [bA, Bool.and_eq_true] at hfin2
  obtain ⟨hra, hrb⟩ := hfin2
  have hgen2 : ∀ r, initA S1 S2 r ∈ Subgroup.closure ({S1, S2} : Set (Equiv.Perm (Fin n))) :=
    initA_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have ea : runA (initA S1 S2) D.prog2 D.ra = a :=
    MOC.prep_unique (Nat.eq_of_beq_eq_true hra ▸ (hR2 D.ra).1) hA
  have eb : runA (initA S1 S2) D.prog2 D.rb = b :=
    MOC.prep_unique (Nat.eq_of_beq_eq_true hrb ▸ (hR2 D.rb).1) hB
  refine ⟨S1 ^ D.ke, S2 ^ D.kf, S1, S2, hs1, hs2, Subgroup.pow_mem _ hs1 _,
    Subgroup.pow_mem _ hs2 _, he, hf, hef, he1, fun k hk => ?_, (Commute.self_pow S1 D.ke).eq,
    (Commute.self_pow S2 D.kf).eq, ea ▸ runA_mem _ D.prog2 hgen2 D.ra,
    eb ▸ runA_mem _ D.prog2 hgen2 D.rb⟩
  simpa using neAll_sound hsz pf pe D.p _ 1 (ps_one hsz) hne k hk

end CFSG.KC.CentGenK

end
