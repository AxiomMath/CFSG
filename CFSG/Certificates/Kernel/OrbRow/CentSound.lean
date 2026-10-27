module

public import Certificates.Data.Kernel.OrbRow.Cent
public import CFSG.Certificates.Kernel.OrbRow.Sound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp CFSG.KS

theorem invsF_sound {n w m : ℕ} {c : List ℕ → Bool} :
    ∀ {S : List ℕ}, invsF n w m S c = true → ∃ L, c L = true
  | [], h => ⟨[], h⟩
  | s :: S, h => by
    have h' : strictB (CFSG.KS.pinvS n w m s)
        (fun si => invsF n w m S (fun L => c (List.cons si L))) = true := h
    have hs : ∀ y (k : ℕ → Bool), strictB y k = k y := by
      intro y k
      cases y <;> rfl
    rw [hs] at h'
    obtain ⟨L, hL⟩ := invsF_sound h'
    exact ⟨_, hL⟩

theorem memK_sound {x : ℕ} : ∀ {L : List ℕ}, memK x L = true → x ∈ L
  | [], h => absurd h Bool.false_ne_true
  | y :: L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memK x L) true (Nat.beq x y) = true := h
    by_cases hxy : x = y
    · exact hxy ▸ List.mem_cons_self
    · have hb : Nat.beq x y = false := by
        cases hh : Nat.beq x y
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hh) hxy
      rw [hb] at h'
      exact List.mem_cons_of_mem _ (memK_sound h')

theorem lettersK_sound {k lv : ℕ} : ∀ {wd : List ℕ}, lettersK k lv wd = true →
    ∀ j ∈ wd, j < k ∧ Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true
  | [], _, j, hj => absurd hj List.not_mem_nil
  | l :: wd, h, j, hj => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    rcases List.mem_cons.1 hj with rfl | hj
    · exact ⟨Nat.le_of_ble_eq_true h1, h2⟩
    · exact lettersK_sound h3 j hj

private theorem cent_beq (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem cent_blt (a b : ℕ) : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem memK_of_mem {x : ℕ} : ∀ {L : List ℕ}, x ∈ L → memK x L = true
  | [], h => absurd h List.not_mem_nil
  | y :: L, h => by
    have h' : memK x (y :: L) = Bool.rec (motive := fun _ => Bool) (memK x L) true (Nat.beq x y) :=
      rfl
    rw [h', PK.bIf_eq]
    by_cases hxy : x = y
    · rw [if_pos ((cent_beq _ _).2 hxy)]
    · rw [if_neg (fun hb => hxy ((cent_beq _ _).1 hb))]
      exact memK_of_mem ((List.mem_cons.1 h).resolve_left hxy)

private theorem cent_lenS : ∀ L : List ℕ, lenS L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (cent_lenS L)

private theorem cent_fpow (f : ℕ → ℕ) : ∀ (e q : ℕ), fpow f e q = f^[e] q
  | 0, _ => rfl
  | e + 1, q => by
    rw [Function.iterate_succ_apply, ← cent_fpow f e (f q)]
    change strictN (f q) (fpow f e) = _
    rw [PK.strictN_eq]

theorem fixSetK_sound {n w m x : ℕ} {F : List ℕ} (h : fixSetK n w m x F = true) {i : ℕ}
    (hi : i < n) : pg w m x i = i ↔ i ∈ F := by
  have h1 := allN_spec h i hi
  simp only [PK.bIf_eq] at h1
  by_cases hb : Nat.beq (pg w m x i) i = true
  · rw [if_pos hb] at h1
    exact ⟨fun _ => memK_sound h1, fun _ => (cent_beq _ _).1 hb⟩
  · rw [if_neg hb] at h1
    refine ⟨fun he => absurd ((cent_beq _ _).2 he) hb, fun hF => ?_⟩
    rw [if_pos (memK_of_mem hF)] at h1
    exact absurd h1 Bool.false_ne_true

theorem actFK_sound {w m x : ℕ} {B img : List ℕ} (h : actFK w m x B img = true) {t : ℕ}
    (ht : t < img.length) : pg w m x (getS B t) = getS B (getS img t) := by
  have h' : allN (lenS img)
      (fun t => Nat.beq (pg w m x (getS B t)) (getS B (getS img t))) = true := h
  rw [cent_lenS] at h'
  exact (cent_beq _ _).1 (allN_spec h' t ht)

theorem lvCommK_sound {n w m : ℕ} {S : List ℕ} {k lv x : ℕ} (h : lvCommK n w m S k lv x = true)
    {j : ℕ} (hj : lvOk k lv j) {i : ℕ} (hi : i < n) :
    pg w m (getS S j) (pg w m x i) = pg w m x (pg w m (getS S j) i) := by
  obtain ⟨hjk, hjb⟩ := lvOk_iff.1 hj
  have h1 := allN_spec h j hjk
  simp only [PK.bIf_eq] at h1
  rw [if_pos ((lvBit_iff _ _).2 hjb)] at h1
  exact (cent_beq _ _).1 (allN_spec h1 i hi)

theorem powIdK_sound {n w m x e : ℕ} (h : powIdK n w m x e = true) {i : ℕ} (hi : i < n) :
    (pg w m x)^[e] i = i := by
  rw [← cent_fpow]
  exact (cent_beq _ _).1 (allN_spec h i hi)

theorem movesK_sound {n w m x : ℕ} (h : movesK n w m x = true) : ∃ i < n, pg w m x i ≠ i := by
  have h' : Bool.rec (motive := fun _ => Bool) true false
      (allN n (fun i => Nat.beq (pg w m x i) i)) = true := h
  rw [PK.bIf_eq] at h'
  refine Classical.byContradiction fun hc => ?_
  have hc' : ∀ i < n, pg w m x i = i := fun i hi =>
    Classical.byContradiction fun hne => hc ⟨i, hi, hne⟩
  rw [if_pos (PK.allN_iff.2 fun i hi => (cent_beq _ _).2 (hc' i hi))] at h'
  exact absurd h' Bool.false_ne_true

inductive ActReach (act : ℕ → ℕ → ℕ) (k root : ℕ) : ℕ → Prop
  | root : ActReach act k root root
  | step {e j : ℕ} : ActReach act k root e → j < k → ActReach act k root (act j e)

private theorem cent_getS_mem : ∀ {L : List ℕ} {t : ℕ}, t < L.length → getS L t ∈ L
  | [], t, ht => absurd ht (Nat.not_lt_zero t)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: L, t + 1, ht => List.mem_cons_of_mem _ (cent_getS_mem (L := L) (by
      rw [List.length_cons] at ht
      omega))

private theorem cent_exists_getS {e : ℕ} : ∀ {L : List ℕ}, e ∈ L → ∃ t < L.length, getS L t = e
  | [], he => absurd he List.not_mem_nil
  | x :: L, he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨0, by rw [List.length_cons]; omega, rfl⟩
    · obtain ⟨t, ht, hte⟩ := cent_exists_getS he
      exact ⟨t + 1, by rw [List.length_cons]; omega, hte⟩

private theorem cent_recK {act : ℕ → ℕ → ℕ} {k fw fm root cnt : ℕ} {E RR : List ℕ} {e r : ℕ}
    (h : recK act k fw fm root cnt E RR e r = true) :
    (recDep fw r = 0 → e = root) ∧
      (recDep fw r ≠ 0 → ∃ par j, par < cnt ∧ j < k ∧
        recDep fw (getS RR par) + 1 = recDep fw r ∧ e = act j (getS E par)) ∧
      (∀ l < k, ∃ q < cnt, getS E q = act l e) := by
  unfold recK at h
  simp only [PK.strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [PK.bIf_eq] at h1
  refine ⟨fun hd => ?_, fun hd => ?_, fun l hl => ?_⟩
  · rw [if_pos ((cent_beq _ _).2 hd)] at h1
    exact (cent_beq _ _).1 h1
  · rw [if_neg (fun hb => hd ((cent_beq _ _).1 hb))] at h1
    obtain ⟨hp, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨hj, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨hdd, he⟩ := (bAnd_iff _ _).1 h1
    exact ⟨_, _, (cent_blt _ _).1 hp, (cent_blt _ _).1 hj, (cent_beq _ _).1 hdd,
      (cent_beq _ _).1 he⟩
  · obtain ⟨hq, hqe⟩ := (bAnd_iff _ _).1 (allN_spec h2 l hl)
    exact ⟨_, (cent_blt _ _).1 hq, (cent_beq _ _).1 hqe⟩

private theorem cent_recsFrom {act : ℕ → ℕ → ℕ} {ord : ℕ → ℕ} {k fw fm root cnt : ℕ}
    {E RR : List ℕ} : ∀ {Es Rs : List ℕ} {i prev : ℕ},
    recsFrom act ord k fw fm root cnt E RR Es Rs i prev = true →
      Es.length = Rs.length ∧ i + Es.length = cnt ∧ (Es.map ord).Pairwise (· < ·) ∧
        (i ≠ 0 → ∀ e ∈ Es, prev < ord e) ∧
        ∀ t < Es.length, recK act k fw fm root cnt E RR (getS Es t) (getS Rs t) = true
  | [], Rs, i, prev, h => by
    have h' : bAnd(Nat.beq i cnt,
        List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Rs) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    cases Rs with
    | nil =>
      refine ⟨rfl, ?_, List.Pairwise.nil, fun _ e he => absurd he List.not_mem_nil,
        fun t ht => absurd ht (Nat.not_lt_zero t)⟩
      rw [List.length_nil, Nat.add_zero]
      exact (cent_beq _ _).1 h1
    | cons r Rt => exact absurd h2 Bool.false_ne_true
  | e :: Es, Rs, i, prev, h => by
    cases Rs with
    | nil => exact absurd h Bool.false_ne_true
    | cons r Rt =>
      have h' : strictB (ord e) (fun oe => bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt prev oe),
          bAnd(recK act k fw fm root cnt E RR e r, strictB (Nat.succ i) fun i' =>
            recsFrom act ord k fw fm root cnt E RR Es Rt i' oe))) = true := h
      simp only [PK.strictB_eq] at h'
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
      obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
      obtain ⟨hl, hc, hs, hp, hr⟩ := cent_recsFrom h3
      refine ⟨by rw [List.length_cons, List.length_cons, hl], by rw [List.length_cons]; omega,
        ?_, ?_, ?_⟩
      · rw [List.map_cons, List.pairwise_cons]
        refine ⟨fun b hb => ?_, hs⟩
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
        exact hp (Nat.succ_ne_zero i) e' he'
      · intro hi e' he'
        have hlt : prev < ord e := by
          rw [PK.bIf_eq, if_neg (fun hb => hi ((cent_beq _ _).1 hb))] at h1
          exact (cent_blt _ _).1 h1
        rcases List.mem_cons.1 he' with rfl | he'
        · exact hlt
        · exact Nat.lt_trans hlt (hp (Nat.succ_ne_zero i) e' he')
      · intro t ht
        cases t with
        | zero => exact h2
        | succ t =>
          exact hr t (by
            rw [List.length_cons] at ht
            omega)

theorem orbRecK_sound {act : ℕ → ℕ → ℕ} {ord : ℕ → ℕ} {k fw fm root cnt : ℕ} {E RR : List ℕ}
    (h : orbRecK act ord k fw fm root cnt E RR = true) :
    E.length = cnt ∧ (E.map ord).Nodup ∧ (0 < cnt → root ∈ E) ∧
      (∀ e ∈ E, ∀ j < k, act j e ∈ E) ∧ ∀ e ∈ E, ActReach act k root e := by
  obtain ⟨hlen, hcnt, hsort, -, hrec⟩ := cent_recsFrom h
  rw [Nat.zero_add] at hcnt
  have hrec' : ∀ t < cnt, recK act k fw fm root cnt E RR (getS E t) (getS RR t) = true :=
    fun t ht => hrec t (by omega)
  refine ⟨hcnt, hsort.imp (fun h => Nat.ne_of_lt h), fun hc => ?_, ?_, ?_⟩
  ·
    have key : ∀ d, ∀ t < cnt, recDep fw (getS RR t) = d → root ∈ E := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro t ht hd
        obtain ⟨h0, h1, -⟩ := cent_recK (hrec' t ht)
        by_cases hd0 : recDep fw (getS RR t) = 0
        · rw [← h0 hd0]
          exact cent_getS_mem (by omega)
        · obtain ⟨par, j, hpar, -, hdep, -⟩ := h1 hd0
          exact ih _ (by omega) par hpar rfl
    exact key _ 0 hc rfl
  · intro e he j hj
    obtain ⟨t, ht, rfl⟩ := cent_exists_getS he
    obtain ⟨-, -, h2⟩ := cent_recK (hrec' t (by omega))
    obtain ⟨q, hq, hqe⟩ := h2 j hj
    rw [← hqe]
    exact cent_getS_mem (by omega)
  · have key : ∀ d, ∀ t < cnt, recDep fw (getS RR t) = d → ActReach act k root (getS E t) := by
      intro d
      induction d with
      | zero =>
        intro t ht hd
        obtain ⟨h0, -, -⟩ := cent_recK (hrec' t ht)
        rw [h0 hd]
        exact ActReach.root
      | succ d ih =>
        intro t ht hd
        obtain ⟨-, h1, -⟩ := cent_recK (hrec' t ht)
        obtain ⟨par, j, hpar, hj, hdep, he⟩ := h1 (by omega)
        rw [he]
        exact ActReach.step (ih par hpar (by omega)) hj
    intro e he
    obtain ⟨t, ht, rfl⟩ := cent_exists_getS he
    exact key _ t (by omega) rfl

theorem normK_sound {n w m : ℕ} {G : ℕ → ℕ} {k x : ℕ} {B : List ℕ} {off nf : ℕ} {RK : List ℕ}
    (h : normK n w m G k x B off nf RK = true) :
    permOK n w m (n * w) x (CFSG.KS.pinvS n w m x) = true ∧
      ∀ j < k, conjKey w m x (CFSG.KS.pinvS n w m x) (G j) B off nf ∈ RK := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (allN k (fun j => memK (conjKey w m x (CFSG.KS.pinvS n w m x) (G j) B off nf) RK))
      (permOK n w m (Nat.mul n w) x (CFSG.KS.pinvS n w m x)) = true := by
    have h0 := h
    unfold normK at h0
    rwa [PK.strictB_eq] at h0
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
  exact ⟨h1, fun j hj => memK_sound (allN_spec h2 j hj)⟩

end CFSG.KC.OrbRow

end
