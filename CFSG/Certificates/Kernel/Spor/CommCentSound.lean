module

public import Certificates.Data.Kernel.Spor.CommCent
public import CFSG.Certificates.Kernel.Spor.CommBaseSound

public section

namespace CFSG.KC.CommBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w nL : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)}

theorem sumBelow_eq_sum (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    CFSG.KC.Loop.sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have hgen : ∀ h, CFSG.KC.Loop.sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + CFSG.KC.Loop.sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
        omega
      simp only [e, nIf_eq, Nat.blt_eq]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem le_hi (n : ℕ) : n ≤ 64 * Nat.add (Nat.shiftRight n 6) 1 := by
  change n ≤ 64 * (n >>> 6 + 1)
  rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 6 = 64 from rfl]
  omega

theorem sumBelow_card (f : ℕ → Bool) :
    CFSG.KC.Loop.sumBelow n (Nat.add (Nat.shiftRight n 6) 1) (fun p => nIf(f p, 1, 0)) =
      (Finset.univ.filter fun p : Fin n => f p = true).card := by
  rw [sumBelow_eq_sum _ _ _ (le_hi n), Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun p => nIf(f p, 1, 0)) n]
  exact Finset.sum_congr rfl fun p _ => nIf_eq _ _ _

theorem cntR_eq (RF b : ℕ) :
    cntR n w (mask w) RF b = (Finset.univ.filter fun p : Fin n => pg w (mask w) RF p = b).card := by
  rw [cntR, sumBelow_card]
  exact congrArg Finset.card (Finset.filter_congr fun p _ => by rw [Nat.beq_eq])

theorem fixCnt_eq {P : ℕ} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) :
    fixCnt n w (mask w) P = (Finset.univ.filter fun p => g p = p).card := by
  rw [fixCnt, sumBelow_card]
  refine congrArg Finset.card (Finset.filter_congr fun p _ => ?_)
  rw [Nat.beq_eq, hP p, Fin.val_inj]

theorem memL_iff {v : ℕ} {Ts : List ℕ} : memL v Ts = true ↔ v ∈ Ts := by
  rw [memL, anyL_iff]
  constructor
  · rintro ⟨t, ht, e⟩
    rwa [← Nat.eq_of_beq_eq_true e]
  · exact fun h => ⟨v, h, Nat.beq_refl v⟩

theorem choose_of_baseOK (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) {r : BaseRec} (h : baseOK n w (mask w) L nL r = true) :
    ∃ hb : r.1 < n, ∀ f : ℕ → Bool, chooseL r f = true → f (x ⟨r.1, hb⟩) = true := by
  obtain ⟨b, ss, ex, sw, pr⟩ := r
  change baseOKc n w (mask w) L nL b ss ex sw pr = true at h
  unfold baseOKc at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hb, -, hss, hsb, hex, -, hall⟩ := h
  rw [Nat.blt_eq] at hb
  rw [allL_iff] at hss hsb hex
  rw [allN_iff] at hall
  replace hss : ∀ s ∈ ss, ∀ z ∈ s, z < nL := fun s hs => lettersOK_iff.1 (hss s hs)
  replace hsb : ∀ s ∈ ss, wapp w (mask w) L s b = b := fun s hs =>
    Nat.eq_of_beq_eq_true (hsb s hs)
  replace hex : ∀ e ∈ ex, e.2 < nL ∧ pg w (mask w) (L e.2) b ≠ b ∧
      pg w (mask w) (L e.2) e.1 = e.1 := fun e he => by
    have := hex e he
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, Nat.ne_of_beq_eq_false (notB_true this.2.1),
      Nat.eq_of_beq_eq_true this.2.2⟩
  replace hall : ∀ y < n, fixAll w (mask w) L ss y = true → allowed b ex sw pr y = true :=
    fun y hy hf => by
      have := hall y hy
      rwa [bIf_eqC, if_pos hf] at this
  refine ⟨hb, fun f hf => ?_⟩
  change bAnd(f b, bIf(Nat.beq pr b, allL (fun s : ℕ × List ℕ => f s.1) sw, f pr)) = true at hf
  rw [bAnd_eq, Bool.and_eq_true, bIf_eqC] at hf
  set B : Fin n := ⟨b, hb⟩
  have hS : ∀ s ∈ ss, word ℓ s B = B := fun s hs =>
    Fin.ext (by rw [← wapp_eq hL (hss s hs)]; exact hsb s hs)
  have hSc : ∀ s ∈ ss, Commute x (word ℓ s) := fun s hs => commute_word hx (hss s hs)
  have hc : ∀ s ∈ ss, word ℓ s (x B) = x B := fun s hs => by
    rw [← comm_apply (hSc s hs), hS s hs]
  have hf' : fixAll w (mask w) L ss (x B) = true := by
    rw [fixAll, allL_iff]
    intro s hs
    rw [Nat.beq_eq, wapp_eq hL (hss s hs), hc s hs]
  rcases allowed_cases (hall (x B) (x B).2 hf') with h1 | ⟨hpr, ⟨e, he, he1⟩ | ⟨t, ht, ht1⟩⟩ |
      ⟨hne, h1⟩
  · rw [h1]
    exact hf.1
  · exfalso
    obtain ⟨hz, hmove, hfixe⟩ := hex e he
    have hmove' : ℓ e.2 B ≠ B := fun hc => hmove ((hL e.2 hz B).trans (congrArg Fin.val hc))
    have hfix' : ℓ e.2 (x B) = x B := Fin.ext (by rw [← hL e.2 hz, ← he1]; exact hfixe)
    apply hmove'
    apply x.injective
    rw [comm_apply (hx e.2 hz), hfix']
  · rw [if_pos (by rw [Nat.beq_eq]; exact hpr), allL_iff] at hf
    rw [← ht1]
    exact hf.2 t ht
  · rw [if_neg (by rw [Nat.beq_eq]; exact hne)] at hf
    rw [h1]
    exact hf.2

theorem root_spec (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {B : List BaseRec} {PF ZF DF RF : ℕ}
    (hF : forestOK n w (mask w) L nL B PF ZF DF = true) (hR : rootOK n w (mask w) PF RF = true)
    (p : Fin n) : ∃ r ∈ B, ∃ hb : r.1 < n, pg w (mask w) RF p = r.1 ∧
      ∀ X : Equiv.Perm (Fin n), (∀ z < nL, Commute X (ℓ z)) →
        (X p = p ↔ X ⟨r.1, hb⟩ = ⟨r.1, hb⟩) := by
  rw [forestOK, allN_iff] at hF
  rw [rootOK, allN_iff] at hR
  have key : ∀ d, ∀ p : Fin n, pg w (mask w) DF p = d → ∃ r ∈ B, ∃ hb : r.1 < n,
      pg w (mask w) RF p = r.1 ∧ ∀ X : Equiv.Perm (Fin n), (∀ z < nL, Commute X (ℓ z)) →
        (X p = p ↔ X ⟨r.1, hb⟩ = ⟨r.1, hb⟩) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp
      have hq := hF p p.2
      have hr := hR p p.2
      rw [strictB_eq, bIf_eqC] at hq hr
      by_cases hqp : Nat.beq (pg w (mask w) PF p) p = true
      · rw [if_pos hqp, anyL_iff] at hq
        rw [if_pos hqp] at hr
        obtain ⟨r, hrB, hr1⟩ := hq
        have e : r.1 = p := Nat.eq_of_beq_eq_true hr1
        have hp' : (⟨r.1, e ▸ p.2⟩ : Fin n) = p := Fin.ext e
        refine ⟨r, hrB, e ▸ p.2, (Nat.eq_of_beq_eq_true hr).trans e.symm, fun X _ => ?_⟩
        rw [hp']
      · rw [if_neg hqp, bAnd_eq, Bool.and_eq_true, strictB_eq, bAnd_eq, bAnd_eq,
          Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at hq
        rw [if_neg hqp] at hr
        obtain ⟨hqn, hz, hd, hl⟩ := hq
        replace hl := Nat.eq_of_beq_eq_true hl
        set q : Fin n := ⟨pg w (mask w) PF p, hqn⟩
        have hlq : ℓ (pg w (mask w) ZF p) q = p := Fin.ext (by rw [← hL _ hz]; exact hl)
        obtain ⟨r, hrB, hb, hRq, hX⟩ := ih _ (hp ▸ hd) q rfl
        refine ⟨r, hrB, hb, (Nat.eq_of_beq_eq_true hr).trans hRq, fun X hXc => ?_⟩
        rw [← hX X hXc, ← hlq, comm_apply (hXc _ hz)]
        exact (ℓ _).injective.eq_iff
  exact key _ p rfl

theorem distOK_iff {B : List BaseRec} : distOK B = true ↔ B.Pairwise fun r s => r.1 ≠ s.1 := by
  induction B with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | cons r rs ih =>
    change bAnd(allL (fun s : BaseRec => notB (Nat.beq r.1 s.1)) rs, distOK rs) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.pairwise_cons, allL_iff]
    refine and_congr_left' (forall₂_congr fun s _ => ?_)
    constructor
    · intro h e
      have := notB_true h
      rw [e, Nat.beq_refl] at this
      exact Bool.noConfusion this
    · intro h
      have : Nat.beq r.1 s.1 = false :=
        Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
      rw [this]
      rfl

theorem card_filter_exists {α β : Type} [Fintype α] [DecidableEq α] (f : α → ℕ) (key : β → ℕ) (Q : β → Prop)
    [DecidablePred Q] :
    ∀ B : List β, B.Pairwise (fun r s => key r ≠ key s) →
      (Finset.univ.filter fun a => ∃ r ∈ B, f a = key r ∧ Q r).card =
        (B.map fun r => if Q r then (Finset.univ.filter fun a => f a = key r).card else 0).sum
  | [], _ => by simp
  | r :: rs, hB => by
    rw [List.pairwise_cons] at hB
    rw [List.map_cons, List.sum_cons, ← card_filter_exists f key Q rs hB.2]
    have e : (Finset.univ.filter fun a => ∃ s ∈ r :: rs, f a = key s ∧ Q s) =
        (Finset.univ.filter fun a => f a = key r ∧ Q r) ∪
          (Finset.univ.filter fun a => ∃ s ∈ rs, f a = key s ∧ Q s) := by
      rw [← Finset.filter_or]
      exact Finset.filter_congr fun a _ => by
        simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    rw [e, Finset.card_union_of_disjoint]
    · congr 1
      by_cases hq : Q r
      · rw [if_pos hq]
        exact congrArg Finset.card (Finset.filter_congr fun a _ => and_iff_left hq)
      · rw [if_neg hq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun a _ h => hq h.2
    · rw [Finset.disjoint_filter]
      rintro a - ⟨h1, -⟩ ⟨s, hs, h2, -⟩
      exact hB.1 s hs (h1.symm.trans h2)

theorem card_fix_eq (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {B : List BaseRec} {PF ZF DF RF : ℕ}
    (hF : forestOK n w (mask w) L nL B PF ZF DF = true) (hR : rootOK n w (mask w) PF RF = true)
    (hD : distOK B = true) {X : Equiv.Perm (Fin n)} (hX : ∀ z < nL, Commute X (ℓ z))
    (Q : BaseRec → Prop) [DecidablePred Q]
    (hQ : ∀ r ∈ B, ∀ hb : r.1 < n, (X ⟨r.1, hb⟩ = ⟨r.1, hb⟩ ↔ Q r)) :
    (Finset.univ.filter fun p => X p = p).card =
      (B.map fun r => if Q r then cntR n w (mask w) RF r.1 else 0).sum := by
  have e : (Finset.univ.filter fun p => X p = p) =
      Finset.univ.filter fun p : Fin n => ∃ r ∈ B, pg w (mask w) RF p = r.1 ∧ Q r := by
    refine Finset.filter_congr fun p _ => ?_
    obtain ⟨r, hrB, hb, hRp, hXp⟩ := root_spec hL hF hR p
    rw [hXp X hX, hQ r hrB hb]
    constructor
    · exact fun h => ⟨r, hrB, hRp, h⟩
    · rintro ⟨s, hs, h1, h2⟩
      have e : r = s := by
        by_contra hne
        have hrs : r.1 = s.1 := hRp.symm.trans h1
        rcases List.mem_iff_get.1 hrB with ⟨i, rfl⟩
        rcases List.mem_iff_get.1 hs with ⟨j, rfl⟩
        have hij : i ≠ j := fun h => hne (h ▸ rfl)
        have hP := (distOK_iff.1 hD)
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
        · exact List.pairwise_iff_get.1 hP i j h hrs
        · exact List.pairwise_iff_get.1 hP j i h hrs.symm
      exact e ▸ h2
  rw [e, card_filter_exists (fun p : Fin n => pg w (mask w) RF p) Prod.fst Q B (distOK_iff.1 hD)]
  congr 1
  exact List.map_congr_left fun r _ => by rw [cntR_eq]

theorem enumOK_sound {m t RF : ℕ} {Ts : List ℕ} (y : ℕ → ℕ) :
    ∀ (rs : List BaseRec) (fa fb : ℕ) (aA aB : Bool), enumOK n w m t RF Ts rs fa fb aA aB = true →
      (∀ r ∈ rs, ∀ f : ℕ → Bool, chooseL r f = true → f (y r.1) = true) →
      enumOK n w m t RF Ts []
        (fa + (rs.map fun r => if y r.1 = r.1 then cntR n w m RF r.1 else 0).sum)
        (fb + (rs.map fun r => if pg w m t (y r.1) = r.1 then cntR n w m RF r.1 else 0).sum)
        (aA && rs.all fun r => Nat.beq (y r.1) r.1)
        (aB && rs.all fun r => Nat.beq (pg w m t (y r.1)) r.1) = true
  | [], fa, fb, aA, aB, h, _ => by simpa using h
  | r :: rs, fa, fb, aA, aB, h, hy => by
    change strictB (cntR n w m RF r.1) (fun c => chooseL r (fun y =>
      enumOK n w m t RF Ts rs (Nat.add fa (nIf(Nat.beq y r.1, c, 0)))
        (Nat.add fb (nIf(Nat.beq (pg w m t y) r.1, c, 0)))
        (bAnd(aA, Nat.beq y r.1)) (bAnd(aB, Nat.beq (pg w m t y) r.1)))) = true at h
    rw [strictB_eq] at h
    have h1 := hy r List.mem_cons_self _ h
    have h2 := enumOK_sound y rs _ _ _ _ h1 fun s hs => hy s (List.mem_cons_of_mem r hs)
    simp only [bAnd_eq, nIf_eq, Nat.beq_eq] at h2
    convert h2 using 2
    · simp only [List.map_cons, List.sum_cons]
      split_ifs <;> simp [Nat.add_assoc]
    · simp only [List.map_cons, List.sum_cons]
      split_ifs <;> simp [Nat.add_assoc]
    · simp only [List.all_cons, Nat.beq_eq, Bool.and_assoc]
    · simp only [List.all_cons, Nat.beq_eq, Bool.and_assoc]

theorem eq_one_or_of_centFixOK (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) {tI : ℕ} (hτ : ∀ z < nL, Commute (ℓ tI) (ℓ z))
    (hxx : x * x = 1) {Ts : List ℕ}
    (hT : ∀ y : Equiv.Perm (Fin n), (y = x ∨ y = x * ℓ tI) → y ≠ 1 →
      (Finset.univ.filter fun p => y p = p).card ∈ Ts)
    {B : List BaseRec} {PF ZF DF RF : ℕ}
    (h : centFixOK n w (mask w) L nL tI B PF ZF DF RF Ts = true) : x = 1 ∨ x = ℓ tI := by
  unfold centFixOK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hCB, htI, hR, hD, hE⟩ := h
  rw [Nat.blt_eq] at htI
  rw [commBaseOK, bAnd_eq, Bool.and_eq_true, allL_iff] at hCB
  obtain ⟨hBase, hF⟩ := hCB
  set τ := ℓ tI
  have hτL : PRep n w (L tI) τ := hL tI htI
  have hy : ∀ z < nL, Commute (x * τ) (ℓ z) := fun z hz => (hx z hz).mul_left (hτ z hz)
  let yv : ℕ → ℕ := fun b => if hb : b < n then (x ⟨b, hb⟩ : ℕ) else b
  have hyv : ∀ r ∈ B, ∀ hb : r.1 < n, yv r.1 = x ⟨r.1, hb⟩ := fun r _ hb => dif_pos hb
  have hch : ∀ r ∈ B, ∀ f : ℕ → Bool, chooseL r f = true → f (yv r.1) = true := by
    intro r hr f hf
    obtain ⟨hb, hc⟩ := choose_of_baseOK hL hx (hBase r hr)
    rw [hyv r hr hb]
    exact hc f hf
  have hE' := enumOK_sound yv B 0 0 true true hE hch
  change bIf(true && _, true, bIf(true && _, true, notB (bAnd(memL _ Ts, memL _ Ts)))) = true
    at hE'
  rw [bIf_eqC, bIf_eqC, Bool.true_and, Bool.true_and, bAnd_eq] at hE'
  have hQA : ∀ r ∈ B, ∀ hb : r.1 < n, (x ⟨r.1, hb⟩ = ⟨r.1, hb⟩ ↔ yv r.1 = r.1) :=
    fun r hr hb => by rw [hyv r hr hb, Fin.ext_iff]
  have hQB : ∀ r ∈ B, ∀ hb : r.1 < n,
      ((x * τ) ⟨r.1, hb⟩ = ⟨r.1, hb⟩ ↔ pg w (mask w) (L tI) (yv r.1) = r.1) := fun r hr hb => by
    rw [Equiv.Perm.mul_apply, comm_apply (hx tI htI), hyv r hr hb, hτL, Fin.ext_iff]
  have cA := card_fix_eq hL hF hR hD hx _ hQA
  have cB := card_fix_eq hL hF hR hD hy _ hQB
  have fixAll : ∀ X : Equiv.Perm (Fin n), (∀ z < nL, Commute X (ℓ z)) →
      (∀ r ∈ B, ∀ hb : r.1 < n, X ⟨r.1, hb⟩ = ⟨r.1, hb⟩) → X = 1 :=
    fun X hX hB => eq_one_of_forestOK hL hX hF hB
  have hxτ : x * τ = 1 → x = τ := fun e => by
    have h1 : x = τ⁻¹ := eq_inv_of_mul_eq_one_left e
    have h2 : x = x⁻¹ := eq_inv_of_mul_eq_one_left hxx
    rw [h2, h1, inv_inv]
  by_cases hA : B.all (fun r => Nat.beq (yv r.1) r.1) = true
  · left
    refine fixAll x hx fun r hr hb => (hQA r hr hb).2 ?_
    exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 hA r hr)
  rw [if_neg hA] at hE'
  by_cases hB : B.all (fun r => Nat.beq (pg w (mask w) (L tI) (yv r.1)) r.1) = true
  · right
    refine hxτ (fixAll _ hy fun r hr hb => (hQB r hr hb).2 ?_)
    exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 hB r hr)
  rw [if_neg hB] at hE'
  by_cases h1 : x = 1
  · exact Or.inl h1
  by_cases h2 : x * τ = 1
  · exact Or.inr (hxτ h2)
  exfalso
  have m1 := hT x (Or.inl rfl) h1
  have m2 := hT (x * τ) (Or.inr rfl) h2
  rw [cA, Nat.zero_add] at *
  rw [cB] at m2
  have := notB_true hE'
  rw [Bool.and_eq_false_iff] at this
  simp only [Nat.zero_add] at this
  rcases this with e | e
  · exact absurd (memL_iff.2 m1) (by rw [e]; exact Bool.false_ne_true)
  · exact absurd (memL_iff.2 m2) (by rw [e]; exact Bool.false_ne_true)

end CFSG.KC.CommBase

end
