module

public import CFSG.Certificates.Kernel.LocalQTPipeCosetBfs
public import CFSG.Certificates.Kernel.LocalQTPipeBasic

public section

namespace CFSG.KC.LQT.PPC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PPB
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem f2_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hr hl, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hab⟩ := f2_mem_left hl h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem f2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hr hl, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, hab⟩ := f2_mem_right hl h
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem f2_map {α : Type} {R : Nat → Array Nat → Prop} (l : List α) (f : α → Nat)
    (g : α → Array Nat) (h : ∀ x ∈ l, R (f x) (g x)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons x t ih =>
    exact List.Forall₂.cons (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

@[expose] def MaskOf (N : Nat) (ts : List (Array Nat)) (B : Nat) : Prop :=
  ∀ i, B.testBit i = true ↔ (i < N ∧ Reach ts 0 i)

noncomputable def smallLoop (N W : Nat) (GS : List Nat) (PT : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun seen => Nat.blt 0 (lenA seen))
    (fun p _ ih seen => andB
      (List.rec (motive := fun _ => Bool) (Nat.beq p 0)
        (fun _ _ _ => anyL seen fun q => anyL GS fun g => Nat.beq (imgW W g q) p) seen)
      (ih (List.cons p seen))) PT

theorem smallLoop_spec {N W : Nat} {GS : List Nat} {ts : List (Array Nat)}
    (hcodes' : ∀ g ∈ GS, ∃ t ∈ ts, ∀ x < N, imgW W g x = arrImg t x) :
    ∀ (PT seen : List Nat), (∀ x ∈ seen ++ PT, x < N) → smallLoop N W GS PT seen = true →
      (∀ q ∈ seen, Reach ts 0 q) → (∀ p ∈ PT, Reach ts 0 p) ∧ (seen = [] → ∃ t, PT = 0 :: t)
  | [], seen, _, h, _ => by
    have e : smallLoop N W GS [] seen = Nat.blt 0 (lenA seen) := rfl
    rw [e, blt_iff, lenA_eq] at h
    refine ⟨by simp, fun hs => ?_⟩
    subst hs
    simp at h
  | p :: t, seen, hlt, h, hseen => by
    have e : smallLoop N W GS (p :: t) seen = andB
        (List.rec (motive := fun _ => Bool) (Nat.beq p 0)
          (fun _ _ _ => anyL seen fun q => anyL GS fun g => Nat.beq (imgW W g q) p) seen)
        (smallLoop N W GS t (p :: seen)) := rfl
    rw [e, andB_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hp : Reach ts 0 p ∧ (seen = [] → p = 0) := by
      cases seen with
      | nil =>
        have h1' : Nat.beq p 0 = true := h1
        have hp0 := beq_iff.1 h1'
        subst hp0
        exact ⟨Reach.base, fun _ => rfl⟩
      | cons q s =>
        have h1' : anyL (q :: s) (fun q => anyL GS fun g => Nat.beq (imgW W g q) p) = true := h1
        rw [anyL_iff] at h1'
        obtain ⟨q', hq', hq''⟩ := h1'
        rw [anyL_iff] at hq''
        obtain ⟨g, hg, hgq⟩ := hq''
        obtain ⟨t', ht', hcode⟩ := hcodes' g hg
        have hqN : q' < N := hlt q' (List.mem_append_left _ hq')
        have := Reach.step t' ht' (hseen q' hq')
        rw [← hcode q' hqN, beq_iff.1 hgq] at this
        exact ⟨this, fun h => by simp at h⟩
    have hlt' : ∀ x ∈ (p :: seen) ++ t, x < N := by
      intro x hx
      apply hlt
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
    have := smallLoop_spec hcodes' t (p :: seen) hlt' h2 (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp.1
      · exact hseen q hq)
    refine ⟨fun x hx => ?_, fun hs => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact hp.1
      · exact this.1 x hx
    · exact ⟨t, by rw [hp.2 hs]⟩

theorem smallK_sound {N W : Nat} {GS : List Nat} {ts : List (Array Nat)}
    (hgt : ∀ g ∈ GS, ∃ t ∈ ts, ∀ x < N, imgW W g x = arrImg t x)
    (htg : ∀ t ∈ ts, ∃ g ∈ GS, ∀ x < N, imgW W g x = arrImg t x) {B : Nat} {C : List Nat}
    (h : smallK N W GS B C = true) : MaskOf N ts B := by
  unfold smallK at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hB := beq_iff.1 h1
  rw [allL_iff] at h2 h3
  have hlt : ∀ x ∈ C, x < N := fun x hx => blt_iff.1 (h2 x hx)
  have h4' : smallLoop N W GS C [] = true := h4
  obtain ⟨hr, hz⟩ := smallLoop_spec hgt C [] (by simpa using hlt) h4' (by simp)
  obtain ⟨t, ht⟩ := hz rfl
  have hmem : ∀ i, B.testBit i = true ↔ i ∈ C := by
    intro i; rw [← hB, maskL_testBit]
  intro i
  rw [hmem]
  constructor
  · intro hi
    exact ⟨hlt i hi, hr i hi⟩
  · rintro ⟨hiN, hri⟩
    have : ∀ j, Reach ts 0 j → j ∈ C := by
      intro j hj
      induction hj with
      | base => rw [ht]; exact List.mem_cons_self
      | step t' ht' hj ih =>
        have hjN := hlt _ ih
        obtain ⟨g, hg, hcode⟩ := htg t' ht'
        have h5 := allL_iff _ _ |>.1 (h3 _ ih) g hg
        rw [bitK_eq, hcode _ hjN, hmem] at h5
        exact h5
    exact this i hri

noncomputable def fullLoop (N W : Nat) (GS : List Nat) (RPK : Nat) (REPS : List Nat)
    (E : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun QV => Nat.beq QV (maskL REPS))
    (fun e _ ih QV => CFSG.KC.LQT.P.letB (Nat.shiftRight e 3) fun y =>
      CFSG.KC.LQT.P.letB (Nat.land e 7) fun g =>
      andB (andB (Nat.blt y N) (andB (Nat.blt g (lenA GS)) (PP.bitK QV (imgW W RPK y))))
        (ih (Nat.lor QV (Nat.shiftLeft 1 (imgW W RPK (imgW W (getK GS g) y))))))
    E

theorem fullLoop_spec {N W : Nat} {GS : List Nat} {ts : List (Array Nat)} {RPK : Nat}
    {repR : Array Nat} {REPS : List Nat} (hN : 0 < N) (hRP : Rep N W RPK repR)
    (hRO : ∀ i < N, Reach ts (repR.getD i 0) i)
    (hgt : ∀ g ∈ GS, ∃ t ∈ ts, ∀ x < N, imgW W g x = arrImg t x)
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N)
    (hinj : ∀ t ∈ ts, ∀ i < N, ∀ j < N, arrImg t i = arrImg t j → i = j) :
    ∀ (E : List Nat) (QV : Nat), fullLoop N W GS RPK REPS E QV = true →
      (∀ r, QV.testBit r = true → Reach ts 0 r) → ∀ r ∈ REPS, Reach ts 0 r
  | [], QV, h, hQ, r, hr => by
    have e : fullLoop N W GS RPK REPS [] QV = Nat.beq QV (maskL REPS) := rfl
    rw [e, beq_iff] at h
    exact hQ r (by rw [h, maskL_testBit]; exact hr)
  | e0 :: E, QV, h, hQ, r, hr => by
    have e : fullLoop N W GS RPK REPS (e0 :: E) QV =
        andB (andB (Nat.blt (Nat.shiftRight e0 3) N) (andB (Nat.blt (Nat.land e0 7) (lenA GS))
          (PP.bitK QV (imgW W RPK (Nat.shiftRight e0 3)))))
          (fullLoop N W GS RPK REPS E (Nat.lor QV (Nat.shiftLeft 1
            (imgW W RPK (imgW W (getK GS (Nat.land e0 7)) (Nat.shiftRight e0 3)))))) := by
      have e0' : fullLoop N W GS RPK REPS (e0 :: E) QV =
        CFSG.KC.LQT.P.letB (Nat.shiftRight e0 3) fun y =>
        CFSG.KC.LQT.P.letB (Nat.land e0 7) fun g =>
        andB (andB (Nat.blt y N) (andB (Nat.blt g (lenA GS)) (PP.bitK QV (imgW W RPK y))))
          (fullLoop N W GS RPK REPS E
            (Nat.lor QV (Nat.shiftLeft 1 (imgW W RPK (imgW W (getK GS g) y))))) := rfl
      rw [e0', letB_eq, letB_eq]
    rw [e] at h
    generalize Nat.shiftRight e0 3 = y at h
    generalize Nat.land e0 7 = g at h
    rw [andB_iff, andB_iff, andB_iff, blt_iff, blt_iff, bitK_eq, lenA_eq] at h
    obtain ⟨⟨hy, hg, hbit⟩, hrest⟩ := h
    refine fullLoop_spec hN hRP hRO hgt htab hinj E _ hrest ?_ r hr
    intro r' hr'
    have hrd : ∀ i < N, imgW W RPK i = repR.getD i 0 := fun i hi => (hRP.2 i hi).2
    have hry := hQ _ hbit
    rw [hrd y hy] at hry
    have hGg : getK GS g ∈ GS := by
      rw [getK_eq, List.getD_eq_getElem _ _ hg]; exact List.getElem_mem hg
    obtain ⟨t, ht, hcode⟩ := hgt _ hGg
    have hz : imgW W (getK GS g) y = arrImg t y := hcode y hy
    have hzN : arrImg t y < N := htab t ht y hy
    have h1 : Reach ts 0 (arrImg t y) :=
      Reach.step t ht (reach_trans hry (hRO y hy))
    have hrzN : repR.getD (arrImg t y) 0 < N := (hRP.2 _ hzN).1
    have h2 := reach_symm htab hinj hrzN (hRO _ hzN)
    have h3 := reach_trans h1 h2
    have hr'' : (QV ||| Nat.shiftLeft 1 (imgW W RPK (imgW W (getK GS g) y))).testBit r' = true :=
      hr'
    rw [Nat.testBit_or, Bool.or_eq_true] at hr''
    rcases hr'' with h4 | h4
    · exact hQ r' h4
    · rw [shiftLeft_one, Nat.testBit_two_pow] at h4
      have h5 : r' = imgW W RPK (imgW W (getK GS g) y) := by simpa [eq_comm] using h4
      rw [h5, hz, hrd _ hzN]
      exact h3

theorem fullK_sound {N W : Nat} {GS : List Nat} {ts : List (Array Nat)} {RPK : Nat}
    {repR : Array Nat} {REPS E : List Nat} (hN : 0 < N) (hRP : Rep N W RPK repR)
    (hRO : ∀ i < N, Reach ts (repR.getD i 0) i) (hRREPS : ∀ i < N, repR.getD i 0 ∈ REPS)
    (hgt : ∀ g ∈ GS, ∃ t ∈ ts, ∀ x < N, imgW W g x = arrImg t x)
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N)
    (hinj : ∀ t ∈ ts, ∀ i < N, ∀ j < N, arrImg t i = arrImg t j → i = j)
    (h : fullK N W GS RPK REPS E = true) : ∀ i < N, Reach ts 0 i := by
  have h' : fullLoop N W GS RPK REPS E (Nat.shiftLeft 1 (imgW W RPK 0)) = true := h
  have hrd : ∀ i < N, imgW W RPK i = repR.getD i 0 := fun i hi => (hRP.2 i hi).2
  have h0 : Reach ts 0 (repR.getD 0 0) :=
    reach_symm htab hinj (hRP.2 0 hN).1 (hRO 0 hN)
  have key := fullLoop_spec hN hRP hRO hgt htab hinj E _ h' (by
    intro r hr
    rw [shiftLeft_one, Nat.testBit_two_pow] at hr
    have : r = imgW W RPK 0 := by simpa [eq_comm] using hr
    rw [this, hrd 0 hN]
    exact h0)
  intro i hi
  exact reach_trans (key _ (hRREPS i hi)) (hRO i hi)

theorem orbChk_sound {N W : Nat} {GS : List Nat} {ts : List (Array Nat)} {RPK : Nat}
    {repR : Array Nat} {REPS : List Nat} (hN : 0 < N) (hRP : Rep N W RPK repR)
    (hRO : ∀ i < N, Reach ts (repR.getD i 0) i) (hRREPS : ∀ i < N, repR.getD i 0 ∈ REPS)
    (hgt : ∀ g ∈ GS, ∃ t ∈ ts, ∀ x < N, imgW W g x = arrImg t x)
    (htg : ∀ t ∈ ts, ∃ g ∈ GS, ∀ x < N, imgW W g x = arrImg t x)
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N)
    (hinj : ∀ t ∈ ts, ∀ i < N, ∀ j < N, arrImg t i = arrImg t j → i = j) {B : Nat} {C : List Nat}
    (h : orbChk N W GS RPK REPS B C = true) : MaskOf N ts B := by
  unfold orbChk at h
  cases hb : Nat.beq B (Nat.sub (Nat.shiftLeft 1 N) 1)
  · rw [hb] at h
    exact smallK_sound hgt htg h
  · rw [hb] at h
    have hB : B = 2 ^ N - 1 := by
      have := beq_iff.1 hb
      rw [this]
      change Nat.shiftLeft 1 N - 1 = _
      rw [shiftLeft_one]
    have := fullK_sound hN hRP hRO hRREPS hgt htab hinj h
    intro i
    rw [hB, Nat.testBit_two_pow_sub_one]
    constructor
    · intro hi
      have hiN : i < N := by simpa using hi
      exact ⟨hiN, this i hiN⟩
    · rintro ⟨hiN, _⟩
      simpa using hiN

end CFSG.KC.LQT.PPC
