module

public import Certificates.Data.Kernel.LocalQT.Tc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.PinvSSound

public section

namespace CFSG.KC.LQT.TCK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.LQT.TC CFSG.QuasithinUnique.Setup.X1
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n w : ℕ}

abbrev RP (n w P : ℕ) (g : Equiv.Perm (Fin n)) : Prop := CFSG.KS.Raw.Orb.PRep n w P g

theorem sB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sN (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem getTc_eq (d : ℕ) : ∀ (L : List ℕ) (k : ℕ), getTc d L k = L.getD k d
  | [], _ => rfl
  | x :: L, 0 => rfl
  | x :: L, k + 1 => by
    change getTc d L k = _
    rw [getTc_eq d L k]
    rfl

theorem rp_pinvS (hw : n < 2 ^ w) {P : ℕ} {g : Equiv.Perm (Fin n)} (h : RP n w P g) :
    RP n w (pinvS n w (mask w) P) g⁻¹ := by
  have hinj : CFSG.KS.PinvS.InjK n w P := by
    refine ⟨fun i hi => ?_, fun a ha b hb e => ?_⟩
    · rw [h ⟨i, hi⟩]
      exact (g _).isLt
    · rw [h ⟨a, ha⟩, h ⟨b, hb⟩] at e
      have := g.injective (Fin.ext e)
      exact congrArg Fin.val this
  intro x
  have hx := h (g⁻¹ x)
  have e : g (g⁻¹ x) = x := by simp
  rw [e] at hx
  have := CFSG.KS.PinvS.pg_pinvS hw hinj (g⁻¹ x).isLt
  rw [hx] at this
  exact this

theorem rp_pcomp (hn : n < 2 ^ 32) {P Q : ℕ} {g h : Equiv.Perm (Fin n)} (hP : RP n w P g)
    (hQ : RP n w Q h) : RP n w (pcomp n w (mask w) P Q) (g * h) :=
  CFSG.KS.Raw.Orb.prep_pcomp hn hP hQ

theorem rp_idn (h : idK n w (mask w) = true) : RP n w (pidn n w) 1 := by
  intro x
  unfold idK at h
  have := (CFSG.KS.Raw.Orb.allN_iff.1 h) x x.isLt
  exact Nat.eq_of_beq_eq_true this

theorem of_permOK {P Q : ℕ} (h : permOK n w (mask w) (n * w) P Q = true) :
    ∃ g : Equiv.Perm (Fin n), PRep n (unpack n w P, unpack n w Q) g ∧ RP n w P g ∧
      RP n w Q g⁻¹ := by
  obtain ⟨h1, h2⟩ := rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack h)
  exact ⟨_, ⟨h1, h2⟩, CFSG.KS.Raw.Orb.prep_of_rep h1, CFSG.KS.Raw.Orb.prep_of_rep h2⟩

theorem pLetter_pos (regs : List PArr) (j : ℕ) :
    pLetter n regs (Int.ofNat (j + 1)) = regs.getD j (pId n) := by
  have h0 : Int.ofNat (j + 1) ≠ 0 := by
    rw [Int.ofNat_eq_natCast]
    omega
  have h1 : (0 : ℤ) < Int.ofNat (j + 1) := by
    rw [Int.ofNat_eq_natCast]
    omega
  simp only [pLetter, h0, h1, ↓reduceIte]
  simp

theorem pLetter_neg (regs : List PArr) (k : ℕ) :
    pLetter n regs (Int.negSucc k) = pInv (regs.getD k (pId n)) := by
  simp only [pLetter, Int.negSucc_ne_zero, ↓reduceIte, Int.negSucc_not_pos]
  congr 2

theorem gensTc_sound : ∀ (G GI : List ℕ), gensTc n w G GI = true →
    G.length = GI.length ∧ ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true
  | [], [], _ => ⟨rfl, by simp⟩
  | [], _ :: _, h => absurd h (by simp [gensTc])
  | _ :: _, [], h => absurd h (by simp [gensTc])
  | g :: G, gi :: GI, h => by
    change bAnd(canonK n w (mask w) (n * w) g, bAnd(permOK n w (mask w) (n * w) g gi,
      gensTc n w G GI)) = true at h
    obtain ⟨-, h⟩ := bAnd_true h
    obtain ⟨hp, h⟩ := bAnd_true h
    obtain ⟨hl, hz⟩ := gensTc_sound G GI h
    refine ⟨by simp [hl], fun p hp' => ?_⟩
    rw [List.zip_cons_cons, List.mem_cons] at hp'
    rcases hp' with rfl | hp'
    · exact hp
    · exact hz p hp'

section Gens

variable {idn : ℕ} {G GI : List ℕ} (hn : n < 2 ^ 32) (hw : n < 2 ^ w) (hid : RP n w idn 1)
  (hl : G.length = GI.length) (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true)

include hid hl hz in
theorem gen_getD (k : ℕ) :
    ∃ g : Equiv.Perm (Fin n),
      PRep n ((((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2))).getD k (pId n)) g ∧
      RP n w (G.getD k idn) g ∧ RP n w (GI.getD k idn) g⁻¹ := by
  by_cases hk : k < G.length
  · have hk' : k < GI.length := hl ▸ hk
    have hkz : k < (G.zip GI).length := by simp [hk, hk']
    obtain ⟨g, h1, h2, h3⟩ := of_permOK (hz _ (List.getElem_mem hkz))
    refine ⟨g, ?_, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa using hkz), List.getElem_map]
      exact h1
    · rw [List.getD_eq_getElem _ _ hk]
      simpa using h2
    · rw [List.getD_eq_getElem _ _ hk']
      simpa using h3
  · have hk' : ¬ k < GI.length := hl ▸ hk
    refine ⟨1, ?_, ?_, ?_⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      exact pRep_id
    · rw [List.getD_eq_default _ _ (by omega)]
      exact hid
    · rw [List.getD_eq_default _ _ (by omega), inv_one]
      exact hid

include hid hl hz in
theorem letG_sound (z : ℤ) :
    ∃ g : Equiv.Perm (Fin n),
      PRep n (pLetter n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2)) z) g ∧
      RP n w (letG idn G GI z) g := by
  rcases z with (_ | j) | k
  · exact ⟨1, by simp [pLetter, pRep_id], hid⟩
  · obtain ⟨g, h1, h2, -⟩ := gen_getD hid hl hz j
    refine ⟨g, ?_, ?_⟩
    · rw [pLetter_pos]
      exact h1
    · change RP n w (getTc idn G j) g
      rw [getTc_eq]
      exact h2
  · obtain ⟨g, h1, -, h3⟩ := gen_getD hid hl hz k
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [pLetter_neg]
      exact h1.inv
    · change RP n w (getTc idn GI k) g⁻¹
      rw [getTc_eq]
      exact h3

include hn hid hl hz in
theorem wordTc_sound : ∀ wd : List ℤ,
    ∃ g : Equiv.Perm (Fin n),
      PRep n (pWord n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2)) wd) g ∧
      RP n w (wordTc n w idn G GI wd) g
  | [] => ⟨1, pRep_id, hid⟩
  | z :: wd => by
    obtain ⟨g, h1, h2⟩ := letG_sound hid hl hz z
    obtain ⟨h, h3, h4⟩ := wordTc_sound wd
    refine ⟨g * h, h1.mul h3, ?_⟩
    change RP n w (strictN (wordTc n w idn G GI wd)
      (fun q => pcomp n w (mask w) (letG idn G GI z) q)) (g * h)
    rw [sN]
    exact rp_pcomp hn h2 h4

end Gens

def Rel (n w : ℕ) (regs : List PArr) (Ps : List ℕ) : Prop :=
  List.Forall₂ (fun r P => ∃ g : Equiv.Perm (Fin n), PRep n r g ∧ RP n w P g) regs Ps

theorem rel_append {regs : List PArr} {Ps : List ℕ} (h : Rel n w regs Ps) {r : PArr} {P : ℕ}
    {g : Equiv.Perm (Fin n)} (hr : PRep n r g) (hP : RP n w P g) :
    Rel n w (regs ++ [r]) (Ps ++ [P]) :=
  List.rel_append h (List.Forall₂.cons ⟨g, hr, hP⟩ List.Forall₂.nil)

theorem rel_getD {regs : List PArr} {Ps : List ℕ} (h : Rel n w regs Ps) {idn : ℕ}
    (hid : RP n w idn 1) (k : ℕ) :
    ∃ g : Equiv.Perm (Fin n), PRep n (regs.getD k (pId n)) g ∧
      RP n w (regTc idn Ps.reverse Ps.length k) g := by
  have hl := h.length_eq
  by_cases hk : k < Ps.length
  · have hk' : k < regs.length := hl ▸ hk
    obtain ⟨g, h1, h2⟩ := List.forall₂_iff_get.1 h |>.2 k hk' hk
    refine ⟨g, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hk']
      exact h1
    · unfold regTc
      have hb : Nat.blt k Ps.length = true := by
        rw [Nat.blt_eq]
        exact hk
      rw [hb]
      change RP n w (getTc idn Ps.reverse (Nat.sub (Nat.sub Ps.length k) 1)) g
      rw [getTc_eq, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse]
      have e : Ps.length - 1 - (Nat.sub (Nat.sub Ps.length k) 1) = k := by
        change Ps.length - 1 - (Ps.length - k - 1) = k
        omega
      simp only [e]
      exact h2
  · refine ⟨1, ?_, ?_⟩
    · rw [List.getD_eq_default _ _ (by omega)]
      exact pRep_id
    · unfold regTc
      have : Nat.blt k Ps.length = false := by
        rw [Bool.eq_false_iff]
        intro e
        rw [Nat.blt_eq] at e
        exact hk e
      rw [this]
      exact hid

theorem letTc_sound (hw : n < 2 ^ w) {regs : List PArr} {Ps : List ℕ} (h : Rel n w regs Ps)
    {idn : ℕ} (hid : RP n w idn 1) (z : ℤ) :
    ∃ g : Equiv.Perm (Fin n), PRep n (pLetter n regs z) g ∧
      RP n w (letTc n w idn Ps.reverse Ps.length z) g := by
  rcases z with (_ | j) | k
  · exact ⟨1, by simp [pLetter, pRep_id], hid⟩
  · obtain ⟨g, h1, h2⟩ := rel_getD h hid j
    refine ⟨g, ?_, h2⟩
    rw [pLetter_pos]
    exact h1
  · obtain ⟨g, h1, h2⟩ := rel_getD h hid k
    refine ⟨g⁻¹, ?_, rp_pinvS hw h2⟩
    rw [pLetter_neg]
    exact h1.inv

theorem pRun_cons (regs : List PArr) (pq : ℤ × ℤ) (rest : List (ℤ × ℤ)) :
    pRun n regs (pq :: rest) =
      pRun n (regs ++ [pMul n (pLetter n regs pq.1) (pLetter n regs pq.2)]) rest := rfl

theorem runTc_sound (hn : n < 2 ^ 32) (hw : n < 2 ^ w) {idn : ℕ} (hid : RP n w idn 1)
    (k : List ℕ → ℕ → Bool) : ∀ (prog : List (ℤ × ℤ)) (regs : List PArr) (Ps : List ℕ),
    Rel n w regs Ps → runTc n w idn prog k Ps.reverse Ps.length = true →
      ∃ Ps', Rel n w (pRun n regs prog) Ps' ∧ k Ps'.reverse Ps'.length = true
  | [], regs, Ps, h, hk => ⟨Ps, h, hk⟩
  | pq :: prog, regs, Ps, h, hk => by
    change strictB (pcomp n w (mask w) (letTc n w idn Ps.reverse Ps.length pq.1)
      (letTc n w idn Ps.reverse Ps.length pq.2))
      (fun x => runTc n w idn prog k (x :: Ps.reverse) (Nat.succ Ps.length)) = true at hk
    rw [sB] at hk
    obtain ⟨g, h1, h2⟩ := letTc_sound hw h hid pq.1
    obtain ⟨g', h3, h4⟩ := letTc_sound hw h hid pq.2
    have hr := rel_append h (h1.mul h3) (rp_pcomp hn h2 h4)
    have e1 : (pcomp n w (mask w) (letTc n w idn Ps.reverse Ps.length pq.1)
        (letTc n w idn Ps.reverse Ps.length pq.2)) :: Ps.reverse =
        (Ps ++ [pcomp n w (mask w) (letTc n w idn Ps.reverse Ps.length pq.1)
          (letTc n w idn Ps.reverse Ps.length pq.2)]).reverse := by simp
    have e2 : Nat.succ Ps.length = (Ps ++ [pcomp n w (mask w)
        (letTc n w idn Ps.reverse Ps.length pq.1) (letTc n w idn Ps.reverse Ps.length pq.2)]).length :=
      by simp
    rw [e1, e2] at hk
    rw [pRun_cons]
    exact runTc_sound hn hw hid k prog _ _ hr hk

theorem initTc_sound (hn : n < 2 ^ 32) (hw : n < 2 ^ w) {idn : ℕ} (hid : RP n w idn 1)
    {G GI : List ℕ} (hl : G.length = GI.length)
    (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true) {T : ℕ} {t : PArr}
    {τ : Equiv.Perm (Fin n)} (ht : PRep n t τ) (hT : RP n w T τ) (k : List ℕ → ℕ → Bool) :
    ∀ (ws : List (List ℤ)) (regs : List PArr) (Ps : List ℕ),
    Rel n w regs Ps → initTc n w idn G GI T ws k Ps.reverse Ps.length = true →
      ∃ Ps', Rel n w (regs ++ ws.map fun wd =>
        pConj n (pWord n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2)) wd) t) Ps' ∧
        k Ps'.reverse Ps'.length = true
  | [], regs, Ps, h, hk => ⟨Ps, by simpa using h, hk⟩
  | wd :: ws, regs, Ps, h, hk => by
    change strictB (conjTc n w T (wordTc n w idn G GI wd))
      (fun x => initTc n w idn G GI T ws k (x :: Ps.reverse) (Nat.succ Ps.length)) = true at hk
    rw [sB] at hk
    obtain ⟨g, h1, h2⟩ := wordTc_sound hn hid hl hz wd
    have hc : RP n w (conjTc n w T (wordTc n w idn G GI wd)) (g * τ * g⁻¹) := by
      unfold conjTc
      rw [sN]
      exact rp_pcomp hn (rp_pcomp hn h2 hT) (rp_pinvS hw h2)
    have hr := rel_append h ((h1.mul ht).mul h1.inv) hc
    have e1 : conjTc n w T (wordTc n w idn G GI wd) :: Ps.reverse =
        (Ps ++ [conjTc n w T (wordTc n w idn G GI wd)]).reverse := by simp
    have e2 : Nat.succ Ps.length = (Ps ++ [conjTc n w T (wordTc n w idn G GI wd)]).length := by
      simp
    rw [e1, e2] at hk
    obtain ⟨Ps', h3, h4⟩ := initTc_sound hn hw hid hl hz ht hT k ws _ _ hr hk
    refine ⟨Ps', ?_, h4⟩
    simpa [List.append_assoc, pConj] using h3

theorem memTc_iff (x : ℕ) : ∀ rev : List ℕ, memTc x rev = true → x ∈ rev
  | [], h => absurd h (by simp [memTc])
  | y :: rev, h => by
    change Bool.rec (motive := fun _ => Bool) (memTc x rev) true (Nat.beq x y) = true at h
    cases hb : Nat.beq x y
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (memTc_iff x rev h)
    · rw [Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self

theorem targTc_sound (targets rev : List ℕ) (h : targTc n w targets rev = true) :
    ∀ A ∈ targets, A ∈ rev := by
  induction targets with
  | nil => simp
  | cons A targets ih =>
    change bAnd(canonK n w (mask w) (n * w) A, bAnd(memTc A rev, targTc n w targets rev)) = true
      at h
    obtain ⟨-, h⟩ := bAnd_true h
    obtain ⟨h1, h2⟩ := bAnd_true h
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact memTc_iff _ _ h1
    · exact ih h2 B hB

theorem tcK_sound {G GI : List ℕ} {T TI : ℕ} {ws : List (List ℤ)} {prog : List (ℤ × ℤ)}
    {targets : List ℕ} (h : tcK n w G GI T TI ws prog targets = true) :
    threeConjCheck n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2))
      (unpack n w T, unpack n w TI) ws prog (targets.map (unpack n w)) = true := by
  unfold tcK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨hc, h⟩ := bAnd_true h
  obtain ⟨hp, h⟩ := bAnd_true h
  obtain ⟨hn1, hw1, -, -⟩ := CFSG.KS.PF.canon_facts hc
  have hn : n < 2 ^ 32 := by omega
  have hw : n < 2 ^ w := by omega
  have hidn := rp_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨τ, ht, hT, -⟩ := of_permOK hp
  have h0 : Rel n w [] [] := List.Forall₂.nil
  obtain ⟨Ps, hR, hk⟩ := initTc_sound hn hw hidn hl hz ht hT _ ws [] [] h0 h
  obtain ⟨Ps', hR', hk'⟩ := runTc_sound hn hw hidn _ prog _ Ps hR hk
  have htarg := targTc_sound targets Ps'.reverse hk'
  unfold threeConjCheck
  rw [List.all_eq_true]
  intro A' hA'
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
  have hAP : A ∈ Ps' := List.mem_reverse.1 (htarg A hA)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hAP
  have hi' : i < (pRun n ([] ++ ws.map fun wd => pConj n (pWord n ((G.zip GI).map fun p =>
      (unpack n w p.1, unpack n w p.2)) wd) (unpack n w T, unpack n w TI)) prog).length := by
    rw [hR'.length_eq]
    exact hi
  obtain ⟨g, h1, h2⟩ := List.forall₂_iff_get.1 hR' |>.2 i hi' hi
  rw [List.any_eq_true]
  refine ⟨_, ?_, (eqA_iff h1.1 (CFSG.KS.Raw.Orb.rep_unpack h2)).2 rfl⟩
  simp only [List.nil_append] at hi' ⊢
  exact List.getElem_mem hi'

end CFSG.KC.LQT.TCK

end
