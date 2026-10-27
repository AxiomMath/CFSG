module

public import Certificates.Data.Kernel.QuatPack
public import Certificates.Data.E4QuatCheck
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.QuatK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.ClassicalInvolution.Q3.TL4.E4C

variable {n w : Nat}

@[expose] def CRep (n w P : Nat) (g : Equiv.Perm (Fin n)) : Prop :=
  PRep n w P g ∧ P >>> (n * w) = 0

theorem crep_mulK (hn : n < 2 ^ 32) (hw : 0 < w) {P Q : Nat} {g h : Equiv.Perm (Fin n)}
    (hP : PRep n w P g) (hQ : PRep n w Q h) : CRep n w (mulK n w P Q) (g * h) :=
  ⟨prep_pcomp hn hP hQ, CFSG.KS.PF.pcomp_shr P Q hn hw⟩

theorem crep_of_canonK {P : Nat} {g : Equiv.Perm (Fin n)}
    (hc : canonK n w (mask w) (n * w) P = true) (hP : PRep n w P g) : CRep n w P g :=
  ⟨hP, (CFSG.KS.PF.canon_facts hc).2.2.1⟩

theorem crep_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : CRep n w (pidn n w) 1 :=
  ⟨prep_pidn hn hw, CFSG.KS.PF.pidn_shr hn hw⟩

theorem beq_eq (hw : 0 < w) {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hP : CRep n w P g)
    (hQ : CRep n w Q h) : Nat.beq P Q = decide (g = h) := by
  by_cases hgh : g = h
  · rw [decide_eq_true hgh]
    subst hgh
    rw [CFSG.KS.PF.eq_of_fields hw hP.2 hQ.2 fun i hi =>
      (hP.1 ⟨i, hi⟩).trans (hQ.1 ⟨i, hi⟩).symm]
    exact Nat.beq_refl Q
  · rw [decide_eq_false hgh]
    cases e : Nat.beq P Q
    · rfl
    · have e' := Nat.eq_of_beq_eq_true e
      subst e'
      exact absurd (Equiv.ext fun x => Fin.ext ((hP.1 x).symm.trans (hQ.1 x))) hgh

theorem all_f2 {α β : Type} {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (hfg : ∀ a b, R a b → f a = g b) : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      l₁.all f = l₂.all g
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [List.all_cons, List.all_cons, hfg _ _ h, all_f2 hfg t]

theorem any_f2 {α β : Type} {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (hfg : ∀ a b, R a b → f a = g b) : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      l₁.any f = l₂.any g
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [List.any_cons, List.any_cons, hfg _ _ h, any_f2 hfg t]

theorem memK_eq (hw : 0 < w) {L : List Nat} {LP : List (Equiv.Perm (Fin n))}
    (hL : List.Forall₂ (CRep n w) L LP) {x : Nat} {X : Equiv.Perm (Fin n)} (hx : CRep n w x X) :
    memK L x = decide (X ∈ LP) := by
  induction hL with
  | nil => simp [memK]
  | cons hab _ ih =>
    simp only [memK, List.any_cons] at ih ⊢
    rw [ih, beq_eq hw hx hab]
    simp only [List.mem_cons, Bool.decide_or]

theorem q8K_forall₂ (hn : n < 2 ^ 32) (hw : 0 < w) {e r i j : Nat} {R I J : Equiv.Perm (Fin n)}
    (he : CRep n w e 1) (hr : CRep n w r R) (hi : CRep n w i I) (hj : CRep n w j J) :
    List.Forall₂ (CRep n w) (q8K n w e r i j) (q8Elems R I J) := by
  have m := @crep_mulK n w hn hw
  exact .cons he (.cons hr (.cons hi (.cons (m hi.1 hr.1) (.cons hj (.cons (m hj.1 hr.1)
    (.cons (m hi.1 hj.1) (.cons (m (m hi.1 hj.1).1 hr.1) .nil)))))))

theorem sameSetK_eq (hw : 0 < w) {A B : List Nat} {AP BP : List (Equiv.Perm (Fin n))}
    (hA : List.Forall₂ (CRep n w) A AP) (hB : List.Forall₂ (CRep n w) B BP) :
    sameSetK A B = sameSet AP BP := by
  rw [sameSetK, sameSet, all_f2 (fun a b h => memK_eq hw hB h) hA,
    all_f2 (fun a b h => memK_eq hw hA h) hB]

theorem conj_eq_inv_iff {G : Type*} [Group G] (x u : G) : x * u * x⁻¹ = u⁻¹ ↔ u * (x * u) = x := by
  constructor
  · intro h
    calc u * (x * u) = u * (x * u * x⁻¹) * x := by group
      _ = x := by rw [h]; group
  · intro h
    calc x * u * x⁻¹ = u⁻¹ * (u * (x * u)) * x⁻¹ := by group
      _ = u⁻¹ := by rw [h]; group

theorem badWitK_eq (hn : n < 2 ^ 32) (hw : 0 < w) {u : Nat} {c : Nat × Nat}
    {U C : Equiv.Perm (Fin n)} (hu : CRep n w u U) (hc1 : CRep n w c.1 C)
    (hc2 : CRep n w c.2 C⁻¹) : badWitK n w u c = badWit U C := by
  have m := @crep_mulK n w hn hw
  have hx := m (m hc1.1 hu.1).1 hc2.1
  simp only [badWitK, badWit]
  rw [beq_eq hw (m hx.1 hu.1) (m hu.1 hx.1), beq_eq hw (m hu.1 (m hx.1 hu.1).1) hx,
    decide_eq_decide.mpr (conj_eq_inv_iff (C * U * C⁻¹) U)]

theorem violatesK_eq (hn : n < 2 ^ 32) (hw : 0 < w) {T : List Nat}
    {TP : List (Equiv.Perm (Fin n))} (hT : List.Forall₂ (CRep n w) T TP) {i j : Nat}
    {I J : Equiv.Perm (Fin n)} (hi : CRep n w i I) (hj : CRep n w j J) {c : Nat × Nat}
    {C : Equiv.Perm (Fin n)} (hc1 : CRep n w c.1 C) (hc2 : CRep n w c.2 C⁻¹) :
    violatesK n w T i j c = violates TP I J C := by
  have m := @crep_mulK n w hn hw
  rw [violatesK, violates,
    any_f2 (fun a b h => congrArg (!·) (memK_eq hw hT (m (m hc1.1 h.1).1 hc2.1))) hT,
    any_f2 (R := CRep n w) (fun a b h => any_f2 (R := CRep n w)
      (fun a' b' h' => congrArg (!·) (beq_eq hw (m h.1 h'.1) (m h'.1 h.1)))
      (.cons (m (m hc1.1 hi.1).1 hc2.1) (.cons (m (m hc1.1 hj.1).1 hc2.1) .nil)))
      (.cons hi (.cons hj .nil))]

theorem identSqCheckK_eq (hn : n < 2 ^ 32) (hw : 0 < w) {e r : Nat} {R : Equiv.Perm (Fin n)}
    (he : CRep n w e 1) (hr : CRep n w r R) {S : List Nat} {SP : List (Equiv.Perm (Fin n))}
    (hS : List.Forall₂ (CRep n w) S SP) {W : List (Nat × Nat)} {WP : List (Equiv.Perm (Fin n))}
    (hW : List.Forall₂ (fun c C => CRep n w c.1 C ∧ CRep n w c.2 C⁻¹) W WP)
    {Ls : List (List Nat)} {LsP : List (List (Equiv.Perm (Fin n)))}
    (hLs : List.Forall₂ (List.Forall₂ (CRep n w)) Ls LsP) :
    identSqCheckK n w e r S W Ls = identSqCheck R SP WP LsP := by
  have m := @crep_mulK n w hn hw
  unfold identSqCheckK identSqCheck
  refine all_f2 (fun u U hu => ?_) hS
  rw [any_f2 (fun c C hc => badWitK_eq hn hw hu hc.1 hc.2) hW]
  congr 1
  refine all_f2 (fun v V hv => ?_) hS
  have hq := q8K_forall₂ hn hw he hr hu hv
  rw [beq_eq hw (m hu.1 (m hv.1 hu.1).1) hv, any_f2 (fun A AP hA => sameSetK_eq hw hq hA) hLs,
    any_f2 (fun c C hc => violatesK_eq hn hw hq hu hv hc.1 hc.2) hW,
    decide_eq_decide.mpr (conj_eq_inv_iff V U)]

theorem cond_spec {c b : Bool} (h : cond c b (!b) = true) : b = true ↔ c = true := by
  cases c <;> cases b <;> simp_all

theorem listOKK_spec {l : List Nat} {p : Nat} (h : listOKK n w l p = true) :
    l.length = n ∧ ∀ i (hi : i < l.length), pg w (mask w) p i = l[i] := by
  rw [listOKK, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun i hi => ?_⟩
  have hm : (l[i], i) ∈ l.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi)
  exact Nat.eq_of_beq_eq_true (h.2 _ hm)

theorem sqScanK_spec (hn : n < 2 ^ 32) (hw : 0 < w) {T : Nat → Nat} {N r : Nat} {idx : List Nat}
    (h : sqScanK n w T N r idx = true) {g : Nat → Equiv.Perm (Fin n)}
    (hT : ∀ i < N, PRep n w (T i) (g i)) {R : Equiv.Perm (Fin n)} (hr : CRep n w r R) :
    (∀ i ∈ idx, i < N) ∧ ∀ i < N, (g i * g i = R ↔ i ∈ idx) := by
  rw [sqScanK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun i hi => by have h1 := h.1 i hi; rwa [Nat.blt_eq] at h1, fun i hi => ?_⟩
  have h1 := cond_spec (h.2 i (List.mem_range.2 hi))
  rw [beq_eq hw (crep_mulK hn hw (hT i hi) (hT i hi)) hr, decide_eq_true_iff,
    List.contains_iff_mem] at h1
  exact h1

theorem cfgK_eq (hw : 0 < w) {e u v u' v' y : Nat} {tw : List (Nat × Nat)}
    {U V U' V' Y : Equiv.Perm (Fin n)} {twP : List (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))}
    (hn : n < 2 ^ 32) (he : CRep n w e 1) (hu : PRep n w u U) (hv : PRep n w v V)
    (hu' : PRep n w u' U') (hv' : PRep n w v' V') (hy : PRep n w y Y)
    (htw : List.Forall₂ (fun p P => PRep n w p.1 P.1 ∧ PRep n w p.2 P.2) tw twP) :
    cfgK n w e u v u' v' tw y = true ↔ Y * U = U * Y ∧ Y * V = V * Y ∧ Y * Y = 1 ∧
      ∃ P ∈ twP, Y * U' = P.1 * Y ∧ Y * V' = P.2 * Y := by
  have m := @crep_mulK n w hn hw
  rw [cfgK, beq_eq hw (m hy hu) (m hu hy), beq_eq hw (m hy hv) (m hv hy), beq_eq hw (m hy hy) he,
    any_f2 (g := fun P => decide (Y * U' = P.1 * Y ∧ Y * V' = P.2 * Y)) (fun p P hp => by
      rw [beq_eq hw (m hy hu') (m hp.1 hy), beq_eq hw (m hy hv') (m hp.2 hy), Bool.decide_and])
      htw]
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.any_eq_true, and_assoc]

theorem cfgScanK_spec {e u v u' v' : Nat} {tw : List (Nat × Nat)} {T : Nat → Nat} {N s : Nat}
    {idx : List Nat} (h : cfgScanK n w e u v u' v' tw T N s idx = true) {i : Nat} (hi : i < N)
    (hc : cfgK n w e u v u' v' tw (mulK n w (T i) s) = true) : i ∈ idx := by
  rw [cfgScanK, List.all_eq_true] at h
  exact List.contains_iff_mem.1 ((cond_spec (h i (List.mem_range.2 hi))).1 hc)

end CFSG.KC.QuatK

end
