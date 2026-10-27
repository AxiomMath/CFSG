module

public import Certificates.Data.Kernel.TwoF4LieK
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.TwoF4LieSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.TwoF4LieK

open scoped Pointwise

abbrev Pm := Equiv.Perm (Fin 1755)

abbrev PR (P : ℕ) (g : Pm) : Prop := PRep 1755 11 P g

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem prep_mul {P Q : ℕ} {g h : Pm} (hP : PR P g) (hQ : PR Q h) : PR (mul P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_idP : PR idP 1 := prep_pidn (by norm_num) (by norm_num)

theorem gp_eq {P : ℕ} {g : Pm} (hP : PR P g) (x : Fin 1755) : gp P x = g x := hP x

@[expose] noncomputable def letP (g : ℕ → Pm) (c : ℕ) : Pm :=
  if c % 2 = 0 then g (c / 2 - 1) else (g (c / 2 - 1))⁻¹

@[expose] noncomputable def wordP (g : ℕ → Pm) (wd : List ℕ) : Pm := (wd.map (letP g)).prod

@[expose] def CodesOK (wd : List ℕ) : Prop := ∀ c ∈ wd, 2 ≤ c ∧ c < 10

variable {F FI : ℕ → ℕ} {g : ℕ → Pm}

theorem lett_prep (hF : ∀ h < 4, PR (F h) (g h)) (hFI : ∀ h < 4, PR (FI h) (g h)⁻¹) {c : ℕ}
    (hc : 2 ≤ c) (hc' : c < 10) : PR (lett F FI c) (letP g c) := by
  interval_cases c
  · exact hF 0 (by norm_num)
  · exact hFI 0 (by norm_num)
  · exact hF 1 (by norm_num)
  · exact hFI 1 (by norm_num)
  · exact hF 2 (by norm_num)
  · exact hFI 2 (by norm_num)
  · exact hF 3 (by norm_num)
  · exact hFI 3 (by norm_num)

theorem letP_inv (c : ℕ) : letP (fun h => (g h)⁻¹) c = (letP g c)⁻¹ := by
  unfold letP
  split_ifs <;> simp

theorem wN_prep (hF : ∀ h < 4, PR (F h) (g h)) (hFI : ∀ h < 4, PR (FI h) (g h)⁻¹) :
    ∀ wd : List ℕ, CodesOK wd → PR (wN F FI wd) (wordP g wd)
  | [], _ => by
    change PR idP (wordP g [])
    simpa [wordP] using prep_idP
  | c :: wd, hw => by
    have h1 := lett_prep hF hFI (hw c (List.mem_cons_self)).1 (hw c (List.mem_cons_self)).2
    have h2 := wN_prep hF hFI wd (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
    have e : wN F FI (c :: wd) = mul (lett F FI c) (wN F FI wd) := strictN_eq' _ _
    rw [e]
    simpa [wordP] using prep_mul h1 h2

theorem wPt_eq (hF : ∀ h < 4, PR (F h) (g h)) (hFI : ∀ h < 4, PR (FI h) (g h)⁻¹) :
    ∀ wd : List ℕ, CodesOK wd → ∀ x : Fin 1755, wPt F FI wd x = (wordP g wd x : ℕ)
  | [], _, x => by simp [wordP, wPt]
  | c :: wd, hw, x => by
    have h1 := lett_prep hF hFI (hw c (List.mem_cons_self)).1 (hw c (List.mem_cons_self)).2
    have h2 := wPt_eq hF hFI wd (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) x
    have e : wPt F FI (c :: wd) x = gp (lett F FI c) (wPt F FI wd x) := strictN_eq' _ _
    rw [e, h2]
    have := gp_eq h1 (wordP g wd x)
    rw [this]
    simp [wordP, Equiv.Perm.mul_apply]

theorem wInv_eq (hF : ∀ h < 4, PR (F h) (g h)) (hFI : ∀ h < 4, PR (FI h) (g h)⁻¹) :
    ∀ wd : List ℕ, CodesOK wd → ∀ y : Fin 1755, wInv F FI wd y = ((wordP g wd)⁻¹ y : ℕ)
  | [], _, y => by simp [wordP, wInv]
  | c :: wd, hw, y => by
    have hFI' : ∀ h < 4, PR (F h) ((fun h => (g h)⁻¹) h)⁻¹ := fun h hh => by
      simpa using hF h hh
    have h1 := lett_prep (g := fun h => (g h)⁻¹) hFI hFI' (hw c (List.mem_cons_self)).1
      (hw c (List.mem_cons_self)).2
    rw [letP_inv] at h1
    have e : wInv F FI (c :: wd) y = wInv F FI wd (gp (lett FI F c) y) := strictN_eq' _ _
    rw [e, gp_eq h1 y]
    rw [wInv_eq hF hFI wd (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))]
    simp [wordP, mul_inv_rev, Equiv.Perm.mul_apply]

theorem bAnd_eq' (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem allL_iff {f : ℕ → List ℕ → Bool} : ∀ (L : List (List ℕ)) (i : ℕ),
    allL f L i = true ↔ ∀ k (hk : k < L.length), f (i + k) L[k] = true
  | [], i => by simp [allL]
  | r :: L, i => by
    change Bool.rec (motive := fun _ => Bool) false (strictB (Nat.succ i) (allL f L)) (f i r) =
      true ↔ _
    rw [strictB_eq', bAnd_eq', Bool.and_eq_true, allL_iff L (Nat.succ i)]
    constructor
    · rintro ⟨h0, h⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k =>
        have := h k (by simpa using hk)
        rwa [Nat.succ_add, ← Nat.add_succ] at this
    · intro h
      have h0 := h 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      refine ⟨h0, fun k hk => ?_⟩
      have h1 := h (k + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_succ] at h1
      have e : i + (k + 1) = Nat.succ i + k := by omega
      rwa [e] at h1

theorem treeK_zero {E G : ℕ → ℕ} {R : List (List ℕ)} (h : treeK E G R = true)
    (hR : 0 < R.length) : E 0 = idP := by
  have := (allL_iff R 0).1 h 0 hR
  exact Nat.eq_of_beq_eq_true this

theorem treeK_sound {E G : ℕ → ℕ} {R : List (List ℕ)} {K : Subgroup Pm} {m : ℕ}
    (hG : ∀ l < m, ∃ x ∈ K, PR (G l) x) (hl : ∀ r ∈ R, r.tail.headD 0 < m)
    (h : treeK E G R = true) : ∀ i < R.length, ∃ x ∈ K, PR (E i) x := by
  have hrow := (allL_iff R 0).1 h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hr := hrow i hi
    rw [Nat.zero_add] at hr
    by_cases hi0 : i = 0
    · subst hi0
      have e : E 0 = idP := Nat.eq_of_beq_eq_true hr
      exact ⟨1, K.one_mem, by rw [e]; exact prep_idP⟩
    · have hb : Nat.beq i 0 = false := by
        cases e : Nat.beq i 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hi0
      simp only [hb, bAnd_eq', Bool.and_eq_true, Nat.blt_eq] at hr
      obtain ⟨hpar, he⟩ := hr
      obtain ⟨x, hx, hpx⟩ := ih _ hpar (by omega)
      obtain ⟨y, hy, hpy⟩ := hG _ (hl _ (List.getElem_mem hi))
      refine ⟨y * x, K.mul_mem hy hx, ?_⟩
      rw [Nat.eq_of_beq_eq_true he]
      exact prep_mul hpy hpx

theorem ugK_sound {A S U : ℕ → ℕ} {R : List (List ℕ)} {K : Subgroup Pm} {m : ℕ}
    (hA : ∀ q < 64, ∃ x ∈ K, PR (A q) x) (hS : ∀ s < m, ∃ x ∈ K, PR (S s) x)
    (hR : ∀ r ∈ R, r.headD 0 < 64 ∧ r.getD 1 0 < m ∧ r.getD 2 0 < 64)
    (hU : ∀ k < R.length, ∀ i < 1755, gp (U k) i < 1755)
    (h : ugK A S U R = true) : ∀ k < R.length, ∃ x ∈ K, PR (U k) x := by
  intro k hk
  have hr := (allL_iff R 0).1 h k hk
  rw [Nat.zero_add] at hr
  have he := Nat.eq_of_beq_eq_true hr
  obtain ⟨hq, hs, hq'⟩ := hR _ (List.getElem_mem hk)
  obtain ⟨a, ha, hpa⟩ := hA _ hq
  obtain ⟨s, hs', hps⟩ := hS _ hs
  obtain ⟨a', ha', hpa'⟩ := hA _ hq'
  refine ⟨a'⁻¹ * s * a, K.mul_mem (K.mul_mem (K.inv_mem ha') hs') ha, fun i => ?_⟩
  have hUi := hU k hk i i.2
  have e1 : gp (mul (A (R[k].getD 2 0)) (U k)) i =
      gp (mul (S (R[k].getD 1 0)) (A (R[k].headD 0))) i := by rw [he]
  have p1 : gp (mul (A (R[k].getD 2 0)) (U k)) i = gp (A (R[k].getD 2 0)) (gp (U k) i) :=
    CFSG.KS.PF.pg_pcomp (by norm_num) i.2
  have p2 : gp (mul (S (R[k].getD 1 0)) (A (R[k].headD 0))) i =
      gp (S (R[k].getD 1 0)) (gp (A (R[k].headD 0)) i) :=
    CFSG.KS.PF.pg_pcomp (by norm_num) i.2
  have e2 : gp (A (R[k].getD 2 0)) (gp (U k) i) = (a' ⟨gp (U k) i, hUi⟩ : ℕ) :=
    gp_eq hpa' ⟨_, hUi⟩
  rw [p1, p2, gp_eq hpa i, gp_eq hps (a i), e2] at e1
  have e4 : a' ⟨gp (U k) i, hUi⟩ = s (a i) := Fin.ext e1
  change gp (U k) i = ((a'⁻¹ * s * a) i : ℕ)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e4]
  simp

theorem fixAll_sound {a : ℕ} {L : List ℕ} (h : fixAll a L = true) : ∀ p ∈ L, gp a p = p := by
  intro p hp
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h p hp)

theorem distK_sound {f : ℕ → ℕ} {L : List ℕ} {n : ℕ} (h : distK (fun i => keyK (f i) L) n = true) :
    ∀ i < n, ∀ j < n, (∀ p ∈ L, gp (f i) p = gp (f j) p) → i = j := by
  have hkey : ∀ a b : ℕ, ∀ L : List ℕ, (∀ p ∈ L, gp a p = gp b p) → keyK a L = keyK b L := by
    intro a b L
    induction L with
    | nil => intro _; rfl
    | cons p L ih =>
      intro hp
      change Nat.lor (gp a p) (Nat.shiftLeft (keyK a L) 11) =
        Nat.lor (gp b p) (Nat.shiftLeft (keyK b L) 11)
      rw [hp p List.mem_cons_self, ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))]
  have hne : ∀ i < n, ∀ j < i, keyK (f i) L ≠ keyK (f j) L := by
    intro i hi j hj e
    unfold distK at h
    have h1 := allN_iff.1 h i hi
    beta_reduce at h1
    rw [strictB_eq', allN_iff] at h1
    have h2 := h1 j hj
    beta_reduce at h2
    rw [e, Nat.beq_refl] at h2
    exact Bool.false_ne_true h2
  intro i hi j hj hag
  have e := hkey _ _ L hag
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd e.symm (hne j hj i hij)
  · exact hij
  · exact absurd e (hne i hi j hij)

section Factor

variable {S : Subgroup Pm} {a b : ℕ → Pm} {base : List ℕ}

theorem eq_idx (hbfix : ∀ j < 64, ∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 →b j p = p)
    (hadist : ∀ i < 64, ∀ i' < 64, (∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 →a i p = a i' p) → i = i')
    (hbdist : ∀ j < 64, ∀ j' < 64, (∀ p : Fin 1755, (p : ℕ) ∈ base.drop 4 →b j p = b j' p) → j = j')
    {i i' j j' : ℕ} (hi : i < 64) (hi' : i' < 64) (hj : j < 64) (hj' : j' < 64)
    (h : ∀ p : Fin 1755, (p : ℕ) ∈ base →(a i * b j) p = (a i' * b j') p) : i = i' ∧ j = j' := by
  have e1 : i = i' := hadist i hi i' hi' fun p hp => by
    have := h p (List.mem_of_mem_take hp)
    rwa [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hbfix j hj p hp, hbfix j' hj' p hp] at this
  subst e1
  refine ⟨rfl, hbdist j hj j' hj' fun p hp => ?_⟩
  have := h p (List.mem_of_mem_drop hp)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at this
  exact (a i).injective this

theorem factor_cover (hS : Nat.card S = 4096) (ha : ∀ i < 64, a i ∈ S) (hb : ∀ j < 64, b j ∈ S)
    (hbfix : ∀ j < 64, ∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 →b j p = p)
    (hadist : ∀ i < 64, ∀ i' < 64, (∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 →a i p = a i' p) → i = i')
    (hbdist : ∀ j < 64, ∀ j' < 64, (∀ p : Fin 1755, (p : ℕ) ∈ base.drop 4 →b j p = b j' p) → j = j') :
    ∀ x ∈ S, ∃ i < 64, ∃ j < 64, x = a i * b j := by
  let f : Fin 64 × Fin 64 → S := fun ij =>
    ⟨a ij.1 * b ij.2, S.mul_mem (ha _ ij.1.2) (hb _ ij.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ e
    have e' : a i * b j = a i' * b j' := congrArg Subtype.val e
    obtain ⟨h1, h2⟩ := eq_idx hbfix hadist hbdist i.2 i'.2 j.2 j'.2 fun p _ => by rw [e']
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [hS]⟩
  intro x hx
  obtain ⟨⟨i, j⟩, e⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨i, i.2, j, j.2, (congrArg Subtype.val e).symm⟩

theorem factor_faithful (hS : Nat.card S = 4096) (ha : ∀ i < 64, a i ∈ S)
    (hb : ∀ j < 64, b j ∈ S) (hbfix : ∀ j < 64, ∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 →b j p = p)
    (hadist : ∀ i < 64, ∀ i' < 64, (∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 →a i p = a i' p) → i = i')
    (hbdist : ∀ j < 64, ∀ j' < 64, (∀ p : Fin 1755, (p : ℕ) ∈ base.drop 4 →b j p = b j' p) → j = j')
    {x y : Pm} (hx : x ∈ S) (hy : y ∈ S) (h : ∀ p : Fin 1755, (p : ℕ) ∈ base →x p = y p) : x = y := by
  obtain ⟨i, hi, j, hj, rfl⟩ := factor_cover hS ha hb hbfix hadist hbdist x hx
  obtain ⟨i', hi', j', hj', rfl⟩ := factor_cover hS ha hb hbfix hadist hbdist y hy
  obtain ⟨rfl, rfl⟩ := eq_idx hbfix hadist hbdist hi hi' hj hj' h
  rfl

end Factor

theorem memK_iff {x : ℕ} {L : List ℕ} : memK x L = true ↔ x ∈ L := by
  induction L with
  | nil => simp [memK]
  | cons y L ih =>
    change Bool.rec (motive := fun _ => Bool) (memK x L) true (Nat.beq x y) = true ↔ _
    cases h : Nat.beq x y
    · have : x ≠ y := fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)
      simp [ih, this]
    · simp [Nat.eq_of_beq_eq_true h]

theorem reach_forK {F FI A B lp : ℕ → ℕ} {base : List ℕ} {P : ℕ → Prop} {Rw : List ℕ → Prop}
    (hstep : ∀ r : List ℕ, Rw r → rowF F FI A B lp base r = true →
      P (Nat.add (Nat.mul 64 (r.getD 2 0)) (r.getD 3 0)) → P (nodeOf r)) :
    ∀ (rows : List (List ℕ)) (acc : List ℕ), (∀ r ∈ rows, Rw r) → (∀ k ∈ acc, P k) →
      forK F FI A B lp base rows acc = true → ∀ k ∈ acc ++ rows.map nodeOf, P k
  | [], acc, _, hacc, _ => by simpa using hacc
  | r :: rows, acc, hrw, hacc, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (forK F FI A B lp base rows (nodeOf r :: acc)) (rowF F FI A B lp base r))
      (memK _ acc) = true at h
    cases h1 : memK (Nat.add (Nat.mul 64 (r.getD 2 0)) (r.getD 3 0)) acc
    · rw [h1] at h
      exact (Bool.false_ne_true h).elim
    rw [h1] at h
    cases h2 : rowF F FI A B lp base r
    · rw [h2] at h
      exact (Bool.false_ne_true h).elim
    rw [h2] at h
    have hr : P (nodeOf r) := hstep r (hrw r List.mem_cons_self) h2 (hacc _ (memK_iff.1 h1))
    have := reach_forK hstep rows (nodeOf r :: acc)
      (fun r' hr' => hrw r' (List.mem_cons_of_mem _ hr')) (by
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hr
      · exact hacc k hk) h
    intro k hk
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hk
    rcases hk with hk | rfl | hk
    · exact this k (by simp [hk])
    · exact hr
    · exact this k (by simp [hk])

theorem rowF_sound {A B lp : ℕ → ℕ} {base r : List ℕ} {a b a' b' : Pm}
    (hF : ∀ h < 4, PR (F h) (g h)) (hFI : ∀ h < 4, PR (FI h) (g h)⁻¹) (hw : CodesOK (r.drop 4))
    (ha : PR (A (r.getD 0 0)) a) (hb : PR (B (r.getD 1 0)) b) (ha' : PR (A (r.getD 2 0)) a')
    (hb' : PR (B (r.getD 3 0)) b') (hlp : ∀ k < 3, lp k < 1755)
    (h : rowF F FI A B lp base r = true) :
    ((wordP g (r.drop 4))⁻¹ * (a * b) * wordP g (r.drop 4)) 0 = 0 ∧
      (∀ p : Fin 1755, onL0 lp p = true →
        onL0 lp (((wordP g (r.drop 4))⁻¹ * (a * b) * wordP g (r.drop 4)) p) = true) ∧
      (∀ p : Fin 1755, (p : ℕ) ∈ base →
        ((wordP g (r.drop 4))⁻¹ * (a * b) * wordP g (r.drop 4)) p = (a' * b') p) ∧
      (wordP g (r.drop 4) 0 = 0 ∨
        ∀ p : Fin 1755, onL0 lp p = true → onL0 lp (wordP g (r.drop 4) p) = true) := by
  have hbeq : ∀ x y : ℕ, Nat.beq x y = true ↔ x = y :=
    fun x y => ⟨Nat.eq_of_beq_eq_true, fun e => e ▸ Nat.beq_refl x⟩
  have bor : ∀ c e : Bool, Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
    intro c e
    cases c <;> rfl
  have honL : ∀ p, onL0 lp p = true ↔ p = lp 0 ∨ p = lp 1 ∨ p = lp 2 := by
    intro p
    simp only [onL0, bor, Bool.or_eq_true, hbeq]
  have hpt : ∀ q (hq : q < 1755), wPt F FI (r.drop 4) q = (wordP g (r.drop 4) ⟨q, hq⟩ : ℕ) :=
    fun q hq => wPt_eq hF hFI _ hw ⟨q, hq⟩
  have hf : ∀ q (hq : q < 1755), wInv F FI (r.drop 4) (gp (A (r.getD 0 0)) (gp (B (r.getD 1 0))
      (wPt F FI (r.drop 4) q))) =
      (((wordP g (r.drop 4))⁻¹ * (a * b) * wordP g (r.drop 4)) ⟨q, hq⟩ : ℕ) := by
    intro q hq
    rw [hpt q hq, gp_eq hb, gp_eq ha, wInv_eq hF hFI _ hw]
    simp [Equiv.Perm.mul_apply]
  unfold rowF stabS stabK at h
  simp only [strictB_eq', bAnd_eq', Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hy0, hy1, hy2, hy3⟩, hbase, hk⟩ := h
  have l0 := hlp 0 (by norm_num)
  have l1 := hlp 1 (by norm_num)
  have l2 := hlp 2 (by norm_num)
  refine ⟨Fin.ext ?_, ?_, fun p hp => Fin.ext ?_, ?_⟩
  · have e := hf 0 (by norm_num)
    rw [Nat.eq_of_beq_eq_true hy0] at e
    exact e.symm
  · intro p hp
    rcases (honL p).1 hp with e | e | e
    · have : p = ⟨lp 0, l0⟩ := Fin.ext e
      subst this
      rw [← hf _ l0]
      exact hy1
    · have : p = ⟨lp 1, l1⟩ := Fin.ext e
      subst this
      rw [← hf _ l1]
      exact hy2
    · have : p = ⟨lp 2, l2⟩ := Fin.ext e
      subst this
      rw [← hf _ l2]
      exact hy3
  · have e := Nat.eq_of_beq_eq_true (hbase p hp)
    rw [hf p p.2, gp_eq hb', gp_eq ha'] at e
    exact e
  · rw [hpt 0 (by norm_num)] at hk
    by_cases h0 : (wordP g (r.drop 4) ⟨0, by norm_num⟩ : ℕ) = 0
    · exact Or.inl (Fin.ext h0)
    · right
      have hb0 : Nat.beq (wordP g (r.drop 4) ⟨0, by norm_num⟩ : ℕ) 0 = false := by
        cases e : Nat.beq (wordP g (r.drop 4) ⟨0, by norm_num⟩ : ℕ) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) h0
      rw [hb0] at hk
      simp only [bAnd_eq', Bool.and_eq_true] at hk
      obtain ⟨k0, k1, k2⟩ := hk
      intro p hp
      rcases (honL p).1 hp with e | e | e
      · have : p = ⟨lp 0, l0⟩ := Fin.ext e
        subst this
        rw [← hpt _ l0]
        exact k0
      · have : p = ⟨lp 1, l1⟩ := Fin.ext e
        subst this
        rw [← hpt _ l1]
        exact k1
      · have : p = ⟨lp 2, l2⟩ := Fin.ext e
        subst this
        rw [← hpt _ l2]
        exact k2

theorem covK_sound {A B : ℕ → ℕ} {ns : List ℕ} {L : List (List ℕ)} {i₀ : ℕ}
    (h : covK A B ns L i₀ = true) : ∀ i < L.length, ∀ j < (L.getD i []).length,
      (∃ w < 1755, gp (A (i₀ + i)) (gp (B j) (gp (A (i₀ + i)) (gp (B j) w))) ≠ w) ∨
        64 * (i₀ + i) + j = 0 ∨ 64 * (i₀ + i) + j ∈ ns := by
  have key : ∀ (a : ℕ) (row : List ℕ) (j x : ℕ),
      List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun w _ ih j x => bAnd(strictB (B j) (fun b =>
          bIf(Nat.blt w (nat_lit 1755),
            bIf(Nat.beq (gp a (gp b (gp a (gp b w)))) w, false, true),
            bIf(Nat.beq w (nat_lit 1999), Nat.beq x (nat_lit 0), memK x ns))),
          strictB (Nat.succ j) (fun j' => strictB (Nat.succ x) (ih j')))) row j x = true →
      ∀ m < row.length, (∃ w < 1755, gp a (gp (B (j + m)) (gp a (gp (B (j + m)) w))) ≠ w) ∨
        x + m = 0 ∨ x + m ∈ ns := by
    intro a row
    induction row with
    | nil => intro j x _ m hm; simp at hm
    | cons w t ih =>
      intro j x h m hm
      simp only [strictB_eq', bAnd_eq', Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases m with
      | zero =>
        simp only [Nat.add_zero]
        cases hlt : Nat.blt w (nat_lit 1755)
        · simp only [hlt] at h1
          cases h99 : Nat.beq w (nat_lit 1999)
          · simp only [h99] at h1
            exact Or.inr (Or.inr (memK_iff.1 h1))
          · simp only [h99] at h1
            exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h1))
        · simp only [hlt] at h1
          have hw : w < 1755 := by simpa using hlt
          refine Or.inl ⟨w, hw, fun e => ?_⟩
          rw [e, Nat.beq_refl] at h1
          exact Bool.false_ne_true h1
      | succ m =>
        have := ih (Nat.succ j) (Nat.succ x)
          (by simpa only [strictB_eq', bAnd_eq', Bool.and_eq_true] using h2) m (by simpa using hm)
        have e1 : Nat.succ j + m = j + (m + 1) := by omega
        have e2 : Nat.succ x + m = x + (m + 1) := by omega
        rwa [e1, e2] at this
  intro i hi j hj
  have hr := (allL_iff L 0).1 h i hi
  rw [Nat.zero_add, strictB_eq'] at hr
  have hj' : j < L[i].length := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hj
  have := key _ L[i] 0 _ hr j hj'
  simpa [Nat.mul_eq, Nat.add_eq] using this

@[expose] def StepR (S M : Subgroup Pm) (Q : Pm → Prop) (x y : Pm) : Prop :=
  x ∈ S ∧ y ∈ S ∧ ∃ c ∈ M, Q c ∧ y = c * x * c⁻¹

theorem chain_of_cover {S M : Subgroup Pm} {Q : Pm → Prop} {a b : ℕ → Pm} {z t : Pm}
    {node : ℕ → Prop}
    (hcover : ∀ x ∈ S, ∃ i < 64, ∃ j < 64, x = a i * b j)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hcov : ∀ i < 64, ∀ j < 64, a i * b j * (a i * b j) ≠ 1 ∨ 64 * i + j = 0 ∨ node (64 * i + j))
    (hnode : ∀ i < 64, ∀ j < 64, node (64 * i + j) →
      Relation.ReflTransGen (StepR S M Q) z (a i * b j) ∨
        Relation.ReflTransGen (StepR S M Q) t (a i * b j)) :
    ∀ x ∈ S, x * x = 1 → x ≠ 1 →
      Relation.ReflTransGen (StepR S M Q) z x ∨ Relation.ReflTransGen (StepR S M Q) t x := by
  intro x hx h2 h1
  obtain ⟨i, hi, j, hj, rfl⟩ := hcover x hx
  rcases hcov i hi j hj with h | h | h
  · exact absurd h2 h
  · have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0 hj0
    exact absurd (by rw [ha0, hb0, one_mul]) h1
  · exact hnode i hi j hj h

theorem stepR_of_row {S M : Subgroup Pm} {Q : Pm → Prop} {base : List ℕ}
    (hfaith : ∀ x ∈ S, ∀ y ∈ S, (∀ q : Fin 1755, (q : ℕ) ∈ base →x q = y q) → x = y) {p x c : Pm}
    (hp : p ∈ S) (hx : x ∈ S) (hc : c ∈ M) (hQ : Q c) (hy : c⁻¹ * x * c ∈ S)
    (hagree : ∀ q : Fin 1755, (q : ℕ) ∈ base →(c⁻¹ * x * c) q = p q) : StepR S M Q p x := by
  have e := hfaith _ hy _ hp hagree
  refine ⟨hp, hx, c, hc, hQ, ?_⟩
  rw [← e]
  group

theorem smul_eq_of_maps {L : Finset (Fin 1755)} {y : Pm} (h : ∀ p ∈ L, y p ∈ L) : y • L = L := by
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_smul_finset])
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_smul_finset.1 hq
  exact h p hp

theorem fixCnt_sound {P : ℕ} {x : Pm} (hP : PR P x) :
    (Finset.univ.filter fun p : Fin 1755 => x p = p).card = fixCnt P := by
  have inner : ∀ (F : ℕ → ℕ) k,
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
        ∑ l ∈ Finset.range k, F l := by
    intro F k
    induction k with
    | zero => simp
    | succ k ih =>
      change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
      rw [ih, Finset.sum_range_succ, Nat.add_comm]
  have outer : ∀ (m : ℕ) (f : ℕ → ℕ) hi, CFSG.KC.Loop.sumBelow m hi f =
      ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m) := by
    intro m f hi
    induction hi with
    | zero => simp [CFSG.KC.Loop.sumBelow]
    | succ hi ih =>
      have e : CFSG.KC.Loop.sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0
          (fun l ih2 => Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i)
            (Nat.blt i m)) (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64)
          (CFSG.KC.Loop.sumBelow m hi f) := rfl
      have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
        change hi <<< 6 + l = _
        rw [Nat.shiftLeft_eq, Nat.mul_comm]
      rw [e, inner, ih, Nat.mul_succ, Finset.sum_range_add]
      simp only [e2]
      exact Nat.add_comm _ _
  have spec : ∀ {m hi : ℕ} (f : ℕ → ℕ), m ≤ 64 * hi →
      CFSG.KC.Loop.sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
    intro m hi f hm
    rw [outer]
    obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
    rw [hd, Finset.sum_range_add]
    have h2 : ∑ l ∈ Finset.range d,
        Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      have hb : Nat.blt (m + l) m = false := by
        cases e : Nat.blt (m + l) m
        · rfl
        · rw [Nat.blt_eq] at e
          omega
      rw [hb]
    rw [h2, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hb : Nat.blt i m = true := by
      rw [Nat.blt_eq]
      exact Finset.mem_range.1 hi
    rw [hb]
  have hsum : fixCnt P = ∑ i ∈ Finset.range 1755,
      Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (gp P i) i) := spec _ (by decide)
  rw [hsum, Finset.card_filter, Finset.sum_range]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [gp_eq hP p]
  by_cases e : x p = p
  · rw [if_pos e, e, Nat.beq_refl]
  · have hb : Nat.beq (x p : ℕ) p = false := by
      cases hb : Nat.beq (x p : ℕ) p
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)) e
    rw [if_neg e, hb]

@[expose] def PFixL (line : Fin 2925 → Finset (Fin 1755)) (t : Pm) (v : Fin 2925) : Prop :=
  ∀ p ∈ line v, t p = p

@[expose] def PLinkedL (line : Fin 2925 → Finset (Fin 1755)) (t : Pm) (v : Fin 2925) : Prop :=
  ∀ p ∈ line v, ∃ w, PFixL line t w ∧ w ≠ v ∧ p ∈ line w

theorem pflK_sound {lp : ℕ → ℕ} {line : Fin 2925 → Finset (Fin 1755)} {T : ℕ} {L : List ℕ}
    {t : Pm} (hT : PR T t)
    (hline : ∀ (v : Fin 2925) (p : Fin 1755), p ∈ line v ↔ ∃ k < 3, lp (3 * v + k) = p)
    (hL : ∀ v ∈ L, v < 2925) (hlp : ∀ i < 8775, lp i < 1755)
    (h : pflK lp T L = true) :
    PFixL line t 0 ∧ PLinkedL line t 0 ∧ ∀ v, PFixL line t v → PLinkedL line t v → v = 0 := by
  have bIf_true : ∀ c x y : Bool, Bool.rec (motive := fun _ => Bool) y x c = true →
      (c = true → x = true) ∧ (c = false → y = true) := by
    intro c x y
    cases c <;> simp
  have bor : ∀ c e : Bool, Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
    intro c e
    cases c <;> rfl
  have hlt : ∀ (v : Fin 2925) {k : ℕ}, k < 3 → lp (3 * v + k) < 1755 := fun v k hk =>
    hlp _ (by omega)
  have hfix : ∀ v : Fin 2925,
      PFixL line t v ↔ ∀ k < 3, gp T (lp (3 * v + k)) = lp (3 * v + k) := by
    intro v
    constructor
    · intro hv k hk
      have hp : (⟨lp (3 * v + k), hlt v hk⟩ : Fin 1755) ∈ line v := (hline v _).2 ⟨k, hk, rfl⟩
      exact (gp_eq hT ⟨_, hlt v hk⟩).trans (congrArg Fin.val (hv _ hp))
    · intro hv p hp
      obtain ⟨k, hk, e⟩ := (hline v p).1 hp
      apply Fin.ext
      rw [← gp_eq hT p, ← e]
      exact hv k hk
  have hpfix : ∀ v : Fin 2925, pfix lp T v = true ↔ PFixL line t v := by
    intro v
    rw [hfix v]
    unfold pfix
    simp only [bAnd_eq', Bool.and_eq_true, Nat.beq_eq, Nat.mul_eq, Nat.add_eq]
    constructor
    · rintro ⟨h0, h1, h2⟩ k hk
      interval_cases k
      · simpa using h0
      · exact h1
      · exact h2
    · intro hv
      exact ⟨by simpa using hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num)⟩
  have hon : ∀ p w : ℕ, onLine lp p w = true ↔ ∃ k < 3, lp (3 * w + k) = p := by
    intro p w
    unfold onLine
    simp only [bor, Bool.or_eq_true, Nat.beq_eq, Nat.mul_eq, Nat.add_eq]
    constructor
    · rintro (e | e | e)
      · exact ⟨0, by norm_num, by simpa using e.symm⟩
      · exact ⟨1, by norm_num, e.symm⟩
      · exact ⟨2, by norm_num, e.symm⟩
    · rintro ⟨k, hk, e⟩
      interval_cases k
      · exact Or.inl (by simpa using e.symm)
      · exact Or.inr (Or.inl e.symm)
      · exact Or.inr (Or.inr e.symm)
  unfold pflK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨hA, h0, hl0, hall⟩ := h
  have hmem : ∀ v : Fin 2925, (v : ℕ) ∈ L ↔ PFixL line t v := by
    intro v
    have hv := allN_iff.1 hA v v.2
    beta_reduce at hv
    obtain ⟨h1, h2⟩ := bIf_true _ _ _ hv
    rw [← hpfix v, ← memK_iff]
    cases hp : pfix lp T v
    · obtain ⟨h3, -⟩ := bIf_true _ _ _ (h2 hp)
      exact ⟨fun hm => h3 hm, fun e => absurd e (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => h1 hp⟩
  have hlink : ∀ v : Fin 2925, linkedK lp L v = true ↔ PLinkedL line t v := by
    intro v
    unfold linkedK
    rw [allN_iff]
    constructor
    · intro hk p hp
      obtain ⟨k, hk3, e⟩ := (hline v p).1 hp
      have h1 := hk k hk3
      beta_reduce at h1
      obtain ⟨w, hw, hw2⟩ := List.any_eq_true.1 h1
      simp only [bAnd_eq', Bool.and_eq_true] at hw2
      obtain ⟨hne, hon'⟩ := hw2
      have hwv : w ≠ v := fun e' => by
        rw [e', Nat.beq_refl] at hne
        exact absurd hne (by decide)
      obtain ⟨k', hk', e'⟩ := (hon _ _).1 hon'
      exact ⟨⟨w, hL w hw⟩, (hmem _).1 hw, fun e2 => hwv (congrArg Fin.val e2),
        (hline _ p).2 ⟨k', hk', e'.trans e⟩⟩
    · intro hv k hk
      beta_reduce
      have hp : (⟨lp (3 * v + k), hlt v hk⟩ : Fin 1755) ∈ line v := (hline v _).2 ⟨k, hk, rfl⟩
      obtain ⟨w, hw1, hw2, hw3⟩ := hv _ hp
      refine List.any_eq_true.2 ⟨w, (hmem w).2 hw1, ?_⟩
      simp only [bAnd_eq', Bool.and_eq_true]
      refine ⟨?_, (hon _ _).2 ((hline w _).1 hw3)⟩
      have hb : Nat.beq (w : ℕ) v = false := by
        cases e : Nat.beq (w : ℕ) v
        · rfl
        · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true e)) hw2
      rw [hb]
  refine ⟨(hmem 0).1 (memK_iff.1 h0), (hlink 0).1 hl0, fun v hv hv' => ?_⟩
  have hb := List.all_eq_true.1 hall v ((hmem v).2 hv)
  obtain ⟨h1, h2⟩ := bIf_true _ _ _ hb
  cases e : Nat.beq (v : ℕ) 0
  · obtain ⟨h3, -⟩ := bIf_true _ _ _ (h2 e)
    exact absurd (h3 ((hlink v).2 hv')) (by decide)
  · exact Fin.ext (Nat.eq_of_beq_eq_true e)

end CFSG.KC.TwoF4LieSound

end
