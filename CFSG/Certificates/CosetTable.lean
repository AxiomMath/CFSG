module

public import CFSG.Certificates.CosetEnumeration
public import Certificates.Data.CFSGNative.CosetTable.Enum
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

theorem getD_set! {α : Type*} (a : Array α) (i j : ℕ) (v d : α) :
    (a.set! i v).getD j d = if i = j ∧ i < a.size then v else a.getD j d := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem size_set! {α : Type*} (a : Array α) (i : ℕ) (v : α) : (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem getD_replicate {α : Type*} (n i : ℕ) (v : α) : (Array.replicate n v).getD i v = v := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem getD_range (n i : ℕ) : (Array.range n).getD i i = i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_range]
  split <;> rfl

variable {G : Type*} [Group G] (L : ℕ) (gen : ℕ → G) (H : Subgroup G)

noncomputable def rep (par : Array ℕ) (c : ℕ) : G :=
  if _h : 0 < par.getD c 0 / L ∧ par.getD c 0 / L < c then
    rep par (par.getD c 0 / L) * gen (par.getD c 0 % L)
  else 1
termination_by c
decreasing_by exact _h.2

theorem rep_eq (par : Array ℕ) (c : ℕ) :
    rep L gen par c = if 0 < par.getD c 0 / L ∧ par.getD c 0 / L < c then
      rep L gen par (par.getD c 0 / L) * gen (par.getD c 0 % L) else 1 := by
  rw [rep]
  split <;> simp_all

theorem rep_congr (par par' : Array ℕ) (b : ℕ)
    (h : ∀ c ≤ b, par.getD c 0 = par'.getD c 0) : rep L gen par b = rep L gen par' b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    conv_lhs => rw [rep_eq]
    conv_rhs => rw [rep_eq]
    rw [h b le_rfl]
    split
    · rename_i hc
      rw [ih _ hc.2 (fun c hc' => h c (by omega))]
    · rfl

def Rel (par : Array ℕ) (a : ℕ) (g : G) (b : ℕ) : Prop :=
  rep L gen par a * g * (rep L gen par b)⁻¹ ∈ H

variable {L gen H}

theorem rel_iff {par : Array ℕ} {a b : ℕ} {g : G} :
    Rel L gen H par a g b ↔ rep L gen par a * g * (rep L gen par b)⁻¹ ∈ H := Iff.rfl

theorem Rel.refl (par : Array ℕ) (a : ℕ) : Rel L gen H par a 1 a := by
  simp [Rel]

theorem Rel.trans {par : Array ℕ} {a b c : ℕ} {g h : G} (h₁ : Rel L gen H par a g b)
    (h₂ : Rel L gen H par b h c) : Rel L gen H par a (g * h) c := by
  have := H.mul_mem h₁ h₂
  unfold Rel at *
  simpa [mul_assoc] using this

theorem Rel.symm {par : Array ℕ} {a b : ℕ} {g : G} (h : Rel L gen H par a g b) :
    Rel L gen H par b g⁻¹ a := by
  have := H.inv_mem h
  unfold Rel at *
  simpa [mul_assoc] using this

theorem Rel.of_eq {par : Array ℕ} {a b : ℕ} {g g' : G} (h : Rel L gen H par a g b) (e : g = g') :
    Rel L gen H par a g' b := e ▸ h

theorem rel_congr {par par' : Array ℕ} {a b : ℕ} {g : G}
    (h : ∀ c ≤ max a b, par.getD c 0 = par'.getD c 0) :
    Rel L gen H par a g b ↔ Rel L gen H par' a g b := by
  unfold Rel
  rw [rep_congr L gen par par' a (fun c hc => h c (by omega)),
    rep_congr L gen par par' b (fun c hc => h c (by omega))]


variable (L gen H) in
structure Inv (tab fwd par : Array ℕ) (next : ℕ) : Prop where
  tab_lt : ∀ e, tab.getD e 0 ≠ 0 → tab.getD e 0 < next
  tab_row : ∀ e, tab.getD e 0 ≠ 0 → e / L < next
  tab_rel : ∀ e, tab.getD e 0 ≠ 0 → Rel L gen H par (e / L) (gen (e % L)) (tab.getD e 0)
  fwd_lt : ∀ c < next, fwd.getD c c < next
  fwd_rel : ∀ c < next, Rel L gen H par c 1 (fwd.getD c c)
  fwd_fresh : ∀ c, next ≤ c → fwd.getD c c = c
  next_two : 2 ≤ next
  par_one : par.getD 1 0 = 0

variable (L gen H) in
abbrev SInv (st : St) : Prop := Inv L gen H st.tab st.fwd st.par st.next

theorem Inv.rep_one {st : St} (h : SInv L gen H st) : rep L gen st.par 1 = 1 := by
  rw [rep_eq, h.par_one]
  simp

theorem Inv.set_tab {tab fwd par : Array ℕ} {next : ℕ} (h : Inv L gen H tab fwd par next)
    {e v : ℕ} (hv : v ≠ 0 → v < next ∧ e / L < next ∧ Rel L gen H par (e / L) (gen (e % L)) v) :
    Inv L gen H (tab.set! e v) fwd par next := by
  constructor
  · intro e' he'
    rw [getD_set!] at he' ⊢
    split at he' <;> rename_i hh
    · rw [ite_eq_left hh]; exact (hv he').1
    · rw [ite_eq_right hh]; exact h.tab_lt e' he'
  · intro e' he'
    rw [getD_set!] at he'
    split at he' <;> rename_i hh
    · obtain ⟨rfl, -⟩ := hh; exact (hv he').2.1
    · exact h.tab_row e' he'
  · intro e' he'
    rw [getD_set!] at he' ⊢
    split at he' <;> rename_i hh
    · rw [ite_eq_left hh]; obtain ⟨rfl, -⟩ := hh; exact (hv he').2.2
    · rw [ite_eq_right hh]; exact h.tab_rel e' he'
  · exact h.fwd_lt
  · exact h.fwd_rel
  · exact h.fwd_fresh
  · exact h.next_two
  · exact h.par_one

theorem Inv.set_fwd {st : St} (h : SInv L gen H st) {c d : ℕ} (hc : c < st.next)
    (hd : d < st.next) (hcd : Rel L gen H st.par c 1 d) :
    Inv L gen H st.tab (st.fwd.set! c d) st.par st.next := by
  constructor
  · exact h.tab_lt
  · exact h.tab_row
  · exact h.tab_rel
  · intro c' hc'
    rw [getD_set!]
    split <;> rename_i hh
    · exact hd
    · exact h.fwd_lt c' hc'
  · intro c' hc'
    rw [getD_set!]
    split <;> rename_i hh
    · obtain ⟨rfl, -⟩ := hh; exact hcd
    · exact h.fwd_rel c' hc'
  · intro c' hc'
    rw [getD_set!]
    split <;> rename_i hh
    · obtain ⟨rfl, -⟩ := hh; omega
    · exact h.fwd_fresh c' hc'
  · exact h.next_two
  · exact h.par_one

theorem div_mod_letter {c x : ℕ} (hx : x < L) : (c * L + x) / L = c ∧ (c * L + x) % L = x := by
  have hL : 0 < L := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hx, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem walk_spec {st : St} (h : SInv L gen H st) :
    ∀ (w : List ℕ) (lim k c : ℕ), (∀ y ∈ w, y < L) →
      k ≤ (walk L st.tab lim k c w).1 ∧ (walk L st.tab lim k c w).1 - k ≤ w.length ∧
      Rel L gen H st.par c (evalWord gen (w.take ((walk L st.tab lim k c w).1 - k)))
        (walk L st.tab lim k c w).2 ∧
      (c < st.next → (walk L st.tab lim k c w).2 < st.next) := by
  intro w
  induction w with
  | nil => intro lim k c _; simp [walk, Rel.refl]
  | cons y w ih =>
    intro lim k c hw
    have hy : y < L := hw y (by simp)
    have hw' : ∀ y ∈ w, y < L := fun y' hy' => hw y' (by simp [hy'])
    cases lim with
    | zero => simp [walk, Rel.refl]
    | succ lim =>
      simp only [walk]
      split
      · simp [Rel.refl]
      · rename_i hd
        have hd' : st.tab.getD (c * L + y) 0 ≠ 0 := by simpa using hd
        obtain ⟨h1, h2, h3, h4⟩ := ih lim (k + 1) (st.tab.getD (c * L + y) 0) hw'
        obtain ⟨hdiv, hmod⟩ := div_mod_letter (c := c) hy
        have hrel := h.tab_rel _ hd'
        rw [hdiv, hmod] at hrel
        refine ⟨by omega, ?_, ?_, fun _ => h4 (h.tab_lt _ hd')⟩
        · rw [List.length_cons]; omega
        have hk : (walk L st.tab lim (k + 1) (st.tab.getD (c * L + y) 0) w).1 - k =
            ((walk L st.tab lim (k + 1) (st.tab.getD (c * L + y) 0) w).1 - (k + 1)) + 1 := by
          omega
        rw [hk, List.take_succ_cons, evalWord_cons]
        exact hrel.trans h3

theorem find_spec {st : St} (h : SInv L gen H st) :
    ∀ (fuel c : ℕ), Rel L gen H st.par c 1 (find st.fwd fuel c) ∧
      (c < st.next → find st.fwd fuel c < st.next) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact ⟨Rel.refl _ _, id⟩
  | succ fuel ih =>
    intro c
    simp only [find]
    split
    · exact ⟨Rel.refl _ _, id⟩
    · by_cases hc : c < st.next
      · obtain ⟨h1, h2⟩ := ih (st.fwd.getD c c)
        exact ⟨(h.fwd_rel c hc).trans h1 |>.of_eq (by simp), fun _ => h2 (h.fwd_lt c hc)⟩
      · have := h.fwd_fresh c (by omega)
        rename_i hne
        exact absurd (by simpa using this) hne

theorem merge_inv {st : St} (h : SInv L gen H st) {a b : ℕ}
    (hab : Rel L gen H st.par a 1 b) : SInv L gen H (merge st a b) := by
  unfold merge
  dsimp only
  obtain ⟨ha1, ha2⟩ := find_spec h st.next a
  obtain ⟨hb1, hb2⟩ := find_spec h st.next b
  split
  · exact h
  · rename_i hne
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_le] at hne
    obtain ⟨⟨-, hra⟩, hrb⟩ := hne
    have hr : Rel L gen H st.par (find st.fwd st.next a) 1 (find st.fwd st.next b) :=
      (ha1.symm.trans (hab.trans hb1)).of_eq (by simp)
    split
    · exact h.set_fwd (c := find st.fwd st.next b) hrb hra (hr.symm.of_eq (by simp))
    · exact h.set_fwd (c := find st.fwd st.next a) hra hrb hr


variable (gen H) in
structure Good (P : Params) : Prop where
  inv_lt : ∀ x < P.L, P.inv.getD x 0 < P.L
  gen_inv : ∀ x < P.L, gen (P.inv.getD x 0) = (gen x)⁻¹
  scans : ∀ x, ∀ p ∈ P.scans.getD x [],
    p.2 = invWord P.inv p.1 ∧ (∀ y ∈ p.1, y < P.L) ∧ evalWord gen p.1 = 1
  subs : ∀ p ∈ P.subs, p.2 = invWord P.inv p.1 ∧ (∀ y ∈ p.1, y < P.L) ∧ evalWord gen p.1 ∈ H
  rels : ∀ p ∈ P.rels, p.2 = invWord P.inv p.1 ∧ (∀ y ∈ p.1, y < P.L) ∧ evalWord gen p.1 = 1

variable {P : Params}

theorem Inv.set_pair (hP : Good gen H P) {tab fwd par : Array ℕ} {next : ℕ}
    (h : Inv P.L gen H tab fwd par next) {f x b : ℕ}
    (hx : x < P.L) (hf : f < next) (hb : b < next) (hr : Rel P.L gen H par f (gen x) b) :
    Inv P.L gen H ((tab.set! (f * P.L + x) b).set! (b * P.L + P.inv.getD x 0) f) fwd par next := by
  have hix := hP.inv_lt x hx
  obtain ⟨d1, m1⟩ := div_mod_letter (c := f) hx
  obtain ⟨d2, m2⟩ := div_mod_letter (c := b) hix
  have h1 : Inv P.L gen H (tab.set! (f * P.L + x) b) fwd par next :=
    h.set_tab (fun _ => ⟨hb, by rw [d1]; exact hf, by rw [d1, m1]; exact hr⟩)
  exact h1.set_tab (fun _ => ⟨hf, by rw [d2]; exact hb, by
      rw [d2, m2, hP.gen_inv x hx]; exact hr.symm⟩)

theorem coincLetter_inv (hP : Good gen H P) {st : St} (h : SInv P.L gen H st) {g x : ℕ}
    (hx : x < P.L) : SInv P.L gen H (coincLetter P st g x) := by
  unfold coincLetter
  dsimp only
  split
  · exact h
  · rename_i hd0
    have hd : st.tab.getD (g * P.L + x) 0 ≠ 0 := by simpa using hd0
    obtain ⟨dg, mg⟩ := div_mod_letter (c := g) hx
    have hgd := h.tab_rel _ hd
    rw [dg, mg] at hgd
    have hdlt := h.tab_lt _ hd
    have hglt := h.tab_row _ hd
    rw [dg] at hglt
    have hix := hP.inv_lt x hx
    have hgi := hP.gen_inv x hx
    have key : ∀ st1 : St, SInv P.L gen H st1 → st1.fwd = st.fwd → st1.par = st.par →
        st1.next = st.next → SInv P.L gen H (
          if st1.tab.getD (find st1.fwd st1.next g * P.L + x) 0 != 0 then
            merge st1 (find st1.fwd st1.next (st.tab.getD (g * P.L + x) 0))
              (st1.tab.getD (find st1.fwd st1.next g * P.L + x) 0)
          else if st1.tab.getD (find st1.fwd st1.next (st.tab.getD (g * P.L + x) 0) * P.L +
              P.inv.getD x 0) 0 != 0 then
            merge st1 (find st1.fwd st1.next g)
              (st1.tab.getD (find st1.fwd st1.next (st.tab.getD (g * P.L + x) 0) * P.L +
                P.inv.getD x 0) 0)
          else { st1 with
            tab := (st1.tab.set! (find st1.fwd st1.next g * P.L + x)
              (find st1.fwd st1.next (st.tab.getD (g * P.L + x) 0))).set!
              (find st1.fwd st1.next (st.tab.getD (g * P.L + x) 0) * P.L + P.inv.getD x 0)
              (find st1.fwd st1.next g),
            ded := st1.ded.push (find st1.fwd st1.next g * P.L + x) }) := by
      intro st1 h1 hfwd hpar hnext
      set d := st.tab.getD (g * P.L + x) 0 with hdd
      have hgd1 : Rel P.L gen H st1.par g (gen x) d := hpar ▸ hgd
      obtain ⟨hmu1, hmu2⟩ := find_spec h1 st1.next g
      obtain ⟨hnu1, hnu2⟩ := find_spec h1 st1.next d
      set mu := find st1.fwd st1.next g
      set nu := find st1.fwd st1.next d
      have hmu : mu < st1.next := hmu2 (by rw [hnext]; exact hglt)
      have hnu : nu < st1.next := hnu2 (by rw [hnext]; exact hdlt)
      have hmn : Rel P.L gen H st1.par mu (gen x) nu :=
        ((hmu1.symm.trans hgd1).trans hnu1).of_eq (by simp)
      split
      · rename_i he0
        have he : st1.tab.getD (mu * P.L + x) 0 ≠ 0 := by simpa using he0
        obtain ⟨dm, mm⟩ := div_mod_letter (c := mu) hx
        have hme := h1.tab_rel _ he
        rw [dm, mm] at hme
        exact merge_inv h1 ((hmn.symm.trans hme).of_eq (by simp))
      · split
        · rename_i _ he0
          have he : st1.tab.getD (nu * P.L + P.inv.getD x 0) 0 ≠ 0 := by simpa using he0
          obtain ⟨dn, mn⟩ := div_mod_letter (c := nu) hix
          have hne := h1.tab_rel _ he
          rw [dn, mn, hgi] at hne
          exact merge_inv h1 ((hmn.trans hne).of_eq (by simp))
        · exact Inv.set_pair hP h1 hx hmu hnu hmn
    split
    · refine key _ ?_ rfl rfl rfl
      exact h.set_tab (by simp)
    · exact key st h rfl rfl rfl

theorem coincRow_inv (hP : Good gen H P) {g : ℕ} :
    ∀ (n : ℕ), n ≤ P.L → ∀ st : St, SInv P.L gen H st → SInv P.L gen H (coincRow P g n st) := by
  intro n
  induction n with
  | zero => intro _ st h; exact h
  | succ n ih =>
    intro hn st h
    exact ih (by omega) _ (coincLetter_inv hP h (by omega))

theorem coincQueue_inv (hP : Good gen H P) :
    ∀ (fuel : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (coincQueue P fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    simp only [coincQueue]
    split
    · exact ih _ (coincRow_inv hP P.L le_rfl { st with qi := st.qi + 1 } h)
    · exact h

theorem coincidence_inv (hP : Good gen H P) {st : St} (h : SInv P.L gen H st) {a b : ℕ}
    (hab : Rel P.L gen H st.par a 1 b) : SInv P.L gen H (coincidence P st a b) :=
  coincQueue_inv hP _ _ (merge_inv h hab)

theorem deduce_inv (hP : Good gen H P) {st : St} (h : SInv P.L gen H st) {f x b : ℕ}
    (hr : Rel P.L gen H st.par f (gen x) b) : SInv P.L gen H (deduce P st f x b) := by
  unfold deduce
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact Inv.set_pair hP h hc.2 hc.1.1 hc.1.2 hr
  · exact h


theorem define_inv (hP : Good gen H P) {st : St} (h : SInv P.L gen H st) (a x : ℕ) :
    SInv P.L gen H (define P st a x) := by
  unfold define
  dsimp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨ha0, hab⟩, hx⟩, hbs⟩ := hc
    set b := st.next
    set par' := st.par.set! b (a * P.L + x)
    have hpar : ∀ c < b, st.par.getD c 0 = par'.getD c 0 := by
      intro c hc
      rw [getD_set!, ite_eq_right (by omega)]
    have hrel : ∀ {u v : ℕ} {g : G}, u < b → v < b →
        (Rel P.L gen H st.par u g v ↔ Rel P.L gen H par' u g v) := fun hu hv =>
      rel_congr (fun c hc => hpar c (by omega))
    have h0 : Inv P.L gen H st.tab st.fwd par' (b + 1) := by
      constructor
      · exact fun e he => Nat.lt_succ_of_lt (h.tab_lt e he)
      · exact fun e he => Nat.lt_succ_of_lt (h.tab_row e he)
      · exact fun e he => (hrel (h.tab_row e he) (h.tab_lt e he)).mp (h.tab_rel e he)
      · intro c hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
        · exact Nat.lt_succ_of_lt (h.fwd_lt c hc)
        · rw [h.fwd_fresh _ le_rfl]; omega
      · intro c hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
        · exact (hrel hc (h.fwd_lt c hc)).mp (h.fwd_rel c hc)
        · rw [h.fwd_fresh _ le_rfl]; exact Rel.refl _ _
      · exact fun c hc => h.fwd_fresh c (by omega)
      · have := h.next_two; omega
      · rw [← hpar 1 (by have := h.next_two; omega)]; exact h.par_one
    have hrep : rep P.L gen par' b = rep P.L gen par' a * gen x := by
      rw [rep_eq]
      have hd : par'.getD b 0 = a * P.L + x := by rw [getD_set!, ite_eq_left ⟨rfl, hbs⟩]
      obtain ⟨dd, mm⟩ := div_mod_letter (c := a) hx
      rw [hd, dd, mm, ite_eq_left ⟨ha0, hab⟩]
    have hnew : Rel P.L gen H par' a (gen x) b := by
      unfold Rel; rw [hrep]; simp
    exact Inv.set_pair hP h0 hx (by omega) (by omega) hnew
  · exact h

theorem evalWord_append' (u v : List ℕ) :
    evalWord gen (u ++ v) = evalWord gen u * evalWord gen v := by
  simp [evalWord, List.map_append, List.prod_append]

theorem evalWord_split (w : List ℕ) {i : ℕ} (hi : i < w.length) :
    evalWord gen w = evalWord gen (w.take i) * gen (w.getD i 0) * evalWord gen (w.drop (i + 1)) := by
  conv_lhs => rw [← List.take_append_drop i w, List.drop_eq_getElem_cons hi]
  rw [evalWord_append', evalWord_cons, List.getD_eq_getElem _ _ hi, mul_assoc]

theorem evalWord_take_invWord (hP : Good gen H P) (w : List ℕ) (hw : ∀ y ∈ w, y < P.L)
    (j : ℕ) :
    evalWord gen ((invWord P.inv w).take j) = (evalWord gen (w.drop (w.length - j)))⁻¹ := by
  have key : ∀ u : List ℕ, (∀ y ∈ u, y < P.L) →
      evalWord gen (u.reverse.map fun x => P.inv.getD x 0) = (evalWord gen u)⁻¹ := by
    intro u
    induction u with
    | nil => intro _; simp [evalWord]
    | cons y u ih =>
      intro hu
      have hy : evalWord gen [P.inv.getD y 0] = (gen y)⁻¹ := by
        rw [evalWord_cons, evalWord_nil, mul_one, hP.gen_inv y (hu y (by simp))]
      rw [List.reverse_cons, List.map_append, evalWord_append',
        ih (fun y' hy' => hu y' (by simp [hy'])), List.map_cons, List.map_nil, hy, evalWord_cons,
        mul_inv_rev]
  rw [invWord, ← List.map_take, List.take_reverse]
  exact key _ (fun y hy => hw y (List.mem_of_mem_drop hy))

variable (gen H) in
def ScanOK (par : Array ℕ) : Scan → Prop
  | .closed => True
  | .coinc f b => Rel P.L gen H par f 1 b
  | .deduct f x b => Rel P.L gen H par f (gen x) b
  | .gap _ _ => True

theorem scanWord_spec (hP : Good gen H P) {st : St} (h : SInv P.L gen H st) (a : ℕ)
    (w : List ℕ) (hw : ∀ y ∈ w, y < P.L)
    (hcyc : Rel P.L gen H st.par a (evalWord gen w) a) :
    ScanOK (P := P) gen H st.par (scanWord P.L st.tab a w (invWord P.inv w)) := by
  have hw' : ∀ y ∈ invWord P.inv w, y < P.L := by
    intro y hy
    simp only [invWord, List.mem_map, List.mem_reverse] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hP.inv_lt z (hw z hz)
  have hlen : (invWord P.inv w).length = w.length := by simp [invWord]
  obtain ⟨-, hi1, hi2, -⟩ := walk_spec h w w.length 0 a hw
  unfold scanWord
  dsimp only
  set i := (walk P.L st.tab w.length 0 a w).1
  set f := (walk P.L st.tab w.length 0 a w).2
  simp only [Nat.sub_zero] at hi1 hi2
  split
  · rename_i hir
    have hir' : i = w.length := by simpa using hir
    rw [hir', List.take_length] at hi2
    split
    · trivial
    · exact (hi2.symm.trans hcyc).of_eq (by simp)
  · rename_i hir
    have hir' : i < w.length := by simp at hir; omega
    obtain ⟨-, hj1, hj2, -⟩ := walk_spec h (invWord P.inv w) (w.length - i) 0 a hw'
    set j := (walk P.L st.tab (w.length - i) 0 a (invWord P.inv w)).1
    set b := (walk P.L st.tab (w.length - i) 0 a (invWord P.inv w)).2
    simp only [Nat.sub_zero] at hj1 hj2
    rw [evalWord_take_invWord hP w hw] at hj2
    split
    · rename_i hjr
      have hjr' : j = w.length - i := by simpa using hjr
      rw [hjr', show w.length - (w.length - i) = i by omega] at hj2
      split
      · trivial
      · refine ((hi2.symm.trans hcyc).trans hj2).of_eq ?_
        have hsplit : evalWord gen w = evalWord gen (w.take i) * evalWord gen (w.drop i) := by
          conv_lhs => rw [← List.take_append_drop i w]
          exact evalWord_append' _ _
        rw [hsplit]
        group
    · split
      · rename_i _ hjr
        have hjr' : j + 1 = w.length - i := by simpa using hjr
        rw [show w.length - j = i + 1 by omega] at hj2
        refine ((hi2.symm.trans hcyc).trans hj2).of_eq ?_
        rw [evalWord_split w hir']
        group
      · trivial

theorem scan_inv (hP : Good gen H P) {st : St} (h : SInv P.L gen H st) (a : ℕ) (w : List ℕ)
    (hw : ∀ y ∈ w, y < P.L) (hcyc : Rel P.L gen H st.par a (evalWord gen w) a) :
    SInv P.L gen H (scan P st a w (invWord P.inv w)) := by
  have hs := scanWord_spec hP h a w hw hcyc
  unfold scan
  revert hs
  generalize scanWord P.L st.tab a w (invWord P.inv w) = r
  intro hs
  cases r with
  | closed => exact h
  | coinc f b => exact coincidence_inv hP h hs
  | deduct f x b => exact deduce_inv hP h hs
  | gap f x => exact h

theorem scanAll_inv (hP : Good gen H P) (a : ℕ) :
    ∀ (ps : List (List ℕ × List ℕ)), (∀ p ∈ ps,
      p.2 = invWord P.inv p.1 ∧ (∀ y ∈ p.1, y < P.L) ∧ evalWord gen p.1 = 1) →
      ∀ st : St, SInv P.L gen H st → SInv P.L gen H (scanAll P a ps st) := by
  intro ps
  induction ps with
  | nil => intro _ st h; exact h
  | cons p ps ih =>
    intro hps st h
    simp only [scanAll]
    split
    · obtain ⟨h1, h2, h3⟩ := hps p (by simp)
      apply ih (fun q hq => hps q (by simp [hq]))
      rw [h1]
      exact scan_inv hP h a p.1 h2 (by rw [h3]; exact Rel.refl _ _)
    · exact h

theorem processDed_inv (hP : Good gen H P) :
    ∀ (fuel : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (processDed P fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    simp only [processDed]
    split
    · exact h
    · split
      · exact ih _ (scanAll_inv hP _ _ (hP.scans _) _ h)
      · exact ih _ h

theorem fillWord_inv (hP : Good gen H P) (w : List ℕ) (hw : ∀ y ∈ w, y < P.L)
    (hwH : evalWord gen w ∈ H) :
    ∀ (fuel : ℕ) (st : St), SInv P.L gen H st →
      SInv P.L gen H (fillWord P w (invWord P.inv w) fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    have hcyc : Rel P.L gen H st.par 1 (evalWord gen w) 1 := by
      unfold Rel; rw [h.rep_one]; simpa using hwH
    have hs := scanWord_spec hP h 1 w hw hcyc
    simp only [fillWord]
    revert hs
    generalize scanWord P.L st.tab 1 w (invWord P.inv w) = r
    intro hs
    cases r with
    | closed => exact h
    | coinc f b => exact coincidence_inv hP h hs
    | deduct f x b => exact deduce_inv hP h hs
    | gap f x =>
      dsimp only
      have hd := define_inv hP h f x
      split
      · exact hd
      · exact ih _ hd

theorem fillSubs_inv (hP : Good gen H P) (fuel : ℕ) :
    ∀ (ps : List (List ℕ × List ℕ)), (∀ p ∈ ps,
      p.2 = invWord P.inv p.1 ∧ (∀ y ∈ p.1, y < P.L) ∧ evalWord gen p.1 ∈ H) →
      ∀ st : St, SInv P.L gen H st → SInv P.L gen H (fillSubs P fuel ps st) := by
  intro ps
  induction ps with
  | nil => intro _ st h; exact h
  | cons p ps ih =>
    intro hps st h
    simp only [fillSubs]
    obtain ⟨h1, h2, h3⟩ := hps p (by simp)
    apply ih (fun q hq => hps q (by simp [hq]))
    apply processDed_inv hP
    rw [h1]
    exact fillWord_inv hP p.1 h2 h3 _ _ h

theorem fillRow_inv (hP : Good gen H P) (fuel c : ℕ) :
    ∀ (n : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (fillRow P fuel c n st) := by
  intro n
  induction n with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    simp only [fillRow]
    split
    · exact h
    · split
      · exact ih _ (processDed_inv hP _ _ (define_inv hP h _ _))
      · exact ih _ h

theorem felsch_inv (hP : Good gen H P) (fuel : ℕ) :
    ∀ (n c : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (felsch P fuel n c st) := by
  intro n
  induction n with
  | zero => intro c st h; exact h
  | succ n ih =>
    intro c st h
    simp only [felsch]
    split
    · exact ih _ _ (fillRow_inv hP fuel c P.L st h)
    · exact h

theorem hltWord_inv (hP : Good gen H P) (c : ℕ) (w : List ℕ) (hw : ∀ y ∈ w, y < P.L)
    (hw1 : evalWord gen w = 1) :
    ∀ (fuel : ℕ) (st : St), SInv P.L gen H st →
      SInv P.L gen H (hltWord P c w (invWord P.inv w) fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    have hcyc : Rel P.L gen H st.par c (evalWord gen w) c := by rw [hw1]; exact Rel.refl _ _
    have hs := scanWord_spec hP h c w hw hcyc
    simp only [hltWord]
    split
    · exact h
    · revert hs
      generalize scanWord P.L st.tab c w (invWord P.inv w) = r
      intro hs
      cases r with
      | closed => exact h
      | coinc f b => exact coincidence_inv hP h hs
      | deduct f x b => exact deduce_inv hP h hs
      | gap f x =>
        dsimp only
        have hd := define_inv hP h f x
        split
        · exact hd
        · exact ih _ hd

theorem hltRow_inv (hP : Good gen H P) (fuel c : ℕ) :
    ∀ (ps : List (List ℕ × List ℕ)), (∀ p ∈ ps,
      p.2 = invWord P.inv p.1 ∧ (∀ y ∈ p.1, y < P.L) ∧ evalWord gen p.1 = 1) →
      ∀ st : St, SInv P.L gen H st → SInv P.L gen H (hltRow P fuel c ps st) := by
  intro ps
  induction ps with
  | nil => intro _ st h; exact h
  | cons p ps ih =>
    intro hps st h
    simp only [hltRow]
    split
    · exact h
    · obtain ⟨h1, h2, h3⟩ := hps p (by simp)
      apply ih (fun q hq => hps q (by simp [hq]))
      apply processDed_inv hP
      rw [h1]
      exact hltWord_inv hP c p.1 h2 h3 _ _ h

theorem hlt_inv (hP : Good gen H P) (fuel : ℕ) :
    ∀ (n c : ℕ) (st : St), SInv P.L gen H st → SInv P.L gen H (hlt P fuel n c st) := by
  intro n
  induction n with
  | zero => intro c st h; exact h
  | succ n ih =>
    intro c st h
    simp only [hlt]
    split
    · exact ih _ _ (hltRow_inv hP fuel c P.rels hP.rels st h)
    · exact h

theorem init_inv (cap : ℕ) : SInv P.L gen H (St.init P.L cap) := by
  constructor
  all_goals simp only [St.init]
  · intro e he; exact absurd (getD_replicate _ e 0) he
  · intro e he; exact absurd (getD_replicate _ e 0) he
  · intro e he; exact absurd (getD_replicate _ e 0) he
  · intro c hc; rw [getD_range]; exact hc
  · intro c _; rw [getD_range]; exact Rel.refl _ _
  · intro c _; exact getD_range _ c
  · exact le_rfl
  · exact getD_replicate _ 1 0

theorem enumerate_inv (hP : Good gen H P) (cap : ℕ) : SInv P.L gen H (enumerate P cap) :=
  felsch_inv hP _ _ _ _ (fillSubs_inv hP _ _ hP.subs _ (init_inv cap))

theorem enumerateHLT_inv (hP : Good gen H P) (cap : ℕ) : SInv P.L gen H (enumerateHLT P cap) :=
  felsch_inv hP _ _ _ _ (hlt_inv hP _ _ _ _ (fillSubs_inv hP _ _ hP.subs _ (init_inv cap)))


theorem allBelow_iff (p : ℕ → Bool) : ∀ n, allBelow p n = true ↔ ∀ i < n, p i = true := by
  intro n
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem countBelowAux_eq (p : ℕ → Bool) :
    ∀ n acc, countBelowAux p n acc = acc + ((Finset.range n).filter fun i => p i = true).card := by
  intro n
  induction n with
  | zero => intro acc; simp [countBelowAux]
  | succ n ih =>
    intro acc
    rw [countBelowAux, ih, Finset.range_add_one, Finset.filter_insert]
    cases h : p n
    · simp
    · simp only [↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega

theorem countBelow_eq (p : ℕ → Bool) :
    ∀ n, countBelow p n = ((Finset.range n).filter fun i => p i = true).card := by
  intro n
  rw [countBelow, countBelowAux_eq, Nat.zero_add]

theorem index_le_of_complete (hP : Good gen H P)
    (hgen : Subgroup.closure (gen '' Set.Iio P.L) = ⊤) {st : St} (h : SInv P.L gen H st)
    (hc : st.complete P.L = true) : H.FiniteIndex ∧ H.index ≤ st.liveCount := by
  unfold St.complete at hc
  rw [Bool.and_eq_true, allBelow_iff] at hc
  obtain ⟨h1, hrow⟩ := hc
  have hlive : ∀ c, st.live c = true → 0 < c ∧ c < st.next := by
    intro c hc
    simp only [St.live, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2⟩
  have hstep : ∀ c, st.live c = true → ∀ x < P.L, st.live (st.tab.getD (c * P.L + x) 0) = true ∧
      Rel P.L gen H st.par c (gen x) (st.tab.getD (c * P.L + x) 0) := by
    intro c hc x hx
    have hr := hrow c (hlive c hc).2
    simp only [hc, Bool.not_true, Bool.false_or, allBelow_iff] at hr
    have hl := hr x hx
    refine ⟨hl, ?_⟩
    have hne : st.tab.getD (c * P.L + x) 0 ≠ 0 := by
      have := (hlive _ hl).1; omega
    have := h.tab_rel _ hne
    obtain ⟨dd, mm⟩ := div_mod_letter (c := c) hx
    rwa [dd, mm] at this
  have key : ∀ g : G, ∃ c, st.live c = true ∧ Rel P.L gen H st.par 1 g c := by
    intro g
    have hg : g ∈ Subgroup.closure (gen '' Set.Iio P.L) := hgen ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨1, h1, Rel.refl _ _⟩
    | mul_right g _ y hy ih =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨c, hc, hr⟩ := ih
      obtain ⟨hl, hr'⟩ := hstep c hc x hx
      exact ⟨_, hl, hr.trans hr'⟩
    | mul_inv_cancel g _ y hy ih =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨c, hc, hr⟩ := ih
      obtain ⟨hl, hr'⟩ := hstep c hc _ (hP.inv_lt x hx)
      exact ⟨_, hl, (hr.trans hr').of_eq (by rw [hP.gen_inv x hx])⟩
  set S := (Finset.range st.next).filter (fun c => st.live c = true)
  have hsurj : Function.Surjective
      (fun c : S => (QuotientGroup.mk (rep P.L gen st.par c)⁻¹ : G ⧸ H)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨c, hc, hr⟩ := key y⁻¹
      refine ⟨⟨c, by simp [S, hc, (hlive c hc).2]⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      have := H.inv_mem hr
      rw [h.rep_one] at this
      simpa [mul_inv_rev] using this
  have hfin : Finite (G ⧸ H) := Finite.of_surjective _ hsurj
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  rw [Subgroup.index_eq_card, St.liveCount, countBelow_eq]
  have := Nat.card_le_card_of_surjective _ hsurj
  simpa [Nat.card_eq_fintype_card] using this

theorem index_le_of_check (hP : Good gen H P)
    (hgen : Subgroup.closure (gen '' Set.Iio P.L) = ⊤) {cap n : ℕ} (h : check P cap n = true) :
    H.FiniteIndex ∧ H.index ≤ n := by
  unfold check at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨-, hc⟩, hn⟩ := h
  rw [← hn]
  exact index_le_of_complete hP hgen (enumerate_inv hP cap) hc

theorem index_le_of_checkHLT (hP : Good gen H P)
    (hgen : Subgroup.closure (gen '' Set.Iio P.L) = ⊤) {cap n : ℕ} (h : checkHLT P cap n = true) :
    H.FiniteIndex ∧ H.index ≤ n := by
  unfold checkHLT at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨-, hc⟩, hn⟩ := h
  rw [← hn]
  exact index_le_of_complete hP hgen (enumerateHLT_inv hP cap) hc

end CFSG.CosetTable
