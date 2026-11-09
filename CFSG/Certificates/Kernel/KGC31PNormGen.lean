module

public import CFSG.Certificates.Kernel.KGC31PNormSound
public import CFSG.Certificates.Kernel.KGC31PBSound
public import Certificates.Data.Kernel.KGC31PSplit
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK

variable {n w : Nat}

theorem pnormAll_pc (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hok : pspanOK n w bs = true) {g t : Nat} (hg : PP n w g) (ht : PP n w t)
    (h1 : pnormAll n w bs g (pinv n w g) = true) (h2 : pnormAll n w bs t (pinv n w t) = true) :
    pnormAll n w bs (pc n w g t) (pinv n w (pc n w g t)) = true := by
  rw [pnormAll_iff hsz hb hok hg] at h1
  rw [pnormAll_iff hsz hb hok ht] at h2
  rw [pnormAll_iff hsz hb hok (hg.pc ht), sg_pc hg ht]
  exact Subgroup.mul_mem _ h1 h2

theorem pnormAll_pidn (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hok : pspanOK n w bs = true) : pnormAll n w bs (pidn n w) (pinv n w (pidn n w)) = true := by
  rw [pnormAll_iff hsz hb hok (PP.id hsz), sg_id hsz]
  exact Subgroup.one_mem _

theorem pnormAll_pfilter (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hok : pspanOK n w bs = true) {fk : Nat → Bool} :
    ∀ (Ls : List (List Nat)),
      (∀ L ∈ Ls, ∀ t ∈ L, PP n w t ∧ pnormAll n w bs t (pinv n w t) = true) →
      ∀ g acc, PP n w g → pnormAll n w bs g (pinv n w g) = true →
      (∀ x ∈ acc, pnormAll n w bs x (pinv n w x) = true) →
      ∀ x ∈ pfilterProducts n w fk Ls g acc, pnormAll n w bs x (pinv n w x) = true
  | [], _, g, acc, _, hg, hacc, x, hx => by
    unfold pfilterProducts at hx
    split at hx
    · rcases List.mem_cons.1 hx with rfl | h
      · exact hg
      · exact hacc x h
    · exact hacc x hx
  | L :: Ls, h, g, acc, hgp, hg, hacc, x, hx => by
    have hLs : ∀ L ∈ Ls, ∀ t ∈ L, PP n w t ∧ pnormAll n w bs t (pinv n w t) = true :=
      fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
    unfold pfilterProducts at hx
    suffices ∀ (l : List Nat), (∀ t ∈ l, PP n w t ∧ pnormAll n w bs t (pinv n w t) = true) →
        ∀ a, (∀ y ∈ a, pnormAll n w bs y (pinv n w y) = true) →
        ∀ y ∈ l.foldl (fun acc t => pfilterProducts n w fk Ls (pc n w g t) acc) a,
          pnormAll n w bs y (pinv n w y) = true from
      this L (h L List.mem_cons_self) acc hacc x hx
    intro l
    induction l with
    | nil => intro _ a ha y hy; exact ha y hy
    | cons t l ih =>
      intro hl a ha y hy
      rw [List.foldl_cons] at hy
      have ht := hl t List.mem_cons_self
      exact ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)) _
        (pnormAll_pfilter hsz hb hok Ls hLs (pc n w g t) a (hgp.pc ht.1)
          (pnormAll_pc hsz hb hok hgp ht.1 hg ht.2) ha) y hy

theorem pcount_true : ∀ (Ls : List (List Nat)) (g : Nat),
    pcountProducts n w (fun _ => true) Ls g = (Ls.map List.length).prod
  | [], g => by unfold pcountProducts; simp
  | T :: Ts, g => by
    unfold pcountProducts
    simp only [pcount_true Ts]
    suffices ∀ (T : List Nat) (c : Nat),
        T.foldl (fun c _ => c + (Ts.map List.length).prod) c = c + T.length * (Ts.map List.length).prod by
      rw [this T 0, List.map_cons, List.prod_cons, Nat.zero_add]
    intro T
    induction T with
    | nil => intro c; simp
    | cons t T ih =>
      intro c
      rw [List.foldl_cons, ih, List.length_cons, Nat.succ_mul]
      omega

theorem pfilter_length (Ls : List (List Nat)) (g : Nat) :
    (pfilterProducts n w (fun _ => true) Ls g []).length = (Ls.map List.length).prod := by
  have h := pfilter_countP n w (fun _ => true) (fun _ => true) Ls g []
  simp only [List.countP_true, List.length_nil, Nat.zero_add, Bool.and_self] at h
  rw [h, pcount_true]

@[expose] noncomputable def pcountPr (n w : Nat) (f : Nat → Bool) (B : List Nat) (C : List (List Nat)) :
    Nat → List (List Nat) → Nat → Nat
  | _, [], g => if f g then 1 else 0
  | k, T :: Ts, g => T.foldl (fun c t => c +
      bif (C.getD k []).contains (pg w (mask w) (pc n w g t) (B.getD k 0)) then
        pcountPr n w f B C (k + 1) Ts (pc n w g t) else 0) 0

theorem pg_pfilter_fix (hn : n < 2 ^ 32) {b : Nat} (hb : b < n) :
    ∀ (Ls : List (List Nat)), (∀ L ∈ Ls, ∀ t ∈ L, pg w (mask w) t b = b) →
      ∀ g acc, (∀ x ∈ acc, pg w (mask w) x b = pg w (mask w) g b) →
      ∀ x ∈ pfilterProducts n w (fun _ => true) Ls g acc, pg w (mask w) x b = pg w (mask w) g b
  | [], _, g, acc, hacc, x, hx => by
    unfold pfilterProducts at hx
    rcases List.mem_cons.1 hx with rfl | h
    · rfl
    · exact hacc x h
  | L :: Ls, h, g, acc, hacc, x, hx => by
    have hLs : ∀ L ∈ Ls, ∀ t ∈ L, pg w (mask w) t b = b :=
      fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
    unfold pfilterProducts at hx
    suffices ∀ (l : List Nat), (∀ t ∈ l, pg w (mask w) t b = b) →
        ∀ a, (∀ y ∈ a, pg w (mask w) y b = pg w (mask w) g b) →
        ∀ y ∈ l.foldl (fun acc t => pfilterProducts n w (fun _ => true) Ls (pc n w g t) acc) a,
          pg w (mask w) y b = pg w (mask w) g b from
      this L (h L List.mem_cons_self) acc hacc x hx
    intro l
    induction l with
    | nil => intro _ a ha y hy; exact ha y hy
    | cons t l ih =>
      intro hl a ha y hy
      rw [List.foldl_cons] at hy
      have e : pg w (mask w) (pc n w g t) b = pg w (mask w) g b := by
        unfold pc
        rw [PF.pg_pcomp hn hb, hl t List.mem_cons_self]
      refine ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)) _ ?_ y hy
      intro z hz
      rw [← e]
      exact pg_pfilter_fix hn hb Ls hLs (pc n w g t) a (fun y hy => (ha y hy).trans e.symm) z hz

theorem pcount_eq_zero {f : Nat → Bool} {Ls : List (List Nat)} {g : Nat}
    (h : ∀ x ∈ pfilterProducts n w (fun _ => true) Ls g [], f x = false) :
    pcountProducts n w f Ls g = 0 := by
  have e := pfilter_countP n w (fun _ => true) f Ls g []
  simp only [Bool.true_and, List.countP_nil, Nat.zero_add] at e
  rw [← e, List.countP_eq_zero]
  intro x hx
  simp [h x hx]

theorem foldl_add_congr {T : List Nat} {F G : Nat → Nat} (h : ∀ t ∈ T, F t = G t) :
    ∀ c, T.foldl (fun c t => c + F t) c = T.foldl (fun c t => c + G t) c := by
  induction T with
  | nil => intro c; rfl
  | cons t T ih =>
    intro c
    rw [List.foldl_cons, List.foldl_cons, h t List.mem_cons_self]
    exact ih (fun s hs => h s (List.mem_cons_of_mem _ hs)) _

theorem pcount_pr (hn : n < 2 ^ 32) {f : Nat → Bool} {B : List Nat} {C : List (List Nat)} :
    ∀ (Ls : List (List Nat)) (k : Nat),
      (∀ i < Ls.length, B.getD (k + i) 0 < n) →
      (∀ j < Ls.length, ∀ t ∈ Ls.getD j [], ∀ i < j,
        pg w (mask w) t (B.getD (k + i) 0) = B.getD (k + i) 0) →
      (∀ x, f x = true → ∀ i < Ls.length,
        (C.getD (k + i) []).contains (pg w (mask w) x (B.getD (k + i) 0)) = true) →
      ∀ g, pcountProducts n w f Ls g = pcountPr n w f B C k Ls g
  | [], k, _, _, _, g => by unfold pcountProducts pcountPr; rfl
  | T :: Ts, k, hB, hfix, hf, g => by
    unfold pcountProducts pcountPr
    have hB' : ∀ i < Ts.length, B.getD (k + 1 + i) 0 < n := fun i hi => by
      have := hB (i + 1) (by simp; omega)
      rwa [show k + (i + 1) = k + 1 + i by omega] at this
    have hfix' : ∀ j < Ts.length, ∀ t ∈ Ts.getD j [], ∀ i < j,
        pg w (mask w) t (B.getD (k + 1 + i) 0) = B.getD (k + 1 + i) 0 := fun j hj t ht i hi => by
      have := hfix (j + 1) (by simp; omega) t (by simpa using ht) (i + 1) (by omega)
      rwa [show k + (i + 1) = k + 1 + i by omega] at this
    have hf' : ∀ x, f x = true → ∀ i < Ts.length,
        (C.getD (k + 1 + i) []).contains (pg w (mask w) x (B.getD (k + 1 + i) 0)) = true :=
      fun x hx i hi => by
        have := hf x hx (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this
    refine foldl_add_congr (fun t _ => ?_) 0
    cases hq : (C.getD k []).contains (pg w (mask w) (pc n w g t) (B.getD k 0))
    · rw [Bool.cond_false]
      apply pcount_eq_zero
      intro x hx
      cases hfx : f x
      · rfl
      · have h0 := hf x hfx 0 (by simp)
        simp only [Nat.add_zero] at h0
        have hb0 : B.getD k 0 < n := by simpa using hB 0 (by simp)
        have hfx0 : ∀ L ∈ Ts, ∀ t ∈ L, pg w (mask w) t (B.getD k 0) = B.getD k 0 := by
          intro L hL t ht
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
          have := hfix (j + 1) (by simp; omega) t
            (by show t ∈ Ts.getD j []; rw [List.getD_eq_getElem _ _ hj]; exact ht) 0 (by omega)
          simpa using this
        rw [pg_pfilter_fix hn hb0 Ts hfx0 _ [] (fun _ h => absurd h List.not_mem_nil) x hx, hq] at h0
        exact absurd h0 (by decide)
    · rw [Bool.cond_true]
      exact pcount_pr hn Ts (k + 1) hB' hfix' hf' _

theorem pfixes_contains {bl : List (List Nat)} {x b : Nat} {T : List Nat} (hT : T ∈ bl) (hb : b ∈ T)
    (h : pfixesBlocks w bl x = true) : T.contains (pg w (mask w) x b) = true := by
  unfold pfixesBlocks at h
  exact List.all_eq_true.1 (List.all_eq_true.1 h T hT) b hb

end CFSG.KC.KGC31P

end
