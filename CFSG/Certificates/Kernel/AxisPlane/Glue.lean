module

public import CFSG.Certificates.Kernel.AxisPlane.Steps
public import CFSG.Certificates.Kernel.AxisPlane.Pop
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.AxisPlane.Chk
public import Mathlib.Data.Set.Card

public section

set_option maxHeartbeats 400000

namespace CFSG.KC.AxisPlane

open CFSG.Monster.AxisCount.Native.Cover

structure PlanesOK (rows : Array (Array Nat)) (opss rls : List (List Nat))
    (Ls Qs : List Nat) (Rss : List (List Nat)) (lams sizes : List Nat) : Prop where
  chk : PlanesChk opss rls Ls Qs Rss lams sizes
  size_eq : rows.size = opss.length
  rows_eq : ∀ g < rows.size, rows[g]! = (rls.getD g []).toArray

section Fields

variable {rows : Array (Array Nat)} {opss rls : List (List Nat)} {Ls Qs : List Nat}
  {Rss : List (List Nat)} {lams sizes : List Nat} (H : PlanesOK rows opss rls Ls Qs Rss lams sizes)
include H

theorem PlanesOK.len_Rss : Rss.length = rows.size := H.chk.len_Rss.trans H.size_eq.symm
theorem PlanesOK.ops_ok : ∀ g < rows.size, opsOK (opss.getD g []) (rls.getD g []) = true :=
  fun g hg => H.chk.ops_ok g (H.size_eq ▸ hg)
theorem PlanesOK.inv : ∀ g < rows.size, ∀ b < Ls.length, invK (opss.getD g []) (Ls.getD b 0) = true :=
  fun g hg => H.chk.inv g (H.size_eq ▸ hg)
theorem PlanesOK.img_len : ∀ g < rows.size, (Rss.getD g []).length = Qs.length :=
  fun g hg => H.chk.img_len g (H.size_eq ▸ hg)
theorem PlanesOK.img : ∀ g < rows.size, ∀ j < Qs.length,
    imgEqK (opss.getD g []) (Qs.getD j 0) ((Rss.getD g []).getD j 0) = true :=
  fun g hg => H.chk.img g (H.size_eq ▸ hg)
theorem PlanesOK.gen : genK Qs Rss = true := H.chk.gen
theorem PlanesOK.cov : covK Ls Qs = true := H.chk.cov
theorem PlanesOK.seeds : seedsK Ls Qs lams = true := H.chk.seeds
theorem PlanesOK.d0 : d0K Qs lams = true := H.chk.d0
theorem PlanesOK.qs_pos : 0 < Qs.length := H.chk.qs_pos
theorem PlanesOK.lams_lt : lams.length < 2 ^ Ls.length := H.chk.lams_lt
theorem PlanesOK.cnt : ∀ r < lams.length, cntK Ls (r + 1) (sizes.getD r 0) = true := H.chk.cnt

end Fields

theorem codeAt_congr {x y : Nat} : ∀ (Ps : List Nat), (∀ P ∈ Ps, dat P x = dat P y) →
    codeAt Ps x = codeAt Ps y
  | [], _ => rfl
  | P :: Ps, h => by
    rw [codeAt_cons, codeAt_cons, h P (List.mem_cons_self ..),
      codeAt_congr Ps (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))]

theorem invK_spec {ops : List Nat} {P : Nat} (h : invK ops P = true) {q : Nat}
    (hq : q < 16777216) : dat (applyK ops P) q = dat P q := by
  rw [invK, Nat.beq_eq] at h
  have := congrArg (fun z => dat z q) h
  simp only [dat_land, dat_xor, dat_allK, dat_zero, decide_eq_true hq, Bool.and_true] at this
  revert this
  cases dat (applyK ops P) q <;> cases dat P q <;> simp

theorem imgEqK_spec {ops : List Nat} {P R : Nat} (h : imgEqK ops P R = true) {q : Nat}
    (hq : q < 16777216) : dat (applyK ops P) q = dat R q := by
  rw [imgEqK, Nat.beq_eq] at h
  have := congrArg (fun z => dat z q) h
  simp only [dat_land, dat_xor, dat_allK, dat_zero, decide_eq_true hq, Bool.and_true] at this
  revert this
  cases dat (applyK ops P) q <;> cases dat R q <;> simp

theorem mem_getD {α : Type} {l : List α} {a : α} (d : α) (h : a ∈ l) : ∃ i < l.length, l.getD i d = a := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi, e]⟩

theorem seedsGo_spec (Ls Qs : List Nat) : ∀ (lams : List Nat) (r₀ : Nat), seedsGo Ls Qs lams r₀ = true →
    ∀ r < lams.length, lams.getD r 0 < 16777216 ∧ codeAt Ls (lams.getD r 0) = r₀ + r + 1 ∧
      codeAt Qs (lams.getD r 0) = 1
  | [], _, _, r, hr => absurd hr (by simp)
  | x :: lams, r₀, h, r, hr => by
    obtain ⟨h1, h2⟩ := CFSG.KC.Benes.andB_true h
    obtain ⟨h2, h3⟩ := CFSG.KC.Benes.andB_true h2
    obtain ⟨h3, h4⟩ := CFSG.KC.Benes.andB_true h3
    rw [Nat.blt_eq] at h1
    rw [Nat.beq_eq] at h2 h3
    rcases r with _ | r
    · exact ⟨h1, by simpa using h2, h3⟩
    · have := seedsGo_spec Ls Qs lams (r₀ + 1) h4 r (by simpa using hr)
      simpa [show r₀ + 1 + r + 1 = r₀ + (r + 1) + 1 by omega] using this

theorem dat_seedPl : ∀ (lams : List Nat) (q : Nat), dat (seedPl lams) q = true → q ∈ lams
  | [], q, h => by simp [seedPl, dat_zero] at h
  | x :: lams, q, h => by
    change dat (Nat.lor (Nat.shiftLeft 1 (Nat.add 64 x)) (seedPl lams)) q = true at h
    rw [dat_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [dat, CFSG.KC.Benes.nshl, CFSG.KC.Benes.nadd, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      simp only [decide_eq_true_eq] at h
      exact List.mem_cons.2 (Or.inl (by omega))
    · exact List.mem_cons_of_mem _ (dat_seedPl lams q h)

section Facts

variable {rows : Array (Array Nat)} {opss rls : List (List Nat)} {Ls Qs : List Nat}
  {Rss : List (List Nat)} {lams sizes : List Nat}

theorem PlanesOK.opsValid (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {g : Nat}
    (hg : g < rows.size) : CFSG.KC.AxisPlane.opsValid (opss.getD g []) = true :=
  (CFSG.KC.Benes.andB_true (H.ops_ok g hg)).1

theorem PlanesOK.act (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {g : Nat}
    (hg : g < rows.size) {x : Nat} (hx : x < 16777216) : cvImg rows g x = vecOps (opss.getD g []) x := by
  rw [cvImg, H.rows_eq g hg, actRows_eq_vecOps (H.ops_ok g hg) hx]

theorem PlanesOK.inv_code (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {g : Nat}
    (hg : g < rows.size) {x : Nat} (hx : x < 16777216) :
    codeAt Ls (vecOps (opss.getD g []) x) = codeAt Ls x := by
  apply codeAt_congr
  intro P hP
  obtain ⟨b, hb, rfl⟩ := mem_getD 0 hP
  have hv := vecOps_lt (H.opsValid hg) hx
  have h1 := invK_spec (H.inv g hg b hb) hv
  rw [dat_applyK (H.opsValid hg) _ hv, piOps_vecOps (H.opsValid hg)] at h1
  exact h1.symm

theorem codeAt_imgs {ops : List Nat} (hv : opsValid ops = true) {y : Nat} (hy : y < 16777216) :
    ∀ (Qs Rs : List Nat), Qs.length = Rs.length →
      (∀ j < Qs.length, imgEqK ops (Qs.getD j 0) (Rs.getD j 0) = true) →
      codeAt Rs y = codeAt Qs (piOps ops y)
  | [], [], _, _ => rfl
  | Q :: Qs, R :: Rs, hl, h => by
    rw [codeAt_cons, codeAt_cons, codeAt_imgs hv hy Qs Rs (by simpa using hl)
      (fun j hj => h (j + 1) (by simpa using hj))]
    have := imgEqK_spec (h 0 (by simp)) hy
    rw [dat_applyK hv _ hy] at this
    simp only [List.getD_cons_zero] at this
    rw [this]
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

theorem PlanesOK.pred (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {y : Nat}
    (hy : y < 16777216) (h2 : 2 ≤ codeAt Qs y) :
    ∃ g < rows.size, codeAt Qs (piOps (opss.getD g []) y) + 1 = codeAt Qs y := by
  have hg := H.gen
  obtain ⟨Q0, Qt, hQ⟩ : ∃ Q0 Qt, Qs = Q0 :: Qt := by
    cases Qs with
    | nil => exact absurd H.qs_pos (by simp)
    | cons a t => exact ⟨a, t, rfl⟩
  have hany : dat (anyK Qt) y = true := by
    rw [dat_anyK]
    by_contra hc
    push Not at hc
    have h0 : codeAt Qt y = 0 := (codeAt_eq_zero Qt y).2 (fun P hP => by simpa using hc P hP)
    rw [hQ, codeAt_cons, h0] at h2
    have := toNat_le_one (dat Q0 y)
    omega
  have e : genK Qs Rss = subK (anyK Qt) (predK Qs Rss) := by rw [hQ]; rfl
  rw [e] at hg
  have hp := subK_spec hg hy hany
  have key : ∀ (L : List (List Nat)), dat (predK Qs L) y = true →
      ∃ Rs ∈ L, dat (incK Qs Rs allK) y = true := by
    intro L
    induction L with
    | nil => intro h; simp [predK, dat_zero] at h
    | cons Rs L ih =>
      intro h
      change dat (Nat.lor (incK Qs Rs allK) (predK Qs L)) y = true at h
      rw [dat_lor, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨Rs, List.mem_cons_self .., h⟩
      · obtain ⟨Rs', h1, h2⟩ := ih h
        exact ⟨Rs', List.mem_cons_of_mem _ h1, h2⟩
  obtain ⟨Rs, hRs, hinc⟩ := key Rss hp
  obtain ⟨g, hgl, rfl⟩ := mem_getD [] hRs
  have hg' : g < rows.size := by rw [← H.len_Rss]; exact hgl
  rw [dat_incK Qs _ (H.img_len g hg').symm _ y hy, dat_allK, decide_eq_true hy] at hinc
  simp only [decide_eq_true_eq] at hinc
  refine ⟨g, hg', ?_⟩
  rw [← codeAt_imgs (H.opsValid hg') hy Qs _ (H.img_len g hg').symm (H.img g hg')]
  simpa using hinc.symm

theorem PlanesOK.seed (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {r : Nat}
    (hr : r < lams.length) :
    lams.getD r 0 < 16777216 ∧ codeAt Ls (lams.getD r 0) = r + 1 ∧ codeAt Qs (lams.getD r 0) = 1 := by
  have := seedsGo_spec Ls Qs lams 0 H.seeds r hr
  simpa using this

theorem PlanesOK.level_one (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {y : Nat}
    (hy : y < 16777216) (h1 : codeAt Qs y = 1) : ∃ r < lams.length, lams.getD r 0 = y := by
  have h := subK_spec H.d0 hy (by
    rw [dat_codeK, decide_eq_true hy, h1, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by
      have := H.qs_pos; omega))]
    rfl)
  exact mem_getD 0 (dat_seedPl lams y h)

theorem orbitOf_step {m : Nat} {f : Nat → Nat → Nat} {s a : Nat} (ha : a ∈ orbitOf m f s) {g : Nat}
    (hg : g < m) : f g a ∈ orbitOf m f s :=
  Relation.ReflTransGen.tail ha ⟨g, hg, rfl⟩

theorem PlanesOK.reach (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) :
    ∀ c, ∀ y < 16777216, codeAt Qs y = c → c ≠ 0 →
      ∃ r < lams.length, y ∈ natOrbit rows (lams.getD r 0) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro y hy hc hc0
    by_cases h1 : c = 1
    · obtain ⟨r, hr, e⟩ := H.level_one hy (hc.trans h1)
      exact ⟨r, hr, e ▸ Relation.ReflTransGen.refl⟩
    · obtain ⟨g, hg, hp⟩ := H.pred hy (by omega)
      have hx := piOps_lt (H.opsValid hg) hy
      obtain ⟨r, hr, hmem⟩ := ih (c - 1) (by omega) _ hx (by omega) (by omega)
      refine ⟨r, hr, ?_⟩
      have e : cvImg rows g (piOps (opss.getD g []) y) = y := by
        rw [H.act hg hx, vecOps_piOps (H.opsValid hg)]
      rw [← e]
      exact orbitOf_step hmem hg

theorem PlanesOK.orbit_code (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {s : Nat}
    (hs : s < 16777216) {v : Nat} (hv : v ∈ natOrbit rows s) :
    v < 16777216 ∧ codeAt Ls v = codeAt Ls s := by
  induction hv with
  | refl => exact ⟨hs, rfl⟩
  | tail _ hab ih =>
    obtain ⟨g, hg, rfl⟩ := hab
    rw [H.act hg ih.1]
    exact ⟨vecOps_lt (H.opsValid hg) ih.1, (H.inv_code hg ih.1).trans ih.2⟩

theorem PlanesOK.orbit_eq (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {r : Nat}
    (hr : r < lams.length) :
    natOrbit rows (lams.getD r 0) = {x | x < 16777216 ∧ codeAt Ls x = r + 1} := by
  obtain ⟨hs, hsl, -⟩ := H.seed hr
  ext x
  constructor
  · intro hx
    obtain ⟨h1, h2⟩ := H.orbit_code hs hx
    exact ⟨h1, h2.trans hsl⟩
  · rintro ⟨hx, hc⟩
    have hq : codeAt Qs x ≠ 0 := by
      have h := subK_spec H.cov hx (by
        rw [dat_anyK]
        by_contra hc'
        push Not at hc'
        have := (codeAt_eq_zero Ls x).2 (fun P hP => by simpa using hc' P hP)
        omega)
      rw [dat_anyK] at h
      obtain ⟨P, hP, hd⟩ := h
      intro h0
      have := (codeAt_eq_zero Qs x).1 h0 P hP
      rw [this] at hd
      exact absurd hd (by decide)
    obtain ⟨r', hr', hm⟩ := H.reach _ x hx rfl hq
    obtain ⟨hs', hsl', -⟩ := H.seed hr'
    have := (H.orbit_code hs' hm).2
    rw [hc, hsl'] at this
    have : r = r' := by omega
    subst this
    exact hm

theorem orbits_of_planesOK (H : PlanesOK rows opss rls Ls Qs Rss lams sizes) {r : Nat}
    (hr : r < lams.length) :
    natOrbit rows (lams.getD r 0) ⊆ Set.Iio 16777216 ∧
    (natOrbit rows (lams.getD r 0)).ncard = sizes.getD r 0 ∧
    ∀ r' < lams.length, r ≠ r' →
      Disjoint (natOrbit rows (lams.getD r 0)) (natOrbit rows (lams.getD r' 0)) := by
  refine ⟨fun x hx => by rw [H.orbit_eq hr] at hx; exact hx.1, ?_, fun r' hr' hne => ?_⟩
  · have hcnt := H.cnt r hr
    rw [cntK, Nat.beq_eq, popK_eq] at hcnt
    rw [H.orbit_eq hr, ← hcnt]
    have e : {x | x < 16777216 ∧ codeAt Ls x = r + 1} =
        ↑((Finset.range 16777216).filter fun q =>
          (Nat.shiftRight (codeK Ls (r + 1)) 64).testBit q = true) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
      rw [← dat_eq_shr, dat_codeK, Nat.mod_eq_of_lt (by have := H.lams_lt; omega)]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simp [h1, h2]⟩
      · rintro ⟨h1, h2⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        exact ⟨h1, h2.2⟩
    rw [e, Set.ncard_coe_finset]
  · rw [H.orbit_eq hr, H.orbit_eq hr', Set.disjoint_left]
    rintro x ⟨-, h1⟩ ⟨-, h2⟩
    omega

end Facts

end CFSG.KC.AxisPlane

end
