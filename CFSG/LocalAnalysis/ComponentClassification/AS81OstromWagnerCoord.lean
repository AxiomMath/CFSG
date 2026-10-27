module

public import CFSG.LocalAnalysis.ComponentClassification.AS81OstromWagnerPlane

public section

namespace CFSG.ComponentClassification.AS81.OstromWagner

variable {P : Type} {lines : Set (Set P)}

structure AffFrame (lines : Set (Set P)) (o : P) (a b c : Set P) : Prop where
  ha : a ∈ lines
  hb : b ∈ lines
  hc : c ∈ lines
  hab : ¬Par a b
  hac : ¬Par a c
  hbc : ¬Par b c
  oa : o ∈ a
  ob : o ∈ b
  oc : o ∈ c

structure Labelling (a : Set P) (o : P) (lab : P → Fin 4) : Prop where
  inj : ∀ x ∈ a, ∀ y ∈ a, lab x = lab y → x = y
  surj : ∀ k, ∃ x ∈ a, lab x = k
  zero : lab o = 0

namespace AffFrame

variable {o : P} {a b c : Set P} (hF : AffFrame lines o a b c)
include hF

theorem hba : ¬Par b a := fun h => hF.hab h.symm

theorem hca : ¬Par c a := fun h => hF.hac h.symm

theorem hcb : ¬Par c b := fun h => hF.hbc h.symm

end AffFrame

theorem exists_affFrame (hA : IsAffinePlane P lines) (h2 : ∃ x y : P, x ≠ y) :
    ∃ o a b c, AffFrame lines o a b c := by
  obtain ⟨o, q, r, hcol⟩ := hA.nondegenerate
  have hoq : o ≠ q := by
    rintro rfl
    by_cases hor : o = r
    · subst hor
      obtain ⟨x, y, hxy⟩ := h2
      by_cases hxo : x = o
      · subst hxo
        exact hcol ⟨_, (hA.ln_spec hxy).1, (hA.ln_spec hxy).2.1, (hA.ln_spec hxy).2.1,
          (hA.ln_spec hxy).2.1⟩
      · exact hcol ⟨_, (hA.ln_spec hxo).1, (hA.ln_spec hxo).2.2, (hA.ln_spec hxo).2.2,
          (hA.ln_spec hxo).2.2⟩
    · exact hcol ⟨_, (hA.ln_spec hor).1, (hA.ln_spec hor).2.1, (hA.ln_spec hor).2.1,
        (hA.ln_spec hor).2.2⟩
  obtain ⟨ha, hoa, hqa⟩ := hA.ln_spec hoq
  have hra : r ∉ ln lines o q := fun h => hcol ⟨_, ha, hoa, hqa, h⟩
  have hor : o ≠ r := fun h => hra (h ▸ hoa)
  have hqr : q ≠ r := fun h => hra (h ▸ hqa)
  obtain ⟨hb, hob, hrb⟩ := hA.ln_spec hor
  obtain ⟨hd, hqd, hrd⟩ := hA.ln_spec hqr
  set a := ln lines o q
  set b := ln lines o r
  set d := ln lines q r
  have hab : a ≠ b := fun h => hra (h ▸ hrb)
  have had : ¬Par a d := not_par_of_mem (fun h => hra (h ▸ hrd)) hqa hqd
  have hbd : ¬Par b d := by
    refine not_par_of_mem (fun h => hra ?_) hrb hrd
    rw [hA.eq_of_mem ha hb hoq hoa hqa hob (h ▸ hqd)]
    exact hrb
  refine ⟨o, a, b, par lines d o, ⟨ha, hb, hA.par_mem hd o, not_par_of_mem hab hoa hob,
    fun h => had ?_, fun h => hbd ?_, hoa, hob, hA.mem_par hd o⟩⟩
  · exact hA.par_trans ha (hA.par_mem hd o) hd h (hA.par_par hd o).symm
  · exact hA.par_trans hb (hA.par_mem hd o) hd h (hA.par_par hd o).symm

theorem _root_.CFSG.ComponentClassification.AS81.IsAffinePlane.exists_par_meet
    (hA : IsAffinePlane P lines) {d d' : Set P} (hd : d ∈ lines) (hd' : d' ∈ lines)
    (hdd' : ¬Par d d') (x y : P) : ∃ p, par lines d p = par lines d x ∧
      par lines d' p = par lines d' y := by
  have hn : ¬Par (par lines d x) (par lines d' y) := fun h =>
    hdd' (hA.par_trans hd (hA.par_mem hd x) hd' (hA.par_par hd x)
      (hA.par_trans (hA.par_mem hd x) (hA.par_mem hd' y) hd' h (hA.par_par hd' y).symm))
  obtain ⟨p, hpx, hpy⟩ := exists_mem_of_not_par hn
  exact ⟨p, ((hA.par_eq_par_iff hd).2 hpx).symm, ((hA.par_eq_par_iff hd').2 hpy).symm⟩

section Axis

variable [Nonempty P] {o : P} {a b c : Set P}

theorem _root_.CFSG.ComponentClassification.AS81.IsAffinePlane.eq_of_par_eq_of_mem
    (hA : IsAffinePlane P lines) {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines)
    (hdt : ¬Par d t) {x y : P} (hx : x ∈ t) (hy : y ∈ t) (h : par lines d x = par lines d y) :
    x = y := by
  rw [← hA.proj_of_mem hd ht hdt hx, ← hA.proj_of_mem hd ht hdt hy]
  exact (hA.proj_eq_proj_iff hd ht hdt).2 h

theorem _root_.CFSG.ComponentClassification.AS81.IsAffinePlane.mem_of_proj_eq
    (hA : IsAffinePlane P lines) {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines)
    (hdt : ¬Par d t) (hod : o ∈ d) {p : P} (h : proj lines d t p = o) : p ∈ d := by
  have h1 := hA.proj_mem_par hd ht hdt p
  rw [h] at h1
  have h2 : par lines d p = d := ((hA.par_eq_par_iff hd).2 h1).trans (hA.par_of_mem hd hod)
  exact h2 ▸ hA.mem_par hd p

theorem natCard_axis (hA : IsAffinePlane P lines) (hF : AffFrame lines o a b c)
    (h16 : Nat.card P = 16) : Nat.card a = 4 := by
  set f : P → a × a := fun p =>
    (⟨proj lines b a p, hA.proj_mem hF.hb hF.ha hF.hba p⟩,
      ⟨proj lines c a p, hA.proj_mem hF.hc hF.ha hF.hca p⟩) with hf
  have hinj : Function.Injective f := by
    intro p q h
    simp only [hf, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact hA.eq_of_par_eq_of_par_eq hF.hb hF.hc hF.hbc
      ((hA.proj_eq_proj_iff hF.hb hF.ha hF.hba).1 h.1)
      ((hA.proj_eq_proj_iff hF.hc hF.ha hF.hca).1 h.2)
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨p, hpx, hpy⟩ := hA.exists_par_meet hF.hb hF.hc hF.hbc x y
    refine ⟨p, ?_⟩
    simp only [hf, Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [← hA.proj_of_mem hF.hb hF.ha hF.hba hx]
      exact (hA.proj_eq_proj_iff hF.hb hF.ha hF.hba).2 hpx
    · rw [← hA.proj_of_mem hF.hc hF.ha hF.hca hy]
      exact (hA.proj_eq_proj_iff hF.hc hF.ha hF.hca).2 hpy
  have h := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [h16, Nat.card_prod] at h
  have h4 : Nat.card a ^ 2 = 4 ^ 2 := by
    rw [sq, ← h]
    norm_num
  exact Nat.pow_left_injective (by norm_num) h4

variable [Finite P] in
theorem exists_labelling (hA : IsAffinePlane P lines) (hF : AffFrame lines o a b c)
    (h16 : Nat.card P = 16) : ∃ lab : P → Fin 4, Labelling a o lab := by
  classical
  set e := Finite.equivFinOfCardEq (natCard_axis hA hF h16)
  set σ := e.trans (Equiv.swap (e ⟨o, hF.oa⟩) 0)
  refine ⟨fun x => if h : x ∈ a then σ ⟨x, h⟩ else 0, ⟨?_, ?_, ?_⟩⟩
  · intro x hx y hy h
    simp only [hx, hy, ↓reduceDIte] at h
    exact congrArg Subtype.val (σ.injective h)
  · intro k
    obtain ⟨⟨x, hx⟩, hxk⟩ := σ.surjective k
    exact ⟨x, hx, by simp only [hx, ↓reduceDIte, hxk]⟩
  · simp only [hF.oa, ↓reduceDIte, σ, Equiv.trans_apply, Equiv.swap_apply_left]

end Axis

section Coords

variable [Nonempty P] (lines) (a b c : Set P) (lab : P → Fin 4)

@[expose] noncomputable def cZ (d : Set P) (p : P) : Fin 4 := lab (proj lines d a p)

@[expose] noncomputable def cX (p : P) : Fin 4 := lab (proj lines c a (proj lines a b p))

variable {lines a b c lab} {o : P} (hA : IsAffinePlane P lines) (hF : AffFrame lines o a b c)
  (hL : Labelling a o lab)
include hA hF hL

theorem cZ_eq_cZ_iff {d : Set P} (hd : d ∈ lines) (hda : ¬Par d a) {p q : P} :
    cZ lines a lab d p = cZ lines a lab d q ↔ par lines d p = par lines d q := by
  rw [cZ, cZ, ← hA.proj_eq_proj_iff hd hF.ha hda]
  exact ⟨hL.inj _ (hA.proj_mem hd hF.ha hda p) _ (hA.proj_mem hd hF.ha hda q),
    fun h => by rw [h]⟩

theorem cX_eq_cX_iff {p q : P} :
    cX lines a b c lab p = cX lines a b c lab q ↔ par lines a p = par lines a q := by
  rw [← hA.proj_eq_proj_iff hF.ha hF.hb hF.hab]
  constructor
  · intro h
    have h1 := hL.inj _ (hA.proj_mem hF.hc hF.ha hF.hca _) _ (hA.proj_mem hF.hc hF.ha hF.hca _) h
    rw [hA.proj_eq_proj_iff hF.hc hF.ha hF.hca] at h1
    exact hA.eq_of_par_eq_of_mem hF.hc hF.hb hF.hcb (hA.proj_mem hF.ha hF.hb hF.hab p)
      (hA.proj_mem hF.ha hF.hb hF.hab q) h1
  · intro h
    rw [cX, cX, h]

theorem eq_of_cX_eq_of_cZ_eq {d : Set P} (hd : d ∈ lines) (hda : ¬Par d a) {p q : P}
    (hX : cX lines a b c lab p = cX lines a b c lab q)
    (hZ : cZ lines a lab d p = cZ lines a lab d q) : p = q :=
  hA.eq_of_par_eq_of_par_eq hF.ha hd (fun h => hda h.symm) ((cX_eq_cX_iff hA hF hL).1 hX)
    ((cZ_eq_cZ_iff hA hF hL hd hda).1 hZ)

theorem eq_of_cZ_eq_of_cZ_eq {d d' : Set P} (hd : d ∈ lines) (hda : ¬Par d a) (hd' : d' ∈ lines)
    (hda' : ¬Par d' a) (hdd' : ¬Par d d') {p q : P}
    (hZ : cZ lines a lab d p = cZ lines a lab d q)
    (hZ' : cZ lines a lab d' p = cZ lines a lab d' q) : p = q :=
  hA.eq_of_par_eq_of_par_eq hd hd' hdd' ((cZ_eq_cZ_iff hA hF hL hd hda).1 hZ)
    ((cZ_eq_cZ_iff hA hF hL hd' hda').1 hZ')

omit hL in
theorem cZ_of_mem_a {d : Set P} (hd : d ∈ lines) (hda : ¬Par d a) {p : P} (hp : p ∈ a) :
    cZ lines a lab d p = lab p := by
  rw [cZ, hA.proj_of_mem hd hF.ha hda hp]

omit hL in
theorem cX_of_mem_b {p : P} (hp : p ∈ b) : cX lines a b c lab p = cZ lines a lab c p := by
  rw [cX, cZ, hA.proj_of_mem hF.ha hF.hb hF.hab hp]

theorem cZ_eq_zero_iff {d : Set P} (hd : d ∈ lines) (hda : ¬Par d a) (hod : o ∈ d) {p : P} :
    cZ lines a lab d p = 0 ↔ p ∈ d := by
  constructor
  · intro h
    refine hA.mem_of_proj_eq hd hF.ha hda hod (hL.inj _ (hA.proj_mem hd hF.ha hda p) _ hF.oa ?_)
    rw [hL.zero]
    exact h
  · intro hp
    have h1 : par lines d p = d := hA.par_of_mem hd hp
    have h2 := hA.proj_mem_par hd hF.ha hda p
    rw [h1] at h2
    rw [cZ, hA.eq_of_not_par hd hF.ha hda h2 (hA.proj_mem hd hF.ha hda p) hod hF.oa, hL.zero]

theorem mem_of_cX_eq_zero {p : P} (h : cX lines a b c lab p = 0) : p ∈ a := by
  have h1 : proj lines c a (proj lines a b p) = o := by
    refine hL.inj _ (hA.proj_mem hF.hc hF.ha hF.hca _) _ hF.oa ?_
    rw [hL.zero]
    exact h
  have h2 := hA.mem_of_proj_eq hF.hc hF.ha hF.hca hF.oc h1
  have h3 : proj lines a b p = o := hA.eq_of_not_par hF.hb hF.hc hF.hbc
    (hA.proj_mem hF.ha hF.hb hF.hab p) h2 hF.ob hF.oc
  exact hA.mem_of_proj_eq hF.ha hF.hb hF.hab hF.oa h3

theorem cX_eq_zero_iff {p : P} : cX lines a b c lab p = 0 ↔ p ∈ a := by
  refine ⟨mem_of_cX_eq_zero hA hF hL, fun hp => ?_⟩
  have h1 := hA.proj_mem_par hF.ha hF.hb hF.hab p
  rw [hA.par_of_mem hF.ha hp] at h1
  have h2 : proj lines a b p = o :=
    hA.eq_of_not_par hF.hb hF.ha hF.hba (hA.proj_mem hF.ha hF.hb hF.hab p) h1 hF.ob hF.oa
  rw [cX, h2, hA.proj_of_mem hF.hc hF.ha hF.hca hF.oa, hL.zero]

end Coords

end CFSG.ComponentClassification.AS81.OstromWagner
