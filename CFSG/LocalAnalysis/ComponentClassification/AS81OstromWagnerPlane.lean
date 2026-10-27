module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Inputs

public section

namespace CFSG.ComponentClassification.AS81

namespace OstromWagner

variable {P : Type} {lines : Set (Set P)}

@[expose] def Par (ℓ m : Set P) : Prop := ℓ = m ∨ Disjoint ℓ m

theorem Par.refl (ℓ : Set P) : Par ℓ ℓ := Or.inl rfl

theorem Par.symm {ℓ m : Set P} (h : Par ℓ m) : Par m ℓ := h.imp Eq.symm fun h => h.symm

theorem Par.eq_of_mem {ℓ m : Set P} (h : Par ℓ m) {p : P} (hℓ : p ∈ ℓ) (hm : p ∈ m) : ℓ = m :=
  h.resolve_right fun hd => Set.disjoint_left.1 hd hℓ hm

theorem not_par_of_mem {ℓ m : Set P} (hne : ℓ ≠ m) {p : P} (hℓ : p ∈ ℓ) (hm : p ∈ m) :
    ¬Par ℓ m := fun h => hne (h.eq_of_mem hℓ hm)

theorem exists_mem_of_not_par {ℓ m : Set P} (h : ¬Par ℓ m) : ∃ x, x ∈ ℓ ∧ x ∈ m :=
  Set.not_disjoint_iff.1 fun hd => h (Or.inr hd)

open Classical in
@[expose] noncomputable def par (lines : Set (Set P)) (d : Set P) (p : P) : Set P :=
  if h : ∃ m, m ∈ lines ∧ p ∈ m ∧ Par d m then h.choose else ∅

@[expose] noncomputable def proj [Nonempty P] (lines : Set (Set P)) (d t : Set P) (p : P) : P :=
  Classical.epsilon fun x => x ∈ t ∧ x ∈ par lines d p

open Classical in
@[expose] noncomputable def ln (lines : Set (Set P)) (p q : P) : Set P :=
  if h : ∃ ℓ, ℓ ∈ lines ∧ p ∈ ℓ ∧ q ∈ ℓ then h.choose else ∅

end OstromWagner

namespace IsAffinePlane

open OstromWagner

variable {P : Type} {lines : Set (Set P)} (hA : IsAffinePlane P lines)
include hA

theorem eq_of_mem {ℓ m : Set P} (hℓ : ℓ ∈ lines) (hm : m ∈ lines) {p q : P} (hpq : p ≠ q)
    (hpℓ : p ∈ ℓ) (hqℓ : q ∈ ℓ) (hpm : p ∈ m) (hqm : q ∈ m) : ℓ = m :=
  (hA.line_unique p q hpq).unique ⟨hℓ, hpℓ, hqℓ⟩ ⟨hm, hpm, hqm⟩

theorem existsUnique_par {d : Set P} (hd : d ∈ lines) (p : P) :
    ∃! m, m ∈ lines ∧ p ∈ m ∧ Par d m := by
  by_cases hp : p ∈ d
  · refine ⟨d, ⟨hd, hp, Par.refl d⟩, ?_⟩
    rintro m ⟨-, hpm, hpar⟩
    exact (hpar.eq_of_mem hp hpm).symm
  · obtain ⟨m, ⟨hm, hpm, hdm⟩, hu⟩ := hA.parallel d hd p hp
    refine ⟨m, ⟨hm, hpm, Or.inr hdm⟩, ?_⟩
    rintro m' ⟨hm', hpm', hpar⟩
    rcases hpar with h | h
    · exact absurd (h ▸ hpm') hp
    · exact hu m' ⟨hm', hpm', h⟩

theorem par_spec {d : Set P} (hd : d ∈ lines) (p : P) :
    par lines d p ∈ lines ∧ p ∈ par lines d p ∧ Par d (par lines d p) := by
  have h : ∃ m, m ∈ lines ∧ p ∈ m ∧ Par d m := (hA.existsUnique_par hd p).exists
  rw [par, dite_eq_left h]
  exact h.choose_spec

theorem par_mem {d : Set P} (hd : d ∈ lines) (p : P) : par lines d p ∈ lines :=
  (hA.par_spec hd p).1

theorem mem_par {d : Set P} (hd : d ∈ lines) (p : P) : p ∈ par lines d p :=
  (hA.par_spec hd p).2.1

theorem par_par {d : Set P} (hd : d ∈ lines) (p : P) : Par d (par lines d p) :=
  (hA.par_spec hd p).2.2

theorem eq_par {d m : Set P} (hd : d ∈ lines) (hm : m ∈ lines) {p : P} (hp : p ∈ m)
    (h : Par d m) : m = par lines d p :=
  (hA.existsUnique_par hd p).unique ⟨hm, hp, h⟩ (hA.par_spec hd p)

theorem par_of_mem {d : Set P} (hd : d ∈ lines) {p : P} (hp : p ∈ d) : par lines d p = d :=
  (hA.eq_par hd hd hp (Par.refl d)).symm

theorem par_trans {ℓ m k : Set P} (hℓ : ℓ ∈ lines) (hm : m ∈ lines) (hk : k ∈ lines)
    (hℓm : Par ℓ m) (hmk : Par m k) : Par ℓ k := by
  by_cases hd : Disjoint ℓ k
  · exact Or.inr hd
  obtain ⟨p, hpℓ, hpk⟩ := Set.not_disjoint_iff.1 hd
  exact Or.inl ((hA.eq_par hm hℓ hpℓ hℓm.symm).trans (hA.eq_par hm hk hpk hmk).symm)

theorem par_eq_par_iff {d : Set P} (hd : d ∈ lines) {p q : P} :
    par lines d p = par lines d q ↔ q ∈ par lines d p :=
  ⟨fun h => h ▸ hA.mem_par hd q, fun h => hA.eq_par hd (hA.par_mem hd p) h (hA.par_par hd p)⟩

theorem par_eq_of_par {d d' : Set P} (hd : d ∈ lines) (hd' : d' ∈ lines) (h : Par d d')
    (p : P) : par lines d' p = par lines d p :=
  (hA.eq_par hd' (hA.par_mem hd p) (hA.mem_par hd p)
    (hA.par_trans hd' hd (hA.par_mem hd p) h.symm (hA.par_par hd p))).symm

theorem not_par_of_par {d d' t : Set P} (hd : d ∈ lines) (hd' : d' ∈ lines) (ht : t ∈ lines)
    (hdt : ¬Par d t) (h : Par d d') : ¬Par d' t :=
  fun h' => hdt (hA.par_trans hd hd' ht h h')

theorem eq_of_not_par {ℓ m : Set P} (hℓ : ℓ ∈ lines) (hm : m ∈ lines) (h : ¬Par ℓ m) {x y : P}
    (hxℓ : x ∈ ℓ) (hxm : x ∈ m) (hyℓ : y ∈ ℓ) (hym : y ∈ m) : x = y := by
  by_contra hxy
  exact h (Or.inl (hA.eq_of_mem hℓ hm hxy hxℓ hyℓ hxm hym))

theorem eq_of_par_eq_of_par_eq {d d' : Set P} (hd : d ∈ lines) (hd' : d' ∈ lines)
    (hdd' : ¬Par d d') {p q : P} (h : par lines d p = par lines d q)
    (h' : par lines d' p = par lines d' q) : p = q := by
  have hdp : ¬Par (par lines d p) (par lines d' p) := fun hp =>
    hdd' (hA.par_trans hd (hA.par_mem hd p) hd' (hA.par_par hd p)
      (hA.par_trans (hA.par_mem hd p) (hA.par_mem hd' p) hd' hp (hA.par_par hd' p).symm))
  exact hA.eq_of_not_par (hA.par_mem hd p) (hA.par_mem hd' p) hdp (hA.mem_par hd p)
    (hA.mem_par hd' p) ((hA.par_eq_par_iff hd).1 h) ((hA.par_eq_par_iff hd').1 h')

section Proj

variable [Nonempty P]

theorem proj_spec {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines) (hdt : ¬Par d t) (p : P) :
    proj lines d t p ∈ t ∧ proj lines d t p ∈ par lines d p := by
  have h : ∃ x, x ∈ t ∧ x ∈ par lines d p := by
    obtain ⟨x, hx, hx'⟩ := exists_mem_of_not_par
      (hA.not_par_of_par hd (hA.par_mem hd p) ht hdt (hA.par_par hd p))
    exact ⟨x, hx', hx⟩
  exact Classical.epsilon_spec h

theorem proj_mem {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines) (hdt : ¬Par d t) (p : P) :
    proj lines d t p ∈ t :=
  (hA.proj_spec hd ht hdt p).1

theorem proj_mem_par {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines) (hdt : ¬Par d t) (p : P) :
    proj lines d t p ∈ par lines d p :=
  (hA.proj_spec hd ht hdt p).2

theorem eq_proj {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines) (hdt : ¬Par d t) {p x : P}
    (hxt : x ∈ t) (hxp : x ∈ par lines d p) : x = proj lines d t p :=
  hA.eq_of_not_par ht (hA.par_mem hd p)
    (fun h => hA.not_par_of_par hd (hA.par_mem hd p) ht hdt (hA.par_par hd p) h.symm) hxt hxp
    (hA.proj_mem hd ht hdt p) (hA.proj_mem_par hd ht hdt p)

theorem proj_of_mem {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines) (hdt : ¬Par d t) {p : P}
    (hp : p ∈ t) : proj lines d t p = p :=
  (hA.eq_proj hd ht hdt hp (hA.mem_par hd p)).symm

theorem par_proj {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines) (hdt : ¬Par d t) (p : P) :
    par lines d (proj lines d t p) = par lines d p :=
  ((hA.par_eq_par_iff hd).2 (hA.proj_mem_par hd ht hdt p)).symm

theorem proj_eq_proj_iff {d t : Set P} (hd : d ∈ lines) (ht : t ∈ lines) (hdt : ¬Par d t)
    {p q : P} : proj lines d t p = proj lines d t q ↔ par lines d p = par lines d q := by
  constructor
  · intro h
    rw [← hA.par_proj hd ht hdt p, h, hA.par_proj hd ht hdt q]
  · intro h
    simp only [proj, h]

end Proj

theorem ln_spec {p q : P} (hpq : p ≠ q) :
    ln lines p q ∈ lines ∧ p ∈ ln lines p q ∧ q ∈ ln lines p q := by
  have h : ∃ ℓ, ℓ ∈ lines ∧ p ∈ ℓ ∧ q ∈ ℓ := (hA.line_unique p q hpq).exists
  rw [ln, dite_eq_left h]
  exact h.choose_spec

theorem eq_ln {p q : P} (hpq : p ≠ q) {ℓ : Set P} (hℓ : ℓ ∈ lines) (hp : p ∈ ℓ) (hq : q ∈ ℓ) :
    ℓ = ln lines p q :=
  (hA.line_unique p q hpq).unique ⟨hℓ, hp, hq⟩ (hA.ln_spec hpq)

end IsAffinePlane

end CFSG.ComponentClassification.AS81
