module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {Ω : Type*} [DecidableEq Ω]

@[expose] def dblGens (σ : Perm Ω) (c : Ω → Bool) : Set (Perm Ω) :=
  {g | ∃ x y, y ≠ x ∧ y ≠ σ x ∧ c y = c x ∧ g = swap x (σ x) * swap y (σ y)}

@[expose] def dblGroup (σ : Perm Ω) (c : Ω → Bool) : Subgroup (Perm Ω) :=
  Subgroup.closure (dblGens σ c)

omit [DecidableEq Ω] in
theorem not_isPGroup_of_threeCycle {P : Subgroup (Perm Ω)} (hP : IsPGroup 2 P) {g : Perm Ω}
    (hg : g ∈ P) {a b c : Ω} (hab : a ≠ b) (_hbc : b ≠ c) (hca : c ≠ a)
    (h1 : g a = b) (h2 : g b = c) (h3 : g c = a) : False := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hk' : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcube : ∀ x, g (g (g x)) = x → (g ^ 3) x = x := by
    intro x hx
    simpa [pow_succ, Perm.mul_apply] using hx
  have ha3 : (g ^ 3) a = a := hcube a (by rw [h1, h2, h3])
  have hb3 : (g ^ 3) b = b := hcube b (by rw [h2, h3, h1])
  have hc3 : (g ^ 3) c = c := hcube c (by rw [h3, h1, h2])
  have hmod : 2 ^ k % 3 ≠ 0 := by
    intro h
    have : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  have hsplit : 2 ^ k = 3 * (2 ^ k / 3) + 2 ^ k % 3 := (Nat.div_add_mod _ _).symm
  have hfix : ∀ x, (g ^ 3) x = x → (g ^ (3 * (2 ^ k / 3))) x = x := by
    intro x hx
    rw [pow_mul]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hx _
  have hr : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by omega
  have key : (g ^ (2 ^ k)) a = a := by rw [hk']; rfl
  rcases hr with hr | hr
  · rw [hsplit, hr, pow_add, Perm.mul_apply, pow_one, h1, hfix b hb3] at key
    exact hab key.symm
  · rw [hsplit, hr, pow_add, Perm.mul_apply] at key
    have : (g ^ 2) a = c := by simp [pow_succ, Perm.mul_apply, h1, h2]
    rw [this, hfix c hc3] at key
    exact hca key

theorem threeCycle_of_blocks {p p' d q q' e f : Ω}
    (hpp' : p ≠ p') (hpd : p ≠ d) (hp'd : p' ≠ d)
    (hqp : q ≠ p) (hqp' : q ≠ p') (hqd : q ≠ d)
    (hq'p : q' ≠ p) (hq'p' : q' ≠ p') (hq'd : q' ≠ d)
    (hep : e ≠ p) (hep' : e ≠ p') (hed : e ≠ d)
    (hfp : f ≠ p) (hfp' : f ≠ p') (hfd : f ≠ d) :
    ((swap p p' * swap q q') * (swap p d * swap e f)) p = d ∧
    ((swap p p' * swap q q') * (swap p d * swap e f)) d = p' ∧
    ((swap p p' * swap q q') * (swap p d * swap e f)) p' = p := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hep.symm hfp.symm, swap_apply_left,
      swap_apply_of_ne_of_ne hqd.symm hq'd.symm, swap_apply_of_ne_of_ne hpd.symm hp'd.symm]
  · simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hed.symm hfd.symm, swap_apply_right,
      swap_apply_of_ne_of_ne hqp.symm hq'p.symm, swap_apply_left]
  · simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hep'.symm hfp'.symm, swap_apply_of_ne_of_ne hpp'.symm hp'd,
      swap_apply_of_ne_of_ne hqp'.symm hq'p'.symm, swap_apply_right]

section Matching

variable [Fintype Ω]

@[expose] def cls (c : Ω → Bool) (x : Ω) : Finset Ω := Finset.univ.filter fun y => c y = c x

omit [DecidableEq Ω] in
theorem cls_card_eq (c : Ω → Bool) {x y : Ω} (h : c x = c y) : (cls c x).card = (cls c y).card := by
  simp [cls, h]

omit [DecidableEq Ω] in
theorem eq_of_card_cls_two (c : Ω → Bool) (hcard : 6 ≤ Fintype.card Ω) {x y : Ω}
    (hx : (cls c x).card = 2) (hy : (cls c y).card = 2) : c x = c y := by
  by_contra hne
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω))
    (fun z => c z = c x)
  have hsub : Finset.univ.filter (fun z => ¬ c z = c x) = cls c y := by
    ext z
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hz : c z <;> cases hxx : c x <;> cases hyy : c y <;> simp_all
  rw [hsub] at hpart
  have h1 : (Finset.univ.filter (fun z => c z = c x)).card = 2 := hx
  rw [h1, hy, Finset.card_univ] at hpart
  omega

variable {σ : Perm Ω}

theorem cls_eq_pair (c : Ω → Bool) (hσ1 : ∀ x, σ x ≠ x) (hc : ∀ x, c (σ x) = c x) {x : Ω}
    (hx : (cls c x).card = 2) : cls c x = {x, σ x} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | rfl
    · rfl
    · exact hc _
  · rw [hx, Finset.card_pair (hσ1 x).symm]

theorem exists_mem_cls_aux (c : Ω → Bool) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (hc : ∀ x, c (σ x) = c x) {p d : Ω} (hdp : d ≠ p) (hdσ : d ≠ σ p)
    (h2 : (cls c p).card ≠ 2) (h4 : (cls c p).card ≠ 4) :
    ∃ q, c q = c p ∧ q ≠ p ∧ q ≠ σ p ∧ q ≠ d ∧ q ≠ σ d := by
  by_contra hno
  push Not at hno
  have hsub : cls c p ⊆ {p, σ p, d, σ d} := by
    intro z hz
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    by_cases h1 : z = p
    · simp [h1]
    by_cases h2 : z = σ p
    · simp [h2]
    by_cases h3 : z = d
    · simp [h3]
    by_cases h4 : z = σ d
    · simp [h4]
    exact absurd (hno z hz h1 h2 h3) h4
  have hp : p ∈ cls c p := by simp [cls]
  have hp' : σ p ∈ cls c p := by simp [cls, hc]
  by_cases hd : d ∈ cls c p
  · have hd0 : c d = c p := by simpa [cls] using hd
    have hd' : σ d ∈ cls c p := by simp [cls, hc, hd0]
    have : cls c p = {p, σ p, d, σ d} := by
      apply Finset.Subset.antisymm hsub
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    apply h4
    rw [this]
    have e1 : p ≠ σ p := (hσ1 p).symm
    have e2 : p ≠ d := hdp.symm
    have e3 : p ≠ σ d := by
      intro h; apply hdσ; rw [← hσ2 d, ← h]
    have e4 : σ p ≠ d := hdσ.symm
    have e5 : σ p ≠ σ d := by
      intro h; apply hdp; have := congrArg σ h; rw [hσ2, hσ2] at this; exact this.symm
    have e6 : d ≠ σ d := (hσ1 d).symm
    simp [Finset.card_insert_of_notMem, e1, e2, e3, e4, e5, e6]
  · have hd' : σ d ∉ cls c p := by
      intro h
      apply hd
      simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      rw [← hc d]; exact h
    have : cls c p = {p, σ p} := by
      apply Finset.Subset.antisymm
      · intro z hz
        have := hsub hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        rcases this with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (h ▸ hz) hd
        · exact absurd (h ▸ hz) hd'
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
    exact h2 (by rw [this, Finset.card_pair (hσ1 p).symm])

omit [DecidableEq Ω] in
theorem mem_cls_iff (c : Ω → Bool) {x y : Ω} : y ∈ cls c x ↔ c y = c x := by
  simp [cls]

section TwoMatchings

variable {σ τ : Perm Ω} {cσ cτ : Ω → Bool}

theorem key_no_cover (hcard : 6 ≤ Fintype.card Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (hcσ : ∀ x, cσ (σ x) = cσ x)
    (hτ1 : ∀ x, τ x ≠ x) (hτ2 : ∀ x, τ (τ x) = x) (hcτ : ∀ x, cτ (τ x) = cτ x)
    (hall : ∀ x, σ x ≠ τ x → (cls cσ x).card = 2 ∨ (cls cτ x).card = 2)
    {p : Ω} (hp : σ p ≠ τ p) (hN : (cls cσ p).card = 2) : False := by
  have hpair : cls cσ p = {p, σ p} := cls_eq_pair (σ := σ) cσ hσ1 hcσ hN
  have hdΔ : σ (τ p) ≠ τ (τ p) := by
    rw [hτ2]
    intro h
    apply hp
    have := congrArg σ h
    rw [hσ2] at this
    exact this.symm
  have hqΔ : σ (τ (σ p)) ≠ τ (τ (σ p)) := by
    rw [hτ2]
    intro h
    apply hp
    have h1 : τ (σ p) = p := by
      have := congrArg σ h
      rw [hσ2] at this
      rw [this, hσ2]
    have := congrArg τ h1
    rw [hτ2] at this
    exact this
  have hdN : (cls cτ (τ p)).card = 2 := by
    rcases hall _ hdΔ with h | h
    · exfalso
      have hc := eq_of_card_cls_two cσ hcard h hN
      have hmem : τ p ∈ cls cσ p := (mem_cls_iff cσ).2 hc
      rw [hpair] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact hτ1 p h'
      · exact hp h'.symm
    · exact h
  have hqN : (cls cτ (τ (σ p))).card = 2 := by
    rcases hall _ hqΔ with h | h
    · exfalso
      have h' : (cls cσ (σ p)).card = 2 := by rw [cls_card_eq cσ (hcσ p)]; exact hN
      have hc := eq_of_card_cls_two cσ hcard h h'
      have hmem : τ (σ p) ∈ cls cσ (σ p) := (mem_cls_iff cσ).2 hc
      rw [cls_eq_pair (σ := σ) cσ hσ1 hcσ h'] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton, hσ2] at hmem
      rcases hmem with h'' | h''
      · exact hτ1 _ h''
      · apply hp
        have := congrArg τ h''
        rw [hτ2] at this
        exact this
    · exact h
  have hc := eq_of_card_cls_two cτ hcard hqN hdN
  have hmem : τ (σ p) ∈ cls cτ (τ p) := (mem_cls_iff cτ).2 hc
  rw [cls_eq_pair (σ := τ) cτ hτ1 hcτ hdN] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, hτ2] at hmem
  rcases hmem with h' | h'
  · exact hσ1 p (τ.injective h')
  · apply hp
    have := congrArg τ h'
    rw [hτ2] at this
    exact this

theorem exists_good_point (hcard : 6 ≤ Fintype.card Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (hcσ : ∀ x, cσ (σ x) = cσ x)
    (hτ1 : ∀ x, τ x ≠ x) (hτ2 : ∀ x, τ (τ x) = x) (hcτ : ∀ x, cτ (τ x) = cτ x)
    (hne : σ ≠ τ) :
    ∃ p, σ p ≠ τ p ∧ (cls cσ p).card ≠ 2 ∧ (cls cτ p).card ≠ 2 := by
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ τ p := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  by_contra hno
  push Not at hno
  have hall : ∀ x, σ x ≠ τ x → (cls cσ x).card = 2 ∨ (cls cτ x).card = 2 := by
    intro x hx
    by_contra h
    push Not at h
    exact h.2 (hno x hx h.1)
  by_cases hN : (cls cσ p).card = 2
  · exact key_no_cover hcard hσ1 hσ2 hcσ hτ1 hτ2 hcτ hall hp hN
  · have hN' : (cls cτ p).card = 2 := hno p hp hN
    refine key_no_cover (σ := τ) (τ := σ) hcard hτ1 hτ2 hcτ hσ1 hσ2 hcσ ?_ hp.symm hN'
    intro x hx
    exact (hall x hx.symm).symm

theorem eq_of_dblGroup_le_isPGroup (hcard : 6 ≤ Fintype.card Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (hcσ : ∀ x, cσ (σ x) = cσ x)
    (hτ1 : ∀ x, τ x ≠ x) (hτ2 : ∀ x, τ (τ x) = x) (hcτ : ∀ x, cτ (τ x) = cτ x)
    (h4σ : ∀ x, (cls cσ x).card ≠ 4) (h4τ : ∀ x, (cls cτ x).card ≠ 4)
    {P : Subgroup (Perm Ω)} (hP : IsPGroup 2 P)
    (hσP : dblGroup σ cσ ≤ P) (hτP : dblGroup τ cτ ≤ P) : σ = τ := by
  by_contra hne
  obtain ⟨p, hp, hNσ, hNτ⟩ := exists_good_point hcard hσ1 hσ2 hcσ hτ1 hτ2 hcτ hne
  obtain ⟨q, hqc, hqp, hqp', hqd, hqd'⟩ := exists_mem_cls_aux (σ := σ) cσ hσ1 hσ2 hcσ
    (p := p) (d := τ p) (hτ1 p) (Ne.symm hp) hNσ (h4σ p)
  obtain ⟨e, hec, hep, hep', hed, hed'⟩ := exists_mem_cls_aux (σ := τ) cτ hτ1 hτ2 hcτ
    (p := p) (d := σ p) (hσ1 p) hp hNτ (h4τ p)
  have hx : swap p (σ p) * swap q (σ q) ∈ dblGroup σ cσ :=
    Subgroup.subset_closure ⟨p, q, hqp, hqp', hqc, rfl⟩
  have hy : swap p (τ p) * swap e (τ e) ∈ dblGroup τ cτ :=
    Subgroup.subset_closure ⟨p, e, hep, hep', hec, rfl⟩
  have hg := P.mul_mem (hσP hx) (hτP hy)
  have hσinj : ∀ a b, σ a = σ b → a = b := fun a b h => σ.injective h
  have hτinj : ∀ a b, τ a = τ b → a = b := fun a b h => τ.injective h
  obtain ⟨h1, h2, h3⟩ := threeCycle_of_blocks (p := p) (p' := σ p) (d := τ p) (q := q)
    (q' := σ q) (e := e) (f := τ e) (hσ1 p).symm (hτ1 p).symm hp
    hqp hqp' hqd
    (by intro h; apply hqp'; rw [← h, hσ2])
    (by intro h; exact hqp (hσinj _ _ h))
    (by intro h; apply hqd'; rw [← h, hσ2])
    hep hed hep'
    (by intro h; apply hep'; rw [← h, hτ2])
    (by intro h; apply hed'; rw [← h, hτ2])
    (by intro h; exact hep (hτinj _ _ h))
  exact not_isPGroup_of_threeCycle hP hg (a := p) (b := τ p) (c := σ p)
    (hτ1 p).symm hp.symm (hσ1 p) h1 h2 h3

end TwoMatchings

end Matching

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

end
