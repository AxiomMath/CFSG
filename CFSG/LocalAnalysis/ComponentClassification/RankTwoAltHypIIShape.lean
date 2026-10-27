module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIILocal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIITransport

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoHypIIY

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sign_eq_one_of_fixedPoints {t w : Perm α} (hw : w ^ 2 = 1) (hwt : (w * t) ^ 2 = 1)
    (hfix : ∀ x, w x = x ↔ (w * t) x = x) : sign t = 1 := by
  have h1 := sign_of_pow_two_eq_one hw
  have h2 := sign_of_pow_two_eq_one hwt
  have hcard : Fintype.card (Function.fixedPoints w) =
      Fintype.card (Function.fixedPoints (w * t)) :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun x => hfix x)
  have ht : t = w * (w * t) := by rw [← mul_assoc, ← sq, hw, one_mul]
  rw [ht, map_mul, h1, h2, hcard]
  exact Int.units_mul_self _

theorem exists_twoOrbit_of_sign_ne_one {t s : Perm α} (ht2 : ∀ x, t (t x) = x)
    (hs2 : ∀ x, s (s x) = x) (hts : ∀ x, t (s x) = s (t x)) (hsign : sign t ≠ 1) :
    ∃ p, t p ≠ p ∧ (s p = p ∨ s p = t p) := by
  by_contra hcon
  push Not at hcon
  let wf : α → α := fun x => if t x = x then x else s x
  have hst : ∀ x, t x ≠ x → t (s x) ≠ s x := fun x hx h => hx (by
    rw [hts] at h
    exact s.injective h)
  have hinv : Function.Involutive wf := by
    intro x
    by_cases hx : t x = x
    · simp only [wf, hx, ↓reduceIte]
    · simp only [wf, hx, hst x hx, ↓reduceIte, hs2]
  let w : Perm α := hinv.toPerm
  have hw : ∀ x, w x = wf x := fun x => rfl
  have hwt : ∀ x, w (t x) = t (w x) := by
    intro x
    by_cases hx : t x = x
    · rw [hw, hw, hx]
      simp only [wf, hx, ↓reduceIte]
    · have htx : t (t x) ≠ t x := by rw [ht2]; exact fun h => hx h.symm
      simp only [hw, wf, hx, htx, ↓reduceIte, hts]
  refine hsign (sign_eq_one_of_fixedPoints (w := w) ?_ ?_ fun x => ?_)
  · ext x
    simp only [sq, Perm.mul_apply, Perm.one_apply, hw, hinv x]
  · ext x
    simp only [sq, Perm.mul_apply, Perm.one_apply, hwt, ht2, hw, hinv x]
  · simp only [Perm.mul_apply]
    by_cases hx : t x = x
    · simp [hw, wf, hx]
    · have htx : t (t x) ≠ t x := by rw [ht2]; exact fun h => hx h.symm
      obtain ⟨hsx, hstx⟩ := hcon x hx
      simp only [hw, wf, hx, htx, ↓reduceIte]
      refine ⟨fun h => absurd h hsx, fun h => absurd ?_ hstx⟩
      have h' := congrArg s h
      rw [hs2] at h'
      exact h'.symm


theorem s1a_apply : ∀ i, s1a i = ![1, 0, 3, 2, 5, 4] i := by decide +kernel
theorem s1b_apply : ∀ i, s1b i = ![0, 1, 4, 5, 2, 3] i := by decide +kernel
theorem s2a_apply : ∀ i, s2a i = ![1, 0, 3, 2, 4, 5] i := by decide +kernel
theorem s2b_apply : ∀ i, s2b i = ![0, 1, 2, 3, 5, 4] i := by decide +kernel
theorem s3a_apply : ∀ i, s3a i = ![0, 2, 1, 3, 4] i := by decide +kernel
theorem s3b_apply : ∀ i, s3b i = ![0, 1, 2, 4, 3] i := by decide +kernel

theorem qWitness_of_model {k : ℕ} (hk : 5 ≤ k) {a b : Perm (Fin k)}
    (hA : alternatingGroup (Fin k) ≤ nE (alternatingGroup (Fin k)) (closure {a, b}))
    {E : Subgroup (Perm α)} {ya yb : Perm α} (hya : ya ∈ E) (hyb : yb ∈ E) (f : Fin k → α)
    (hf : Function.Injective f) (ha : ∀ i, ya (f i) = f (a i)) (hb : ∀ i, yb (f i) = f (b i)) :
    QWitness (alternatingGroup α) E :=
  qWitness_of_alternatingGroup_le_nE ⟨f, hf⟩ (by simpa using hk)
    (forall_mem_closure_pair ⟨f, hf⟩ hya hyb ha hb) hA

theorem sign_eq_of_bijective {k : ℕ} {f : Fin k → α} (hf : Function.Bijective f) {y : Perm α}
    {m : Perm (Fin k)} (hy : ∀ i, y (f i) = f (m i)) : sign y = sign m := by
  have h : y = (Equiv.ofBijective f hf).permCongr m := by
    ext x
    obtain ⟨i, rfl⟩ := hf.2 x
    rw [Equiv.permCongr_apply, Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply, hy]
  rw [h, sign_permCongr]

theorem sign_eq_of_embedding {k : ℕ} (f : Fin k ↪ α) {y : Perm α} {m : Perm (Fin k)}
    (hy : ∀ i, y (f i) = f (m i)) (hfix : ∀ x, x ∉ Set.range f → y x = x) :
    sign y = sign m := by
  have h : y = viaEmbeddingHom f m := by
    ext x
    by_cases hx : x ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hx
      rw [hy, viaEmbeddingHom_apply_image]
    · rw [hfix x hx, viaEmbeddingHom_apply_of_notMem f m hx]
  rw [h, sign_viaEmbeddingHom]

section Models

variable {E : Subgroup (Perm α)} {ya yb : Perm α} (hya : ya ∈ E) (hyb : yb ∈ E)
  (ha2 : ∀ x, ya (ya x) = x) (hb2 : ∀ x, yb (yb x) = x) (hab : ∀ x, ya (yb x) = yb (ya x))
include hya hyb ha2 hb2 hab

theorem qWitness_s1 {p r : α} (hp1 : yb p = p) (hp2 : ya p ≠ p) (hr1 : ya r ≠ r)
    (hr2 : yb r ≠ r) (hr3 : ya r ≠ yb r) : QWitness (alternatingGroup α) E := by
  have hyap : yb (ya p) = ya p := by rw [← hab, hp1]
  have h01 : p ≠ ya p := fun h => hp2 h.symm
  have h02 : p ≠ r := by rintro rfl; exact hr2 hp1
  have h03 : p ≠ ya r := by
    rintro rfl; apply hr2; rw [← hab] at hp1; exact ya.injective hp1
  have h04 : p ≠ yb r := by
    rintro rfl; rw [hb2] at hp1; exact hr2 hp1.symm
  have h05 : p ≠ ya (yb r) := by
    rintro rfl; apply hr2; rw [← hab, hb2] at hp1; exact (ya.injective hp1).symm
  have h12 : ya p ≠ r := by intro h; rw [h] at hyap; exact hr2 hyap
  have h13 : ya p ≠ ya r := fun h => h02 (ya.injective h)
  have h14 : ya p ≠ yb r := by intro h; rw [h, hb2] at hyap; exact hr2 hyap.symm
  have h15 : ya p ≠ ya (yb r) := fun h => h04 (ya.injective h)
  have h23 : r ≠ ya r := fun h => hr1 h.symm
  have h24 : r ≠ yb r := fun h => hr2 h.symm
  have h25 : r ≠ ya (yb r) := by
    intro h; have h' := congrArg ya h; rw [ha2] at h'; exact hr3 h'
  have h35 : ya r ≠ ya (yb r) := fun h => h24 (ya.injective h)
  have h45 : yb r ≠ ya (yb r) := by
    intro h; apply hr1; rw [hab] at h; exact (yb.injective h).symm
  refine qWitness_of_model (by norm_num) alternatingGroup_le_nE_s1 hya hyb
    ![p, ya p, r, ya r, yb r, ya (yb r)] ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
        | exact h01 hij | exact h01 hij.symm | exact h02 hij | exact h02 hij.symm
        | exact h03 hij | exact h03 hij.symm | exact h04 hij | exact h04 hij.symm
        | exact h05 hij | exact h05 hij.symm | exact h12 hij | exact h12 hij.symm
        | exact h13 hij | exact h13 hij.symm | exact h14 hij | exact h14 hij.symm
        | exact h15 hij | exact h15 hij.symm | exact h23 hij | exact h23 hij.symm
        | exact h24 hij | exact h24 hij.symm | exact h25 hij | exact h25 hij.symm
        | exact hr3 hij | exact hr3 hij.symm | exact h35 hij | exact h35 hij.symm
        | exact h45 hij | exact h45 hij.symm
  · intro i
    rw [s1a_apply]
    fin_cases i <;> simp [ha2]
  · intro i
    rw [s1b_apply]
    fin_cases i <;> simp [hb2, hp1, hyap, hab]


theorem qWitness_s2 {p p' r : α} (hp1 : yb p = p) (hp2 : ya p ≠ p) (hq1 : yb p' = p')
    (hq2 : ya p' ≠ p') (hpq : p' ≠ p) (hpq' : p' ≠ ya p) (hr1 : ya r = r) (hr2 : yb r ≠ r) :
    QWitness (alternatingGroup α) E := by
  have hyap : yb (ya p) = ya p := by rw [← hab, hp1]
  have hyaq : yb (ya p') = ya p' := by rw [← hab, hq1]
  have hybr : ya (yb r) = yb r := by rw [hab, hr1]
  have h01 : p ≠ ya p := fun h => hp2 h.symm
  have h02 : p ≠ p' := fun h => hpq h.symm
  have h03 : p ≠ ya p' := by
    intro h; apply hpq'; rw [h, ha2]
  have h04 : p ≠ r := by rintro rfl; exact hp2 hr1
  have h05 : p ≠ yb r := by rintro rfl; exact hp2 hybr
  have h12 : ya p ≠ p' := fun h => hpq' h.symm
  have h13 : ya p ≠ ya p' := fun h => h02 (ya.injective h)
  have h14 : ya p ≠ r := by
    intro h; apply h04; have h' := congrArg ya h; rwa [ha2, hr1] at h'
  have h15 : ya p ≠ yb r := by
    intro h; have h' := congrArg ya h; rw [ha2, hybr] at h'; exact h05 h'
  have h23 : p' ≠ ya p' := fun h => hq2 h.symm
  have h24 : p' ≠ r := by rintro rfl; exact hq2 hr1
  have h25 : p' ≠ yb r := by rintro rfl; exact hq2 hybr
  have h34 : ya p' ≠ r := by
    intro h; apply h24; have h' := congrArg ya h; rwa [ha2, hr1] at h'
  have h35 : ya p' ≠ yb r := by
    intro h; have h' := congrArg ya h; rw [ha2, hybr] at h'; exact h25 h'
  have h45 : r ≠ yb r := fun h => hr2 h.symm
  refine qWitness_of_model (by norm_num) alternatingGroup_le_nE_s2 hya hyb
    ![p, ya p, p', ya p', r, yb r] ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
        | exact h01 hij | exact h01 hij.symm | exact h02 hij | exact h02 hij.symm
        | exact h03 hij | exact h03 hij.symm | exact h04 hij | exact h04 hij.symm
        | exact h05 hij | exact h05 hij.symm | exact h12 hij | exact h12 hij.symm
        | exact h13 hij | exact h13 hij.symm | exact h14 hij | exact h14 hij.symm
        | exact h15 hij | exact h15 hij.symm | exact h23 hij | exact h23 hij.symm
        | exact h24 hij | exact h24 hij.symm | exact h25 hij | exact h25 hij.symm
        | exact h34 hij | exact h34 hij.symm | exact h35 hij | exact h35 hij.symm
        | exact h45 hij | exact h45 hij.symm
  · intro i
    rw [s2a_apply]
    fin_cases i <;> simp [ha2, hr1, hybr]
  · intro i
    rw [s2b_apply]
    fin_cases i <;> simp [hb2, hp1, hq1, hyap, hyaq]

theorem qWitness_s3 {f p r : α} (hf1 : ya f = f) (hf2 : yb f = f) (hp1 : yb p = p)
    (hp2 : ya p ≠ p) (hr1 : ya r = r) (hr2 : yb r ≠ r) : QWitness (alternatingGroup α) E := by
  have hyap : yb (ya p) = ya p := by rw [← hab, hp1]
  have hybr : ya (yb r) = yb r := by rw [hab, hr1]
  have h01 : f ≠ p := by rintro rfl; exact hp2 hf1
  have h02 : f ≠ ya p := by
    intro h; have h' := congrArg ya h; rw [ha2, hf1] at h'; exact h01 h'
  have h03 : f ≠ r := by rintro rfl; exact hr2 hf2
  have h04 : f ≠ yb r := by
    intro h; have h' := congrArg yb h; rw [hb2, hf2] at h'; exact h03 h'
  have h12 : p ≠ ya p := fun h => hp2 h.symm
  have h13 : p ≠ r := by rintro rfl; exact hp2 hr1
  have h14 : p ≠ yb r := by rintro rfl; exact hp2 hybr
  have h23 : ya p ≠ r := by
    intro h; apply h13; have h' := congrArg ya h; rwa [ha2, hr1] at h'
  have h24 : ya p ≠ yb r := by
    intro h; have h' := congrArg ya h; rw [ha2, hybr] at h'; exact h14 h'
  have h34 : r ≠ yb r := fun h => hr2 h.symm
  refine qWitness_of_model (by norm_num) alternatingGroup_le_nE_s3 hya hyb
    ![f, p, ya p, r, yb r] ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
        | exact h01 hij | exact h01 hij.symm | exact h02 hij | exact h02 hij.symm
        | exact h03 hij | exact h03 hij.symm | exact h04 hij | exact h04 hij.symm
        | exact h12 hij | exact h12 hij.symm | exact h13 hij | exact h13 hij.symm
        | exact h14 hij | exact h14 hij.symm | exact h23 hij | exact h23 hij.symm
        | exact h24 hij | exact h24 hij.symm | exact h34 hij | exact h34 hij.symm
  · intro i
    rw [s3a_apply]
    fin_cases i <;> simp [ha2, hf1, hr1, hybr]
  · intro i
    rw [s3b_apply]
    fin_cases i <;> simp [hb2, hf2, hp1, hyap]

end Models

@[expose] def s4a : Perm (Fin 6) := swap 0 1 * swap 4 5

@[expose] def s4b : Perm (Fin 6) := swap 2 3 * swap 4 5

theorem s4a_apply : ∀ i, s4a i = ![1, 0, 2, 3, 5, 4] i := by decide +kernel
theorem s4b_apply : ∀ i, s4b i = ![0, 1, 3, 2, 5, 4] i := by decide +kernel

section Parity

variable {ya yb : Perm α} (ha2 : ∀ x, ya (ya x) = x) (hb2 : ∀ x, yb (yb x) = x)
  (hab : ∀ x, ya (yb x) = yb (ya x))
include ha2 hb2 hab

theorem sign_eq_one_s4 {p q f : α} (hp1 : yb p = p) (hp2 : ya p ≠ p) (hq1 : ya q = q)
    (hq2 : yb q ≠ q) (hf1 : ya f = yb f) (hf2 : ya f ≠ f) (hfp : f ≠ p) (hfyp : f ≠ ya p)
    (hfq : f ≠ q) (hfyq : f ≠ yb q) (hall : ∀ x, x = p ∨ x = ya p ∨ x = q ∨ x = yb q ∨ x = f ∨
      x = ya f) : sign ya = 1 ∧ sign yb = 1 := by
  have hyap : yb (ya p) = ya p := by rw [← hab, hp1]
  have hybq : ya (yb q) = yb q := by rw [hab, hq1]
  have hybf : yb (ya f) = f := by rw [← hab, ← hf1, ha2]
  have h01 : p ≠ ya p := fun h => hp2 h.symm
  have h02 : p ≠ q := by rintro rfl; exact hq2 hp1
  have h03 : p ≠ yb q := by
    intro h; have h' := congrArg yb h; rw [hb2, hp1] at h'; exact h02 h'
  have h04 : p ≠ f := fun h => hfp h.symm
  have h05 : p ≠ ya f := by
    intro h; apply hfp; have h' := congrArg yb h; rw [hp1, hybf] at h'; exact h'.symm
  have h12 : ya p ≠ q := by
    intro h; apply h02; have h' := congrArg ya h; rwa [ha2, hq1] at h'
  have h13 : ya p ≠ yb q := by
    intro h; apply h03; have h' := congrArg ya h; rwa [ha2, hybq] at h'
  have h14 : ya p ≠ f := fun h => hfyp h.symm
  have h15 : ya p ≠ ya f := fun h => h04 (ya.injective h)
  have h23 : q ≠ yb q := fun h => hq2 h.symm
  have h24 : q ≠ f := fun h => hfq h.symm
  have h25 : q ≠ ya f := by
    intro h; apply hfq; have h' := congrArg ya h; rw [hq1, ha2] at h'; exact h'.symm
  have h34 : yb q ≠ f := fun h => hfyq h.symm
  have h35 : yb q ≠ ya f := by
    intro h; apply hfyq; have h' := congrArg ya h; rw [hybq, ha2] at h'; exact h'.symm
  have h45 : f ≠ ya f := fun h => hf2 h.symm
  have hinj : Function.Injective ![p, ya p, q, yb q, f, ya f] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
        | exact h01 hij | exact h01 hij.symm | exact h02 hij | exact h02 hij.symm
        | exact h03 hij | exact h03 hij.symm | exact h04 hij | exact h04 hij.symm
        | exact h05 hij | exact h05 hij.symm | exact h12 hij | exact h12 hij.symm
        | exact h13 hij | exact h13 hij.symm | exact h14 hij | exact h14 hij.symm
        | exact h15 hij | exact h15 hij.symm | exact h23 hij | exact h23 hij.symm
        | exact h24 hij | exact h24 hij.symm | exact h25 hij | exact h25 hij.symm
        | exact h34 hij | exact h34 hij.symm | exact h35 hij | exact h35 hij.symm
        | exact h45 hij | exact h45 hij.symm
  have hsurj : Function.Surjective ![p, ya p, q, yb q, f, ya f] := by
    intro x
    rcases hall x with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  have ha : ∀ i, ya (![p, ya p, q, yb q, f, ya f] i) = ![p, ya p, q, yb q, f, ya f] (s4a i) := by
    intro i
    rw [s4a_apply]
    fin_cases i <;> simp [ha2, hq1, hybq]
  have hb : ∀ i, yb (![p, ya p, q, yb q, f, ya f] i) = ![p, ya p, q, yb q, f, ya f] (s4b i) := by
    intro i
    rw [s4b_apply]
    fin_cases i <;> simp [hb2, hp1, hyap, hf1]
  rw [sign_eq_of_bijective ⟨hinj, hsurj⟩ ha, sign_eq_of_bijective ⟨hinj, hsurj⟩ hb]
  exact ⟨by decide +kernel, by decide +kernel⟩

end Parity



theorem sign_swap01_swap23 : sign (swap (0 : Fin 4) 1 * swap 2 3) = 1 := by decide +kernel

theorem swap01_swap23_apply :
    ∀ i : Fin 4, (swap (0 : Fin 4) 1 * swap 2 3 : Perm (Fin 4)) i = ![1, 0, 3, 2] i := by
  decide +kernel

theorem qWitness_of_twoOrbit' (h5 : 5 ≤ Fintype.card α) {E : Subgroup (Perm α)} {t s : Perm α}
    (htE : t ∈ E) (hsE : s ∈ E) (ht2 : ∀ x, t (t x) = x) (hs2 : ∀ x, s (s x) = x)
    (hts : ∀ x, t (s x) = s (t x)) (hsign : sign t ≠ 1 ∨ 7 ≤ Fintype.card α) (hs1 : s ≠ 1)
    {p₀ : α} (hp1 : s p₀ = p₀) (hp2 : t p₀ ≠ p₀) : QWitness (alternatingGroup α) E := by
  have hst : ∀ x, s (t x) = t (s x) := fun x => (hts x).symm
  have hu2 : ∀ x, (t * s) ((t * s) x) = x := fun x => by
    simp only [Perm.mul_apply, hts, ht2, hs2]
  have huE : t * s ∈ E := E.mul_mem htE hsE
  have htu : ∀ x, t ((t * s) x) = (t * s) (t x) := fun x => by simp only [Perm.mul_apply, hts]
  have hus : ∀ x, (t * s) (s x) = s ((t * s) x) := fun x => by simp only [Perm.mul_apply, hts]
  have hutp : (t * s) p₀ = t p₀ := by rw [Perm.mul_apply, hp1]
  have hstp : s (t p₀) = t p₀ := by rw [hst, hp1]
  by_cases hreg : ∃ q, t q ≠ q ∧ s q ≠ q ∧ t q ≠ s q
  · obtain ⟨q, hq1, hq2, hq3⟩ := hreg
    exact qWitness_s1 htE hsE ht2 hs2 hts hp1 hp2 hq1 hq2 hq3
  push Not at hreg
  obtain ⟨r, hr⟩ : ∃ r, s r ≠ r := by
    by_contra h
    push Not at h
    exact hs1 (Equiv.ext h)
  by_cases htr : t r = r
  ·
    have hsr : t (s r) = s r := by rw [hts, htr]
    by_cases hfix : ∃ f, t f = f ∧ s f = f
    · obtain ⟨f, hf1, hf2⟩ := hfix
      exact qWitness_s3 htE hsE ht2 hs2 hts hf1 hf2 hp1 hp2 htr hr
    push Not at hfix
    by_cases h2s : ∃ q, s q = q ∧ t q ≠ q ∧ q ≠ p₀ ∧ q ≠ t p₀
    · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := h2s
      exact qWitness_s2 htE hsE ht2 hs2 hts hp1 hp2 hq1 hq2 hq3 hq4 htr hr
    push Not at h2s
    by_cases h2t : ∃ q, t q = q ∧ s q ≠ q ∧ q ≠ r ∧ q ≠ s r
    · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := h2t
      exact qWitness_s2 hsE htE hs2 ht2 hst htr hr hq1 hq2 hq3 hq4 hp1 hp2
    push Not at h2t
    by_cases hu : ∃ q, t q ≠ q ∧ s q = t q
    · obtain ⟨q, hq1, hq2⟩ := hu
      have huq : (t * s) q = q := by rw [Perm.mul_apply, hq2, ht2]
      by_cases h2u : ∃ q', t q' ≠ q' ∧ s q' = t q' ∧ q' ≠ q ∧ q' ≠ t q
      · obtain ⟨q', hq1', hq2', hq3', hq4'⟩ := h2u
        have huq' : (t * s) q' = q' := by rw [Perm.mul_apply, hq2', ht2]
        have hur : (t * s) r ≠ r := by rw [Perm.mul_apply, hts, htr]; exact hr
        exact qWitness_s2 htE huE ht2 hu2 htu huq hq1 huq' hq1' hq3' hq4' htr hur
      push Not at h2u
      exfalso
      have hall6 : ∀ x, x = p₀ ∨ x = t p₀ ∨ x = r ∨ x = s r ∨ x = q ∨ x = t q := by
        intro x
        by_cases hx1 : t x = x
        · by_cases hx2 : s x = x
          · exact absurd hx2 (hfix x hx1)
          · rcases or_iff_not_imp_left.mpr (h2t x hx1 hx2) with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · by_cases hx2 : s x = x
          · rcases or_iff_not_imp_left.mpr (h2s x hx2 hx1) with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rcases or_iff_not_imp_left.mpr (h2u x hx1 (hreg x hx1 hx2).symm) with h | h
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      rcases hsign with hsign | h7
      · refine hsign (sign_eq_one_s4 ht2 hs2 hts hp1 hp2 htr hr hq2.symm hq1 ?_ ?_ ?_ ?_
          hall6).1
        · rintro rfl; rw [hp1] at hq2; exact hp2 hq2.symm
        · rintro rfl; rw [hstp, ht2] at hq2; exact hp2 hq2
        · rintro rfl; exact hq1 htr
        · rintro rfl; exact hq1 hsr
      · have hsub : (Finset.univ : Finset α) ⊆ {p₀, t p₀, r, s r, q, t q} := by
          intro x _
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hall6 x
        have := (Finset.card_le_card hsub).trans Finset.card_le_six
        rw [Finset.card_univ] at this
        omega
    push Not at hu
    exfalso
    have hall : (Finset.univ : Finset α) ⊆ {p₀, t p₀, r, s r} := by
      intro x _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx1 : t x = x
      · by_cases hx2 : s x = x
        · exact absurd hx2 (hfix x hx1)
        · rcases or_iff_not_imp_left.mpr (h2t x hx1 hx2) with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      · by_cases hx2 : s x = x
        · rcases or_iff_not_imp_left.mpr (h2s x hx2 hx1) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact absurd (hreg x hx1 hx2).symm (hu x hx1)
    have := (Finset.card_le_card hall).trans Finset.card_le_four
    rw [Finset.card_univ] at this
    omega
  ·
    have hsr : s r = t r := (hreg r htr hr).symm
    have hur : (t * s) r = r := by rw [Perm.mul_apply, hsr, ht2]
    by_cases hq : ∃ q, t q ≠ q ∧ q ≠ p₀ ∧ q ≠ t p₀ ∧ q ≠ r ∧ q ≠ t r
    · obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ := hq
      by_cases hsq : s q = q
      · have huq : (t * s) q ≠ q := by rw [Perm.mul_apply, hsq]; exact hq1
        exact qWitness_s2 huE hsE hu2 hs2 hus hp1 (by rw [hutp]; exact hp2) hsq huq hq2
          (by rw [hutp]; exact hq3) hur hr
      · have huq : (t * s) q = q := by rw [Perm.mul_apply, ← hreg q hq1 hsq, ht2]
        exact qWitness_s2 hsE huE hs2 hu2 (fun x => (hus x).symm) hur hr huq hsq hq4
          (by rw [hsr]; exact hq5) hp1 (by rw [hutp]; exact hp2)
    push Not at hq
    rcases hsign with hsign | h7
    · exfalso
      have hstr : s (t r) ≠ t r := by
        rw [hst, hsr, ht2]; exact fun h => htr h.symm
      have hinj : Function.Injective ![p₀, t p₀, r, t r] := by
        have h01 : p₀ ≠ t p₀ := fun h => hp2 h.symm
        have h02 : p₀ ≠ r := by rintro rfl; exact hr hp1
        have h03 : p₀ ≠ t r := by rintro rfl; exact hstr hp1
        have h12 : t p₀ ≠ r := by rintro rfl; exact hr hstp
        have h13 : t p₀ ≠ t r := fun h => h02 (t.injective h)
        have h23 : r ≠ t r := fun h => htr h.symm
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
          first
            | exact h01 hij | exact h01 hij.symm | exact h02 hij | exact h02 hij.symm
            | exact h03 hij | exact h03 hij.symm | exact h12 hij | exact h12 hij.symm
            | exact h13 hij | exact h13 hij.symm | exact h23 hij | exact h23 hij.symm
      refine hsign ((sign_eq_of_embedding ⟨_, hinj⟩ (m := swap 0 1 * swap 2 3) ?_ ?_).trans
        sign_swap01_swap23)
      · intro i
        rw [swap01_swap23_apply]
        fin_cases i <;> simp [ht2]
      · intro x hx
        by_contra hx1
        by_cases h0 : x = p₀
        · exact hx ⟨0, by simp [h0]⟩
        by_cases h1 : x = t p₀
        · exact hx ⟨1, by simp [h1]⟩
        by_cases h2 : x = r
        · exact hx ⟨2, by simp [h2]⟩
        exact hx ⟨3, by simp [hq x hx1 h0 h1 h2]⟩
    ·
      have hfixT : ∀ x, x ≠ p₀ → x ≠ t p₀ → x ≠ r → x ≠ t r → t x = x := fun x h0 h1 h2 h3 => by
        by_contra hx1
        exact h3 (hq x hx1 h0 h1 h2)
      have hS3 : ∀ f, t f = f → s f = f → QWitness (alternatingGroup α) E := fun f hf1 hf2 =>
        qWitness_s3 huE hsE hu2 hs2 hus (f := f) (by rw [Perm.mul_apply, hf2, hf1]) hf2 hp1
          (by rw [hutp]; exact hp2) hur hr
      obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {p₀, t p₀, r, t r}) (t := Finset.univ)
        (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_four (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
      have htx := hfixT x hx0 hx1 hx2 hx3
      by_cases hsx : s x = x
      · exact hS3 x htx hsx
      obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {p₀, t p₀, r, t r, x, s x}) (t := Finset.univ)
        (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_six (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5⟩ := hy
      have hty := hfixT y hy0 hy1 hy2 hy3
      by_cases hsy : s y = y
      · exact hS3 y hty hsy
      exact qWitness_s2 hsE htE hs2 ht2 hst htx hsx hty hsy hy4 hy5 hp1 hp2

theorem qWitness_of_twoOrbit (h5 : 5 ≤ Fintype.card α) {E : Subgroup (Perm α)} {t s : Perm α}
    (htE : t ∈ E) (hsE : s ∈ E) (ht2 : ∀ x, t (t x) = x) (hs2 : ∀ x, s (s x) = x)
    (hts : ∀ x, t (s x) = s (t x)) (hsign : sign t ≠ 1) (hs1 : s ≠ 1) {p₀ : α}
    (hp1 : s p₀ = p₀) (hp2 : t p₀ ≠ p₀) : QWitness (alternatingGroup α) E :=
  qWitness_of_twoOrbit' h5 htE hsE ht2 hs2 hts (Or.inl hsign) hs1 hp1 hp2

end CFSG.ComponentClassification.RankTwoAlt
