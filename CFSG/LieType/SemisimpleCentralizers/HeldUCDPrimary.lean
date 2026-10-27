module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDForm
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

@[expose] noncomputable def gcF (F : Finset L[X]) (f : L[X]) : L[X] := ∏ g ∈ F.erase f, g

section Coprime

variable {F : Finset L[X]}

theorem isCoprime_of_mem_ne (hirr : ∀ f ∈ F, Irreducible f) (hmon : ∀ f ∈ F, Monic f)
    {f g : L[X]} (hf : f ∈ F) (hg : g ∈ F) (hne : f ≠ g) : IsCoprime f g := by
  rw [(hirr f hf).coprime_iff_not_dvd]
  intro hdvd
  have hassoc := (hirr f hf).associated_of_dvd (hirr g hg) hdvd
  exact hne (Polynomial.eq_of_monic_of_associated (hmon f hf) (hmon g hg) hassoc)

theorem dvd_gcF_of_ne {f g : L[X]} (hg : g ∈ F) (hne : g ≠ f) : g ∣ gcF F f :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, hg⟩)

theorem not_dvd_gcF (hirr : ∀ f ∈ F, Irreducible f) (hmon : ∀ f ∈ F, Monic f)
    {f : L[X]} (hf : f ∈ F) : ¬ f ∣ gcF F f := by
  intro hdvd
  obtain ⟨g, hg, hfg⟩ := (Prime.dvd_finset_prod_iff (hirr f hf).prime _).mp hdvd
  have hgF := Finset.mem_of_mem_erase hg
  have hne : g ≠ f := Finset.ne_of_mem_erase hg
  have hassoc := (hirr f hf).associated_of_dvd (hirr g hgF) hfg
  exact hne (Polynomial.eq_of_monic_of_associated (hmon f hf) (hmon g hgF) hassoc).symm

theorem isCoprime_gcF (hirr : ∀ f ∈ F, Irreducible f) (hmon : ∀ f ∈ F, Monic f)
    {f : L[X]} (hf : f ∈ F) : IsCoprime f (gcF F f) :=
  (hirr f hf).coprime_iff_not_dvd.mpr (not_dvd_gcF hirr hmon hf)

end Coprime

section Idempotents

variable {F : Finset L[X]}

@[expose] noncomputable def Pmat (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X]) (F : Finset L[X])
    (f : L[X]) : Matrix (Fin n) (Fin n) L :=
  aeval s (b f * gcF F f)

variable {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {b : L[X] → L[X]}

theorem dvd_prod_of_dvd_all (hirr : ∀ f ∈ F, Irreducible f) (hmon : ∀ f ∈ F, Monic f)
    (hprod : ∏ f ∈ F, f = X ^ m - 1) {q : L[X]} (h : ∀ f ∈ F, f ∣ q) : (X ^ m - 1 : L[X]) ∣ q := by
  rw [← hprod]
  refine Finset.prod_dvd_of_coprime ?_ h
  intro f hf g hg hne
  exact isCoprime_of_mem_ne hirr hmon hf hg hne

theorem aeval_eq_zero_of_dvd (hsm : s ^ m = 1) {q : L[X]} (h : (X ^ m - 1 : L[X]) ∣ q) :
    aeval s q = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [map_mul, show aeval s (X ^ m - 1 : L[X]) = 0 by simp [hsm], zero_mul]

theorem mul_gcF (hprod : ∏ f ∈ F, f = X ^ m - 1) {f : L[X]} (hf : f ∈ F) :
    f * gcF F f = X ^ m - 1 := by
  rw [← hprod]
  exact Finset.mul_prod_erase F id hf

section Splitting

variable (hirr : ∀ f ∈ F, Irreducible f) (hmon : ∀ f ∈ F, Monic f)
  (hprod : ∏ f ∈ F, f = X ^ m - 1) (hsm : s ^ m = 1)
  {a : L[X] → L[X]} (hab : ∀ f ∈ F, a f * f + b f * gcF F f = 1)
include hirr hmon hprod hsm hab

theorem sum_Pmat : ∑ f ∈ F, Pmat s b F f = 1 := by
  have hdvd : ∀ f ∈ F, f ∣ (∑ g ∈ F, b g * gcF F g) - 1 := by
    intro f hf
    rw [← Finset.add_sum_erase F _ hf]
    have h1 : f ∣ b f * gcF F f - 1 := ⟨-(a f), by linear_combination hab f hf⟩
    have h2 : f ∣ ∑ g ∈ F.erase f, b g * gcF F g := by
      refine Finset.dvd_sum fun g hg => ?_
      have hne : g ≠ f := Finset.ne_of_mem_erase hg
      exact dvd_mul_of_dvd_right (dvd_gcF_of_ne (f := g) (g := f) hf (Ne.symm hne)) (b g)
    have := dvd_add h1 h2
    convert this using 1
    ring
  have h0 := aeval_eq_zero_of_dvd hsm (dvd_prod_of_dvd_all hirr hmon hprod hdvd)
  rw [map_sub, map_sum, map_one, sub_eq_zero] at h0
  exact h0

theorem Pmat_mul_of_ne {f g : L[X]} (hf : f ∈ F) (hg : g ∈ F) (hne : f ≠ g) :
    Pmat s b F f * Pmat s b F g = 0 := by
  rw [Pmat, Pmat, ← map_mul]
  apply aeval_eq_zero_of_dvd hsm
  apply dvd_prod_of_dvd_all hirr hmon hprod
  intro h hh
  by_cases hhf : h = f
  · rw [hhf]
    have h' : f ∣ gcF F g := dvd_gcF_of_ne (f := g) (g := f) hf hne
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h' (b g)) _
  · have h' : h ∣ gcF F f := dvd_gcF_of_ne hh hhf
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h' (b f)) _

theorem Pmat_mul_self {f : L[X]} (hf : f ∈ F) :
    Pmat s b F f * Pmat s b F f = Pmat s b F f := by
  rw [Pmat, ← map_mul]
  have hfgc := mul_gcF hprod hf
  have hdvd : (X ^ m - 1 : L[X]) ∣ (b f * gcF F f) * (b f * gcF F f) - b f * gcF F f :=
    ⟨-(a f * b f), by linear_combination (b f * gcF F f) * hab f hf - (a f * b f) * hfgc⟩
  have h0 := aeval_eq_zero_of_dvd hsm hdvd
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem aeval_mul_Pmat_self {f : L[X]} (hf : f ∈ F) :
    aeval s f * Pmat s b F f = 0 := by
  rw [Pmat, ← map_mul]
  have hfgc := mul_gcF hprod hf
  have : f * (b f * gcF F f) = (X ^ m - 1 : L[X]) * b f := by
    rw [← hfgc]; ring
  rw [this]
  exact aeval_eq_zero_of_dvd hsm (dvd_mul_right _ _)

theorem aeval_mul_Pmat_iff {f : L[X]} (hf : f ∈ F) (hPf : Pmat s b F f ≠ 0) (q : L[X]) :
    aeval s q * Pmat s b F f = 0 ↔ f ∣ q := by
  constructor
  · intro h
    by_contra hnd
    have hcop : IsCoprime f q := (hirr f hf).coprime_iff_not_dvd.mpr hnd
    obtain ⟨u, v, huv⟩ := hcop
    apply hPf
    have h1 : aeval s u * aeval s f + aeval s v * aeval s q = 1 := by
      rw [← map_mul, ← map_mul, ← map_add, huv, map_one]
    calc Pmat s b F f = (aeval s u * aeval s f + aeval s v * aeval s q) * Pmat s b F f := by
          rw [h1, one_mul]
      _ = aeval s u * (aeval s f * Pmat s b F f) + aeval s v * (aeval s q * Pmat s b F f) := by
          simp only [add_mul, mul_assoc]
      _ = 0 := by
          rw [aeval_mul_Pmat_self hirr hmon hprod hsm hab hf, h, mul_zero, mul_zero, add_zero]
  · rintro ⟨r, rfl⟩
    have hc : aeval s f * aeval s r = aeval s r * aeval s f := by
      rw [← map_mul, ← map_mul, mul_comm]
    rw [map_mul, hc, mul_assoc, aeval_mul_Pmat_self hirr hmon hprod hsm hab hf, mul_zero]

theorem idem_mul_Pmat {f : L[X]} (hf : f ∈ F) (hPf : Pmat s b F f ≠ 0) {e : L[X]}
    (he : aeval s e * aeval s e = aeval s e) :
    aeval s e * Pmat s b F f = 0 ∨ aeval s e * Pmat s b F f = Pmat s b F f := by
  have h1 : aeval s (e * e - e) * Pmat s b F f = 0 := by
    rw [map_sub, map_mul, sub_mul, he, sub_self]
  have h2 : f ∣ e * (e - 1) := by
    have := (aeval_mul_Pmat_iff hirr hmon hprod hsm hab hf hPf _).mp h1
    rwa [show e * e - e = e * (e - 1) by ring] at this
  rcases (hirr f hf).prime.dvd_or_dvd h2 with h4 | h4
  · left
    exact (aeval_mul_Pmat_iff hirr hmon hprod hsm hab hf hPf e).mpr h4
  · right
    have h5 : aeval s (e - 1) * Pmat s b F f = 0 :=
      (aeval_mul_Pmat_iff hirr hmon hprod hsm hab hf hPf (e - 1)).mpr h4
    rw [map_sub, map_one, sub_mul, one_mul] at h5
    exact sub_eq_zero.mp h5

end Splitting

section Adjoint

variable {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {b : L[X] → L[X]} {F : Finset L[X]}

theorem adjM_zero' (τ : L ≃+* L) : adjM τ (0 : Matrix (Fin n) (Fin n) L) = 0 := by
  simp [adjM]

theorem Pmat_eq_of_eq (hirr : ∀ f ∈ F, Irreducible f) (hmon : ∀ f ∈ F, Monic f)
    (hprod : ∏ f ∈ F, f = X ^ m - 1) (hsm : s ^ m = 1) {a : L[X] → L[X]}
    (hab : ∀ f ∈ F, a f * f + b f * gcF F f = 1) {g g' : L[X]} (hg : g ∈ F) (hg' : g' ∈ F)
    (hPg : Pmat s b F g ≠ 0) (h : Pmat s b F g = Pmat s b F g') : g = g' := by
  by_contra hne
  apply hPg
  calc Pmat s b F g = Pmat s b F g * Pmat s b F g := (Pmat_mul_self hirr hmon hprod hsm hab hg).symm
    _ = Pmat s b F g * Pmat s b F g' := by rw [← h]
    _ = 0 := Pmat_mul_of_ne hirr hmon hprod hsm hab hg hg' hne

end Adjoint

section Perm

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}

structure PrimaryHyp (τ : L ≃+* L) (s : Matrix (Fin n) (Fin n) L) (m : ℕ) (F : Finset L[X])
    (a b : L[X] → L[X]) : Prop where
  hτ : ∀ x, τ (τ x) = x
  hm : 0 < m
  hirr : ∀ f ∈ F, Irreducible f
  hmon : ∀ f ∈ F, Monic f
  hprod : ∏ f ∈ F, f = X ^ m - 1
  hsm : s ^ m = 1
  hs : adjM τ s * s = 1
  hab : ∀ f ∈ F, a f * f + b f * gcF F f = 1

variable {a b : L[X] → L[X]}

theorem PrimaryHyp.Pmat_idem (H : PrimaryHyp τ s m F a b) {f : L[X]} (hf : f ∈ F) :
    Pmat s b F f * Pmat s b F f = Pmat s b F f :=
  _root_.CFSG.LieType.SemisimpleCentralizers.HeldUCD.Pmat_mul_self H.hirr H.hmon H.hprod H.hsm H.hab hf

theorem PrimaryHyp.Pmat_orth (H : PrimaryHyp τ s m F a b) {f g : L[X]} (hf : f ∈ F)
    (hg : g ∈ F) (hne : f ≠ g) : Pmat s b F f * Pmat s b F g = 0 :=
  _root_.CFSG.LieType.SemisimpleCentralizers.HeldUCD.Pmat_mul_of_ne H.hirr H.hmon H.hprod H.hsm H.hab hf hg hne

theorem PrimaryHyp.adjM_Pmat' (H : PrimaryHyp τ s m F a b) (f : L[X]) :
    adjM τ (Pmat s b F f) = aeval s (starP τ m (b f * gcF F f)) :=
  adjM_aeval_eq_aeval_starP τ H.hτ H.hm s H.hsm H.hs _

theorem PrimaryHyp.exists_adjM_Pmat' (H : PrimaryHyp τ s m F a b) {f : L[X]} (hf : f ∈ F)
    (hPf : Pmat s b F f ≠ 0) : ∃ g ∈ F, adjM τ (Pmat s b F f) = Pmat s b F g := by
  obtain ⟨e, he⟩ : ∃ e : L[X], adjM τ (Pmat s b F f) = aeval s e := ⟨_, H.adjM_Pmat' f⟩
  have he_idem : aeval s e * aeval s e = aeval s e := by
    rw [← he, ← adjM_mul, H.Pmat_idem hf]
  have he_ne : aeval s e ≠ 0 := by
    intro h0
    apply hPf
    rw [← adjM_adjM τ H.hτ (Pmat s b F f), he, h0, adjM_zero' τ]
  have hsum : aeval s e = ∑ g ∈ F, aeval s e * Pmat s b F g := by
    rw [← Finset.mul_sum, HeldUCD.sum_Pmat H.hirr H.hmon H.hprod H.hsm H.hab, mul_one]
  obtain ⟨g, hgF, hEg⟩ : ∃ g ∈ F, aeval s e * Pmat s b F g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply he_ne
    rw [hsum]
    exact Finset.sum_eq_zero fun g hg => hcon g hg
  have hPg : Pmat s b F g ≠ 0 := fun h0 => hEg (by rw [h0, mul_zero])
  have hEPg : aeval s e * Pmat s b F g = Pmat s b F g :=
    (HeldUCD.idem_mul_Pmat H.hirr H.hmon H.hprod H.hsm H.hab hgF hPg he_idem).resolve_left hEg
  have hadjE : adjM τ (aeval s e) = Pmat s b F f := by rw [← he, adjM_adjM τ H.hτ]
  have h2 : adjM τ (Pmat s b F g) * Pmat s b F f = adjM τ (Pmat s b F g) := by
    have := congrArg (adjM τ) hEPg
    rwa [adjM_mul, hadjE] at this
  obtain ⟨e', he'⟩ : ∃ e' : L[X], adjM τ (Pmat s b F g) = aeval s e' := ⟨_, H.adjM_Pmat' g⟩
  have he'_idem : aeval s e' * aeval s e' = aeval s e' := by
    rw [← he', ← adjM_mul, H.Pmat_idem hgF]
  have he'_ne : adjM τ (Pmat s b F g) ≠ 0 := by
    intro h0
    apply hPg
    rw [← adjM_adjM τ H.hτ (Pmat s b F g), h0, adjM_zero' τ]
  have h2' : aeval s e' * Pmat s b F f = aeval s e' := by
    rw [← he']
    exact h2
  have hEq : adjM τ (Pmat s b F g) = Pmat s b F f := by
    rcases HeldUCD.idem_mul_Pmat H.hirr H.hmon H.hprod H.hsm H.hab hf hPf he'_idem with h3 | h3
    · exfalso
      apply he'_ne
      rw [he']
      exact h2'.symm.trans h3
    · rw [he']
      exact h2'.symm.trans h3
  exact ⟨g, hgF, by rw [← hEq, adjM_adjM τ H.hτ]⟩

theorem hfm_Pmat_eq_zero {π : L[X] → L[X]} {f g : L[X]} (H : PrimaryHyp τ s m F a b)
    (hf : f ∈ F) (hg : g ∈ F) (hπ : adjM τ (Pmat s b F f) = Pmat s b F (π f))
    (hπF : π f ∈ F) (hne : g ≠ π f) (x y : Fin n → L) :
    hfm τ (Pmat s b F f *ᵥ x) (Pmat s b F g *ᵥ y) = 0 := by
  rw [hfm_mulVec, hπ, Matrix.mulVec_mulVec, H.Pmat_orth hπF hg (Ne.symm hne), Matrix.zero_mulVec]
  simp [hfm]

theorem eq_zero_of_hfm_block {π : L[X] → L[X]} {f : L[X]} (H : PrimaryHyp τ s m F a b)
    (hf : f ∈ F) (hπ : adjM τ (Pmat s b F f) = Pmat s b F (π f)) (hπF : π f ∈ F)
    {x : Fin n → L} (hx : Pmat s b F f *ᵥ x = x)
    (h : ∀ y, hfm τ x (Pmat s b F (π f) *ᵥ y) = 0) : x = 0 := by
  apply hfm_nondeg τ x
  intro z
  have hz : z = ∑ g ∈ F, Pmat s b F g *ᵥ z := by
    rw [← Matrix.sum_mulVec, HeldUCD.sum_Pmat H.hirr H.hmon H.hprod H.hsm H.hab, Matrix.one_mulVec]
  rw [hz, hfm_sum_right]
  refine Finset.sum_eq_zero fun g hg => ?_
  by_cases hgπ : g = π f
  · rw [hgπ]
    exact h _
  · have := hfm_Pmat_eq_zero H hf hg hπ hπF hgπ x z
    rw [hx] at this
    exact this

end Perm

end Idempotents

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
