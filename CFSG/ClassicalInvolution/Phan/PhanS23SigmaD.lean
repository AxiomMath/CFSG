module

public import CFSG.ClassicalInvolution.Phan.PhanS23SigmaB

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Descent

@[expose] def cCoef (ρ ς : ZMod 7) : GF49 := ⟨4 * ρ, -(4 * ς)⟩

@[expose] def dCoef (ρ ς : ZMod 7) : GF49 := ⟨4 * ρ, 4 * ς⟩

theorem cd_apply (ρ ς : ZMod 7) (z : GF49) :
    cCoef ρ ς * z + dCoef ρ ς * star z = algebraMap (ZMod 7) GF49 (ρ * z.re + ς * z.im) := by
  have hh : (2 : ZMod 7) * 4 = 1 := by decide
  refine QuadraticAlgebra.ext ?_ ?_
  · simp only [cCoef, dCoef, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.algebraMap_re]
    linear_combination (ρ * z.re + ς * z.im) * hh
  · simp only [cCoef, dCoef, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.algebraMap_im]
    ring

@[expose] def Zfam {ι : Type} (u : ι → Fin 7 → GF49) : ι ⊕ ι → Fin 7 → ZMod 7 :=
  Sum.elim (fun i => reV (u i)) (fun i => imV (u i))

theorem sum_Zfam {ι : Type} [Fintype ι] (u : ι → Fin 7 → GF49) (r : ι ⊕ ι → ZMod 7) :
    ∑ k, r k • Zfam u k =
      fun j => ∑ i, (r (Sum.inl i) * (u i j).re + r (Sum.inr i) * (u i j).im) := by
  funext j
  simp only [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Zfam,
    Sum.elim_inl, Sum.elim_inr, reV, imV, Finset.sum_add_distrib]

theorem sum_cd {ι : Type} [Fintype ι] (u : ι → Fin 7 → GF49) (r : ι ⊕ ι → ZMod 7) :
    ∑ i, cCoef (r (Sum.inl i)) (r (Sum.inr i)) • u i +
        ∑ i, dCoef (r (Sum.inl i)) (r (Sum.inr i)) • starV (u i) =
      fun j => algebraMap (ZMod 7) GF49
        (∑ i, (r (Sum.inl i) * (u i j).re + r (Sum.inr i) * (u i j).im)) := by
  funext j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, starV,
    ← Finset.sum_add_distrib, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    cd_apply (r (Sum.inl i)) (r (Sum.inr i)) (u i j)

theorem rel_iff {ι : Type} [Fintype ι] (u : ι → Fin 7 → GF49) (r : ι ⊕ ι → ZMod 7) :
    ∑ k, r k • Zfam u k = 0 ↔
      ∑ i, cCoef (r (Sum.inl i)) (r (Sum.inr i)) • u i +
        ∑ i, dCoef (r (Sum.inl i)) (r (Sum.inr i)) • starV (u i) = 0 := by
  rw [sum_Zfam, sum_cd]
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    simp only [Pi.zero_apply] at hj ⊢
    rw [hj, map_zero]
  · intro h
    funext j
    have hj := congrFun h j
    simp only [Pi.zero_apply] at hj ⊢
    exact (map_eq_zero_iff _ (QuadraticAlgebra.algebraMap_injective)).1 hj

theorem two_cancel {a b : ZMod 7} (h : 2 * a = 2 * b) : a = b :=
  mul_left_cancel₀ (by decide) h

theorem gram4 {ι : Type} {u u' : ι → Fin 7 → GF49}
    (h1 : ∀ i j, polarK (u i) (u j) = polarK (u' i) (u' j))
    (h2 : ∀ i j, polarK (u i) (starV (u j)) = polarK (u' i) (starV (u' j))) (i j : ι) :
    QuadraticMap.polar qF (reV (u i)) (reV (u j)) =
        QuadraticMap.polar qF (reV (u' i)) (reV (u' j)) ∧
      QuadraticMap.polar qF (imV (u i)) (imV (u j)) =
        QuadraticMap.polar qF (imV (u' i)) (imV (u' j)) ∧
      QuadraticMap.polar qF (reV (u i)) (imV (u j)) =
        QuadraticMap.polar qF (reV (u' i)) (imV (u' j)) ∧
      QuadraticMap.polar qF (imV (u i)) (reV (u j)) =
        QuadraticMap.polar qF (imV (u' i)) (reV (u' j)) := by
  have e1 := congrArg QuadraticAlgebra.re (h1 i j)
  have e2 := congrArg QuadraticAlgebra.re (h2 i j)
  have e3 := congrArg QuadraticAlgebra.im (h1 i j)
  have e4 := congrArg QuadraticAlgebra.im (h2 i j)
  rw [polarK_re, polarK_re] at e1
  rw [polarK_starV_re, polarK_starV_re] at e2
  rw [polarK_im, polarK_im] at e3
  rw [polarK_starV_im, polarK_starV_im] at e4
  exact ⟨two_cancel (by linear_combination e1 + e2), two_cancel (by linear_combination e2 - e1),
    two_cancel (by linear_combination e3 - e4), two_cancel (by linear_combination e3 + e4)⟩

theorem descent_witt (hW : FamilyWitt7) {ι : Type} [Fintype ι] (u u' : ι → Fin 7 → GF49)
    (h1 : ∀ i j, polarK (u i) (u j) = polarK (u' i) (u' j))
    (h2 : ∀ i j, polarK (u i) (starV (u j)) = polarK (u' i) (starV (u' j)))
    (h3 : ∀ c d : ι → GF49, ∑ i, c i • u i + ∑ i, d i • starV (u i) = 0 ↔
      ∑ i, c i • u' i + ∑ i, d i • starV (u' i) = 0) :
    ∃ E : (Fin 7 → GF49) ≃ₗ[GF49] (Fin 7 → GF49),
      (∀ x y, polarK (E x) (E y) = polarK x y) ∧ (∀ x, E (starV x) = starV (E x)) ∧
        ∀ i, E (u i) = u' i := by
  have hgram : ∀ k l, QuadraticMap.polar qF (Zfam u k) (Zfam u l) =
      QuadraticMap.polar qF (Zfam u' k) (Zfam u' l) := by
    rintro (i | i) (j | j)
    · exact (gram4 h1 h2 i j).1
    · exact (gram4 h1 h2 i j).2.2.1
    · exact (gram4 h1 h2 i j).2.2.2
    · exact (gram4 h1 h2 i j).2.1
  have hrel : ∀ c : ι ⊕ ι → ZMod 7, ∑ k, c k • Zfam u k = 0 ↔ ∑ k, c k • Zfam u' k = 0 := by
    intro c
    rw [rel_iff, rel_iff]
    exact h3 (fun i => cCoef (c (Sum.inl i)) (c (Sum.inr i)))
      (fun i => dCoef (c (Sum.inl i)) (c (Sum.inr i)))
  obtain ⟨e, he⟩ := hW (ι ⊕ ι) (Zfam u) (Zfam u') hgram hrel
  refine ⟨extEquiv e, polarK_extEquiv e, starV_extEquiv e, fun i => ext_reV_imV ?_ ?_⟩
  · rw [reV_extEquiv]
    exact he (Sum.inl i)
  · rw [imV_extEquiv]
    exact he (Sum.inr i)

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Descent
