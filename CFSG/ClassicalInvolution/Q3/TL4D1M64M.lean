module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAME
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32D
public import CFSG.ClassicalInvolution.Q3.TL4D1M3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Equiv Matrix

theorem fanoVec_l32 {σ : Perm (Fin 7)} (hσ : σ ∈ l32) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∀ y, fanoVec (σ y) = A.1 *ᵥ fanoVec y := by
  obtain ⟨A, rfl⟩ := exists_lpermHom_eq hσ
  exact ⟨A, fun y => by rw [lpermHom_apply, fanoVec_lapply]⟩

theorem fixed_of_line {σ : Perm (Fin 7)} (hσ : σ ∈ l32) (h2 : σ * σ = 1) {x z : Fin 7}
    (h : fanoVec x + fanoVec (σ x) = fanoVec z) : σ z = z := by
  obtain ⟨A, hA⟩ := fanoVec_l32 hσ
  have hxx : σ (σ x) = x := apply_apply_of_mul_self h2 x
  apply fanoVec_injective
  rw [hA, ← h, mulVec_add, ← hA, ← hA, hxx, add_comm]

theorem fano_four : ∀ p q r w : Fin 7, p ≠ q → p ≠ r → p ≠ w → q ≠ r → q ≠ w → r ≠ w →
    fanoVec p + fanoVec q ≠ fanoVec r → fanoVec p + fanoVec q ≠ fanoVec w →
    fanoVec p + fanoVec r ≠ fanoVec w → fanoVec q + fanoVec r ≠ fanoVec w →
    ∃ ℓ ∈ fanoLines, ({p, q, r, w} : Finset (Fin 7)) = ℓᶜ := by
  decide

theorem e64_regular : ∀ s ∈ l32, ∀ t ∈ l32, s * s = 1 → t * t = 1 → s * t = t * s → ∀ a,
    s a ≠ a → t a ≠ a → s (t a) ≠ a → ({a, s a, t a, s (t a)} : Finset (Fin 7)) ∈ e64Sets := by
  intro s hs t ht hs2 ht2 hst a hsa hta hsta
  have hss := apply_apply_of_mul_self hs2
  have htt := apply_apply_of_mul_self ht2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by rw [← Perm.mul_apply, ← hst, Perm.mul_apply]
  have e5 : t a ≠ s a := fun h => hsta (by rw [h, hss])
  have e6 : s (t a) ≠ s a := fun h => hta (s.injective h)
  have e7 : s (t a) ≠ t a := fun h => hsa (t.injective (by rw [hts, h]))
  have hu2 : s * t * (s * t) = 1 := by
    calc s * t * (s * t) = s * (t * s) * t := by group
      _ = s * s * (t * t) := by rw [← hst]; group
      _ = 1 := by rw [hs2, ht2, one_mul]
  have c1 : fanoVec a + fanoVec (s a) ≠ fanoVec (t a) := fun h => e7 (fixed_of_line hs hs2 h)
  have c2 : fanoVec a + fanoVec (s a) ≠ fanoVec (s (t a)) := fun h => by
    have := fixed_of_line hs hs2 h
    rw [hss] at this
    exact e7 this.symm
  have c3 : fanoVec a + fanoVec (t a) ≠ fanoVec (s (t a)) := fun h => by
    have := fixed_of_line ht ht2 h
    rw [hts, htt] at this
    exact e6 this.symm
  have c4 : fanoVec (s a) + fanoVec (t a) ≠ fanoVec (s (t a)) := fun h => by
    have hsa' : (s * t) (s a) = t a := by rw [Perm.mul_apply, hts, hss]
    have h' : fanoVec (s a) + fanoVec ((s * t) (s a)) = fanoVec (s (t a)) := by rw [hsa']; exact h
    have := fixed_of_line (l32.mul_mem hs ht) hu2 h'
    rw [Perm.mul_apply, hts, htt, hss] at this
    exact hsta this.symm
  exact fano_four a (s a) (t a) (s (t a)) (Ne.symm hsa) (Ne.symm hta) (Ne.symm hsta)
    (Ne.symm e5) (Ne.symm e6) (Ne.symm e7) c1 c2 c3 c4

theorem e64_members : ModelMembers e64Sets e64Sub :=
  modelMembers_of_regular (by norm_num) l32_sign fun s hs t ht hs2 ht2 hst a hsa hta hsta =>
    Or.inl (e64_regular s hs t ht hs2 ht2 hst a hsa hta hsta)

theorem e64_facts : ModelFacts e64Sets e64Sub :=
  ⟨e64_normal, e64_perfect, e64_three, e64_members⟩

end CFSG.ClassicalInvolution.Q3.TL4
