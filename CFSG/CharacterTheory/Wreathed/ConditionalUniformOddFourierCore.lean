module

public import CFSG.CharacterTheory.Wreathed.ConditionalOddFourierCore

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalUniformOddFourier

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem eq_zero_of_sq_sum_le_card_odd {B O : Finset ι} {g : ι → ℤ} {ψ : ι} (hOB : O ⊆ B)
    (hψB : ψ ∈ B) (hψO : ψ ∉ O) (hodd : ∀ φ ∈ O, Odd (g φ))
    (hsq : ∑ φ ∈ B, g φ * g φ ≤ O.card) : g ψ = 0 := by
  have hone : ∀ φ ∈ O, 1 ≤ g φ * g φ := by
    intro φ hφ
    have hne : g φ ≠ 0 := by
      intro h
      have h' := hodd φ hφ
      rw [h, Int.odd_iff] at h'
      norm_num at h'
    rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
  have hbig : g ψ * g ψ + O.card ≤ ∑ φ ∈ B, g φ * g φ := by
    calc g ψ * g ψ + (O.card : ℤ) = g ψ * g ψ + ∑ _φ ∈ O, (1 : ℤ) := by simp
      _ ≤ g ψ * g ψ + ∑ φ ∈ O, g φ * g φ := by
          gcongr with φ hφ
          exact hone φ hφ
      _ = ∑ φ ∈ insert ψ O, g φ * g φ :=
          (Finset.sum_insert (f := fun φ => g φ * g φ) hψO).symm
      _ ≤ ∑ φ ∈ B, g φ * g φ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.insert_subset hψB hOB) fun φ _ _ => mul_self_nonneg _
  exact mul_self_eq_zero.mp (le_antisymm (by linarith) (mul_self_nonneg _))

variable {B : Finset ι} {p : ι} {d : ι → ℤ} {J : Finset κ} {c : κ → ι → ℤ} {y : ι → ℤ}
  {σ : ℤ} {χ : κ → ι} {V : ι → ℤ}

theorem family_constituents (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V)
    {j₀ : κ} (hj₀ : j₀ ∈ J) (h0 : ∀ j ∈ J, V (χ j) = 0)
    (hyval : ∀ ψ ∈ B, y ψ = 0 ∨ y ψ = 1 ∨ y ψ = -1) (hyp : y p = 1)
    (hydeg : ∑ ψ ∈ B, d ψ * y ψ = 0) (horth : ∀ j ∈ J, ∑ ψ ∈ B, y ψ * c j ψ = 0)
    (hpar : ∀ j ∈ J, ∀ ψ ∈ B, c j ψ ≡ y ψ [ZMOD 2]) (hdeg2 : ∀ ψ ∈ B, ψ ≠ p → 2 ≤ d ψ) :
    ∃ (α : Fin 3 → ι) (β η : Fin 3 → ℤ) (e : Fin 3),
      Function.Injective α ∧ (∀ i, α i ∈ B ∧ α i ≠ p) ∧ (∀ i, β i = 1 ∨ β i = -1) ∧
      (∀ i, η i = 1 ∨ η i = -1) ∧ (∀ j ∈ J, ∀ i, χ j ≠ α i) ∧
      (∀ ψ ∈ B, y ψ = unitVector p ψ + ∑ i, β i * unitVector (α i) ψ) ∧
      (∀ j ∈ J, ∀ ψ ∈ B, c j ψ =
        -unitVector p ψ + ∑ i, η i * unitVector (α i) ψ + 2 * σ * unitVector (χ j) ψ) ∧
      η e = -β e ∧ (∀ i, i ≠ e → η i = β i) ∧ 1 + ∑ i, β i * d (α i) = 0 ∧
      (∀ j ∈ J, σ * d (χ j) = 1 + β e * d (α e)) ∧ β e = σ ∧
      (∀ j ∈ J, d (χ j) = d (α e) + σ) := by
  have hoddiff : ∀ j ∈ J, ∀ ψ ∈ B, (Odd (c j ψ) ↔ y ψ ≠ 0) := by
    intro j hj ψ hψ
    have h := hpar j hj ψ hψ
    unfold Int.ModEq at h
    rw [Int.odd_iff]
    rcases hyval ψ hψ with hy | hy | hy <;> rw [hy] at h ⊢ <;> omega
  obtain ⟨α, η, hinj, hα, hη, hV⟩ := hf.descI hc hj₀ h0
  have hcj : ∀ j ∈ J, ∀ ψ ∈ B, c j ψ =
      -unitVector p ψ + ∑ i, η i * unitVector (α i) ψ + 2 * σ * unitVector (χ j) ψ := by
    intro j hj ψ hψ
    rw [hf.eq j hj ψ hψ, hV ψ hψ]
  have hcα : ∀ j ∈ J, ∀ k, c j (α k) = η k := by
    intro j hj k
    rw [hcj j hj (α k) (hα k).1, unitVector_of_ne (hα k).2.1, sum_mul_unitVector_apply hinj,
      unitVector_of_ne ((hα k).2.2 j hj)]
    ring
  set β : Fin 3 → ℤ := fun i => y (α i) with hβdef
  have hβ : ∀ i, β i = 1 ∨ β i = -1 := by
    intro i
    have hodd : Odd (c j₀ (α i)) := by
      rw [hcα j₀ hj₀ i, Int.odd_iff]
      rcases hη i with h | h <;> rw [h] <;> norm_num
    have hne := (hoddiff j₀ hj₀ (α i) (hα i).1).mp hodd
    rcases hyval (α i) (hα i).1 with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  have hy : ∀ ψ ∈ B, y ψ = unitVector p ψ + ∑ i, β i * unitVector (α i) ψ := by
    intro ψ hψ
    by_cases hψp : ψ = p
    · rw [hψp, hyp, unitVector_self,
        sum_mul_unitVector_of_forall_ne β fun i h => (hα i).2.1 h.symm]
      ring
    by_cases hψα : ∃ k, ψ = α k
    · obtain ⟨k, rfl⟩ := hψα
      rw [unitVector_of_ne (hα k).2.1, sum_mul_unitVector_apply hinj]
      ring
    have hψα' : ∀ i, ψ ≠ α i := fun i h => hψα ⟨i, h⟩
    have heven : ¬ Odd (c j₀ ψ) := by
      rw [hcj j₀ hj₀ ψ hψ, unitVector_of_ne hψp, sum_mul_unitVector_of_forall_ne η hψα',
        Int.odd_iff, mul_assoc]
      omega
    have hy0 : y ψ = 0 := by
      by_contra hne
      exact heven ((hoddiff j₀ hj₀ ψ hψ).mpr hne)
    rw [hy0, unitVector_of_ne hψp, sum_mul_unitVector_of_forall_ne β hψα']
    ring
  have hy' : ∀ ψ ∈ B, y ψ = 1 * unitVector p ψ + ∑ i, β i * unitVector (α i) ψ := by
    intro ψ hψ
    rw [hy ψ hψ, one_mul]
  have hαB : ∀ i, α i ∈ B := fun i => (hα i).1
  have hβη : ∑ i, β i * η i = 1 := by
    have h := horth j₀ hj₀
    have hcongr : ∑ ψ ∈ B, y ψ * c j₀ ψ =
        ∑ ψ ∈ B, c j₀ ψ * (1 * unitVector p ψ + ∑ i, β i * unitVector (α i) ψ) :=
      Finset.sum_congr rfl fun ψ hψ => by rw [hy' ψ hψ, mul_comm]
    rw [hcongr, sum_mul_unitVector_add_sum hc.mem hαB, hc.principal j₀ hj₀] at h
    simp only [hcα j₀ hj₀] at h
    linarith
  obtain ⟨e, hηe, hηi⟩ := exists_unique_sign_flip hβ hη hβη
  have hYdeg : 1 + ∑ i, β i * d (α i) = 0 := by
    have hcongr : ∑ ψ ∈ B, d ψ * y ψ =
        ∑ ψ ∈ B, d ψ * (1 * unitVector p ψ + ∑ i, β i * unitVector (α i) ψ) :=
      Finset.sum_congr rfl fun ψ hψ => by rw [hy' ψ hψ]
    rw [← hydeg, hcongr, sum_mul_unitVector_add_sum hc.mem hαB, hc.one, mul_one]
  have hXdeg : ∀ j ∈ J, -1 + ∑ i, η i * d (α i) + 2 * σ * d (χ j) = 0 := by
    intro j hj
    have hcongr : ∑ ψ ∈ B, d ψ * c j ψ =
        ∑ ψ ∈ B, (d ψ * ((-1) * unitVector p ψ + ∑ i, η i * unitVector (α i) ψ) +
          2 * σ * (d ψ * unitVector (χ j) ψ)) :=
      Finset.sum_congr rfl fun ψ hψ => by rw [hcj j hj ψ hψ]; ring
    have h := hc.degree j hj
    rw [hcongr, Finset.sum_add_distrib, sum_mul_unitVector_add_sum hc.mem hαB, ← Finset.mul_sum,
      sum_mul_unitVector (hf.mem j hj), hc.one] at h
    linarith
  have hflip : ∑ i, η i * d (α i) = ∑ i, β i * d (α i) - 2 * β e * d (α e) := by
    have h : ∑ i, (η i - β i) * d (α i) = (η e - β e) * d (α e) := by
      refine Finset.sum_eq_single e (fun i _ hie => ?_) fun h => absurd (Finset.mem_univ e) h
      rw [hηi i hie, sub_self, zero_mul]
    have h' : ∑ i, (η i - β i) * d (α i) = ∑ i, η i * d (α i) - ∑ i, β i * d (α i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h', hηe] at h
    linarith
  have hσδ : ∀ j ∈ J, σ * d (χ j) = 1 + β e * d (α e) := by
    intro j hj
    have h := hXdeg j hj
    rw [hflip] at h
    linarith
  have hA := hdeg2 (α e) (hα e).1 (hα e).2.1
  have hβe : β e = σ := by
    have h := hσδ j₀ hj₀
    have hpos := hc.pos (χ j₀) (hf.mem j₀ hj₀)
    rcases hβ e with hb | hb <;> rcases hf.sign with hs | hs <;> rw [hb, hs] at h ⊢ <;> omega
  have hδ : ∀ j ∈ J, d (χ j) = d (α e) + σ := by
    intro j hj
    have h := hσδ j hj
    rw [hβe] at h
    rcases hf.sign with hs | hs <;> rw [hs] at h ⊢ <;> omega
  exact ⟨α, β, η, e, hinj, fun i => ⟨(hα i).1, (hα i).2.1⟩, hβ, hη,
    fun j hj i h => (hα i).2.2 j hj h.symm, hy, hcj, hηe, hηi, hYdeg, hσδ, hβe, hδ⟩

end CFSG.Wreathed.ConditionalUniformOddFourier
