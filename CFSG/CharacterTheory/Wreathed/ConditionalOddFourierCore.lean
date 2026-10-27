module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityDescriptions

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalOddFourier

open CFSG.Wreathed.ConditionalFourier

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem sum_mul_unitVector_add_sum {B : Finset ι} {q : ι} {α : Fin 3 → ι} (hq : q ∈ B)
    (hα : ∀ i, α i ∈ B) (f : ι → ℤ) (a : ℤ) (γ : Fin 3 → ℤ) :
    ∑ ψ ∈ B, f ψ * (a * unitVector q ψ + ∑ i, γ i * unitVector (α i) ψ) =
      a * f q + ∑ i, γ i * f (α i) := by
  have h : ∀ ψ, f ψ * (a * unitVector q ψ + ∑ i, γ i * unitVector (α i) ψ) =
      a * (f ψ * unitVector q ψ) + ∑ i, γ i * (f ψ * unitVector (α i) ψ) := by
    intro ψ
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun ψ _ => h ψ, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_mul_unitVector hq, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, sum_mul_unitVector (hα i)]

theorem sum_mul_unitVector_apply {α : Fin 3 → ι} (hα : Function.Injective α) (γ : Fin 3 → ℤ)
    (k : Fin 3) : ∑ i, γ i * unitVector (α i) (α k) = γ k := by
  rw [Finset.sum_eq_single k]
  · rw [unitVector_self, mul_one]
  · intro i _ hik
    rw [unitVector_of_ne fun h => hik (hα h).symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem sum_mul_unitVector_of_forall_ne {α : Fin 3 → ι} (γ : Fin 3 → ℤ) {ψ : ι}
    (hψ : ∀ i, ψ ≠ α i) : ∑ i, γ i * unitVector (α i) ψ = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [unitVector_of_ne (hψ i), mul_zero]

omit [DecidableEq ι] in
theorem exists_unique_sign_flip {β η : Fin 3 → ℤ} (hβ : ∀ i, β i = 1 ∨ β i = -1)
    (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∑ i, β i * η i = 1) :
    ∃ e : Fin 3, η e = -β e ∧ ∀ i, i ≠ e → η i = β i := by
  rw [Fin.sum_univ_three] at h
  have key : ∀ i, (η i = β i ∧ β i * η i = 1) ∨ (η i = -β i ∧ β i * η i = -1) := by
    intro i
    rcases hβ i with hb | hb <;> rcases hη i with he | he <;> rw [hb, he] <;> norm_num
  rcases key 0 with ⟨h0, h0'⟩ | ⟨h0, h0'⟩ <;> rcases key 1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases key 2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · omega
  · refine ⟨2, h2, fun i hi => ?_⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact absurd rfl hi
  · refine ⟨1, h1, fun i hi => ?_⟩
    fin_cases i
    · exact h0
    · exact absurd rfl hi
    · exact h2
  · omega
  · refine ⟨0, h0, fun i hi => ?_⟩
    fin_cases i
    · exact absurd rfl hi
    · exact h1
    · exact h2
  · omega
  · omega
  · omega

variable {B : Finset ι} {p : ι} {d : ι → ℤ} {J : Finset κ} {c : κ → ι → ℤ} {y : ι → ℤ}

theorem odd_class_constituents (hc : ParityColumns B p d J c) (hJ : 4 ≤ J.card)
    (hyval : ∀ ψ ∈ B, y ψ = 0 ∨ y ψ = 1 ∨ y ψ = -1)
    (hy4 : (B.filter fun ψ => y ψ ≠ 0).card = 4) (hyp : y p = 1)
    (hydeg : ∑ ψ ∈ B, d ψ * y ψ = 0) (horth : ∀ j ∈ J, ∑ ψ ∈ B, y ψ * c j ψ = 0)
    (hpar : ∀ j ∈ J, ∀ ψ ∈ B, c j ψ ≡ y ψ [ZMOD 2]) (hdeg2 : ∀ ψ ∈ B, ψ ≠ p → 2 ≤ d ψ) :
    ∃ (α : Fin 3 → ι) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : κ → ι) (e : Fin 3),
      Function.Injective α ∧ (∀ i, α i ∈ B ∧ α i ≠ p) ∧ (∀ i, β i = 1 ∨ β i = -1) ∧
      (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧ Set.InjOn χ J ∧
      (∀ j ∈ J, χ j ∈ B ∧ χ j ≠ p ∧ ∀ i, χ j ≠ α i) ∧ (∀ j ∈ J, ∀ t ∈ J, d (χ j) = d (χ t)) ∧
      (∀ ψ ∈ B, y ψ = unitVector p ψ + ∑ i, β i * unitVector (α i) ψ) ∧
      (∀ j ∈ J, ∀ ψ ∈ B, c j ψ =
        -unitVector p ψ + ∑ i, η i * unitVector (α i) ψ + 2 * σ * unitVector (χ j) ψ) ∧
      η e = -β e ∧ (∀ i, i ≠ e → η i = β i) ∧ 1 + ∑ i, β i * d (α i) = 0 ∧
      (∀ j ∈ J, σ * d (χ j) = 1 + β e * d (α e)) ∧ β e = σ ∧
      (∀ j ∈ J, d (χ j) = d (α e) + σ) := by
  obtain ⟨σ₀, χ₀, V₀, hf₀⟩ := hc.exists_family (by omega)
  obtain ⟨σ, χ, V, hf, hnorm⟩ := hf₀.normalize hc (by omega)
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  have hoddiff : ∀ j ∈ J, ∀ ψ ∈ B, (Odd (c j ψ) ↔ y ψ ≠ 0) := by
    intro j hj ψ hψ
    have h := hpar j hj ψ hψ
    unfold Int.ModEq at h
    rw [Int.odd_iff]
    rcases hyval ψ hψ with hy | hy | hy <;> rw [hy] at h ⊢ <;> omega
  have h0 : ∀ j ∈ J, V (χ j) = 0 := by
    rcases hnorm with h0 | h1
    · exact h0
    exfalso
    have hodd : ∀ t ∈ J, y (χ t) ≠ 0 := by
      intro t ht
      apply (hoddiff j₀ hj₀ (χ t) (hf.mem t ht)).mp
      rw [hf.eq j₀ hj₀ (χ t) (hf.mem t ht), h1 t ht, Int.odd_iff]
      rcases hf.sign with h | h <;> rw [h] <;> omega
    have hsub : insert p (J.image χ) ⊆ B.filter fun ψ => y ψ ≠ 0 := by
      intro ψ hψ
      rw [Finset.mem_insert, Finset.mem_image] at hψ
      rw [Finset.mem_filter]
      rcases hψ with rfl | ⟨t, ht, rfl⟩
      · exact ⟨hc.mem, by rw [hyp]; norm_num⟩
      · exact ⟨hf.mem t ht, hodd t ht⟩
    have hp : p ∉ J.image χ := by
      rw [Finset.mem_image]
      rintro ⟨t, ht, h⟩
      exact hf.ne t ht h
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hp, Finset.card_image_of_injOn hf.injOn, hy4] at hcard
    omega
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
  exact ⟨α, β, η, σ, χ, e, hinj, fun i => ⟨(hα i).1, (hα i).2.1⟩, hβ, hη, hf.sign, hf.injOn,
    fun j hj => ⟨hf.mem j hj, hf.ne j hj, fun i h => (hα i).2.2 j hj h.symm⟩, hf.deg, hy, hcj,
    hηe, hηi, hYdeg, hσδ, hβe, hδ⟩

end CFSG.Wreathed.ConditionalOddFourier
