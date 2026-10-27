module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Omega

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Equiv Matrix CFSG.Open

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem sum_sub_sum_compl {α : Type} [Fintype α] [DecidableEq α] (e : Fin 3 ↪ α) (g : α → K) :
    ∑ j, g j - ∑ i : Fin 3, g (e i) = ∑ j ∈ (Finset.univ.image e)ᶜ, g j := by
  have h1 := Finset.sum_compl_add_sum (Finset.univ.image e) g
  rw [Finset.sum_image (fun x _ y _ h => e.injective h)] at h1
  rw [← h1]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem hQ_of_frame {m : ℕ} (hm : 3 ≤ m) (X Y : Fin m → ι) (hX : Function.Injective X)
    (hY : Function.Injective Y) (hXY : ∀ i j, X i ≠ Y j) (R Q : (ι → K) → K)
    (hQ : ∀ v, Q v = ∑ j, v (X j) * v (Y j) + R v)
    (hR : ∀ v w : ι → K, (∀ a, a ∉ Set.range X → a ∉ Set.range Y → v a = w a) → R v = R w)
    (E : P6 ↪ ι) (hEl : ∀ i, E (Sum.inl i) = X (Fin.castLE hm i))
    (hEr : ∀ i, E (Sum.inr i) = Y (Fin.castLE hm i)) (v w : ι → K)
    (hvw : ∀ a, a ∉ Set.range E → v a = w a) : Q v - Q3 E v = Q w - Q3 E w := by
  have key : ∀ u : ι → K, Q u - Q3 E u =
      ∑ j ∈ (Finset.univ.image (Fin.castLEEmb hm))ᶜ, u (X j) * u (Y j) + R u := by
    intro u
    have h := sum_sub_sum_compl (K := K) (Fin.castLEEmb hm) (fun j => u (X j) * u (Y j))
    simp only [Q3, hEl, hEr, Fin.castLEEmb_apply] at h ⊢
    rw [hQ u, add_sub_right_comm, h]
  rw [key v, key w]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : ∀ i : Fin 3, Fin.castLE hm i ≠ j := fun i hi => by
      apply (Finset.mem_compl.1 hj)
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
    have h1 : X j ∉ Set.range E := by
      rintro ⟨x, hx⟩
      rcases x with i | i
      · rw [hEl] at hx
        exact hj' i (hX hx)
      · rw [hEr] at hx
        exact hXY _ _ hx.symm
    have h2 : Y j ∉ Set.range E := by
      rintro ⟨x, hx⟩
      rcases x with i | i
      · rw [hEl] at hx
        exact hXY _ _ hx
      · rw [hEr] at hx
        exact hj' i (hY hx)
    rw [hvw _ h1, hvw _ h2]
  · refine hR v w fun a haX haY => hvw a ?_
    rintro ⟨x, hx⟩
    rcases x with i | i
    · rw [hEl] at hx
      exact haX ⟨_, hx⟩
    · rw [hEr] at hx
      exact haY ⟨_, hx⟩

theorem threeTwoWitness_omega_plus [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    ThreeTwoWitness (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  refine threeTwoWitness_statedProj_omega _
    ((Fin.castLEEmb hn).sumMap (Fin.castLEEmb hn)) ?_
  intro v w hvw
  refine hQ_of_frame hn (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr Sum.inl_injective
    Sum.inr_injective (fun _ _ => Sum.inl_ne_inr) (fun _ => 0) _ (fun v => by simp [StatedQuadPlus])
    (fun _ _ _ => rfl) _ (fun _ => rfl) (fun _ => rfl) v w hvw

theorem threeTwoWitness_omega_odd [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    ThreeTwoWitness (StatedProj (StatedOmega (StatedQuadOdd n K))) := by
  refine threeTwoWitness_statedProj_omega _
    ((Fin.castLEEmb hn).sumMap ((Fin.castLEEmb hn).trans Function.Embedding.inl)) ?_
  intro v w hvw
  refine hQ_of_frame hn (Sum.inl : Fin n → Fin n ⊕ Fin n ⊕ Unit) (fun j => Sum.inr (Sum.inl j))
    Sum.inl_injective (fun a b h => Sum.inl_injective (Sum.inr_injective h))
    (fun _ _ => Sum.inl_ne_inr) (fun v => v (Sum.inr (Sum.inr ())) ^ 2) _
    (fun v => rfl) ?_ _ (fun _ => rfl) (fun _ => rfl) v w hvw
  intro v w h
  have := h (Sum.inr (Sum.inr ())) (by
    rintro ⟨i, hi⟩
    cases hi) (by
    rintro ⟨i, hi⟩
    cases hi)
  simp [this]

theorem threeTwoWitness_omega_minus [Finite K] {n : ℕ} (hn : 4 ≤ n) (b c : K) :
    ThreeTwoWitness (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  have hn' : 3 ≤ n - 1 := by omega
  refine threeTwoWitness_statedProj_omega _
    ((Fin.castLEEmb hn').sumMap ((Fin.castLEEmb hn').trans Function.Embedding.inl)) ?_
  intro v w hvw
  refine hQ_of_frame hn' (Sum.inl : Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (fun j => Sum.inr (Sum.inl j)) Sum.inl_injective
    (fun a b h => Sum.inl_injective (Sum.inr_injective h)) (fun _ _ => Sum.inl_ne_inr)
    (fun v => v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
      c * v (Sum.inr (Sum.inr 1)) ^ 2) _ (fun v => ?_) ?_ _ (fun _ => rfl) (fun _ => rfl) v w hvw
  · simp only [StatedQuadMinus]
    ring
  · intro v w h
    have h0 := h (Sum.inr (Sum.inr 0)) (by
      rintro ⟨i, hi⟩
      cases hi) (by
      rintro ⟨i, hi⟩
      cases hi)
    have h1 := h (Sum.inr (Sum.inr 1)) (by
      rintro ⟨i, hi⟩
      cases hi) (by
      rintro ⟨i, hi⟩
      cases hi)
    simp [h0, h1]

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
