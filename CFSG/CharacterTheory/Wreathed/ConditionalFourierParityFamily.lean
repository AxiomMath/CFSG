module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityCore
public import CFSG.CharacterTheory.Blocks.NormTwoCommonSign

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFourier

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

structure ParityColumns (B : Finset ι) (p : ι) (d : ι → ℤ) (J : Finset κ) (c : κ → ι → ℤ) :
    Prop where
  mem : p ∈ B
  pos : ∀ χ ∈ B, 0 < d χ
  one : d p = 1
  gram : ∀ j ∈ J, ∀ t ∈ J, ∑ χ ∈ B, c j χ * c t χ = if j = t then 8 else 4
  degree : ∀ j ∈ J, ∑ χ ∈ B, d χ * c j χ = 0
  principal : ∀ j ∈ J, c j p = -1
  parity : ∀ j ∈ J, ∀ t ∈ J, ∀ χ ∈ B, 2 ∣ c j χ - c t χ

structure ParityFamily (B : Finset ι) (p : ι) (d : ι → ℤ) (J : Finset κ) (c : κ → ι → ℤ)
    (σ : ℤ) (χ : κ → ι) (V : ι → ℤ) : Prop where
  sign : σ = 1 ∨ σ = -1
  injOn : Set.InjOn χ J
  mem : ∀ j ∈ J, χ j ∈ B
  ne : ∀ j ∈ J, χ j ≠ p
  deg : ∀ j ∈ J, ∀ t ∈ J, d (χ j) = d (χ t)
  eq : ∀ j ∈ J, ∀ ψ ∈ B, c j ψ = V ψ + 2 * σ * unitVector (χ j) ψ

variable {B : Finset ι} {p : ι} {d : ι → ℤ} {J : Finset κ} {c : κ → ι → ℤ}

namespace ParityColumns

theorem exists_root (hc : ParityColumns B p d J c) {j₀ j : κ} (hj₀ : j₀ ∈ J) (hj : j ∈ J)
    (hne : j ≠ j₀) :
    ∃ α β, α ∈ B ∧ β ∈ B ∧ α ≠ β ∧ α ≠ p ∧ β ≠ p ∧ d α = d β ∧
      ∀ χ ∈ B, c j χ = c j₀ χ + 2 * (unitVector α χ - unitVector β χ) := by
  set r : ι → ℤ := fun χ => (c j χ - c j₀ χ) / 2
  have h2r : ∀ χ ∈ B, 2 * r χ = c j χ - c j₀ χ := fun χ hχ =>
    Int.mul_ediv_cancel' (hc.parity j hj j₀ hj₀ χ hχ)
  have hsq : ∑ χ ∈ B, r χ ^ 2 = 2 := by
    have hcongr : ∑ χ ∈ B, (2 * r χ) ^ 2 = ∑ χ ∈ B, (c j χ * c j χ -
        2 * (c j χ * c j₀ χ) + c j₀ χ * c j₀ χ) :=
      Finset.sum_congr rfl fun χ hχ => by rw [h2r χ hχ]; ring
    have h4 : ∑ χ ∈ B, (2 * r χ) ^ 2 = 8 := by
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hc.gram j hj j hj, hc.gram j hj j₀ hj₀, hc.gram j₀ hj₀ j₀ hj₀, ite_eq_left rfl,
        ite_eq_right hne, ite_eq_left rfl]
      norm_num
    have h4' : ∑ χ ∈ B, (2 * r χ) ^ 2 = 4 * ∑ χ ∈ B, r χ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    omega
  have hsum : ∑ χ ∈ B, d χ * r χ = 0 := by
    have hcongr : ∑ χ ∈ B, 2 * (d χ * r χ) = ∑ χ ∈ B, (d χ * c j χ - d χ * c j₀ χ) :=
      Finset.sum_congr rfl fun χ hχ => by rw [← mul_sub, ← h2r χ hχ]; ring
    have h : 2 * ∑ χ ∈ B, d χ * r χ = 0 := by
      rw [Finset.mul_sum, hcongr, Finset.sum_sub_distrib, hc.degree j hj, hc.degree j₀ hj₀,
        sub_zero]
    omega
  obtain ⟨α, hα, β, hβ, hαβ, hdeg, hroot⟩ := root_of_sq_sum_two hc.pos hsq hsum
  have hrp : r p = 0 := by
    have h := h2r p hc.mem
    rw [hc.principal j hj, hc.principal j₀ hj₀] at h
    omega
  have hrα : r α = 1 := by
    rw [hroot α hα, unitVector_self, unitVector_of_ne hαβ]
    norm_num
  have hrβ : r β = -1 := by
    rw [hroot β hβ, unitVector_self, unitVector_of_ne (Ne.symm hαβ)]
    norm_num
  refine ⟨α, β, hα, hβ, hαβ, fun h => ?_, fun h => ?_, hdeg, fun χ hχ => ?_⟩
  · rw [h, hrp] at hrα
    exact absurd hrα (by norm_num)
  · rw [h, hrp] at hrβ
    exact absurd hrβ (by norm_num)
  · have h := h2r χ hχ
    rw [hroot χ hχ] at h
    linarith

theorem inner_roots (hc : ParityColumns B p d J c) {j₀ j t : κ} (hj₀ : j₀ ∈ J) (hj : j ∈ J)
    (ht : t ∈ J) (hj0 : j ≠ j₀) (ht0 : t ≠ j₀) (hjt : j ≠ t) {a b a' b' : ι}
    (hrj : ∀ χ ∈ B, c j χ = c j₀ χ + 2 * (unitVector a χ - unitVector b χ))
    (hrt : ∀ χ ∈ B, c t χ = c j₀ χ + 2 * (unitVector a' χ - unitVector b' χ)) :
    ∑ χ ∈ B, (unitVector a χ - unitVector b χ) * (unitVector a' χ - unitVector b' χ) = 1 := by
  have hexp : ∑ χ ∈ B, (c j χ - c j₀ χ) * (c t χ - c j₀ χ) = ∑ χ ∈ B, (c j χ * c t χ -
      c j χ * c j₀ χ - c j₀ χ * c t χ + c j₀ χ * c j₀ χ) :=
    Finset.sum_congr rfl fun χ _ => by ring
  have h4 : ∑ χ ∈ B, (c j χ - c j₀ χ) * (c t χ - c j₀ χ) = 4 := by
    rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hc.gram j hj t ht, hc.gram j hj j₀ hj₀, hc.gram j₀ hj₀ t ht, hc.gram j₀ hj₀ j₀ hj₀,
      ite_eq_right hjt, ite_eq_right hj0, ite_eq_right (Ne.symm ht0), ite_eq_left rfl]
    norm_num
  have hcongr : ∑ χ ∈ B, (c j χ - c j₀ χ) * (c t χ - c j₀ χ) =
      4 * ∑ χ ∈ B, (unitVector a χ - unitVector b χ) * (unitVector a' χ - unitVector b' χ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hrj χ hχ, hrt χ hχ]
    ring
  omega

end ParityColumns

theorem parityFamily_of_common {j₀ : κ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {y : ι} {x : κ → ι}
    (hy : y ∈ B) (hyp : y ≠ p)
    (hx : ∀ j ∈ J.erase j₀, x j ∈ B ∧ x j ≠ p ∧ x j ≠ y ∧ d (x j) = d y)
    (hxinj : Set.InjOn x (J.erase j₀))
    (hrep : ∀ j ∈ J.erase j₀, ∀ ψ ∈ B,
      c j ψ = c j₀ ψ + 2 * σ * (unitVector (x j) ψ - unitVector y ψ)) :
    ParityFamily B p d J c σ (fun j => if j = j₀ then y else x j)
      (fun ψ => c j₀ ψ - 2 * σ * unitVector y ψ) := by
  have hmem : ∀ {j}, j ∈ J → j ≠ j₀ → j ∈ J.erase j₀ := fun hj hne =>
    Finset.mem_erase.mpr ⟨hne, hj⟩
  refine ⟨hσ, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj t ht h
    by_cases hj0 : j = j₀ <;> by_cases ht0 : t = j₀
    · rw [hj0, ht0]
    · simp only [hj0, ht0, ↓reduceIte] at h
      exact absurd h.symm (hx t (hmem ht ht0)).2.2.1
    · simp only [hj0, ht0, ↓reduceIte] at h
      exact absurd h (hx j (hmem hj hj0)).2.2.1
    · simp only [hj0, ht0, ↓reduceIte] at h
      exact hxinj (hmem hj hj0) (hmem ht ht0) h
  · intro j hj
    by_cases hj0 : j = j₀
    · simpa only [hj0, ↓reduceIte] using hy
    · simpa only [hj0, ↓reduceIte] using (hx j (hmem hj hj0)).1
  · intro j hj
    by_cases hj0 : j = j₀
    · simpa only [hj0, ↓reduceIte] using hyp
    · simpa only [hj0, ↓reduceIte] using (hx j (hmem hj hj0)).2.1
  · have hd : ∀ j ∈ J, d (if j = j₀ then y else x j) = d y := by
      intro j hj
      by_cases hj0 : j = j₀
      · simp only [hj0, ↓reduceIte]
      · simpa only [hj0, ↓reduceIte] using (hx j (hmem hj hj0)).2.2.2
    intro j hj t ht
    rw [hd j hj, hd t ht]
  · intro j hj ψ hψ
    by_cases hj0 : j = j₀
    · simp only [hj0, ↓reduceIte]
      ring
    · simp only [hj0, ↓reduceIte]
      rw [hrep j (hmem hj hj0) ψ hψ]
      ring

namespace ParityColumns

theorem exists_family (hc : ParityColumns B p d J c) (hJ : 2 ≤ J.card) :
    ∃ σ χ V, ParityFamily B p d J c σ χ V := by
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  have hRcard : (J.erase j₀).card = J.card - 1 := Finset.card_erase_of_mem hj₀
  obtain ⟨j₁, hj₁⟩ : (J.erase j₀).Nonempty := Finset.card_pos.mp (by omega)
  have hroots : ∀ j ∈ J.erase j₀, ∃ α β, α ∈ B ∧ β ∈ B ∧ α ≠ β ∧ α ≠ p ∧ β ≠ p ∧
      d α = d β ∧ ∀ χ ∈ B, c j χ = c j₀ χ + 2 * (unitVector α χ - unitVector β χ) :=
    fun j hj => hc.exists_root hj₀ (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  have : Nonempty ι := ⟨p⟩
  choose! α β hαB hβB hαβ hαp hβp hd hrep using hroots
  have hshare : ∀ j ∈ J.erase j₀, ∀ t ∈ J.erase j₀, j ≠ t →
      (α j = α t ∧ β j ≠ β t) ∨ (α j ≠ α t ∧ β j = β t) := by
    intro j hj t ht hjt
    have h := hc.inner_roots hj₀ (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase ht)
      (Finset.ne_of_mem_erase hj) (Finset.ne_of_mem_erase ht) hjt (hrep j hj) (hrep t ht)
    rw [inner_root_root (hαB j hj) (hβB j hj)] at h
    exact share_of_inner_root_eq_one (hαβ j hj) (hαβ t ht) h
  have : Nonempty (J.erase j₀) := ⟨⟨j₁, hj₁⟩⟩
  rcases CFSG.pairwise_shared_pairs_have_common_coordinate (fun i : J.erase j₀ => α i)
      (fun i : J.erase j₀ => β i) (fun i i' hii' =>
        (hshare i i.2 i' i'.2 fun h => hii' (Subtype.ext h)).imp And.left And.right) with
    ⟨A, hA⟩ | ⟨A, hA⟩
  ·
    have hA' : ∀ j ∈ J.erase j₀, α j = A := fun j hj => hA ⟨j, hj⟩
    refine ⟨-1, _, _,
      parityFamily_of_common (j₀ := j₀) (Or.inr rfl) (y := A) (x := β) ?_ ?_ ?_ ?_ ?_⟩
    · rw [← hA' j₁ hj₁]
      exact hαB j₁ hj₁
    · rw [← hA' j₁ hj₁]
      exact hαp j₁ hj₁
    · intro j hj
      refine ⟨hβB j hj, hβp j hj, ?_, ?_⟩
      · rw [← hA' j hj]
        exact Ne.symm (hαβ j hj)
      · rw [← hA' j hj]
        exact (hd j hj).symm
    · intro j hj t ht h
      by_contra hjt
      rcases hshare j hj t ht hjt with ⟨_, h'⟩ | ⟨h', _⟩
      · exact h' h
      · exact h' ((hA' j hj).trans (hA' t ht).symm)
    · intro j hj ψ hψ
      rw [hrep j hj ψ hψ, hA' j hj]
      ring
  ·
    have hA' : ∀ j ∈ J.erase j₀, β j = A := fun j hj => hA ⟨j, hj⟩
    refine ⟨1, _, _,
      parityFamily_of_common (j₀ := j₀) (Or.inl rfl) (y := A) (x := α) ?_ ?_ ?_ ?_ ?_⟩
    · rw [← hA' j₁ hj₁]
      exact hβB j₁ hj₁
    · rw [← hA' j₁ hj₁]
      exact hβp j₁ hj₁
    · intro j hj
      refine ⟨hαB j hj, hαp j hj, ?_, ?_⟩
      · rw [← hA' j hj]
        exact hαβ j hj
      · rw [← hA' j hj]
        exact hd j hj
    · intro j hj t ht h
      by_contra hjt
      rcases hshare j hj t ht hjt with ⟨_, h'⟩ | ⟨h', _⟩
      · exact h' ((hA' j hj).trans (hA' t ht).symm)
      · exact h' h
    · intro j hj ψ hψ
      rw [hrep j hj ψ hψ, hA' j hj]
      ring

end ParityColumns

end CFSG.Wreathed.ConditionalFourier
