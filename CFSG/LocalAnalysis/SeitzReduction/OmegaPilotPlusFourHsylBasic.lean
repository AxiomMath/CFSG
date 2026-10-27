module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori

public section

namespace CFSG.SeitzReduction.OmegaPilot

open QuadraticMap Module
open CFSG.LieType.Universal.Spin (quadPlus)

section Pair

variable {K : Type*} [Field K] {ι : Type*} {Q : QuadraticForm K (ι → K)}

theorem polar_eq_zero_of_mem_totallySingular {S : Submodule K (ι → K)} (hS : ∀ x ∈ S, Q x = 0)
    {x y : ι → K} (hx : x ∈ S) (hy : y ∈ S) : polar Q x y = 0 := by
  rw [polar, hS _ (S.add_mem hx hy), hS x hx, hS y hy, sub_zero, sub_zero]

theorem polar_eq_zero_of_invariant_pair {S : Submodule K (ι → K)} (hS : ∀ x ∈ S, Q x = 0)
    {u w w' : ι → K} (hu : Q u = 0) (huw : polar Q u w = 0) (huw' : polar Q u w' = 0)
    (hww' : polar Q w w' = 1)
    (h₁ : ∀ x ∈ S, x + polar Q x u • w - polar Q x w • u ∈ S)
    (h₂ : ∀ x ∈ S, x + polar Q x u • w' - polar Q x w' • u ∈ S) {x : ι → K} (hx : x ∈ S) :
    polar Q x u = 0 := by
  have hy : polar Q x u • w - polar Q x w • u ∈ S := by
    have h := S.sub_mem (h₁ x hx) hx
    have he : x + polar Q x u • w - polar Q x w • u - x = polar Q x u • w - polar Q x w • u := by
      abel
    rwa [he] at h
  have hy' : polar Q x u • w' - polar Q x w' • u ∈ S := by
    have h := S.sub_mem (h₂ x hx) hx
    have he : x + polar Q x u • w' - polar Q x w' • u - x =
        polar Q x u • w' - polar Q x w' • u := by
      abel
    rwa [he] at h
  have h0 := polar_eq_zero_of_mem_totallySingular hS hy hy'
  have hwu : polar Q w u = 0 := by rw [polar_comm]; exact huw
  have huu : polar Q u u = 0 := by rw [polar_self, hu, smul_zero]
  rw [polar_sub_left, polar_sub_right, polar_sub_right, polar_smul_left, polar_smul_left,
    polar_smul_left, polar_smul_left, polar_smul_right, polar_smul_right, polar_smul_right,
    polar_smul_right, hww', hwu, huw', huu] at h0
  simp only [smul_eq_mul, mul_zero, mul_one, sub_zero] at h0
  exact mul_self_eq_zero.mp h0

end Pair

section Solid

variable {K : Type} [Field K]

theorem fin_four_eq_of_ne {a b c k : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hak : a ≠ k)
    (hbc : b ≠ c) (hbk : b ≠ k) (hck : c ≠ k) (i : Fin 4) :
    i = a ∨ i = b ∨ i = c ∨ i = k := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases c with ⟨c, hc⟩
  rcases k with ⟨k, hk⟩
  rcases i with ⟨i, hi⟩
  simp only [ne_eq, Fin.mk.injEq] at hab hac hak hbc hbk hck ⊢
  omega

theorem polar_quadPlus_right_single_inl {n : ℕ} (x : Fin n ⊕ Fin n → K) (i : Fin n) :
    polar (quadPlus n K) x (Pi.single (.inl i) 1) = x (.inr i) := by
  rw [polar_comm]
  exact (isHypCoord_quadPlus (K := K) i).polar_left x

theorem polar_quadPlus_right_single_inr {n : ℕ} (x : Fin n ⊕ Fin n → K) (i : Fin n) :
    polar (quadPlus n K) x (Pi.single (.inr i) 1) = x (.inl i) := by
  rw [polar_comm]
  exact (isHypCoord_quadPlus (K := K) i).polar_right x

private theorem polar_eq_zero_of_invariant_coord {n : ℕ} {S : Submodule K (Fin n ⊕ Fin n → K)}
    (hS : ∀ x ∈ S, quadPlus n K x = 0) {u : Fin n ⊕ Fin n → K} {j : Fin n}
    (hu : quadPlus n K u = 0) (huj : u (.inr j) = 0) (huj' : u (.inl j) = 0)
    (h₁ : ∀ x ∈ S, x + polar (quadPlus n K) x u • Pi.single (.inl j) 1 -
      polar (quadPlus n K) x (Pi.single (.inl j) 1) • u ∈ S)
    (h₂ : ∀ x ∈ S, x + polar (quadPlus n K) x u • Pi.single (.inr j) 1 -
      polar (quadPlus n K) x (Pi.single (.inr j) 1) • u ∈ S) {x : Fin n ⊕ Fin n → K}
    (hx : x ∈ S) : polar (quadPlus n K) x u = 0 := by
  refine polar_eq_zero_of_invariant_pair hS hu ?_ ?_ ?_ h₁ h₂ hx
  · rw [polar_quadPlus_right_single_inl, huj]
  · rw [polar_quadPlus_right_single_inr, huj']
  · rw [polar_quadPlus_right_single_inr]
    simp

theorem false_of_invariant_solid_quadPlus {a b c k : Fin 4} (hab : a ≠ b) (hac : a ≠ c)
    (hak : a ≠ k) (hbc : b ≠ c) (hbk : b ≠ k) (hck : c ≠ k)
    {S : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hS4 : finrank K S = 4)
    (hS : ∀ x ∈ S, quadPlus 4 K x = 0)
    (hinv : ∀ u w : Fin 4 ⊕ Fin 4 → K, quadPlus 4 K u = 0 → quadPlus 4 K w = 0 →
      polar (quadPlus 4 K) u w = 0 → u (.inl k) = 0 → u (.inr k) = 0 → u (.inr a) = 0 →
      w (.inl k) = 0 → w (.inr k) = 0 → w (.inr a) = 0 →
      ∀ x ∈ S, x + polar (quadPlus 4 K) x u • w - polar (quadPlus 4 K) x w • u ∈ S) :
    False := by
  classical
  have hE : ∀ i : Fin 4, quadPlus 4 K (Pi.single (.inl i) 1) = 0 := fun i =>
    (isHypCoord_quadPlus (K := K) i).map_left
  have hF : ∀ i : Fin 4, quadPlus 4 K (Pi.single (.inr i) 1) = 0 := fun i =>
    (isHypCoord_quadPlus (K := K) i).map_right
  have hEE : ∀ i j : Fin 4, polar (quadPlus 4 K) (Pi.single (.inl i) 1)
      (Pi.single (.inl j) 1) = 0 := fun i j => by
    rw [polar_quadPlus_right_single_inl]
    simp
  have hFF : ∀ i j : Fin 4, polar (quadPlus 4 K) (Pi.single (.inr i) 1)
      (Pi.single (.inr j) 1) = 0 := fun i j => by
    rw [polar_quadPlus_right_single_inr]
    simp
  have hEF : ∀ i j : Fin 4, i ≠ j → polar (quadPlus 4 K) (Pi.single (.inl i) 1)
      (Pi.single (.inr j) 1) = 0 := fun i j hij => by
    rw [polar_quadPlus_right_single_inr]
    simp [hij]
  have hFE : ∀ i j : Fin 4, i ≠ j → polar (quadPlus 4 K) (Pi.single (.inr i) 1)
      (Pi.single (.inl j) 1) = 0 := fun i j hij => by
    rw [polar_quadPlus_right_single_inl]
    simp [hij]
  have hinvE : ∀ i j : Fin 4, i ≠ k → j ≠ k → ∀ (s t : Bool),
      (s = false → i ≠ a) → (t = false → j ≠ a) →
      polar (quadPlus 4 K) (if s then Pi.single (.inl i) 1 else Pi.single (.inr i) 1)
        (if t then Pi.single (.inl j) 1 else Pi.single (.inr j) 1) = 0 →
      ∀ x ∈ S, x + polar (quadPlus 4 K) x
          (if s then Pi.single (.inl i) 1 else Pi.single (.inr i) 1) •
          (if t then Pi.single (.inl j) 1 else Pi.single (.inr j) 1) -
        polar (quadPlus 4 K) x (if t then Pi.single (.inl j) 1 else Pi.single (.inr j) 1) •
          (if s then Pi.single (.inl i) 1 else Pi.single (.inr i) 1) ∈ S := by
    intro i j hik hjk s t hs ht hp
    refine hinv _ _ ?_ ?_ hp ?_ ?_ ?_ ?_ ?_ ?_
    · cases s <;> simp [hE, hF]
    · cases t <;> simp [hE, hF]
    · cases s <;> simp [hik]
    · cases s <;> simp [hik]
    · cases s
      · simp [hs rfl]
      · simp
    · cases t <;> simp [hjk]
    · cases t <;> simp [hjk]
    · cases t
      · simp [ht rfl]
      · simp
  have hxfb : ∀ x ∈ S, x (.inr b) = 0 := fun x hx => by
    rw [← polar_quadPlus_right_single_inl x b]
    refine polar_eq_zero_of_invariant_coord hS (hE b) (j := c) (by simp) (by simp [hbc]) ?_ ?_ hx
    · exact hinvE b c hbk hck true true (by simp) (by simp) (hEE b c)
    · exact hinvE b c hbk hck true false (by simp) (fun _ => hac.symm) (hEF b c hbc)
  have hxeb : ∀ x ∈ S, x (.inl b) = 0 := fun x hx => by
    rw [← polar_quadPlus_right_single_inr x b]
    refine polar_eq_zero_of_invariant_coord hS (hF b) (j := c) (by simp [hbc]) (by simp) ?_ ?_ hx
    · exact hinvE b c hbk hck false true (fun _ => hab.symm) (by simp) (hFE b c hbc)
    · exact hinvE b c hbk hck false false (fun _ => hab.symm) (fun _ => hac.symm) (hFF b c)
  have hxfc : ∀ x ∈ S, x (.inr c) = 0 := fun x hx => by
    rw [← polar_quadPlus_right_single_inl x c]
    refine polar_eq_zero_of_invariant_coord hS (hE c) (j := b) (by simp) (by simp [hbc.symm])
      ?_ ?_ hx
    · exact hinvE c b hck hbk true true (by simp) (by simp) (hEE c b)
    · exact hinvE c b hck hbk true false (by simp) (fun _ => hab.symm) (hEF c b hbc.symm)
  have hxec : ∀ x ∈ S, x (.inl c) = 0 := fun x hx => by
    rw [← polar_quadPlus_right_single_inr x c]
    refine polar_eq_zero_of_invariant_coord hS (hF c) (j := b) (by simp [hbc.symm]) (by simp)
      ?_ ?_ hx
    · exact hinvE c b hck hbk false true (fun _ => hac.symm) (by simp) (hFE c b hbc.symm)
    · exact hinvE c b hck hbk false false (fun _ => hac.symm) (fun _ => hab.symm) (hFF c b)
  have hxfa : ∀ x ∈ S, x (.inr a) = 0 := fun x hx => by
    rw [← polar_quadPlus_right_single_inl x a]
    refine polar_eq_zero_of_invariant_coord hS (hE a) (j := b) (by simp) (by simp [hab]) ?_ ?_ hx
    · exact hinvE a b hak hbk true true (by simp) (by simp) (hEE a b)
    · exact hinvE a b hak hbk true false (by simp) (fun _ => hab.symm) (hEF a b hab)
  have hle : S ≤ Submodule.span K ((({(Pi.single (Sum.inl a) 1 : Fin 4 ⊕ Fin 4 → K),
      (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K),
      (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K)} : Finset (Fin 4 ⊕ Fin 4 → K))) :
        Set (Fin 4 ⊕ Fin 4 → K)) := by
    intro x hx
    have hxe : x = x (.inl a) • Pi.single (.inl a) 1 + x (.inl k) • Pi.single (.inl k) 1 +
        x (.inr k) • Pi.single (.inr k) 1 := by
      funext j
      rcases j with i | i
      · rcases fin_four_eq_of_ne hab hac hak hbc hbk hck i with rfl | rfl | rfl | rfl
        · simp [hak]
        · simp [hab.symm, hbk, hxeb x hx]
        · simp [hac.symm, hck, hxec x hx]
        · simp [hak.symm]
      · rcases fin_four_eq_of_ne hab hac hak hbc hbk hck i with rfl | rfl | rfl | rfl
        · simp [hak, hxfa x hx]
        · simp [hbk, hxfb x hx]
        · simp [hck, hxfc x hx]
        · simp
    rw [hxe]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have h3 := (Submodule.finrank_mono hle).trans (finrank_span_finset_le_card _)
  have h3' := h3.trans Finset.card_le_three
  omega

end Solid

end CFSG.SeitzReduction.OmegaPilot
