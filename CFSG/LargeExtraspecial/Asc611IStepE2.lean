module

public import CFSG.LargeExtraspecial.Asc611IStepE1
public import CFSG.LargeExtraspecial.Asc611IChain

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m} {U : Subgroup (PG m)}

theorem herm_invN_congr_left (he : e * e = 1) {x z : Fin m → K} (hxz : invN e x = invN e z)
    (y : Fin m → K) : herm frob x (invN e y) = herm frob z (invN e y) := by
  rw [herm_invN_swap he y x, hxz, ← herm_invN_swap he y z]

theorem exists_frame_two (he : e * e = 1) {z₀ z₁ : Fin m → K}
    (h0 : herm frob z₀ (invN e z₀) = 1) (h1 : herm frob z₁ (invN e z₁) = 1)
    (h01 : herm frob z₀ (invN e z₁) = 0) :
    ∃ q₀ q₁ : Fin m → K, invN e q₀ = invN e z₀ ∧ invN e q₁ = invN e z₁ ∧
      IsFrame e ![q₀, q₁] := by
  have F0 : IsFrame e (Fin.elim0 : Fin 0 → Fin m → K) :=
    ⟨fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨q₀, hN0, hi0, -⟩ := exists_frame_ext he F0 h0 (fun i => i.elim0)
  have hH : ∀ {x z : Fin m → K}, invN e x = invN e z → ∀ y,
      herm frob x (invN e y) = herm frob z (invN e y) := fun hxz y =>
    herm_invN_congr_left he hxz y
  have hq0 : herm frob q₀ (invN e q₀) = 1 := by rw [hN0, hH hN0, h0]
  have F1 : IsFrame e ![q₀] :=
    ⟨fun i j => by fin_cases i; fin_cases j; exact hq0,
      fun i j => by fin_cases i; fin_cases j; exact hi0⟩
  have hq0z1 : herm frob q₀ (invN e z₁) = 0 := by rw [hH hN0, h01]
  obtain ⟨q₁, hN1, hi1, hq01⟩ := exists_frame_ext he F1 h1 (fun i => by
    fin_cases i; exact hq0z1)
  refine ⟨q₀, q₁, hN0, hN1, isFrame_two he hq0 ?_ ?_ hi0 hi1 (hq01 0)⟩
  · rw [hN1, hH hN1, h1]
  · rw [hN1, hq0z1]

theorem exists_unit_or_maximal (he : e * e = 1) {r : ℕ} (q : Fin r → Fin m → K) :
    (∃ z, (∀ i, herm frob (q i) (invN e z) = 0) ∧ herm frob z (invN e z) = 1) ∨
      ∀ z, (∀ i, herm frob (q i) (invN e z) = 0) → herm frob z (invN e z) = 0 := by
  by_cases h : ∃ z, (∀ i, herm frob (q i) (invN e z) = 0) ∧ herm frob z (invN e z) = 1
  · exact Or.inl h
  · right
    intro z hz
    rcases herm_invN_self he z with h0 | h1
    · exact h0
    · exact absurd ⟨z, hz, h1⟩ h

theorem exists_snoc (he : e * e = 1) {r : ℕ} {q : Fin r → Fin m → K} (F : IsFrame e q)
    {z : Fin m → K} (hqz : ∀ i, herm frob (q i) (invN e z) = 0)
    (hz : herm frob z (invN e z) = 1) :
    ∃ z' : Fin m → K, IsFrame e (Fin.snoc q z' : Fin (r + 1) → Fin m → K) := by
  obtain ⟨z', hN, hi, hqz'⟩ := exists_frame_ext he F hz hqz
  refine ⟨z', F.snoc he ?_ (fun i => by rw [hN, hqz]) hi hqz'⟩
  rw [hN, herm_invN_congr_left he hN, hz]

theorem false_of_frame2 (S : Setup e U) {q₀ q₁ : Fin m → K} (F2 : IsFrame e ![q₀, q₁])
    {u₀ : SUid frob m} (hu₀ : (QuotientGroup.mk u₀ : PG m) ∈ U)
    (Mf : ∀ r, Matrix (Fin r) (Fin r) F4)
    (hpad : ∀ r, 2 ≤ r → (∀ i j : Fin r, ((Mf (r + 1)).map eF4) (Fin.castSucc i)
      (Fin.castSucc j) = ((Mf r).map eF4) i j) ∧
      (∀ j, ((Mf (r + 1)).map eF4) (Fin.last r) j = 0) ∧
      ∀ i, ((Mf (r + 1)).map eF4) i (Fin.last r) = 0)
    (hact : ActsBy e ![q₀, q₁] ((Mf 2).map eF4) u₀)
    (h2 : (∀ z, (∀ i, herm frob (![q₀, q₁] i) (invN e z) = 0) →
      herm frob z (invN e z) = 0) → False)
    (h3 : ∀ q : Fin 3 → Fin m → K, IsFrame e q →
      (∀ z, (∀ i, herm frob (q i) (invN e z) = 0) → herm frob z (invN e z) = 0) →
      ActsBy e q ((Mf 3).map eF4) u₀ → False)
    (h4 : ∃ c₁ c₂ c₃ d : Fin 4 → F4, (∑ i, c₁ i ^ 2 * c₁ i = 0) ∧
      (∑ i, c₂ i ^ 2 * c₂ i = 0) ∧ (∑ i, c₃ i ^ 2 * c₃ i = 0) ∧
      stepF (stepF (Mf 4) c₁ + stepF (Mf 4) c₂) c₃ = rk1F d ∧ d ≠ 0) : False := by
  have he := S.invol
  rcases exists_unit_or_maximal he ![q₀, q₁] with ⟨z, hqz, hz⟩ | hno
  · obtain ⟨z₂, F3⟩ := exists_snoc he F2 hqz hz
    obtain ⟨p1, p2, p3⟩ := hpad 2 le_rfl
    have hact3 : ActsBy e (Fin.snoc ![q₀, q₁] z₂ : Fin 3 → Fin m → K) ((Mf 3).map eF4) u₀ :=
      fun x => by rw [hact x, frameMap_snoc p1 p2 p3]
    rcases exists_unit_or_maximal he (Fin.snoc ![q₀, q₁] z₂ : Fin 3 → Fin m → K) with
      ⟨z, hqz, hz⟩ | hno3
    · obtain ⟨z₃, F4'⟩ := exists_snoc he F3 hqz hz
      obtain ⟨p1', p2', p3'⟩ := hpad 3 (by norm_num)
      have hact4 : ActsBy e (Fin.snoc (Fin.snoc ![q₀, q₁] z₂ : Fin 3 → Fin m → K) z₃ :
          Fin 4 → Fin m → K) ((Mf 4).map eF4) u₀ :=
        fun x => by rw [hact3 x, frameMap_snoc p1' p2' p3']
      obtain ⟨c₁, c₂, c₃, d, n₁, n₂, n₃, hch, hd⟩ := h4
      exact false_of_chain3 S F4' hu₀ hact4 n₁ n₂ n₃ hch hd
    · exact h3 _ F3 hno3 hact3
  · exact h2 hno

end CFSG.LargeExtraspecial.Asc611I
