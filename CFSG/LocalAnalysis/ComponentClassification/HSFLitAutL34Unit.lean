module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Model

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts Subgroup


@[expose] def CR4 : Subgroup (Equiv.Perm (Fin 42)) := centralizer {r₄} ⊓ R

theorem card_CR4 : Nat.card CR4 = 864 := by
  have h1 := conjClass₄.2
  rw [← ConjAct.orbit_eq_carrier_conjClasses, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer] at h1
  have h2 := card_mul_index (MulAction.stabilizer (ConjAct R) r₄R)
  have hca : Nat.card (ConjAct R) = Nat.card R := Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [h1, ← nat_card_centralizer_nat_card_stabilizer, hca, card_R] at h2
  have h3 : Nat.card (centralizer {r₄R} : Subgroup R) = Nat.card CR4 := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, x.1.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).2⟩, mem_centralizer_singleton_iff.2 ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)
    · exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).1)
  rw [← h3]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 280) (h2.trans (by norm_num))

theorem W_le_CR4 : W ≤ CR4 := fun _ hx =>
  mem_inf.2 ⟨(mem_inf.1 hx).1, TR_le_R (mem_inf.1 hx).2⟩

theorem factorization_864 : (864 : ℕ).factorization 2 = 5 := by
  have h : (864 : ℕ) = 2 ^ 5 * 27 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 27)]
  simp

theorem unitary_facts {X : Subgroup (Equiv.Perm (Fin 42))} (hXR : X ≤ R) (hX : IsPGroup 2 X)
    (hXr : ∀ x ∈ X, x * r₄ = r₄ * x) :
    Nat.card X ≤ 32 ∧
      (∀ E : Subgroup (Equiv.Perm (Fin 42)), E ≤ X → (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 8) ∧
      ∀ y ∈ X, y * y ≠ 1 → ∀ a ∈ X, ∀ b ∈ X, a * y = y * a → b * y = y * b → a * b = b * a := by
  have hXH : X ≤ CR4 := fun x hx => mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (hXr x hx), hXR hx⟩
  obtain ⟨d, -, hd⟩ := exists_conj_mem_of_card W_le_CR4
    (by rw [card_W, card_CR4, factorization_864]; norm_num) hXH hX
  have hinj : ∀ {A : Subgroup (Equiv.Perm (Fin 42))} (x y : A),
      d * (x : Equiv.Perm (Fin 42)) * d⁻¹ = d * y * d⁻¹ → x = y :=
    fun x y h => Subtype.ext (by simpa using h)
  refine ⟨?_, fun E hEX hE2 => ?_, fun y hy hy2 a ha b hb hay hby => ?_⟩
  · rw [← card_W]
    exact Nat.card_le_card_of_injective (fun x : X => (⟨d * x * d⁻¹, hd x x.2⟩ : W))
      fun x y h => hinj x y (congrArg Subtype.val h)
  · refine le_eight_of_lt (hX.to_le hEX) (lt_of_le_of_lt (Nat.card_le_card_of_injective
      (fun e : E => (⟨d * e * d⁻¹, hd e (hEX e.2), by
        rw [show d * e * d⁻¹ * (d * e * d⁻¹) = d * (e * e) * d⁻¹ by group, hE2 e e.2]
        group⟩ : {x // x ∈ W ∧ x * x = 1}))
      fun x y h => hinj x y (congrArg Subtype.val h)) card_sq_W_lt)
  · have hc : ∀ u v : Equiv.Perm (Fin 42), u * v = v * u →
        d * u * d⁻¹ * (d * v * d⁻¹) = d * v * d⁻¹ * (d * u * d⁻¹) := fun u v h => by
      rw [show d * u * d⁻¹ * (d * v * d⁻¹) = d * (u * v) * d⁻¹ by group, h]
      group
    have hy2' : d * y * d⁻¹ * (d * y * d⁻¹) ≠ 1 := by
      rw [show d * y * d⁻¹ * (d * y * d⁻¹) = d * (y * y) * d⁻¹ by group]
      intro h
      apply hy2
      have := congrArg (fun g => d⁻¹ * g * d) h
      simpa [mul_assoc] using this
    have h := comm_of_mem_W (hd y hy) hy2' (hd a ha) (hd b hb) (hc a y hay) (hc b y hby)
    rw [show d * a * d⁻¹ * (d * b * d⁻¹) = d * (a * b) * d⁻¹ by group,
      show d * b * d⁻¹ * (d * a * d⁻¹) = d * (b * a) * d⁻¹ by group] at h
    simpa using h

end CFSG.ComponentClassification.HSFLit.AutL34
