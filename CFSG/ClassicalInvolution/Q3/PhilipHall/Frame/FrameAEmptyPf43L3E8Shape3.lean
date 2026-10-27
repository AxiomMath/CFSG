module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Shape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace FaithfulL3E8

variable {X : Type} [Group X] {E : Subgroup X}

theorem eq_bot_of_le_normalizer (h : FaithfulL3E8 X E) {P D : Subgroup X}
    (hP : Nonempty (↥P ≃* QuaternionGroup 2)) (hD : Odd (Nat.card D))
    (hPD : P ≤ Subgroup.normalizer (D : Set X)) : D = ⊥ := by
  haveI := h.normal
  obtain ⟨e⟩ := h.quotient
  haveI : Finite D := Nat.finite_of_card_ne_zero hD.pos.ne'
  let f : X →* L3Two := e.toMonoidHom.comp (QuotientGroup.mk' E)
  have hf : ∀ x : X, f x = 1 ↔ x ∈ E := fun x => by
    show e (QuotientGroup.mk' E x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by simpa [sq] using h.elemAbelian.2 x hx
  obtain ⟨a, b, z, haP, hbP, hzP, haa, hbb, hcc, hbab, hz1⟩ : ∃ a b z : X, a ∈ P ∧ b ∈ P ∧
      z ∈ P ∧ a * a = z ∧ b * b = z ∧ a * b * (a * b) = z ∧ b * a * b⁻¹ = a⁻¹ ∧ z ≠ 1 := by
    obtain ⟨φ⟩ := hP
    let ψ : QuaternionGroup 2 →* X := P.subtype.comp φ.symm.toMonoidHom
    have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.symm.injective
    refine ⟨ψ (QuaternionGroup.a 1), ψ (QuaternionGroup.xa 0), ψ (QuaternionGroup.a 2),
      (φ.symm (QuaternionGroup.a 1)).2, (φ.symm (QuaternionGroup.xa 0)).2,
      (φ.symm (QuaternionGroup.a 2)).2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [map_mul] using congrArg ψ
        (show QuaternionGroup.a 1 * QuaternionGroup.a 1 = (QuaternionGroup.a 2 : QuaternionGroup 2)
          by decide)
    · simpa only [map_mul] using congrArg ψ
        (show QuaternionGroup.xa 0 * QuaternionGroup.xa 0 =
          (QuaternionGroup.a 2 : QuaternionGroup 2) by decide)
    · simpa only [map_mul] using congrArg ψ
        (show QuaternionGroup.a 1 * QuaternionGroup.xa 0 *
            (QuaternionGroup.a 1 * QuaternionGroup.xa 0) =
          (QuaternionGroup.a 2 : QuaternionGroup 2) by decide)
    · simpa only [map_mul, map_inv] using congrArg ψ
        (show QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
          ((QuaternionGroup.a 1)⁻¹ : QuaternionGroup 2) by decide)
    · intro h1
      have h2 : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 :=
        hψinj (h1.trans (map_one ψ).symm)
      exact absurd h2 (by decide)
  have hzE : z ∈ E := by
    by_contra hzE
    refine l3Two_no_q8 (f a) (f b) ?_ ?_ ?_
    · rw [← map_mul, ← map_mul, haa, hbb]
    · rw [← map_mul, haa]
      exact fun h1 => hzE ((hf z).1 h1)
    · simpa only [map_mul, map_inv] using congrArg f hbab
  have hodd : ∀ d ∈ D, ∀ k : ℕ, d ^ (2 ^ k) = 1 → d = 1 := fun d hd k hk =>
    orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow
      (Odd.of_dvd_nat hD (Subgroup.orderOf_dvd_natCard D hd)) (orderOf_dvd_of_pow_eq_one hk))
  have hfpf : ∀ c : X, c * c = z → ∀ d ∈ D, c * d = d * c → d = 1 := by
    intro c hc d hd hcd
    have hcE : c ∉ E := fun hcE => hz1 (by rw [← hc]; exact hEsq c hcE)
    have h4 : f d ^ 4 = 1 := l3Two_centralizer_exp (f c) (f d)
      (by rw [← map_mul, hc]; exact (hf z).2 hzE) (fun h1 => hcE ((hf c).1 h1))
      (by rw [← map_mul, ← map_mul, hcd])
    have h4E : d ^ 4 ∈ E := (hf _).1 (by rw [map_pow, h4])
    refine hodd d hd 3 ?_
    rw [show (2 : ℕ) ^ 3 = 4 + 4 by norm_num, pow_add]
    exact hEsq _ h4E
  have hzD : ∀ d ∈ D, z * d * z⁻¹ = d := by
    intro d hd
    have h1 : z * d * z⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hPD hzP) d).mp hd
    have h2 : z * d * z⁻¹ * d⁻¹ ∈ D := D.mul_mem h1 (D.inv_mem hd)
    have h3 : z * d * z⁻¹ * d⁻¹ ∈ E := by
      have : z * d * z⁻¹ * d⁻¹ = z * (d * z⁻¹ * d⁻¹) := by group
      rw [this]
      exact E.mul_mem hzE (‹E.Normal›.conj_mem _ (E.inv_mem hzE) d)
    have h4 : z * d * z⁻¹ * d⁻¹ = 1 :=
      hodd _ h2 1 (by rw [pow_one, sq]; exact hEsq _ h3)
    exact mul_inv_eq_one.mp h4
  have hinv : ∀ c ∈ P, c * c = z → ∀ d ∈ D, c * d * c⁻¹ = d⁻¹ := by
    intro c hcP hc
    have hcN := hPD hcP
    let σ : D →* D := MonoidHom.mk'
      (fun d => ⟨c * d * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN d).mp d.2⟩)
      (fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group))
    have hσ : ∀ d : D, (σ d : X) = c * d * c⁻¹ := fun d => rfl
    have hfix : MonoidHom.FixedPointFree σ := by
      intro d hd
      have h1 : c * (d : X) * c⁻¹ = d := by rw [← hσ, hd]
      have h2 : c * (d : X) = d * c := by
        calc c * (d : X) = c * d * c⁻¹ * c := by group
          _ = d * c := by rw [h1]
      exact Subtype.ext (hfpf c hc d d.2 h2)
    have hinvol : Function.Involutive σ := by
      intro d
      apply Subtype.ext
      rw [hσ, hσ]
      calc c * (c * (d : X) * c⁻¹) * c⁻¹ = (c * c) * d * (c * c)⁻¹ := by group
        _ = d := by rw [hc]; exact hzD d d.2
    intro d hd
    exact congrArg Subtype.val (congrFun (hfix.coe_eq_inv_of_involutive hinvol) ⟨d, hd⟩)
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  refine hfpf (a * b) hcc d hd ?_
  have h1 := hinv a haP haa
  have h2 := hinv b hbP hbb
  calc a * b * d = a * (b * d * b⁻¹) * a⁻¹ * (a * b) := by group
    _ = a * d⁻¹ * a⁻¹ * (a * b) := by rw [h2 d hd]
    _ = d⁻¹⁻¹ * (a * b) := by rw [h1 _ (D.inv_mem hd)]
    _ = d * (a * b) := by rw [inv_inv]

end FaithfulL3E8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
