module

public import CFSG.GH74.Generic.S1.Exo.ExoticFixed
public import CFSG.GH74.Generic.S1.ExoticGlue

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup

variable {K : Type} [Group K]

@[expose] def IsExoticAutAt (q : ℕ) (α : MulAut K) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSL 4 F), Nat.card F = q ∧ q % 4 = 3 ∧
      IsExoticLin (StatedSL 4 F) (MulAut.congr e α)) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSU 4 q F), Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧
      IsExoticUni (StatedSU 4 q F) q (MulAut.congr e α))

theorem IsExoticAut.exists_at {α : MulAut K} (h : IsExoticAut α) : ∃ q : ℕ, IsExoticAutAt q α := by
  rcases h with ⟨F, _, _, e, hF, hβ⟩ | ⟨q, F, _, _, e, hF, hq, hβ⟩
  · exact ⟨Nat.card F, Or.inl ⟨F, inferInstance, inferInstance, e, rfl, hF, hβ⟩⟩
  · exact ⟨q, Or.inr ⟨F, inferInstance, inferInstance, e, hF, hq, hβ⟩⟩

theorem IsExoticAutAt.odd {q : ℕ} {α : MulAut K} (h : IsExoticAutAt q α) : Odd q := by
  rcases h with ⟨F, _, _, e, hF, h3, hβ⟩ | ⟨F, _, _, e, hF, hq, hβ⟩
  · exact Nat.odd_iff.2 (by omega)
  · exact Nat.odd_iff.2 (by omega)

theorem IsExoticAutAt.conj_mul {q : ℕ} {α : MulAut K} (h : IsExoticAutAt q α) {w : K} (hw2 : w * w = 1)
    (hwf : α w = w) : IsExoticAutAt q (MulAut.conj w * α) := by
  rcases h with ⟨F, _, _, e, hF, h3, hβ⟩ | ⟨F, _, _, e, hF, hq, hβ⟩
  · refine Or.inl ⟨F, inferInstance, inferInstance, e, hF, h3, ?_⟩
    rw [congr_conj_mul]
    refine IsExoticLin.conj_mul hβ (w := e w) (by rw [← map_mul, hw2, map_one]) ?_
    simp [MulAut.congr_apply, hwf]
  · refine Or.inr ⟨F, inferInstance, inferInstance, e, hF, hq, ?_⟩
    rw [congr_conj_mul]
    refine IsExoticUni.conj_mul hF hq hβ (w := e w) (by rw [← map_mul, hw2, map_one]) ?_
    simp [MulAut.congr_apply, hwf]

theorem IsExoticAutAt.exoticFixedGroup {q : ℕ} {α : MulAut K} (h : IsExoticAutAt q α) {z : K}
    (hz : z ∈ Subgroup.center K) (hz1 : z ≠ 1) : ExoticFixedGroup α z q := by
  rcases h with ⟨F, _, _, e, hF, h3, hβ⟩ | ⟨F, _, _, e, hF, hq, hβ⟩
  · refine ExoticFixedGroup.of_congr e ?_
    have hc := (mem_center_iff_of_mulEquiv e z).2 hz
    have hneg : ((e z : ↥(StatedSL 4 F)) : GL (Fin 4) F) = -1 := by
      rcases (mem_center_statedSL_four_iff (by omega) _).1 hc with h | h
      · exfalso
        apply hz1
        apply e.injective
        rw [map_one]
        exact Subtype.ext h
      · rw [h, xGL_eq_neg_one]
    have := exoticFixedGroup_lin (by omega) hβ (e z) hneg
    rwa [hF] at this
  · refine ExoticFixedGroup.of_congr e ?_
    have hc := (mem_center_iff_of_mulEquiv e z).2 hz
    have hneg : ((e z : ↥(StatedSU 4 q F)) : GL (Fin 4) F) = -1 := by
      obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
      rcases (mem_center_statedSU_four_iff hF hq _).1 hc with h | h
      · exfalso
        apply hz1
        apply e.injective
        rw [map_one]
        exact Subtype.ext h
      · rw [h, xGL_eq_neg_one]
    exact exoticFixedGroup_uni hF hq hβ (e z) hneg

section Full

variable {Γ : Type} [Group Γ]

theorem ExoticFixedGroup.exists_involution_full {β : MulAut Γ} {z : Γ} {q : ℕ}
    (h : ExoticFixedGroup β z q) (hq : Odd q) (hq1 : 1 < q) :
    ∃ Ω : Subgroup Γ, (∀ k ∈ Ω, β k = k) ∧ IsSimpleGroup ↥Ω ∧ Group.IsPerfect ↥Ω ∧ z ∉ Ω ∧
      (∀ k : Γ, β k = k → k ∈ Ω ∨ z * k ∈ Ω) ∧ ∃ w ∈ Ω, w * w = 1 ∧ w ≠ 1 := by
  obtain ⟨Ω, hfix, hs, hp, hc, -, -, hzΩ, hall⟩ := h
  refine ⟨Ω, hfix, hs, hp, hzΩ, hall, ?_⟩
  have hne : Nat.card ↥Ω ≠ 0 := natCard_pos_aux hq1 hc
  have : Finite ↥Ω := Nat.finite_of_card_ne_zero hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥Ω := by
    have h4 : 4 ∣ Nat.card ↥Ω * 2 := by
      rw [hc]
      exact Dvd.dvd.mul_left (Dvd.dvd.trans (by norm_num : 4 ∣ 16) (sixteen_dvd_pow_four_sub_one hq)) _
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ω) 2 h2
  refine ⟨(x : Γ), x.2, ?_, ?_⟩
  · have : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
    exact congrArg Subtype.val this
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

end Full

end CFSG.GH74.Generic.S1.Exo
