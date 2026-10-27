module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute
  eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)

variable {G : Type*} [Group G] [Finite G]

theorem exists_root_factor_five {W₀ A : Subgroup G} {t u y : G} (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hW₀ : W₀ ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hW₀2 : ∀ w ∈ W₀, w * w = 1)
    (hW₀c : Nat.card W₀ = 16) (htW₀ : t ∈ normalizer (W₀ : Set G))
    (hV₀ : Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 4)
    (hyA : y ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hyW₀ : y ∈ normalizer (W₀ : Set G))
    (hy0 : W₀ ⊓ centralizer ({y} : Set G) = ⊥) (hA16 : ¬ 16 ∣ Nat.card A)
    (huA : u ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hut : u * t = t * u)
    (huW₀ : u ∈ normalizer (W₀ : Set G)) (huC : u ∉ centralizer (W₀ : Set G))
    (hu2 : u * u = 1) :
    W₀ ⊓ A ≠ ⊥ ∧ ∃ x ∈ A, u = x * (t * x * t⁻¹) ∧ x * x = 1 ∧
      x ∈ normalizer (W₀ : Set G) ∧ x ∉ centralizer ((W₀ ⊓ A : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' : Subgroup G := A.map (MulAut.conj t).toMonoidHom with hA'
  obtain ⟨hE4, hEE⟩ :=
    sup_inf_eq_of_card_sixteen ht hinf hc hW₀ hW₀2 hW₀c htW₀ hV₀ hyA hyW₀ hy0 hA16
  set E : Subgroup G := W₀ ⊓ A with hE
  set E' : Subgroup G := W₀ ⊓ A' with hE'
  have hEE' : E.map (MulAut.conj t).toMonoidHom = E' := map_conj_inf_eq ht htW₀
  have hE'E : E'.map (MulAut.conj t).toMonoidHom = E := by
    rw [← hEE', map_conj_map_conj_of_mul_self ht]
  have hcEE : ∀ a ∈ E, ∀ b ∈ E', a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have htt : ∀ z : G, t * (t * z * t⁻¹) * t⁻¹ = z := conj_conj_of_mul_self ht
  have htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E' := fun e he => hEE' ▸ ⟨e, he, rfl⟩
  have htE' : ∀ e ∈ E', t * e * t⁻¹ ∈ E := fun e he => hE'E ▸ ⟨e, he, rfl⟩
  obtain ⟨x, hxA, hux⟩ := exists_eq_mul_conj_of_mem_sup ht hinf hc huA hut
  set x' : G := t * x * t⁻¹ with hx'
  have hx'A' : x' ∈ A' := (mem_map_conj_iff_of_mul_self ht).2 (by rw [htt]; exact hxA)
  have hxx' : x * x' = x' * x := hc x hxA x' hx'A'
  have hx2 : x * x = 1 := by
    have h1 : (x * x) * (x' * x') = 1 := by
      rw [← hu2, hux]
      calc x * x * (x' * x') = x * (x * x') * x' := by group
        _ = x * (x' * x) * x' := by rw [hxx']
        _ = x * x' * (x * x') := by group
    have h2 : x * x ∈ A' := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact A'.inv_mem (A'.mul_mem hx'A' hx'A')
    have h3 : x * x ∈ A ⊓ A' := Subgroup.mem_inf.2 ⟨A.mul_mem hxA hxA, h2⟩
    rwa [hinf, Subgroup.mem_bot] at h3
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hx'2 : x' * x' = 1 := by
    rw [hx', show t * x * t⁻¹ * (t * x * t⁻¹) = t * (x * x) * t⁻¹ by group, hx2, mul_one,
      mul_inv_cancel]
  have hcA' : ∀ b ∈ A', ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have huNA : u ∈ normalizer (A : Set G) := sup_le_normalizer_of_commute hc huA
  have huNA' : u ∈ normalizer (A' : Set G) :=
    sup_le_normalizer_of_commute hcA' (by rw [sup_comm]; exact huA)
  have huE : ∀ e ∈ E, u * e * u⁻¹ ∈ E := fun e he => Subgroup.mem_inf.2
    ⟨(mem_normalizer_iff.1 huW₀ e).1 he.1, (mem_normalizer_iff.1 huNA e).1 he.2⟩
  have huE' : ∀ e ∈ E', u * e * u⁻¹ ∈ E' := fun e he => Subgroup.mem_inf.2
    ⟨(mem_normalizer_iff.1 huW₀ e).1 he.1, (mem_normalizer_iff.1 huNA' e).1 he.2⟩
  have hu2' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huNE : u ∈ normalizer (E : Set G) := mem_normalizer_of_mul_self_of_conj_mem hu2 huE
  have huNE' : u ∈ normalizer (E' : Set G) := mem_normalizer_of_mul_self_of_conj_mem hu2 huE'
  have hxE : ∀ e ∈ E, x * e * x⁻¹ = u * e * u⁻¹ := by
    intro e he
    have h1 : e * x' = x' * e := hc e he.2 x' hx'A'
    rw [hux]
    calc x * e * x⁻¹ = x * (e * x') * x'⁻¹ * x⁻¹ := by group
      _ = x * (x' * e) * x'⁻¹ * x⁻¹ := by rw [h1]
      _ = x * x' * e * (x * x')⁻¹ := by group
  have hxE' : ∀ e ∈ E', x * e * x⁻¹ = e := by
    intro e he
    rw [hc x hxA e he.2, mul_inv_cancel_right]
  have hxNE : x ∈ normalizer (E : Set G) :=
    mem_normalizer_of_mul_self_of_conj_mem hx2 fun e he => (hxE e he) ▸ huE e he
  have hxNE' : x ∈ normalizer (E' : Set G) :=
    mem_normalizer_of_mul_self_of_conj_mem hx2 fun e he => (hxE' e he).symm ▸ he
  have hxNW₀ : x ∈ normalizer (W₀ : Set G) := by
    refine mem_normalizer_of_mul_self_of_conj_mem hx2 fun w hw => ?_
    rw [← hEE] at hw ⊢
    obtain ⟨e, he, e', he', rfl⟩ := exists_mul_of_mem_sup_of_commute hcEE hw
    rw [show x * (e * e') * x⁻¹ = (x * e * x⁻¹) * (x * e' * x⁻¹) by group, hxE' e' he']
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hxNE e).1 he)) (mem_sup_right he')
  have hxCE : x ∉ centralizer (E : Set G) := by
    intro hxC
    apply huC
    have huCE : ∀ e ∈ E, u * e * u⁻¹ = e := by
      intro e he
      rw [← hxE e he, ← (mem_centralizer_iff.1 hxC) e he, mul_inv_cancel_right]
    have huCE' : ∀ e ∈ E', u * e * u⁻¹ = e := by
      intro e he
      have h1 := huCE _ (htE' e he)
      calc u * e * u⁻¹ = (u * t) * (t * e * t⁻¹) * (u * t)⁻¹ := by
            rw [show (u * t) * (t * e * t⁻¹) * (u * t)⁻¹ =
              u * (t * (t * e * t⁻¹) * t⁻¹) * u⁻¹ by group, htt]
        _ = (t * u) * (t * e * t⁻¹) * (t * u)⁻¹ := by rw [hut]
        _ = t * (u * (t * e * t⁻¹) * u⁻¹) * t⁻¹ := by group
        _ = e := by rw [h1, htt]
    rw [mem_centralizer_iff]
    intro w hw
    rw [← hEE] at hw
    obtain ⟨e, he, e', he', rfl⟩ := exists_mul_of_mem_sup_of_commute hcEE hw
    have h1 : u * (e * e') * u⁻¹ = e * e' := by
      rw [show u * (e * e') * u⁻¹ = (u * e * u⁻¹) * (u * e' * u⁻¹) by group, huCE e he,
        huCE' e' he']
    calc e * e' * u = u * (e * e') * u⁻¹ * u := by rw [h1]
      _ = u * (e * e') := by group
  refine ⟨fun h => ?_, x, hxA, hux, hx2, hxNW₀, hxCE⟩
  have h1 : Nat.card E = 1 := by rw [h, Subgroup.card_bot]
  omega

theorem swapData_five {W₀ A : Subgroup G} {t u y : G} (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hW₀ : W₀ ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hW₀2 : ∀ w ∈ W₀, w * w = 1)
    (hW₀c : Nat.card W₀ = 16) (htW₀ : t ∈ normalizer (W₀ : Set G))
    (hV₀ : Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 4)
    (hyA : y ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hyW₀ : y ∈ normalizer (W₀ : Set G))
    (hy0 : W₀ ⊓ centralizer ({y} : Set G) = ⊥) (hA16 : ¬ 16 ∣ Nat.card A)
    (huA : u ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hut : u * t = t * u)
    (huW₀ : u ∈ normalizer (W₀ : Set G)) (huC : u ∉ centralizer (W₀ : Set G))
    (hu2 : u * u = 1) :
    ∃ X : Subgroup G, W₀ ⊓ A ≠ ⊥ ∧
      zpowers u ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom ∧
      zpowers u ≤ normalizer (W₀ : Set G) ∧ IsPGroup 2 X ∧ X ≤ A ∧
      X ≤ normalizer (W₀ : Set G) ∧ X ⊓ centralizer ((W₀ ⊓ A : Subgroup G) : Set G) = ⊥ ∧
      4 < 2 * Nat.card X ^ 2 := by
  obtain ⟨hE1, x, hxA, -, hx2, hxN, hxC⟩ := exists_root_factor_five ht hinf hc hW₀ hW₀2 hW₀c
    htW₀ hV₀ hyA hyW₀ hy0 hA16 huA hut huW₀ huC hu2
  have hx1 : x ≠ 1 := fun h => hxC (h ▸ one_mem _)
  have hox : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  refine ⟨zpowers x, hE1, (zpowers_le).2 huA, (zpowers_le).2 huW₀,
    isPGroup_zpowers_of_mul_self_eq_one hx2, (zpowers_le).2 hxA, (zpowers_le).2 hxN, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzx, hzC⟩ := Subgroup.mem_inf.1 hz
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hox hzx with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hzC) hxC
  · rw [Nat.card_zpowers, hox]
    norm_num

end CFSG.SeitzReduction.LinearPilot
