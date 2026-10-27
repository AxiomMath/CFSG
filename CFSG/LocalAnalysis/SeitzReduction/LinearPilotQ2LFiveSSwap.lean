module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSAbs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute
  card_sup_of_commute eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)

variable {G : Type*} [Group G]

section Helpers

theorem factor_eq_of_mul_eq_mul_sOne {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (h : a₁ * b₁ = a₂ * b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
    calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
      _ = b₂ * b₁⁻¹ := by group
  have hmem : a₂⁻¹ * a₁ ∈ A ⊓ B :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₂) ha₁, h1 ▸ mul_mem hb₂ (inv_mem hb₁)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  have ha : a₁ = a₂ := by
    calc a₁ = a₂ * (a₂⁻¹ * a₁) := by group
      _ = a₂ := by rw [hmem, mul_one]
  refine ⟨ha, ?_⟩
  rw [ha] at h
  exact mul_left_cancel h

theorem mem_map_conj_iff_of_mul_self {t : G} (ht : t * t = 1) {A : Subgroup G} {b : G} :
    b ∈ A.map (MulAut.conj t).toMonoidHom ↔ t * b * t⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [conj_conj_of_mul_self ht]
  · intro h
    refine ⟨t * b * t⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_conj_of_mul_self ht b

theorem mem_normalizer_centralizer_sOne {W : Subgroup G} {g : G}
    (hg : g ∈ normalizer (W : Set G)) : g ∈ normalizer (centralizer (W : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : g⁻¹ * w * g ∈ W := by
      have h1 := (mem_normalizer_iff.1 hg (g⁻¹ * w * g)).2
      apply h1
      rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
    have h2 := hc _ hw'
    calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * w := by group
  · intro hc
    rw [mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : g * w * g⁻¹ ∈ W := (mem_normalizer_iff.1 hg w).1 hw
    have h2 := hc _ hw'
    calc w * c = g⁻¹ * ((g * w * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * w * g⁻¹)) * g := by rw [h2]
      _ = c * w := by group

end Helpers

section Decomp

variable {A : Subgroup G} {t : G}

theorem exists_eq_mul_conj_of_mem_sup (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) {u : G}
    (hu : u ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hut : u * t = t * u) :
    ∃ x ∈ A, u = x * (t * x * t⁻¹) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hu
  have hb' : t * b * t⁻¹ ∈ A := (mem_map_conj_iff_of_mul_self ht).1 hb
  have ha' : t * a * t⁻¹ ∈ A.map (MulAut.conj t).toMonoidHom :=
    (mem_map_conj_iff_of_mul_self ht).2 (by rwa [conj_conj_of_mul_self ht])
  have h2 : t * (a * b) * t⁻¹ = a * b := by rw [← hut, mul_inv_cancel_right]
  have h1 : a * b = (t * b * t⁻¹) * (t * a * t⁻¹) := by
    calc a * b = t * (a * b) * t⁻¹ := h2.symm
      _ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      _ = (t * b * t⁻¹) * (t * a * t⁻¹) := (hc _ hb' _ ha').symm
  obtain ⟨-, h4⟩ := factor_eq_of_mul_eq_mul_sOne hinf ha hb' hb ha' h1
  exact ⟨a, ha, by rw [h4]⟩

theorem map_conj_inf_eq (ht : t * t = 1) {W₀ : Subgroup G} (htW₀ : t ∈ normalizer (W₀ : Set G)) :
    (W₀ ⊓ A).map (MulAut.conj t).toMonoidHom = W₀ ⊓ A.map (MulAut.conj t).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwW, hwA⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 htW₀ w).1 hwW, ?_⟩
    rw [mem_map_conj_iff_of_mul_self ht, conj_conj_of_mul_self ht]
    exact hwA
  · intro hz
    obtain ⟨hzW, hzA⟩ := Subgroup.mem_inf.1 hz
    refine ⟨t * z * t⁻¹, Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 htW₀ z).1 hzW,
      (mem_map_conj_iff_of_mul_self ht).1 hzA⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_conj_of_mul_self ht z

theorem sup_le_normalizer_of_commute {B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ normalizer (A : Set G) := by
  refine sup_le le_normalizer ?_
  rw [le_normalizer_iff]
  intro b hb a ha
  rw [← hc a ha b hb, mul_inv_cancel_right]
  exact ha

end Decomp

section Sixteen

variable [Finite G] {A W₀ : Subgroup G} {t y : G}

theorem sup_inf_eq_of_card_sixteen (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hW₀ : W₀ ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hW₀2 : ∀ w ∈ W₀, w * w = 1)
    (hW₀c : Nat.card W₀ = 16) (htW₀ : t ∈ normalizer (W₀ : Set G))
    (hV₀ : Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 4)
    (hyA : y ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hyW₀ : y ∈ normalizer (W₀ : Set G))
    (hy0 : W₀ ⊓ centralizer ({y} : Set G) = ⊥) (hA16 : ¬ 16 ∣ Nat.card A) :
    Nat.card (W₀ ⊓ A : Subgroup G) = 4 ∧
      (W₀ ⊓ A) ⊔ (W₀ ⊓ A.map (MulAut.conj t).toMonoidHom) = W₀ := by
  set A' : Subgroup G := A.map (MulAut.conj t).toMonoidHom with hA'
  set E : Subgroup G := W₀ ⊓ A with hE
  set E' : Subgroup G := W₀ ⊓ A' with hE'
  have hWc : ∀ v ∈ W₀, ∀ w ∈ W₀, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₀2 hv hw
  have hEE' : E.map (MulAut.conj t).toMonoidHom = E' := map_conj_inf_eq ht htW₀
  have hE'c : Nat.card E' = Nat.card E := by
    rw [← hEE']
    exact Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hEt : E ⊓ (W₀ ⊓ centralizer ({t} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzA : z ∈ A := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).2
    have hzt : z ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).2).2
    have hzt' : t * z * t⁻¹ = z := by
      rw [mem_centralizer_singleton_iff] at hzt
      rw [← hzt, mul_inv_cancel_right]
    have hzA' : z ∈ A' := (mem_map_conj_iff_of_mul_self ht).2 (by rw [hzt']; exact hzA)
    have h1 : z ∈ A ⊓ A' := Subgroup.mem_inf.2 ⟨hzA, hzA'⟩
    rwa [hinf] at h1
  have hEle : Nat.card E ≤ 4 := by
    have hN : W₀ ⊓ centralizer ({t} : Set G) ≤ normalizer (E : Set G) := by
      rw [le_normalizer_iff]
      intro a ha e he
      rw [← hWc e he.1 a ha.1, mul_inv_cancel_right]
      exact he
    have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne hN
    rw [hEt, Subgroup.card_bot, mul_one, hV₀] at h1
    have h2 : Nat.card (E ⊔ (W₀ ⊓ centralizer ({t} : Set G)) : Subgroup G) ≤ 16 := by
      rw [← hW₀c]
      exact Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
    omega
  have hEdvd : Nat.card E ∣ 16 := by
    rw [← hW₀c]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro e he
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hyW₀ e).1 he.1,
      (mem_normalizer_iff.1 (sup_le_normalizer_of_commute hc hyA) e).1 he.2⟩
  have hE2 : Nat.card E ≠ 2 := by
    intro h2
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [h2]; norm_num)
    obtain ⟨⟨e, heE⟩, he1⟩ := exists_ne (1 : E)
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    have hoe : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hW₀2 e heE.1) he1'
    have hzE : zpowers e = E := by
      refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 heE) ?_
      rw [Nat.card_zpowers, hoe, h2]
    have hye : y * e * y⁻¹ ∈ zpowers e := hzE ▸ hyE e heE
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hoe hye with h | h
    · apply he1'
      have h3 : e = y⁻¹ * (y * e * y⁻¹) * y := by group
      rw [h3, h]
      group
    · have h3 : e ∈ W₀ ⊓ centralizer ({y} : Set G) := by
        refine Subgroup.mem_inf.2 ⟨heE.1, ?_⟩
        rw [mem_centralizer_singleton_iff]
        calc e * y = (y * e * y⁻¹) * y := by rw [h]
          _ = y * e := by group
      rw [hy0, Subgroup.mem_bot] at h3
      exact he1' h3
  have hE1 : Nat.card E ≠ 1 := by
    intro h1
    have hEb : E = ⊥ := Subgroup.eq_bot_of_card_eq E h1
    have hE'b : W₀ ⊓ A' = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [← hE'c] at h1
      exact h1
    have hN : W₀ ≤ normalizer (A' : Set G) := by
      have hc' : ∀ b ∈ A', ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
      exact hW₀.trans (by rw [sup_comm]; exact sup_le_normalizer_of_commute hc')
    have h3 := card_sup_mul_card_inf_of_le_normalizer_sOne hN
    rw [inf_comm, hE'b, Subgroup.card_bot, mul_one, hW₀c] at h3
    have h4 : Nat.card (A' ⊔ W₀ : Subgroup G) ∣ Nat.card (A ⊔ A' : Subgroup G) :=
      Subgroup.card_dvd_of_le (sup_le le_sup_right hW₀)
    rw [h3, card_sup_of_commute hc hinf] at h4
    have hA'c : Nat.card A' = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have hpos : 0 < Nat.card A' := Nat.card_pos
    rw [mul_comm (Nat.card A) (Nat.card A')] at h4
    exact hA16 (Nat.dvd_of_mul_dvd_mul_left hpos h4)
  have hE4 : Nat.card E = 4 := by
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16] at hEdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hEdvd
    interval_cases k <;> simp_all
  refine ⟨hE4, ?_⟩
  have hcEE : ∀ a ∈ E, ∀ b ∈ E', a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have hinfEE : E ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ A ⊓ A' := Subgroup.mem_inf.2 ⟨hz.1.2, hz.2.2⟩
    rwa [hinf] at h1
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
  rw [card_sup_of_commute hcEE hinfEE, hE'c, hE4, hW₀c]

end Sixteen

section Norm

theorem centralizer_le_normalizer_of_le {H K : Subgroup G} (hKH : K ≤ H) :
    centralizer (H : Set G) ≤ normalizer (K : Set G) := by
  rw [le_normalizer_iff]
  intro c hc k hk
  rw [← (mem_centralizer_iff.1 hc) k (hKH hk), mul_inv_cancel_right]
  exact hk

theorem map_conj_map_conj_of_mul_self {t : G} (ht : t * t = 1) (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  ext z
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [conj_conj_of_mul_self ht]
  · intro hz
    refine ⟨t * z * t⁻¹, ⟨z, hz, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_conj_of_mul_self ht z

theorem mem_normalizer_inf_of_swap {W₀ E E' : Subgroup G} {g : G}
    (hgW : W₀.map (MulAut.conj g).toMonoidHom = W₀) (hgE : E.map (MulAut.conj g).toMonoidHom = E')
    (hgE' : E'.map (MulAut.conj g).toMonoidHom = E) :
    g ∈ normalizer ((normalizer (W₀ : Set G) ⊓ normalizer (E : Set G) ⊓
      normalizer (E' : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  change (normalizer (W₀ : Set G) ⊓ normalizer (E : Set G) ⊓
      normalizer (E' : Set G)).map (MulAut.conj g).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g).injective, map_inf _ _ _ (MulAut.conj g).injective,
    map_equiv_normalizer_eq, map_equiv_normalizer_eq, map_equiv_normalizer_eq, hgW, hgE, hgE',
    inf_assoc, inf_comm (normalizer (E' : Set G)), ← inf_assoc]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.1 hg

end Norm

end CFSG.SeitzReduction.LinearPilot
