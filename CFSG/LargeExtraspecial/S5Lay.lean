module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LargeExtraspecial.S5Gen2

public section

namespace CFSG.LargeExtraspecial.S5

open Subgroup CFSG.Open

variable {X : Type*} [Group X]

theorem mem_normalizer_sup {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_of_forall_commute {A : Subgroup X} {g : X} (h : ∀ a ∈ A, g * a = a * g) :
    g ∈ normalizer (A : Set X) := by
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [h a ha, mul_inv_cancel_right]
    exact ha
  · intro ha
    have h2 := h _ ha
    have e : g * a * g⁻¹ * g = g * (g * a * g⁻¹) := h2.symm
    have e2 : a = g * a * g⁻¹ := by
      calc a = g⁻¹ * (g * a * g⁻¹ * g) := by group
        _ = g⁻¹ * (g * (g * a * g⁻¹)) := by rw [e]
        _ = g * a * g⁻¹ := by group
    rw [e2]
    exact ha

theorem le_normalizer_of_isComponentOf [Finite X] {A C K : Subgroup X}
    (hA : IsComponentOf A K) (hC : IsComponentOf C K) : C ≤ normalizer (A : Set X) := by
  by_cases h : C = A
  · rw [h]
    exact le_normalizer
  · intro c hc
    exact mem_normalizer_of_forall_commute fun a ha =>
      mul_comm_of_isComponentOf_ne hC hA h hc ha

theorem isSubnormal_sup_of_isComponentOf [Finite X] {A B K : Subgroup X}
    (hA : IsComponentOf A K) (hB : IsComponentOf B K) : IsSubnormal (A ⊔ B) K := by
  set E := sSup {C : Subgroup X | IsComponentOf C K} with hE
  have hAE : A ≤ E := le_sSup hA
  have hBE : B ≤ E := le_sSup hB
  have hEK : E ≤ K := sSup_le fun C hC => hC.1
  have hnE : ((A ⊔ B).subgroupOf E).Normal := by
    refine normal_subgroupOf_of_le_normalizer ?_
    refine sSup_le fun C hC => fun c hc => mem_normalizer_sup ?_ ?_
    · exact le_normalizer_of_isComponentOf hA hC hc
    · exact le_normalizer_of_isComponentOf hB hC hc
  have hle : ∀ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ E := by
    intro k hk
    rw [map_le_iff_le_comap]
    refine sSup_le fun C hC => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_conj hC hk)
  have hnK : (E.subgroupOf K).Normal := by
    refine normal_subgroupOf_of_le_normalizer fun k hk => ?_
    rw [mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hle k hk) ?_
    have h2 := map_mono (f := (MulAut.conj k).toMonoidHom) (hle k⁻¹ (K.inv_mem hk))
    rwa [map_map, show (MulAut.conj k).toMonoidHom.comp (MulAut.conj k⁻¹).toMonoidHom =
      MonoidHom.id X by ext; simp [mul_assoc], map_id] at h2
  exact CFSG.ClassicalInvolution.isSubnormal_trans
    (CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf (sup_le hAE hBE) hnE)
    (CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hEK hnK)

theorem two_dvd_card_of_isQuasisimple [Finite X] {A : Subgroup X}
    (hA : CFSG.Open.IsQuasisimple A) : 2 ∣ Nat.card A := by
  by_contra h
  exact not_isSolvable_of_isQuasisimple hA
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)))

theorem odd_orderOf_of_forall [Finite X] {C : Set X} (hpow : ∀ x ∈ C, ∀ n : ℕ, x ^ n ∈ C)
    (h2 : ∀ y ∈ C, ∀ k : ℕ, y ^ (2 ^ k) = 1 → y = 1) {x : X} (hx : x ∈ C) :
    Odd (orderOf x) := by
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hxm : x ^ m = 1 := by
    refine h2 _ (hpow x hx m) k ?_
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hdvd : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
  exact Odd.of_dvd_nat hm hdvd

theorem eq_one_of_pow_odd_of_pow_two {y : X} {m k : ℕ} (hm : Odd m) (h1 : y ^ m = 1)
    (h2 : y ^ (2 ^ k) = 1) : y = 1 := by
  have hd1 := orderOf_dvd_of_pow_eq_one h1
  have hd2 := orderOf_dvd_of_pow_eq_one h2
  have hcop : (orderOf y).Coprime (2 ^ k) :=
    (Nat.Coprime.pow_right k (hm.coprime_two_right)).coprime_dvd_left hd1
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hd2)

end CFSG.LargeExtraspecial.S5
