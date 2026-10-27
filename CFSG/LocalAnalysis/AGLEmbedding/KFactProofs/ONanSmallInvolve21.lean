module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL
public import CFSG.Sporadic.Recognition.McLASCert

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Blueprint CFSG.Sporadic.Schreier

theorem exists_orderOf_eq_of_surjective {K L : Type} [Group K] [Finite K] [Group L]
    (A : Subgroup K) (f : A →* L) (hf : Function.Surjective f) (g : L) :
    ∃ x : K, orderOf x = orderOf g := by
  obtain ⟨a, rfl⟩ := hf g
  obtain ⟨m, hm⟩ := orderOf_map_dvd f a
  have hpos : 0 < orderOf a := orderOf_pos a
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  refine ⟨((a ^ m : A) : K), ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hm.symm), hm]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)

theorem exists_orderOf_twenty_one_of_isAltTwoP_five {L : Type} [Group L] (hL : IsAltTwoP 5 L) :
    ∃ g : L, orderOf g = 21 := by
  obtain ⟨e⟩ := hL
  let σ : Equiv.Perm (Fin (2 * 5)) :=
    List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5, 6, 7, 8, 9]
  have hσ : σ ∈ alternatingGroup (Fin (2 * 5)) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  have hord : orderOf σ = 21 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide +kernel, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide +kernel
  refine ⟨e.symm ⟨σ, hσ⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hord]

theorem not_orderOf_twenty_one_of_classes {H : Type*} [Group H] (x₁ x₂ : H)
    (c₁ : Nat.card (Subgroup.centralizer ({x₁} : Set H)) = 29160)
    (c₂ : Nat.card (Subgroup.centralizer ({x₂} : Set H)) = 972)
    (hall : ∀ y : H, orderOf y = 3 → IsConj y x₁ ∨ IsConj y x₂) (y : H) :
    orderOf y ≠ 21 := by
  intro hy
  have hz : orderOf (y ^ 7) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hy]; norm_num), hy]
  have hw : orderOf (y ^ 3) = 7 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hy]; norm_num), hy]
  have hcomm : y ^ 3 * y ^ 7 = y ^ 7 * y ^ 3 := (Commute.pow_pow_self y 3 7).eq
  have key : ∀ x : H, (∃ c : H, c * y ^ 7 * c⁻¹ = x) →
      7 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) := by
    rintro x ⟨c, rfl⟩
    have hmem : c * y ^ 3 * c⁻¹ ∈ Subgroup.centralizer ({c * y ^ 7 * c⁻¹} : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      calc c * y ^ 7 * c⁻¹ * (c * y ^ 3 * c⁻¹) = c * (y ^ 7 * y ^ 3) * c⁻¹ := by group
        _ = c * (y ^ 3 * y ^ 7) * c⁻¹ := by rw [hcomm]
        _ = c * y ^ 3 * c⁻¹ * (c * y ^ 7 * c⁻¹) := by group
    have hord : orderOf (c * y ^ 3 * c⁻¹) = 7 := by
      have := MulEquiv.orderOf_eq (MulAut.conj c) (y ^ 3)
      rw [MulAut.conj_apply] at this
      rw [this, hw]
    have := orderOf_dvd_natCard (⟨c * y ^ 3 * c⁻¹, hmem⟩ :
      Subgroup.centralizer ({c * y ^ 7 * c⁻¹} : Set H))
    rwa [Subgroup.orderOf_mk, hord] at this
  rcases hall (y ^ 7) hz with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have := key x₁ ⟨c, hc⟩
    rw [c₁] at this
    omega
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have := key x₂ ⟨c, hc⟩
    rw [c₂] at this
    omega

theorem not_orderOf_twenty_one_of_isMcL
    {K : Type} [Group K]
    (hs : IsSimpleGroup K) (hK : IsSporadicGroup .McL K) (x : K) : orderOf x ≠ 21 := by
  obtain ⟨e⟩ := nonempty_equiv_mclP hs hK
  obtain ⟨x₁, x₂, -, -, c₁, c₂, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mcl_two_classes_order_three
      CFSG.Sporadic.Recognition.McLAS.threeFacts_cert
  have e' : K ≃* NativeSporadic.McL := e.trans mclPermEquiv.symm
  intro hx
  have h1 : orderOf (e' x) = 21 := by rw [MulEquiv.orderOf_eq]; exact hx
  exact @not_orderOf_twenty_one_of_classes NativeSporadic.McL inferInstance x₁ x₂ c₁ c₂ hall
    (e' x) h1

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
