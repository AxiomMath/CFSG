module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigQJoin

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem mem_of_mul_self_eq_one (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K')
    (hodd : ∀ z ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓ coreActionKernel K,
      orderOf z ≠ 2)
    {d : G} (hd : d ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') (hd2 : d * d = 1) :
    d ∈ K := by
  obtain ⟨k, hk, hc⟩ := exists_inv_mul_mem_coreActionKernel hK.1 hd.1
  set c := k⁻¹ * d with hcdef
  have hKQ : K ≤ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' :=
    le_inf ((le_twoLayerIn_of_isTwoComponentIn hK.1).trans le_sup_right)
      (le_coreActionKernel_of_ne hK' hK hne.symm)
  have hcQ : c ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓ coreActionKernel K :=
    mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKQ hk)) hd, hc⟩
  have hcN : c ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp hc).1
  have hcc : c * c ∈ K := by
    have e : c * c = (c * k * c⁻¹)⁻¹ * k⁻¹ * (d * d) := by simp only [hcdef]; group
    rw [e, hd2, mul_one]
    exact mul_mem (inv_mem ((mem_normalizer_iff.mp hcN k).mp hk)) (inv_mem hk)
  have hcodd : Odd (orderOf c) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
    exact hodd _ (pow_mem hcQ _) (orderOf_pow_orderOf_div h0 (even_iff_two_dvd.mp hev))
  have hcK : c ∈ K := by
    obtain ⟨j, hj⟩ := hcodd
    have e : c = (c * c) ^ (j + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf c + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact pow_mem hcc _
  have hd' : d = k * c := by simp only [hcdef, mul_inv_cancel_left]
  rw [hd']
  exact mul_mem hk hcK

@[expose] def SolomonQTwoDisconnectedSylowInvFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
      IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') →
      3 ≤ CFSG.Open.pRank 2 K →
      (∃ (S' : Sylow 2 ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'))
          (E F : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')),
          IsKleinFour E ∧ E ≤ S' ∧ IsKleinFour F ∧ F ≤ S' ∧
            ¬ Relation.ReflTransGen
              (CommFourAdj ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')) E F) →
      (∃ D : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'),
          IsKleinFour D ∧ ∀ A : Subgroup G, IsKleinFour A →
            ¬ A ≤ K ⊓ centralizer
              ((D.map ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K').subtype :
                Subgroup G) : Set G)) →
      center (coreQuot K) ≠ ⊥ →
      (∀ Z : Subgroup (coreQuot K), Z ≤ center (coreQuot K) → ¬ IsKleinFour Z) →
      (∃ z ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓ coreActionKernel K,
        orderOf z = 2) →
      IsSolomonI (coreQuot K)

theorem solomonQTwoDisconnectedSylowCycFor_of_inv (h : SolomonQTwoDisconnectedSylowInvFor) :
    SolomonQTwoDisconnectedSylowCycFor := by
  intro G _ _ hG N hN hr K hK K' hK' hne hdisc h3 hS' hD hZ hZ4
  by_cases hz : ∃ z ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓ coreActionKernel K,
      orderOf z = 2
  · exact h G hG N hN hr K hK K' hK' hne hdisc h3 hS' hD hZ hZ4 hz
  exfalso
  set Q' := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' with hQ'
  obtain ⟨D, hD4, hDA⟩ := hD
  set DG := D.map Q'.subtype with hDG
  have hDG4 : IsKleinFour DG := by
    refine isKleinFour_of_card_eq_four ?_ fun x hx => ?_
    · rw [hDG, Subgroup.card_map_of_injective Q'.subtype_injective, hD4.card_four]
    · obtain ⟨v, hv, rfl⟩ := hx
      rw [← map_pow, sq_eq_one_of_isKleinFour hD4 hv, map_one]
  have hDGK : DG ≤ K := fun d hd =>
    mem_of_mul_self_eq_one hK hK' hne (fun z hz' hz2 => hz ⟨z, hz', hz2⟩) (map_subtype_le _ hd)
      (by rw [← pow_two]; exact Sig.sq_eq_one_of_isKleinFour hDG4 hd)
  exact hDA DG hDG4 (le_inf hDGK (le_centralizer_of_le_of_comm le_rfl (comm_of_isKleinFour hDG4)))

end CFSG.ComponentClassification.Sol76.Sig
