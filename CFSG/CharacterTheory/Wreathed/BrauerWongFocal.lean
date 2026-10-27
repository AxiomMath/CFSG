module

public import CFSG.CharacterTheory.Wreathed.QuaternionFocal
public import CFSG.CharacterTheory.Wreathed.SimpleFusion

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u v

@[expose] def NoAbelianTwoPowerIndexIntersection (X : Type v) [Group X] (S : Subgroup X) : Prop :=
  ∀ H : Subgroup X, H.Normal → (∃ k : ℕ, H.index = 2 ^ k) → ¬ IsMulCommutative ↥(S ⊓ H)

variable {G : Type u} [Group G]

theorem isMulCommutative_of_le_modelBase {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    {H : Subgroup G} (hH : H ≤ modelBase S e) : IsMulCommutative H := by
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨u, hu, hux⟩ := hH x.property
  obtain ⟨w, hw, hwy⟩ := hH y.property
  apply Subtype.ext
  change (x : G) * y = y * x
  rw [← hux, ← hwy, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val
    (isMulCommutative_iff.mp (base_is_abelian m) ⟨u, hu⟩ ⟨w, hw⟩)

variable [Finite G]

theorem transferFocal_ker_spec (S : Sylow 2 G) :
    ((S : Subgroup G).transferFocal.ker).Normal ∧
      (∃ k : ℕ, ((S : Subgroup G).transferFocal.ker).index = 2 ^ k) ∧
      (S : Subgroup G) ⊓ (S : Subgroup G).transferFocal.ker = (S : Subgroup G).focalSubgroup ∧
      ((S : Subgroup G).transferFocal.ker).index * Nat.card (S : Subgroup G).focalSubgroup =
        Nat.card (S : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ((S : Subgroup G).transferFocal.ker).index =
      Nat.card (↥(S : Subgroup G) ⧸ (S : Subgroup G).focalSubgroupOf) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr
      (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf S).toEquiv
  have hcardF : Nat.card (S : Subgroup G).focalSubgroupOf =
      Nat.card (S : Subgroup G).focalSubgroup :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S : Subgroup G).focalSubgroup_le).toEquiv
  refine ⟨MonoidHom.normal_ker _, ?_, ?_, ?_⟩
  · rw [hidx]
    exact (S.isPGroup'.to_quotient _).exists_card_eq
  · rw [inf_comm]
    exact Subgroup.ker_transferFocal_inf_eq_focalSubgroup S
  · rw [hidx, ← hcardF]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem vSym3_of_noAbelian (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hH : NoAbelianTwoPowerIndexIntersection G (S : Subgroup G)) :
    Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3)) := by
  rcases modelVNormalizerQuotient_alternatives n hn S e with htwo | hsix
  · exfalso
    have hF := model_base_contains_focal_of_v_order_two n hn S e htwo
    obtain ⟨hK, hidx, hinf, -⟩ := transferFocal_ker_spec S
    apply hH _ hK hidx
    rw [hinf]
    exact isMulCommutative_of_le_modelBase S e hF
  · exact hsix

theorem mem_of_odd_of_two_power_index {X : Type v} [Group X] [Finite X] (K : Subgroup X)
    [K.Normal] (hK : ∃ k : ℕ, K.index = 2 ^ k) (h : X) (hodd : Odd (orderOf h)) : h ∈ K := by
  obtain ⟨k, hk⟩ := hK
  rw [← QuotientGroup.eq_one_iff]
  have hdvd₁ : orderOf (QuotientGroup.mk' K h) ∣ orderOf h := orderOf_map_dvd _ _
  have hdvd₂ : orderOf (QuotientGroup.mk' K h) ∣ 2 ^ k := by
    rw [← hk, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf h) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hone : orderOf (QuotientGroup.mk' K h) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd₁ hcop) hdvd₂
  exact orderOf_eq_one_iff.mp hone

theorem quaternionEight_not_commutative :
    ¬ ∀ a b : QuaternionGroup 2, a * b = b * a := by decide

theorem noAbelian_of_quaternion_conjugation {X : Type v} [Group X] [Finite X] (S : Subgroup X)
    {Q : Type v} [Group Q] (eQ : QuaternionGroup 2 ≃* Q) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3)
    (f : Q →* X) (hf : Function.Injective f) (hfS : f.range ≤ S) (h : X)
    (hodd : Odd (orderOf h)) (hconj : ∀ q : Q, f (a q) = h * f q * h⁻¹) :
    NoAbelianTwoPowerIndexIntersection X S := by
  intro K hK hidx hcomm
  have hhK : h ∈ K := mem_of_odd_of_two_power_index K hidx h hodd
  have hgen : automorphismDifferences a ≤ K.comap f := by
    rw [automorphismDifferences, Subgroup.closure_le]
    rintro _ ⟨q, rfl⟩
    change f (a q * q⁻¹) ∈ K
    rw [map_mul, map_inv, hconj]
    have hc : f q * h⁻¹ * (f q)⁻¹ ∈ K := hK.conj_mem _ (K.inv_mem hhK) _
    have := K.mul_mem hhK hc
    simpa only [mul_assoc] using this
  rw [quaternion_differences_eq_top eQ a horder, top_le_iff] at hgen
  have hrange : ∀ q : Q, f q ∈ S ⊓ K := fun q =>
    ⟨hfS ⟨q, rfl⟩, by
      have hq : q ∈ K.comap f := hgen ▸ Subgroup.mem_top q
      exact hq⟩
  apply quaternionEight_not_commutative
  intro x y
  apply eQ.injective
  apply hf
  have hxy := congrArg Subtype.val
    (isMulCommutative_iff.mp hcomm ⟨f (eQ x), hrange _⟩ ⟨f (eQ y), hrange _⟩)
  change f (eQ x) * f (eQ y) = f (eQ y) * f (eQ x) at hxy
  simpa only [map_mul] using hxy

theorem noAbelian_of_vNormalizer_actor (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (g : Subgroup.normalizer (modelV S e : Set G))
    (hodd : Odd (orderOf g)) (horder : orderOf (modelVQuotientAction S e g) = 3) :
    NoAbelianTwoPowerIndexIntersection G (S : Subgroup G) := by
  refine noAbelian_of_quaternion_conjugation (S : Subgroup G)
    ((originalQuaternionProjectionEquiv n hn).trans (modelQEquiv S e))
    (modelQAutomorphism n hn S e g)
    ((modelQ_intrinsic_action_order n hn S e g).trans horder) (modelQ S e).subtype
    (modelQ S e).subtype_injective ?_ g.val ?_ ?_
  · rw [Subgroup.range_subtype]
    exact (modelQ_le_modelV n hn S e).trans (modelV_le_sylow S e)
  · rwa [← Subgroup.orderOf_coe] at hodd
  · intro q
    exact modelQAutomorphism_coe n hn S e g q

theorem noAbelian_of_vSym3 (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    NoAbelianTwoPowerIndexIntersection G (S : Subgroup G) := by
  obtain ⟨g, -, hodd, horder⟩ := modelVNormalizer_exists_odd_three_power_actor n hn S e hsix
  exact noAbelian_of_vNormalizer_actor n hn S e g hodd horder

end CFSG.Wreathed.BrauerWong
