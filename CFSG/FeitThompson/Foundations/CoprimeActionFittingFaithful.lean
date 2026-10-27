module

public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.FaithfulCoprimeBaseCentralizer
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting

open SemidirectProduct

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}

instance instFiniteSemidirectProduct [Finite G] [Finite A] : Finite (G ⋊[φ] A) :=
  Finite.of_equiv _ equivProd.symm

theorem conj_inl (x : G ⋊[φ] A) (g : G) :
    x * inl g * x⁻¹ = inl (x.left * φ x.right g * x.left⁻¹) := by
  refine SemidirectProduct.ext ?_ ?_ <;>
    simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, mul_assoc]

theorem map_inl_normal_of_characteristic (H : Subgroup G) [H.Characteristic] :
    (H.map (inl : G →* G ⋊[φ] A)).Normal := by
  constructor
  rintro y ⟨g, hg, rfl⟩ x
  rw [conj_inl]
  refine Subgroup.mem_map_of_mem _ ?_
  have h1 : (φ x.right) g ∈ H :=
    Subgroup.characteristic_iff_map_eq.1 ‹H.Characteristic› (φ x.right) ▸
      Subgroup.mem_map_of_mem _ hg
  exact (Subgroup.normal_of_characteristic H).conj_mem _ h1 _

theorem range_inl_normal : ((inl : G →* G ⋊[φ] A).range).Normal := by
  rw [range_inl_eq_ker_rightHom]
  exact (rightHom (φ := φ)).normal_ker

theorem natCard_range_inl : Nat.card ((inl : G →* G ⋊[φ] A).range) = Nat.card G :=
  Nat.card_congr (MonoidHom.ofInjective (inl_injective (φ := φ))).toEquiv.symm

variable [Finite G] [Finite A]

theorem le_range_inl_of_normal_of_isPGroup (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime) {N : Subgroup (G ⋊[φ] A)} (hN : N.Normal)
    (hpg : IsPGroup p N) : N ≤ (inl : G →* G ⋊[φ] A).range := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpG : p ∣ Nat.card G
  ·
    have hpA : ¬ p ∣ Nat.card A := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpG h)
    rw [range_inl_eq_ker_rightHom]
    intro x hx
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := hpg ⟨x, hx⟩
    have hox : orderOf x ∣ p ^ k := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_of_pow_eq_one hk
    have h1 : orderOf (rightHom x : A) ∣ p ^ k := (orderOf_map_dvd _ _).trans hox
    have h2 : orderOf (rightHom x : A) ∣ Nat.card A := orderOf_dvd_natCard _
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpA)) h1 h2)
  ·
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
    have hcopN : (Nat.card N).Coprime (Nat.card ((inl : G →* G ⋊[φ] A).range)) := by
      rw [hn, natCard_range_inl]
      exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hpG)
    have hdisj : Disjoint N ((inl : G →* G ⋊[φ] A).range) :=
      Subgroup.disjoint_of_coprime_natCard hcopN
    have hcentral : N ≤ Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.commute_of_normal_of_disjoint N _ hN range_inl_normal hdisj x h hx hh).symm
    exact hcentral.trans (centralizer_range_inl_le_range_inl hcop hφ)

theorem pCore_semidirectProduct_le_range_inl (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime) :
    pCore p (G ⋊[φ] A) ≤ (inl : G →* G ⋊[φ] A).range :=
  le_range_inl_of_normal_of_isPGroup hcop hφ hp (pCore_normal p _) (isPGroup_pCore hp _)

theorem pCore_semidirectProduct_eq_bot (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G) :
    pCore p (G ⋊[φ] A) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_pCore hp (G ⋊[φ] A))
  have hdvd : Nat.card (pCore p (G ⋊[φ] A)) ∣ Nat.card G := by
    rw [← natCard_range_inl (φ := φ)]
    exact Subgroup.card_dvd_of_le (pCore_semidirectProduct_le_range_inl hcop hφ hp)
  rw [← Subgroup.card_eq_one, hn]
  rcases Nat.eq_zero_or_pos n with rfl | hn'
  · simp
  · exact absurd ((dvd_pow_self p hn'.ne').trans (hn ▸ hdvd)) hpG

theorem fittingRaw_semidirectProduct_le_range_inl (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) :
    fittingRaw (G ⋊[φ] A) ≤ (inl : G →* G ⋊[φ] A).range := by
  refine fittingRaw_le fun N hN hN' => ?_
  obtain ⟨p, hp, hpg⟩ := isPrimePowerOrder_iff_isPGroup.1 hN'
  exact le_range_inl_of_normal_of_isPGroup hcop hφ hp hN hpg

theorem map_inl_fittingRaw_le_fittingRaw (G A : Type*) [Group G] [Group A] [Finite G] [Finite A]
    (φ : A →* MulAut G) :
    (fittingRaw G).map (inl : G →* G ⋊[φ] A) ≤ fittingRaw (G ⋊[φ] A) :=
  le_fittingRaw_of_normal_of_isNilpotent (map_inl_normal_of_characteristic _)
    (Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (fittingRaw G) inl inl_injective))

theorem fittingRaw_semidirectProduct_eq_map_inl (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) :
    fittingRaw (G ⋊[φ] A) = (fittingRaw G).map (inl : G →* G ⋊[φ] A) := by
  refine le_antisymm ?_ (map_inl_fittingRaw_le_fittingRaw G A φ)
  set F := fittingRaw (G ⋊[φ] A)
  have hmap : (F.comap (inl : G →* G ⋊[φ] A)).map (inl : G →* G ⋊[φ] A) = F :=
    Subgroup.map_comap_eq_self (fittingRaw_semidirectProduct_le_range_inl hcop hφ)
  have hnorm : (F.comap (inl : G →* G ⋊[φ] A)).Normal := (fittingRaw_normal _).comap _
  have hnil : Group.IsNilpotent (F.comap (inl : G →* G ⋊[φ] A)) :=
    Group.nilpotent_of_mulEquiv (G := F)
      (((Subgroup.equivMapOfInjective (F.comap (inl : G →* G ⋊[φ] A)) inl
        inl_injective).trans (MulEquiv.subgroupCongr hmap)).symm)
  calc F = (F.comap (inl : G →* G ⋊[φ] A)).map (inl : G →* G ⋊[φ] A) := hmap.symm
    _ ≤ (fittingRaw G).map (inl : G →* G ⋊[φ] A) :=
        Subgroup.map_mono (le_fittingRaw_of_normal_of_isNilpotent hnorm hnil)

theorem comap_inl_fittingRaw_semidirectProduct (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) :
    (fittingRaw (G ⋊[φ] A)).comap (inl : G →* G ⋊[φ] A) = fittingRaw G := by
  rw [fittingRaw_semidirectProduct_eq_map_inl hcop hφ,
    Subgroup.comap_map_eq_self_of_injective inl_injective]

noncomputable def fittingRawSemidirectProductMulEquiv (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) : fittingRaw (G ⋊[φ] A) ≃* fittingRaw G :=
  (MulEquiv.subgroupCongr (fittingRaw_semidirectProduct_eq_map_inl hcop hφ)).trans
    (Subgroup.equivMapOfInjective (fittingRaw G) inl inl_injective).symm

@[simp]
theorem coe_fittingRawSemidirectProductMulEquiv_symm_apply
    (hcop : (Nat.card G).Coprime (Nat.card A)) (hφ : Function.Injective φ)
    (x : fittingRaw G) :
    ((fittingRawSemidirectProductMulEquiv hcop hφ).symm x : G ⋊[φ] A) = inl (x : G) := (rfl)

theorem pCore_semidirectProduct_eq_map_inl (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime) :
    pCore p (G ⋊[φ] A) = (pCore p G).map (inl : G →* G ⋊[φ] A) := by
  refine le_antisymm ?_ ?_
  ·
    have hle := pCore_semidirectProduct_le_range_inl hcop hφ hp
    have hmap : ((pCore p (G ⋊[φ] A)).comap (inl : G →* G ⋊[φ] A)).map
        (inl : G →* G ⋊[φ] A) = pCore p (G ⋊[φ] A) := Subgroup.map_comap_eq_self hle
    have hnorm : ((pCore p (G ⋊[φ] A)).comap (inl : G →* G ⋊[φ] A)).Normal :=
      (pCore_normal p _).comap _
    have hpg : IsPGroup p ((pCore p (G ⋊[φ] A)).comap (inl : G →* G ⋊[φ] A)) :=
      (isPGroup_pCore hp (G ⋊[φ] A)).comap_of_injective inl inl_injective
    exact hmap ▸ Subgroup.map_mono (le_pCore hp hnorm hpg)
  ·
    exact le_pCore hp (map_inl_normal_of_characteristic (pCore p G))
      ((isPGroup_pCore hp G).map inl)

end

end CFSG.FeitThompson
