module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsMain
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasASplit

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.M12Cover

theorem exists_center_eq_zpowers {Q : Type} [Group Q] [Finite Q]
    (hZ2 : Nat.card (center Q) = 2) : ∃ t ∈ center Q, orderOf t = 2 ∧ center Q = zpowers t := by
  have : Nontrivial (center Q) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨t, htZ⟩, ht1⟩ := exists_ne (1 : center Q)
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : orderOf t = 2 := by
    have h := orderOf_dvd_natCard (⟨t, htZ⟩ : center Q)
    rw [hZ2, Subgroup.orderOf_mk] at h
    exact ((Nat.dvd_prime Nat.prime_two).mp h).resolve_left
      (fun h1 => ht1' (orderOf_eq_one_iff.mp h1))
  refine ⟨t, htZ, ht2, (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htZ) ?_).symm⟩
  rw [hZ2, Nat.card_zpowers, ht2]

theorem sporadicCoverRankInput_M12 :
    SporadicCoverRankInput .M12 := by
  intro Q _ _ hQ hZ2 ⟨e⟩
  obtain ⟨t, htZ, ht2, hcen⟩ := exists_center_eq_zpowers hZ2
  let e' : Q ⧸ center Q ≃* NativeSporadic.M12 := e
  set π : Q →* NativeSporadic.M12 := e'.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπ
  have hπs : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = zpowers t := (ker_quotientMap e').trans hcen
  obtain ⟨-, hDD, -, hz2, hzc, -, hW, hWD, -, hr1, hs1, hrs, hWsq, hWc, hS, hinv, -, hh⟩ :=
    fusionData_pinned
  obtain ⟨W, hWW⟩ := hS
  have hrW : elemR ∈ fusionW := by rw [hW]; exact subset_closure (Set.mem_insert _ _)
  have hsW : elemS ∈ fusionW := by rw [hW]; exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrD : elemR ∈ fixedD := hWD hrW
  have hsD : elemS ∈ fixedD := hWD hsW
  obtain ⟨-, ⟨eA, heA, -⟩, -⟩ :=
    CentralCover.central_double_cover_splits_over_perfect_factor_from_involution_fusion π
      hπs hker ht2 htZ (Subgroup.isPerfect_iff.2 hDD) W
      (fun w hw => by
        rw [hWW, mem_subgroupOf] at hw
        exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hWsq _ hw))
      hrD (fun q hq hq2 => by
        obtain ⟨d, hd, hqd⟩ := hinv q hq hq2
        exact ⟨d, hd, hqd.symm⟩) hzc hz2 ⟨_, hh⟩
  set r' : fixedD := ⟨elemR, hrD⟩
  set s' : fixedD := ⟨elemS, hsD⟩
  have hπa : π (eA.symm r' : Q) = elemR := by rw [← heA, MulEquiv.apply_symm_apply]
  have hπb : π (eA.symm s' : Q) = elemS := by rw [← heA, MulEquiv.apply_symm_apply]
  have hr2 : r' * r' = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]; exact hWsq _ hrW)
  have hs2 : s' * s' = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]; exact hWsq _ hsW)
  have hrs' : r' * s' = s' * r' := Subtype.ext (hWc _ hrW _ hsW)
  have hss : elemS * elemS = 1 := by rw [← pow_two]; exact hWsq _ hsW
  have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at ht2; omega
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  refine three_le_pRank_of_four_group (τ := MonoidHom.id Q) (πG := π) (πQ := π) (fun _ => rfl)
    (a := (eA.symm r' : Q)) (b := (eA.symm s' : Q)) ?_ ?_ ?_ ?_ ?_ ?_ htZ htt ht1
    (by rw [← MonoidHom.mem_ker, hker]; exact mem_zpowers t)
  · rw [← Subgroup.coe_mul, ← map_mul, hr2, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← map_mul, hs2, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← map_mul, hrs', map_mul, Subgroup.coe_mul]
  · rw [hπa]; exact hr1
  · rw [hπb]; exact hs1
  · rw [map_mul, hπa, hπb]
    intro h
    apply hrs
    have h1 := eq_inv_of_mul_eq_one_left h
    rwa [inv_eq_of_mul_eq_one_right hss] at h1

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
