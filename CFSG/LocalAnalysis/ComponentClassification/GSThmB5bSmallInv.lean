module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Small

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Equiv Equiv.Perm

theorem cycleType_of_involution_alternating {n : ℕ} (hn : n ≤ 7) {σ : Perm (Fin n)}
    (hσA : σ ∈ alternatingGroup (Fin n)) (hσ : orderOf σ = 2) :
    σ.cycleType = Multiset.replicate 2 2 := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (σ := σ) (by rw [hσ]; exact Nat.prime_two)
  rw [hσ] at hk
  have hsum : σ.cycleType.sum ≤ n := by
    have := sum_cycleType_le σ
    simpa using this
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsign := hσA
  rw [mem_alternatingGroup, sign_of_cycleType, hk, Multiset.sum_replicate,
    Multiset.card_replicate, smul_eq_mul] at hsign
  have hk1 : k + 1 = 2 := by
    have h3 : k ≤ 2 := by omega
    interval_cases k
    · exfalso
      norm_num at hsign
    · rfl
    · exfalso
      norm_num at hsign
  rw [hk, hk1]

theorem isConj_alternating_of_involution {n : ℕ} {σ τ : alternatingGroup (Fin n)}
    (hσ : orderOf σ = 2) (hc : IsConj (σ : Perm (Fin n)) (τ : Perm (Fin n))) : IsConj σ τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.mp hc
  have hσ1 : (σ : Perm (Fin n)) ≠ 1 := by
    intro h1
    have : σ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hσ2 : (σ : Perm (Fin n)) * (σ : Perm (Fin n)) = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ, pow_two] at h
    exact congrArg Subtype.val h
  obtain ⟨x, hx⟩ : ∃ x, (σ : Perm (Fin n)) x ≠ x := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have hxx : (σ : Perm (Fin n)) ((σ : Perm (Fin n)) x) = x := by
    have := congrArg (fun g : Perm (Fin n) => g x) hσ2
    simpa using this
  set ρ := swap x ((σ : Perm (Fin n)) x) with hρ
  have hρσ : (σ : Perm (Fin n)) * ρ * (σ : Perm (Fin n))⁻¹ = ρ := by
    rw [hρ, ← swap_apply_apply, hxx, swap_comm]
  have hsignρ : sign ρ = -1 := sign_swap (Ne.symm hx)
  rcases Int.units_eq_one_or (sign π) with h | h
  · exact isConj_iff.mpr ⟨⟨π, mem_alternatingGroup.mpr h⟩, Subtype.ext hπ⟩
  · refine isConj_iff.mpr ⟨⟨π * ρ, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_alternatingGroup, map_mul, h, hsignρ]
      rfl
    · have hρσ' : ρ * (σ : Perm (Fin n)) * ρ⁻¹ = σ := by
        have h1 : (σ : Perm (Fin n)) * ρ = ρ * σ := by
          calc (σ : Perm (Fin n)) * ρ = ((σ : Perm (Fin n)) * ρ * (σ : Perm (Fin n))⁻¹) * σ := by
                group
            _ = ρ * σ := by rw [hρσ]
        rw [← h1, mul_inv_cancel_right]
      show π * ρ * (σ : Perm (Fin n)) * (π * ρ)⁻¹ = τ
      calc π * ρ * (σ : Perm (Fin n)) * (π * ρ)⁻¹
          = π * (ρ * (σ : Perm (Fin n)) * ρ⁻¹) * π⁻¹ := by group
        _ = τ := by rw [hρσ', hπ]

theorem alternating_involutions_conj {n : ℕ} (hn : n ≤ 7) (s t : alternatingGroup (Fin n))
    (hs : orderOf s = 2) (ht : orderOf t = 2) :
    ∃ g : alternatingGroup (Fin n), g⁻¹ * s * g = t := by
  have hs' : orderOf (s : Perm (Fin n)) = 2 := by rw [Subgroup.orderOf_coe, hs]
  have ht' : orderOf (t : Perm (Fin n)) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hc : IsConj (s : Perm (Fin n)) (t : Perm (Fin n)) := by
    rw [isConj_iff_cycleType_eq, cycleType_of_involution_alternating hn s.2 hs',
      cycleType_of_involution_alternating hn t.2 ht']
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_alternating_of_involution hs hc)
  exact ⟨c⁻¹, by rw [inv_inv, hc]⟩

theorem lieModel_psl_two_involutions_conj {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hL : Blueprint.LieModel Y .PSL 2 p f) (s t : Y) (hs : orderOf s = 2) (ht : orderOf t = 2) :
    ∃ g : Y, g⁻¹ * s * g = t := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := GSLit.statedClassicalModel_of_lieModel_psl_two hL
  set e' : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm with he'
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩
  have hinv : ∀ y : Y, orderOf y = 2 → BenderSuzuki.PFAppendixIII.IsInvolution (e' y) := by
    intro y hy
    have hy' : orderOf (e' y) = 2 := by rw [MulEquiv.orderOf_eq, hy]
    refine ⟨fun h1 => ?_, by have h2 := pow_orderOf_eq_one (e' y); rwa [hy'] at h2⟩
    rw [h1, orderOf_one] at hy'
    exact absurd hy' (by norm_num)
  obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F hodd
    (e' s) (e' t) (hinv s hs) (hinv t ht)
  refine ⟨e'.symm g⁻¹, e'.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv, hg]

theorem cfSmallInv : CFSmallInv := by
  intro Y _ _ hY s t hs ht
  rcases hY with ⟨n, hn, ⟨e⟩⟩ | ⟨p, f, -, hp2, -, -, hL⟩
  · obtain ⟨g, hg⟩ := alternating_involutions_conj (by omega) (e s) (e t)
      (by rw [MulEquiv.orderOf_eq, hs]) (by rw [MulEquiv.orderOf_eq, ht])
    refine ⟨e.symm g, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
  · exact lieModel_psl_two_involutions_conj hp2 hL s t hs ht

end CFSG.ComponentClassification.GSThmB
