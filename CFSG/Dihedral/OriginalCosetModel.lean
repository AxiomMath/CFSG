module

public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.Dihedral.GorensteinWalter.ASevenNormalizerCosetData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerThreeCycle
public import CFSG.Dihedral.OriginalFourgroupsGeneral

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem aSeven_equiv_aligned (e : G ≃* alternatingGroup (Fin 7)) :
    ∃ f : G ≃* alternatingGroup (Fin 7), f d.t = a7t := by
  have ht := d.t_isInvolution_general
  have hte : BenderSuzuki.PFAppendixIII.IsInvolution (e d.t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact ht.1 (e.injective (by simpa using h))
    · simpa using congrArg e ht.2
  obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (e d.t) a7t hte a7t_involution
  exact ⟨e.trans (MulAut.conj g), hg⟩

omit [Finite G] in
theorem group_card_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7)) :
    Nat.card G = 2520 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

theorem n_eq_three_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7)) : d.n = 3 := by
  have h := d.S.card_eq_multiplicity
  change Nat.card (d.S : Subgroup G) = _ at h
  rw [d.order_S, group_card_of_aSeven_model e] at h
  have hfactor : (2520 : ℕ).factorization 2 = 3 := by
    have hprod : 2520 = 2 ^ 3 * 315 := by decide
    rw [hprod, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 315)]
  rw [hfactor] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h

theorem R_card_of_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) : Nat.card d.R = 3 := by
  have ht := d.t_isInvolution_general
  have hte : BenderSuzuki.PFAppendixIII.IsInvolution (e d.t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact ht.1 (e.injective (by simpa using h))
    · simpa using congrArg e ht.2
  have hcent : d.R.map e.toMonoidHom ≤
      Subgroup.centralizer ({e d.t} : Set (alternatingGroup (Fin 7))) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxC : x ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.R_le hx
    simpa using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have hodd : Odd (Nat.card (d.R.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact d.R_odd
  have hle := aSeven_odd_subgroup_centralizing_involution_card_le_three hodd hte hcent
  rw [Subgroup.card_map_of_injective e.injective] at hle
  have hne : Nat.card d.R ≠ 1 := by
    intro h
    exact hR (d.R.eq_bot_of_card_eq h)
  have hpos : 0 < Nat.card d.R := Nat.card_pos
  obtain ⟨k, hk⟩ := d.R_odd
  omega

theorem commonE_eq_bot_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7)) :
    d.commonE = ⊥ := by
  have hodd : Odd (Nat.card d.commonE) :=
    d.R_odd.of_dvd_nat (Subgroup.card_dvd_of_le (show d.commonE ≤ d.R from inf_le_left))
  have hker := a7rho_centralizer_odd_trivial_of_sylow_image e.toMonoidHom
    d.commonE (d.S : Subgroup G) hodd inf_le_right
    (d.S.mapSurjective e.surjective) (Sylow.coe_mapSurjective e.surjective d.S).symm
  apply le_antisymm _ bot_le
  rw [e.toMonoidHom.ker_eq_bot e.injective] at hker
  exact hker

theorem R_map_eq_a7U (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7))
    (ht : e d.t = a7t) : d.R.map e.toMonoidHom = a7U := by
  have hcent : d.R.map e.toMonoidHom ≤
      Subgroup.centralizer ({a7t} : Set (alternatingGroup (Fin 7))) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e x * a7t = a7t * e x
    have hxC : x ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.R_le hx
    simpa only [map_mul, ht] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have hodd : ∀ x : alternatingGroup (Fin 7), x ∈ d.R.map e.toMonoidHom →
      Odd (orderOf x) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    change Odd (orderOf (e r))
    rw [e.orderOf_eq]
    exact d.R_odd.of_dvd_nat (d.R.orderOf_dvd_natCard hr)
  have hle := aSeven_odd_subgroup_centralizing_a7t_le_zpowers hodd hcent
  rw [← a7U_eq_zpowers] at hle
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective e.injective, d.R_card_of_aSeven_model hR e,
    aSeven_structure_fact_1_8_ii_centralizer.1]

end CFSG.DihedralBlueprint.OriginalData
