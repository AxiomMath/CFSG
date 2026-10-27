module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem card_fixedBy_quotient_subgroupOf_normalizer_eq_one {G : Type*} [Group G]
    [Finite G] {T X : Subgroup G} (hTX : T ≤ X) (hT : Odd (Nat.card T))
    (hodd : ∀ m ∈ X, m ∈ Subgroup.normalizer (T : Set G) → Odd (orderOf m) → m ∈ T)
    (hti : ∀ x ∈ X, T ⊓ T.map (MulAut.conj x).toMonoidHom ≠ ⊥ →
      x ∈ Subgroup.normalizer (T : Set G))
    {g : T.subgroupOf X} (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy
      ((↥X) ⧸ (Subgroup.normalizer (T : Set G)).subgroupOf X) g) = 1 := by
  classical
  have hle : T.subgroupOf X ≤ (Subgroup.normalizer (T : Set G)).subgroupOf X :=
    Subgroup.subgroupOf_mono X T.le_normalizer
  refine Nat.card_eq_one_iff_exists.mpr
    ⟨⟨QuotientGroup.mk (1 : X), ?_⟩, fun y => ?_⟩
  · rw [MulAction.mem_fixedBy, Subgroup.smul_def, MulAction.Quotient.smul_mk,
      QuotientGroup.eq]
    simpa using inv_mem (hle g.2)
  · have hy : g • y.1 = y.1 := MulAction.mem_fixedBy.mp y.2
    obtain ⟨x, hx⟩ : ∃ x : X, QuotientGroup.mk x = y.1 :=
      ⟨y.1.out, QuotientGroup.out_eq' y.1⟩
    rw [← hx, Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul,
      QuotientGroup.eq] at hy
    have hmem : x⁻¹ * ((g : X) : G) * x ∈ Subgroup.normalizer (T : Set G) := by
      have h' := Subgroup.mem_subgroupOf.mp hy
      have heq : ((((g : X) * x)⁻¹ * x : X) : G) = x⁻¹ * ((g : X) : G)⁻¹ * x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq] at h'
      have h'' := inv_mem h'
      rwa [show (x⁻¹ * ((g : X) : G)⁻¹ * x)⁻¹ = x⁻¹ * ((g : X) : G) * x by
        simp only [Subgroup.coe_inv]
        group] at h''
    have hxX : (x : G) ∈ X := x.2
    have hgT : ((g : X) : G) ∈ T := Subgroup.mem_subgroupOf.mp g.2
    have hmX : x⁻¹ * ((g : X) : G) * x ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem hxX) (hTX hgT)) hxX
    have hodd_g : Odd (orderOf ((g : X) : G)) :=
      Odd.of_dvd_nat hT (Subgroup.orderOf_dvd_natCard T hgT)
    have hodd_conj : Odd (orderOf (x⁻¹ * ((g : X) : G) * x)) := by
      rw [← SemiconjBy.orderOf_eq (a := (x : G)⁻¹)
        (show SemiconjBy (x : G)⁻¹ ((g : X) : G) (x⁻¹ * ((g : X) : G) * x) from by
          unfold SemiconjBy
          simp only [Subgroup.coe_inv]
          group)]
      exact hodd_g
    have hmT : x⁻¹ * ((g : X) : G) * x ∈ T := hodd _ hmX hmem hodd_conj
    have hg_inf : ((g : X) : G) ∈
        T ⊓ T.map (MulAut.conj (x : G)).toMonoidHom := by
      refine ⟨hgT, ?_⟩
      change ((g : X) : G) ∈ Subgroup.map (MulAut.conj (x : G)).toMonoidHom T
      rw [Subgroup.mem_map]
      refine ⟨x⁻¹ * ((g : X) : G) * x, hmT, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_inv]
      group
    have hg1 : ((g : X) : G) ≠ 1 := by
      intro h
      exact hg (Subtype.ext (Subtype.ext h))
    have hne : T ⊓ T.map (MulAut.conj (x : G)).toMonoidHom ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hg_inf
      exact hg1 hg_inf
    have hxN : (x : G) ∈ Subgroup.normalizer (T : Set G) := hti (x : G) hxX hne
    have hxM : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr hxN
    have hq : (QuotientGroup.mk x :
        (↥X) ⧸ (Subgroup.normalizer (T : Set G)).subgroupOf X) =
        QuotientGroup.mk (1 : X) := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hxM
    exact Subtype.ext (by rw [← hx, hq])

theorem index_normalizer_modEq_one {G : Type*} [Group G] [Finite G] {T X : Subgroup G}
    (hTX : T ≤ X) (hT : Odd (Nat.card T))
    (hodd : ∀ m ∈ X, m ∈ Subgroup.normalizer (T : Set G) → Odd (orderOf m) → m ∈ T)
    (hti : ∀ x ∈ X, T ⊓ T.map (MulAut.conj x).toMonoidHom ≠ ⊥ →
      x ∈ Subgroup.normalizer (T : Set G)) :
    ((Subgroup.normalizer (T : Set G)).subgroupOf X).index ≡ 1 [MOD Nat.card T] := by
  classical
  let S : Subgroup X := T.subgroupOf X
  let M : Subgroup X := (Subgroup.normalizer (T : Set G)).subgroupOf X
  let Ω := (↥X) ⧸ M
  have hST : Nat.card S = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv
  have hfixone : Nat.card (MulAction.fixedBy Ω (1 : S)) = Nat.card Ω := by
    rw [show MulAction.fixedBy Ω (1 : S) = Set.univ by
      ext q
      simp, Nat.card_univ]
  have hfixne : ∀ g : S, g ≠ 1 → Nat.card (MulAction.fixedBy Ω g) = 1 :=
    fun g hg => card_fixedBy_quotient_subgroupOf_normalizer_eq_one hTX hT hodd hti hg
  have : Fintype S := Fintype.ofFinite S
  have : ∀ g : S, Fintype (MulAction.fixedBy Ω g) := fun _ => Fintype.ofFinite _
  have : Fintype (Quotient (MulAction.orbitRel S Ω)) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group S Ω
  simp only [← Nat.card_eq_fintype_card] at hB
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : S)), hfixone,
    Finset.sum_congr rfl fun g hg => hfixne g (Finset.ne_of_mem_erase hg),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hST, smul_eq_mul, mul_one, mul_comm] at hB
  have hΩ1 : 1 ≤ Nat.card Ω := Nat.card_pos
  have hT1 : 1 ≤ Nat.card T := Nat.card_pos
  change Nat.card Ω ≡ 1 [MOD Nat.card T]
  refine ((Nat.modEq_iff_dvd' hΩ1).mpr
    ⟨Nat.card (Quotient (MulAction.orbitRel S Ω)) - 1, ?_⟩).symm
  rw [Nat.mul_sub_one]
  generalize Nat.card T * Nat.card (Quotient (MulAction.orbitRel S Ω)) = X at hB ⊢
  generalize Nat.card T = q at hB hT1 ⊢
  omega

end CFSG.GroupTheory

end
