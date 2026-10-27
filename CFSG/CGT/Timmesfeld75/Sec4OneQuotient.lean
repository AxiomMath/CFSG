module

public import CFSG.CGT.Timmesfeld75.L2FixedSylow
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Quotient

variable {G : Type} [Group G]

theorem conjSubgroup_map_subgroupOf (X N U : Subgroup G) [(N.subgroupOf X).Normal] (g : ↥X) :
    conjSubgroup (QuotientGroup.mk g : ↥X ⧸ N.subgroupOf X)
        ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) =
      ((conjSubgroup (g : G) U).subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
  rw [← conjSubgroup_subgroupOf]
  exact (map_conjSubgroup (QuotientGroup.mk' (N.subgroupOf X)) g (U.subgroupOf X)).symm

theorem exists_mul_of_map_le {X N V : Subgroup G} [(N.subgroupOf X).Normal] {a : G}
    (haX : a ∈ Subgroup.normalizer (X : Set G))
    (φ : ↥X ⧸ N.subgroupOf X ≃* ↥X ⧸ N.subgroupOf X)
    (hφ : ∀ y : ↥X, φ (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.1 haX y).1 y.2⟩ : ↥X))
    (hV : V ≤ X)
    (hfix : ((V.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))).map φ.toMonoidHom =
      (V.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) :
    ∀ u ∈ V, ∃ u' ∈ V, ∃ n ∈ N, a * u * a⁻¹ = u' * n := by
  intro u hu
  have huX : u ∈ X := hV hu
  have hmem : φ (QuotientGroup.mk (⟨u, huX⟩ : ↥X)) ∈
      (V.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    rw [← hfix]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hu))
  obtain ⟨w, hw, hwφ⟩ := hmem
  rw [hφ] at hwφ
  have h1 := QuotientGroup.eq.1 hwφ
  have h2 : (w : G)⁻¹ * (a * u * a⁻¹) ∈ N := Subgroup.mem_subgroupOf.1 h1
  refine ⟨(w : G), Subgroup.mem_subgroupOf.1 hw, (w : G)⁻¹ * (a * u * a⁻¹), h2, ?_⟩
  group

theorem exists_fixed_conj_of_involution {X N U : Subgroup G} [(N.subgroupOf X).Normal] {q : ℕ}
    (hUX : U ≤ X)
    (hpair : IsL2Pair (↥X ⧸ N.subgroupOf X)
      ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) q)
    {a : G} (haa : a * a = 1) (haX : a ∈ Subgroup.normalizer (X : Set G))
    (haN : a ∈ Subgroup.normalizer (N : Set G)) :
    ∃ g ∈ X, ∀ u ∈ conjSubgroup g U, ∃ u' ∈ conjSubgroup g U, ∃ n ∈ N,
      a * u * a⁻¹ = u' * n := by
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := X) (N := N) haX haN
  have hφφ := quotient_conj_equiv_involutive haX haa φ hφ
  have := hpair.finite
  obtain ⟨P, hP⟩ := exists_fixed_sylow_of_involutive φ hφφ
  obtain ⟨gb, hgb⟩ := hpair.exists_conj_eq_sylow P
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  refine ⟨(g : G), g.2, ?_⟩
  have hPimg : (P : Subgroup (↥X ⧸ N.subgroupOf X)) =
      ((conjSubgroup (g : G) U).subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    rw [← hgb]
    exact conjSubgroup_map_subgroupOf X N U g
  refine exists_mul_of_map_le haX φ hφ (conjSubgroup_le_of_le_of_mem hUX g.2) ?_
  rw [← hPimg]
  exact hP

theorem exists_inner_of_unique_fixed {X N U : Subgroup G} [hN : (N.subgroupOf X).Normal] {q : ℕ}
    (hNX : N ≤ X) (hUX : U ≤ X)
    (hpair : IsL2Pair (↥X ⧸ N.subgroupOf X)
      ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) q)
    {a : G} (haa : a * a = 1) (haX : a ∈ Subgroup.normalizer (X : Set G))
    (haN : a ∈ Subgroup.normalizer (N : Set G)) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (huniq : ∀ g ∈ X, (∀ u ∈ conjSubgroup g U, ∃ u' ∈ conjSubgroup g U, ∃ n ∈ N,
      a * u * a⁻¹ = u' * n) → conjSubgroup g U = U) :
    ∃ t ∈ U, t ∉ N ∧ ∀ x ∈ X, (t⁻¹ * a) * x * (t⁻¹ * a)⁻¹ * x⁻¹ ∈ N := by
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := X) (N := N) haX haN
  have hφφ := quotient_conj_equiv_involutive haX haa φ hφ
  have hφU := map_quotient_conj_equiv haX haU haa φ hφ
  have huniq' : ∀ gb : ↥X ⧸ N.subgroupOf X,
      (conjSubgroup gb ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)))).map
          φ.toMonoidHom =
        conjSubgroup gb ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) →
      conjSubgroup gb ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) =
        (U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    intro gb hgb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    rw [conjSubgroup_map_subgroupOf] at hgb ⊢
    have hU' := huniq (g : G) g.2 (exists_mul_of_map_le haX φ hφ
      (conjSubgroup_le_of_le_of_mem hUX g.2) hgb)
    rw [hU']
  obtain ⟨tb, htb, htb1, htb'⟩ :=
    hpair.exists_involution_of_unique_fixed φ hφφ hφU huniq'
  obtain ⟨t', ht', rfl⟩ := htb
  have htU : (t' : G) ∈ U := Subgroup.mem_subgroupOf.1 ht'
  refine ⟨(t' : G), htU, fun htN => htb1 ?_, fun x hx => ?_⟩
  · exact (QuotientGroup.eq_one_iff t').2 (Subgroup.mem_subgroupOf.2 htN)
  · have h1 := htb' (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
    rw [hφ] at h1
    have h2 := QuotientGroup.eq.1 (h1.trans (rfl :
      (QuotientGroup.mk' (N.subgroupOf X) t' * QuotientGroup.mk (⟨x, hx⟩ : ↥X) *
          (QuotientGroup.mk' (N.subgroupOf X) t')⁻¹ : ↥X ⧸ N.subgroupOf X) =
        QuotientGroup.mk (t' * ⟨x, hx⟩ * t'⁻¹)))
    have h3 : (a * x * a⁻¹)⁻¹ * ((t' : G) * x * (t' : G)⁻¹) ∈ N := Subgroup.mem_subgroupOf.1 h2
    have hxt : x * (t' : G)⁻¹ ∈ X := X.mul_mem hx (X.inv_mem t'.2)
    have hXN : X ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).1 hN
    have h4 := (Subgroup.mem_normalizer_iff.1 (hXN hxt) _).1 (N.inv_mem h3)
    have e : ((t' : G)⁻¹ * a) * x * ((t' : G)⁻¹ * a)⁻¹ * x⁻¹ =
        (x * (t' : G)⁻¹) * ((a * x * a⁻¹)⁻¹ * ((t' : G) * x * (t' : G)⁻¹))⁻¹ *
          (x * (t' : G)⁻¹)⁻¹ := by
      group
    rw [e]
    exact h4

end Quotient

end CFSG.CGT.Timmesfeld75
