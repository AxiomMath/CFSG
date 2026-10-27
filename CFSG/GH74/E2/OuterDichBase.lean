
module

public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.SectionalRank
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateEquiv
public meta import Mathlib
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

@[expose] public section

namespace CFSG.GH74.E2

open Subgroup

theorem isCyclic_of_rank_le_one_aux {A : Type*} [Group A] [Finite A] (h : Group.rank A ≤ 1) :
    IsCyclic A := by
  obtain ⟨s, hs, hcl⟩ := Group.rank_spec A
  obtain ⟨x, hx⟩ := Finset.card_le_one_iff_subset_singleton.mp (hs ▸ h : s.card ≤ 1)
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨x, top_unique ?_⟩
  rw [← hcl, Subgroup.zpowers_eq_closure]
  refine Subgroup.closure_mono fun y hy => ?_
  have := hx hy
  simpa using this

theorem not_isCyclic_of_three_sq {A : Type*} [Group A] [Finite A] {a b : A}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ¬ IsCyclic A := by
  intro hcyc
  classical
  have := Fintype.ofFinite A
  have hcard := IsCyclic.card_pow_eq_one_le (α := A) (n := 2) (by norm_num)
  have h3 : ({1, a, b} : Finset A) ⊆ Finset.univ.filter (fun x : A => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rw [pow_two]; exact ha
    · rw [pow_two]; exact hb
  have h3c : ({1, a, b} : Finset A).card = 3 :=
    Finset.card_eq_three.2 ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have := Finset.card_le_card h3
  omega

theorem dich_case_A {S : Type*} [Group S] [Finite S] (hS : Gen4 S) (hS2 : IsPGroup 2 S)
    {Q T : Subgroup S} (hQn : Q.Normal) (hTn : T.Normal) {q₁ q₂ : S} (hq₁ : q₁ ∈ Q)
    (hq₂ : q₂ ∈ Q) (hsq₁ : q₁ * q₁ ∈ Subgroup.centralizer (Q : Set S))
    (hsq₂ : q₂ * q₂ ∈ Subgroup.centralizer (Q : Set S)) (hnc : q₁ * q₂ ≠ q₂ * q₁)
    (hA : ∀ x : S, ∃ y ∈ T, y⁻¹ * x ∈ Subgroup.centralizer (Q : Set S)) :
    Group.rank (S ⧸ T) ≤ 2 := by
  classical
  set R : Subgroup S := Subgroup.centralizer (Q : Set S) with hR
  have hRn : R.Normal := by
    refine ⟨fun r hr g => ?_⟩
    rw [hR, Subgroup.mem_centralizer_iff] at hr ⊢
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      simpa using hQn.conj_mem q hq g⁻¹
    have := hr _ hq'
    calc q * (g * r * g⁻¹) = g * ((g⁻¹ * q * g) * r) * g⁻¹ := by group
      _ = g * (r * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
      _ = (g * r * g⁻¹) * q := by group
  by_contra hrk
  push Not at hrk
  have := hTn
  have := hRn
  let f : S →* (S ⧸ T) × (S ⧸ R) := (QuotientGroup.mk' T).prod (QuotientGroup.mk' R)
  have hf : Function.Surjective f := by
    rintro ⟨a, b⟩
    obtain ⟨a0, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b0, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨y₁, hy₁, hr₁⟩ := hA a0
    obtain ⟨y, hy, hr⟩ := hA b0
    refine ⟨y * (y₁⁻¹ * a0), ?_⟩
    refine Prod.ext ?_ ?_
    · show QuotientGroup.mk (y * (y₁⁻¹ * a0)) = QuotientGroup.mk a0
      rw [QuotientGroup.eq]
      have h1 : (y * (y₁⁻¹ * a0))⁻¹ * a0 = (y₁⁻¹ * a0)⁻¹ * (y⁻¹ * y₁) * (y₁⁻¹ * a0) := by group
      rw [h1]
      have h2 := hTn.conj_mem (y⁻¹ * y₁) (T.mul_mem (T.inv_mem hy) hy₁) (y₁⁻¹ * a0)⁻¹
      rwa [inv_inv] at h2
    · show QuotientGroup.mk (y * (y₁⁻¹ * a0)) = QuotientGroup.mk b0
      rw [QuotientGroup.eq]
      have h1 : (y * (y₁⁻¹ * a0))⁻¹ * b0 = (y₁⁻¹ * a0)⁻¹ * (y⁻¹ * b0) := by group
      rw [h1]
      exact R.mul_mem (R.inv_mem hr₁) hr
  have h4 : Group.rank S ≤ 4 := by
    have hTop : IsPGroup 2 (⊤ : Subgroup S) := hS2.of_equiv Subgroup.topEquiv.symm
    have := Gen4.rank_le_four hS hTop
    rwa [Group.rank_congr (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S)] at this
  have h5 := Group.rank_le_of_surjective f hf
  have hT2 : IsPGroup 2 (S ⧸ T) := hS2.to_quotient T
  have hR2 : IsPGroup 2 (S ⧸ R) := hS2.to_quotient R
  have h6 := rank_add_le_rank_prod hT2 hR2
  have h7 : 2 ≤ Group.rank (S ⧸ R) := by
    by_contra h
    push Not at h
    have hcyc := isCyclic_of_rank_le_one_aux (by omega : Group.rank (S ⧸ R) ≤ 1)
    have hq₁R : q₁ ∉ R := fun h => hnc (by
      have := (Subgroup.mem_centralizer_iff.1 h) q₂ hq₂
      exact this.symm)
    have hq₂R : q₂ ∉ R := fun h => hnc (by
      have := (Subgroup.mem_centralizer_iff.1 h) q₁ hq₁
      exact this)
    have hq₁₂R : q₁⁻¹ * q₂ ∉ R := fun h => hnc (by
      have this := (Subgroup.mem_centralizer_iff.1 h) q₁ hq₁
      have e : q₁⁻¹ * q₂ * q₁ = q₂ := by
        calc q₁⁻¹ * q₂ * q₁ = q₁ * (q₁⁻¹ * q₂) := this.symm
          _ = q₂ := by group
      calc q₁ * q₂ = q₁ * (q₁⁻¹ * q₂ * q₁) := by rw [e]
        _ = q₂ * q₁ := by group)
    refine not_isCyclic_of_three_sq (a := (QuotientGroup.mk q₁ : S ⧸ R))
      (b := (QuotientGroup.mk q₂ : S ⧸ R)) ?_ ?_ ?_ ?_ ?_ hcyc
    · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]; exact hsq₁
    · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]; exact hsq₂
    · rwa [Ne, QuotientGroup.eq_one_iff]
    · rwa [Ne, QuotientGroup.eq_one_iff]
    · intro h
      exact hq₁₂R (QuotientGroup.eq.1 h)
  omega

theorem exists_noncomm_sq_central {S : Type*} [Group S] {Q : Subgroup S}
    (e : ↥Q ≃* QuaternionGroup 2) :
    ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₁ ∈ Subgroup.centralizer (Q : Set S) ∧
      q₂ * q₂ ∈ Subgroup.centralizer (Q : Set S) ∧ q₁ * q₂ ≠ q₂ * q₁ := by
  have h1 : ∀ y : QuaternionGroup 2, y * (QuaternionGroup.a 1 * QuaternionGroup.a 1) =
      (QuaternionGroup.a 1 * QuaternionGroup.a 1) * y := by decide
  have h2 : ∀ y : QuaternionGroup 2, y * (QuaternionGroup.xa 0 * QuaternionGroup.xa 0) =
      (QuaternionGroup.xa 0 * QuaternionGroup.xa 0) * y := by decide
  have h3 : QuaternionGroup.a 1 * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * (QuaternionGroup.a 1 : QuaternionGroup 2) := by decide
  refine ⟨(e.symm (QuaternionGroup.a 1) : S), (e.symm _).2, (e.symm (QuaternionGroup.xa 0) : S),
    (e.symm _).2, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨y, hy⟩ := e.symm.surjective ⟨q, hq⟩
    have := congrArg (fun z : ↥Q => (z : S)) (show e.symm (y * (QuaternionGroup.a 1 *
      QuaternionGroup.a 1)) = e.symm ((QuaternionGroup.a 1 * QuaternionGroup.a 1) * y) by
        rw [h1 y])
    simp only [map_mul, Subgroup.coe_mul, hy] at this
    exact this
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨y, hy⟩ := e.symm.surjective ⟨q, hq⟩
    have := congrArg (fun z : ↥Q => (z : S)) (show e.symm (y * (QuaternionGroup.xa 0 *
      QuaternionGroup.xa 0)) = e.symm ((QuaternionGroup.xa 0 * QuaternionGroup.xa 0) * y) by
        rw [h2 y])
    simp only [map_mul, Subgroup.coe_mul, hy] at this
    exact this
  · intro h
    apply h3
    have h5 : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
        e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext h
    have h4 := congrArg e h5
    simpa using h4

theorem dich_case_A_q8 {S : Type*} [Group S] [Finite S] (hS : Gen4 S) (hS2 : IsPGroup 2 S)
    {Q T : Subgroup S} (hQn : Q.Normal) (hTn : T.Normal)
    (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2))
    (hA : ∀ x : S, ∃ y ∈ T, y⁻¹ * x ∈ Subgroup.centralizer (Q : Set S)) :
    Group.rank (S ⧸ T) ≤ 2 := by
  obtain ⟨e⟩ := hQ8
  obtain ⟨q₁, h1, q₂, h2, hs1, hs2, hnc⟩ := exists_noncomm_sq_central e
  exact dich_case_A hS hS2 hQn hTn h1 h2 hs1 hs2 hnc hA

end CFSG.GH74.E2
