module

public import CFSG.GH74.GLS.IVK.Statements.Sec1A7
public import CFSG.GH74.GLS.IVK.A7.Core
public import CFSG.GH74.GLS.IVK.L2.NotationTransport
public import CFSG.RankThree.Literature.ThompsonDihedralProduct

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS Equiv Equiv.Perm

section Dihedral

theorem equiv_P0_dihedral :
    Nonempty (↥(A7.T0 ⊓ alternatingGroup (Fin 7)) ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρ4 : orderOf (A7.r * A7.f0) = 4 := by
    have h : orderOf (A7.r * A7.f0) = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 1) (by decide +kernel) (by decide +kernel)
    simpa using h
  have hσ2 : (A7.s * A7.f0) ^ 2 = 1 := by decide +kernel
  have hrel : (A7.s * A7.f0) * (A7.r * A7.f0) * (A7.s * A7.f0)⁻¹ = (A7.r * A7.f0)⁻¹ := by
    decide +kernel
  have hnot : (A7.s * A7.f0) ∉ zpowers (A7.r * A7.f0) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hc : (A7.s * A7.f0) * (A7.r * A7.f0) = (A7.r * A7.f0) * (A7.s * A7.f0) := by
      rw [← hk]
      exact ((Commute.refl (A7.r * A7.f0)).zpow_left k).eq
    exact absurd hc (by decide +kernel)
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup hσ2 hrel hnot
  rw [hρ4] at e
  have hle : closure ({A7.r * A7.f0, A7.s * A7.f0} : Set A7.S7) ≤
      A7.T0 ⊓ alternatingGroup (Fin 7) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hmem : ∀ y ∈ A7.P0list, y ∈ A7.T0 ⊓ alternatingGroup (Fin 7) := fun y hy =>
      ⟨A7.P0list_sub y hy, Equiv.Perm.mem_alternatingGroup.mpr (A7.P0list_even y hy)⟩
    rcases hx with rfl | rfl
    · exact hmem _ (by decide +kernel)
    · exact hmem _ (by decide +kernel)
  have hcard : Nat.card (closure ({A7.r * A7.f0, A7.s * A7.f0} : Set A7.S7)) = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcl : closure ({A7.r * A7.f0, A7.s * A7.f0} : Set A7.S7) =
      A7.T0 ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [A7.card_T0_inf_A7, hcard])
  exact ⟨(MulEquiv.subgroupCongr hcl.symm).trans e⟩

theorem equiv_D8_dihedral : Nonempty (A7.D8 ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρ4 : orderOf A7.r = 4 := by
    have h : orderOf A7.r = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 1) (by decide +kernel) (by decide +kernel)
    simpa using h
  have hσ2 : A7.s ^ 2 = 1 := by decide +kernel
  have hrel : A7.s * A7.r * A7.s⁻¹ = A7.r⁻¹ := by decide +kernel
  have hnot : A7.s ∉ zpowers A7.r := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hc : A7.s * A7.r = A7.r * A7.s := by
      rw [← hk]
      exact ((Commute.refl A7.r).zpow_left k).eq
    exact absurd hc (by decide +kernel)
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup hσ2 hrel hnot
  rw [hρ4] at e
  have hle : closure ({A7.r, A7.s} : Set A7.S7) ≤ A7.D8 := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · show _ ∈ A7.D8list
      decide +kernel
    · show _ ∈ A7.D8list
      decide +kernel
  have hcard : Nat.card (closure ({A7.r, A7.s} : Set A7.S7)) = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcl : closure ({A7.r, A7.s} : Set A7.S7) = A7.D8 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [A7.card_D8, hcard])
  exact ⟨(MulEquiv.subgroupCongr hcl.symm).trans e⟩

end Dihedral

section Proofs

theorem ivk_1_1T : IVK_1_1T := by
  intro T
  obtain ⟨f, h⟩ := A7.exists_split T
  exact ⟨f, h⟩

theorem ivk_1_1a : IVK_1_1a := by
  intro T
  obtain ⟨g, hg⟩ := A7.exists_conj_T0 T
  obtain ⟨e⟩ := equiv_P0_dihedral
  refine ⟨4, by norm_num, by norm_num, ⟨?_⟩⟩
  rw [A7.T_inf_A7_eq_map hg]
  exact (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e

theorem ivk_1_1b : IVK_1_1b := by
  intro T f hsplit z hzT hz2 hzc
  obtain ⟨g, hg⟩ := A7.exists_conj_T0 T
  obtain ⟨-, hcyc, hfT, -, hfc, -⟩ := hsplit
  have hf : f = g * A7.f0 * g⁻¹ := A7.split_unique hg hfT hcyc hfc
  have hz : z = g * A7.r ^ 2 * g⁻¹ := A7.central_involution_eq hg hzT hz2 hzc
  rw [hf, hz]
  exact A7.cycleType_fz g

theorem ivk_1_1c_a : IVK_1_1c_a := by
  intro T f hsplit
  obtain ⟨-, hcyc, -⟩ := hsplit
  exact A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr hcyc)

theorem ivk_1_1d : IVK_1_1d := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy hx2 hy2
    obtain ⟨c, hc, hcxy⟩ := A7.involutions_conj_alternating hx hy hx2 hy2
    exact ⟨c, hc, hcxy⟩
  · intro T z hzT hz2 hzc
    obtain ⟨g, hg⟩ := A7.exists_conj_T0 T
    obtain ⟨⟨e⟩, X, hX, hXT⟩ := A7.central_involution_data hg hzT hz2 hzc
    obtain ⟨eD⟩ := equiv_D8_dihedral
    exact ⟨⟨e.trans (MulEquiv.prodCongr eD (MulEquiv.refl _))⟩, X, hX, hXT⟩

theorem ivk_1_1g : IVK_1_1g := by
  intro u hu
  have hu2 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have hne : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  let H : Subgroup (Equiv.Perm (Fin 7)) :=
    centralizer ({u} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)
  have hub : ∀ r : ℕ, (∃ E : Subgroup ↥H, IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 2 ^ r) →
      r ≤ 2 := by
    rintro r ⟨E, hE, hcard⟩
    have hsq : ∀ x ∈ E.map H.subtype, x * x = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) a ha
      have h3 : a * a = 1 := by rw [← pow_two]; exact h2
      exact congrArg Subtype.val h3
    have hle : E.map H.subtype ≤ alternatingGroup (Fin 7) := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2.2
    have h4 := A7.card_le_four_of_sq_eq_one (E.map H.subtype) hle hsq
    rw [Subgroup.card_map_of_injective H.subtype_injective, hcard] at h4
    by_contra h
    push Not at h
    have h5 : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
    omega
  obtain ⟨E₀, hE₀le, hE₀c, hE₀s, hE₀card⟩ := A7.klein_in_centralizer u hu2 hne
  have hA : IsFourSubgroup (E₀.subgroupOf H) := by
    refine isFourSubgroup_of ?_ ?_ ?_
    · intro x hx y hy
      exact Subtype.ext (hE₀c x.1 hx y.1 hy)
    · intro x hx
      exact Subtype.ext (hE₀s x.1 hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀le).toEquiv]
      exact hE₀card
  have hmem : 2 ∈ {r : ℕ | ∃ E : Subgroup ↥H, IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 2 ^ r} :=
    ⟨E₀.subgroupOf H, hA.1, by rw [hA.2]; norm_num⟩
  have hbdd : BddAbove {r : ℕ | ∃ E : Subgroup ↥H, IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 2 ^ r} := ⟨2, fun r hr => hub r hr⟩
  show sSup {r : ℕ | ∃ E : Subgroup ↥H, IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 2 ^ r} = 2
  exact le_antisymm (csSup_le ⟨2, hmem⟩ (fun r hr => hub r hr)) (le_csSup hbdd hmem)

theorem ivk_1_1h : IVK_1_1h := by
  intro T f hsplit z hzT hz2 hzc
  exact A7.centralizer_A7_two_two_two_equiv (ivk_1_1b T f hsplit z hzT hz2 hzc)

theorem ivk_1_1f : IVK_1_1f := by
  intro U hUA hU4
  obtain ⟨hc, hs⟩ := isFourSubgroup_props hU4
  exact A7.shapeF_of_four U hUA hs hc hU4.2

end Proofs

end CFSG.GH74.GLS.IVK
