module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Orth

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.GLTheoremA.T263.SD
open scoped commutatorElement Pointwise

section Famsel

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem sdo_nontrivial_of_threeSingular
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) : Nontrivial V := by
  obtain ⟨U, hU, -⟩ := hT
  refine Module.nontrivial_of_finrank_pos (R := K) ?_
  have := Submodule.finrank_le U
  omega

theorem sdo_center_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Subgroup.center ↥(orthDerived Q) = ⊥ := by
  haveI := sdo_nontrivial_of_threeSingular hT
  obtain ⟨-, hcen, -⟩ := CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  rw [eq_bot_iff]
  intro z hz
  rw [hcen] at hz
  have h1 := CFSG.RankThree.PartOne.eq_one_of_mem_scalars_of_mem_orthDerived hQ z.2
    (Subgroup.mem_subgroupOf.1 hz)
  exact Subgroup.mem_bot.2 (Subtype.ext h1)

end Famsel

section Transfer

theorem sdo_transfer {G : Type*} [Group G] {p : ℕ} (Ω C : Subgroup G) (hCΩ : C ≤ Ω) (g : ↥Ω)
    (hCeq : C.subgroupOf Ω = Subgroup.centralizer ({g} : Set ↥Ω)) (B Y : Subgroup ↥Ω)
    (J : Subgroup G) (hJΩ : J ≤ Ω) (hJc : CFSG.Open.IsComponentOf J C)
    (hJp : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJne : ⁅⁅B.map Ω.subtype, Y.map Ω.subtype⁆, J⁆ ≠ ⊥)
    (hJle : ⁅B.map Ω.subtype, Y.map Ω.subtype⁆ ≤ J ⊔ (C ⊓ Subgroup.centralizer (J : Set G))) :
    ∃ J' : Subgroup ↥Ω, CFSG.Open.IsComponentOf J' (Subgroup.centralizer ({g} : Set ↥Ω)) ∧
      p ∣ Nat.card (↥J' ⧸ Subgroup.center ↥J') ∧ ⁅⁅B, Y⁆, J'⁆ ≠ ⊥ ∧
      ⁅B, Y⁆ ≤ J' ⊔ (Subgroup.centralizer ({g} : Set ↥Ω) ⊓ Subgroup.centralizer (J' : Set ↥Ω)) := by
  have hmapJ : (J.subgroupOf Ω).map Ω.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJΩ
  refine ⟨J.subgroupOf Ω, ?_, ?_, ?_, ?_⟩
  · rw [← hCeq]
    exact ⟨Subgroup.subgroupOf_mono Ω hJc.1, sdo_isSubnormal_subgroupOf Ω hJc.2.1,
      sdo_isQuasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hJΩ).symm hJc.2.2⟩
  · rw [sdo_card_quot_center_congr (Subgroup.subgroupOfEquivOfLe hJΩ)]
    exact hJp
  · intro h
    apply hJne
    have h1 : (⁅⁅B, Y⁆, J.subgroupOf Ω⁆).map Ω.subtype =
        ⁅⁅B.map Ω.subtype, Y.map Ω.subtype⁆, J⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator, hmapJ]
    rw [← h1, h, Subgroup.map_bot]
  · intro r hr
    have hr' : (r : G) ∈ ⁅B.map Ω.subtype, Y.map Ω.subtype⁆ := by
      rw [← Subgroup.map_commutator]
      exact ⟨r, hr, rfl⟩
    have h2 := hJle hr'
    have hnorm : (Subgroup.centralizer (J : Set G)) ≤ Subgroup.normalizer (J : Set G) :=
      Subgroup.centralizer_le_normalizer _
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left J
      (C ⊓ Subgroup.centralizer (J : Set G)) (inf_le_right.trans hnorm)
    have h3 : (r : G) ∈ (J : Set G) *
        ((C ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G) := by
      rw [← hmul]
      exact h2
    obtain ⟨a, ha, c, hc, hrac⟩ := h3
    have hcC : c ∈ C := (Subgroup.mem_inf.1 hc).1
    have hcΩ : c ∈ Ω := hCΩ hcC
    have haP : (⟨a, hJΩ ha⟩ : ↥Ω) ∈ J.subgroupOf Ω := Subgroup.mem_subgroupOf.2 ha
    have hcP : (⟨c, hcΩ⟩ : ↥Ω) ∈ Subgroup.centralizer ({g} : Set ↥Ω) ⊓
        Subgroup.centralizer ((J.subgroupOf Ω : Subgroup ↥Ω) : Set ↥Ω) := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [← hCeq]
        exact Subgroup.mem_subgroupOf.2 hcC
      · rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 (j : G) hjJ
    have hrP : r = (⟨a, hJΩ ha⟩ : ↥Ω) * ⟨c, hcΩ⟩ := Subtype.ext hrac.symm
    rw [hrP]
    exact Subgroup.mul_mem_sup haP hcP

end Transfer

section Famsel2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem famSelOrth_holds : FamSelOrth := by
  intro p hp hp2 K _ _ _ V _ _ _ Q hQ hT hK3
  refine sdo_famSel_of_elements p (sdo_center_orthDerived hQ hT) ?_
  intro g hgp hg1 B hB Y hYc hY2 hYB hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hpl : p ≠ ringChar K := by
    rw [ringChar.eq K 2]
    exact hp2
  have hx : OddOrderIsometry Q p ((g : ↥(orthDerived Q)) : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ g hord
  have hmem : ∀ h : ↥(orthDerived Q), h * g = g * h →
      (h : V ≃ₗ[K] V) ∈ isometryCentralizer Q ((g : ↥(orthDerived Q)) : V ≃ₗ[K] V) ⊓ orthDerived Q := by
    intro h hh
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨orthDerived_le_orthogonalGroup h.2, ?_⟩, h.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hh
  have hBC : B.map (orthDerived Q).subtype ≤
      isometryCentralizer Q ((g : ↥(orthDerived Q)) : V ≃ₗ[K] V) ⊓ orthDerived Q := by
    rintro _ ⟨b, hb, rfl⟩
    exact hmem b (hB b hb).2
  have hYC : Y.map (orthDerived Q).subtype ≤
      isometryCentralizer Q ((g : ↥(orthDerived Q)) : V ≃ₗ[K] V) ⊓ orthDerived Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact hmem y (Subgroup.mem_centralizer_singleton_iff.1 (hYc hy))
  have hBp : ∀ z ∈ B.map (orthDerived Q).subtype, z ^ p = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have := congrArg Subtype.val (hB b hb).1
    simpa using this
  have hY2' : ∀ z ∈ Y.map (orthDerived Q).subtype, ∃ n : ℕ, z ^ 2 ^ n = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hY2 ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have h1 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hYB' : ∀ b ∈ B.map (orthDerived Q).subtype, ∀ y ∈ Y.map (orthDerived Q).subtype,
      b * y * b⁻¹ ∈ Y.map (orthDerived Q).subtype := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨b * y * b⁻¹, hYB b hb y hy, by simp⟩
  have hne' : ⁅B.map (orthDerived Q).subtype, Y.map (orthDerived Q).subtype⁆ ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_commutator] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (orthDerived Q).subtype_injective).1 h
  obtain ⟨J, hJc, hJΩ, hJp, hJne, hJle⟩ := sdo_ambient hQ hp hp2 hK3 hx
    (B.map (orthDerived Q).subtype) (Y.map (orthDerived Q).subtype) hBC hYC hBp hY2' hYB' hne'
  have hCeq : (isometryCentralizer Q ((g : ↥(orthDerived Q)) : V ≃ₗ[K] V) ⊓ orthDerived Q).subgroupOf
      (orthDerived Q) = Subgroup.centralizer ({g} : Set ↥(orthDerived Q)) := by
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hh
      have := Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).2
      exact Subtype.ext this
    · intro hh
      exact hmem h hh
  exact sdo_transfer (orthDerived Q) _ inf_le_right g hCeq B Y J hJΩ hJc hJp hJne hJle

end Famsel2

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Orth

end
