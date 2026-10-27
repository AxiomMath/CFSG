module

public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth_commutator_centralizer_le_of_blocks
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (x : orthDerived Q) (hxp : orderOf x = p) (F : Subgroup (ProjOrthDerived Q))
    (hspec : ∀ Rep : Finset K[X], IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep →
      ∀ h ∈ Rep, h ≠ X - 1 → 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
        componentImage Q (x : V ≃ₗ[K] V) h ≤ F)
    (hfix : 3 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V)) →
      fixedComponentImage Q (x : V ≃ₗ[K] V) ≤ F) :
    ⁅Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} : Set (ProjOrthDerived Q)),
      Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q))⁆ ≤ F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  set a : ProjOrthDerived Q := QuotientGroup.mk x with ha_def
  have ha : orderOf a = p := by
    have h1 : a ^ p = 1 := by
      rw [ha_def, ← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one, QuotientGroup.mk_one]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h2 | h2
    · exfalso
      have ha1 : a = 1 := orderOf_eq_one_iff.mp h2
      obtain ⟨-, -, hZ, -⟩ :=
        CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
      have hxZ : x ∈ (CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q) :=
        (QuotientGroup.eq_one_iff x).mp ha1
      have hdvd : p ∣ Nat.card ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
          (orthDerived Q)) := by
        rw [← hxp]
        exact Subgroup.orderOf_dvd_natCard _ hxZ
      have hpos : 0 < Nat.card ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
          (orthDerived Q)) := Nat.card_pos
      have := Nat.le_of_dvd hpos hdvd
      omega
    · exact h2
  obtain ⟨⟨Rep0, hRep0⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range le_rfl a ha x rfl hxp
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))
    with hN
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
    with hρ
  set Mo : Subgroup ↥(orthDerived Q) := (isometryCentralizer Q xe).subgroupOf (orthDerived Q)
    with hMo
  obtain ⟨hNeq, -, -, -, -, hspecK, -, -⟩ := hmain Rep0 hRep0
  have hbot : ∀ h ∈ Rep0, ¬ 2 ≤ primaryMultiplicity xe.toLinearMap h → specialBlock Q xe h = ⊥ := by
    intro h hh hm
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep0.1 hh)⟩
    have hpos := hx.primaryMultiplicity_pos (hRep0.1 hh)
    have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
    exact hx.specialBlock_eq_bot_of_finrank_eq_one (hRep0.1 hh) h1
  have hspecΩ : ∀ h ∈ Rep0, h ≠ X - 1 → specialBlock Q xe h ≤ orthDerived Q := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · exact (hspecK h hh hne hm).1
    · rw [hbot h hh hm]
      exact bot_le
  have hspecF : ∀ h ∈ Rep0, h ≠ X - 1 → componentImage Q xe h ≤ F := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · exact hspec Rep0 hRep0 h hh hne hm
    · have : componentImage Q xe h = ⊥ := by
        unfold componentImage
        rw [hbot h hh hm, Subgroup.bot_subgroupOf, Subgroup.map_bot]
      rw [this]
      exact bot_le
  set K₀ : Subgroup (V ≃ₗ[K] V) := (F.comap ρ).map (orthDerived Q).subtype with hK₀
  have hmemK₀ : ∀ b : ↥(orthDerived Q), ρ b ∈ F → (b : V ≃ₗ[K] V) ∈ K₀ :=
    fun b hb => ⟨b, hb, rfl⟩
  have hspK₀ : specialProduct Q xe Rep0 ≤ K₀ := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    intro j hj
    have hjΩ := hspecΩ h hh hne hj
    refine hmemK₀ ⟨j, hjΩ⟩ (hspecF h hh hne ?_)
    exact Subgroup.mem_map.mpr ⟨⟨j, hjΩ⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hsfdK₀ : 3 ≤ finrank K (fixedSpace xe) → supportedFixedDerived Q xe ≤ K₀ := by
    intro h3 f hf
    have hfΩ := hx.supportedFixedDerived_le_orthDerived hf
    refine hmemK₀ ⟨f, hfΩ⟩ (hfix h3 ?_)
    exact Subgroup.mem_map.mpr ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  have hspM : specialProduct Q xe Rep0 ≤ isometryCentralizer Q xe :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  have hkey : ⁅Mo, Mo⁆ ≤ F.comap ρ := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    have hmM : (m : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm
    have hm'M : (m' : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm'
    have hg : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈
        ⁅isometryCentralizer Q xe, isometryCentralizer Q xe⁆ :=
      Subgroup.commutator_mem_commutator hmM hm'M
    obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep0 hg
    have hgK : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈ K₀ := by
      by_cases hdim : 3 ≤ finrank K (fixedSpace xe)
      · rw [hgjf]
        exact K₀.mul_mem (hspK₀ hj) (hsfdK₀ hdim hf)
      · have hdim2 : finrank K (fixedSpace xe) ≤ 2 := by omega
        have hfM : f ∈ isometryCentralizer Q xe := supportedFixedDerived_le_isometryCentralizer hf
        have hjM : j ∈ isometryCentralizer Q xe := hspM hj
        have hgM : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := by
          rw [hgjf]
          exact mul_mem hjM hfM
        have h1 : isometryRestrictFixed Q xe ⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V),
            hgM⟩ = 1 := by
          have h2 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) =
              ⁅(⟨(m : V ≃ₗ[K] V), hmM⟩ : ↥(isometryCentralizer Q xe)),
                (⟨(m' : V ≃ₗ[K] V), hm'M⟩ : ↥(isometryCentralizer Q xe))⁆ :=
            Subtype.ext rfl
          rw [h2, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep0 hdim2 hmM m.2 hm'M m'.2).eq
        have h3 : isometryRestrictFixed Q xe ⟨f, hfM⟩ = 1 := by
          have h4 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ := Subtype.ext hgjf
          rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep0 hj hjM,
            one_mul] at h1
          exact h1
        have hfB := supportedFixedDerived_le_supportedBlock hf
        have h5 : restrictFixed Q xe ⟨f, hfB⟩ = 1 := by
          rw [← isometryRestrictFixed_restrictFixed]
          exact h3
        have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
        rw [hgjf, hf1, mul_one]
        exact hspK₀ hj
    obtain ⟨b, hb, hbg⟩ := hgK
    have hb' : b = ⁅m, m'⁆ := Subtype.ext hbg
    rw [hb'] at hb
    exact hb
  have hNN : ⁅N, N⁆ = ⁅Mo, Mo⁆.map ρ := by
    rw [hNeq]
    exact (Subgroup.map_commutator Mo Mo ρ).symm
  rw [hNN]
  exact Subgroup.map_le_iff_le_comap.mpr hkey

end CFSG.HardMathSupport.Timmesfeld.CrossChar
