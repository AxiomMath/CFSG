module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Stmt
public import CFSG.ClassicalInvolution.Q3.Q3NMInner
public import CFSG.ClassicalInvolution.Q3.Q3PPFundFix

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM CFSG.Assembly.LowTwoRank

section Data


variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {zb : X}

theorem layerKind_data {c : CompData} (h : S4LayerKind c Φ zb) :
    ∃ φ : c.G →* X, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center c.G ∧
      ∀ L ∈ Φ, ∃ R ∈ c.fund, L = R.map φ := by
  obtain ⟨ι, -, D, i₁, hi, hk, -⟩ := h
  subst hk
  refine ⟨D.hom i₁, ?_, D.ker_le_center i₁, fun L hL => ?_⟩
  · have hrange : (D.hom i₁).range = ⊤ := by
      have h1 : (⨆ i, (D.hom i).range) = (D.hom i₁).range := by
        apply le_antisymm
        · exact iSup_le fun i => by rw [hi i]
        · exact le_iSup (fun i => (D.hom i).range) i₁
      rw [← h1]
      exact D.generate
    exact MonoidHom.range_eq_top.mp hrange
  · obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl := hi i
    exact ⟨R, hR, hLR⟩

end Data

section Quasi

variable {Q : Type} [Group Q]

theorem isQuasisimple_of_open (h : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsimple := h.2
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcon _ _
  have htop : (⊤ : Subgroup Q) ≤ Subgroup.center Q := h.1 ▸ hle
  obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : Q ⧸ Subgroup.center Q)).mp
    hsimple.toNontrivial
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ha ((QuotientGroup.eq_one_iff x).mpr (htop (Subgroup.mem_top x)))

end Quasi

section Main


theorem s4VertexAt_of_fixedOddFreeFund {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (hFT : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hTD4 : t ≠ .trialityD4) (hD4 : ¬ (t = .POmegaPlus ∧ n = 4))
    (hF : Q3PP.FixedOddFreeFund (CompData.model t n)) :
    S4VertexModelLeafAt (CompData.model t n) := by
  intro X _ _ Φ zb _ hlay _
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨φ, hφs, hφk, hΦ1⟩ := layerKind_data hlay
  have hKq : CFSG.Open.IsQuasisimple (CompData.model t n).G :=
    (ModelFacts.modelClauseZero t n 3 1 hp hFT hadm).1
  have hXq : CFSG.Open.IsQuasisimple X := isQuasisimple_of_centralQuotient hKq φ hφs hφk
  refine ⟨isQuasisimple_of_open hXq, ?_, ?_⟩
  · have : Group.IsPerfect X := ⟨hXq.1⟩
    have : Group.IsPerfect (CompData.model t n).G := ⟨hKq.1⟩
    have hodd := oddAut_inner_centralQuotient hD4 hTD4 hp hFT hadm X φ hφs hφk
    have hfix : ∀ τ : MulAut X, (∃ A ∈ Φ, ∀ a ∈ A, τ a = a) → τ ≠ 1 → τ * τ = 1 →
        oddCoreIn (fixedSubgroup (autToCentralQuotient X τ)) = ⊥ := by
      rintro τ ⟨A, hA, hτA⟩ - hτ2
      obtain ⟨R, hR, rfl⟩ := hΦ1 A hA
      let ε := centralQuotientIso φ hφs hφk
      let ρ : MulAut ((CompData.model t n).G ⧸ Subgroup.center (CompData.model t n).G) :=
        MulAut.congr ε.symm (autToCentralQuotient X τ)
      have hτ2' : autToCentralQuotient X τ * autToCentralQuotient X τ = 1 := by
        rw [← map_mul, hτ2, map_one]
      have hρ2 : ρ * ρ = 1 := by
        change MulAut.congr ε.symm (autToCentralQuotient X τ) *
          MulAut.congr ε.symm (autToCentralQuotient X τ) = 1
        rw [← map_mul, hτ2', map_one]
      have hρR : ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r := by
        intro r hr
        have h1 : ε (QuotientGroup.mk r) = QuotientGroup.mk (φ r) := rfl
        change ε.symm (autToCentralQuotient X τ (ε (QuotientGroup.mk r))) = _
        rw [h1, autToCentralQuotient_mk, hτA (φ r) (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)]
        exact ε.symm_apply_eq.mpr h1.symm
      have h1 := oddCoreIn_fixed_congr_eq_bot' ε ρ (hF ρ hρ2 ⟨R, hR, hρR⟩)
      have h2 : MulAut.congr ε ρ = autToCentralQuotient X τ := by
        change MulAut.congr ε (MulAut.congr ε.symm (autToCentralQuotient X τ)) = _
        refine MulEquiv.ext fun x => ?_
        simp [MulAut.congr_apply]
      rwa [h2] at h1
    exact autOddFreeOn_of_fixed_quotient _ hodd hfix
  · intro A hA B hB
    obtain ⟨R, hR, rfl⟩ := hΦ1 A hA
    obtain ⟨R', hR', rfl⟩ := hΦ1 B hB
    obtain ⟨g, hg⟩ : ∃ g : (CompData.model t n).G,
        R' = R.map (MulAut.conj g).toMonoidHom :=
      ModelFacts.fundamentalSingleClass t n 3 1 hp hFT hadm hG2 hTD4 R hR R' hR'
    subst hg
    refine ⟨φ g, ?_⟩
    show Subgroup.map (MulAut.conj (φ g)).toMonoidHom (Subgroup.map φ R) =
      Subgroup.map φ (Subgroup.map (MulAut.conj g).toMonoidHom R)
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext r
    simp [map_mul, map_inv]

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
