module

public import Certificates.Data.CFSGNative.Co2Rank.Dfs
public import Certificates.Certificate129082
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2FixBound
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Co2Inv
public import CFSG.Sporadic.Co2Schreier.LocalLit

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5

open CFSG.Sporadic.Co2Rank CFSG.Sporadic.Co2Inv CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Blueprint
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier Matrix

theorem exists_rep_native (x : NativeSporadic.Co2) (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ r < 3, IsConj x (repCo2 r) := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowS x (isPGroup_zpowers_of_invol hx hx1)
  obtain ⟨k, hk, hke⟩ := exists_eltS_of_mem hg
  have h2 : eltS k * eltS k = 1 := by
    rw [hke]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx, mul_one, mul_inv_cancel]
  have h1 : eltS k ≠ 1 := by
    rw [hke]
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  obtain ⟨r, hr, hconj⟩ := exists_rep_of_invol hk h2 h1
  have hxk : IsConj x (eltS k) := by
    rw [hke]
    exact isConj_iff.2 ⟨g, rfl⟩
  exact ⟨r, hr, hxk.trans hconj⟩

theorem d5_native
    (B : Subgroup NativeSporadic.Co2) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hno : ∀ x ∈ B, x ≠ 1 → ¬ IsConj x (repCo2 0)) :
    Nat.card B ≤ 128 := by
  classical
  have hcheck := Certificates.certificate129082
  have hfr : ∀ r < 3, FixBound.fixN co2PermHom (repCo2 r) = (Finset.univ.filter fun i : Fin 2300 =>
      rowsMatrix 22 co2InvReps[r]! *ᵥ co2Vec i = co2Vec i).card := by
    intro r hr
    unfold FixBound.fixN
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    rw [← co2PermEquiv_apply, ← repCo2_val hr, ← co2Vec_permEquiv]
    exact ⟨fun h => by rw [h], fun h => Fin.ext (co2Vec_injective (Fin.isLt _) i.2 h)⟩
  refine FixBound.card_le_of_fix co2PermHom (by simp) B hcomm hsq fun x hx hx1 => ?_
  obtain ⟨r, hr, hxr⟩ := exists_rep_native x (hsq x hx) hx1
  obtain ⟨g, hg⟩ := isConj_iff.1 hxr
  have hc : FixBound.fixN co2PermHom x = FixBound.fixN co2PermHom (repCo2 r) := by
    rw [← hg, FixBound.fixN_conj]
  rw [hc, hfr r hr]
  interval_cases r
  · exact absurd hxr (hno x hx hx1)
  · exact Or.inl hcheck.1
  · exact Or.inr hcheck.2

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5
