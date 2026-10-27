module

public import Certificates.Certificate24530
public import CFSG.Sporadic.Co1.Cover.Eps
public import CFSG.Sporadic.Co1.Module.TwoB

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.Co1.CoverNative CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2 CFSG.Blueprint Matrix

attribute [local irreducible] eps0 ga gb regCov rrCov epsRows

@[expose] noncomputable def epsMask
    (m : ℕ) : NativeSporadic.Co1 :=
  epsHom (Multiplicative.ofAdd (toVecD 11 m))

theorem matHom_epsMask (m : ℕ) :
    matHom (epsMask m) = rowsMatrix 24 (eprodRows epsRows m) :=
  matHom_epsHom_toVecD m

theorem ncard_fix_epsMask
    {m a b : ℕ} (h : countsOK (eprodRows epsRows m) a b = true) :
    {v : Vec24 | co1Act (epsMask m) v = v}.ncard = a ∧
      {v : Vec24 | co1Act (epsMask m) v = v ∧ q₀ v = 1}.ncard = b := by
  obtain ⟨h1, h2⟩ := countsOK_facts h
  have hfix : {v : Vec24 | co1Act (epsMask m) v = v} =
      {v | rowsMatrix 24 (eprodRows epsRows m) *ᵥ v = v} := by
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, matHom_epsMask]
  have hfixq : {v : Vec24 | co1Act (epsMask m) v = v ∧ q₀ v = 1} =
      {v | rowsMatrix 24 (eprodRows epsRows m) *ᵥ v = v ∧ q₀ v = 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, matHom_epsMask]
  rw [hfix, hfixq]
  exact ⟨h1, h2⟩

theorem epsA_facts :
    orderOf (epsMask eMaskA) = 2 ∧
      {v : Vec24 | co1Act (epsMask eMaskA) v = v}.ncard = 2 ^ 16 := by
  obtain ⟨h1, h2, -, -⟩ := Certificates.certificate24530
  exact ⟨orderOf_eq_of_orderIs (matHom_epsMask eMaskA) (by norm_num) h1,
    (ncard_fix_epsMask h2).1⟩

theorem epsC_facts :
    orderOf (epsMask eMaskC) = 2 ∧
      {v : Vec24 | co1Act (epsMask eMaskC) v = v}.ncard = 2 ^ 12 ∧
      {v : Vec24 | co1Act (epsMask eMaskC) v = v ∧ q₀ v = 1}.ncard = 2048 := by
  obtain ⟨-, -, h1, h2⟩ := Certificates.certificate24530
  exact ⟨orderOf_eq_of_orderIs (matHom_epsMask eMaskC) (by norm_num) h1,
    (ncard_fix_epsMask h2).1, (ncard_fix_epsMask h2).2⟩

theorem isConj_epsA_or_epsC
    {s : NativeSporadic.Co1} (hs : orderOf s = 2) (hB : ¬ CFSG.Monster.GMS.IsCo1TwoB s) :
    IsConj s (epsMask eMaskA) ∨ IsConj s (epsMask eMaskC) := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := CFSG.Monster.GMS.co1_involution_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, hqA, hqB, hqC, -⟩ := hrep
  obtain ⟨hoA, hfixA⟩ := epsA_facts
  obtain ⟨hoC, hfixC, hqC'⟩ := epsC_facts
  have hconjA : IsConj (epsMask eMaskA) sA := by
    rcases hcls _ hoA with h | h | h
    · exact h
    · exfalso
      have h1 := (CFSG.Monster.GMS.co1Inv_isConj_invariants h).1
      have e1 : (CFSG.Monster.GMS.co1Fix (epsMask eMaskA)).ncard = 2 ^ 16 := hfixA
      have e2 : (CFSG.Monster.GMS.co1Fix sB).ncard = 2 ^ 12 := hfB
      rw [e1, e2] at h1
      norm_num at h1
    · exfalso
      have h1 := (CFSG.Monster.GMS.co1Inv_isConj_invariants h).1
      have e1 : (CFSG.Monster.GMS.co1Fix (epsMask eMaskA)).ncard = 2 ^ 16 := hfixA
      have e2 : (CFSG.Monster.GMS.co1Fix sC).ncard = 2 ^ 12 := hfC
      rw [e1, e2] at h1
      norm_num at h1
  have hconjC : IsConj (epsMask eMaskC) sC := by
    rcases hcls _ hoC with h | h | h
    · exfalso
      have h1 := (CFSG.Monster.GMS.co1Inv_isConj_invariants h).1
      have e1 : (CFSG.Monster.GMS.co1Fix (epsMask eMaskC)).ncard = 2 ^ 12 := hfixC
      have e2 : (CFSG.Monster.GMS.co1Fix sA).ncard = 2 ^ 16 := hfA
      rw [e1, e2] at h1
      norm_num at h1
    · exfalso
      have h1 := (CFSG.Monster.GMS.co1Inv_isConj_invariants h).2.1
      rw [hqC', hqB] at h1
      norm_num at h1
    · exact h
  rcases hcls s hs with h | h | h
  · exact Or.inl (h.trans hconjA.symm)
  · exfalso
    apply hB
    obtain ⟨c1, c2, -⟩ := CFSG.Monster.GMS.co1Inv_isConj_invariants h
    refine ⟨hs, c1.trans hfB, fun v hv => ?_⟩
    by_contra hq
    have h1 : q₀ v = 1 := by
      rcases CFSG.Sporadic.Co1.Cover.zmod2_cases (q₀ v) with h0 | h1
      · exact absurd h0 hq
      · exact h1
    have hmem : v ∈ {v : Fin 24 → ZMod 2 | co1Act s v = v ∧ q₀ v = 1} := ⟨hv, h1⟩
    have h0 : {v : Fin 24 → ZMod 2 | co1Act s v = v ∧ q₀ v = 1}.ncard = 0 := c2.trans hqB
    rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
    rw [h0] at hmem
    exact hmem
  · exact Or.inr (h.trans hconjC.symm)

theorem exists_isConj_eps
    {s : NativeSporadic.Co1} (hs : orderOf s = 2) (hB : ¬ CFSG.Monster.GMS.IsCo1TwoB s) :
    ∃ x : Multiplicative (Fin 11 → ZMod 2), IsConj s (epsHom x) := by
  rcases isConj_epsA_or_epsC hs hB with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

end CFSG.EvenSporadicStandard.TwoCo1
