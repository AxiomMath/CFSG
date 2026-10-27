
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase1

public import Certificates.Certificate13620

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Foote.E27.Fi22S0 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
  CFSG.F3.Native
open scoped Pointwise

theorem classify_parts :
    labRep.size = nR ∧ labCls.size = nR ∧ labOf.size = nS ∧ witOf.size = nS ∧ conjW.size = nR ∧
    (∀ i < nS, i = 0 ∨ tabMul par L i (tabMul par L i i) ≠ 0 ∨
      (labOf[i]! < nR ∧ witOf[i]! < nS ∧ labRep[labOf[i]!]! < nS ∧
        tabMul par L witOf[i]! i = tabMul par L labRep[labOf[i]!]! witOf[i]!)) ∧
    (∀ l < nR, labCls[l]! < 4 ∧ (∀ z ∈ conjW[l]!, z < (chainLetters orb).size) ∧
      eqT (compT 3510 (lettersT (chainLetters orb) conjW[l]!) (eltT par (genT orb) labRep[l]!))
        (compT 3510 (eltT par (genT orb) globRep[labCls[l]!]!)
          (lettersT (chainLetters orb) conjW[l]!)) = true) ∧
    (∀ k < 4, globRep[k]! ≠ 0 ∧
      tabMul par L globRep[k]! (tabMul par L globRep[k]! globRep[k]!) = 0 ∧
      2187 ≤ tabComm par L nS globRep[k]!) ∧
    tabComm par L nS globRep[0]! = 2187 := by
  have h := Certificates.certificate13620
  unfold classifyOK classifyCore at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun i hi => ?_, fun l hl => ?_, fun k hk => ?_, h9⟩
  · rcases h6 i hi with (h0 | h0) | ⟨⟨⟨h10, h11⟩, h12⟩, h13⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨h10, h11, h12, h13⟩)
  · obtain ⟨⟨h10, h11⟩, h12⟩ := h7 l hl
    exact ⟨h10, h11, h12⟩
  · obtain ⟨⟨h10, h11⟩, h12⟩ := h8 k hk
    exact ⟨h10, h11, h12⟩

theorem isConj_labRep
    {l : ℕ} (hl : l < nR) (hr : labRep[l]! < nS) :
    ∃ k < 4, IsConj (tabElt gJ par labRep[l]!) (xRep k) := by
  obtain ⟨-, -, -, -, -, -, hc, -, -⟩ := classify_parts
  obtain ⟨hk, hw, he⟩ := hc l hl
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  have hρ : globRep[labCls[l]!]! < nS := globRep_lt _ hk
  set c : J := (conjW[l]!.map (pairG gs)).prod with hc'
  have hct := rep_lettersT _ hw
  have e := eq_of_rep_eqT ((hct.compT (rep_eltT _ hr))) ((rep_eltT _ hρ).compT hct) he
  refine ⟨labCls[l]!, hk, isConj_iff.2 ⟨c, ?_⟩⟩
  rw [e, mul_inv_cancel_right, xRep_def]

theorem isConj_xRep_of_mem
    {i : ℕ} (hi : i < nS) (h3 : orderOf (tabElt gJ par i) = 3) :
    ∃ k < 4, IsConj (tabElt gJ par i) (xRep k) := by
  obtain ⟨-, -, -, -, -, hlab, -, -, -⟩ := classify_parts
  have hT := tabData
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [tabElt_zero, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hcube : tabMul par L i (tabMul par L i i) = 0 := by
    obtain ⟨hl1, e1⟩ := hT.mul i hi i hi
    obtain ⟨hl2, e2⟩ := hT.mul i hi _ hl1
    have hpow : tabElt gJ par i ^ 3 = 1 := by
      have := pow_orderOf_eq_one (tabElt gJ par i)
      rwa [h3] at this
    have : tabElt gJ par (tabMul par L i (tabMul par L i i)) = tabElt gJ par 0 := by
      rw [tabElt_zero, ← e2, ← e1, ← hpow, pow_three', mul_assoc]
    exact hT.inj _ hl2 0 (by unfold nS; omega) this
  rcases hlab i hi with h0 | h0 | ⟨hl, hw, hr, he⟩
  · exact absurd h0 hi0
  · exact absurd hcube h0
  · obtain ⟨k, hk, hc⟩ := isConj_labRep hl hr
    refine ⟨k, hk, IsConj.trans ?_ hc⟩
    obtain ⟨-, e1⟩ := hT.mul _ hw _ hi
    obtain ⟨-, e2⟩ := hT.mul _ hr _ hw
    rw [he] at e1
    have e3 : tabElt gJ par witOf[i]! * tabElt gJ par i =
        tabElt gJ par labRep[labOf[i]!]! * tabElt gJ par witOf[i]! := by rw [e1, e2]
    refine isConj_iff.2 ⟨tabElt gJ par witOf[i]!, ?_⟩
    rw [e3, mul_inv_cancel_right]

theorem fi22_classify (s : J)
    (hs : orderOf s = 3) : ∃ k < 4, IsConj s (xRep k) := by
  have := finite_J
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := exists_sylow_table
  have hsp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J Q T
  have hsT : g * s * g⁻¹ ∈ (T : Subgroup J) := by
    have h1 : s ∈ (Q : Subgroup J) := hQ (Subgroup.mem_zpowers s)
    have h2 : MulAut.conj g s ∈ (MulAut.conj g • (Q : Set J)) := Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * s * g⁻¹ ∈ T := by simpa [MulAut.conj_apply] using h2
    exact h3
  obtain ⟨i, hi, hie⟩ := (hT _).1 hsT
  have hio : orderOf (tabElt gJ par i) = 3 := by
    rw [hie, orderOf_conj']
    exact hs
  obtain ⟨k, hk, hc⟩ := isConj_xRep_of_mem hi hio
  refine ⟨k, hk, IsConj.trans ?_ hc⟩
  rw [hie]
  exact isConj_iff.2 ⟨g, rfl⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
