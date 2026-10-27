module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieDerived

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


private theorem wcR_exists_noncomm {F : Type} [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    {a : ℕ} (hF : Nat.card F = 3 ^ (2 * a + 1)) :
    ∃ x y : reeFixed ReeTag.G2 F a,
      (x : adjointGroup ReeTag.G2.tag F) ∈ (nativeData ReeTag.G2.tag F).U ∧
      (y : adjointGroup ReeTag.G2.tag F) ∈ (nativeData ReeTag.G2.tag F).U ∧ x * y ≠ y * x := by
  have hmem : ∀ t b c : F, ∃ g : reeFixed ReeTag.G2 F a,
      ((g : adjointGroup ReeTag.G2.tag F) : ModGL ReeTag.G2.tag F) = smallReeCoord a F t b c ∧
        (g : adjointGroup ReeTag.G2.tag F) ∈ (nativeData ReeTag.G2.tag F).U := by
    intro t b c
    refine ⟨⟨⟨smallReeCoord a F t b c, ReeTag.smallReeCoord_mem_adjointGroup t b c⟩, ?_⟩, rfl, ?_⟩
    · rw [mem_reeFixed, ← ReeTag.finiteReeAut_eq_reeAut]
      exact Subtype.ext (ReeTag.finiteReeAut_smallReeCoord hF t b c)
    · exact ReeTag.mem_nativeData_U_of_mem_posUnipotent (smallReeCoord_mem_posUnipotent a F t b c)
  obtain ⟨x, hxv, hxU⟩ := hmem 1 0 0
  obtain ⟨y, hyv, hyU⟩ := hmem 0 1 0
  refine ⟨x, y, hxU, hyU, fun hxy => ?_⟩
  have h : smallReeCoord a F 1 0 0 * smallReeCoord a F 0 1 0 =
      smallReeCoord a F 0 1 0 * smallReeCoord a F 1 0 0 := by
    have h := congrArg (fun g : reeFixed ReeTag.G2 F a =>
      ((g : adjointGroup ReeTag.G2.tag F) : ModGL ReeTag.G2.tag F)) hxy
    simp only [Subgroup.coe_mul, hxv, hyv] at h
    exact h
  have h1 : smallReeCoord a F 1 0 0 * smallReeCoord a F 0 1 0 = smallReeCoord a F 1 1 0 := by
    rw [smallReeCoord_mul hF]
    congr 1 <;> ring
  have h2 : smallReeCoord a F 0 1 0 * smallReeCoord a F 1 0 0 = smallReeCoord a F 1 1 (-1) := by
    rw [smallReeCoord_mul hF, smallReeSigma_zero]
    congr 1 <;> ring
  rw [h1, h2] at h
  have h' := (ReeTag.bijOn_smallReeCoord (a := a) hF).2.1
    (Set.mem_univ ((1 : F), (1 : F), (0 : F))) (Set.mem_univ ((1 : F), (1 : F), (-1 : F))) h
  have h3 : (0 : F) = -1 := congrArg (fun p : F × F × F => p.2.2) h'
  exact one_ne_zero (neg_eq_zero.mp h3.symm)

theorem wcOn_reeG2 {K : Type} [Group K] [Finite K] {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel K .twistedG2 p f) : WCOn 3 K := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  obtain ⟨-, -, -, hp, -, h3⟩ := hadm
  subst hp hf
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have : CharP F ReeTag.G2.prime := ‹CharP F 3›
  have ha : 1 ≤ a := by omega
  have := Finite.of_equiv _ e.toEquiv
  obtain ⟨T, hT⟩ := exists_sylow_reeFixed .G2 F a
  have hTle : (T : Subgroup (reeFixed .G2 F a)) ≤ commutator (reeFixed .G2 F a) := by
    intro x hx
    rw [hT] at hx
    obtain ⟨y, hy, hyx⟩ := reeFixed_U_le_derived .G2 F a ha hF x hx x.2
    rwa [Subtype.ext hyx] at hy
  obtain ⟨x, y, hx, hy, hxy⟩ := wcR_exists_noncomm (a := a) hF
  refine WCOn.of_mulEquiv e
    (WCOn.of_derivedCentralQuotient_noncomm (p := 3) _
      ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed .G2 F a)).trans
        ((reeFixed .G2 F a).equivMapOfInjective _ Subtype.val_injective).symm)
      (holds_reeFixed .G2 F a) T hTle T.isPGroup' hTle (x := x) (y := y)
      (by rw [hT]; exact hx) (by rw [hT]; exact hy) hxy)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
