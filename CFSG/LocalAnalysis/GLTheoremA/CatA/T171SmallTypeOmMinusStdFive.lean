module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusStdGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem five_blocks_impossible (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5) {Bb : Subgroup ↥(orthDerived Q)}
    [Fintype ↥(orthImage Bb)] [DecidableEq (Hyperplane (orthImage Bb) 3)]
    (hAe : IsElemAbelian 3 (orthImage Bb))
    (h5 : (blockSet (orthImage Bb)).card = 5) (hT : TwoLocal Bb) : False := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF : (3 : ZMod 2) ≠ 0 := by decide
  have hB : ∀ a : ↥(orthImage Bb), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[ZMod 2] V) u) ((a : V ≃ₗ[ZMod 2] V) v) = polarBilin Q u v :=
    fun a => polar_orthImage (Ã := Bb) a
  obtain ⟨hC, hplane⟩ := five_blocks_data hQ hAe hdim hB h5
  obtain ⟨P, hP2, hPne, hBN⟩ := hT
  obtain ⟨R, hRne, hRinv, hRiso⟩ :=
    exists_invariant_totallyIsotropic_of_twoLocal hQ hdim hP2 hPne hBN
  have hRinvA : ∀ a : ↥(orthImage Bb), ∀ v ∈ R, (a : V ≃ₗ[ZMod 2] V) v ∈ R := by
    rintro ⟨b, hb⟩ v hv
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hb
    exact hRinv c hc v hv
  obtain ⟨w, hwR, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
  obtain ⟨D, hDmem, hDw⟩ :=
    exists_projBlock_ne_zero_of_fixedSpace_bot hp hpF hAe hC hw0
  have hpwR : projBlock (orthImage Bb) hp hpF hAe D w ∈ R :=
    projBlock_apply_mem_of_invariant hp hpF hAe hRinvA hwR
  have hpwD : projBlock (orthImage Bb) hp hpF hAe D w ∈ blockSpace (orthImage Bb) D.1 :=
    projBlock_apply_mem (orthImage Bb) hp hpF hAe D w
  have hIne : R ⊓ blockSpace (orthImage Bb) D.1 ≠ ⊥ := by
    intro hbot
    have hmem : projBlock (orthImage Bb) hp hpF hAe D w ∈
        R ⊓ blockSpace (orthImage Bb) D.1 := ⟨hpwR, hpwD⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hDw hmem
  have hIinv : ∀ a : ↥(orthImage Bb), ∀ v ∈ R ⊓ blockSpace (orthImage Bb) D.1,
      (a : V ≃ₗ[ZMod 2] V) v ∈ R ⊓ blockSpace (orthImage Bb) D.1 := by
    intro a v hv
    exact ⟨hRinvA a v hv.1, blockSpace_invariant (orthImage Bb) hp hpF hAe hv.2⟩
  have hIle : finrank (ZMod 2) ↥(R ⊓ blockSpace (orthImage Bb) D.1) ≤ 2 := by
    calc finrank (ZMod 2) ↥(R ⊓ blockSpace (orthImage Bb) D.1)
        ≤ finrank (ZMod 2) ↥(blockSpace (orthImage Bb) D.1) :=
          Submodule.finrank_mono inf_le_right
      _ = 2 := hplane D hDmem
  have hI2 : finrank (ZMod 2) ↥(R ⊓ blockSpace (orthImage Bb) D.1) = 2 := by
    rcases Nat.lt_or_ge (finrank (ZMod 2) ↥(R ⊓ blockSpace (orthImage Bb) D.1)) 2
      with hlt | hge
    · exfalso
      have hIpos : 0 < finrank (ZMod 2) ↥(R ⊓ blockSpace (orthImage Bb) D.1) := by
        rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
        exact hIne
      have hI1 : finrank (ZMod 2) ↥(R ⊓ blockSpace (orthImage Bb) D.1) = 1 := by omega
      have hfix : ∀ a : ↥(orthImage Bb), ∀ v ∈ R ⊓ blockSpace (orthImage Bb) D.1,
          (a : V ≃ₗ[ZMod 2] V) v = v := by
        intro a v hv
        by_cases hv0 : v = 0
        · rw [hv0, map_zero]
        · have hspan : Submodule.span (ZMod 2) {v} = R ⊓ blockSpace (orthImage Bb) D.1 := by
            refine Submodule.eq_of_le_of_finrank_le
              ((Submodule.span_singleton_le_iff_mem _ _).mpr hv) ?_
            rw [finrank_span_singleton hv0, hI1]
          have hav : (a : V ≃ₗ[ZMod 2] V) v ∈ R ⊓ blockSpace (orthImage Bb) D.1 := hIinv a v hv
          rw [← hspan, Submodule.mem_span_singleton] at hav
          obtain ⟨c, hc⟩ := hav
          have hc0 : c = 1 := by
            by_contra hcne
            have hcz : c = 0 := by
              have hcases : c = 0 ∨ c = 1 := by
                fin_cases c
                · exact Or.inl rfl
                · exact Or.inr rfl
              rcases hcases with h | h
              · exact h
              · exact absurd h hcne
            rw [hcz, zero_smul] at hc
            refine hv0 ((a : V ≃ₗ[ZMod 2] V).injective ?_)
            rw [map_zero]
            exact hc.symm
          rw [hc0, one_smul] at hc
          exact hc.symm
      have hleC : R ⊓ blockSpace (orthImage Bb) D.1 ≤ fixedSpaceOf (orthImage Bb) := by
        intro v hv
        rw [mem_fixedSpaceOf]
        intro a
        exact hfix a v hv
      exact hIne (le_bot_iff.mp (hleC.trans (le_of_eq hC)))
    · omega
  have hVDleR : blockSpace (orthImage Bb) D.1 ≤ R := by
    have heq : R ⊓ blockSpace (orthImage Bb) D.1 = blockSpace (orthImage Bb) D.1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hI2, hplane D hDmem])
    rw [← heq]
    exact inf_le_left
  have hnd := blockSpace_polar_nondegenerate (orthImage Bb) hQ hp hpF hAe hB D
  obtain ⟨u, huD, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((mem_blockSet).1 hDmem)
  have hex : ∃ v ∈ blockSpace (orthImage Bb) D.1, polar Q u v ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (congrArg Subtype.val (hnd.1 ⟨u, huD⟩ fun v => by
      have hv := h v.1 v.2
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        QuadraticMap.polarBilin_apply_apply] using hv))
  obtain ⟨v, hvD, huv⟩ := hex
  have hzero := (LinearMap.BilinForm.mem_orthogonal_iff.1
    (hRiso (hVDleR huD)) v (hVDleR hvD))
  exact huv (by
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hzero)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
