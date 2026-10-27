module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7Mu
import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuCtx
public import CFSG.ClassicalInvolution.Asc77.AscMuTabAbel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Hat2A7P1
  CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section Clique


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G}
  {W : Subgroup G}


theorem exists_rep_a7 (hP : PartIHypG8 Ω) (hW : W ∈ WSet Ω) {M : Subgroup G} (hM : M ∈ Ω) :
    ∃ g : G, ∃ ρ : Rep Ω W, ρ.K = conjSub g M := by
  obtain ⟨R, hR⟩ := MuTab.exists_sylow2In M
  obtain ⟨S', hWS'⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨S₀, hS₀⟩ := hR.2.1.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₀ S'
  have hD : conjSub g R ∈ DSet Ω W := by
    refine Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hP.hyp hW hWS'
      (RSet.conj hP.hyp.conjInvariant (mem_RSet_of_isSylow2In hM hR) g) ?_
    rw [← hg]
    exact conjSub_mono hS₀
  exact ⟨g, T8.mkRep hP hW (hP.hyp.conjInvariant g M hM) hD (hR.conj g), rfl⟩

theorem sylow_frame_a7 (hP : PartIHypG8 Ω) {M M' : Subgroup G} {z : G} (hM : M ∈ Ω)
    (hM' : M' ∈ Ω) (hz : IsUniqueInvolution M z) (hz' : IsUniqueInvolution M' z)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (R R' : Subgroup G), W ≤ (S : Subgroup G) ∧ IsSylow2In R M ∧
      IsSylow2In R' M' ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hWab := Q3.Q3CL.Thompson.commutes_of_mem_WSet hP.hyp hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ M) M :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hP.cls.isSubnormal_of_uniqueInvolution hM hz)
  have hR' : IsSylow2In (T ⊓ M') M' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hP.cls.isSubnormal_of_uniqueInvolution hM' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  exact ⟨S, T ⊓ M, T ⊓ M', hWT.trans hTS, hR, hR', inf_le_left.trans hTS,
    inf_le_left.trans hTS⟩

theorem exists_second_rep_a7 (hP : PartIHypG8 Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hperp : KPerp Ω K = {K, K'}) (hW : W ∈ WSet Ω)
    {g : G} {ρ : Rep Ω W} (hg : ρ.K = conjSub g K) :
    ∃ ρ' : Rep Ω W, ρ'.K = conjSub g K' ∧ ρ'.K ∈ omegaNbr Ω ρ.K := by
  have hΩ : HypOmegaGen Ω := hP.hyp
  obtain ⟨hK'Ω, z', hzK, hzK'⟩ := hK'
  have hzz : z' = z := (hz.eq hzK).symm
  rw [hzz] at hzK'
  have hz₁ : IsUniqueInvolution ρ.K (g * z * g⁻¹) := by
    rw [hg]
    exact hz.conj g
  have hzW : g * z * g⁻¹ ∈ W :=
    (Q3.Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW ρ.hK ρ.hR ρ.hRK hz₁).2
  have hK₁' : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  obtain ⟨S, R₁, R₁', hWS, hR₁, hR₁', hR₁S, hR₁'S⟩ :=
    sylow_frame_a7 hP ρ.hK hK₁' hz₁ (hzK'.conj g) hW hzW
  have hR₁'D : R₁' ∈ DSet Ω W :=
    Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK₁' hR₁') hR₁'S
  refine ⟨T8.mkRep hP hW hK₁' hR₁'D hR₁', rfl, ?_⟩
  have hK'n : K' ∈ omegaNbr Ω K := by
    have h1 : K' ∈ KPerp Ω K := by
      rw [hperp]
      exact Or.inr rfl
    rcases h1 with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have := omegaNbr_conj hΩ.conjInvariant hK'n g
  rw [← hg] at this
  exact this

theorem muIsoE4_a7 (hs : Std2A7 Ω K) {z : G} (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hperp : KPerp Ω K = {K, K'}) (hW : W ∈ WSet Ω) :
    MuIsoE4 Ω W := by
  have hP : PartIHypG8 Ω := partIHypG8_of_std2A7 hs
  have hΩ : HypOmegaGen Ω := hP.hyp
  have c := T8.ctxOf hP hW
  obtain ⟨g₀, ρ₀, hρ₀⟩ := exists_rep_a7 hP hW hs.mem
  obtain ⟨ρ₁, hρ₁K, hρ₁n⟩ := exists_second_rep_a7 hP hz hK' hne hperp hW hρ₀
  have hne₁ : ρ₁.K ≠ ρ₀.K := hρ₁n.2.1
  have hd₀ := muTabElt_mem ρ₀
  have hd₁ := muTabElt_mem ρ₁
  have hd₀₁ : muTabElt ρ₀ ≠ muTabElt ρ₁ := fun h => hne₁ (by
    have := c.K_eq_of_img_eq ρ₀ ρ₁ (congrArg Subtype.val h)
    exact this.symm)
  have hsub : muDelta Ω W ⊆ {muTabElt ρ₀, muTabElt ρ₁} := by
    intro a ha
    obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta ha
    by_cases hσ : σ.K = ρ₀.K
    · left
      exact Subtype.ext (Q3.Q3T6.Mu.ctx_img_eq_of_K_eq c σ ρ₀ hσ)
    · right
      have hstar : σ.K ∈ omegaStarNbr Ω ρ₀.K :=
        (Q3.Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hΩ hW ρ₀.hK σ.hK (Ne.symm hσ) ρ₀.hR σ.hR
          ρ₀.hRK σ.hRK).1
      have hnbr : σ.K ∈ omegaNbr Ω ρ₀.K :=
        omegaStarNbr_subset_omegaNbr_a7 hs.toPre2A7 ρ₀.hK σ.hK hstar
      have h1 : conjSub g₀⁻¹ σ.K ∈ KPerp Ω K := by
        have := omegaNbr_conj hΩ.conjInvariant hnbr g₀⁻¹
        rw [hρ₀, conjSub_inv_conjSub] at this
        exact Set.mem_insert_of_mem _ this
      have h1' : conjSub g₀⁻¹ σ.K ∈ KPerp Ω K := h1
      rw [hperp] at h1'
      have hσK : σ.K = ρ₁.K := by
        rcases h1' with h2 | h2
        · exfalso
          have h3 : conjSub g₀⁻¹ σ.K = K := h2
          apply hσ
          rw [hρ₀, ← h3, conjSub_conjSub_inv]
        · have h3 : conjSub g₀⁻¹ σ.K = K' := h2
          rw [hρ₁K, ← h3, conjSub_conjSub_inv]
      exact Subtype.ext (Q3.Q3T6.Mu.ctx_img_eq_of_K_eq c σ ρ₁ hσK)
  have hcomm : muTabElt ρ₀ * muTabElt ρ₁ = muTabElt ρ₁ * muTabElt ρ₀ :=
    muGroup_comm_a7 hs hW _ _
  have hgen : Subgroup.closure ({muTabElt ρ₀, muTabElt ρ₁} : Set ↥(muGroup Ω W)) = ⊤ := by
    refine top_unique ?_
    rw [← closure_muDelta_eq_top Ω W]
    exact Subgroup.closure_mono hsub
  exact MuTab.nonempty_mulEquiv_klein (Q3.Q3T6.Mu.muDelta_mul_self hΩ hW hd₀)
    (Q3.Q3T6.Mu.muDelta_mul_self hΩ hW hd₁) hcomm (muDelta_ne_one hW hd₀)
    (muDelta_ne_one hW hd₁) hd₀₁ hgen

theorem a7C23_1_proved : A7C23_1 := by
  intro G _ _ _ Ω K K' z h W hW
  exact Or.inl (muIsoE4_a7 h.1.stand h.1.hz h.1.hK' h.1.hne h.2 hW)

end Clique

end CFSG.ClassicalInvolution.Hat2A7S
