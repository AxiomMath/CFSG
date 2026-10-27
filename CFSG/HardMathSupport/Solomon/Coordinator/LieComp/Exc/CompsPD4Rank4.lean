module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Class
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4TwClass
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4TwLayers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDRankFour

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KD4L CompsPD4Layers
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section Rank4


theorem rationalLieType_of_rank_four {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hq : ringChar L = 2 ∨ 5 ≤ S.D.q) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hE6 := e6FixDNAll_proved
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact CompsPD4Class.rationalLieType_rationalComponent_of_d4_outer d4Base_E6
        d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) CompsPD4Layers.d4TrialityLayerRL_E6
        CompsPD4Layers.d4SwapLayerRL_E6 S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin hq
    · rw [hs, Function.iterate_one] at hnin
      refine rationalLieType_rationalComponent_of_d4_twE6_of_layer S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv
        hρ hnin (fun ℓ f _ _ hf hqf n hn u hu π hleaf hπ1 _ hact => ?_)
      have hqℓ : ℓ = 2 ∨ 5 ≤ ℓ ^ f := by
        rw [← hqf, ← ringChar.eq L ℓ]
        exact hq
      have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
      have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
          (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
      have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
          (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
      have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
          (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
      rcases hleaf with hc | hc | hc | hc | hc | hc
      · exact absurd hc hπ1
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2,
          CompsPD4TwLayers.twisted_swap_layer_RL hf hqℓ h12 hv1 hv2 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2,
          CompsPD4TwLayers.twisted_swap_layer_RL hf hqℓ h14 hv1 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2,
          CompsPD4TwLayers.twisted_swap_layer_RL hf hqℓ h24 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2,
          CompsPD4TwLayers.twisted_triality_layer_RL hf h12 h24 h14 hv1 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2,
          CompsPD4TwLayers.twisted_triality_layer_RL hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact⟩
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact CompsPD4Class.rationalLieType_rationalComponent_of_d4_outer d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6)
      CompsPD4Layers.d4TrialityLayerRL_E7 CompsPD4Layers.d4SwapLayerRL_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hq
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact CompsPD4Class.rationalLieType_rationalComponent_of_d4_outer d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6)
      CompsPD4Layers.d4TrialityLayerRL_E8 CompsPD4Layers.d4SwapLayerRL_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hq

theorem excRationalLieTypesOuterD_rank4_holds : ExcRationalLieTypesOuterD_rank4 := by
  intro τ L _ _ p₀ S a hT hap h1 i hshape hr4 hout hqs
  have hℓ3 : ringChar L ≠ 3 := ringChar_ne_of_pow_eq_one Nat.prime_three hap h1
  have hpL : (((3 : ℕ)) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne Nat.prime_three hℓ3
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
    rw [hshape.2, hr4]
  have hq : ringChar L = 2 ∨ 5 ≤ S.D.q := by
    obtain ⟨r, e, hr, hchar, he, hqe⟩ := LangSetup.exists_char_pow S
    have hrc : ringChar L = r := ringChar.eq L r
    by_cases h2 : r = 2
    · exact Or.inl (hrc.trans h2)
    · right
      have h3 : r ≠ 3 := fun h => hℓ3 (hrc.trans h)
      have h4 : r ≠ 4 := by
        rintro rfl
        exact absurd hr (by norm_num)
      have hr5 : 5 ≤ r := by
        have := hr.two_le
        omega
      rw [hqe]
      exact hr5.trans (Nat.le_self_pow (Nat.ne_of_gt he) r)
  exact rationalLieType_of_rank_four S Nat.prime_three hpL hT hTp h1 i hr4 hc hout hq

theorem excRationalLieTypesOuterD_proved : ExcRationalLieTypesOuterD :=
  excRationalLieTypesOuterD_of_rank4 excRationalLieTypesOuterD_rank4_holds

end Rank4

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
