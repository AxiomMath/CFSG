module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Lane
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints D4TrialityLayer d4Nodes)


section D4Class


theorem ssTw_pgroup_d4class {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hℓ5 : 5 ≤ ℓ) :
    ∃ V : Subgroup ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i), IsPGroup ℓ V ∧
      8 ≤ Nat.card V := by
  have hE6 : E6FixDNAll := e6FixDNAll_proved
  cases τ with
  | G2 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    exfalso
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
      exact ssTw_pgroup_d4_outer (Or.inl rfl) d4Base_E6 d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) S
        hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin hℓ hℓ5
    · rw [hs, Function.iterate_one] at hnin
      exact ssTw_pgroup_d4_twE6 hE6 S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin hℓ hℓ5
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ssTw_pgroup_d4_outer (Or.inr (Or.inl rfl)) d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hℓ hℓ5
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ssTw_pgroup_d4_outer (Or.inr (Or.inr rfl)) d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hℓ hℓ5

end D4Class

end CFSG.HardMathSupport.Dickson.Sec6
