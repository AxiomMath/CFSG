module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinExc
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSuzukiSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLargeReeTitsSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIReeSocle

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

omit [Finite Y] [IsSimpleGroup Y] in
theorem three_pow_mod_sixteen (a : ℕ) : 3 ^ (2 * (2 * a + 1)) % 16 = 9 := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (2 * (n + 1) + 1) = 2 * (2 * n + 1) + 4 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem hinFor_suzuki :
    HinFor fun Y _ => ∃ ℓ f : ℕ, Blueprint.SuzukiModel Y ℓ f := by
  intro Y _ _ _ ⟨ℓ, f, hY⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  exact UnbalancedCorr.faithful_suzuki_socle_involution_component_exclusion hWs hWnab hWC hτ
    (hLW τ) (isComponentOf_map_conj_layer hZ hL) ℓ f
    (SectionRank.suzukiModel_of_mulEquiv eW.symm hY)

theorem hinFor_largeReeTits :
    HinFor fun Y _ => ∃ (t : Assembly.LowTwoRank.StatedLieTag) (ℓ f : ℕ),
      (t = .twistedF4 ∨ t = .Tits) ∧ Blueprint.ReeTitsModel Y t ℓ f := by
  intro Y _ _ _ ⟨t, ℓ, f, ht, hY⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, -, hWs, hWnab, -, -⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨-, hno, -⟩ :=
    UnbalancedCorr.simple_generalized_fitting_large_Ree_Tits_involution_centralizers_component_free
      rfl hWs hWnab hτ ht (SectionRank.reeTitsModel_of_mulEquiv eW.symm hY)
  exact hno _ (isComponentOf_map_conj_layer hZ hL)

theorem hinFor_smallRee :
    HinFor fun Y _ => ∃ ℓ f : ℕ, Blueprint.ReeTitsModel Y .twistedG2 ℓ f := by
  intro Y _ _ _ ⟨ℓ, f, hY⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨-, -, hℓ, ⟨a, ha, hfa⟩, hiso⟩ := LieType.Ree.small_Ree_model_Schreier Y ℓ f hY
  subst hℓ
  obtain ⟨-, a', hfa', K, _, _, hK, ⟨e'⟩⟩ := hY
  have haa : a' = a := by omega
  subst haa
  have hc : CharP K LieType.Ree.ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  obtain ⟨φ⟩ := hiso a' K hfa hK ⟨e'⟩
  obtain ⟨-, -, -, -, hp3, hma, -⟩ :=
    OutcomeLocal.faithful_small_Ree_socle_small_source_involution_selector_explicit hWs hWnab
      hWC hτ (hLW τ) (isComponentOf_map_conj_layer hZ hL) hp hp2 hm
      (Or.inl (statedSrc_layerMap hZ hL)) ha
      (by rw [hK, hfa]) (eW.symm.trans φ)
  subst hp3
  subst hma
  have h9 := three_pow_mod_sixteen a'
  generalize 3 ^ (2 * (2 * a' + 1)) = N at h16 h9
  omega

theorem hinFor_reeTits :
    HinFor fun Y _ => ∃ (t : Assembly.LowTwoRank.StatedLieTag) (ℓ f : ℕ),
      t ∈ Blueprint.reeTitsTags ∧ Blueprint.ReeTitsModel Y t ℓ f := by
  refine HinFor.mono ?_ (hinFor_smallRee.or hinFor_largeReeTits)
  intro Y _ ⟨t, ℓ, f, ht, hY⟩
  simp only [Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact Or.inl ⟨ℓ, f, hY⟩
  · exact Or.inr ⟨_, ℓ, f, Or.inl rfl, hY⟩
  · exact Or.inr ⟨_, ℓ, f, Or.inr rfl, hY⟩

theorem hinFor_exceptionalRep :
    HinFor fun Y _ => Blueprint.ExceptionalRep Y :=
  HinFor.mono (fun _ _ h => h) (hinFor_chevalleyExceptional.or (hinFor_reeTits.or hinFor_suzuki))

end CFSG.ComponentClassification.HarrisLit.Hin
