module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleExcToral
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormRee
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormF4

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Assembly.LowTwoRank

@[expose] def OddExcToralRep (S : Type) [Group S] : Prop :=
  ∃ (t : StatedLieTag) (p f : ℕ), p ≠ 2 ∧ (t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E8) ∧
    ChevalleyExceptionalModel S t p f

@[expose] def OddExcRestRep (S : Type) [Group S] : Prop :=
  ∃ (t : StatedLieTag) (p f : ℕ), p ≠ 2 ∧ (t = .E7 ∨ t = .twistedE6 ∨ t = .trialityD4) ∧
    ChevalleyExceptionalModel S t p f

theorem singleComponentCleanAt_oddExcToral :
    SingleComponentCleanAt (fun S _ => OddExcToralRep S) := by
  refine singleComponentCleanAt_of_bigComponentUniqueAt fun T _ _ hT ⟨t, p, f, hp2, ht, hm⟩ => ?_
  obtain ⟨⟨hp, hf, -⟩, hmod⟩ := hm
  have key : ∀ τ : Tag, OddExcInnerDiagSLForm τ → OddExcInnerDiagNonSLUnique τ →
      UntwistedChevalleyModel T τ (p ^ f) →
        ∃ r : ℕ, r.Prime ∧ BigComponentUniqueAt r T ∧ CentralizerGenerationAt r T := by
    rintro τ hform huniq ⟨K, _, _, hK, ⟨e⟩⟩
    have : CharP K p := finite_field_prime_power_characteristic hp hf hK
    have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have : Finite (ModGL τ K) := finite_modGL
    let e' : T ≃* adjointGroup τ K := e.trans (RankThree.Chevalley.adjointQuotientEquiv τ K)
    have : IsSimpleGroup (adjointGroup τ K) := e'.symm.isSimpleGroup
    refine ⟨ringChar K, (ringChar.eq K p).symm ▸ hp, bigComponentUniqueAt_of_mulEquiv e'
      (bigComponentUniqueAt_adjointGroup hform huniq hp hp2 hK center_adjointGroup_eq_bot),
      centralizerGenerationAt_of_mulEquiv e' (centralizerGenerationAt_adjointGroup τ K hK2)⟩
  rcases ht with rfl | rfl | rfl | rfl
  · exact key .G2 oddExcInnerDiagSLForm_G2 oddExcInnerDiagNonSLUnique_G2 hmod
  · exact key .F4 oddExcInnerDiagSLForm_F4 oddExcInnerDiagNonSLUnique_F4 hmod
  · exact key .E6 oddExcInnerDiagSLForm_E6 oddExcInnerDiagNonSLUnique_E6 hmod
  · exact key .E8 oddExcInnerDiagSLForm_E8 oddExcInnerDiagNonSLUnique_E8 hmod

theorem singleComponentCleanAt_smallRee :
    SingleComponentCleanAt (fun S _ => ∃ p f : ℕ, ReeTitsModel S .twistedG2 p f) := by
  classical
  intro T _ _ hT ⟨p, f, hRT⟩ X Y hXq hYq hXr hYr hXY hXc hYc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUX, hUe, hUc⟩ := exists_fourGroup_of_two_le_pRank hXr
  obtain ⟨A, hAY, hAe, hAc⟩ := exists_fourGroup_of_two_le_pRank hYr
  have : CFSG.IsElementaryAbelian 2 A := hAe
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hAc]; norm_num)
  obtain ⟨⟨y, hyA⟩, hy1'⟩ := exists_ne (1 : A)
  have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext h)
  have hy2 : orderOf y = 2 :=
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian y hyA) hy1
  have hLie : LieModel T .twistedG2 0 p f := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hRT⟩))
  obtain ⟨hXs, hXna, -⟩ := oddReeInvolutionSLForm_holds T 0 p f hLie y hy2 X
    (hXc y (hAY hyA) hy2).1 (hXc y (hAY hyA) hy2).2
  have hZX : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hXna
      have hb : b ∈ center X := by rw [h]; exact mem_top b
      exact absurd (mem_center_iff.1 hb a) hab
  have hYX : Y ≤ centralizer (X : Set T) :=
    commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hXY)
  have hXY1 : ∀ z : T, z ∈ X → z ∈ Y → z = 1 := by
    intro z hzX hzY
    have hz : (⟨z, hzX⟩ : X) ∈ center X := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 (hYX hzY) g g.2)
    rw [hZX, mem_bot] at hz
    exact congrArg Subtype.val hz
  have h8 : ∀ S : Sylow 2 T, Nat.card S = 8 := by
    intro S
    obtain ⟨-, -, hp3, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T p f hRT
    subst hp3
    obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hRT
    have ha' : a' = a := by omega
    subst ha'
    have : CharP K G2.prime := finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
    obtain ⟨E⟩ := hiso a' K hfa hK hw
    have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
    have : Finite (ModGL G2.tag K) := finite_modGL
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
    obtain ⟨-, -, hcard8, ⟨P, hP⟩, -⟩ :=
      Walter.Ree.Model.small_Ree_prime_field_involution_fusion a' K hK' w₀ hw₀
    have hP8 : Nat.card P = 8 := by
      rw [← hcard8, ← hP, card_map_of_injective (G2.reeGamma K a').subtype_injective]
    rw [Sylow.card_eq_multiplicity, ← hP8, Sylow.card_eq_multiplicity, Nat.card_congr E.toEquiv]
  have hUp : IsPGroup 2 U := CFSG.IsElementaryAbelian.isPGroup 2 U
  have hAp : IsPGroup 2 A := CFSG.IsElementaryAbelian.isPGroup 2 A
  have hUA : U ≤ normalizer (A : Set T) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    intro u hu
    rw [mem_centralizer_iff]
    intro a ha
    exact (mem_centralizer_iff.1 (hYX (hAY ha)) u (hUX hu)).symm
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right' hUp hAp hUA).exists_le_sylow
  have hUS : U ≤ S := le_sup_left.trans hS
  have hAS : A ≤ S := le_sup_right.trans hS
  let φ : U × A → (S : Subgroup T) := fun x => ⟨(x.1 : T) * x.2, mul_mem (hUS x.1.2) (hAS x.2.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨u, a⟩ ⟨u', a'⟩ h
    have h' : (u : T) * a = u' * a' := congrArg Subtype.val h
    have hz : (u' : T)⁻¹ * u = a' * (a : T)⁻¹ := by
      calc (u' : T)⁻¹ * u = (u' : T)⁻¹ * (u * a) * (a : T)⁻¹ := by group
        _ = (u' : T)⁻¹ * (u' * a') * (a : T)⁻¹ := by rw [h']
        _ = a' * (a : T)⁻¹ := by group
    have h1 : (u' : T)⁻¹ * u = 1 := hXY1 _ (hUX (mul_mem (inv_mem u'.2) u.2))
      (hz ▸ hAY (mul_mem a'.2 (inv_mem a.2)))
    have huu : u = u' := Subtype.ext (inv_mul_eq_one.1 h1).symm
    subst huu
    have haa : a = a' := Subtype.ext (mul_left_cancel h')
    rw [haa]
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, hUc, hAc, h8 S] at hle
  norm_num at hle

theorem singleComponentCleanAt_oddExceptional_of_rest
    (hrest : SingleComponentCleanAt (fun S _ => OddExcRestRep S)) :
    SingleComponentCleanAt (fun S _ => OddExceptionalRep S) := by
  intro T _ _ hT hP
  rcases hP with ⟨t, p, f, hp2, ht, hm⟩ | hR
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact singleComponentCleanAt_oddExcToral T hT ⟨_, p, f, hp2, Or.inl rfl, hm⟩
    · exact singleComponentCleanAt_oddExcToral T hT ⟨_, p, f, hp2, Or.inr (Or.inl rfl), hm⟩
    · exact singleComponentCleanAt_oddExcToral T hT
        ⟨_, p, f, hp2, Or.inr (Or.inr (Or.inl rfl)), hm⟩
    · exact hrest T hT ⟨_, p, f, hp2, Or.inl rfl, hm⟩
    · exact singleComponentCleanAt_oddExcToral T hT
        ⟨_, p, f, hp2, Or.inr (Or.inr (Or.inr rfl)), hm⟩
    · exact hrest T hT ⟨_, p, f, hp2, Or.inr (Or.inl rfl), hm⟩
    · exact hrest T hT ⟨_, p, f, hp2, Or.inr (Or.inr rfl), hm⟩
  · exact singleComponentCleanAt_smallRee T hT hR

end CFSG.ComponentClassification.Sol76.Sig
