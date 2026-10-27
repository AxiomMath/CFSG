module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem isSQTKCat_of_le {G : Type} [Group G] [Finite G] {H L : Subgroup G} (hLH : L ≤ H)
    (hH : IsSQTKCat ↥H) : IsSQTKCat ↥L :=
  CFSG.SectionRank.IsSQTKCat.of_le hLH hH

theorem ResidualFamily.of_alt_six {S : Type} [Group S]
    (h : Nonempty (S ≃* alternatingGroup (Fin 6))) : ResidualFamily S := Or.inl h

theorem ResidualFamily.of_psu_three_three {S : Type} [Group S]
    (h : StatedClassicalModel S .PSU 3 3 1) : ResidualFamily S := Or.inr (Or.inl h)

theorem ResidualFamily.of_classical_two {S : Type} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSL 3 2 f ∨ StatedClassicalModel S .PSU 3 2 f ∨
      StatedClassicalModel S .PSp 2 2 f) : ResidualFamily S :=
  Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩))

theorem ResidualFamily.of_G2 {S : Type} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : ResidualFamily S :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩)))

theorem ResidualFamily.of_triality {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : ResidualFamily S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩))))

theorem ResidualFamily.of_largeRee {S : Type} [Group S] {f : ℕ} (hf : Odd f) (hf3 : 3 ≤ f)
    (h : ReeTitsModel S .twistedF4 2 f) : ResidualFamily S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hf3, h⟩)))))

theorem ResidualFamily.of_Tits {S : Type} [Group S] (h : ReeTitsModel S .Tits 2 1) :
    ResidualFamily S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem familyRestriction
    (hlayer : ActorLayerProp) (hspor : NoSporadicComponentProp)
    (hSuz : NoSuzukiComponentProp) (hA78 : NoAlt78BinaryLinearProp)
    (hodd : OddClassicalSmallProp) : FamilyRestrictionProp := by
  intro V _ _ H T M E hFF hns hSQTK hnoSL2 L hL
  have hquasi : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComp hL
  have hLH : L ≤ H := hL.1
  have hLay : ActorLayer V H T M := hlayer V H T M E hFF hns
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := hLay.odd_card_center hL
  have hSQTK_L : IsSQTKCat ↥L := isSQTKCat_of_le hLH hSQTK
  have hstep : CatalogStepConclusion ↥L := catalogStepHyp ↥L hquasi hSQTK_L hZodd
  have hSQT_S : CFSG.IsStronglyQuasithin (CQ L) := hstep.2 (Subgroup.center ↥L) le_rfl
  refine ⟨?_, hstep.1, hSQT_S⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have premise5 : Nonempty (CQ L ≃* alternatingGroup (Fin 5)) → False := by
    rintro ⟨e⟩
    have hF : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    obtain ⟨e'⟩ := specialLinear_two_equiv_alternating_five (GaloisField 2 2)
      (by rw [hF]; norm_num)
    exact hnoSL2 L hL (GaloisField 2 2) 2 le_rfl hF ⟨e.trans e'.symm⟩
  have hnonab : ∃ a b : CQ L, a * b ≠ b * a := hquasi.2.2
  have hcat : Catalog (CQ L) := catalog_center_quotient hquasi hSQTK_L.2
  have hlist := CFSG.Milestones.cl_lit_sqtk_simple_list (CQ L) hnonab hSQT_S hcat
  obtain ⟨hA7, hAn⟩ := hA78 V H T M E hFF hns L hL
  have hsl2 : ∀ f : ℕ, 2 ≤ f → StatedClassicalModel (CQ L) .PSL 2 2 f → False := by
    intro f hf hmod
    obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := hmod
    have : CharP K' 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := f) hK'
    exact hnoSL2 L hL K' f hf hK' ⟨e.trans (statedProjSL_two_equiv K')⟩
  have hbin : ∀ n : ℕ, 3 ≤ n → StatedClassicalModel (CQ L) .PSL n 2 1 → False := by
    intro n hn hmod
    obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := hmod
    exact hAn n hn ⟨e.trans (statedProjSL_equiv_of_card_two n K' (by simpa using hK'))⟩
  rcases hlist with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd'⟩ | (⟨f, hf⟩ | hTits) |
    ⟨n, hn, hmod⟩ | ⟨s, -, ⟨e⟩⟩
  ·
    rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 by omega) with rfl | rfl | rfl | rfl
    · exact (premise5 ⟨e⟩).elim
    · exact ResidualFamily.of_alt_six ⟨e⟩
    · exact (hA7 7 (Or.inl rfl) ⟨e⟩).elim
    · exact (hA7 8 (Or.inr rfl) ⟨e⟩).elim
  ·
    have hsmall : ∀ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel (CQ L) t n p f →
        ResidualFamily (CQ L) := by
      intro t n f hmod
      have h3 := hodd V H T M E hFF hns hSQTK L hL p hp hp2 t n f hmod
      rcases h3 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact (premise5 (alternating_five_of_model_five hmod)).elim
      · exact ResidualFamily.of_alt_six (alternating_six_of_model_nine hmod)
      · exact ResidualFamily.of_psu_three_three hmod
    rcases hodd' with ⟨f, -, hmod⟩ | hmod | hmod
    · exact hsmall _ _ _ hmod
    · exact hsmall _ _ _ hmod
    · exact hsmall _ _ _ hmod
  ·
    rcases hf with ⟨hf, hmod⟩ | ⟨hf, hmod⟩ | ⟨hf, hmod⟩ | ⟨hf, hmod⟩ | ⟨hf, hmod⟩ | ⟨hf, hmod⟩ |
      ⟨hf, hf3, hmod⟩ | ⟨hf, hf3, hmod⟩
    · exact (hsl2 f hf hmod).elim
    · by_cases hf1 : f = 1
      · subst hf1
        exact (hbin 3 le_rfl hmod).elim
      · exact ResidualFamily.of_classical_two (by omega) (Or.inl hmod)
    · exact ResidualFamily.of_classical_two hf (Or.inr (Or.inl hmod))
    · exact ResidualFamily.of_classical_two hf (Or.inr (Or.inr hmod))
    · exact ResidualFamily.of_G2 hf hmod
    · exact ResidualFamily.of_triality hf hmod
    · exact ResidualFamily.of_largeRee hf hf3 hmod
    · exact (hSuz V H T M E hFF L hL f hmod).elim
  · exact ResidualFamily.of_Tits hTits
  · exact (hbin n (by omega) hmod).elim
  · exact (hspor V H T M E hFF hns hSQTK.1 L hL ⟨s, ⟨e⟩⟩).elim

end CFSG.QuasithinUnique.Setup.Family
