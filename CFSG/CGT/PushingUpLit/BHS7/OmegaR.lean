module

public import CFSG.CGT.PushingUpLit.BHS7.ClaimA
public import CFSG.CGT.PushingUpLit.BHS7.OmegaCentral

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem mem_btBlocksMax_of_subnormal (h : MinCex G T) {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hsub : IsSubnormal F G) : F ∈ btBlocksMax G T := by
  have hFG : F ∈ btBlocksG G T := mem_btBlocksG_of_isBTBlock hF
  refine ⟨hFG, fun F' hF' hle => ?_⟩
  rcases six_twelve_c h.charTwo h.sylow hFG hsub hF' with h1 | h1
  · exact le_antisymm h1 hle
  · exfalso
    have hc : ⁅F, F⁆ = ⊥ := le_bot_iff.mp (h1 ▸ Subgroup.commutator_mono hle le_rfl)
    have h2 : pCoreOf 2 F = ⊥ := by
      have h3 : ⁅pCoreOf 2 F, F⁆ ≤ ⁅F, F⁆ :=
        Subgroup.commutator_mono (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F) le_rfl
      rw [hc, hF.perfect] at h3
      exact le_bot_iff.mp h3
    exact pCoreOf_ne_bot hF (charTwo_of_isBTBlock h.charTwo h.sylow hF) h2

theorem omegaR_le_cStarIn (h : MinCex G T) {E₀ : Subgroup Γ}
    (hE₀ : E₀ ∈ omegaSet G T) : omegaR G T ≤ cStarIn G T := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  set R : Subgroup Γ := omegaR G T with hRdef
  have hRG : R ≤ G := omegaR_le
  have hRn : G ≤ Subgroup.normalizer (R : Set Γ) := le_normalizer_omegaR
  have hTL : T ≤ R ⊔ T := le_sup_right
  have hLG : R ⊔ T ≤ G := sup_le hRG hT.1
  have hTR : T ≤ Subgroup.normalizer (R : Set Γ) := hT.1.trans hRn
  have hblock_le : ∀ (S F : Subgroup Γ), IsBTBlock G S F → F ≤ R ⊔ T → F ≤ R := fun S F hF hFL =>
    le_of_forall_odd_le (opResidual_eq_of_isBTBlock hF) fun x hx hodd =>
      mem_of_odd_orderOf_sup hT.2.1 hTR (hFL hx) hodd
  have hE₀b : IsBTBlock G T E₀ := omega_isBTBlock h hE₀
  have hlt : R ⊔ T < G := by
    refine lt_of_le_of_ne hLG fun hEq => ?_
    exact omega_not_le_omegaR h hE₀ (hblock_le T E₀ hE₀b (hEq ▸ hE₀b.le))
  by_contra hRC
  have hLC : ¬ R ⊔ T ≤ cStarIn G T := fun hl => hRC ((le_sup_left : R ≤ R ⊔ T).trans hl)
  have hBL : baum T ≤ R ⊔ T := (inf_le_left : baum T ≤ T).trans hTL
  have hTL' : IsSylowTwoOf T (R ⊔ T) := isSylowTwoOf_of_le_of_le hT hTL hLG
  obtain ⟨-, -, hconcl⟩ := seven_three h hT ⟨hlt, hBL, hLC⟩ hTL'
  obtain ⟨𝒢, hbl, hinv, hcomm, hsup, -⟩ := hconcl
  have hex : ∃ F ∈ 𝒢, ¬ F ≤ cStarIn G T := by
    by_contra hall
    push Not at hall
    apply hLC
    rw [← hsup]
    exact sup_le (two_three_d hT hb0 hlt.le hTL' (inf_le_left : baum T ≤ T))
      (iSup₂_le fun F hF => hall F hF)
  obtain ⟨F, hF, hFn⟩ := hex
  have hFb : IsBTBlock (R ⊔ T) T F := hbl F hF
  have hFG : IsBTBlock G T F := isBTBlock_of_sub hFb hLG rfl hFn
  have hFR : F ≤ R := hblock_le T F hFG hFb.le
  have hsubL : IsSubnormal F (R ⊔ T) := isSubnormal_of_mem_concl hbl hinv hcomm hF
  have hsubR : IsSubnormal F R := A3.subnormal_of_le_of_le hsubL hFR le_sup_left
  have hsubG : IsSubnormal F G :=
    A3.subnormal_trans hsubR (isSubnormal_of_le_of_le_normalizer hRG hRn)
  have hFmax : F ∈ btBlocksMax G T := mem_btBlocksMax_of_subnormal h hFG hsubG
  have hFΩ : F ∈ omegaSet G T :=
    ⟨mem_bStarG_of_mem_bStarT ⟨⟨hFmax, hFG⟩, hFn⟩, hsubG⟩
  exact omega_not_le_omegaR h hFΩ hFR

end CFSG.CGT.PushingUpLit.BHS7
