module

public import CFSG.CGT.PushingUpLit.BHS.ThreeEightAux
public import CFSG.CGT.PushingUpLit.BHS.Prelim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.CGT.PushingUpLit.BHS.ThreeSeven

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Lift.Piece
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

theorem charTwo_top_of_charTwo' {Γ : Type*} [Group Γ] {X : Subgroup Γ} (h : CharTwo X) :
    CharTwo (⊤ : Subgroup ↥X) := by
  have h' : CharTwo (X.subgroupOf X) := by
    rw [CT.charTwo_iff_internal] at h ⊢
    exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
      (Subgroup.subgroupOfEquivOfLe (le_refl X)).symm h
  rwa [Subgroup.subgroupOf_self] at h'

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_pushUp_parabolics {G T V : Subgroup Γ}
    (hG : CharTwo G) (hT : IsSylowTwoOf T G) (hne : cStarIn G T ≠ G)
    (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (hVT : omegaOneCenterOf T ≤ V) (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G))
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ (g : ↥G) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer (G : Set Γ)).subgroupOf V) :
    ∃ P' : Subgroup Γ, P' ≤ G ∧ baum T ≤ P' ∧ V ≤ P' ∧ IsSylowTwoOf (baum T) P' ∧
      IsMinParabolic2 (baum T) P' ∧ CharTwo P' ∧ (P'.subgroupOf G).map α = ⊤ ∧
      (∀ C : Subgroup Γ, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
        ¬ P' ≤ Subgroup.normalizer (C : Set Γ)) ∧
      (∀ t ∈ T, ∃ b ∈ baum T, b⁻¹ * t ∈ Subgroup.centralizer (V : Set Γ)) ∧
      ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (V : Set Γ) := by
  classical
  have hT2 : IsPGroup 2 T := hT.2.1
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    apply hne
    refine le_antisymm (cStarIn_le G ⊥) fun g hg => ?_
    have hΩ : omegaOneCenterOf (⊥ : Subgroup Γ) = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.closure_le _).mpr fun x hx => ?_)
      exact hx.1.1
    refine centralizer_le_cStarIn G ⊥ ⟨hg, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have h1 : h = 1 := Subgroup.mem_bot.mp (hΩ ▸ hh)
    simp [h1]
  have hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T :=
    (inf_le_inf_left G (Subgroup.centralizer_le fun x hx => hVT hx)).trans
      (centralizer_le_cStarIn G T)
  have hOT : pCoreOf 2 G ≤ T := hT.pCoreOf_le
  have hVQ' : V ≤ pCoreOf 2 G := hVQ.trans (C1GN.omegaOneCenterOf_le_self _)
  have hVT' : V ≤ T := hVQ'.trans hOT
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_le' hVQ (isElemAbelian_omegaOneCenterOf' _)
  have hb0 : baum T ≠ ⊥ := C1GN.baum_ne_bot hT2 hT0
  have hTC : T ≤ cStarIn G T := le_cStarIn_self hT.1 hT2 hT0
  obtain ⟨P, hTP, hPG, hPC, hmin⟩ := exists_minimal_not_le (S := T) (Y := G) (M := cStarIn G T)
    hT.1 (fun h => hne (le_antisymm (cStarIn_le G T) h))
  have hminP : IsMinParabolic2 T P := isMinParabolic2_of_minimal hT hT0 hTP hPG hPC hmin
  have hVP : V ≤ P := hVT'.trans hTP
  have hVnP : P ≤ Subgroup.normalizer (V : Set Γ) := hPG.trans hVn
  have hPtop : (P.subgroupOf G).map α = ⊤ :=
    map_eq_top_of_not_le_cStarIn hT hT0 hVn hC α hα hαk (le_sup_of_le_left hTP) hPG hPC
  obtain ⟨hαP, hαkP, hβeP, hβkP⟩ := natural_data_restrict α hαk β hβe hβk hPG hPtop
  have hbaum : ¬ baum T ≤ Subgroup.centralizer (V : Set Γ) :=
    baum_not_le_centralizer hT hT0 hVn hC hne
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) :=
    thompsonJ_not_le_centralizer hVT' hVe hbaum
  obtain ⟨hSylH₀, hVH₀, hαH₀, hTSC⟩ :=
    three_seven_linear hminP hVP hVe hVnP (α.comp (Subgroup.inclusion hPG)) hαP hαkP β hβ hβeP
      hβkP hJ
  have hSP : baum T ≤ twoResidual P ⊔ baum T := le_sup_right
  have hH₀P : twoResidual P ⊔ baum T ≤ P :=
    sup_le (twoResidual_le P) ((inf_le_left : baum T ≤ T).trans hTP)
  have hH₀C : ¬ twoResidual P ⊔ baum T ≤ cStarIn G T := by
    intro h
    apply map_cStarIn_ne_top (cStarIn_le G T) α hαk hC hne
    refine top_unique fun A _ => ?_
    obtain ⟨x, hxH, hxA⟩ := hαH₀ A
    exact ⟨⟨x, hPG x.2⟩, Subgroup.mem_subgroupOf.mpr (h hxH), hxA⟩
  obtain ⟨P', hSP', hP'H₀, hP'C, hminP'⟩ := exists_minimal_not_le (S := baum T)
    (Y := twoResidual P ⊔ baum T) (M := cStarIn G T) hSP hH₀C
  have hP'P : P' ≤ P := hP'H₀.trans hH₀P
  have hP'G : P' ≤ G := hP'P.trans hPG
  have hSylP' : IsSylowTwoOf (baum T) P' := isSylowTwoOf_of_le hSylH₀ hSP' hP'H₀
  have hP'T : P' ⊔ T = P := by
    by_contra hne'
    have hlt : P' ⊔ T < P := lt_of_le_of_ne (sup_le hP'P hTP) hne'
    exact hP'C (le_sup_left.trans (hmin (P' ⊔ T) le_sup_right hlt))
  have hTn : T ≤ Subgroup.normalizer (baum T : Set Γ) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hnn' : ¬ P' ≤ Subgroup.normalizer (baum T : Set Γ) := by
    intro hn
    apply hPC
    have : P ≤ Subgroup.normalizer (baum T : Set Γ) := hP'T ▸ sup_le hn hTn
    exact fun x hx => inf_normalizer_baum_le_cStarIn hb0 ⟨hPG hx, this hx⟩
  have hSC : baum T ≤ cStarIn G T := (inf_le_left : baum T ≤ T).trans hTC
  have hminP'' : IsMinParabolic2 (baum T) P' :=
    isMinParabolic2_of_minimal_gen hSylP' hSC hnn' hP'C hminP'
  have hαP'top : (P'.subgroupOf G).map α = ⊤ := by
    refine map_eq_top_of_not_le_cStarIn hT hT0 hVn hC α hα hαk ?_ hP'G hP'C
    intro t ht
    obtain ⟨b, hb, hbt⟩ := hTSC t ht
    have htG : t ∈ G := hT.1 ht
    have hbG : b ∈ G := hT.1 ((inf_le_left : baum T ≤ T) hb)
    have e : t = b * (b⁻¹ * t) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (hSP' hb) ⟨G.mul_mem (G.inv_mem hbG) htG, hbt⟩
  have hVH₀n : twoResidual P ⊔ baum T ≤ Subgroup.normalizer (V : Set Γ) := hH₀P.trans hVnP
  have hVS : V ≤ baum T :=
    (le_pCoreOf_of_normalizes (p := 2) hVH₀ hVH₀n (hT2.to_le hVT')).trans hSylH₀.pCoreOf_le
  have hVP' : V ≤ P' := hVS.trans hSP'
  have hcharP : CharTwo P := two_two_core hG (hOT.trans hTP) hPG
  have hTnH₀ : T ≤ Subgroup.normalizer ((twoResidual P ⊔ baum T : Subgroup Γ) : Set Γ) := by
    intro t ht
    have h1 : t ∈ Subgroup.normalizer (twoResidual P : Set Γ) :=
      le_normalizer_twoResidual P (hTP ht)
    exact C1.mem_normalizer_sup h1 (hTn ht)
  have hTsylP : IsSylowTwoOf T P := isSylowTwoOf_of_le hT hTP hPG
  have hcharH₀ : CharTwo (twoResidual P ⊔ baum T) :=
    two_two_normalizes hcharP hH₀P (hTsylP.pCoreOf_le.trans hTnH₀)
  have hcharP' : CharTwo P' := two_two_core hcharH₀ (hSylH₀.pCoreOf_le.trans hSP') hP'H₀
  refine ⟨P', hP'G, hSP', hVP', hSylP', hminP'', hcharP', hαP'top, ?_, hTSC, ?_⟩
  · intro C hCS hC0 hCchar hn
    apply hPC
    have hTC' : T ≤ Subgroup.normalizer (C : Set Γ) :=
      hTn.trans (normalizer_le_normalizer_of_char' hCS hCchar)
    have hPn : P ≤ Subgroup.normalizer (C : Set Γ) := hP'T ▸ sup_le hn hTC'
    have hle : G ⊓ Subgroup.normalizer (C : Set Γ) ≤ cgsIn G (baum T) :=
      le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hC0 (le_iSup_of_le hCchar le_rfl)))
    intro x hx
    exact Subgroup.mem_sup_right (hle ⟨hPG hx, hPn hx⟩)
  · rw [B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum T) inf_le_left]
    exact hJ

end CFSG.CGT.PushingUpLit.BHS
