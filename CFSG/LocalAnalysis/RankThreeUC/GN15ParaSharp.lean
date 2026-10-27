module

public import CFSG.LocalAnalysis.RankThreeUC.GN15ParaStrong
import CFSG.LocalAnalysis.RankThreeUC.GN15Pair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem c118Univ_mono_left {G : Type*} [Group G] {B C D T₂ : Subgroup G} (hDC : D ≤ C)
    (h : C118Univ B C T₂) : C118Univ B D T₂ := by
  intro Ω _ _ H ι hι hcl
  rcases h Ω H ι hι hcl with h1 | h2 | h3
  · exact Or.inl (le_trans (Subgroup.map_mono fun x hx => hDC hx) h1)
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

section Sharp

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

omit [Finite X] in
theorem gnImg_centralizer_le_of_le {D : Subgroup X} (h : T₁ ≤ D) :
    gnImg T (Subgroup.centralizer (D : Set X)) ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) :=
  Subgroup.map_mono (Subgroup.centralizer_le h)

theorem exists_threeElement_dichotomy_sharp (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) :
    ∃ C : Subgroup X, C ≤ baum T ∧ (C.subgroupOf (baum T)).Characteristic ∧
      C ≤ omegaOneCenterOf (baum T) ∧ C118Univ (baum T) C T₂ ∧ T₁ ≤ C ⊓ gnV T ∧
      ∀ {R : Subgroup X}, baum T ≤ R → R ≤ T → T ⊓ gnC T ≤ R →
        ∀ {c : X ⧸ gnC T}, orderOf c = 3 →
          gnImg T R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (X ⧸ gnC T)) →
          ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) →
          c ∈ gnImg T (Subgroup.centralizer ((C ⊓ gnV T : Subgroup X) : Set X)) ∨
            c ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) ∨
            ∃ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H ∧ IsBlock2 H Kb ∧
              IsAltType Kb 3 ∧ ¬ Kb ≤ gnC T ∧ gnImg T Kb = Subgroup.zpowers c := by
  obtain ⟨h1ne, h1Z, -, h2ne, h2B, h2ch, -⟩ := id hP
  obtain ⟨C₁', C, -, -, -, hT₁C, hCB, hCchar, hCΩ, hCU⟩ := isC118Pair_sharpen hX.sylow.2.1 hP
  have hT₁V : T₁ ≤ gnV T := h1Z.trans Subgroup.le_normalClosure
  have hT₁D : T₁ ≤ C ⊓ gnV T := le_inf hT₁C hT₁V
  refine ⟨C, hCB, hCchar, hCΩ, hCU, hT₁D, ?_⟩
  intro R hBR hRT hCR c hc3 hnorm hnotB
  exact threeElement_dichotomy_strong hX (D := C ⊓ gnV T)
    (fun h => h1ne (le_bot_iff.mp (h ▸ hT₁D))) (inf_le_left.trans hCΩ) inf_le_right h2ne h2B h2ch
    (c118Univ_mono_left inf_le_left hCU) hBR hRT hCR hc3 hnorm hnotB

end Sharp

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
