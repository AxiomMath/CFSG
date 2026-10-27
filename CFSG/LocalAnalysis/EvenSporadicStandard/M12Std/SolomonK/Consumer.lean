module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child4Final

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier.Co3
open CFSG.EvenSmallLie.SympSix CFSG.SectionRank

@[expose] def Yoshida74LocalK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ t : G, orderOf t = 2 →
    Nonempty (centralizer ({t} : Set G) ≃* Multiplicative (ZMod 2) × Carrier .M12) →
      ∃ c : G, orderOf c = 2 ∧ commutator (centralizer ({c} : Set G)) = ⊤ ∧
        Nat.card (center (centralizer ({c} : Set G))) = 2 ∧
        SolomonA12HypK (centralizer ({c} : Set G) ⧸ center (centralizer ({c} : Set G)))

theorem centralizer_ne_top_of_perfect {G : Type} [Group G] [IsSimpleGroup G] {c : G}
    (hc : c ≠ 1) (hperf : commutator (centralizer ({c} : Set G)) = ⊤)
    (hZ : Nat.card (center (centralizer ({c} : Set G))) = 2) :
    centralizer ({c} : Set G) ≠ ⊤ := by
  intro htop
  have hcc : c ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({c} : Set G) := htop ▸ mem_top g
    exact (mem_centralizer_iff.1 hg c (Set.mem_singleton c)).symm
  have hcenter : center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact absurd (mem_bot.1 (h ▸ hcc)) hc
    · exact h
  have hcomm : ∀ a b : G, a * b = b * a := fun a b =>
    mem_center_iff.1 (hcenter ▸ mem_top b) a
  have hcP : center (centralizer ({c} : Set G)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hcomm _ _)
  have hbot : commutator (centralizer ({c} : Set G)) = ⊥ :=
    (commutator_eq_bot_iff_center_eq_top (centralizer ({c} : Set G))).2 hcP
  have h1 : (⊥ : Subgroup (centralizer ({c} : Set G))) = ⊤ := hbot.symm.trans hperf
  have h2 : Nat.card (center (centralizer ({c} : Set G))) = 1 := by
    rw [hcP, Subgroup.card_top, ← Subgroup.card_top, ← h1, Subgroup.card_bot]
  omega

theorem isKGroupCat_centralQuotient {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper Catalog G) {c : G} (hP : centralizer ({c} : Set G) ≠ ⊤) :
    IsKGroupCat (centralizer ({c} : Set G) ⧸ center (centralizer ({c} : Set G))) :=
  (CFSG.QuasithinUnique.isKGroupCat_of_kProper hK hP).quotient _

@[expose] def Yoshida74Co3K : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G → IsSimpleGroup G →
    ∀ t : G, orderOf t = 2 →
      Nonempty (centralizer ({t} : Set G) ≃* Multiplicative (ZMod 2) × Carrier .M12) →
        IsSporadic G .Co3

@[expose] def Yoshida74SecondCentralizerK :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G → IsSimpleGroup G →
    ∀ t : G, orderOf t = 2 →
      Nonempty (centralizer ({t} : Set G) ≃* Multiplicative (ZMod 2) × Carrier .M12) →
        ∃ (s : G) (θ : co3M ≃* centralizer ({s} : Set G)), (θ co3ZM : G) = s

section Certified

set_option linter.unusedSectionVars false

theorem yoshida74SecondCentralizerK_of_localK (hL : Yoshida74LocalK) (hS : SolomonA12InputK) :
    Yoshida74SecondCentralizerK := by
  intro G _ _ hK hG t ht e
  obtain ⟨c, hc2, hperf, hZ, hhyp⟩ := hL G hG t ht e
  have hc1' : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    omega
  have : Finite (centralizer ({c} : Set G) ⧸ center (centralizer ({c} : Set G))) := inferInstance
  have hX := hS _ (isKGroupCat_centralQuotient hK (centralizer_ne_top_of_perfect hc1' hperf hZ))
    hhyp
  have hcmem : (⟨c, mem_centralizer_iff.2 (by simp)⟩ : centralizer ({c} : Set G)) ∈
      center (centralizer ({c} : Set G)) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (by
      have := mem_centralizer_iff.1 g.2 c (by simp)
      simpa using this.symm)
  have hc1 : (⟨c, mem_centralizer_iff.2 (by simp)⟩ : centralizer ({c} : Set G)) ≠ 1 := by
    intro h
    exact hc1' (congrArg Subtype.val h)
  obtain ⟨θ, hθ⟩ := CFSG.EvenSmallLie.SympSix.sp62_double_cover_unique_of_mem_center
    (centralizer ({c} : Set G)) hperf hZ hX hcmem hc1
  exact ⟨c, θ, congrArg Subtype.val hθ⟩

end Certified

section CertifiedCo3

set_option linter.unusedSectionVars false

theorem yoshida74Co3K_of_secondCentralizerK (hS : Yoshida74SecondCentralizerK) :
    Yoshida74Co3K := by
  intro G _ _ hK hG t ht2 e
  obtain ⟨s, θ, hθ⟩ := hS G hK hG t ht2 e
  obtain ⟨hH2, hH3⟩ := fendelInputs_of_asc03 CFSG.Quasithin.s_Asc03_simple G hG s θ hθ
  exact Co3Ident.isSporadic_co3_of_centralizer θ hθ hH2 hH3

end CertifiedCo3

section CertifiedLocal

set_option linter.unusedSectionVars false

theorem yoshida74Co3K_of_localK (hL : Yoshida74LocalK) (hS : SolomonA12InputK) :
    Yoshida74Co3K :=
  yoshida74Co3K_of_secondCentralizerK (yoshida74SecondCentralizerK_of_localK hL hS)

end CertifiedLocal

end CFSG.EvenSporadicStandard.M12Std.SolomonK
