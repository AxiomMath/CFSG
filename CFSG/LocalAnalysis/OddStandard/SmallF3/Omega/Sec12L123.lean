module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123Inj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsZ

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec123_of_noS5 (hp : Asc82Pre11) (hNoZ4 : Asc82StepNoZ4) (hNoS5 : Sec123NoS5) :
    Asc82Lemma123 := by
  intro G _ _ t L S z K1 K2 E X hctx hX
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨-, -, -, htS, -, -⟩ := hp.basic G t L S z hctx.toSec10Ctx.toSec10Z
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have hAlt : Sec122Alt1 (secV t S L E) X :=
    hX.alt.resolve_right fun h => hNoZ4 G t L S z K1 K2 E hctx h.1
  have hX60 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) := by
    obtain ⟨-, V1, V2, -, -, h | h⟩ := id hAlt
    · exact h.1
    · exact absurd h.1 (hNoS5 G t L S z K1 K2 E X hctx hX hAlt)
  obtain ⟨φ, hφ, -, -, hlast⟩ := F.bdata.2.2.2.2.2
  have hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)) := by
    rw [F.bdata.2.2.2.2.1]
    exact hφ
  have hXYc : X ≤ (secM t S L ⊓ L) ⊔ S := le_sup_left.trans hX.sup.le
  have hXN : X ≤ normalizer (secA t S L : Set G) := hXYc.trans (sec122_Yc_le_M F)
  have hker : X ⊓ centralizer (secA t S L : Set G) = ⊥ := sec123_ker_cent F hS htS hXYc hX.inf
  have heq : autIn X (secA t S L) = autIn (secCMt t S L) (secA t S L) :=
    sec123_autIn_eq F hS htS hX.inf hX.sup hX60 hperm hlast
  refine ⟨hX60, hker, heq, ?_⟩
  obtain ⟨e₁⟩ := sec123_autIn_equiv hXN hker
  obtain ⟨e₂⟩ := hX60
  rw [← heq]
  exact ⟨e₁.trans e₂⟩

theorem asc82Lemma123_of (hp : Asc82Pre11) (h121 : Asc82Lemma121) (h63 : Asc82Lemma63)
    (hH : ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
        Asc82Hyp62 G) (h65 : Asc82Lemma65) (hNoZ4 : Asc82StepNoZ4) : Asc82Lemma123 :=
  sec123_of_noS5 hp hNoZ4 (sec123_noS5_of hp h121 h63 hH h65)

end CFSG.OddStandard.SmallF3.Omega
