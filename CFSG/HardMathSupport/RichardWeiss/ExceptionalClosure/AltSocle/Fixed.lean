module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.NaturalSection
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Cooperstein

variable {G : Type} [Group G]

theorem fixed_of_alt_pair' [Finite G]
    (h86 : Asc81bEightSix) (hJ : JordanPrimeCycle) (h85 : Coordinator.GF2EightFive)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {N : ℕ} (hN : N = 12 ∨ N = 16)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin N)) {y : G}
    (hy : y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H)) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  have hpr := hctx.pair
  set S := pCoreOf 2 H with hS
  have hfacts := hpr.blockV_facts h86 hL
  have hVe : IsElemAbelian 2 (blockV S L) := CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hyV : y ∈ blockV S L := (hfacts.2.2.1 ▸ hy : y ∈ blockV S L ⊓ Subgroup.centralizer (S : Set G)).1
  have hV2 : ∀ x ∈ blockV S L, x ^ 2 = 1 := fun x hx => hVe.2 x hx
  have hVc : ∀ a ∈ blockV S L, ∀ b ∈ blockV S L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLV : L ≤ Subgroup.normalizer ((blockV S L : Subgroup G) : Set G) := fun l hl =>
    Coordinator.sup_le_normalizer_blockV S L (Subgroup.mem_sup_left hl)
  have hev : Even N := by rcases hN with rfl | rfl <;> decide
  obtain ⟨-, -, -, -, -, -, -, hsoc⟩ :=
    altNaturalSection_blockV h85 hpr.isKGroup.1 hpr.asc81bHyp hL (by omega) e
  exact three_dvd_of_socleLE_alt_big hJ hN hL.le hLV hV2 hVc e (hsoc hev) hyV

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

end
