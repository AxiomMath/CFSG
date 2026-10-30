module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleConcl
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleBQModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem gOrbConclS_of_hasBQGraph {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hL : IsSimpleGroup ↥L) (hG : Core.HasBQGraph ↥L) (hRN : R ≤ Subgroup.normalizer (L : Set Y))
    (hR2 : IsPGroup 2 R) (hSyl : IsSylowTwoOf (R ⊓ L) L) (hMin : IsMinOverBorel L (R ⊓ L) P)
    (hnP : ¬ R ≤ Subgroup.normalizer (P : Set Y)) : GOrbConclS R P := by
  haveI := hL
  obtain ⟨K, _, _, D, n, H, π, M, hπ, hnode, hedge⟩ := hG
  obtain ⟨π', h', hT⟩ := SimpleBQ.exists_borelQuotient_conj hSyl hπ
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hLN : L ≤ Subgroup.normalizer ((R ⊓ L : Subgroup Y) : Set Y) := fun x hx =>
      Subgroup.centralizer_le_normalizer _ fun y hy => by
        have := hcon ⟨y, (Subgroup.mem_inf.1 hy).2⟩ ⟨x, hx⟩
        simpa using congrArg Subtype.val this
    have h1 : L < P := by
      have := hMin.2.1
      rwa [inf_eq_left.2 hLN] at this
    exact not_lt_of_ge hMin.1 h1
  exact SimpleBQ.concl_of_core h' hRN hR2 hT hMin hnP fun h𝒜 h𝒜2 i hmove =>
    Core.core_alternative h' hnode hedge hnc _ h𝒜2 h𝒜 i hmove

end CFSG.AGLEmbeddingD2.Tits.GN516
