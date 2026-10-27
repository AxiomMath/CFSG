module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36StrongEmb
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbed

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem isSylowOf_top_of_sylow {d : ℕ} [Fact d.Prime] (P : Sylow d G) :
    CFSG.ABGLocalTools.IsSylowOf d (P : Subgroup G) ⊤ :=
  (CFSG.ABGLocalTools.isSylowOf_iff (p := d) (P := (P : Subgroup G)) (K := ⊤)).mpr
    ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩

theorem isStronglyPEmbedded_of_sylow_witness {d : ℕ} [Fact d.Prime] {P : Sylow d G}
    {M : Subgroup G} (hP1 : (P : Subgroup G) ≠ ⊥) (hΓ : rankThreeGamma 1 d (P : Subgroup G) ≤ M)
    (hMtop : M ≠ ⊤) : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M :=
  CFSG.LocalAnalysis.UniquenessCase.UCK.isStronglyPEmbedded_of_rankThreeGamma_le_sylow
    (isSylowOf_top_of_sylow P) hP1 hΓ hMtop

theorem isStronglyPEmbedded_of_twelveCtx (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable M) (d : ℕ) [Fact d.Prime] (hd : d ∈ sigmaSet G M)
    (hdG : d ∣ Nat.card G) : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M := by
  haveI : IsSimpleGroup G := h.cstar.simple
  obtain ⟨P, -, hΓ⟩ := stronglyDEmbedded_of_almost h hns d hd
  exact isStronglyPEmbedded_of_sylow_witness (Sylow.ne_bot_of_dvd_card P hdG) hΓ
    (CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1)

theorem rankThreeSigmaA_dvd_card {G : Type} [Group G] [Finite G] {q : ℕ}
    (h : q ∈ CFSG.Open.rankThreeSigmaA G) : q ∣ Nat.card G := by
  simp only [CFSG.Open.rankThreeSigmaA] at h
  split_ifs at h <;> exact h.2.2.1

theorem isStronglyPEmbedded_of_twelveCtx' {G : Type} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable M) (d : ℕ) [Fact d.Prime] (hd : d ∈ sigmaSet G M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded d M :=
  isStronglyPEmbedded_of_twelveCtx h hns d hd (rankThreeSigmaA_dvd_card hd.1)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
