module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG

theorem pRank_map_eq_of_not_dvd_card_ker {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) {p : Nat} (hp : p.Prime)
    (hker : ¬ p ∣ Nat.card ↥(MonoidHom.ker f)) (H : Subgroup X) :
    CFSG.Open.pRank p (H.map f) = CFSG.Open.pRank p H := by
  have hp1 : 1 < p := hp.one_lt
  let φ : ↥H →* Y := f.comp H.subtype
  have hkerφ : ¬ p ∣ Nat.card ↥φ.ker := by
    have hdvd : Nat.card ↥φ.ker ∣ Nat.card ↥(MonoidHom.ker f) := by
      rw [show φ.ker = (MonoidHom.ker f).comap H.subtype from
        (MonoidHom.comap_ker f H.subtype).symm]
      exact Subgroup.card_comap_dvd_of_injective (MonoidHom.ker f) H.subtype
        H.subtype_injective
    exact fun h => hker (h.trans hdvd)
  haveI : Fact p.Prime := ⟨hp⟩
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ φ.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_quotient_eq φ.ker hkerφ
  have hrange : φ.range = H.map f := by
    rw [show φ = f.comp H.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have htop : CFSG.Open.pRank p (H.map f) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥φ.range) := by
    rw [← hrange]
    exact CFSG.SectionRank.pRank_eq_pRank_top_subgroup φ.range
  have hequiv : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ φ.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥φ.range) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 (QuotientGroup.quotientKerEquivRange φ)
  have htopH : CFSG.Open.pRank p (⊤ : Subgroup ↥H) = CFSG.Open.pRank p H :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm
  calc
    CFSG.Open.pRank p (H.map f) = CFSG.Open.pRank p (⊤ : Subgroup ↥φ.range) := htop
    _ = CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ φ.ker)) := hequiv.symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥H) := hquot
    _ = CFSG.Open.pRank p H := htopH

end CFSG
