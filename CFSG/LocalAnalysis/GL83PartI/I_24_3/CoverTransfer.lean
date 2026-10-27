module

public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverQuotient
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.Walter.AStar.Subnormal
import CFSG.Assembly.Subnormal

public section

namespace GL83.I243

namespace Cover

open CFSG.Open

theorem weakCore_eq_top_of_cover {L : Type} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    (hq : CFSG.Open.IsQuasisimple L) (hZ : CFSG.pCore p L ≠ ⊥)
    (hcyc : IsCyclic ↥(CFSG.pCore p L))
    (hcw : ∀ (K' : Type) [Group K'] [Finite K'], CFSG.Open.IsQuasisimple K' →
      Subgroup.center K' ≠ ⊥ → IsPGroup p (Subgroup.center K') →
      IsCyclic (Subgroup.center K') →
      Nonempty (K' ⧸ Subgroup.center K' ≃* (L ⧸ Subgroup.center L)) →
      ∀ T : Sylow p K', GLBWeakCore p (T : Subgroup K') = ⊤)
    (T : Sylow p L) : GLBWeakCore p (T : Subgroup L) = ⊤ := by
  have hρ : Function.Surjective (QuotientGroup.mk' (primeCentre p L)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (primeCentre p L)).ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact primeCentre_le_center
  have hcop : Nat.Coprime p (Nat.card (QuotientGroup.mk' (primeCentre p L)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact coprime_card_primeCentre
  have h1 := hcw (L ⧸ primeCentre p L) (isQuasisimple_quotient hq) (center_quotient_ne_bot hq hZ)
    (isPGroup_center_quotient hq) (isCyclic_center_quotient hq hcyc)
    (nonempty_equiv_center_quotient hq) (T.mapSurjective hρ)
  rw [Sylow.coe_mapSurjective] at h1
  have h2 := weakCore_map_le_map_weakCore _ hρ hker hcop T.isPGroup'
  rw [h1] at h2
  have h3 : GLBWeakCore p (T : Subgroup L) ⊔ primeCentre p L = ⊤ := by
    have h4 := Subgroup.comap_map_eq (QuotientGroup.mk' (primeCentre p L))
      (GLBWeakCore p (T : Subgroup L))
    rw [top_le_iff.1 h2, Subgroup.comap_top, QuotientGroup.ker_mk'] at h4
    exact h4.symm
  exact eq_top_of_sup_eq_top_of_le_center hq.1 primeCentre_le_center h3

end Cover

open CFSG CFSG.Open

theorem le_weakCore_of_cover
    {X : Type} [Group X] [Finite X] (R : Sylow 3 X) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZ : CFSG.pCore 3 ↥K ≠ ⊥) (hcyc : IsCyclic ↥(CFSG.pCore 3 ↥K))
    (hcw : ∀ (K' : Type) [Group K'] [Finite K'], Open.IsQuasisimple K' →
      Subgroup.center K' ≠ ⊥ → IsPGroup 3 (Subgroup.center K') → IsCyclic (Subgroup.center K') →
      Nonempty (K' ⧸ Subgroup.center K' ≃* (↥K ⧸ Subgroup.center ↥K)) →
      ∀ T : Sylow 3 K', GLBWeakCore 3 (T : Subgroup K') = ⊤) :
    K ≤ GLBWeakCore 3 (R : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (CFSG.Open.IsSubnormal.top_iff.1 hK.2.1)
  have htop := Cover.weakCore_eq_top_of_cover hK.2.2 hZ hcyc hcw S
  have h1 := Cover.map_weakCore_le_weakCore_map Nat.prime_three K.subtype
    (T := (S : Subgroup K)) (fun t _ ht => Subtype.ext ht)
  rw [htop, Subgroup.map_top, Subgroup.range_subtype, hS] at h1
  exact h1.trans (CFSG.PreuniquenessRankFour.Helpers.weakCore_mono 3 Nat.prime_three inf_le_left)

end GL83.I243
