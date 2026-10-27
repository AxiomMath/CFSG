module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Quotient
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.ABGLocalTools (IsSylowOf)

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
  (qs_injOn qs_ker qs_inf_ker qs_not_dvd_core centralizer_map_quotient
    pRank_map_eq_of_coprime_ker)

section Transfer

variable {X : Type} [Group X] [Finite X]

theorem k3_transfer (S : Sylow 3 X) (hSW : Nonempty ((S : Subgroup X) ≃* W3))
    (hx : ∃ x ∈ (S : Subgroup X), x ≠ 1 ∧ x ^ 3 = 1 ∧
      CFSG.Open.pRank 3 (centralizer ({x} : Set X)) ≤ 2) :
    ∃ S' : Sylow 3 (Bar X), Nonempty ((S' : Subgroup (Bar X)) ≃* W3) ∧
      ∃ x ∈ (S' : Subgroup (Bar X)), x ≠ 1 ∧ x ^ 3 = 1 ∧
        CFSG.Open.pRank 3 (centralizer ({x} : Set (Bar X))) ≤ 2 := by
  obtain ⟨e⟩ := hSW
  obtain ⟨x, hxS, hx1, hx3, hxr⟩ := hx
  have hsurj : Function.Surjective (barMk X) :=
    QuotientGroup.mk'_surjective (primeComplementCore (G := X) 3)
  have hO : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) := qs_not_dvd_core
  have hinj : Function.Injective ((barMk X).comp (S : Subgroup X).subtype) := by
    intro a b hab
    exact Subtype.ext (qs_injOn (Q := (S : Subgroup X)) S.isPGroup' a.2 b.2 hab)
  have hrange : ((barMk X).comp (S : Subgroup X).subtype).range =
      (S : Subgroup X).map (barMk X) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have phiS : (S : Subgroup X) ≃* ((S : Subgroup X).map (barMk X)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨S.mapSurjective hsurj, ⟨phiS.symm.trans e⟩, barMk X x, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem (barMk X) hxS
  · intro h1
    have hk : x ∈ (barMk X).ker := MonoidHom.mem_ker.mpr h1
    have hbot : x ∈ (S : Subgroup X) ⊓ (barMk X).ker := Subgroup.mem_inf.mpr ⟨hxS, hk⟩
    rw [qs_inf_ker (Q := (S : Subgroup X)) S.isPGroup' le_rfl, Subgroup.mem_bot] at hbot
    exact hx1 hbot
  · rw [← map_pow, hx3, map_one]
  · have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hS : ¬ 3 ∣ Nat.card ↥(centralizer ({x} : Set X) ⊓ (barMk X).ker) := by
      intro h
      have h1 : Nat.card ↥(centralizer ({x} : Set X) ⊓ (barMk X).ker) ∣
          Nat.card ↥((barMk X).ker) :=
        Subgroup.card_dvd_of_le inf_le_right
      have h2 : Nat.card ↥((barMk X).ker) = Nat.card (primeComplementCore (G := X) 3) := by
        rw [qs_ker]
      rw [h2] at h1
      exact hO (h.trans h1)
    have hc : centralizer ({barMk X x} : Set (Bar X)) =
        (centralizer ({x} : Set X)).map (barMk X) :=
      centralizer_map_quotient (primeComplementCore (G := X) 3) hO hxord
    rw [hc, pRank_map_eq_of_coprime_ker (barMk X) Nat.prime_three hS]
    exact hxr

theorem k3_no_index_three (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ 3) :
    ∀ N : Subgroup (Bar X), N.Normal → N.index ≠ 3 := by
  intro N hN hidx
  refine hno (N.comap (barMk X)) (hN.comap (barMk X)) ?_
  exact (Subgroup.index_comap_of_surjective (H := N) (f := barMk X)
    (QuotientGroup.mk'_surjective (primeComplementCore (G := X) 3))).trans hidx

end Transfer

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
