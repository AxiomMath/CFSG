module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsRoot

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type*} [Group G] {a : ℕ} {K : Type} [Field K]

theorem exists_szRootCoords_of_sylow [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {L : Subgroup G} (e : L ≃* suzukiGroup a K)
    {T₁ : Subgroup G} (hT₁L : T₁ ≤ L) (hT₁ : ∃ P : Sylow 2 L, (P : Subgroup L) = T₁.subgroupOf L)
    {d : G} (hdL : d ∈ L) (hdN : d ∈ normalizer (T₁ : Set G)) :
    ∃ (u v : G → K) (κ : K), SzRootCoords T₁ a d u v κ := by
  obtain ⟨e', he'⟩ := exists_mulEquiv_szModelU_eq hK e hT₁L hT₁
  subst he'
  obtain ⟨u₀, v₀, l, hd⟩ := exists_eq_suzukiSElt_mul_suzukiDElt ha hK e' hdL hdN
  obtain ⟨u, v, hc⟩ := exists_szRootCoords hK e' u₀ v₀ l
  have hd' : ((e'.symm (suzukiSElt a K u₀ v₀ * suzukiDElt a K l) : L) : G) = d := by
    rw [← hd, MulEquiv.symm_apply_apply]
  rw [hd'] at hc
  exact ⟨u, v, l, hc⟩

end CFSG.SeitzReduction.RankOne
