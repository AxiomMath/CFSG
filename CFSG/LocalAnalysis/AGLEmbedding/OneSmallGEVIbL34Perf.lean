module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.not_nine_dvd_card_of_perfect (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {V : Subgroup G} (hV : V ≤ H ⊓ M) (hVp : ⁅V, V⁆ = V) : ¬ 9 ∣ Nat.card V := by
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE (Or.inl ⟨hp3, hL⟩)
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hsolv := hΓ3 K hs hn hc T₁ hTnc hΓT hd.small (Or.inr (Or.inr hL))
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hVH : V ≤ H := hV.trans inf_le_left
  set W := (V.subgroupOf H).map π with hW
  have hWp : ⁅W, W⁆ = W := by
    have h1 : ⁅V.subgroupOf H, V.subgroupOf H⁆ = V.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVH, hVp]
    rw [hW, ← Subgroup.map_commutator, h1]
  have hWX : W ≤ d1X0 3 M H := Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
    (hV (Subgroup.mem_subgroupOf.mp hu))
  have hWC := hd.le_centralizer_of_perfect_of_eq hY (hSch K hs hn hc) hsolv hWX hWp
  have hbound : ∀ Q : Subgroup G, Q ≤ V → IsPGroup 3 Q → Nat.card Q ≤ 3 := by
    intro Q hQV hQp
    have hQH : Q ≤ H := hQV.trans hVH
    have hQ'p : IsPGroup 3 (Q.subgroupOf H) := hQp.comap_subtype
    have hle : (Q.subgroupOf H).map π ≤
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) :=
      (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (hQV (Subgroup.mem_subgroupOf.mp hx))).trans hWC
    have h1 := hd.card_le_of_le_centralizer hR hle (hQ'p.map π)
    rw [card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime (G := H) 3)
      hQ'p] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv] at h1
  intro h9
  exact not_sq_dvd_of_card_le (p := 3) hbound (by norm_num; exact h9)

end CFSG.AGLEmbedding
