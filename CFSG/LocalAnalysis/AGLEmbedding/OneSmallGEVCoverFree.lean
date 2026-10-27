module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.mem_centralizer_star_of_card (hSch : KFactCatalogSchreier)
    (hK1 : KFactOneLie) (hU : KFactUnitarySylowStructure) (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {Hs : Subgroup G} (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    {Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hds : D1CompI p P M Hs R Rbars Ks) :
    d1StarElt p hCHs ∈ Subgroup.centralizer (Ks : Set _) := by
  obtain ⟨T₁, -, hs, hn, hc, -, -⟩ := hds.exists_sylow
  have hout := hSch Ks hs hn hc
  have hxc : ∀ r ∈ (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)),
      d1StarElt p hCHs * r = r * d1StarElt p hCHs := by
    intro t htR
    rw [hds.cfg.rbar] at htR
    obtain ⟨r, hrR, rfl⟩ := htR
    have hrz : (r : G) * z = z * r :=
      Subgroup.mem_centralizer_singleton_iff.mp (hd.le_centralizer_czElt hz hrR)
    have hr : (⟨z, mem_of_centralizer_le hCHs⟩ : Hs) * r = r * ⟨z, mem_of_centralizer_le hCHs⟩ :=
      Subtype.ext hrz.symm
    rw [d1StarElt, ← map_mul, ← map_mul, hr]
  have hxp : d1StarElt p hCHs ^ p = 1 := by
    have h0 : (⟨z, mem_of_centralizer_le hCHs⟩ : Hs) ^ p = 1 :=
      Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hz.2.1,
        pow_orderOf_eq_one])
    rw [d1StarElt, ← map_pow, h0, map_one]
  have hin := D1CompI.mem_sup_centralizer_of_comm hK1 hU hds hxc hxp
  exact D1OneSmallData.mem_centralizer_of_mem_sup_star hd hz hR hCHs hds hout hin

theorem D1OneSmallData.mem_centralizer_star (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hSch : KFactCatalogSchreier) (hK1 : KFactOneLie)
    (hU : KFactUnitarySylowStructure) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hLa : D1SmallLa p M H Rbar K)
    {Hs : Subgroup G} (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    {Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hds : D1CompI p P M Hs R Rbars Ks) :
    d1StarElt p hCHs ∈ Subgroup.centralizer (Ks : Set _) :=
  hd.mem_centralizer_star_of_card hSch hK1 hU hz
    (hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa).1 hCHs hds

theorem d1SmallGEVStarFree_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hSch : KFactCatalogSchreier) (hK1 : KFactOneLie) (hU : KFactUnitarySylowStructure)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) : D1SmallGEVStarFree := by
  intro G _ _ p P M H R Rbar K hd _ z hz _ hB0 _ _ _ _ hL _ _ _ _ _ _ Hs Rbars _ hVHs hcfg hfree
  have hCHs := centralizer_le_of_normalizer_vz_le hVHs
  have hLa : D1SmallLa p M H Rbar K := d1SmallLa_of_not hL
  by_cases hallc : ∀ L : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ L :
        Subgroup (Hs ⧸ primeComplementCore (G := Hs) p))
  · exact h2 G p P M Hs R Rbars hcfg hallc
  push Not at hallc
  obtain ⟨Ks, hKs, hnc⟩ := hallc
  rcases hcfg.red.rankOne_or_center hKs hnc with
    ⟨zs, hzsR, hzsK, hzsp, hzsc, -, -, -, hZ⟩ | hcent
  · have hds : D1CompI p P M Hs R Rbars Ks := ⟨hcfg, hKs, hZ, hnc, ⟨zs, hzsR, hzsK, hzsp, hzsc⟩⟩
    exact (hfree (mem_of_centralizer_le hCHs) Ks hKs).2
      (D1OneSmallData.mem_centralizer_star hOut hExp hSch hK1 hU hd hz hB0 hLa hCHs hds)
  · exact h3 _ p P M Hs R Rbars hcfg Ks hKs
      (fun L hL => hcfg.red.eq_of_forall_mem_center hKs hL hcent) hnc hcent

end CFSG.AGLEmbedding
