module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPBOneL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPOdd
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPBOne

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_outer_rbar (hGen : KFactL34OuterGen)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    {f : H ⧸ primeComplementCore (G := H) p}
    (hfR : f ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hfK : f ∉ K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    (hf3 : f ^ 3 = 1) : False := by
  subst hp3
  obtain ⟨z₀, hz₀R, -, hz₀p, hz₀c⟩ := hd.z
  set Yb := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) with hYb
  have hNR : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤
      Subgroup.normalizer (Yb : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    intro r hr
    have hrN := hd.cfg.red.sylow_le_normalizer_component hd.comp hr
    refine Subgroup.mem_normalizer_fintype fun y hy => ⟨?_, ?_⟩
    · exact Rbar.1.mul_mem (Rbar.1.mul_mem hr hy.1) (Rbar.1.inv_mem hr)
    · exact (Subgroup.normal_subgroupOf_centralizer_normalizer _).conj_mem
        ⟨y, Subgroup.centralizer_le_normalizer _ hy.2⟩ hy.2 ⟨r, hrN⟩
  have hYne : Yb ≠ ⊥ := by
    intro h0
    have hmem : z₀ ∈ Yb := ⟨hz₀R, hz₀c⟩
    rw [h0, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hz₀p
    norm_num at hz₀p
  obtain ⟨z', ⟨hz'R, hz'C⟩, hz'cen, hz'p⟩ :=
    exists_central_order_three_of_le_normalizer Rbar.isPGroup' inf_le_left hNR hYne
  have hz'K : z' ∉ K := by
    intro hz'K
    have hmem : (⟨z', hz'K⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hz'C k k.2)
    rw [hd.center, Subgroup.mem_bot] at hmem
    have h1 : z' = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hz'p
    norm_num at hz'p
  exact hd.cfg.red.false_of_outer_three hGen hd.comp hL hd.noncyclic hz'R hz'K hz'p hz'C hfR
    hf3 (hz'cen f hfR) hfK

theorem D1OneSmallData.false_of_b0_outer (hGen : KFactL34OuterGen) (hAE : KFactL34AutExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : D1SmallOuterR p H Rbar K) : False := by
  obtain ⟨rb, hrb, hrbK⟩ : ∃ rb ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      rb ∉ K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    by_contra h
    push Not at h
    exact hOR h
  by_cases hf : ∃ f ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      f ∉ K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ∧ f ^ 3 = 1
  · obtain ⟨f, hfR, hfK, hf3⟩ := hf
    exact hd.false_of_outer_rbar hGen hp3 hL hfR hfK hf3
  · push Not at hf
    have hrb3 := hf rb hrb hrbK
    rw [hd.cfg.rbar] at hrb
    obtain ⟨rH, hrH, rfl⟩ := hrb
    refine hd.false_of_b0_cube hAE hz hB0 hp3 hL (r := (rH : G)) hrH ?_
    intro h1
    apply hrb3
    have : rH ^ 3 = 1 := Subtype.ext (by simpa using h1)
    rw [← map_pow, this, map_one]

end Config

@[expose] def D1SmallL34Left : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 3 → IsLinThreeFour K → ¬ D1CzSP p z →
    (((D1SmallOuterR p H Rbar K ∧ ¬ D1CzB0 p R z ∧
        ∀ f ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)),
          f ∉ K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) →
            f ^ 3 ≠ 1) ∨ D1SmallU2Fails p M H K) ∧ ¬ D1CzIso p z K) ∨
    (¬ D1SmallOuterR p H Rbar K ∧ (D1SmallU2Fails p M H K ∨ D1SmallOpenPos p M H Rbar K) ∧
      D1CzIso p z K ∧ D1CzB0 p R z ∧ D1CzEven p z) → False

theorem d1SmallL34_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hβ : KFactBeta) (hK10 : KFactSmallInvolve) (hSch : KFactCatalogSchreier)
    (hα : KFactAlphaW) (hK3 : KFactAlphaThreeWeak) (hJ3 : KFactJ3Involve)
    (hO : KFactSmallThreeOrders) (hGen : KFactL34OuterGen) (hAE : KFactL34AutExp)
    (hLeft : D1SmallL34Left) : D1SmallL34 := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hp3 hL h
  by_cases hSP : D1CzSP p z
  · exact hd.false_of_sp_l34 hβ hK10 hSch hα hK3 hJ3 hO hz hp3 hL hSP
  have hR := hLeft G p P M H R Rbar K hd huniq z hz hp3 hL hSP
  by_cases hIso : D1CzIso p z K
  swap
  · rcases h with hb | hc | ⟨-, -, hIso', -⟩
    · by_cases hB0 : D1CzB0 p R z
      · exact hd.false_of_b0_outer hGen hAE hz hB0 hp3 hL hb
      by_cases hf : ∃ f ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)),
          f ∉ K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ∧
            f ^ 3 = 1
      · obtain ⟨f, hfR, hfK, hf3⟩ := hf
        exact hd.false_of_outer_rbar hGen hp3 hL hfR hfK hf3
      · push Not at hf
        exact hR (Or.inl ⟨Or.inl ⟨hb, hB0, hf⟩, hIso⟩)
    · exact hR (Or.inl ⟨Or.inr hc, hIso⟩)
    · exact hIso hIso'
  by_cases hB0 : D1CzB0 p R z
  swap
  · exact hd.false_of_b1_l34 hOut hExp hGen hAE hz hSP hB0 hIso hp3 hL
  by_cases hOR : D1SmallOuterR p H Rbar K
  · exact hd.false_of_b0_outer hGen hAE hz hB0 hp3 hL hOR
  by_cases hE : D1CzEven p z
  · have hpos : D1SmallU2Fails p M H K ∨ D1SmallOpenPos p M H Rbar K := by
      rcases h with hb | hc | ⟨hOP, -⟩
      · exact absurd hb hOR
      · exact Or.inl hc
      · exact Or.inr hOP
    exact hR (Or.inr ⟨hOR, hpos, hIso, hB0, hE⟩)
  · exact hd.false_of_b0_odd hOut hExp hNo2 hShape hOrb hz hB0 hE hIso (fun h => by omega)
      (fun _ _ => hOR)

end CFSG.AGLEmbedding
