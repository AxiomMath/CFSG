module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section SocleTransfer

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem centralizer_le_of_map {X : Subgroup G}
    (hC : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer ((X.subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    ∀ d ∈ H ⊓ M, (∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
      d ∈ R ⊔ GLBPrimeCore p H := by
  intro d hd hdX
  have hdH : d ∈ H := hd.1
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hmem : π ⟨d, hdH⟩ ∈ ((H ⊓ M).subgroupOf H).map π ⊓
      Subgroup.centralizer ((X.subgroupOf H).map π : Set (H ⧸ primeComplementCore (G := H) p)) := by
    refine ⟨Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hd),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hc := hdX x (Subgroup.mem_subgroupOf.mp hx)
    have h1 : π (⟨d, hdH⟩ * x * (⟨d, hdH⟩)⁻¹ * x⁻¹) = 1 :=
      (mk'_primeComplementCore_eq_one_iff p _).mpr (by simpa using hc)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π x * π ⟨d, hdH⟩ =
        (π ⟨d, hdH⟩ * π x * (π ⟨d, hdH⟩)⁻¹ * (π x)⁻¹)⁻¹ * (π ⟨d, hdH⟩ * π x) := by group
      _ = π ⟨d, hdH⟩ * π x := by rw [h1, inv_one, one_mul]
  obtain ⟨r, hr, hrd⟩ := hC hmem
  have hn : ((r⁻¹ * ⟨d, hdH⟩ : H) : G) ∈ GLBPrimeCore p H := by
    rw [← mk'_primeComplementCore_eq_one_iff, map_mul, map_inv, hrd, inv_mul_cancel]
  have e : d = (r : G) * ((r⁻¹ * ⟨d, hdH⟩ : H) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hr) hn

theorem D1Extremal.toPhaseThree_of_forall (h : D1Extremal p P M H R)
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G)
    (hO : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      (W.subgroupOf
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))).Normal →
      p.Coprime (Nat.card W) → W = ⊥) :
    D1PhaseThree p P M H R :=
  h.toPhaseThreeU hglob (h.toD1Escape.primeCore_inf_eq_iff.mpr
    (primeComplementCore_eq_bot_of_forall hO))

theorem D1Extremal.survivorData_of_map (h : D1Extremal p P M H R)
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G)
    {X : Subgroup G} (hXR : X ≤ R) (hX1 : X ≠ ⊥)
    (hO : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      (W.subgroupOf
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))).Normal →
      p.Coprime (Nat.card W) → W = ⊥)
    (hD1 : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) →
      W = ⊥ ∨ (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ W)
    (hC : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer ((X.subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    D1SurvivorData p P M H R X :=
  have : Fact p.Prime := ⟨h.prime⟩
  ⟨h.toPhaseThree_of_forall hglob hO, hXR, hX1,
    fun _ hY hYN => le_glbPrimeCore_or_le_of_forall h.primeCore_le (hXR.trans h.le_H)
      (h.isPGroup.to_le hXR) hD1 hY hYN, centralizer_le_of_map hC⟩

theorem primeComplementCore_eq_bot_of_dichotomy {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {Y₀ Z : Subgroup Y}
    (hD : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → W = ⊥ ∨ Z ≤ W)
    (hZp : IsPGroup p Z) (hZ : Z ≠ ⊥) : primeComplementCore (G := Y₀) p = ⊥ := by
  have hp : p.Prime := Fact.out
  set W := (primeComplementCore (G := Y₀) p).map Y₀.subtype with hWdef
  have hWsub : W.subgroupOf Y₀ = primeComplementCore (G := Y₀) p :=
    Subgroup.comap_map_eq_self_of_injective Y₀.subtype_injective _
  have hWn : Y₀ ≤ Subgroup.normalizer (W : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (by rw [hWsub]; infer_instance)
  have hWc : p.Coprime (Nat.card W) := by
    rw [Subgroup.card_map_of_injective Y₀.subtype_injective]
    exact primeComplementCore_coprime p
  rcases hD W (Subgroup.map_subtype_le _) hWn with hW | hZW
  · exact (Subgroup.map_eq_bot_iff_of_injective _ Y₀.subtype_injective).mp hW
  · exfalso
    apply hZ
    rw [← inf_eq_left.mpr hZW]
    exact inf_eq_bot_of_isPGroup hp hZp hWc

theorem map_inf_centralizer_eq {p : ℕ} [Fact p.Prime] {H U : Subgroup G} (hUH : U ≤ H)
    (hU : IsPGroup p U) :
    ((U ⊓ Subgroup.centralizer (U : Set G)).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (((U.subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _) := by
  have hp : p.Prime := Fact.out
  have hUN : U ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hU (glbPrimeCore_coprime p H)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    refine ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx'.1), ?_⟩
    show _ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hc : (u : G) * x = x * u :=
      Subgroup.mem_centralizer_iff.mp hx'.2 u (Subgroup.mem_subgroupOf.mp hu)
    rw [← map_mul, ← map_mul, show u * x = x * u from Subtype.ext hc]
  · rintro y ⟨⟨u, hu, rfl⟩, hyC⟩
    refine ⟨u, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hu, ?_⟩, rfl⟩
    show _ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvH : v ∈ H := hUH hv
    have h1 := Subgroup.mem_centralizer_iff.mp hyC
      (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨v, hvH⟩)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv))
    have h2 : (((⟨v, hvH⟩ : H) * u * (⟨v, hvH⟩ : H)⁻¹ * u⁻¹ : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 : (((⟨v, hvH⟩ : H) * u * (⟨v, hvH⟩ : H)⁻¹ * u⁻¹ : H) : G) ∈ U := by
      have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
      simpa using U.mul_mem (U.mul_mem (U.mul_mem hv huU) (U.inv_mem hv)) (U.inv_mem huU)
    have h4 : (((⟨v, hvH⟩ : H) * u * (⟨v, hvH⟩ : H)⁻¹ * u⁻¹ : H) : G) = 1 := by
      have hmem : (((⟨v, hvH⟩ : H) * u * (⟨v, hvH⟩ : H)⁻¹ * u⁻¹ : H) : G) ∈
          U ⊓ GLBPrimeCore p H := ⟨h3, h2⟩
      rwa [hUN, Subgroup.mem_bot] at hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    have h5 := mul_inv_eq_one.mp h4
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5

end SocleTransfer

end CFSG.AGLEmbedding
