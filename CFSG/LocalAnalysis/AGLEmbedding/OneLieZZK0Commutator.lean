module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Sylow
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}
  {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}

theorem D1KZeroCore.commutator_le_twoCore_of_simple
    (hc : D1KZeroCore p P M H R Rbar K P' H₁ S)
    (hLn : L.Normal) (hLs : IsSimpleGroup L)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L)
    (h3₁ : D1PhaseThree p P' M H₁ S) (hXY : d1LiftX p H R K ≤ pCorePreimage p M) :
    ⁅GLBPrimeCore p H₁, d1LiftX p H₁ S L⁆ ≤ pCoreOf 2 H₁ := by
  have hd := hc.data
  have hp : p.Prime := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set X := d1LiftX p H R K with hXdef
  have hXH₁ : X ≤ H₁ := hc.liftX_le_H₁
  have hXp : IsPGroup p X := hd.esc.isPGroup.to_le (d1LiftX_le p H R K)
  have hNX : ⁅GLBPrimeCore p H₁, X⁆ ≤ pCoreOf 2 H₁ := by
    rw [Subgroup.commutator_le]
    intro n hn y hy
    rw [commutatorElement_def]
    have hnM : n ∈ M := hc.escape.primeCore_le hn
    have h1 : n * y * n⁻¹ * y⁻¹ ∈ pCorePreimage p M :=
      (pCorePreimage p M).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCorePreimage p M hnM) y).mp (hXY hy)) ((pCorePreimage p M).inv_mem (hXY hy))
    have h2 : n * y * n⁻¹ * y⁻¹ ∈ GLBPrimeCore p H₁ := by
      have h3 : y * n⁻¹ * y⁻¹ ∈ GLBPrimeCore p H₁ :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_glbPrimeCore p H₁ (hXH₁ hy)) _).mp
          ((GLBPrimeCore p H₁).inv_mem hn)
      have e : n * y * n⁻¹ * y⁻¹ = n * (y * n⁻¹ * y⁻¹) := by group
      rw [e]
      exact (GLBPrimeCore p H₁).mul_mem hn h3
    exact h3₁.twoCore_M_le h3₁.twoCore_inf (h3₁.pCorePreimage_inf_le ⟨h1, h2⟩)
  have hNJ := CFSG.AGLEmbedding.commutator_nclIn_le hXH₁ (le_normalizer_glbPrimeCore p H₁)
    (localGroup_le_normalizer_pCoreOf 2 H₁) hNX
  set Lh : Subgroup G := (L.comap π₁).map H₁.subtype with hLh
  have hLhH₁ : Lh ≤ H₁ := Subgroup.map_subtype_le _
  have hLhsub : Lh.subgroupOf H₁ = L.comap π₁ :=
    Subgroup.comap_map_eq_self_of_injective H₁.subtype_injective _
  have hH₁Lh : H₁ ≤ Subgroup.normalizer (Lh : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLhH₁).mp
      (by rw [hLhsub]; exact hLn.comap _)
  have hXLh : X ≤ Lh := fun x hx => ⟨⟨x, hXH₁ hx⟩, Subgroup.mem_comap.mpr
    (hJL (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (le_nclIn (d1LiftX_le_H p H R K) hx)))), rfl⟩
  have hJ₁Lh : nclIn H₁ X ≤ Lh := CFSG.AGLEmbedding.nclIn_le hXLh hLhH₁ hH₁Lh
  have hJ₁L : ((nclIn H₁ X).subgroupOf H₁).map π₁ ≤ L := by
    rintro _ ⟨j, hj, rfl⟩
    have := hJ₁Lh (Subgroup.mem_subgroupOf.mp hj)
    rw [← Subgroup.mem_subgroupOf, hLhsub] at this
    exact this
  have hXt1 : (X.subgroupOf H₁).map π₁ ≠ ⊥ :=
    map_mk_ne_bot_of_isPGroup hp hXH₁ hXp hd.d1LiftX_ne_bot
  have hJ₁n : (((nclIn H₁ X).subgroupOf H₁).map π₁).Normal :=
    (nclIn_normal H₁ X).map _ (QuotientGroup.mk'_surjective _)
  have hJ₁eq : ((nclIn H₁ X).subgroupOf H₁).map π₁ = L :=
    eq_of_le_normalizer_of_isSimpleGroup hJ₁L
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hJ₁n]; exact le_top)
      (ne_bot_of_le_ne_bot hXt1 (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hXH₁))))
  have hsup : d1LiftX p H₁ S L ≤ nclIn H₁ X ⊔ GLBPrimeCore p H₁ := by
    rintro _ ⟨a, ⟨-, haL⟩, rfl⟩
    obtain ⟨b, hb, hba⟩ : π₁ a ∈ ((nclIn H₁ X).subgroupOf H₁).map π₁ := by
      rw [hJ₁eq]
      exact Subgroup.mem_comap.mp haL
    have hn : (b : G)⁻¹ * a ∈ GLBPrimeCore p H₁ :=
      (mk'_primeComplementCore_eq_one_iff p (b⁻¹ * a)).mp
        (by rw [map_mul, map_inv, hba, inv_mul_cancel])
    have e : (a : G) = b * ((b : G)⁻¹ * a) := by group
    rw [Subgroup.coe_subtype, e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hb) hn
  have hS₀J : d1LiftX p H₁ S L ≤ nclIn H₁ X :=
    le_of_le_sup_of_coprime_card_of_le (d1LiftX_le_H p H₁ S L) (nclIn_le_self H₁ X)
      (glbPrimeCore_le p H₁) (nclIn_normal H₁ X)
      (hc.escape.isPGroup.to_le (d1LiftX_le p H₁ S L)) (glbPrimeCore_coprime p H₁).symm hsup
  exact (Subgroup.commutator_mono le_rfl hS₀J).trans hNJ

end CFSG.AGLEmbedding
