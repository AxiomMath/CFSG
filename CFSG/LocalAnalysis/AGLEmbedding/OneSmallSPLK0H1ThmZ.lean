module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nclIn_nclIn_of_simple {p : ℕ} [Fact p.Prime] {H₁ X : Subgroup G}
    (hXH : X ≤ H₁) (hXp : IsPGroup p X) (hX1 : X ≠ ⊥)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} [IsSimpleGroup L] (hLn : L.Normal)
    (hXL : (X.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L) :
    nclIn (nclIn H₁ X) X = nclIn H₁ X := by
  have hp : p.Prime := Fact.out
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set J := nclIn H₁ X with hJdef
  have hXJ : X ≤ J := le_nclIn hXH
  have hJH : J ≤ H₁ := nclIn_le_self H₁ X
  have hLJ : nclIn J X ≤ J := nclIn_le_self J X
  have hXt1 : (X.subgroupOf H₁).map π₁ ≠ ⊥ := map_mk_ne_bot_of_isPGroup hp hXH hXp hX1
  set Lh : Subgroup G := (L.comap π₁).map H₁.subtype with hLh
  have hLhH : Lh ≤ H₁ := Subgroup.map_subtype_le _
  have hLhsub : Lh.subgroupOf H₁ = L.comap π₁ :=
    Subgroup.comap_map_eq_self_of_injective H₁.subtype_injective _
  have hHLh : H₁ ≤ Subgroup.normalizer (Lh : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hLhH).mp ?_
    rw [hLhsub]
    exact hLn.comap _
  have hXLh : X ≤ Lh := fun x hx =>
    ⟨⟨x, hXH hx⟩, hXL (Subgroup.mem_map_of_mem π₁
      (show (⟨x, hXH hx⟩ : H₁) ∈ X.subgroupOf H₁ from hx)), rfl⟩
  have hJL : (J.subgroupOf H₁).map π₁ ≤ L := by
    rw [Subgroup.map_le_iff_le_comap, ← hLhsub]
    exact Subgroup.comap_mono (nclIn_le hXLh hLhH hHLh)
  have hJn : ((J.subgroupOf H₁).map π₁).Normal :=
    (nclIn_normal H₁ X).map _ (QuotientGroup.mk'_surjective _)
  have hJK : (J.subgroupOf H₁).map π₁ = L := by
    refine eq_of_le_normalizer_of_isSimpleGroup hJL ?_
      (ne_bot_of_le_ne_bot hXt1 (Subgroup.map_mono (Subgroup.comap_mono hXJ)))
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hLK : ((nclIn J X).subgroupOf H₁).map π₁ = L :=
    eq_of_le_normalizer_of_isSimpleGroup
      ((Subgroup.map_mono (Subgroup.comap_mono hLJ)).trans hJK.le)
      (hJK.ge.trans (map_le_normalizer_map _ (hLJ.trans hJH) (le_normalizer_nclIn J X)))
      (ne_bot_of_le_ne_bot hXt1 (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hXJ))))
  have hJLN : J ≤ nclIn J X ⊔ (J ⊓ GLBPrimeCore p H₁) := by
    intro j hj
    have hjK : π₁ ⟨j, hJH hj⟩ ∈ ((nclIn J X).subgroupOf H₁).map π₁ := by
      rw [hLK, ← hJK]
      exact Subgroup.mem_map_of_mem _ (show (⟨j, hJH hj⟩ : H₁) ∈ J.subgroupOf H₁ from hj)
    obtain ⟨l, hl, hlj⟩ := hjK
    have hn : (l : G)⁻¹ * j ∈ GLBPrimeCore p H₁ :=
      (mk'_primeComplementCore_eq_one_iff p (l⁻¹ * ⟨j, hJH hj⟩)).mp
        (by rw [map_mul, map_inv, hlj, inv_mul_cancel])
    have e : j = l * ((l : G)⁻¹ * j) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hl ⟨J.mul_mem (J.inv_mem (hLJ hl)) hj, hn⟩
  have hcop : (Nat.card (J ⊓ GLBPrimeCore p H₁ : Subgroup G)).Coprime p :=
    ((glbPrimeCore_coprime p H₁).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)).symm
  have hconj : ∀ c ∈ H₁, ∀ x ∈ X, c * x * c⁻¹ ∈ nclIn J X := by
    intro c hc x hx
    have hXc : X.map (MulAut.conj c).toMonoidHom ≤ J := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H₁ X hc) y).mp (hXJ hy)
    exact le_of_le_sup_of_coprime_card_of_le hXc hLJ inf_le_left (nclIn_normal J X)
      (hXp.map _) hcop (hXc.trans hJLN) ⟨x, hx, rfl⟩
  exact le_antisymm hLJ (nclIn_le_of_forall_conj_mem hconj)

end CFSG.AGLEmbedding
