module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

theorem gen49q_isElemAbelian_map {p : ℕ} {A B : Type*} [Group A] [Group B] (f : A →* B)
    {E : Subgroup A} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

section Quot

variable {G : Type} [Group G] [Finite G] {p : ℕ} {N : Subgroup G}

theorem gen49q_normalizer_map_mk_le {M : Subgroup G} {D : Subgroup N} (hp : p.Prime)
    (hOM : primeComplementCore (G := N) p ≤ (N ⊓ M).subgroupOf N) (hD : IsPGroup p D)
    (hnorm : normalizer ((D.map N.subtype : Subgroup G) : Set G) ≤ M) :
    normalizer ((D.map (QuotientGroup.mk' (primeComplementCore (G := N) p)) :
        Subgroup (N ⧸ primeComplementCore (G := N) p)) :
          Set (N ⧸ primeComplementCore (G := N) p)) ≤
      ((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) := by
  have hNH : normalizer (D : Set N) ≤ (N ⊓ M).subgroupOf N := fun n hn =>
    Subgroup.mem_subgroupOf.mpr
      ⟨n.property, hnorm (Subgroup.le_normalizer_map N.subtype ⟨n, hn, rfl⟩)⟩
  exact le_map_of_comap_le (QuotientGroup.mk'_surjective _)
    ((comap_normalizer_map_le_sup hp _ (primeComplementCore_coprime p) hD).trans
      (sup_le hOM hNH))

theorem gen49q_pRank_top_quotient_le (hp : p.Prime) {k : ℕ} (h : CFSG.Open.pRank p N ≤ k) :
    CFSG.Open.pRank p (⊤ : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤ k := by
  have h1 := pRank_map_mk_eq_pRank_map_subtype hp (primeComplementCore (G := N) p)
    (primeComplementCore_coprime p) ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact h

theorem gen49q_core_le_subgroupOf_inf {M : Subgroup G} (h : rankThreePrimeCore p N ≤ M) :
    primeComplementCore (G := N) p ≤ (N ⊓ M).subgroupOf N := fun o ho =>
  Subgroup.mem_subgroupOf.mpr ⟨o.property, h (by
    rw [rankThreePrimeCore_eq_map_primeComplementCore]
    exact ⟨o, ho, rfl⟩)⟩

theorem gen49q_extract {H M : Subgroup G} {x : G} (hxH : x ∈ H)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal)
    (hKC : K ≤ centralizer ({QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩} :
      Set (H ⧸ primeComplementCore (G := H) p)))
    (hKΓ : ¬ K ≤ ((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    ∃ X : Subgroup G, X ≤ H ∧ rankThreePrimeCore p H ≤ X ∧ (X.subgroupOf H).Normal ∧
      (∀ h ∈ X, h * x * h⁻¹ * x⁻¹ ∈ rankThreePrimeCore p H) ∧ ¬ X ≤ M := by
  set O := primeComplementCore (G := H) p
  refine ⟨(K.comap (QuotientGroup.mk' O)).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_,
    ?_⟩
  · rw [rankThreePrimeCore_eq_map_primeComplementCore]
    refine Subgroup.map_mono fun o ho => ?_
    have h1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [Subgroup.mem_comap, h1]
    exact K.one_mem
  · have h : ((K.comap (QuotientGroup.mk' O)).map H.subtype).subgroupOf H =
        K.comap (QuotientGroup.mk' O) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [h]
    exact hKn.comap _
  · rintro _ ⟨h, hh, rfl⟩
    have hc := mem_centralizer_singleton_iff.mp (hKC hh)
    refine mem_rankThreePrimeCore_of_mk_eq_one (H.mul_mem (H.mul_mem (H.mul_mem h.2 hxH)
      (H.inv_mem h.2)) (H.inv_mem hxH)) ?_
    change QuotientGroup.mk' O (h * ⟨x, hxH⟩ * h⁻¹ * ⟨x, hxH⟩⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
  · intro hXM
    apply hKΓ
    intro k hk
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O k
    exact ⟨h, Subgroup.mem_subgroupOf.mpr ⟨h.2, hXM ⟨h, hk, rfl⟩⟩, rfl⟩

end Quot

end CFSG.LocalAnalysis.RankThreeTheoremC
