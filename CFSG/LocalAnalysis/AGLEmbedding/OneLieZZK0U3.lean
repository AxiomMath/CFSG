module

import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Commutator
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Shape
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroComp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}
  {Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p)}
  {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} {T₁ : Sylow p L}

theorem isCyclic_of_le_plusCore (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁)
    {A : Subgroup G} (hAN : A ≤ d1PlusCore p H₁ L) (hA : IsPGroup p A) : IsCyclic A := by
  have hp : p.Prime := h.red.prime
  have : L.Normal := h.normal
  have hAH : A ≤ H₁ := hAN.trans (Subgroup.map_subtype_le _)
  have hAp : IsPGroup p (A.subgroupOf H₁) := hA.comap_subtype
  have hAC : (A.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤
      Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hAN (Subgroup.mem_subgroupOf.mp ha)
    rw [← Subtype.ext hxa]
    exact hx
  have hcyc := h.red.isCyclic_of_le_centralizer h.comp h.not_le (hAp.map _) hAC
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp
    (primeComplementCore (G := H₁) p)
    (hp.coprime_iff_not_dvd.mp (primeComplementCore_coprime p)) _ hAp
  let e := MulEquiv.ofBijective _ ⟨hinj, (QuotientGroup.mk' _).subgroupMap_surjective _⟩
  have : IsCyclic (A.subgroupOf H₁) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom
    (MulEquiv.surjective _)

theorem commutator_le_twoCore (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁)
    (h3₁ : D1PhaseThree p P' M H₁ S) (hXY : d1LiftX p H R K ≤ pCorePreimage p M) :
    ⁅GLBPrimeCore p H₁, d1LiftX p H₁ S L⁆ ≤ pCoreOf 2 H₁ :=
  h.kzero.toCore.commutator_le_twoCore_of_simple h.normal h.simple h.le h3₁ hXY

end D1OneLieKZeroComp

end CFSG.AGLEmbedding
