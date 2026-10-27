module

import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIConfigO2
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_inf_inf {H M L : Subgroup G} (hLM : IsSubnormal L M) :
    IsSubnormal (H ⊓ L) (H ⊓ M) := by
  have h := hLM.inf H
  rwa [inf_comm L H, inf_comm M H] at h

section Members

variable {M H L I₀ : Subgroup G}

theorem le_inf_of_cZero (hLM : IsSubnormal L M) (hI₀ : I₀ ∈ cZero (H ⊓ L)) : I₀ ≤ H ⊓ M :=
  hI₀.le.trans (inf_le_inf le_rfl hLM.le)

theorem isSubnormal_inf_of_cZero (hLM : IsSubnormal L M) (hI₀ : I₀ ∈ cZero (H ⊓ L)) :
    IsSubnormal I₀ (H ⊓ M) :=
  hI₀.subnormal.trans (isSubnormal_inf_inf hLM)

theorem isSubnormal_oUpperTwo_inf_of_cZero (hLM : IsSubnormal L M) (hI₀ : I₀ ∈ cZero (H ⊓ L)) :
    IsSubnormal (CFSG.ComponentClassification.AS76b.oUpperTwo I₀) (H ⊓ M) := by
  have hle : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ I₀ :=
    CFSG.AGLEmbedding.oUpperTwo_le_self I₀
  refine IsSubnormal.step hle ?_ (isSubnormal_inf_of_cZero hLM hI₀)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => CFSG.ComponentClassification.RankTwoHypIIClassical.oUpperTwo_conj_mem hc hy,
    fun hy => by
      have h := CFSG.ComponentClassification.RankTwoHypIIClassical.oUpperTwo_conj_mem
        (Subgroup.inv_mem _ hc) hy
      simpa [mul_assoc] using h⟩

end Members

section Transfer

variable {p : ℕ} {M H I : Subgroup G}

theorem map_mk_le_d1X0 (hI : I ≤ H ⊓ M) :
    (I.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ d1X0 p M H :=
  Subgroup.map_mono fun _ hx => hI hx

theorem isSubnormal_map_mk_d1X0 (hI : IsSubnormal I (H ⊓ M)) :
    IsSubnormal ((I.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (d1X0 p M H) :=
  (hI.comap H.subtype).map (QuotientGroup.mk' (primeComplementCore (G := H) p))

variable {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem map_mk_le_centralizer_iff (hIH : I ≤ H) :
    (I.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ↔
      I ≤ d1PlusCore p H K := by
  unfold d1PlusCore
  rw [Subgroup.map_le_iff_le_comap]
  constructor
  · intro h x hx
    have hz : (⟨x, hIH hx⟩ : ↥H) ∈ I.subgroupOf H := hx
    exact ⟨⟨x, hIH hx⟩, h hz, rfl⟩
  · intro h x hx
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_subgroupOf.mp hx))
    have hwz' : w = x := H.subtype_injective hwz
    rwa [hwz'] at hw

theorem comap_centralizer_eq_subgroupOf (hIH : I ≤ H) :
    (centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))).comap
        ((QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hIH)) =
      (d1PlusCore p H K).subgroupOf I := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  unfold d1PlusCore
  rw [Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨Subgroup.inclusion hIH x, h, Subgroup.coe_inclusion hIH x⟩
  · rintro ⟨z, hz, hzx⟩
    have hxz : Subgroup.inclusion hIH x = z := Subtype.ext (by
      rw [Subgroup.coe_inclusion]
      exact hzx.symm)
    rw [Subgroup.mem_comap] at hz
    rw [MonoidHom.comp_apply, hxz]
    exact hz

end Transfer

theorem pow_three_mem_d1PlusCore {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {L I₀ : Subgroup G} (hLM : IsSubnormal L M) (hI₀ : I₀ ∈ cZero (H ⊓ L))
    (hO2 : pCoreOf 2 I₀ = pCoreOf 2 (H ⊓ L))
    (hb : IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀)) :
    ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀, x ^ 3 ∈ d1PlusCore p H K := by
  intro x hx
  have hcube : x ^ 3 ∈ pCoreOf 2 I₀ :=
    CFSG.AGLEmbedding.IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds hb x hx
  have hsub : IsSubnormal (H ⊓ L) (H ⊓ M) := isSubnormal_inf_inf hLM
  have h1 : x ^ 3 ∈ pCoreOf 2 (H ⊓ L) := hO2 ▸ hcube
  have h2 : pCoreOf 2 (H ⊓ L) ≤ pCoreOf 2 (H ⊓ M) :=
    CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hsub
  have h3 : pCoreOf 2 (H ⊓ M) ≤ d1PlusCore p H K :=
    hd.b3 (pCoreOf 2 (H ⊓ M)) (pCoreOf_isPGroup 2 (H ⊓ M))
      ((pCoreOf_le 2 (H ⊓ M)).trans inf_le_left)
      ((le_inf hd.le_H hd.base.1).trans (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M)))
  exact h3 (h2 h1)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
