module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Pre

variable {G : Type} [Group G]

abbrev preM (M : Subgroup G) (T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup G :=
  (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

theorem mem_preM {M : Subgroup G} {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : G} (hx : x ∈ M) :
    x ∈ preM M T ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ ∈ T := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hm
  · exact fun h => ⟨⟨x, hx⟩, h, rfl⟩

theorem le_preM {M X : Subgroup G} {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hXM : X ≤ M)
    (hXT : barM M X ≤ T) : X ≤ preM M T := fun _ hx =>
  (mem_preM (hXM hx)).mpr (hXT (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)))

theorem mem_normalizer_preM {M : Subgroup G} {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {g : G}
    (hgM : g ∈ M) (hgT : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    g ∈ Subgroup.normalizer (preM M T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨⟨g, hgM⟩ * m * ⟨g, hgM⟩⁻¹, ?_, by simp⟩
    show QuotientGroup.mk' _ (⟨g, hgM⟩ * m * ⟨g, hgM⟩⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hgT _).mp hm
  · rintro ⟨m, hm, hmx⟩
    have hmx' : (m : G) = g * x * g⁻¹ := hmx
    have hxM : x ∈ M := by
      have : x = g⁻¹ * (m : G) * g := by rw [hmx']; group
      rw [this]
      exact M.mul_mem (M.mul_mem (M.inv_mem hgM) m.2) hgM
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    have hm' : (⟨g, hgM⟩ : M) * ⟨x, hxM⟩ * ⟨g, hgM⟩⁻¹ = m := Subtype.ext (by simp [hmx'])
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨g, hgM⟩ * ⟨x, hxM⟩ * ⟨g, hgM⟩⁻¹) ∈ T :=
      hm' ▸ hm
    rw [map_mul, map_mul, map_inv] at h2
    exact (Subgroup.mem_normalizer_iff.mp hgT _).mpr h2

end Pre

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section LayerBlock

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barM_blockClosure_le_layer {M K L : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) :
    barM M (blockClosure M K L) ≤
      CFSG.ComponentClassification.Layer.subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := by
  set Ly := CFSG.ComponentClassification.Layer.subgroup (↥M ⧸ CFSG.pCore 2 ↥M) with hLy
  refine barM_le_of_le_preimage (sup_le ?_ (iSup_le fun k => iSup_le fun hk => ?_))
  · intro q hq
    refine (mem_preM ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M) hq)).mpr ?_
    rw [(mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq]
    exact Ly.one_mem
  · have hLk := hL.map_conj (hKM hk)
    exact le_preM hLk.le (CFSG.ComponentClassification.Layer.component_le hLk.component)

theorem layer_le_normalizer_component {Y : Type*} [Group Y] [Finite Y] {C : Subgroup Y}
    (hC : IsComponentOf C ⊤) :
    CFSG.ComponentClassification.Layer.subgroup Y ≤ Subgroup.normalizer (C : Set Y) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.ComponentClassification.Layer.component_le hC)).mp
    (CFSG.ComponentClassification.Layer.normal_component hC)

end LayerBlock

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section CommN

variable {G : Type} [Group G] [Finite G]

theorem commutator_sup_glbPrimeCore_le {p : ℕ} {H A B : Subgroup G} (hAH : A ≤ H)
    (hBH : B ≤ H) (hAB : ⁅A, B⁆ ≤ GLBPrimeCore p H) :
    ⁅A ⊔ GLBPrimeCore p H, B ⊔ GLBPrimeCore p H⁆ ≤ GLBPrimeCore p H := by
  set N := GLBPrimeCore p H with hN
  have hNH : N ≤ H := glbPrimeCore_le p H
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A N
    (hAH.trans (le_normalizer_glbPrimeCore p H))] at hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B N
    (hBH.trans (le_normalizer_glbPrimeCore p H))] at hy
  obtain ⟨a, ha, n, hn, rfl⟩ := hx
  obtain ⟨b, hb, m, hm, rfl⟩ := hy
  have hab : ⁅a, b⁆ ∈ N := hAB (Subgroup.commutator_mem_commutator ha hb)
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hn1 : π ⟨n, hNH hn⟩ = 1 := (mem_glbPrimeCore_iff_mk_eq_one (p := p) ⟨n, hNH hn⟩).mp hn
  have hm1 : π ⟨m, hNH hm⟩ = 1 := (mem_glbPrimeCore_iff_mk_eq_one (p := p) ⟨m, hNH hm⟩).mp hm
  have hab1 : π ⁅(⟨a, hAH ha⟩ : H), ⟨b, hBH hb⟩⁆ = 1 :=
    (mem_glbPrimeCore_iff_mk_eq_one (p := p) ⁅(⟨a, hAH ha⟩ : H), ⟨b, hBH hb⟩⁆).mp
      (by simpa [commutatorElement_def] using hab)
  set x : H := ⁅(⟨a, hAH ha⟩ : H) * ⟨n, hNH hn⟩, ⟨b, hBH hb⟩ * ⟨m, hNH hm⟩⁆ with hx
  have hx1 : π x = 1 := by
    rw [hx, commutatorElement_def]
    rw [commutatorElement_def] at hab1
    simp only [map_mul, map_inv, hn1, hm1, mul_one] at hab1 ⊢
    exact hab1
  have key : (x : G) ∈ N := (mem_glbPrimeCore_iff_mk_eq_one (p := p) x).mpr hx1
  simpa [hx, commutatorElement_def] using key

end CommN

end CFSG.AGLEmbedding
