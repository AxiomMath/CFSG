module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveFour
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)} [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem exists_mem_inf_of_mem (hI1 : KFactStepThreeCentNilp) (hI2 : KFactStepThreeIrred)
    (hI4 : KFactStepThreeMaximal) {P : Sylow p G}
    {M : Subgroup G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hp2 : p ≠ 2)
    (hZ : Subgroup.center ↥K = ⊥) (hK1 : 1 ≤ Open.pRank p (⊤ : Subgroup ↥K))
    (hSt : StepThreeGroup p ↥K) (hA : IsEmpty (↥K ≃* alternatingGroup (Fin 10)))
    (hKX : ¬ K ≤ d1X0 p M C)
    (hXM : d1PlusCore p C K ≤ M) (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1)
    {B E : Subgroup G} {b : G} (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) (hBM : B ≤ M)
    (hbB : b ∈ B) (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hEB : E ≤ B)
    {L : Subgroup G} (hLM : L ≤ M) (hML : M ≤ Subgroup.normalizer (L : Set G))
    (hCL : ¬ CFSG.HasNormalPComplement p ↥(C ⊓ L)) :
    ∀ u ∈ B ⊓ hyp111Pre p C K, ∃ w ∈ C ⊓ L, w⁻¹ * u ∈ d1PlusCore p C K := by
  set S : Subgroup (MulAut ↥K) := ((B ⊓ hyp111Pre p C K).subgroupOf C).map φ with hS
  set Nn : Subgroup (MulAut ↥K) := ((C ⊓ M).subgroupOf C).map φ with hNn
  set Ll : Subgroup (MulAut ↥K) := ((C ⊓ L).subgroupOf C).map φ with hLl
  have hmem := mem_iff_act_mem_normalizer hI4 hcore hp2 hZ hK1 hSt hA hKX hXM hXr hBC hBM hbB
    hb hbo hE hEc hEB
  have hnp : ¬ CFSG.HasNormalPComplement p ↥Ll := fun h =>
    hCL (hasNormalPComplement_of_act hp2 hXr (hBC.le hbB) hb hbo inf_le_left h)
  have hNS : Nn ≤ Subgroup.normalizer (S : Set (MulAut ↥K)) := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hmem c).mp (Subgroup.mem_subgroupOf.mp hc).2
  have hIN : (MulAut.conj : ↥K →* MulAut ↥K).range ⊓ Subgroup.normalizer (S : Set (MulAut ↥K)) ≤
      Nn := by
    rintro σ ⟨hσI, hσN⟩
    rw [← map_comap_act_eq] at hσI
    obtain ⟨c, -, rfl⟩ := hσI
    exact ⟨c, Subgroup.mem_subgroupOf.mpr ⟨c.2, (hmem c).mpr hσN⟩, rfl⟩
  have hLN : Ll ≤ Nn := Subgroup.map_mono fun c hc =>
    Subgroup.mem_subgroupOf.mpr ⟨c.2, hLM (Subgroup.mem_subgroupOf.mp hc).2⟩
  have hNL : Nn ≤ Subgroup.normalizer (Ll : Set (MulAut ↥K)) := by
    rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.le_normalizer_map φ ⟨c, ?_, rfl⟩
    have hcL := hML (Subgroup.mem_subgroupOf.mp hc).2
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul,
      Subgroup.coe_inv, SetLike.coe_mem, true_and]
    have hC : (c : G) * h * (c : G)⁻¹ ∈ C := (c * h * c⁻¹).2
    rw [Subgroup.mem_normalizer_iff.mp hcL h]
    exact ⟨fun h1 => ⟨hC, h1⟩, fun h1 => h1.2⟩
  have hle := le_of_not_hasNormalPComplement hI1 hI2 conj_range_normal
    (centralizer_conj_range_eq_bot hZ) (stepThreeGroup_conj_range hZ hSt) (isSylowOf_act hZ hBC)
    hNS hIN hLN hNL hnp
  intro u hu
  have huC : u ∈ C := hBC.le hu.1
  have hu' : (⟨u, huC⟩ : C) ∈ (B ⊓ hyp111Pre p C K).subgroupOf C := Subgroup.mem_subgroupOf.mpr hu
  obtain ⟨w, hw, he⟩ := hle ⟨_, hu', rfl⟩
  refine ⟨w, Subgroup.mem_subgroupOf.mp hw, ?_⟩
  have hk : w⁻¹ * ⟨u, huC⟩ ∈ MonoidHom.ker φ := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  exact (mem_d1PlusCore_iff_mem_ker _).mpr hk

theorem inf_hyp111Pre_le_of (hI1 : KFactStepThreeCentNilp) (hI2 : KFactStepThreeIrred)
    (hI4 : KFactStepThreeMaximal) {P : Sylow p G}
    {M : Subgroup G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hp2 : p ≠ 2)
    (hZ : Subgroup.center ↥K = ⊥) (hK1 : 1 ≤ Open.pRank p (⊤ : Subgroup ↥K))
    (hSt : StepThreeGroup p ↥K) (hA : IsEmpty (↥K ≃* alternatingGroup (Fin 10)))
    (hKX : ¬ K ≤ d1X0 p M C) (hKnp : ¬ CFSG.HasNormalPComplement p ↥K)
    (hXM : d1PlusCore p C K ≤ M) (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1)
    {B E : Subgroup G} {b : G} (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) (hBM : B ≤ M)
    (hbB : b ∈ B) (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hEB : E ≤ B)
    {L : Subgroup G} (hLM : L ≤ M) (hML : M ≤ Subgroup.normalizer (L : Set G))
    (hCL : ¬ CFSG.HasNormalPComplement p ↥(C ⊓ L)) :
    B ⊓ hyp111Pre p C K ≤ L := by
  have hmem := mem_iff_act_mem_normalizer hI4 hcore hp2 hZ hK1 hSt hA hKX hXM hXr hBC hBM hbB
    hb hbo hE hEc hEB
  refine inf_hyp111Pre_le hI2 hSt hZ hKnp hBC hML hXM (fun k hkK hkN => ?_)
    (exists_mem_inf_of_mem hI1 hI2 hI4 hcore hp2 hZ hK1 hSt hA hKX hXM hXr hBC hBM hbB hb hbo hE
      hEc hEB hLM hML hCL)
  have hkC : k ∈ C := Subgroup.map_subtype_le _ hkK
  refine (hmem ⟨k, hkC⟩).mpr (Subgroup.le_normalizer_map φ ?_)
  exact ⟨⟨k, hkC⟩, Subgroup.le_normalizer_comap C.subtype hkN, rfl⟩

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
