module

public import CFSG.ClassicalInvolution.Q3.Sec13EndHyp
import CFSG.ClassicalInvolution.Q3.Sec13PerpD
import CFSG.ClassicalInvolution.Q3.Sec13L711Mu

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem dict_q8Omega {Ω : Set (Subgroup G)} (h : EndHyp Ω) : Q8Omega Ω :=
  ⟨h.thmD.hyp, h.thmD.two, fun J hJ => h.card_eq_eight hJ, h.thmD.aEmpty⟩

private theorem dict_twinSet_conj_image {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G)
    (L : Subgroup G) : twinSet Ω (conjSub g L) = conjSub g '' twinSet Ω L := by
  refine Set.Subset.antisymm ?_ ?_
  · intro M hM
    refine ⟨conjSub g⁻¹ M, ?_, conjSub_conjSub_inv g M⟩
    have hM' := twinSet_conj hΩ hM g⁻¹
    rwa [conjSub_inv_conjSub] at hM'
  · rintro _ ⟨J, hJ, rfl⟩
    exact twinSet_conj hΩ hJ g

private theorem dict_involution_mem {Ω : Set (Subgroup G)} (h : EndHyp Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {K : Subgroup G} (hK : K ∈ DSet Ω W) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ W := by
  have hKΩ : K ∈ Ω := (h.mem_dSet_iff.mp hK).1
  have hKK : IsSylow2In K K :=
    ⟨le_rfl, h.thmD.two K hKΩ, fun _ hV' _ hKV' => le_antisymm hV' hKV'⟩
  obtain ⟨-, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D h.thmD.hyp hW hK hKΩ hKK
  exact (hz.mem_of_le inf_le_left ((h.thmD.two K hKΩ).to_le inf_le_left) (by omega)).2

namespace EndHyp

variable {Ω : Set (Subgroup G)}

theorem exists_mem_dSet (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∃ R ∈ Ω, R ∈ DSet Ω W := by
  obtain ⟨η, hη, rfl⟩ := hW
  rcases Set.eq_empty_or_nonempty η with rfl | ⟨U, hU⟩
  · obtain ⟨L, hL, -⟩ := h.exists_ne
    refine ⟨L, hL, h.mem_dSet_iff.mpr ⟨hL, ?_⟩⟩
    rw [iSup_emptyset, Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
    exact le_top
  · obtain ⟨J, hJ, -⟩ := (dict_q8Omega h).exists_mem_DSet_of_mem_eta hη hU
    exact ⟨J, (h.mem_dSet_iff.mp hJ).1, hJ⟩

theorem twinSet_subset_dSet (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) : twinSet Ω R ⊆ DSet Ω W := by
  rintro M ⟨hM, z, hzR, hzM⟩
  exact h.mem_dSet_of_mem hW hM hzM (dict_involution_mem h hW hR hzR)

theorem ncard_twinSet_of_mem_dSet (h : EndHyp Ω)
    (h9' : ∀ K ∈ Ω, KPerp Ω K = twinSet Ω K) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    (MuIsoS3 Ω W → (twinSet Ω R).ncard = 1) ∧ (MuIsoS4 Ω W → (twinSet Ω R).ncard = 2) ∧
      (MuIsoWylD4 Ω W → (twinSet Ω R).ncard = 4) := by
  have hKP : KPerp Ω R ∩ DSet Ω W = twinSet Ω R := by
    rw [h9' R (h.mem_dSet_iff.mp hR).1]
    exact Set.inter_eq_left.mpr (h.twinSet_subset_dSet hW hR)
  have hc := dSet_class_ncard h hW hR
  rwa [hKP] at hc

theorem exists_twinSet_pair_of_muIsoS4 (h : EndHyp Ω)
    (h9' : ∀ K ∈ Ω, KPerp Ω K = twinSet Ω K) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hS4 : MuIsoS4 Ω W) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    ∃ R' : Subgroup G, R' ≠ R ∧ twinSet Ω R = {R, R'} := by
  obtain ⟨x, y, hxy, hV⟩ := Set.ncard_eq_two.mp
    ((ncard_twinSet_of_mem_dSet h h9' hW hR).2.1 hS4)
  have hRV : R ∈ twinSet Ω R := by
    rw [← h9' R (h.mem_dSet_iff.mp hR).1]
    exact Set.mem_insert _ _
  rw [hV, Set.mem_insert_iff, Set.mem_singleton_iff] at hRV
  rcases hRV with h1 | h1
  · exact ⟨y, fun e => hxy (e.trans h1).symm, by rw [hV, h1]⟩
  · exact ⟨x, fun e => hxy (e.trans h1), by rw [hV, h1, Set.pair_comm]⟩

theorem muIsoS4_of_twinSet_pair (h : EndHyp Ω)
    (h9' : ∀ K ∈ Ω, KPerp Ω K = twinSet Ω K) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R R' : Subgroup G} (hR : R ∈ DSet Ω W) (hV : twinSet Ω R = {R, R'}) (hne : R ≠ R') :
    MuIsoS4 Ω W := by
  have hc := ncard_twinSet_of_mem_dSet h h9' hW hR
  have h2 : (twinSet Ω R).ncard = 2 := by rw [hV, Set.ncard_pair hne]
  rcases h.mu W hW with h3 | h4 | hw
  · have h1 := hc.1 h3
    omega
  · exact h4
  · have h4' := hc.2.2 hw
    omega

theorem exists_twinSet_pair_of_exists_muIsoS4 (h : EndHyp Ω)
    (h9' : ∀ K ∈ Ω, KPerp Ω K = twinSet Ω K) (hS4 : ∃ W ∈ WSet Ω, MuIsoS4 Ω W) :
    ∀ K ∈ Ω, ∃ K' : Subgroup G, K' ≠ K ∧ twinSet Ω K = {K, K'} := by
  obtain ⟨W, hW, hS4W⟩ := hS4
  intro K hK
  obtain ⟨L, hLΩ, hLD⟩ := h.exists_mem_dSet hW
  obtain ⟨L', hne, hV⟩ := h.exists_twinSet_pair_of_muIsoS4 h9' hW hS4W hLD
  obtain ⟨g, rfl⟩ := h.thmD.trans L hLΩ K hK
  refine ⟨conjSub g L', fun e => hne (conjSub_injective g e), ?_⟩
  rw [dict_twinSet_conj_image h.thmD.hyp.conjInvariant g L, hV, Set.image_pair]

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
