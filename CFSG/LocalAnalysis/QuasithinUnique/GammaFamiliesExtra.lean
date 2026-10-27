module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraConfining
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Components

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem UniqueSetting.centralizer_le_of_mem_center_isSylowTwoOf (h : UniqueSetting G T M)
    {T' : Subgroup G} (hT' : IsSylowTwoOf T' M) {z : G}
    (hz : z ∈ T' ⊓ Subgroup.centralizer (T' : Set G)) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ M := by
  have hzpow : Subgroup.zpowers z ≤ T' := (Subgroup.zpowers_le).mpr hz.1
  have hZ : Subgroup.zpowers z ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hz1
  have hAZ : (T' : Set G) ⊆ (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :
      Subgroup G) := by
    intro t ht
    show t ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz.2 t ht
  have hMT : {K : Subgroup G | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
      (T' : Set G) ⊆ (K : Set G)} = {M} := by
    ext K
    constructor
    · rintro ⟨hK, hTK⟩
      exact h.unique_of_isSylowTwoOf_M hT' K hK hTK
    · intro hK
      rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨h.maxLocal, hT'.le⟩
  have htrans := maxTwoLocal_centralizer_transfer hZ (hT'.isPGroup.to_le hzpow) hAZ hMT
  have hcent : Subgroup.centralizer ({z} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent]
  exact htrans.1.trans htrans.2.1

theorem IsGamma0.exists_central_involution (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) :
    ∃ (T' : Subgroup G) (z : G), IsSylowTwoOf T' M ∧ S ≤ T' ∧
      z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) ∧ z ≠ 1 ∧ z ^ 2 = 1 := by
  obtain ⟨-, hSc, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le hSc.1 hS.isPGroup
  have hT'1 : T' ≠ ⊥ := ne_bot_of_le_ne_bot hSc.2.1 hST'
  have hZ : T' ⊓ Subgroup.centralizer (T' : Set G) ≠ ⊥ := inf_centralizer_ne_bot hT'.isPGroup hT'1
  obtain ⟨z, hzZ, hz1, hz2⟩ :=
    GammaExtra.exists_involution_of_ne_bot (hT'.isPGroup.to_le inf_le_left) hZ
  exact ⟨T', z, hT', hST', hzZ, hz1, hz2⟩

theorem IsGamma0.exists_sylow_center_le_lt (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) :
    ∃ T' : Subgroup G, IsSylowTwoOf T' M ∧ S ≤ T' ∧ S < T' ∧
      T' ⊓ Subgroup.centralizer (T' : Set G) ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
  obtain ⟨-, hSc, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le hSc.1 hS.isPGroup
  obtain ⟨hcentre, hlt, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  exact ⟨T', hT', hST', hlt, hcentre⟩

theorem IsGamma0.lemma115Hyp (h : UniqueSetting G T M) {H S : Subgroup G} {z : G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M))
    (hzS : z ∈ S ⊓ Subgroup.centralizer (S : Set G)) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hcentral : ∃ T' : Subgroup G, IsSylowTwoOf T' M ∧
      z ∈ T' ⊓ Subgroup.centralizer (T' : Set G)) : Lemma115Hyp H S M z := by
  have hSH : IsSylowTwoOf S H := hH.isSylowTwoOf_of_inf h hS
  have hE := hH.core_centralizer_le h hS
  have hQS : pCoreOf 2 H ≤ S := hSH.le_of_normalizes
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hQ : pCoreOf 2 H ≤ pCoreOf 2 (H ⊓ M) :=
    le_pCoreOf_of_normalizes (hQS.trans hS.le)
      (inf_le_left.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  obtain ⟨T', hT', hzT'⟩ := hcentral
  exact
    { pCore_ne_bot := hH.isGamma.1
      sylow := hSH
      charTwo := h.charTwo
      pCore_M_ne_bot := CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_pCoreOf_ne_bot M h.isTwoLocal
      le := hS.le.trans inf_le_right
      centralizer_le := fun y hy => (hS.le.trans inf_le_left)
        (hE ⟨hy.1, Subgroup.centralizer_le (by exact_mod_cast hQ) hy.2⟩)
      centralizer_z_le := h.centralizer_le_of_mem_center_isSylowTwoOf hT' hzT' hz1
      z_ne_one := hz1
      z_mem := hzS.1
      z_central := hzS.2
      z_sq := hz2 }

theorem IsGamma0.charTwo_inf (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) : CharTwo (H ⊓ M) := by
  obtain ⟨T', z, hT', hST', hz, hz1, hz2⟩ := hH.exists_central_involution h hS
  obtain ⟨hcentre, -, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  exact (hH.lemma115Hyp h hS (hcentre hz) hz1 hz2 ⟨T', hT', hz⟩).charTwo_inf

theorem IsGamma0.centralizer_le_and_inverts_oddCoreIn (h : UniqueSetting G T M)
    {H S T' : Subgroup G} {z : G} (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M))
    (hT' : IsSylowTwoOf T' M) (hST' : S ≤ T') (hz : z ∈ T' ⊓ Subgroup.centralizer (T' : Set G))
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Subgroup.centralizer ({z} : Set G) ≤ M ∧ ∀ y ∈ oddCoreIn H, z⁻¹ * y * z = y⁻¹ := by
  obtain ⟨hcentre, -, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  exact ⟨h.centralizer_le_of_mem_center_isSylowTwoOf hT' hz hz1,
    (hH.lemma115Hyp h hS (hcentre hz) hz1 hz2 ⟨T', hT', hz⟩).inverts_oddCoreIn⟩

theorem IsGamma0.isConfining_of_relIndex_two_of_le (h : UniqueSetting G T M) {H S R : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hRS : R ≤ S) (hidx : R.relIndex S = 2)
    (hJR : thompsonJ S ≤ R) (hQR : pCoreOf 2 H ≤ R)
    (hCR : S ⊓ Subgroup.centralizer (R : Set G) ≤ R) : IsConfining M R := by
  refine hH.isConfining_of_relIndex_two h hS hJR hRS hidx fun y hy => ?_
  have hyS : y ∈ S := hH.core_centralizer_le h hS
    ⟨hy.1, Subgroup.centralizer_le (by exact_mod_cast hQR) hy.2⟩
  exact hCR ⟨hyS, hy.2⟩

end Components

end CFSG.QuasithinUnique
