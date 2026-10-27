module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Fstar
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate17037
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import Certificates.Certificate12952
public import Certificates.Certificate14951
public import Certificates.Certificate3029

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

theorem oddCoreIn_Gu_eq_bot_of
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (cfg : A5Cfg G T M H S L) {z u : G} (s7 : A5Step7 T M H S L z u) :
    oddCoreIn (centralizerElem u) = ⊥ := by
  have hcs := cfg.cs
  have hΓ2 := s7.Gu_gamma2
  obtain ⟨hz1, hz2'⟩ := z_facts_of_card_two (z := z) (by rw [← s7.z_gen]; exact s7.Z_card)
  have hzZ : z ∈ centerOf (borelP M L) := by rw [s7.z_gen]; exact Subgroup.mem_zpowers z
  have hz : z ∈ T ⊓ Subgroup.centralizer (T : Set G) := s7.Z_le hzZ
  have hTu2 : IsPGroup 2 ↥(T ⊓ centralizerElem u) := hcs.setting.isPGroup.to_le inf_le_left
  have hGM : centralizerElem u ⊓ M = T ⊓ centralizerElem u := by
    rw [inf_comm, ← s7.Tu_eq]
  have hS₁M : IsSylowTwoOf (T ⊓ centralizerElem u) (centralizerElem u ⊓ M) := by
    rw [hGM]
    exact ⟨le_rfl, hTu2, by rw [Subgroup.subgroupOf_self, Subgroup.index_top]; norm_num⟩
  have hinv : ∀ y ∈ oddCoreIn (centralizerElem u), z⁻¹ * y * z = y⁻¹ :=
    (IsGamma0.centralizer_le_and_inverts_oddCoreIn hcs.setting (Or.inr hΓ2) hS₁M
      hcs.setting.isSylowTwoOf_M inf_le_left hz hz1 hz2').2
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  have key : ∀ (C : StdCfg T M H S L), Sec C → u = C.u0 → oddCoreIn (centralizerElem u) = ⊥ := by
    intro C X hu0
    have hzz : z = C.zU := X.z_eq s7.z_gen
    subst hu0
    rw [hzz] at hinv
    exact X.oddCoreIn_Gu_eq_bot hinv
  rcases X.exists_w_of_Z s7.u_mem s7.u_not with h | h
  · exact key C X h
  · let C' : StdCfg T M H S L :=
      C.relabel rho13 (fun σ hσ => rho13_conj_E σ hσ) (fun σ hσ => rho13_conj_E' σ hσ)
    obtain ⟨X'⟩ := exists_sec C' s7.TC_one
    have hu' : u = C'.u0 := by
      rw [h]
      show _ = ((C.iV (vact rho13⁻¹ g1w) : ↥H) : G)
      rw [rho13_inv, vact_rho13_g1w]
    exact key C' X' hu'

theorem lemma2_4_29_9
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) (hP121 : Id2519.Prop121Three) (h2397 : Lemma2_3_9_7W)
    (hK : Lemma2_4_29_9_K) : Lemma2_4_29_9 := by
  intro G _ _ T M H S L cfg z u s7 hnc
  have hcs := cfg.cs
  have hΓ2 := s7.Gu_gamma2
  obtain ⟨hz1, hz2'⟩ := z_facts_of_card_two (z := z) (by rw [← s7.z_gen]; exact s7.Z_card)
  have hzZ : z ∈ centerOf (borelP M L) := by rw [s7.z_gen]; exact Subgroup.mem_zpowers z
  have hz : z ∈ T ⊓ Subgroup.centralizer (T : Set G) := s7.Z_le hzZ
  have hTu2 : IsPGroup 2 ↥(T ⊓ centralizerElem u) := hcs.setting.isPGroup.to_le inf_le_left
  have hGM : centralizerElem u ⊓ M = T ⊓ centralizerElem u := by
    rw [inf_comm, ← s7.Tu_eq]
  have hS₁M : IsSylowTwoOf (T ⊓ centralizerElem u) (centralizerElem u ⊓ M) := by
    rw [hGM]
    exact ⟨le_rfl, hTu2, by rw [Subgroup.subgroupOf_self, Subgroup.index_top]; norm_num⟩
  have hT : IsSylowTwoOf T M := hcs.setting.isSylowTwoOf_M
  have hodd := oddCoreIn_Gu_eq_bot_of h247 h245_4 hC54 h314 cfg s7
  obtain ⟨K, hKc⟩ : ∃ K : Subgroup G, IsComponentIn K (centralizerElem u) := by
    by_contra hno
    exact hnc (charTwo_of_no_component (fun K hK => hno ⟨K, hK⟩) hodd)
  refine ⟨K, ?_⟩
  obtain ⟨hzN, hcomm, hKM, -⟩ := IsGamma0.component_normalized_commutator_not_le hcs.setting
    (Or.inr hΓ2) hS₁M hT inf_le_left hz hz1 hz2' hKc
  obtain ⟨hinn, hlist⟩ := h2397 G T M hcs.setting (centralizerElem u) (T ⊓ centralizerElem u) T z
    (Or.inr hΓ2) hS₁M hT inf_le_left hz hz1 hz2' K hKc
  obtain ⟨hnorm, hsyl, hB, hS6⟩ := step9_of_inspection h247 h245_4 hC54 h314 hP121 hK cfg s7 hodd
    hKc hzN hcomm hKM hinn hlist
  exact
    { toA5Step7 := s7
      K_comp := hKc
      K_norm := hnorm
      RK_sylow := hsyl
      B_eq := hB
      S6 := hS6 }

end CFSG.QuasithinUnique.A5
