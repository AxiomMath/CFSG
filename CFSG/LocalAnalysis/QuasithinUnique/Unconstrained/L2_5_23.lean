module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Fusion

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Conj

variable {G : Type*} [Group G]

theorem conjugate_inf_normalizer {A E : Subgroup G} {s : G} (hs : s ∈ A) :
    CFSG.conjugate (A ⊓ Subgroup.normalizer (E : Set G)) s =
      A ⊓ Subgroup.normalizer ((CFSG.conjugate E s : Subgroup G) : Set G) := by
  unfold CFSG.conjugate
  rw [map_equiv_inf, normalizer_map_equiv, map_conj_eq_self_of_mem (A.inv_mem hs)]

theorem IsUStarPair.conjugate {M H U HU : Subgroup G} {g : G} (hgM : g ∈ M) (hgH : g ∈ H)
    (h : IsUStarPair M H U HU) :
    IsUStarPair M H (CFSG.conjugate U g) (CFSG.conjugate HU g) := by
  have hf : M.map (MulAut.conj g⁻¹).toMonoidHom = M := map_conj_eq_self_of_mem (M.inv_mem hgM)
  have hfH : H.map (MulAut.conj g⁻¹).toMonoidHom = H := map_conj_eq_self_of_mem (H.inv_mem hgH)
  have hf' := map_symm_eq_self_of_map_eq_self hf
  refine ⟨⟨h.1.1.map_equiv hf, ?_⟩, ?_⟩
  · rw [← hfH]
    exact Subgroup.map_mono h.1.2
  · intro V hV
    calc Nat.card V = Nat.card (V.map (MulAut.conj g⁻¹).symm.toMonoidHom) :=
          (card_map_equiv _ V).symm
      _ ≤ Nat.card U := h.2 _ (hV.map_equiv hf')
      _ = Nat.card (U.map (MulAut.conj g⁻¹).toMonoidHom) := (card_map_equiv _ U).symm

end Conj

section Stage

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

theorem Notation25.exists_ustar_pair_le_S (N : Notation25 hs) :
    ∃ U HU : Subgroup G, IsUStarPair M N.H U HU ∧ U ≤ N.S := by
  obtain ⟨⟨-, U₀, HU₀, hwit, hHU₀, hmax⟩, -⟩ := N.gammaU
  have hpair₀ : IsUStarPair M N.H U₀ HU₀ := ⟨⟨hwit, hHU₀⟩, hmax⟩
  have hU₀HM : U₀ ≤ N.H ⊓ M := le_inf (hwit.2.1.trans hHU₀) hwit.1.1
  obtain ⟨S', hU₀S', hS'⟩ := exists_isSylowTwoOf_of_le hU₀HM hwit.1.2.2.1
  obtain ⟨m, hm, hS'm⟩ := N.tuple.sylow_inf.exists_conj hS'
  refine ⟨CFSG.conjugate U₀ m, CFSG.conjugate HU₀ m, hpair₀.conjugate hm.2 hm.1, ?_⟩
  have hsymm : (MulAut.conj m).symm = MulAut.conj m⁻¹ := by
    ext x
    simp [MulAut.conj_symm_apply]
  calc U₀.map (MulAut.conj m⁻¹).toMonoidHom ≤ S'.map (MulAut.conj m⁻¹).toMonoidHom :=
        Subgroup.map_mono hU₀S'
    _ = N.S := by
      rw [hS'm, ← hsymm]
      exact map_equiv_symm_map_equiv _ _

end Stage

theorem lemma2523 : Lemma2523 := by
  intro G _ _ T M hs N t zK h
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]
    exact N.H_le_normalizer_K0
  have h258 : Facts258 N := h.facts258
  have h2512 := h.concl2512 hKH
  obtain ⟨hKA⟩ := h.concl2521.1
  have hSK2 : IsPGroup 2 ↥N.SK := N.tuple.sylow.isPGroup.to_le N.SK_le_S
  have hcardK : Nat.card N.K = 360 := by
    rw [Nat.card_congr hKA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have h8 := eight_le_card_of_shape h258.SK_shape
  have hSKcard : Nat.card N.SK = 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := hSK2.exists_card_eq
    have hdvd : Nat.card N.SK ∣ Nat.card N.K := Subgroup.card_dvd_of_le N.SK_le_K
    rw [hj, hcardK] at hdvd
    rw [hj] at h8 ⊢
    have hj3 : j ≤ 3 := by
      by_contra hcon
      have h4 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have := h4.trans hdvd
      norm_num at this
    have hj3' : 3 ≤ j := by
      by_contra hcon
      have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hj : j = 3 := le_antisymm hj3 hj3'
    rw [hj]
    norm_num
  obtain ⟨e⟩ : Nonempty (↥N.SK ≃* DihedralGroup 4) := by
    rcases h258.SK_shape with ⟨n, hn, he⟩ | he
    · obtain ⟨e⟩ := he
      have hc : Nat.card N.SK = 2 * n := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have : n = 4 := by omega
      subst this
      exact ⟨e⟩
    · exfalso
      obtain ⟨e⟩ := he
      have h16 := CFSG.Semidihedral.card 4 (by norm_num)
      rw [← Nat.card_congr e.toEquiv] at h16
      omega
  obtain ⟨E₁, E₂, hE₁X, hE₂X, hE₁4, hE₂4, hne, hall⟩ := D8.exists_two_four_subgroups e
  obtain ⟨U₀, HU₀, hpair₀, hU₀S⟩ := N.exists_ustar_pair_le_S
  obtain ⟨⟨E₀, hE₀K, hE₀4, hHU₀, hU₀, -, -, -⟩, -⟩ := h2512.1 U₀ HU₀ hpair₀ hU₀S
  have key : ∀ E : Subgroup G, E ≤ N.SK → IsFourSubgroup E →
      IsUStarPair M N.H (N.S ⊓ Subgroup.normalizer (E : Set G))
        (N.H ⊓ Subgroup.normalizer (E : Set G)) := by
    intro E hEK hE4
    obtain ⟨s, hsS, hEs⟩ := a6FourSubgroupFusion G T M hs N hKH h.concl2521 E₀ E hE₀K hE₀4 hEK hE4
    have hsH : s ∈ N.H := N.S_le_H hsS
    have hsM : s ∈ M := hs.setting.le (N.S_le_T hsS)
    have hconj := hpair₀.conjugate hsM hsH
    rw [hU₀, hHU₀, conjugate_inf_normalizer hsS, conjugate_inf_normalizer hsH, ← hEs] at hconj
    exact hconj
  refine ⟨E₁, E₂, hE₁X, hE₂X, hE₁4, hE₂4, hne, hall, ?_, ?_⟩
  · intro U HU hpair hUS
    obtain ⟨⟨E, hEK, hE4, hHU, hU, -, -, -⟩, -⟩ := h2512.1 U HU hpair hUS
    rcases hall E hEK hE4 with rfl | rfl
    · exact Or.inl ⟨hU, hHU⟩
    · exact Or.inr ⟨hU, hHU⟩
  · intro E hE
    rcases hE with rfl | rfl
    · exact ⟨key _ hE₁X hE₁4, h2512.2.1 _ hE₁X hE₁4⟩
    · exact ⟨key _ hE₂X hE₂4, h2512.2.1 _ hE₂X hE₂4⟩

end CFSG.QuasithinUnique
