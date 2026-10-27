module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Setup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Rank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Emb

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open

theorem isElemAbelian_comap_of_inj {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {E : Subgroup H} {p : ℕ} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨IsMulCommutative.of_comm ?_, fun x hx => ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    apply hf
    have := hE.1.is_comm.comm ⟨f a, ha⟩ ⟨f b, hb⟩
    simpa using congrArg Subtype.val this
  · apply hf
    rw [map_pow, hE.2 _ hx, map_one]

theorem elem_le_nine_sp8 (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760) (F : Subgroup Sp8)
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card spT0 = 3 ^ (Nat.card Sp8).factorization 3 := by
    rw [card_spT0, hcard, factorization_three]
    norm_num
  let S0 : Sylow 3 Sp8 := Sylow.ofCard spT0 hc
  have hpg : IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩
  obtain ⟨P, hFP⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Sp8 S0 P
  have hP : (P : Subgroup Sp8) = spT0.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  set F' := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hF'le : F' ≤ spT0 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hFP hx
    rw [hP] at this
    obtain ⟨y, hy, hyx⟩ := this
    have : (MulAut.conj g⁻¹).toMonoidHom x = y := by
      rw [← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hy
  have hF'e : IsElemAbelian 3 F' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hF _
  have hle : F' ≤ spE := fun x hx => (mem_spE_iff_cube x).2 ⟨hF'le hx, hF'e.2 x hx⟩
  have h9 := Subgroup.card_le_of_le hle
  rw [card_spE] at h9
  rwa [hF', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h9

theorem exists_setup {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] (eK : K ≃* Sp8)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760)
    (T : Sylow 3 Y) (h3 : 3 ≤ Open.pRank 3 (T : Subgroup Y)) :
    ∃ (e : K ≃* Sp8) (y : Y), Sp48Setup e (T : Subgroup Y) y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardK : Nat.card K = 3 ^ 4 * 13045760 := by
    rw [← hcard]
    exact Nat.card_congr eK.toEquiv
  have hnot : ¬ (T : Subgroup Y) ≤ K := by
    intro hTK
    obtain ⟨E, hET, hE, hcardE⟩ :=
      CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (T : Subgroup Y)
    have hκ : Function.Injective (emb eK) := emb_injective eK
    have hEκ : E ≤ (emb eK).range := fun x hx => ⟨eK ⟨x, hTK (hET hx)⟩, by simp [emb_apply]⟩
    have hF : IsElemAbelian 3 (E.comap (emb eK)) := isElemAbelian_comap_of_inj hκ hE
    have h9 := elem_le_nine_sp8 hcard _ hF
    have hc : Nat.card (E.comap (emb eK)) = Nat.card E := by
      conv_rhs => rw [← Subgroup.map_comap_eq_self hEκ]
      rw [Subgroup.card_map_of_injective hκ]
    rw [hc, hcardE] at h9
    have : Open.pRank 3 (T : Subgroup Y) ≤ 2 := by
      by_contra hlt
      have : 3 ^ 3 ≤ 3 ^ Open.pRank 3 (T : Subgroup Y) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  obtain ⟨y₀, hy₀T, hy₀K⟩ : ∃ y ∈ (T : Subgroup Y), y ∉ K := by
    by_contra h
    push Not at h
    exact hnot fun x hx => h x hx
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y₀ ^ (3 ^ m) = 1 := by
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨y₀, hy₀T⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨φ, hφ, hφ3, hφK⟩ := exists_frob hC (eK := eK) hy₀K hm
  have hact : ∀ k : Sp8, φ * emb eK k * φ⁻¹ = emb eK (fr k) := by
    intro k
    have := coe_symm_adHom K eK φ k
    rw [hφ] at this
    exact this.symm
  obtain ⟨T1, hT1⟩ := exists_tSub eK φ hφ3 hact hφK
  have hc1 : Nat.card T1 = 3 ^ 5 := hT1.card_T
  have hT1p : IsPGroup 3 T1 := IsPGroup.of_card hc1
  have hTle : Nat.card (T : Subgroup Y) ≤ 3 ^ 5 := by
    have hidx := index_le_six (eK := eK) hC
    have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 T.isPGroup'
    have hdvd : 3 ^ a ∣ 3 ^ 4 * 13045760 * K.index := by
      rw [← ha]
      have := Subgroup.card_subgroup_dvd_card (T : Subgroup Y)
      rwa [← Subgroup.card_mul_index K, hcardK] at this
    rw [ha]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hlt
    have h6 : 3 ^ 6 ∣ 3 ^ 4 * 13045760 * K.index :=
      (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
    generalize K.index = i at hidx hidx0 h6
    interval_cases i <;> omega
  obtain ⟨y₁, hy₁⟩ := exists_conj_eq_map T hT1p hc1 hTle
  refine ⟨econj eK y₁, y₁ * φ * y₁⁻¹, ?_⟩
  rw [hy₁]
  exact hT1.conj y₁

end CFSG.AGLEmbedding.KFactProofs.Sp48
