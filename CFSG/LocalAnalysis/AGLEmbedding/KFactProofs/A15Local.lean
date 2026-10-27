module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalPerm
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalClauses
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalEmbed
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalGamma
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalMax
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalSect
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalSylow

public section

namespace CFSG.AGLEmbedding

namespace A15Local

open Equiv

@[expose] def eqPt : Fin 15 ≃ Pt := (finProdFinEquiv (m := 3) (n := 5)).symm

theorem exists_embedding_pt {Y : Type} [Group Y] (K : Subgroup Y) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 15)) (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    ∃ φ : Y →* Perm Pt, Function.Injective φ ∧ alternatingGroup Pt ≤ φ.range := by
  obtain ⟨φ, hφ, hA⟩ := exists_embedding_alternating_of_ne_six 15 (by norm_num) (by norm_num)
    K e hC
  refine ⟨eqPt.permCongrHom.toMonoidHom.comp φ, eqPt.permCongrHom.injective.comp hφ, ?_⟩
  intro τ hτ
  have hσ : eqPt.permCongrHom.symm τ ∈ alternatingGroup (Fin 15) := by
    rw [Perm.mem_alternatingGroup] at hτ ⊢
    rw [← hτ]
    exact Perm.sign_permCongr eqPt.symm τ
  obtain ⟨y, hy⟩ := hA hσ
  refine ⟨y, ?_⟩
  show eqPt.permCongrHom (φ y) = τ
  rw [hy]
  exact eqPt.permCongrHom.apply_symm_apply τ

theorem a15InSitu_of_le {M : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hτ : blockShift ∈ M) (hMW : M ≤ wr) : A15InSitu sylowT M where
  primeCore := fun _ hW hN hc => eq_bot_of_coprime hA hτ hMW hW hN hc
  normal_dichotomy := fun _ hW hN => eq_bot_or_sylowT_le hA hτ hMW hW hN
  centralizer_le := inf_centralizer_sylowT_le
  pcore := fun _ hW hN hp => eq_bot_of_isPGroup hA hτ hMW hW hN hp
  section_card := fun _ hU V _ hs hna => card_section_of_le_wr hMW hU V hs hna
  normal_closure := fun _ hW hN hT => exists_normal_closure hA hτ hMW hW hN hT

theorem card_sylow_five {Y : Type} [Group Y] [Finite Y] {φ : Y →* Perm Pt}
    (hφ : Function.Injective φ) (hA : alternatingGroup Pt ≤ φ.range) (T : Sylow 5 Y) :
    Nat.card (T : Subgroup Y) = 5 ^ 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hY : Nat.card φ.range = Nat.card Y := Nat.card_range_of_injective hφ
  have hdvd1 : Nat.card Y ∣ Nat.card (Perm Pt) := by
    rw [← hY]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd2 : Nat.card (alternatingGroup Pt) ∣ Nat.card Y := by
    rw [← hY]
    exact Subgroup.card_dvd_of_le hA
  have hAcard : 2 * Nat.card (alternatingGroup Pt) = Nat.card (Perm Pt) :=
    two_mul_nat_card_alternatingGroup
  rw [card_perm_pt] at hAcard hdvd1
  have hA5 : 5 ^ 3 ∣ Nat.card Y := by
    refine dvd_trans ?_ hdvd2
    have : Nat.card (alternatingGroup Pt) = 653837184000 := by omega
    rw [this]
    norm_num
  have hne : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ≤ (Nat.card Y).factorization 5 :=
    (Nat.Prime.pow_dvd_iff_le_factorization this.out hne).1 hA5
  have h4 : (Nat.card Y).factorization 5 < 4 := by
    by_contra hcon
    have : 5 ^ 4 ∣ Nat.card Y :=
      (Nat.Prime.pow_dvd_iff_le_factorization this.out hne).2 (not_lt.1 hcon)
    have h5 := this.trans hdvd1
    norm_num at h5
  rw [T.card_eq_multiplicity]
  congr 1
  omega

end A15Local

open A15Local CFSG.Open Equiv

theorem kFactA15Local : KFactA15Local := by
  intro Y _ _ K hK e hC T Y₀ hW hY₀
  have : K.Normal := hK
  obtain ⟨e⟩ := e
  obtain ⟨φ₁, hφ₁, hA₁⟩ := exists_embedding_pt K e hC
  have hTcard : Nat.card (T : Subgroup Y) = 5 ^ 3 := card_sylow_five hφ₁ hA₁ T
  have hP : IsPGroup 5 ((T : Subgroup Y).map φ₁) := T.isPGroup'.map φ₁
  obtain ⟨g, hg⟩ := exists_conj_eq_sylowT hP
    (by rw [Subgroup.card_map_of_injective hφ₁, hTcard])
  let φ : Y →* Perm Pt := (MulAut.conj g).toMonoidHom.comp φ₁
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp hφ₁
  have hTφ : (T : Subgroup Y).map φ = sylowT := by
    rw [← hg, Subgroup.map_map]
  have hAφ : alternatingGroup Pt ≤ φ.range := by
    intro τ hτ
    have hτ' : g⁻¹ * τ * g ∈ alternatingGroup Pt := by
      have := (Perm.mem_alternatingGroup (f := τ)).1 hτ
      rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, this]
      simp
    obtain ⟨y, hy⟩ := hA₁ hτ'
    refine ⟨y, ?_⟩
    show g * φ₁ y * g⁻¹ = τ
    rw [hy]
    group
  have hT0 : φ.range ⊓ Subgroup.normalizer (sylowT : Set (Perm Pt)) ≤ Y₀.map φ :=
    range_inf_normalizer_le hφ hTφ hW le_rfl isElemAbelian_sylowT (m := 3) (by norm_num)
      card_sylowT
  have hTM : sylowT ≤ Y₀.map φ := by
    intro x hx
    have hx' : x ∈ (T : Subgroup Y).map φ := by rw [hTφ]; exact hx
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hx'
    exact hT0 ⟨⟨t, rfl⟩, Subgroup.le_normalizer hx⟩
  have hτM : blockShift ∈ Y₀.map φ :=
    hT0 ⟨hAφ blockShift_mem_alternatingGroup, blockShift_mem_normalizer⟩
  have hAM : ∀ i, blockAlt i ≤ Y₀.map φ := fun k x hx =>
    range_inf_normalizer_le hφ hTφ hW (qPair_le_sylowT k) (isElemAbelian_qPair k) (m := 2)
      le_rfl (card_qPair k)
      ⟨hAφ (blockAlt_le_alternatingGroup k hx), blockAlt_le_normalizer_qPair k hx⟩
  have h3 : ∃ x ∈ Y₀.map φ, x.IsThreeCycle :=
    ⟨cyc3 0 0 1 2, hAM 0 (cyc3_mem_blockAlt 0 (by decide) (by decide) (by decide)),
      isThreeCycle_cyc3 0 (by decide) (by decide) (by decide)⟩
  rcases le_wr_or_alternatingGroup_le hTM hτM h3 with hMW | hAMa
  · exact A15InSitu.of_map φ hφ hTφ rfl (a15InSitu_of_le hAM hτM hMW)
  ·
    exfalso
    apply hY₀
    have hrange : φ.range ≤ Y₀.map φ := by
      intro y hy
      rcases Int.units_eq_one_or (Perm.sign y) with hs | hs
      · exact hAMa (Perm.mem_alternatingGroup.2 hs)
      · have h1 : mulTwo * y⁻¹ ∈ alternatingGroup Pt := by
          rw [Perm.mem_alternatingGroup, map_mul, map_inv, hs, sign_mulTwo]
          decide
        have hm : mulTwo ∈ φ.range := by
          have := mul_mem (hAφ h1) hy
          simpa using this
        have hmM : mulTwo ∈ Y₀.map φ := hT0 ⟨hm, mulTwo_mem_normalizer⟩
        have h2 : y * mulTwo⁻¹ ∈ alternatingGroup Pt := by
          rw [Perm.mem_alternatingGroup, map_mul, map_inv, hs, sign_mulTwo]
          decide
        simpa using mul_mem (hAMa h2) hmM
    refine Subgroup.map_injective hφ ?_
    rw [← MonoidHom.range_eq_map]
    exact le_antisymm (Subgroup.map_le_range φ Y₀) hrange

end CFSG.AGLEmbedding
