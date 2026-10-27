module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.R37A1

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem isGamma2_of_witness (hcs : ConstrainedSetting G T M H S L) (hB : Basic31 T M H S L s)
    {X S₁ : Subgroup G} (hpc : pCoreOf 2 X ≠ ⊥) (hpair : IsWitnessPair M (baum S) X)
    (hS₁T : S₁ ≤ T) (hS₁R : baum S < S₁) (hS₁X : S₁ ≤ X) :
    IsGamma2 M X ∧ IsSylowTwoOf S₁ X ∧ IsSylowTwoOf S₁ (X ⊓ M) := by
  have hS₁2 : IsPGroup 2 ↥S₁ := hcs.setting.isPGroup.to_le hS₁T
  have hΓ : IsGamma M X := ⟨hpc, baum S, X, hpair, le_rfl⟩
  have hcardT : Nat.card T = 2 * Nat.card S := by
    have := C5.card_eq_card_mul_relIndex hcs.le_T
    rw [hB.idx_T] at this
    omega
  have hcardS : Nat.card S = 2 * Nat.card (baum S) :=
    GammaExtra.card_eq_two_mul_of_relIndex_eq_two inf_le_left hB.idx_R
  have h1 : Nat.card S ≤ Nat.card S₁ := by
    have := GammaExtra.two_mul_card_le_of_lt hS₁R
    omega
  have h2 : Nat.card S₁ ≤ twoPart X := card_le_twoPart hS₁X hS₁2
  obtain ⟨-, hext⟩ := hcs.gamma0.isGamma2_of_card_eq_two_mul hcs.setting hcs.sylow_inf hcardT
  obtain ⟨hcard, hΓ2⟩ := hext _ hΓ (h1.trans h2)
  have hS₁eq : Nat.card S₁ = twoPart X := by omega
  refine ⟨hΓ2, isSylowTwoOf_of_card_eq hS₁X hS₁2 hS₁eq, ?_⟩
  have hS₁M : S₁ ≤ M := hS₁T.trans hcs.setting.le
  have hle : twoPart (X ⊓ M) ≤ twoPart X := twoPart_mono inf_le_left
  have hge : Nat.card S₁ ≤ twoPart (X ⊓ M) := card_le_twoPart (le_inf hS₁X hS₁M) hS₁2
  exact isSylowTwoOf_of_card_eq (le_inf hS₁X hS₁M) hS₁2 (by omega)

section Reentry

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hSA : ConstrainedSetupAt)
  (hlin : Lin2BlockExcluded) (ha5 : A5BlockExcluded) (ha3 : SingleA3Excluded)
  (hK : A3A3K T M H S L s x z₁ z₂ K)
include hD h27_1 hSA hlin ha5 ha3 hK

theorem A3A3K.exists_blocks_A1
    (hbot : (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s = ⊥)
    (hcomm : ∀ a ∈ baum S ⊓ K, ∀ b ∈ conjR (baum S ⊓ K) s, a * b = b * a)
    (hR64 : Nat.card (baum S) = 64) :
    ∃ (L₁ L₂ U₁ U₂ : Subgroup G) (s' : G), IsA4Block L₁ U₁ ∧ IsA4Block L₂ U₂ ∧
      (∀ l ∈ L₁, ∀ l' ∈ L₂, l * l' = l' * l) ∧ U₁ ⊔ U₂ = blockA1 L s x ∧ s' ∈ T ∧
      U₂ = conjR U₁ s' := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨hA1ab, hA1card⟩ := hK.blockA1_card hD h27_1 hbot hcomm
  have hUx := hK.blockUx_le_rK hD h27_1
  have hU2 := hK.blockU2_le_rKs
  have hA12 : IsPGroup 2 (blockA1 L s x) := IsPGroup.of_card (n := 4) (by rw [hA1card]; norm_num)
  have hzA : z₁ * z₂ ∈ blockA1 L s x := hK.z_mem_blockA1
  have hzT := z_central hB hK.toA3A3x
  have hz1 : z₁ * z₂ ≠ 1 := hK.toA3A3x.z_ne
  have hct : CharTwo (normalizer (blockA1 L s x : Set G)) :=
    charTwo_normalizer_of_inf_center hcs.setting.qtke.2.1 hcs.setting.sylow hA12 (by
      intro h
      have : z₁ * z₂ ∈ blockA1 L s x ⊓ (T ⊓ centralizer (T : Set G)) := ⟨hzA, hzT⟩
      rw [h] at this
      exact hz1 (Subgroup.mem_bot.mp this))
  have hA1ne : blockA1 L s x ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA1card
    omega
  have hpcore : blockA1 L s x ≤ pCoreOf 2 (normalizer (blockA1 L s x : Set G)) :=
    le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hA12
  have hpc : pCoreOf 2 (normalizer (blockA1 L s x : Set G)) ≠ ⊥ := fun h =>
    hA1ne (le_bot_iff.mp (h ▸ hpcore))
  have hL₂N := hK.Ls_le_normalizer_blockA1 hD h27_1 hcomm
  have hH₁M : ¬ normalizer (blockA1 L s x : Set G) ≤ M := fun h =>
    hK.toA3A3x.not_Ls_le (hL₂N.trans h)
  have hRN := hK.baum_le_normalizer_blockA1 hD h27_1
  have hRT : baum S ≤ T := (inf_le_left : baum S ≤ S).trans hcs.le_T
  have hpair : IsWitnessPair M (baum S) (normalizer (blockA1 L s x : Set G)) :=
    ⟨(isConfining_baum hcs hB).2, hRN, hpc, hct, hH₁M⟩
  have hc : ∀ a ∈ blockU2 L s, ∀ b ∈ conjR (blockU L) x, a * b = b * a := fun a ha b hb =>
    (hcomm b (hUx hb) a (hU2 ha)).symm
  have hxs : x * s ∈ T ⊓ normalizer (blockA1 L s x : Set G) :=
    ⟨mul_mem hK.x_mem (hcs.le_T hK.s_mem), hK.mul_xs_mem_normalizer_blockA1 hD h27_1 hc⟩
  have hxsR : x * s ∉ baum S := by
    intro h
    apply hK.x_not_mem
    have : x = (x * s) * s⁻¹ := by group
    rw [this]
    exact mul_mem ((inf_le_left : baum S ≤ S) h) (inv_mem hK.s_mem)
  have hRSA : baum S < T ⊓ normalizer (blockA1 L s x : Set G) :=
    lt_of_le_of_ne (le_inf hRT hRN) (fun h => by
      rw [← h] at hxs
      exact hxsR hxs)
  obtain ⟨hΓ2, -, hSylHM⟩ := isGamma2_of_witness hcs hB hpc hpair inf_le_left hRSA inf_le_right
  obtain ⟨P', L', hP'H, hcs'⟩ := hSA G T M (normalizer (blockA1 L s x : Set G))
    (T ⊓ normalizer (blockA1 L s x : Set G)) hcs.setting hcs.notBender hcs.notSmall (Or.inr hΓ2)
    hct hSylHM inf_le_left
  obtain ⟨s', hcfg'⟩ : ∃ s' : G, A3A3 T M P' (T ⊓ normalizer (blockA1 L s x : Set G)) L' s' := by
    rcases hcs'.block.2 with ⟨n, hn, hlin2⟩ | h3 | h5
    · exact (hlin G T M P' _ L' hcs' n hn hlin2).elim
    · by_cases hj : conjJoin (T ⊓ normalizer (blockA1 L s x : Set G)) L' = L'
      · exact (ha3 G T M P' _ L' hcs' h3 hj).elim
      · exact exists_A3A3 hcs' h3 hj
    · exact (ha5 G T M P' _ L' hcs' h5).elim
  have hB' := basic31 hD h27_1 hcfg'
  have hRR : baum (T ⊓ normalizer (blockA1 L s x : Set G)) = baum S := by
    rw [hB'.hbJ, hB'.hJT, ← hB.hJT, ← hB.hbJ]
  have hQ16 : Nat.card (pCoreOf 2 P') = 16 := by
    have := hB'.card_R_Q
    rw [hRR, hR64] at this
    omega
  have hA4 := hcfg'.isA4
  have hA4s := hcfg'.isA4s
  have hc' := hcfg'.comm_elem
  have hinf := hA4.inf_eq_bot hA4s hc'
  have hU0card : Nat.card ↥(blockU L' ⊔ blockU2 L' s') = 16 := by
    have hN : blockU L' ≤ normalizer (blockU2 L' s' : Set G) :=
      C5.le_normalizer_of_commute fun a ha b hb => hc' a (hA4.le ha) b (hA4s.le hb)
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hN
    rw [hinf, Subgroup.card_bot, hA4.card_U, hA4s.card_U] at h1
    omega
  have hU0 := hcfg'.blockU0_eq hB'.hU0
  have hU0Q : blockU L' ⊔ blockU2 L' s' ≤ pCoreOf 2 P' := by
    rw [← hU0, hB'.hQ]
    exact le_sup_right
  have hQeq : blockU L' ⊔ blockU2 L' s' = pCoreOf 2 P' :=
    Subgroup.eq_of_le_of_card_ge hU0Q (by rw [hQ16, hU0card])
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hU₂R : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hA1R : blockA1 L s x ≤ baum S := sup_le hU₂R (hUx.trans inf_le_left)
  have hA1P : blockA1 L s x ≤ P' := hA1R.trans ((le_inf hRT hRN).trans hcs'.sylow.le)
  have hA1Q : blockA1 L s x ≤ pCoreOf 2 P' := le_pCoreOf_of_normalizes hA1P hP'H hA12
  have hA1eq : blockA1 L s x = blockU L' ⊔ blockU2 L' s' :=
    (Subgroup.eq_of_le_of_card_ge hA1Q (by rw [hQ16, hA1card])).trans hQeq.symm
  exact ⟨L', conjR L' s', blockU L', blockU2 L' s', s', hA4, hA4s, hc', hA1eq.symm,
    (inf_le_left : T ⊓ normalizer (blockA1 L s x : Set G) ≤ T) hcfg'.s_mem, rfl⟩

end Reentry

end CFSG.QuasithinUnique.DoubleA3
