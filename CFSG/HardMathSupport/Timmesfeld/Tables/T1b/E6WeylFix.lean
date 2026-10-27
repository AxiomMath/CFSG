
module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylFixBase

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OutStep
public import Certificates.Certificate13603

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding.R3 CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.SporadicRank CFSG.SectionRank
open scoped Matrix Pointwise

theorem e6SylCheck_true : e6SylCheck () = true :=
  Certificates.certificate13603

theorem e6SylFacts : E6SylFacts :=
  e6SylFacts_of_check e6SylCheck_true

section Syl

theorem mul_mem_e6SylMats {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : M ∈ e6SylMats)
    (hN : N ∈ e6SylMats) : M * N ∈ e6SylMats := by
  obtain ⟨A, hA, rfl⟩ := mem_e6SylMats.1 hM
  obtain ⟨B, hB, rfl⟩ := mem_e6SylMats.1 hN
  exact mem_e6SylMats.2 ⟨_, e6SylFacts.mul_mem A hA B hB, toMatL_mmulL 3 6 A B⟩

theorem pow_mem_e6SylMats {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : M ∈ e6SylMats) :
    ∀ k : ℕ, M ^ k ∈ e6SylMats
  | 0 => by rw [pow_zero]; exact one_mem_e6SylMats
  | k + 1 => by rw [pow_succ]; exact mul_mem_e6SylMats (pow_mem_e6SylMats hM k) hM

@[expose] noncomputable def e6Syl : Subgroup (WeylGroup Tag.E6) where
  carrier := {w | e6WeylMat w ∈ e6SylMats}
  mul_mem' {a b} ha hb := by
    have ha' : e6WeylMat a ∈ e6SylMats := ha
    have hb' : e6WeylMat b ∈ e6SylMats := hb
    have h := mul_mem_e6SylMats ha' hb'
    rw [← map_mul] at h
    exact h
  one_mem' := by
    have h := one_mem_e6SylMats
    rw [← map_one e6WeylMat] at h
    exact h
  inv_mem' {w} hw := by
    have hw' : e6WeylMat w ∈ e6SylMats := hw
    have hpos := orderOf_pos w
    have h : w⁻¹ = w ^ (orderOf w - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    have h2 := pow_mem_e6SylMats hw' (orderOf w - 1)
    rw [← map_pow, ← h] at h2
    exact h2

theorem mem_e6Syl {w : WeylGroup Tag.E6} : w ∈ e6Syl ↔ e6WeylMat w ∈ e6SylMats := Iff.rfl

theorem card_e6SylMats : e6SylMats.card = 81 := by
  rw [e6SylMats, List.toFinset_card_of_nodup, List.length_map, e6SylFacts.length]
  refine e6SylFacts.nodup.map_on fun A hA B hB h => ?_
  exact toMatL_inj6 (e6SylL_spec A hA) (e6SylL_spec B hB) h

theorem card_e6Syl : Nat.card e6Syl = 81 := by
  rw [← card_e6SylMats, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨e6WeylMat w, mem_e6Syl.1 w.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (e6WeylMat_injective (congrArg Subtype.val h))
  · rintro ⟨M, hM⟩
    obtain ⟨A, hA, rfl⟩ := mem_e6SylMats.1 hM
    obtain ⟨w, hw⟩ := mem_mrange_of_mem_e6SylL hA
    exact ⟨⟨w, mem_e6Syl.2 (hw ▸ hM)⟩, Subtype.ext hw⟩

end Syl

theorem wordProd_mem_e6Syl (i : ℕ) (hi : i < 4) :
    (coxeterSystem Tag.E6).wordProd (e6SylWordsF.getD i []) ∈ e6Syl := by
  rw [mem_e6Syl, e6WeylMat_wordProd, e6SylWordsF_getD_val i hi, mem_e6SylMats]
  refine exists_mem_wordsL_eq _ _ ?_
  refine List.mem_map.2 ⟨e6SylWords.getD i [], ?_, rfl⟩
  rw [List.getD_eq_getElem _ _ (by simpa [e6SylWords] using hi)]
  exact List.getElem_mem _

section Main

theorem exists_isO3L {w : WeylGroup Tag.E6} (hw : w ∈ e6Syl) (h1 : w ≠ 1) (h3 : w ^ 3 = 1) :
    ∃ A ∈ e6SylL (), toMatL 3 6 A = e6WeylMat w ∧ isO3L A = true := by
  obtain ⟨A, hA, hAw⟩ := mem_e6SylMats.1 (mem_e6Syl.1 hw)
  refine ⟨A, hA, hAw, ?_⟩
  simp only [isO3L, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · intro hAm
    apply h1
    apply e6WeylMat_injective
    rw [map_one, ← hAw, hAm, toMatL_midL]
  · apply toMatL_inj6 (mmulL_spec _ _) midL_spec
    rw [toMatL_mmulL, toMatL_mmulL, hAw, ← map_mul, ← map_mul, toMatL_midL, ← pow_three', h3,
      map_one]

theorem card_fixMat6_le_81 {w : WeylGroup Tag.E6} (hw : w ∈ e6Syl) (h1 : w ≠ 1)
    (h3 : w ^ 3 = 1) : Nat.card (fixMat6 (e6WeylMat w)) ≤ 81 := by
  obtain ⟨A, hA, hAw, hO⟩ := exists_isO3L hw h1 h3
  rw [← hAw]
  exact (card_fixMat6_le A).trans (e6SylFacts.nfix_le A hA hO)

theorem card_e6Fix_mul_card_le_of_le {F : Subgroup (WeylGroup Tag.E6)} (hF : IsElemAbelian 3 F)
    (hFP : F ≤ e6Syl) : Nat.card (e6Fix F) * Nat.card F ≤ 3 ^ 6 := by
  classical
  have : Fintype F := Fintype.ofFinite _
  obtain ⟨k, hk⟩ := exists_card_pow_of_isElemAbelian hF
  have hdvd : 3 ^ k ∣ 3 ^ 4 := by
    rw [← hk]
    have := Subgroup.card_dvd_of_le hFP
    rwa [card_e6Syl] at this
  have hk4 : k ≤ 4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hfixle : ∀ w ∈ F, Nat.card (e6Fix F) ≤ Nat.card (fixMat6 (e6WeylMat w)) := fun w hw =>
    Nat.card_mono (Set.toFinite _) fun v hv => hv w hw
  have hnt : 1 ≤ k → ∃ w ∈ F, w ≠ 1 := by
    intro hk1
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
    rw [hbot, Subgroup.card_bot] at hk
    have : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  rw [hk]
  interval_cases k
  · simpa using card_le_729 (e6Fix F)
  · obtain ⟨w, hw, h1⟩ := hnt (by norm_num)
    have := (hfixle w hw).trans (card_fixMat6_le_81 (hFP hw) h1 (hF.2 w hw))
    calc _ ≤ 81 * 3 ^ 1 := Nat.mul_le_mul_right _ this
      _ ≤ 3 ^ 6 := by norm_num
  · obtain ⟨w, hw, h1⟩ := hnt (by norm_num)
    have := (hfixle w hw).trans (card_fixMat6_le_81 (hFP hw) h1 (hF.2 w hw))
    calc _ ≤ 81 * 3 ^ 2 := Nat.mul_le_mul_right _ this
      _ = 3 ^ 6 := by norm_num
  · by_cases hex : ∃ w ∈ F, w ≠ 1 ∧ Nat.card (fixMat6 (e6WeylMat w)) ≤ 27
    · obtain ⟨w, hw, -, h27⟩ := hex
      calc _ ≤ 27 * 3 ^ 3 := Nat.mul_le_mul_right _ ((hfixle w hw).trans h27)
        _ = 3 ^ 6 := by norm_num
    · exfalso
      push Not at hex
      have hT : ((((e6SylL ()).filter isO3L).filter fun A => decide (27 < nfix6 A)).toFinset).card
          ≤ 25 := (List.toFinset_card_le _).trans e6SylFacts.count
      have hch : ∀ w : F, ∃ A ∈ e6SylL (), toMatL 3 6 A = e6WeylMat w := fun w =>
        mem_e6SylMats.1 (mem_e6Syl.1 (hFP w.2))
      choose g hg hgw using hch
      have hmaps : ∀ w ∈ (Finset.univ.filter fun w : F => w ≠ 1),
          g w ∈ (((e6SylL ()).filter isO3L).filter fun A => decide (27 < nfix6 A)).toFinset := by
        intro w hw
        have hw1 : (w : WeylGroup Tag.E6) ≠ 1 := fun h =>
          (Finset.mem_filter.1 hw).2 (Subtype.ext h)
        obtain ⟨A, hA, hAw, hO⟩ := exists_isO3L (hFP w.2) hw1 (hF.2 w w.2)
        have hgA : g w = A :=
          toMatL_inj6 (e6SylL_spec _ (hg w)) (e6SylL_spec _ hA) (by rw [hgw, hAw])
        rw [hgA]
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        refine ⟨⟨hA, hO⟩, ?_⟩
        have h1 := hex w w.2 hw1
        have h2 := card_fixMat6_le A
        rw [hAw] at h2
        omega
      have hinj : Set.InjOn g (Finset.univ.filter fun w : F => w ≠ 1) := by
        intro a _ b _ hab
        apply Subtype.ext
        apply e6WeylMat_injective
        rw [← hgw a, ← hgw b, hab]
      have hcard := Finset.card_le_card_of_injOn g hmaps hinj
      have hcF : (Finset.univ.filter fun w : F => w ≠ 1).card = 26 := by
        rw [Finset.filter_ne' Finset.univ 1, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ← Nat.card_eq_fintype_card, hk]
        norm_num
      omega
  · exfalso
    have hFeq : F = e6Syl :=
      Subgroup.eq_of_le_of_card_ge hFP (by rw [card_e6Syl, hk]; norm_num)
    have ht := wordProd_mem_e6Syl 0 (by norm_num)
    have hc := wordProd_mem_e6Syl 1 (by norm_num)
    rw [← hFeq] at ht hc
    have hcomm := congrArg Subtype.val (hF.1.is_comm.comm ⟨_, ht⟩ ⟨_, hc⟩)
    simp only [Subgroup.coe_mul] at hcomm
    have hM := congrArg e6WeylMat hcomm
    rw [map_mul, map_mul, e6WeylMat_wordProd, e6WeylMat_wordProd, e6SylWordsF_getD_val 0
      (by norm_num), e6SylWordsF_getD_val 1 (by norm_num), ← toMatL_mmulL, ← toMatL_mmulL] at hM
    exact e6SylFacts.noncomm (toMatL_inj6 (mmulL_spec _ _) (mmulL_spec _ _) hM)

end Main

theorem card_e6Fix_mul_card_le
    (F : Subgroup (WeylGroup Tag.E6)) (hF : IsElemAbelian 3 F) :
    Nat.card (e6Fix F) * Nat.card F ≤ 3 ^ 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 F := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hF.2 g g.2)⟩
  obtain ⟨Q, hFQ⟩ := hp.exists_le_sylow
  let P : Sylow 3 (WeylGroup Tag.E6) := Sylow.ofCard e6Syl
    (by rw [card_e6Syl, card_weylGroup_E6', factorization_51840]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) Q P
  have hle : F.map (MulAut.conj g).toMonoidHom ≤ e6Syl := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj g) • x ∈ (MulAut.conj g) • (Q : Subgroup (WeylGroup Tag.E6)) :=
      Subgroup.smul_mem_pointwise_smul x _ _ (hFQ hx)
    rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_ofCard] at h1
    exact h1
  have h := card_e6Fix_mul_card_le_of_le (isElemAbelian_map hF _) hle
  rwa [card_e6Fix_map_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective] at h

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
