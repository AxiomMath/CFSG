module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEL
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Full

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoClassical
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}

namespace NormPair

variable (np : NormPair A R T g n) (hn : 8 ≤ n) (hc : Sec3 A R T g)
include hc

theorem standard_LE_of_lemma37
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34) :
    standardComponentIsStandard
      (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))) := by
  rcases lemma37_of_le h4 h32 h34 hc.hyp hc.sylowR (W := zpowers (np.wE hn))
      (L := np.LE) (zpowers_le.mpr (np.wE_mem hn)) (np.isQuasisimple_LE hn)
      (le_inf np.LE_le_A (np.LE_le_centralizer hn)) (np.normalizer_inf_le_normalizer_LE hn)
      (np.isSylowOf_R_LE hn hc) with h | ⟨c, hcW, hcL, -, hncl, hRc, k, -, hk, ⟨e⟩⟩
  · exact h
  · exfalso
    set C := centralizer (zpowers (np.wE hn) : Set G) with hCdef
    set B := rightConjugate A g with hBdef
    set N := np.LE ⊔ Lemma34.conj np.LE c with hNdef
    have hLC : np.LE ≤ C := np.LE_le_centralizer hn
    have hNC : N ≤ C := sup_le hLC (conj_le_of_mem hLC hcW)
    have hBC : B ≤ C := np.B_le_centralizer_W hn hc
    have hBN : ∀ b ∈ B, ∀ y ∈ N, b * y * b⁻¹ ∈ N := by
      intro b hb y hy
      have hy' : (⟨y, hNC hy⟩ : C) ∈
          normalClosure ((np.LE.subgroupOf C : Subgroup C) : Set C) := by
        rw [hncl]
        exact hy
      have h1 := (normalClosure_normal (s := ((np.LE.subgroupOf C : Subgroup C) : Set C))).conj_mem
        _ hy' ⟨b, hBC hb⟩
      rw [hncl] at h1
      exact h1
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have : IsSimpleGroup B := np.equivB.isSimpleGroup
    have hBleN : B ≤ N := by
      have hHn : (N.subgroupOf B).Normal :=
        ⟨fun x hx b => by
          rw [mem_subgroupOf] at hx ⊢
          exact hBN b b.2 x hx⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf B) with h | h
      · exfalso
        obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.R_ne_bot
        have hrH : (⟨r, np.le_B hr⟩ : B) ∈ N.subgroupOf B :=
          mem_subgroupOf.mpr (mem_sup_right (hRc hr))
        rw [h, mem_bot] at hrH
        exact hr1 (Subtype.ext (show r = 1 from congrArg Subtype.val hrH))
      · intro b hb
        have hb' : (⟨b, hb⟩ : B) ∈ N.subgroupOf B := h ▸ mem_top _
        exact mem_subgroupOf.mp hb'
    rw [np.card_R (by omega)] at hk
    have hk2 : k = 2 := Nat.pow_right_injective (le_refl 2) (show 2 ^ k = 2 ^ 2 from hk)
    subst hk2
    have hL : Nat.card np.LE = 60 := by
      rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hNcard : Nat.card N ≤ 3600 := by
      have hle : Lemma34.conj np.LE c ≤ normalizer (np.LE : Set G) :=
        hcL.trans (Subgroup.centralizer_le_normalizer _)
      set f : np.LE × Lemma34.conj np.LE c → N := fun p =>
        ⟨(p.1 : G) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ with hf
      have hfs : Function.Surjective f := by
        rintro ⟨y, hy⟩
        have hy' : y ∈ ((np.LE : Set G) * (Lemma34.conj np.LE c : Set G)) := by
          rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
          exact hy
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hy'
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
      have h1 := Nat.card_le_card_of_surjective f hfs
      rw [Nat.card_prod, Lemma34.card_conj, hL] at h1
      exact h1
    have hBcard : 20160 ≤ Nat.card B := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr np.equivB.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      have h8 : (8 : ℕ).factorial ≤ n.factorial := Nat.factorial_le hn
      have h8' : (8 : ℕ).factorial = 40320 := rfl
      omega
    have := Subgroup.card_le_of_le hBleN
    omega

end NormPair

end CFSG.ComponentClassification.RankTwoAlt
