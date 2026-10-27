module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Foundations.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.GroupTheory.ConjNormalFaithful
import CFSG.LocalAnalysis.ComponentClassification.Sol78AltCentralizer
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInner

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree

open Subgroup

variable {X : Type} [Group X] [Finite X]

private lemma card_quotient_pCore_two_of_perm_nine {Hs : Subgroup X}
    (h : Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9))) :
    Nat.card (↥Hs ⧸ CFSG.pCore 2 ↥Hs) = Nat.factorial 9 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]

private lemma index_le_ten_of_perm_nine_quotient {Hs : Subgroup X}
    (hHsQuot : Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9)))
    (hX : Nat.card X ≤ Nat.factorial 10) : Hs.index ≤ 10 := by
  have hcard_quot := card_quotient_pCore_two_of_perm_nine hHsQuot
  have hHs_card : Nat.card ↥Hs =
      Nat.factorial 9 * Nat.card (CFSG.pCore 2 ↥Hs) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Hs), hcard_quot]
  have hHs_ge : Nat.factorial 9 ≤ Nat.card ↥Hs := by
    rw [hHs_card]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have h1 : Hs.index * Nat.factorial 9 ≤ Nat.card X := by
    rw [← Subgroup.index_mul_card Hs]
    exact Nat.mul_le_mul_left _ hHs_ge
  have h9 : Nat.factorial 9 = 362880 := by norm_num
  have h10 : Nat.factorial 10 = 3628800 := by norm_num
  rw [h9] at h1
  rw [h10] at hX
  refine Nat.le_of_mul_le_mul_right (c := 362880) ?_ (by norm_num)
  omega

private lemma card_alternating_ten : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  haveI : Nontrivial (Fin 10) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private lemma card_mulAut_alternating_ten :
    Nat.card (MulAut (alternatingGroup (Fin 10))) = Nat.factorial 10 :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_eq_factorial
    10 (by norm_num) (by norm_num)

private lemma alternating_ten_not_isPGroup_two :
    ¬ IsPGroup 2 (alternatingGroup (Fin 10)) := by
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 10)) := by
    rw [card_alternating_ten]
    norm_num
  rw [hn] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

private lemma subgroupOf_index_le_index {L Hs : Subgroup X} (hL : L.Normal) :
    (Hs.subgroupOf L).index ≤ Hs.index := by
  haveI : L.Normal := hL
  have hsup : Hs.relIndex (L ⊔ Hs) = Hs.relIndex L :=
    CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal L Hs
  have hle : Hs.relIndex (L ⊔ Hs) ≤ Hs.relIndex ⊤ :=
    Subgroup.relIndex_le_of_le_right (H := Hs) (K := L ⊔ Hs) (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  change Hs.relIndex L ≤ Hs.index
  calc Hs.relIndex L = Hs.relIndex (L ⊔ Hs) := hsup.symm
    _ ≤ Hs.relIndex ⊤ := hle
    _ = Hs.index := Subgroup.relIndex_top_right Hs

theorem index_le_nine_of_perm_nine_quotient {T Hs : Subgroup X}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTHs : T ≤ Hs)
    (hHsQuot : Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9)))
    (hX : Nat.card X ≤ Nat.factorial 10) : Hs.index ≤ 9 := by
  have hle : Hs.index ≤ 10 := index_le_ten_of_perm_nine_quotient hHsQuot hX
  have hnot2 : ¬ 2 ∣ Hs.index :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.not_dvd_index_of_isSylowOf_le hTsyl hTHs
  have hmod : Hs.index % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one Hs.index with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hnot2
    · exact h
  omega

theorem false_of_fstar_alternating_ten {L : Subgroup X}
    (hFstar : CFSG.generalizedFitting X = L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* alternatingGroup (Fin 10)) {T Hs : Subgroup X}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTHs : T ≤ Hs)
    (hHsQuot : Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9))) : False := by
  have hLnorm : L.Normal :=
    hFstar ▸ (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  haveI : L.Normal := hLnorm
  have hC : Subgroup.centralizer (L : Set X) ≤ L := by
    simpa [hFstar] using CFSG.centralizer_generalizedFitting_le X
  have hXle : Nat.card X ≤ Nat.card (MulAut ↥L) :=
    Subgroup.card_le_card_mulAut_of_centralizer_le hC hZ
  have hAut : Nat.card (MulAut ↥L) = Nat.factorial 10 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact card_mulAut_alternating_ten
  rw [hAut] at hXle
  have hidx9 : Hs.index ≤ 9 :=
    index_le_nine_of_perm_nine_quotient hTsyl hTHs hHsQuot hXle
  have hrel : (Hs.subgroupOf L).index ≤ 9 :=
    (subgroupOf_index_le_index hLnorm).trans hidx9
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hKtop : Hs.subgroupOf L = ⊤ := by
    by_contra hK
    have h10 := CFSG.ComponentClassification.Sol78.le_index_of_mulEquiv_alternating
      (H := ↥L) (m := 10) (by norm_num) e (K := Hs.subgroupOf L) hK
    omega
  have hLH : L ≤ Hs := Subgroup.subgroupOf_eq_top.mp hKtop
  let R : Subgroup ↥Hs := CFSG.pCore 2 ↥Hs
  haveI hRnorm : R.Normal := CFSG.pCore_normal (G := ↥Hs) (p := 2)
  let q : ↥Hs →* ↥Hs ⧸ R := QuotientGroup.mk' R
  let ι : ↥L →* ↥Hs := Subgroup.inclusion hLH
  obtain ⟨f⟩ := hHsQuot
  let ψ : ↥L →* Equiv.Perm (Fin 9) := f.toMonoidHom.comp (q.comp ι)
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with hker | hker
  · have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
    have hcard_le : Nat.card ↥L ≤ Nat.card (Equiv.Perm (Fin 9)) :=
      Nat.card_le_card_of_injective ψ hinj
    have hLcard : Nat.card ↥L = 1814400 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_alternating_ten
    have h9 : Nat.card (Equiv.Perm (Fin 9)) = 362880 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num
    rw [hLcard, h9] at hcard_le
    omega
  · have hLleR : L ≤ R.map Hs.subtype := by
      intro x hx
      have hmem : (ι ⟨x, hx⟩ : ↥Hs) ∈ R := by
        have hxker : (⟨x, hx⟩ : ↥L) ∈ ψ.ker := by rw [hker]; trivial
        have hψ : ψ ⟨x, hx⟩ = 1 := hxker
        have hq : q (ι ⟨x, hx⟩) = 1 := by
          apply f.injective
          simpa [ψ] using hψ
        exact (QuotientGroup.eq_one_iff (N := R) (ι ⟨x, hx⟩)).mp hq
      exact Subgroup.mem_map.mpr ⟨ι ⟨x, hx⟩, hmem, rfl⟩
    have hLp : IsPGroup 2 L :=
      (CFSG.pCore_isPGroup (G := ↥Hs) (p := 2)).map Hs.subtype |>.to_le hLleR
    exact alternating_ten_not_isPGroup_two (hLp.of_equiv e)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree
