module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS4
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootFive
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseMain

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RestrictedStd.Spor Equiv

section Count

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

omit e in
theorem fixFin_card_add_support_card (σ : Perm (Fin n)) :
    (fixFin σ).card + σ.support.card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => σ i = i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hs : σ.support = Finset.univ.filter (fun i => ¬ σ i = i) := by
    ext i
    simp [Perm.mem_support]
  rw [hs]
  exact h

theorem orderOf_perm_of_involution {y : G} (hy : y ∈ L) (hy2 : orderOf y = 2) :
    orderOf ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]

theorem le_of_fixFin_card_eq_six {y : G} (hy : y ∈ L) (hy2 : orderOf y = 2)
    (h6 : (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card = 6) :
    n = 10 ∨ 14 ≤ n := by
  have h1 := rootSupp_support_card_of_involution (orderOf_perm_of_involution e hy hy2)
    (Perm.mem_alternatingGroup.1 (e ⟨y, hy⟩).2)
  have h2 := fixFin_card_add_support_card
    ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
  omega

end Count

section Three

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem nearGivesRoot_three (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) : NearGivesRoot 3 (· = 12) := by
  intro G _ _ L n Q z h d hQ2 hE hn e ⟨y, hy, hyL, hnear⟩
  have hn12 : n = 12 := hn
  have hf4 : 4 ≤ (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card := by
    rw [← card_fixedPoints_eq]
    exact hnear
  refine nearGives_of_ne_six hlookup hHN hFour h d hQ2 hE e (by omega) (by norm_num)
    (by norm_num) (by omega) hy hf4 ?_
  intro h6
  have := le_of_fixFin_card_eq_six e hyL hy.2.1 h6
  omega

end Three

section Four

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem nearGivesRoot_four (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) : NearGivesRoot 4 (13 ≤ ·) := by
  intro G _ _ L n Q z h d hQ2 hE hn e ⟨y, hy, hyL, hnear⟩
  have hn13 : 13 ≤ n := hn
  have hf4 : 4 ≤ (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card := by
    rw [← card_fixedPoints_eq]
    exact hnear
  by_cases hf6 : (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card = 6
  · have h14 : 14 ≤ n := by
      have := le_of_fixFin_card_eq_six e hyL hy.2.1 hf6
      omega
    obtain ⟨y', hy', hf4', hf6'⟩ := exists_near_ne_six hlookup hHN hFour h d hQ2 hE e h14 hy hf6
    exact nearGives_of_ne_six hlookup hHN hFour h d hQ2 hE e (by omega) (by norm_num)
      (by norm_num) (by omega) hy' hf4' hf6'
  · exact nearGives_of_ne_six hlookup hHN hFour h d hQ2 hE e (by omega) (by norm_num)
      (by norm_num) (by omega) hy hf4 hf6

theorem fusionAll_of_shape_one' (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hn : 12 ≤ n) : FusionAll L z :=
  fusionAll_of_shape_one (nearGivesRoot_four hlookup hHN hFour)
    (nearGivesRoot_three hlookup hHN hFour) h d hQ2 hE hn

end Four

section ByProduct

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem wreath_of_fusionAll (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n)) (hn : 12 ≤ n)
    (hF : FusionAll L z) {S : Finset (Fin n)} (hS : S.card = 3 ∨ S.card = 4)
    (hm : 9 ≤ n - S.card) :
    ∃ ht : z ∈ centralizer (rootGroup (G := G) e S : Set G),
      WreathOutcome (QuotientGroup.mk (⟨z, ht⟩ : ↥(centralizer (rootGroup (G := G) e S : Set G))) :
        Sec G (rootGroup e S)) (secImage (rootGroup e S) (corr (X := G) e (altSub Sᶜ)))
        (n - S.card) := by
  rcases zstar_or_wreath hlookup hHN hFour h d hQ2 hE e hS hm with hz | hW
  swap
  · exact hW
  exfalso
  obtain ⟨b', hb'2, hb'sign, hb'1, hb'S, hb'card⟩ :=
    rootFive_exists_involution_gen (S := S) (by omega)
  have hb'A : b' ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 hb'sign
  set y : G := ((e.symm ⟨b', hb'A⟩ : L) : G) with hy
  have hyL : y ∈ L := (e.symm ⟨b', hb'A⟩).2
  have heb : e ⟨y, hyL⟩ = ⟨b', hb'A⟩ := by
    have : (⟨y, hyL⟩ : L) = e.symm ⟨b', hb'A⟩ := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hb'ord : orderOf b' = 2 := orderOf_eq_prime (by rw [sq]; exact hb'2) hb'1
  have hy2 : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hb'ord
  obtain ⟨g, hg⟩ := hF y hyL hy2
  have hyY : y ∈ FusionSet L z := ⟨hyL, hy2, g, hg⟩
  have hfS : ∀ i ∈ S, ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i := by
    rw [heb]
    exact hb'S
  have hcardF : n - 4 ≤ (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card := by
    rw [heb]
    exact hb'card
  have hid : NormalAltIdent n
      (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card :=
    normalAltIdent_of_five_le (by omega)
  have hfF : (5 ≤ (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ∧
      (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ≠ 6) ∨
      (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card = 4 :=
    Or.inl ⟨by omega, by omega⟩
  obtain ⟨S₁, hS₁c, hS₁⟩ := exists_common_root_of_fix h d hQ2 hE e hyL hy2 hg hfF hid hfS
  have hz₁ : IsZStar (rootGroup e S₁) z :=
    (isZStar_rootGroup_iff h d e hS₁c.symm (by omega)).1 hz
  exact false_of_zstar_common_root h d hQ2 e hn hyY hg hS
    (mem_centralizer_rootGroup_of_fix e hyL hfS) hS₁ hz hz₁

end ByProduct

end CFSG.OddStandard.AltStdSec
