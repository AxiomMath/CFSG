module

public import CFSG.GH74.GLS.C3.Layer1.Th2Defs

import CFSG.GH74.GLS.NT44.ConjugateClosure
import CFSG.GH74.GLS.NT44.FourGroupStrongClosure
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.TwoThin.Equivariance

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

theorem low_rank_conjugate_closure_actor_of_noncentral_involution
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {P T W J : Subgroup G} {x u : G}
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hx2 : orderOf x = 2)
    (hxT : x ∈ T)
    (hTC : T ≤ Subgroup.centralizer ({x} : Set G))
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (CFSG.GH74.GLS.zStar P))
    (hWT : W ≤ T)
    (hJP : J ≤ P)
    (hZW : Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} ≤ W)
    (hWrank : CFSG.pRank 2 ↥W ≤ 2)
    (huT : u ∈ T)
    (huJ : u ∈ J)
    (hu2 : orderOf u = 2)
    (huZ : u ∉ CFSG.GH74.GLS.zStar J) :
    let Z : Subgroup G := Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}
    let A : Subgroup G := Z ⊔ Subgroup.zpowers u
    Z = CFSG.GH74.GLS.omega1 W ∧
      Nat.card ↥Z = 4 ∧
      (∀ z ∈ Z, z ≠ 1 → IsConj x z) ∧
      (∀ z ∈ Z, ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ Z) ∧
      u ∉ W ∧
      A ≤ T ⊓ P ∧
      CFSG.GH74.GLS.IsE 3 ⊤ A ∧
      Nat.card ↥A = 8 ∧
      A ⊓ W = Z ∧
      A ≤ Subgroup.centralizer (W : Set G) := by
  classical
  let Z : Subgroup G := Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}
  let A : Subgroup G := Z ⊔ Subgroup.zpowers u
  change
    Z = CFSG.GH74.GLS.omega1 W ∧
      Nat.card ↥Z = 4 ∧
      (∀ z ∈ Z, z ≠ 1 → IsConj x z) ∧
      (∀ z ∈ Z, ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ Z) ∧
      u ∉ W ∧
      A ≤ T ⊓ P ∧
      CFSG.GH74.GLS.IsE 3 ⊤ A ∧
      Nat.card ↥A = 8 ∧
      A ⊓ W = Z ∧
      A ≤ Subgroup.centralizer (W : Set G)

  have hWleZstar : W ≤ CFSG.GH74.GLS.zStar P := hW.le
  have hWleP : W ≤ P := hWleZstar.trans inf_le_left
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have haT : a ∈ T := hWT ha
    have hbT : b ∈ T := hWT hb
    have haP : a ∈ P := hWleP ha
    have hbZP : b ∈ CFSG.GH74.GLS.zStar P := hWleZstar hb
    have hbCS : b ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.cSec P :=
      (Subgroup.mem_inf.mp hbZP).2
    exact CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec (T := T) (K := P)
      hT.isPGroup haT hbT haP hbCS
  have hTinfPcommW : ∀ t ∈ T ⊓ P, ∀ w ∈ W, t * w = w * t := by
    intro t ht w hw
    have htT : t ∈ T := ht.1
    have htP : t ∈ P := ht.2
    have hwT : w ∈ T := hWT hw
    have hwZP : w ∈ CFSG.GH74.GLS.zStar P := hWleZstar hw
    have hwCS : w ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.cSec P :=
      (Subgroup.mem_inf.mp hwZP).2
    exact CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec (T := T) (K := P)
      hT.isPGroup htT hwT htP hwCS

  have hB : Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} ≤
      T ⊓ CFSG.GH74.GLS.zStar P := by
    intro a ha
    have haW : a ∈ W := hZW ha
    exact ⟨hWT haW, hWleZstar haW⟩

  have hZdata :=
    CFSG.GH74.GLS.NT44.elementary_rank_conjugate_closure_of_le_zStar
      (P := P) (T := T) (x := x) hnonab hT hx2 hB
  have hZ_elem : CFSG.IsElementaryAbelian 2 ↥Z := hZdata.1
  have hZrank2 : 2 ≤ CFSG.pRank 2 ↥Z := hZdata.2
  have hZrank : CFSG.pRank 2 ↥Z = 2 :=
    le_antisymm
      ((CFSG.GH74.GLS.C3.Layer1.Back.pRank_mono' hZW).trans hWrank) hZrank2
  have hZcard : Nat.card ↥Z = 4 := by
    rw [CFSG.GH74.GLS.C3.Layer1.Back.card_eq_two_pow_pRank hZ_elem, hZrank]
    norm_num

  let O : Subgroup G := CFSG.GH74.GLS.omega1 W
  have hOW : O ≤ W := by
    intro y hy
    change y ∈ Subgroup.closure {a : G | a ∈ W ∧ a * a = 1} at hy
    exact (Subgroup.closure_le W).mpr (fun z hz => hz.1) hy
  have hZO : Z ≤ O := by
    intro z hz
    change z ∈ Subgroup.closure {a : G | a ∈ W ∧ a * a = 1}
    exact Subgroup.subset_closure
      ⟨hZW hz, by
        have hzsq := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz
        simpa [pow_two] using hzsq⟩
  have hOcomm : IsMulCommutative ↥O := by
    change IsMulCommutative ↥(Subgroup.closure {a : G | a ∈ W ∧ a * a = 1})
    exact Subgroup.isMulCommutative_closure
      (fun a ha b hb _ => hWcomm a ha.1 b hb.1)
  have hOexp : Monoid.exponent ↥O ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro z
    apply Subtype.ext
    have hzO : (z : G) ∈ Subgroup.closure {a : G | a ∈ W ∧ a * a = 1} := z.2
    show (z : G) ^ 2 = 1
    refine Subgroup.closure_induction (k := {a : G | a ∈ W ∧ a * a = 1})
      (p := fun a _ => a ^ 2 = 1) (x := (z : G)) ?_ ?_ ?_ ?_ hzO
    · intro a ha
      simpa [pow_two] using ha.2
    · simp
    · intro a b _ha _hb ha2 hb2
      have hcomm_ab : a * b = b * a :=
        congrArg Subtype.val
          ((isMulCommutative_iff.mp hOcomm) (⟨a, _ha⟩ : O) (⟨b, _hb⟩ : O))
      calc
        (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
          rw [pow_two, pow_two, pow_two]
          calc
            (a * b) * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hcomm_ab]
            _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, mul_one]
    · intro a _ ha2
      rw [inv_pow, ha2, inv_one]
  have hOelem : CFSG.IsElementaryAbelian 2 ↥O :=
    { toIsMulCommutative := hOcomm, exponent_dvd_p := hOexp }
  have hOrank_le : CFSG.pRank 2 ↥O ≤ 2 :=
    (CFSG.GH74.GLS.C3.Layer1.Back.pRank_mono' hOW).trans hWrank
  have hOrank_ge : 2 ≤ CFSG.pRank 2 ↥O :=
    hZrank2.trans (CFSG.GH74.GLS.C3.Layer1.Back.pRank_mono' hZO)
  have hOrank : CFSG.pRank 2 ↥O = 2 := le_antisymm hOrank_le hOrank_ge
  have hOcard : Nat.card ↥O = 4 := by
    rw [CFSG.GH74.GLS.C3.Layer1.Back.card_eq_two_pow_pRank hOelem, hOrank]
    norm_num
  have hZeqO : Z = O :=
    Subgroup.eq_of_le_of_card_ge hZO (by rw [hOcard, hZcard])

  have hxcent : ∀ t ∈ T, t * x = x * t := by
    intro t ht
    have h := (Subgroup.mem_centralizer_iff.mp (hTC ht)) x (Set.mem_singleton x)
    exact h.symm
  have hfour :=
    CFSG.GH74.GLS.NT44.conjugate_closure_isConj_and_stronglyClosed_of_card_four
      (T := T) (x := x) hT hx2 hxT hxcent (by simpa [Z] using hZcard)

  have hJzstar : J ⊓ CFSG.GH74.GLS.zStar P ≤ CFSG.GH74.GLS.zStar J := by
    intro c hc
    obtain ⟨hcJ, hcZP⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨hcP, hcCS⟩ := Subgroup.mem_inf.mp hcZP
    refine Subgroup.mem_inf.mpr ⟨hcJ, ?_⟩
    refine ⟨Subgroup.le_normalizer hcJ,
      CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hcJ), ?_⟩
    intro j hj
    have hcommJ : ⁅j, c⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hj hcJ) (J.inv_mem hj)) (J.inv_mem hcJ)
    have hcommP : ⁅j, c⁆ ∈ CFSG.GH74.GLS.pPrimeCoreOf 2 P := hcCS.2.2 j (hJP hj)
    exact CFSG.GH74.GLS.Bg.Pu5.inf_pPrimeCoreOf_le hJP ⟨hcommJ, hcommP⟩

  have huP : u ∈ P := hJP huJ
  have huW : u ∉ W := by
    intro huW
    exact huZ (hJzstar (Subgroup.mem_inf.mpr ⟨huJ, hWleZstar huW⟩))
  have huCentW : u ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwT : w ∈ T := hWT hw
    have hwZP : w ∈ CFSG.GH74.GLS.zStar P := hWleZstar hw
    have hwP : w ∈ P := (Subgroup.mem_inf.mp hwZP).1
    have hwCS : w ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.cSec P :=
      (Subgroup.mem_inf.mp hwZP).2
    exact (CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec (T := T) (K := P)
      hT.isPGroup huT hwT huP hwCS).symm
  have hzuCentW : Subgroup.zpowers u ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.zpowers_le.mpr huCentW
  have hZCentW : Z ≤ Subgroup.centralizer (W : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hTinfPcommW z ⟨hWT (hZW hz), hWleP (hZW hz)⟩ w hw).symm
  have huCentZ : u ∈ Subgroup.centralizer (Z : Set G) :=
    Subgroup.centralizer_le hZW huCentW
  have hzuCentZ : Subgroup.zpowers u ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.zpowers_le.mpr huCentZ

  have hu_sq : u ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu2] at h
  have hzu_elem : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers u) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hu_sq
  have hAelem : CFSG.IsElementaryAbelian 2 ↥A := by
    have : CFSG.IsElementaryAbelian 2 ↥Z := hZ_elem
    have : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers u) := hzu_elem
    simpa only [A] using
      (CFSG.IsElementaryAbelian.sup_of_le_centralizer (p := 2)
        (E := Z) (C := Subgroup.zpowers u) hzuCentZ)
  have hzpow : ∀ k : ℤ, u ^ k = 1 ∨ u ^ k = u := by
    intro k
    rw [← zpow_mod_orderOf, hu2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      simp [hk]
    · right
      simp [hk]
  have hdisj : Disjoint Z (Subgroup.zpowers u) := by
    rw [disjoint_iff]
    apply (Subgroup.eq_bot_iff_forall (Z ⊓ Subgroup.zpowers u)).2
    intro y hy
    obtain ⟨hyZ, hyzu⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyzu
    have hyW : y ∈ W := hZW hyZ
    have hukW : u ^ k ∈ W := by simpa [hk] using hyW
    rcases hzpow k with h1 | hu
    · simpa [hk] using h1
    · exact absurd (by rwa [hu] at hukW) huW
  have hAcard : Nat.card ↥A = 8 := by
    have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Z : Set G) :=
      hzuCentZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
    have hcard : Nat.card ↥A =
        Nat.card ↥Z * Nat.card ↥(Subgroup.zpowers u) := by
      rw [show A = Z ⊔ Subgroup.zpowers u from rfl,
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z (Subgroup.zpowers u) hnorm hdisj]
    rw [hcard, hZcard, Nat.card_zpowers, hu2]
  have hArank : CFSG.pRank 2 ↥A = 3 := by
    have : CFSG.IsElementaryAbelian 2 ↥A := hAelem
    exact CFSG.pRank_eq_of_card_eq_pow (p := 2) (k := 3) one_lt_two
      (by norm_num [hAcard])
  have hA_TP : A ≤ T ⊓ P := by
    rw [show A = Z ⊔ Subgroup.zpowers u from rfl]
    refine sup_le ?_ ?_
    · intro z hz
      exact ⟨hWT (hZW hz), hWleP (hZW hz)⟩
    · intro y hy
      exact ⟨Subgroup.zpowers_le.mpr huT hy, Subgroup.zpowers_le.mpr huP hy⟩
  have hAinfW : A ⊓ W = Z := by
    have hZleAW : Z ≤ A ⊓ W := by
      intro z hz
      exact ⟨Subgroup.mem_sup_left hz, hZW hz⟩
    have hcard_dvd_Z : Nat.card ↥Z ∣ Nat.card ↥(A ⊓ W) :=
      Subgroup.card_dvd_of_le hZleAW
    have hcard_dvd_A : Nat.card ↥(A ⊓ W) ∣ Nat.card ↥A :=
      Subgroup.card_dvd_of_le inf_le_left
    have hcard_ge : 4 ≤ Nat.card ↥(A ⊓ W) := by
      have h := Nat.le_of_dvd (Nat.card_pos) hcard_dvd_Z
      rwa [hZcard] at h
    have hcard_le : Nat.card ↥(A ⊓ W) ≤ 8 := by
      have h := Nat.le_of_dvd (Nat.card_pos) hcard_dvd_A
      rwa [hAcard] at h
    have hcard_ne : Nat.card ↥(A ⊓ W) ≠ 8 := by
      intro h8
      have heq : A ⊓ W = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hAcard])
      have hA_le_W : A ≤ W := by
        rw [← heq]
        exact inf_le_right
      exact huW (hA_le_W (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))
    have hcard : Nat.card ↥(A ⊓ W) = 4 := by
      have hdvd : Nat.card ↥(A ⊓ W) ∣ 8 := by
        simpa [hAcard] using hcard_dvd_A
      interval_cases h : Nat.card ↥(A ⊓ W) <;> simp_all
    exact (Subgroup.eq_of_le_of_card_ge (H := Z) (K := A ⊓ W) hZleAW
      (by rw [hcard, hZcard])).symm

  have hAcentW : A ≤ Subgroup.centralizer (W : Set G) := by
    rw [show A = Z ⊔ Subgroup.zpowers u from rfl]
    exact sup_le hZCentW hzuCentW

  exact ⟨by simpa [O] using hZeqO, hZcard, hfour.1, hfour.2, huW, hA_TP,
    ⟨le_top, hAelem, le_of_eq hArank.symm⟩, hAcard, hAinfW, hAcentW⟩

end CFSG.GH74.GLS.NT44

end
