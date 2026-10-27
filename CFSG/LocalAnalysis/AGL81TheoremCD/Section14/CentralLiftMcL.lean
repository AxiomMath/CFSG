module

public import CFSG.Foundations.Basic

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftMcLAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftMcLLocal
import CFSG.GroupTheory.InnerCentralizerProjection
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.ComponentClassification

private theorem pow_dvd_of_pow_succ_dvd_mul {a b k : ℕ} (h : 3 ^ (k + 1) ∣ a * b) (hb : b ∣ 3) :
    3 ^ k ∣ a := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hb with rfl | rfl
  · exact (pow_dvd_pow 3 k.le_succ).trans (by simpa using h)
  · exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) (by rwa [pow_succ] at h)

private theorem onQuotient_pow_three {K : Type} [Group K] (Z : Subgroup K) [Z.Normal]
    (c : MulAut K) (hinv : Z.map c.toMonoidHom = Z) (hc3 : c ^ 3 = 1) :
    CatalogueBFixedCentralQuotient.onQuotient Z c hinv ^ 3 = 1 := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
  have hccc : c (c (c x)) = x := by
    have h := congrArg (fun f : MulAut K => f x) hc3
    simpa [pow_three, MulAut.mul_apply] using h
  simp only [pow_three, MulAut.mul_apply, MulAut.one_apply]
  rw [CatalogueBFixedCentralQuotient.onQuotient_mk,
    CatalogueBFixedCentralQuotient.onQuotient_mk,
    CatalogueBFixedCentralQuotient.onQuotient_mk, hccc]

private theorem onQuotient_ne_one_of_not_mem_centralizer {X : Type} [Group X]
    {K : Subgroup X} (hK : CFSG.IsQuasisimple ↥K) {b : X}
    (hbN : b ∈ Subgroup.normalizer (K : Set X))
    (hbC : b ∉ Subgroup.centralizer (K : Set X))
    (c : MulAut ↥K) (hc : c = K.normalizerMonoidHom ⟨b, hbN⟩)
    (hinv : (Subgroup.center ↥K).map c.toMonoidHom = Subgroup.center ↥K) :
    CatalogueBFixedCentralQuotient.onQuotient (Subgroup.center ↥K) c hinv ≠ 1 := by
  intro hβ
  apply hbC
  refine CFSG.mem_centralizer_of_commutator_mem_center hK.1 hbN ?_
  intro j hj
  have hq : (QuotientGroup.mk' (Subgroup.center ↥K)) (c ⟨j, hj⟩) =
      (QuotientGroup.mk' (Subgroup.center ↥K)) ⟨j, hj⟩ := by
    have h := congrArg (fun f : MulAut (↥K ⧸ Subgroup.center ↥K) =>
      f ((QuotientGroup.mk' (Subgroup.center ↥K)) ⟨j, hj⟩)) hβ
    rw [CatalogueBFixedCentralQuotient.onQuotient_mk, MulAut.one_apply] at h
    exact h
  have hcz : c ⟨j, hj⟩ * ⟨j, hj⟩⁻¹ ∈ Subgroup.center ↥K := by
    rw [← div_eq_mul_inv]
    exact QuotientGroup.eq_iff_div_mem.mp hq
  exact Subgroup.mem_map_of_mem K.subtype (by
    simpa [hc, Subgroup.normalizerMonoidHom_apply_apply_coe] using hcz)

private theorem dvd_card_centralizer_of_quotient_fixed {K : Type} [Group K] [Finite K]
    (Z : Subgroup K) [Z.Normal] (c : MulAut K) (hinv : Z.map c.toMonoidHom = Z)
    (hcentral : Z ≤ Subgroup.center K) (hZ : Nat.card Z = 3)
    (hfix : 3 ^ 5 ∣ Nat.card
      (FixedCommutingProduct.fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z c hinv))) :
    3 ^ 5 ∣ Nat.card (FixedCommutingProduct.fixedSubgroup c) := by
  let P : Subgroup K := CatalogueBFixedCentralQuotient.fixedPreimage Z c hinv
  let proj := CatalogueBFixedCentralQuotient.preimageProjection Z c hinv
  have hproj : Function.Surjective proj :=
    CatalogueBFixedCentralQuotient.preimageProjection_surjective Z c hinv
  have hZP : Z ≤ P := CatalogueBFixedCentralQuotient.central_le_fixedPreimage Z c hinv
  have hZsub : Nat.card (Z.subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ]
  have hker : proj.ker = Z.subgroupOf P := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      exact (QuotientGroup.eq_one_iff y.val).mp (congrArg Subtype.val hy)
    · intro hy
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff y.val).mpr hy
  have hcardP : Nat.card P = 3 * Nat.card (FixedCommutingProduct.fixedSubgroup
      (CatalogueBFixedCentralQuotient.onQuotient Z c hinv)) := by
    have h := Subgroup.card_ker_mul_card_of_surjective hproj
    rw [hker, hZsub] at h
    exact h.symm
  have h6P : 3 ^ 6 ∣ Nat.card P := by
    rw [hcardP, show (3 : ℕ) ^ 6 = 3 * 3 ^ 5 by norm_num]
    exact Nat.mul_dvd_mul_left 3 hfix
  let D : P →* Z := CatalogueBFixedCentralQuotient.displacement Z c hinv hcentral
  have hkerD : D.ker = (FixedCommutingProduct.fixedSubgroup c).subgroupOf P :=
    CatalogueBFixedCentralQuotient.displacement_kernel Z c hinv hcentral
  have hcardD : Nat.card D.ker * Nat.card D.range = Nat.card P :=
    Subgroup.card_ker_mul_card_range D
  have hrange : Nat.card D.range ∣ 3 := by
    have h := Subgroup.card_subgroup_dvd_card D.range
    rwa [hZ] at h
  have hker5 : 3 ^ 5 ∣ Nat.card D.ker :=
    pow_dvd_of_pow_succ_dvd_mul (k := 5) (by rw [hcardD]; exact h6P) hrange
  rw [hkerD] at hker5
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (CatalogueBFixedCentralQuotient.fixed_le_fixedPreimage Z c hinv)).toEquiv] at hker5

private theorem pow_four_dvd_card_map {K : Type} [Group K] [Finite K]
    (Z : Subgroup K) [Z.Normal] (c : MulAut K) (hZ : Nat.card Z = 3)
    (h5 : 3 ^ 5 ∣ Nat.card (FixedCommutingProduct.fixedSubgroup c)) :
    3 ^ 4 ∣ Nat.card ((FixedCommutingProduct.fixedSubgroup c).map (QuotientGroup.mk' Z)) := by
  let C := FixedCommutingProduct.fixedSubgroup c
  let φ : C →* (K ⧸ Z) := (QuotientGroup.mk' Z).comp C.subtype
  have hrange : φ.range = C.map (QuotientGroup.mk' Z) := by
    rw [show φ = (QuotientGroup.mk' Z).comp C.subtype from rfl, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hker : φ.ker = (Z ⊓ C).subgroupOf C := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hy
      exact ⟨(QuotientGroup.eq_one_iff y.val).mp hy, y.2⟩
    · rintro ⟨hz, -⟩
      exact (QuotientGroup.eq_one_iff y.val).mpr hz
  have hkerdvd : Nat.card φ.ker ∣ 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Z ⊓ C ≤ C)).toEquiv,
      ← hZ]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcardφ : Nat.card φ.ker * Nat.card φ.range = Nat.card C :=
    Subgroup.card_ker_mul_card_range φ
  rw [← hrange]
  exact pow_dvd_of_pow_succ_dvd_mul (k := 4) (by rw [mul_comm, hcardφ]; exact h5) hkerdvd

private theorem fixedSubgroup_normalizerMonoidHom {X : Type} [Group X]
    (K : Subgroup X) {b : X} (hbN : b ∈ Subgroup.normalizer (K : Set X)) :
    FixedCommutingProduct.fixedSubgroup (K.normalizerMonoidHom ⟨b, hbN⟩) =
      (K ⊓ Subgroup.centralizer ({b} : Set X)).subgroupOf K := by
  ext y
  rw [show y ∈ FixedCommutingProduct.fixedSubgroup (K.normalizerMonoidHom ⟨b, hbN⟩) ↔
      (K.normalizerMonoidHom ⟨b, hbN⟩) y = y by
    simp [FixedCommutingProduct.fixedSubgroup]]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hcy : (K.normalizerMonoidHom ⟨b, hbN⟩) y = y ↔ b * (y : X) * b⁻¹ = (y : X) := by
    constructor
    · intro h
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  rw [hcy, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    exact ⟨y.2, h.symm⟩
  · rintro ⟨-, h⟩
    exact h.symm

private theorem fixedSubgroup_conj {L : Type} [Group L] (x : L) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set L) := by
  ext y
  rw [show y ∈ FixedCommutingProduct.fixedSubgroup (MulAut.conj x) ↔ MulAut.conj x y = y by
    simp [FixedCommutingProduct.fixedSubgroup]]
  rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

section Certificates


private theorem eq_normalizer_of_le {L : Type} [Group L] [Finite L]
    (e : L ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) (S : Sylow 5 L)
    {H : Subgroup L} (hH : H ≠ ⊤)
    (hS : Subgroup.normalizer ((S : Subgroup L) : Set L) ≤ H) :
    H = Subgroup.normalizer ((S : Subgroup L) : Set L) := by
  obtain ⟨hcoat, -⟩ := isCoatom_normalizer_sylow_five_mcl e S
  rcases eq_or_lt_of_le hS with h | h
  · exact h.symm
  · exact absurd (hcoat.2 H h) hH

theorem not_le_of_mcl {X : Type} [Group X] [Finite X] (K : Subgroup X)
    (hK : CFSG.IsQuasisimple ↥K)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group)
    (hZ : Nat.card (Subgroup.center ↥K) = 3)
    {b : X} (hbN : b ∈ Subgroup.normalizer (K : Set X)) (hb : orderOf b = 3)
    (hbC : b ∉ Subgroup.centralizer (K : Set X))
    {H : Subgroup (↥K ⧸ Subgroup.center ↥K)} (hH : H ≠ ⊤)
    (hS : ∃ S : Sylow 5 (↥K ⧸ Subgroup.center ↥K),
      Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _) ≤ H) :
    ¬ ((K ⊓ Subgroup.centralizer ({b} : Set X)).subgroupOf K).map
        (QuotientGroup.mk' (Subgroup.center ↥K)) ≤ H := by
  classical
  intro hle
  let Z : Subgroup ↥K := Subgroup.center ↥K
  haveI hZnormal : Z.Normal := Subgroup.instNormalCenter
  have hcardZ : Nat.card Z = 3 := hZ
  let c : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbN⟩
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hc3 : c ^ 3 = 1 := by
    have h3 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb3)
    change (K.normalizerMonoidHom ⟨b, hbN⟩) ^ 3 = 1
    rw [← map_pow, h3, map_one]
  have hinv : Z.map c.toMonoidHom = Z := by
    have h := Subgroup.characteristic_iff_map_eq.mp Subgroup.centerCharacteristic c
    simpa [Z] using h
  let β : MulAut (↥K ⧸ Z) := CatalogueBFixedCentralQuotient.onQuotient Z c hinv
  have hβ3 : β ^ 3 = 1 := onQuotient_pow_three Z c hinv hc3
  have hβ1 : β ≠ 1 :=
    onQuotient_ne_one_of_not_mem_centralizer hK hbN hbC c rfl hinv
  obtain ⟨x, hxconj, -, hxdiv⟩ := exists_conj_of_pow_three_mcl e hβ3 hβ1
  have hfixedβ : FixedCommutingProduct.fixedSubgroup β =
      Subgroup.centralizer ({x} : Set (↥K ⧸ Z)) := by
    rw [hxconj, fixedSubgroup_conj]
  have hC5 : 3 ^ 5 ∣ Nat.card (FixedCommutingProduct.fixedSubgroup c) := by
    refine dvd_card_centralizer_of_quotient_fixed Z c hinv le_rfl hcardZ ?_
    rwa [hfixedβ]
  have hCeq := fixedSubgroup_normalizerMonoidHom K hbN
  have h4 : 3 ^ 4 ∣ Nat.card ((FixedCommutingProduct.fixedSubgroup c).map
      (QuotientGroup.mk' Z)) :=
    pow_four_dvd_card_map Z c hcardZ hC5
  obtain ⟨S, hSle⟩ := hS
  have hHN := eq_normalizer_of_le e S hH hSle
  have hcardH : Nat.card H = 3000 := by
    rw [hHN]
    exact (isCoatom_normalizer_sylow_five_mcl e S).2
  have hrangeH : (FixedCommutingProduct.fixedSubgroup c).map (QuotientGroup.mk' Z) ≤ H := by
    rw [hCeq]
    exact hle
  have hdvdH : 3 ^ 4 ∣ 3000 := by
    rw [← hcardH]
    exact h4.trans (Subgroup.card_dvd_of_le hrangeH)
  norm_num at hdvdH

end Certificates

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
