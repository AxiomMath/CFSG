module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End8a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End8b
public import Mathlib.FieldTheory.Finite.GaloisField

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

private noncomputable def slEquivOfRingEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map (e : R →+* S)
  invFun := Matrix.SpecialLinearGroup.map (e.symm : S →+* R)
  left_inv A := by
    apply Subtype.ext
    show (e.symm : S →+* R).mapMatrix ((e : R →+* S).mapMatrix A.val) = A.val
    ext i j
    simp
  right_inv A := by
    apply Subtype.ext
    show (e : R →+* S).mapMatrix ((e.symm : S →+* R).mapMatrix A.val) = A.val
    ext i j
    simp
  map_mul' A B := map_mul _ A B

private theorem oddCore_eq_bot_of_mulEquiv_sl23 {G : Type*} [Group G] [Finite G]
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : CFSG.oddCore G = ⊥ := by
  have hmap_normal : ((CFSG.oddCore G).map e.toMonoidHom).Normal :=
    (CFSG.oddCore_normal G).map e.toMonoidHom e.surjective
  have hmap_odd : Odd (Nat.card ((CFSG.oddCore G).map e.toMonoidHom)) :=
    (CFSG.ABGLocalTools.odd_card_oddCore (H := G)).of_dvd_nat
      (Subgroup.card_map_dvd (H := CFSG.oddCore G) e.toMonoidHom)
  have hle : (CFSG.oddCore G).map e.toMonoidHom ≤
      CFSG.oddCore (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
    CFSG.ABGLocalTools.le_oddCore_of_normal hmap_normal hmap_odd
  rw [oddCore_sl23_eq_bot] at hle
  have hbot : (CFSG.oddCore G).map e.toMonoidHom = ⊥ := le_bot_iff.mp hle
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxmap : e x ∈ (CFSG.oddCore G).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hx
  rw [hbot] at hxmap
  exact e.injective (by simpa using (Subgroup.mem_bot.mp hxmap))

theorem sl2_quotient_of_sup {P : Type} [Group P] [Finite P] {z : P} (hz : z ∈ center P)
    (hz2 : orderOf z = 2) (K R : Subgroup P) [R.Normal]
    (hK : Nonempty (↥K ≃* SL(2, ZMod 3))) (hzK : z ∈ K) (hzR : z ∈ R) {m : ℕ}
    (hcard : Nat.card R = 2 * m) (hm : Odd m) (hKR : K ⊔ R = ⊤) :
    Nonempty (P ⧸ CFSG.oddCore P ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨O, hOnormal, _hOleR, hOcard, _hOinf, hOsup⟩ :=
    exists_odd_normal_complement hz hz2 hzR hcard hm
  haveI hOnorm : O.Normal := hOnormal
  have hoddO : Odd (Nat.card O) := by rw [hOcard]; exact hm
  have hKO_sup : K ⊔ O = ⊤ := by
    have hzKle : zpowers z ≤ K := Subgroup.zpowers_le.mpr hzK
    have h1 : (K ⊔ O) ⊔ zpowers z = ⊤ := by rw [sup_assoc, hOsup, hKR]
    rw [← h1, sup_eq_left.mpr (hzKle.trans le_sup_left)]
  have hKO_inf : K ⊓ O = ⊥ := by
    have hsub_odd : Odd (Nat.card (O.subgroupOf K)) :=
      hoddO.of_dvd_nat
        (Subgroup.card_comap_dvd_of_injective O K.subtype K.subtype_injective)
    have hle : O.subgroupOf K ≤ CFSG.oddCore K :=
      CFSG.ABGLocalTools.le_oddCore_of_normal (hOnormal.subgroupOf K) hsub_odd
    rw [oddCore_eq_bot_of_mulEquiv_sl23 hK.some] at hle
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : K) ∈ O.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx.2
    have hmem : (⟨x, hx.1⟩ : K) ∈ (⊥ : Subgroup K) := hle hx'
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
  have hcompl : K.IsComplement' O := by
    refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff, hKO_inf]
    · rw [← Subgroup.mul_normal K O, hKO_sup, Subgroup.coe_top]
  obtain ⟨eK⟩ := hK
  let eO : P ⧸ O ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    (hcompl.QuotientMulEquiv).trans eK
  have hcore_quot : CFSG.oddCore (P ⧸ O) = ⊥ := oddCore_eq_bot_of_mulEquiv_sl23 eO
  have hcore : CFSG.oddCore P = O := oddCore_eq_of_quotient O hoddO hcore_quot
  haveI : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcardfield : Fintype.card (ZMod 3) = Fintype.card (GaloisField 3 1) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)]
    norm_num
  have e2 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1) :=
    slEquivOfRingEquiv (FiniteField.ringEquivOfCardEq hcardfield)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans (eO.trans e2)⟩

end CFSG.OddStandard.SmallF3.Omega
