module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import CFSG.Quasithin.Background.B6Defs

import CFSG.LinearAlgebra.SL2CharTwoInvolution
import CFSG.Timmesfeld.ARS.NaturalModule
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.Quasithin.Background.C124Perf
import CFSG.GroupTheory.TwoResidualOddOrder
import Mathlib.Algebra.CharP.CharAndCard
import CFSG.Quasithin.MS93.S37RPts
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.Basic
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.E1Inherit
import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Certificates.Certificate43

public section

namespace CFSG.GroupTheory.SL2CharTwo

open CFSG.Quasithin
open Matrix

open scoped commutatorElement

variable {F : Type} [Field F] [Fintype F] {m : ℕ}

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F

private def keyElt [CharP F 2] : SL2 :=
  ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

omit [Fintype F] in
private lemma coe_keyElt [CharP F 2] :
    ((keyElt : SL2) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := rfl

private def sqElt [CharP F 2] : SL2 :=
  ⟨!![1, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

omit [Fintype F] in
private lemma coe_sqElt [CharP F 2] :
    ((sqElt : SL2) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, 0] := rfl

private abbrev wElt : SL2 :=
  (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2W : SL2)

private abbrev uElt (t : F) : SL2 := CFSG.Timmesfeld.RankOne.upperElt F t

private abbrev lElt (t : F) : SL2 := CFSG.Timmesfeld.RankOne.lowerElt F t

omit [Fintype F] in
private lemma coe_uElt (t : F) :
    ((uElt t : SL2) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

omit [Fintype F] in
private lemma coe_lElt (t : F) :
    ((lElt t : SL2) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := rfl

omit [Fintype F] in
private lemma uElt_one_mul_self [CharP F 2] : (uElt (1 : F) : SL2) * uElt (1 : F) = 1 := by
  rw [uElt, CFSG.Timmesfeld.RankOne.upperElt_mul, CharTwo.add_self_eq_zero,
    CFSG.Timmesfeld.RankOne.upperElt_zero]

omit [Fintype F] in
private lemma uElt_one_ne_one [CharP F 2] : (uElt (1 : F) : SL2) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL2 => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_uElt] at this

omit [Fintype F] in
private lemma lElt_one_mul_self [CharP F 2] : (lElt (1 : F) : SL2) * lElt (1 : F) = 1 := by
  rw [lElt, CFSG.Timmesfeld.RankOne.lowerElt_mul, CharTwo.add_self_eq_zero,
    CFSG.Timmesfeld.RankOne.lowerElt_zero]

omit [Fintype F] in
private lemma lElt_one_ne_one [CharP F 2] : (lElt (1 : F) : SL2) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL2 => (g : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp [coe_lElt] at this

omit [Fintype F] in
private lemma eq_one_of_add_one_eq_zero [CharP F 2] {t : F} (h : t + 1 = 0) : t = 1 := by
  have := eq_neg_of_add_eq_zero_left h
  rwa [CharTwo.neg_eq] at this

omit [Fintype F] in
private lemma eq_zero_of_add_one_eq_one {t : F} (h : t + 1 = 1) : t = 0 := by
  have h' : t + 1 = 0 + 1 := by simpa using h
  simpa using add_right_cancel h'

omit [Fintype F] in
private lemma one_add_add_one [CharP F 2] (t : F) : 1 + (t + 1) = t := by
  calc 1 + (t + 1) = (1 + 1) + t := by abel
    _ = t := by rw [CharTwo.add_self_eq_zero, zero_add]

omit [Fintype F] in
private lemma add_one_ne_one {t : F} (h : t ≠ 0) : t + 1 ≠ 1 :=
  fun h1 => h (eq_zero_of_add_one_eq_one h1)

omit [Fintype F] in
private lemma commutator_uElt_wElt [CharP F 2] : ⁅(uElt (1 : F) : SL2), (wElt : SL2)⁆ = keyElt := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right uElt_one_mul_self,
    inv_eq_of_mul_eq_one_right (show (wElt : SL2) * wElt = 1 from CFSG.LinearAlgebra.sl2W_mul_self)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_keyElt, coe_uElt, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero, CharTwo.neg_eq]

omit [Fintype F] in
private lemma keyElt_mul_self [CharP F 2] : (keyElt : SL2) * keyElt = sqElt := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_keyElt, coe_sqElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, CharTwo.add_self_eq_zero]

omit [Fintype F] in
private lemma keyElt_mem_commutator [CharP F 2] : (keyElt : SL2) ∈ commutator SL2 := by
  rw [← commutator_uElt_wElt]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

omit [Fintype F] in
private lemma diagElt_mul_uElt_mul_inv [CharP F 2] (a : Fˣ) (t : F) :
    CFSG.Timmesfeld.ARS.NaturalModule.diagElt a * uElt t *
      (CFSG.Timmesfeld.ARS.NaturalModule.diagElt a)⁻¹ = uElt ((a : F) ^ 2 * t) := by
  rw [CFSG.Timmesfeld.ARS.NaturalModule.diagElt_mul_upperElt]
  group

omit [Fintype F] in
private lemma commutator_dElt_uElt_one [CharP F 2] (a : Fˣ) :
    ⁅CFSG.Timmesfeld.ARS.NaturalModule.diagElt a, (uElt (1 : F) : SL2)⁆ =
      uElt ((a : F) ^ 2 + 1) := by
  have hconj := diagElt_mul_uElt_mul_inv a 1
  have hx : (uElt (1 : F) : SL2) * uElt (1 : F) = 1 := uElt_one_mul_self
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hx]
  calc CFSG.Timmesfeld.ARS.NaturalModule.diagElt a * uElt (1 : F) *
        (CFSG.Timmesfeld.ARS.NaturalModule.diagElt a)⁻¹ * uElt (1 : F)
      = (CFSG.Timmesfeld.ARS.NaturalModule.diagElt a * uElt (1 : F) *
          (CFSG.Timmesfeld.ARS.NaturalModule.diagElt a)⁻¹) * uElt (1 : F) := by group
    _ = uElt ((a : F) ^ 2 * 1) * uElt (1 : F) := by rw [hconj]
    _ = uElt ((a : F) ^ 2 + 1) := by
        rw [mul_one, uElt, uElt, CFSG.Timmesfeld.RankOne.upperElt_mul]

omit [Fintype F] in
private lemma keyElt_mul_uElt_mul_keyElt_sq [CharP F 2] (t : F) :
    (keyElt : SL2) * uElt t * (keyElt * keyElt) = lElt t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_keyElt, coe_uElt, coe_lElt, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero, one_add_add_one]

private abbrev commU : Subgroup SL2 :=
  ⁅(⊤ : Subgroup SL2), Subgroup.zpowers (uElt (1 : F))⁆

omit [Fintype F] in
private lemma sqElt_mem_commU_g45n2 [CharP F 2] : (sqElt : SL2) ∈ commU := by
  have hu : (uElt (1 : F) : SL2) ∈ Subgroup.zpowers (uElt (1 : F)) := Subgroup.mem_zpowers _
  have hmem : ⁅(wElt : SL2), uElt (1 : F)⁆ ∈ commU :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hu
  have hval : ⁅(wElt : SL2), uElt (1 : F)⁆ = sqElt := by
    have hw2 : (wElt : SL2) * wElt = 1 := CFSG.LinearAlgebra.sl2W_mul_self
    have hx2 : (uElt (1 : F) : SL2) * uElt (1 : F) = 1 := uElt_one_mul_self
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hw2,
      inv_eq_of_mul_eq_one_right hx2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_sqElt, coe_uElt, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero, CharTwo.neg_eq]
  rwa [hval] at hmem

omit [Fintype F] in
private lemma keyElt_mem_commU_g45n2 [CharP F 2] : (keyElt : SL2) ∈ commU := by
  have hsq : (sqElt : SL2) ∈ commU := sqElt_mem_commU_g45n2
  have hmem : (sqElt : SL2) * sqElt ∈ commU := mul_mem hsq hsq
  have hsqsq : (sqElt : SL2) * sqElt = (keyElt : SL2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_sqElt, coe_keyElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  rwa [hsqsq] at hmem

omit [Fintype F] in
private lemma keyElt_mul_self_mem_commU_g45n2 [CharP F 2] :
    (keyElt : SL2) * keyElt ∈ commU := by
  rw [keyElt_mul_self]
  exact sqElt_mem_commU_g45n2

private lemma uElt_mem_commU_g45n2 [CharP F 2] {t : F} (ht1 : t ≠ 1) : uElt t ∈ commU := by
  have hu : (uElt (1 : F) : SL2) ∈ Subgroup.zpowers (uElt (1 : F)) := Subgroup.mem_zpowers _
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two hchar (t + 1)
  have ha0 : a ≠ 0 := by
    intro h
    apply ht1
    apply eq_one_of_add_one_eq_zero
    rw [ha, h, mul_zero]
  let b : Fˣ := Units.mk0 a ha0
  have hb : (b : F) = a := Units.val_mk0 ha0
  have hpara : ((b : F) ^ 2 + 1) = t := by
    rw [hb, pow_two, ← ha, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hmem : ⁅(CFSG.Timmesfeld.ARS.NaturalModule.diagElt b : SL2),
      (uElt (1 : F) : SL2)⁆ ∈ commU :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hu
  rw [commutator_dElt_uElt_one, hpara] at hmem
  exact hmem

private lemma upperUnipotent_le_commU_g45n2 [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    CFSG.Timmesfeld.upperUnipotent F ≤ commU := by
  intro x hx
  obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).1 hx
  by_cases ht1 : t = 1
  · subst ht1
    obtain ⟨a, ha0, ha1⟩ := CFSG.Quasithin.MS93.S37R.exists_ne_zero_ne_one' (F := F) (by omega)
    have hb1 : a + 1 ≠ 1 := add_one_ne_one ha0
    have hsum : a + (a + 1) = 1 := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have ha_mem : uElt a ∈ commU := uElt_mem_commU_g45n2 ha1
    have hb_mem : uElt (a + 1) ∈ commU := uElt_mem_commU_g45n2 hb1
    rw [← hsum, ← CFSG.Timmesfeld.RankOne.upperElt_mul]
    exact mul_mem ha_mem hb_mem
  · exact uElt_mem_commU_g45n2 ht1

private lemma lowerUnipotent_le_commU_g45n2 [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    CFSG.Timmesfeld.lowerUnipotent F ≤ commU := by
  intro x hx
  obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_lowerUnipotent_iff F).1 hx
  have hut : uElt t ∈ commU :=
    upperUnipotent_le_commU_g45n2 h4
      ((CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).2 ⟨t, rfl⟩)
  have hmem : (keyElt : SL2) * uElt t * (keyElt * keyElt) ∈ commU :=
    mul_mem (mul_mem keyElt_mem_commU_g45n2 hut) keyElt_mul_self_mem_commU_g45n2
  rwa [keyElt_mul_uElt_mul_keyElt_sq] at hmem

private lemma commutator_zpowers_uElt_one_eq_top [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    ⁅(⊤ : Subgroup SL2), Subgroup.zpowers (uElt (1 : F))⁆ = ⊤ := by
  have hsup := CFSG.Timmesfeld.ARS.NaturalModule.upperUnipotent_sup_lowerUnipotent (K := F)
  change commU = ⊤
  rw [eq_top_iff, ← hsup]
  exact sup_le (upperUnipotent_le_commU_g45n2 h4) (lowerUnipotent_le_commU_g45n2 h4)

private lemma exists_conj_uElt_one [CharP F 2] {s : SL2} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ g : SL2, g * (uElt (1 : F) : SL2) * g⁻¹ = s := by
  obtain ⟨g, hg⟩ := CFSG.LinearAlgebra.exists_conj_sl2W hs2 hs1
  have hx2 : (uElt (1 : F) : SL2) * uElt (1 : F) = 1 := uElt_one_mul_self
  have hx1 : (uElt (1 : F) : SL2) ≠ 1 := uElt_one_ne_one
  obtain ⟨h, hh⟩ := CFSG.LinearAlgebra.exists_conj_sl2W hx2 hx1
  have hw : (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2W : SL2) =
      h⁻¹ * (uElt (1 : F) : SL2) * h := by
    rw [← hh]
    group
  refine ⟨g * h⁻¹, ?_⟩
  calc (g * h⁻¹) * (uElt (1 : F) : SL2) * (g * h⁻¹)⁻¹
      = g * (h⁻¹ * uElt (1 : F) * h) * g⁻¹ := by group
    _ = g * (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2W : SL2) * g⁻¹ := by
        rw [hw]
    _ = s := hg

private lemma commutator_zpowers_eq_top_of_involution [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {s : SL2} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ⁅(⊤ : Subgroup SL2), Subgroup.zpowers s⁆ = ⊤ := by
  obtain ⟨g, hg⟩ := exists_conj_uElt_one (F := F) hs2 hs1
  have hmain : ⁅(⊤ : Subgroup SL2), Subgroup.zpowers (uElt (1 : F))⁆ = ⊤ :=
    commutator_zpowers_uElt_one_eq_top h4
  have hmap := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hmain
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective,
    MonoidHom.map_zpowers] at hmap
  have hval : (MulAut.conj g).toMonoidHom (uElt (1 : F)) = s := by
    change (MulAut.conj g) (uElt (1 : F)) = s
    rw [MulAut.conj_apply]
    exact hg
  rw [hval] at hmap
  exact hmap

private lemma exists_involution_of_isPGroup {T : Subgroup SL2} (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) :
    ∃ t : SL2, t ∈ T ∧ t * t = 1 ∧ t ≠ 1 := by
  classical
  have hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  have hk0 : k ≠ 0 := by
    intro h0
    exact hT1 (Subgroup.card_eq_one.mp (by rw [hk, h0, pow_zero]))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 (by
    rw [hk]
    exact pow_dvd_pow 2 (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)))
  have ht2T : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have ht2 : (t : SL2) * (t : SL2) = 1 := by
    have := congrArg (fun x : ↥T => (x : SL2)) ht2T
    simpa using this
  have ht1 : (t : SL2) ≠ 1 := by
    intro h
    have h1 : t = 1 := Subtype.ext h
    rw [h1, orderOf_one] at ht
    omega
  exact ⟨(t : SL2), t.2, ht2, ht1⟩

private lemma commutator_top_eq_top_of_isPGroup [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {T : Subgroup SL2} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ⁅(⊤ : Subgroup SL2), T⁆ = ⊤ := by
  obtain ⟨t, htT, ht2, ht1⟩ := exists_involution_of_isPGroup hT hT1
  have htop : ⁅(⊤ : Subgroup SL2), Subgroup.zpowers t⁆ = ⊤ :=
    commutator_zpowers_eq_top_of_involution h4 ht2 ht1
  have hle : ⁅(⊤ : Subgroup SL2), Subgroup.zpowers t⁆ ≤ ⁅(⊤ : Subgroup SL2), T⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr htT)
  rw [htop] at hle
  exact le_antisymm le_top hle

private lemma card_SL2_of_card_two (h2 : Nat.card F = 2) : Nat.card SL2 = 6 := by
  have hF2 : Fintype.card F = 2 := by rwa [Nat.card_eq_fintype_card] at h2
  rw [Matrix.card_SL_field (𝔽 := F) 2, hF2, Fin.prod_univ_two]
  norm_num

omit [Fintype F] in
private lemma keyElt_orderOf [CharP F 2] : orderOf (keyElt : SL2) = 3 := by
  have hprime : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3 : (keyElt : SL2) ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, keyElt_mul_self]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_keyElt, coe_sqElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have h1 : (keyElt : SL2) ≠ 1 := by
    intro h
    have := congrArg (fun g : SL2 => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [coe_keyElt] at this
  exact orderOf_eq_prime h3 h1

omit [Fintype F] in
private lemma lElt_one_orderOf [CharP F 2] : orderOf (lElt (1 : F) : SL2) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact lElt_one_mul_self) lElt_one_ne_one

private lemma commutator_eq_zpowers_keyElt_of_card_two [CharP F 2] (h2 : Nat.card F = 2) :
    commutator SL2 = Subgroup.zpowers (keyElt : SL2) := by
  have hG : Nat.card SL2 = 6 := card_SL2_of_card_two h2
  have hord : orderOf (keyElt : SL2) = 3 := keyElt_orderOf
  have hN : Nat.card (Subgroup.zpowers (keyElt : SL2)) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hindex : (Subgroup.zpowers (keyElt : SL2)).index = 2 := by
    rw [Subgroup.index_eq_card_div, hN, hG]
  have hnormal : (Subgroup.zpowers (keyElt : SL2)).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  have htord : orderOf (lElt (1 : F) : SL2) = 2 := lElt_one_orderOf
  have ht_notMem : (lElt (1 : F) : SL2) ∉ Subgroup.zpowers (keyElt : SL2) := by
    intro hmem
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hN, htord] at hdvd
    omega
  have hsup : Subgroup.zpowers (keyElt : SL2) ⊔ Subgroup.zpowers (lElt (1 : F) : SL2) = ⊤ := by
    set N := Subgroup.zpowers (keyElt : SL2)
    set H := Subgroup.zpowers (lElt (1 : F) : SL2)
    have hle : N ≤ N ⊔ H := le_sup_left
    have hdiv : (N ⊔ H).index ∣ N.index := Subgroup.index_dvd_of_le hle
    rw [hindex] at hdiv
    have hne : (N ⊔ H).index ≠ 2 := by
      intro h2'
      have heq : N = N ⊔ H :=
        Subgroup.eq_of_index_dvd_index hle (by rw [hindex, h2'])
      have hmem : (lElt (1 : F) : SL2) ∈ N := by
        rw [heq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      exact ht_notMem hmem
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2'
    · exact Subgroup.index_eq_one.mp h1
    · exact absurd h2' hne
  have hcyc : IsCyclic ↥(Subgroup.zpowers (lElt (1 : F) : SL2)) := inferInstance
  have hcomm : commutator SL2 ≤ Subgroup.zpowers (keyElt : SL2) :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (IsCyclic.isMulCommutative)
  exact le_antisymm hcomm (Subgroup.zpowers_le.mpr keyElt_mem_commutator)

theorem eq_zero_of_forall_mulVec_eq (hF : Fintype.card F = 2 ^ m) {v : Fin 2 → F}
    (hv : ∀ g ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F),
      (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) :
    v = 0 := by
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) hF
  have h := hv keyElt keyElt_mem_commutator
  have h0 : v 1 = v 0 := by
    have := congrFun h 0
    simpa [coe_keyElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h1 : v 0 + v 1 = v 1 := by
    have := congrFun h 1
    simpa [coe_keyElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hv0 : v 0 = 0 := by
    have h1' : v 0 + v 1 = 0 + v 1 := by simpa using h1
    simpa using add_right_cancel h1'
  funext i
  fin_cases i
  · simpa using hv0
  · simp [h0, hv0]

private lemma natCard_eq_two_g45n2 (hF : Fintype.card F = 2 ^ m) (h4 : ¬ 4 ≤ Nat.card F) :
    Nat.card F = 2 := by
  have h2 : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    have h := Fintype.one_lt_card (α := F)
    omega
  have h3 : Nat.card F ≤ 3 := by omega
  have hF' : Nat.card F = 2 ^ m := by rwa [Nat.card_eq_fintype_card]
  rcases m with _ | k
  · rw [hF'] at h2; norm_num at h2
  rcases k with _ | j
  · simpa using hF'
  · exfalso
    have h4' : 4 ≤ 2 ^ (j + 1 + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hF'] at h3
    omega

private lemma sup_zpowers_keyElt_zpowers_eq_top_of_card_two_g45n2 [CharP F 2]
    (hcard : Nat.card F = 2) {t : SL2} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Subgroup.zpowers (keyElt : SL2) ⊔ Subgroup.zpowers t = ⊤ := by
  have hN : Nat.card (Subgroup.zpowers (keyElt : SL2)) = 3 := by
    rw [Nat.card_zpowers, keyElt_orderOf]
  have hG : Nat.card SL2 = 6 := card_SL2_of_card_two hcard
  have hindex : (Subgroup.zpowers (keyElt : SL2)).index = 2 := by
    rw [Subgroup.index_eq_card_div, hN, hG]
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have ht_notMem : t ∉ Subgroup.zpowers (keyElt : SL2) := by
    intro hmem
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hN, htord] at hdvd
    omega
  set N := Subgroup.zpowers (keyElt : SL2)
  set H := Subgroup.zpowers t
  have hle : N ≤ N ⊔ H := le_sup_left
  have hdiv : (N ⊔ H).index ∣ N.index := Subgroup.index_dvd_of_le hle
  rw [hindex] at hdiv
  have hne : (N ⊔ H).index ≠ 2 := by
    intro h2'
    have heq : N = N ⊔ H :=
      Subgroup.eq_of_index_dvd_index hle (by rw [hindex, h2'])
    have hmem : t ∈ N := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact ht_notMem hmem
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2'
  · exact Subgroup.index_eq_one.mp h1
  · exact absurd h2' hne

private lemma conj_ne_keyElt_of_card_two_g45n2 [CharP F 2] (hcard : Nat.card F = 2)
    {t : SL2} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    t * keyElt * t⁻¹ ≠ keyElt := by
  have hK : commutator SL2 = Subgroup.zpowers (keyElt : SL2) :=
    commutator_eq_zpowers_keyElt_of_card_two hcard
  have hsupN : Subgroup.zpowers (keyElt : SL2) ⊔ Subgroup.zpowers t = ⊤ :=
    sup_zpowers_keyElt_zpowers_eq_top_of_card_two_g45n2 hcard ht2 ht1
  intro hconj
  have hcomm : t * keyElt = keyElt * t := by
    calc t * keyElt = (t * keyElt * t⁻¹) * t := by group
      _ = keyElt * t := by rw [hconj]
  have hgC : (keyElt : SL2) ∈ Subgroup.centralizer ({t} : Set SL2) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm
  have htC : t ∈ Subgroup.centralizer ({t} : Set SL2) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rfl
  have hKle : commutator SL2 ≤ Subgroup.centralizer ({t} : Set SL2) := by
    rw [hK]
    exact Subgroup.zpowers_le.mpr hgC
  have hsupC : Subgroup.centralizer ({t} : Set SL2) = ⊤ := by
    refine top_le_iff.mp ?_
    have hle : commutator SL2 ⊔ Subgroup.zpowers t ≤
        Subgroup.centralizer ({t} : Set SL2) :=
      sup_le hKle (Subgroup.zpowers_le.mpr htC)
    rwa [hK, hsupN] at hle
  have hcenter : t ∈ Subgroup.center SL2 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({t} : Set SL2) := by rw [hsupC]; trivial
    rw [Subgroup.mem_centralizer_iff] at hg
    exact (hg t (by simp)).symm
  have hbot : t ∈ (⊥ : Subgroup SL2) := by
    rw [← CFSG.Timmesfeld.RankOne.center_SL2_eq_bot F]
    exact hcenter
  exact ht1 (Subgroup.mem_bot.mp hbot)

private lemma commutator_keyElt_t_ne_one_of_card_two_g45n2 [CharP F 2] (hcard : Nat.card F = 2)
    {t : SL2} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ⁅(keyElt : SL2), t⁆ ≠ 1 := by
  intro hc
  apply conj_ne_keyElt_of_card_two_g45n2 hcard ht2 ht1
  have hcomm : keyElt * t = t * keyElt := by
    have hc' := hc
    rw [commutatorElement_def] at hc'
    calc keyElt * t = keyElt * t * keyElt⁻¹ * t⁻¹ * (t * keyElt) := by group
      _ = 1 * (t * keyElt) := by rw [hc']
      _ = t * keyElt := one_mul _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  calc t * keyElt * t⁻¹ = t * keyElt * t := by rw [htinv]
    _ = t * (keyElt * t) := by rw [mul_assoc]
    _ = t * (t * keyElt) := by rw [hcomm]
    _ = (t * t) * keyElt := by rw [mul_assoc]
    _ = keyElt := by rw [ht2, one_mul]

private lemma zpowers_commutator_keyElt_t_eq_commutator_of_card_two_g45n2 [CharP F 2]
    (hcard : Nat.card F = 2) {t : SL2} (hc_ne : ⁅(keyElt : SL2), t⁆ ≠ 1) :
    Subgroup.zpowers ⁅(keyElt : SL2), t⁆ = commutator SL2 := by
  have hK : commutator SL2 = Subgroup.zpowers (keyElt : SL2) :=
    commutator_eq_zpowers_keyElt_of_card_two hcard
  have hN : Nat.card (Subgroup.zpowers (keyElt : SL2)) = 3 := by
    rw [Nat.card_zpowers, keyElt_orderOf]
  have hc_memK : ⁅(keyElt : SL2), t⁆ ∈ commutator SL2 :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hc_card : Nat.card (Subgroup.zpowers ⁅(keyElt : SL2), t⁆) = 3 := by
    have hdvd : orderOf ⁅(keyElt : SL2), t⁆ ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard (commutator SL2) hc_memK
      rwa [hK, hN] at this
    have hne1 : orderOf ⁅(keyElt : SL2), t⁆ ≠ 1 := by
      intro h1
      exact hc_ne (orderOf_eq_one_iff.mp h1)
    have hord3 : orderOf ⁅(keyElt : SL2), t⁆ = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
      · exact absurd h1 hne1
      · exact h3
    rw [Nat.card_zpowers, hord3]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc_memK)
    (by rw [hK, hN, hc_card])

private lemma commutator_commutator_eq_of_card_two_g45n2 [CharP F 2] (hcard : Nat.card F = 2)
    {T : Subgroup SL2} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ⁅commutator SL2, T⁆ = commutator SL2 := by
  have hK : commutator SL2 = Subgroup.zpowers (keyElt : SL2) :=
    commutator_eq_zpowers_keyElt_of_card_two hcard
  obtain ⟨t, htT, ht2, ht1⟩ := exists_involution_of_isPGroup hT hT1
  have hc_mem : ⁅(keyElt : SL2), t⁆ ∈ ⁅commutator SL2, T⁆ := by
    rw [hK]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) htT
  have hc_ne : ⁅(keyElt : SL2), t⁆ ≠ 1 :=
    commutator_keyElt_t_ne_one_of_card_two_g45n2 hcard ht2 ht1
  have hzeq : Subgroup.zpowers ⁅(keyElt : SL2), t⁆ = commutator SL2 :=
    zpowers_commutator_keyElt_t_eq_commutator_of_card_two_g45n2 hcard hc_ne
  have hrev : commutator SL2 ≤ ⁅commutator SL2, T⁆ := by
    have hle : Subgroup.zpowers ⁅(keyElt : SL2), t⁆ ≤ ⁅commutator SL2, T⁆ :=
      Subgroup.zpowers_le.mpr hc_mem
    rwa [hzeq] at hle
  exact le_antisymm (Subgroup.commutator_le_left _ _) hrev

theorem commutator_commutator_eq_of_isPGroup (hF : Fintype.card F = 2 ^ m)
    {T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ⁅commutator (Matrix.SpecialLinearGroup (Fin 2) F), T⁆ =
      commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) hF
  by_cases h4 : 4 ≤ Nat.card F
  · have hperfect : Group.IsPerfect SL2 :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
    have hK : commutator SL2 = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [hK]
    exact commutator_top_eq_top_of_isPGroup h4 hT hT1
  · exact commutator_commutator_eq_of_card_two_g45n2 (natCard_eq_two_g45n2 hF h4) hT hT1

theorem twoResidual_commutator_eq (hF : Fintype.card F = 2 ^ m) :
    twoResidual (commutator (Matrix.SpecialLinearGroup (Fin 2) F)) =
      commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) hF
  apply le_antisymm (twoResidual_le _)
  by_cases h4 : 4 ≤ Nat.card F
  · have hperfect : Group.IsPerfect SL2 :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
    have hK : commutator SL2 = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [hK]
    exact le_of_eq (CFSG.Quasithin.C124.twoResidual_eq_self_of_perfect' (Y := ⊤)
      Group.IsPerfect.commutator_eq_top).symm
  · have hcardF : Nat.card F = 2 := by
      have h2 : 2 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        have h := Fintype.one_lt_card (α := F)
        omega
      have h3 : Nat.card F ≤ 3 := by omega
      have hF' : Nat.card F = 2 ^ m := by rwa [Nat.card_eq_fintype_card]
      rcases m with _ | k
      · rw [hF'] at h2; norm_num at h2
      rcases k with _ | j
      · simpa using hF'
      · exfalso
        have h4' : 4 ≤ 2 ^ (j + 1 + 1) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [hF'] at h3
        omega
    have hK : commutator SL2 = Subgroup.zpowers (keyElt : SL2) :=
      commutator_eq_zpowers_keyElt_of_card_two hcardF
    have hN : Nat.card (commutator SL2) = 3 := by
      rw [hK, Nat.card_zpowers, keyElt_orderOf]
    exact CFSG.GroupTheory.le_twoResidual_of_odd_card (H := commutator SL2)
      (X := commutator SL2) le_rfl (by rw [hN]; exact ⟨1, by norm_num⟩)

end CFSG.GroupTheory.SL2CharTwo
