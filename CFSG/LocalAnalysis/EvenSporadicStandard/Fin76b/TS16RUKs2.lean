
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs2Base

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dih0
public import Certificates.Certificate27828

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.Sporadic.SmallOddCore

section Inv7

theorem u7_facts :
    centKs reps[4]! = 2880 ∧ isInvA 820 y8Arr (invCand 820 y8Arr) = true ∧ inP y8Arr = true ∧
    eqA 820 (powA 820 y8Arr 8) (idA 820) = true ∧ eqA 820 (powA 820 y8Arr 4) (idA 820) = false ∧
    eqA 820 (compA 820 y8Arr reps[4]!) (compA 820 reps[4]! y8Arr) = true := by
  have h := Certificates.certificate27828.1
  simp only [u7Check, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem rep_y8 : Rep 820 y8Arr y8Perm := (rep_permOfArr u7_facts.2.1).1

theorem y8_mem_P : y8Perm ∈ P := (inP_iff rep_y8).1 u7_facts.2.2.1

theorem y8_orderOf : orderOf y8Perm = 8 := by
  rw [orderOf_eq_eight_iff]
  refine ⟨(eqA_iff (rep_powA rep_y8 8) rep_idA).1 u7_facts.2.2.2.1, fun h => ?_⟩
  have h4 := u7_facts.2.2.2.2.1
  rw [(eqA_iff (rep_powA rep_y8 4) rep_idA).2 h] at h4
  exact Bool.noConfusion h4

theorem y8_comm : y8Perm * rP 4 = rP 4 * y8Perm :=
  (eqA_iff (rep_compA rep_y8 (rep_rP (by norm_num))) (rep_compA (rep_rP (by norm_num)) rep_y8)).1
    u7_facts.2.2.2.2.2

theorem card_cent_rP4 :
    Nat.card {x : ↥U43ExtStar // (x : Equiv.Perm (Fin 820)) * rP 4 = rP 4 * x} = 2880 :=
  (card_cent_Ks (rep_rP (by norm_num : 4 < 9))).trans u7_facts.1

theorem card_CKs7 : Nat.card ↥CKs7 = 2880 := by
  rw [← card_cent_rP4]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2⟩
      invFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2,
        Subgroup.mem_centralizer_singleton_iff.2 x.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem y8_mem_CKs7 : y8Perm ∈ CKs7 :=
  Subgroup.mem_inf.2 ⟨P_le_U43ExtStar y8_mem_P, Subgroup.mem_centralizer_singleton_iff.2 y8_comm⟩

theorem ks_inv7_sylow {u : Equiv.Perm (Fin 820)} (hu : u ∈ U43ExtStar) (hu2 : u * u = 1)
    (hu7 : InCos 7 u) {R : Subgroup (Equiv.Perm (Fin 820))} (hR : R ≤ U43ExtStar)
    (hc : ∀ r ∈ R, r * u = u * r) (hR2 : IsPGroup 2 R) (hcard : 64 ≤ Nat.card ↥R) :
    ∃ r ∈ R, orderOf r = 8 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 : u ≠ 1 := by
    intro h
    have h1 : tP 7 ∈ P := by
      have := hu7
      rw [h] at this
      unfold InCos at this
      simpa using this
    exact absurd ((tP_mem_P_iff (by norm_num)).1 h1) (by norm_num)
  obtain ⟨j, hj, ⟨c, hcP, huc⟩, g, hg, hug⟩ := involution_data (U43ExtStar_le_R hu) hu2 hu1
  have hjk : repCoset[j]! = 7 :=
    inCos_unique (repCoset_lt hj) (by norm_num) (inCos_iff.2 ⟨g, hg, hug⟩) hu7
  have hj4 : j = 4 := repCoset_eq_seven j hj hjk
  subst hj4
  have hcKs : c ∈ U43ExtStar := P_le_U43ExtStar hcP
  set R' : Subgroup (Equiv.Perm (Fin 820)) := R.map (MulAut.conj c⁻¹).toMonoidHom with hR'
  have hmemR' : ∀ x, x ∈ R' ↔ c * x * c⁻¹ ∈ R := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hr
    · intro hx
      exact ⟨c * x * c⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hR'Ks : R' ≤ U43ExtStar := by
    intro x hx
    have h1 := hR ((hmemR' x).1 hx)
    have := U43ExtStar.mul_mem (U43ExtStar.mul_mem (U43ExtStar.inv_mem hcKs) h1) hcKs
    simpa [mul_assoc] using this
  have hR'comm : ∀ x ∈ R', x * rP 4 = rP 4 * x := by
    intro x hx
    have h1 := hc _ ((hmemR' x).1 hx)
    rw [huc] at h1
    have h2 : c * (x * rP 4) * c⁻¹ = c * (rP 4 * x) * c⁻¹ := by
      calc c * (x * rP 4) * c⁻¹ = c * x * c⁻¹ * (c * rP 4 * c⁻¹) := by group
        _ = c * rP 4 * c⁻¹ * (c * x * c⁻¹) := h1
        _ = c * (rP 4 * x) * c⁻¹ := by group
    have h3 := mul_right_cancel h2
    exact mul_left_cancel h3
  have hR'le : R' ≤ CKs7 := fun x hx =>
    Subgroup.mem_inf.2 ⟨hR'Ks hx, Subgroup.mem_centralizer_singleton_iff.2 (hR'comm x hx)⟩
  have hR'card : Nat.card ↥R' = Nat.card ↥R :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hR2
  have hdvd : 2 ^ a ∣ 2880 := by
    rw [← ha, ← hR'card, ← card_CKs7]
    exact Subgroup.card_dvd_of_le hR'le
  have h64 : 2 ^ a = 64 := by
    have hle : 2 ^ a ≤ 64 := by
      by_contra hlt
      push_neg at hlt
      have h7 : 7 ≤ a := by
        by_contra h
        push_neg at h
        have : 2 ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : 128 ∣ 2880 := dvd_trans (Nat.pow_dvd_pow 2 h7) hdvd
      omega
    omega
  set A : Subgroup ↥CKs7 := R'.subgroupOf CKs7 with hA
  have hAcard : Nat.card ↥A = 64 := by
    have e := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'le).toEquiv
    rw [hA, e, hR'card, ha, h64]
  have hidx : A.index = 45 := by
    have := Subgroup.card_mul_index A
    rw [hAcard, card_CKs7] at this
    omega
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 6) (by rw [hAcard]; norm_num)
  let SA : Sylow 2 ↥CKs7 := hA2.toSylow (by rw [hidx]; norm_num)
  set Y : Subgroup ↥CKs7 := (zpowers y8Perm).subgroupOf CKs7 with hY
  have hYcard : Nat.card ↥Y = 8 := by
    have e := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (zpowers_le.2 y8_mem_CKs7)).toEquiv
    rw [hY, e, Nat.card_zpowers, y8_orderOf]
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := 3) (by rw [hYcard]; norm_num)
  obtain ⟨Q₀, hQ₀⟩ := hY2.exists_le_sylow
  obtain ⟨gg, hgg⟩ := MulAction.exists_smul_eq (↥CKs7) Q₀ SA
  let y₀ : ↥CKs7 := ⟨y8Perm, y8_mem_CKs7⟩
  have hy₀Y : y₀ ∈ Y := Subgroup.mem_subgroupOf.2 (mem_zpowers _)
  have hy₀Q : y₀ ∈ (Q₀ : Subgroup ↥CKs7) := hQ₀ hy₀Y
  have hconj : gg * y₀ * gg⁻¹ ∈ (SA : Subgroup ↥CKs7) := by
    rw [← hgg, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul y₀ (MulAut.conj gg) (Q₀ : Subgroup ↥CKs7) hy₀Q
    simpa using this
  have hconj' : (gg * y₀ * gg⁻¹ : ↥CKs7) ∈ A := by
    have : (SA : Subgroup ↥CKs7) = A := rfl
    rwa [this] at hconj
  have hr' : (((gg * y₀ * gg⁻¹ : ↥CKs7) : Equiv.Perm (Fin 820))) ∈ R' :=
    Subgroup.mem_subgroupOf.1 hconj'
  refine ⟨c * ((gg * y₀ * gg⁻¹ : ↥CKs7) : Equiv.Perm (Fin 820)) * c⁻¹, (hmemR' _).1 hr', ?_⟩
  have h1 : c * ((gg * y₀ * gg⁻¹ : ↥CKs7) : Equiv.Perm (Fin 820)) * c⁻¹ =
      (MulAut.conj c) ((gg * y₀ * gg⁻¹ : ↥CKs7) : Equiv.Perm (Fin 820)) := rfl
  rw [h1, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  have h2 : (gg * y₀ * gg⁻¹ : ↥CKs7) = (MulAut.conj gg) y₀ := rfl
  rw [h2, MulEquiv.orderOf_eq]
  show orderOf (⟨y8Perm, y8_mem_CKs7⟩ : ↥CKs7) = 8
  rw [Subgroup.orderOf_mk]
  exact y8_orderOf

end Inv7

section Pairs

theorem pair_facts : ∀ i < 3,
    isInvA 820 xiArrs[i]! (invCand 820 xiArrs[i]!) = true ∧
    eqA 820 (compA 820 xiArrs[i]! xiArrs[i]!) (idA 820) = true ∧
    inP (compA 820 xiArrs[i]! (invCand 820 (tArr 7))) = true ∧
    eqA 820 (compA 820 xiArrs[i]! ks8Reps[5 + i]!)
      (compA 820 (invCand 820 ks8Reps[5 + i]!) xiArrs[i]!) = true ∧
    countW (invRelW (tArr 7) ks8Reps[5 + i]! (invCand 820 ks8Reps[5 + i]!)) blocks [] =
      pairNum[i]! ∧ centKs2 ks8Reps[5 + i]! xiArrs[i]! = pairCent[i]! := by
  have h := Certificates.certificate27828.2.1
  simp only [pairCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  intro i hi
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h i hi
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem rep_xi {i : ℕ} (hi : i < 3) : Rep 820 xiArrs[i]! (xiPerm i) :=
  (rep_permOfArr (pair_facts i hi).1).1

theorem xi_inCos {i : ℕ} (hi : i < 3) : InCos 7 (xiPerm i) :=
  (inP_iff (rep_compA (rep_xi hi) (rep_tArr_inv (by norm_num : 7 < 8)))).1 (pair_facts i hi).2.2.1

theorem xi_mem {i : ℕ} (hi : i < 3) : xiPerm i ∈ U43ExtStar :=
  mem_Ks_iff.2 ⟨7, by norm_num, Or.inr (Or.inr (Or.inr rfl)), xi_inCos hi⟩

theorem xi_sq {i : ℕ} (hi : i < 3) : xiPerm i * xiPerm i = 1 :=
  (eqA_iff (rep_compA (rep_xi hi) (rep_xi hi)) rep_idA).1 (pair_facts i hi).2.1

theorem xi_rel {i : ℕ} (hi : i < 3) :
    xiPerm i * ks8Perm (5 + i) = (ks8Perm (5 + i))⁻¹ * xiPerm i :=
  (eqA_iff (rep_compA (rep_xi hi) (rep_ks8 (by omega : 5 + i < 8)))
    (rep_compA (rep_ks8_inv (by omega : 5 + i < 8)) (rep_xi hi))).1 (pair_facts i hi).2.2.2.1

theorem pair_orbit {i : ℕ} (hi : i < 3) {ξ₀ : ↥U43ExtStar}
    (hξ₀ : ξ₀ ∈ Xi7 (ks8Perm (5 + i)) (ks8Perm (5 + i))⁻¹) :
    ∃ h : ↥U43ExtStar, (h : Equiv.Perm (Fin 820)) * ks8Perm (5 + i) =
        ks8Perm (5 + i) * h ∧
      (ξ₀ : Equiv.Perm (Fin 820)) = h * xiPerm i * (h : Equiv.Perm (Fin 820))⁻¹ := by
  have hj : 5 + i < 8 := by omega
  set Vi : ↥U43ExtStar := ks8Elt (5 + i) hj with hVi
  set ξi : ↥U43ExtStar := ⟨xiPerm i, xi_mem hi⟩ with hξi
  have hξiX : ξi ∈ Xi7 (ks8Perm (5 + i)) (ks8Perm (5 + i))⁻¹ :=
    ⟨xi_inCos hi, xi_sq hi, xi_rel hi⟩
  have hX : ∀ h ∈ centralizer ({Vi} : Set ↥U43ExtStar), ∀ g ∈ Xi7 (ks8Perm (5 + i))
      (ks8Perm (5 + i))⁻¹, h * g * h⁻¹ ∈ Xi7 (ks8Perm (5 + i)) (ks8Perm (5 + i))⁻¹ := by
    intro h hh g hg
    have hhV : (h : Equiv.Perm (Fin 820)) * ks8Perm (5 + i) = ks8Perm (5 + i) * h :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh)
    obtain ⟨hg1, hg2, hg3⟩ := hg
    refine ⟨inCos_conj (by norm_num) (Or.inr (Or.inr (Or.inr rfl))) h.2 hg1, ?_, ?_⟩
    · show (h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹ *
        ((h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹) = 1
      calc (h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹ *
          ((h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹)
          = (h : Equiv.Perm (Fin 820)) * (g * g) * (h : Equiv.Perm (Fin 820))⁻¹ := by group
        _ = 1 := by rw [hg2]; group
    · show (h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹ * ks8Perm (5 + i) =
        (ks8Perm (5 + i))⁻¹ * ((h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹)
      have hVinv : (h : Equiv.Perm (Fin 820)) * (ks8Perm (5 + i))⁻¹ =
          (ks8Perm (5 + i))⁻¹ * h := by
        have := congrArg (fun y => (ks8Perm (5 + i))⁻¹ * y * (ks8Perm (5 + i))⁻¹) hhV
        simpa [mul_assoc] using this.symm
      calc (h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹ * ks8Perm (5 + i)
          = (h : Equiv.Perm (Fin 820)) * ((g : Equiv.Perm (Fin 820)) * ks8Perm (5 + i)) *
            (h : Equiv.Perm (Fin 820))⁻¹ := by
            have : (h : Equiv.Perm (Fin 820))⁻¹ * ks8Perm (5 + i) =
                ks8Perm (5 + i) * (h : Equiv.Perm (Fin 820))⁻¹ := by
              have := congrArg (fun y => (h : Equiv.Perm (Fin 820))⁻¹ * y *
                (h : Equiv.Perm (Fin 820))⁻¹) hhV
              simpa [mul_assoc] using this.symm
            calc (h : Equiv.Perm (Fin 820)) * g * (h : Equiv.Perm (Fin 820))⁻¹ * ks8Perm (5 + i)
                = (h : Equiv.Perm (Fin 820)) * g * ((h : Equiv.Perm (Fin 820))⁻¹ *
                  ks8Perm (5 + i)) := by group
              _ = (h : Equiv.Perm (Fin 820)) * g * (ks8Perm (5 + i) *
                  (h : Equiv.Perm (Fin 820))⁻¹) := by rw [this]
              _ = _ := by group
        _ = (h : Equiv.Perm (Fin 820)) * ((ks8Perm (5 + i))⁻¹ * g) * (h : Equiv.Perm (Fin 820))⁻¹ := by
            rw [hg3]
        _ = _ := by
            calc (h : Equiv.Perm (Fin 820)) * ((ks8Perm (5 + i))⁻¹ * g) *
                (h : Equiv.Perm (Fin 820))⁻¹
                = ((h : Equiv.Perm (Fin 820)) * (ks8Perm (5 + i))⁻¹) * g *
                  (h : Equiv.Perm (Fin 820))⁻¹ := by group
              _ = (ks8Perm (5 + i))⁻¹ * h * g * (h : Equiv.Perm (Fin 820))⁻¹ := by rw [hVinv]
              _ = _ := by group
  have hcentH : Nat.card ↥(centralizer ({Vi} : Set ↥U43ExtStar)) = ks8Cent[5 + i]! :=
    card_centralizer_ks8 hj
  have hcardX : Nat.card ↥(Xi7 (ks8Perm (5 + i)) (ks8Perm (5 + i))⁻¹) = pairNum[i]! := by
    rw [card_Xi7 (rep_ks8 hj) (rep_ks8_inv hj)]
    exact (pair_facts i hi).2.2.2.2.1
  have hcardI : Nat.card ↥(centralizer ({Vi} : Set ↥U43ExtStar) ⊓
      centralizer ({ξi} : Set ↥U43ExtStar)) = pairCent[i]! := by
    rw [← (pair_facts i hi).2.2.2.2.2, ← card_cent_Ks2 (rep_ks8 hj) (rep_xi hi)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  have harith : ks8Cent[5 + i]! = pairNum[i]! * pairCent[i]! := pair_arith i hi
  obtain ⟨h, hh, hξ⟩ := single_orbit (centralizer ({Vi} : Set ↥U43ExtStar))
    (Xi7 (ks8Perm (5 + i)) (ks8Perm (5 + i))⁻¹) hX hξiX
    (by rw [hcentH, hcardX, hcardI, harith]) ξ₀ hξ₀
  refine ⟨h, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh), ?_⟩
  exact congrArg Subtype.val hξ

theorem d16_facts :
    isInvA 820 d16A (invCand 820 d16A) = true ∧ isInvA 820 d16B (invCand 820 d16B) = true ∧
    inP (compA 820 d16A (invCand 820 (tArr 5))) = true ∧
    inP (compA 820 d16B (invCand 820 (tArr 5))) = true ∧
    eqA 820 (powA 820 d16A 8) (idA 820) = true ∧ eqA 820 (powA 820 d16A 4) (idA 820) = false ∧
    eqA 820 (compA 820 d16B d16B) (idA 820) = true ∧
    eqA 820 (compA 820 d16B d16A) (compA 820 (invCand 820 d16A) d16B) = true ∧
    (∀ j < 8, eqA 820 d16B (powA 820 d16A j) = false) ∧
    (eqA 820 (compA 820 d16A ks8Reps[7]!) (compA 820 ks8Reps[7]! d16A) = true ∧
      eqA 820 (compA 820 d16B ks8Reps[7]!) (compA 820 ks8Reps[7]! d16B) = true) ∧
    (eqA 820 (compA 820 d16A xiArrs[2]!) (compA 820 xiArrs[2]! d16A) = true ∧
      eqA 820 (compA 820 d16B xiArrs[2]!) (compA 820 xiArrs[2]! d16B) = true) := by
  have h := Certificates.certificate27828.2.2
  simp only [d16Check, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun j hj => ?_, h10, h11⟩
  have := h9 j hj
  simpa using this

theorem rep_d16a : Rep 820 d16A d16a := (rep_permOfArr d16_facts.1).1

theorem rep_d16b : Rep 820 d16B d16b := (rep_permOfArr d16_facts.2.1).1

theorem d16a_inCos : InCos 5 d16a :=
  (inP_iff (rep_compA rep_d16a (rep_tArr_inv (by norm_num : 5 < 8)))).1 d16_facts.2.2.1

theorem d16b_inCos : InCos 5 d16b :=
  (inP_iff (rep_compA rep_d16b (rep_tArr_inv (by norm_num : 5 < 8)))).1 d16_facts.2.2.2.1

theorem d16a_mem : d16a ∈ U43ExtStar :=
  mem_Ks_iff.2 ⟨5, by norm_num, Or.inr (Or.inr (Or.inl rfl)), d16a_inCos⟩

theorem d16b_mem : d16b ∈ U43ExtStar :=
  mem_Ks_iff.2 ⟨5, by norm_num, Or.inr (Or.inr (Or.inl rfl)), d16b_inCos⟩

theorem d16a_orderOf : orderOf d16a = 8 := by
  rw [orderOf_eq_eight_iff]
  refine ⟨(eqA_iff (rep_powA rep_d16a 8) rep_idA).1 d16_facts.2.2.2.2.1, fun h => ?_⟩
  have h4 := d16_facts.2.2.2.2.2.1
  rw [(eqA_iff (rep_powA rep_d16a 4) rep_idA).2 h] at h4
  exact Bool.noConfusion h4

theorem d16b_sq : d16b * d16b = 1 :=
  (eqA_iff (rep_compA rep_d16b rep_d16b) rep_idA).1 d16_facts.2.2.2.2.2.2.1

theorem d16b_rel : d16b * d16a * d16b⁻¹ = d16a⁻¹ := by
  have h : d16b * d16a = d16a⁻¹ * d16b :=
    (eqA_iff (rep_compA rep_d16b rep_d16a)
      (rep_compA (rep_inv_of_isInvA rep_d16a d16_facts.1) rep_d16b)).1 d16_facts.2.2.2.2.2.2.2.1
  rw [h]
  have : d16b⁻¹ = d16b := inv_eq_of_mul_eq_one_right d16b_sq
  rw [this]
  calc d16a⁻¹ * d16b * d16b = d16a⁻¹ * (d16b * d16b) := by group
    _ = d16a⁻¹ := by rw [d16b_sq, mul_one]

theorem d16b_not_mem : d16b ∉ zpowers d16a := by
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf, d16a_orderOf] at h
  obtain ⟨j, hj, hjb⟩ := Finset.mem_image.1 h
  have hj8 : j < 8 := Finset.mem_range.1 hj
  have h1 := d16_facts.2.2.2.2.2.2.2.2.1 j hj8
  have h2 := (eqA_iff rep_d16b (rep_powA rep_d16a j)).2 hjb.symm
  rw [h2] at h1
  exact Bool.noConfusion h1

theorem d16a_comm_v : d16a * ks8Perm 7 = ks8Perm 7 * d16a :=
  (eqA_iff (rep_compA rep_d16a (rep_ks8 (by norm_num))) (rep_compA (rep_ks8 (by norm_num))
    rep_d16a)).1 d16_facts.2.2.2.2.2.2.2.2.2.1.1

theorem d16b_comm_v : d16b * ks8Perm 7 = ks8Perm 7 * d16b :=
  (eqA_iff (rep_compA rep_d16b (rep_ks8 (by norm_num))) (rep_compA (rep_ks8 (by norm_num))
    rep_d16b)).1 d16_facts.2.2.2.2.2.2.2.2.2.1.2

theorem d16a_comm_xi : d16a * xiPerm 2 = xiPerm 2 * d16a :=
  (eqA_iff (rep_compA rep_d16a (rep_xi (by norm_num))) (rep_compA (rep_xi (by norm_num))
    rep_d16a)).1 d16_facts.2.2.2.2.2.2.2.2.2.2.1

theorem d16b_comm_xi : d16b * xiPerm 2 = xiPerm 2 * d16b :=
  (eqA_iff (rep_compA rep_d16b (rep_xi (by norm_num))) (rep_compA (rep_xi (by norm_num))
    rep_d16b)).1 d16_facts.2.2.2.2.2.2.2.2.2.2.2

theorem D16sub_equiv : Nonempty (↥D16sub ≃* DihedralGroup 8) := by
  have := CFSG.GH74.GLS.Stage2.Local.P27.Psp4.exists_mulEquiv_dihedral 8 d16a d16b
    d16a_orderOf d16b_sq d16b_rel d16b_not_mem
  exact this

theorem card_D16sub : Nat.card ↥D16sub = 16 := by
  obtain ⟨e⟩ := D16sub_equiv
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem card_Cpair {i : ℕ} (hi : i < 3) : Nat.card ↥(Cpair i) = pairCent[i]! := by
  rw [← (pair_facts i hi).2.2.2.2.2, ← card_cent_Ks2 (rep_ks8 (by omega : 5 + i < 8)) (rep_xi hi)]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 x.2).1).1⟩,
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 x.2).1).2,
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2⟩
      invFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨x.1.2,
        Subgroup.mem_centralizer_singleton_iff.2 x.2.1⟩,
        Subgroup.mem_centralizer_singleton_iff.2 x.2.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem ks_pair_D16 {v ξ : Equiv.Perm (Fin 820)} (hv : v ∈ U43ExtStar) (hv8 : orderOf v = 8)
    (hv7 : InCos 7 v) (hξ : ξ ∈ U43ExtStar) (hξ2 : ξ * ξ = 1) (hξ7 : InCos 7 ξ)
    (hrel : ξ * v = v⁻¹ * ξ) {S' : Subgroup (Equiv.Perm (Fin 820))} (hS : S' ≤ U43ExtStar)
    (hc1 : ∀ r ∈ S', r * v = v * r) (hc2 : ∀ r ∈ S', r * ξ = ξ * r) (hcard : Nat.card ↥S' = 16) :
    Nonempty (↥S' ≃* DihedralGroup 8) := by
  classical
  obtain ⟨j, hj, hcos, c, hcK, hvc, -⟩ := ks8_classes hv hv8
  have hjk : ks8Coset[j]! = 7 := inCos_unique (ks8_coset_lt j hj).1 (by norm_num) hcos hv7
  obtain ⟨i, rfl⟩ : ∃ i, j = 5 + i := ⟨j - 5, by have := ks8Coset_seven j hj hjk; omega⟩
  have hi : i < 3 := by omega
  have hVmem := ks8_mem hj
  have hV0 : ks8Perm (5 + i) = c⁻¹ * v * c := by
    rw [hvc]; group
  have hcinv : c⁻¹ ∈ U43ExtStar := U43ExtStar.inv_mem hcK
  have hξ₀mem : c⁻¹ * ξ * c ∈ U43ExtStar :=
    U43ExtStar.mul_mem (U43ExtStar.mul_mem hcinv hξ) hcK
  have hξ₀ : (⟨c⁻¹ * ξ * c, hξ₀mem⟩ : ↥U43ExtStar) ∈
      Xi7 (ks8Perm (5 + i)) (ks8Perm (5 + i))⁻¹ := by
    refine ⟨?_, ?_, ?_⟩
    · have := inCos_conj (k := 7) (by norm_num) (Or.inr (Or.inr (Or.inr rfl))) hcinv hξ7
      simpa using this
    · show c⁻¹ * ξ * c * (c⁻¹ * ξ * c) = 1
      calc c⁻¹ * ξ * c * (c⁻¹ * ξ * c) = c⁻¹ * (ξ * ξ) * c := by group
        _ = 1 := by rw [hξ2]; group
    · show c⁻¹ * ξ * c * ks8Perm (5 + i) = (ks8Perm (5 + i))⁻¹ * (c⁻¹ * ξ * c)
      rw [hV0]
      calc c⁻¹ * ξ * c * (c⁻¹ * v * c) = c⁻¹ * (ξ * v) * c := by group
        _ = c⁻¹ * (v⁻¹ * ξ) * c := by rw [hrel]
        _ = (c⁻¹ * v * c)⁻¹ * (c⁻¹ * ξ * c) := by group
  obtain ⟨h, hhV, hξh⟩ := pair_orbit hi hξ₀
  have hdmem : c * (h : Equiv.Perm (Fin 820)) ∈ U43ExtStar := U43ExtStar.mul_mem hcK h.2
  set d : Equiv.Perm (Fin 820) := c * (h : Equiv.Perm (Fin 820)) with hd
  have hdv : d * ks8Perm (5 + i) = v * d := by
    calc d * ks8Perm (5 + i) = c * ((h : Equiv.Perm (Fin 820)) * ks8Perm (5 + i)) := by
          rw [hd]; group
      _ = c * (ks8Perm (5 + i) * (h : Equiv.Perm (Fin 820))) := by rw [hhV]
      _ = (c * ks8Perm (5 + i) * c⁻¹) * (c * (h : Equiv.Perm (Fin 820))) := by group
      _ = v * d := by rw [← hvc, hd]
  have hdξ : d * xiPerm i = ξ * d := by
    have h1 : c⁻¹ * ξ * c = (h : Equiv.Perm (Fin 820)) * xiPerm i * (h : Equiv.Perm (Fin 820))⁻¹ := hξh
    rw [hd]
    calc c * (h : Equiv.Perm (Fin 820)) * xiPerm i
        = c * ((h : Equiv.Perm (Fin 820)) * xiPerm i * (h : Equiv.Perm (Fin 820))⁻¹) *
          (h : Equiv.Perm (Fin 820)) := by group
      _ = c * (c⁻¹ * ξ * c) * (h : Equiv.Perm (Fin 820)) := by rw [h1]
      _ = ξ * (c * (h : Equiv.Perm (Fin 820))) := by group
  set S₁ : Subgroup (Equiv.Perm (Fin 820)) := S'.map (MulAut.conj d⁻¹).toMonoidHom with hS₁
  have hmemS₁ : ∀ x, x ∈ S₁ ↔ d * x * d⁻¹ ∈ S' := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hr
    · intro hx
      exact ⟨d * x * d⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hS₁Ks : S₁ ≤ U43ExtStar := by
    intro x hx
    have h1 := hS ((hmemS₁ x).1 hx)
    have := U43ExtStar.mul_mem (U43ExtStar.mul_mem (U43ExtStar.inv_mem hdmem) h1) hdmem
    simpa [mul_assoc] using this
  have hS₁card : Nat.card ↥S₁ = 16 := by
    rw [hS₁, Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective, hcard]
  have hS₁V : ∀ x ∈ S₁, x * ks8Perm (5 + i) = ks8Perm (5 + i) * x := by
    intro x hx
    have h1 := hc1 _ ((hmemS₁ x).1 hx)
    have hvd : v = d * ks8Perm (5 + i) * d⁻¹ := by
      have := hdv
      calc v = v * d * d⁻¹ := by group
        _ = d * ks8Perm (5 + i) * d⁻¹ := by rw [← hdv]
    rw [hvd] at h1
    have h2 : d * (x * ks8Perm (5 + i)) * d⁻¹ = d * (ks8Perm (5 + i) * x) * d⁻¹ := by
      calc d * (x * ks8Perm (5 + i)) * d⁻¹
          = d * x * d⁻¹ * (d * ks8Perm (5 + i) * d⁻¹) := by group
        _ = d * ks8Perm (5 + i) * d⁻¹ * (d * x * d⁻¹) := h1
        _ = d * (ks8Perm (5 + i) * x) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hS₁ξ : ∀ x ∈ S₁, x * xiPerm i = xiPerm i * x := by
    intro x hx
    have h1 := hc2 _ ((hmemS₁ x).1 hx)
    have hξd : ξ = d * xiPerm i * d⁻¹ := by
      calc ξ = ξ * d * d⁻¹ := by group
        _ = d * xiPerm i * d⁻¹ := by rw [← hdξ]
    rw [hξd] at h1
    have h2 : d * (x * xiPerm i) * d⁻¹ = d * (xiPerm i * x) * d⁻¹ := by
      calc d * (x * xiPerm i) * d⁻¹
          = d * x * d⁻¹ * (d * xiPerm i * d⁻¹) := by group
        _ = d * xiPerm i * d⁻¹ * (d * x * d⁻¹) := h1
        _ = d * (xiPerm i * x) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hS₁C : S₁ ≤ Cpair i := fun x hx =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hS₁Ks hx,
      Subgroup.mem_centralizer_singleton_iff.2 (hS₁V x hx)⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (hS₁ξ x hx)⟩
  have hdvd : 16 ∣ pairCent[i]! := by
    rw [← card_Cpair hi, ← hS₁card]
    exact Subgroup.card_dvd_of_le hS₁C
  have hi2 : i = 2 := pairCent_sixteen i hi hdvd
  subst hi2
  have hCcard : Nat.card ↥(Cpair 2) = 16 := by
    rw [card_Cpair (by norm_num)]
    decide
  have hS₁eq : S₁ = Cpair 2 := Subgroup.eq_of_le_of_card_ge hS₁C (by rw [hCcard, hS₁card])
  have hDle : D16sub ≤ Cpair 2 := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d16a_mem,
        Subgroup.mem_centralizer_singleton_iff.2 d16a_comm_v⟩,
        Subgroup.mem_centralizer_singleton_iff.2 d16a_comm_xi⟩
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d16b_mem,
        Subgroup.mem_centralizer_singleton_iff.2 d16b_comm_v⟩,
        Subgroup.mem_centralizer_singleton_iff.2 d16b_comm_xi⟩
  have hDeq : D16sub = Cpair 2 :=
    Subgroup.eq_of_le_of_card_ge hDle (by rw [hCcard, card_D16sub])
  obtain ⟨e⟩ := D16sub_equiv
  have e1 : ↥S₁ ≃* ↥D16sub := MulEquiv.subgroupCongr (hS₁eq.trans hDeq.symm)
  exact ⟨(Subgroup.equivMapOfInjective S' (MulAut.conj d⁻¹).toMonoidHom
    (MulAut.conj d⁻¹).injective).trans (e1.trans e)⟩

end Pairs

end CFSG.EvenSporadicStandard.Fin76b.U16
