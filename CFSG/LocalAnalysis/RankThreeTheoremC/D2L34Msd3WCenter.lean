module

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_inf_centralizer {W X : Subgroup G} (hWp : IsPGroup 3 W)
    (hWX : W ≤ normalizer (X : Set G)) (hX : 3 ∣ Nat.card X) :
    3 ∣ Nat.card (X ⊓ centralizer (W : Set G) : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := normalizer (X : Set G) with hN
  set S : Subgroup N := W.subgroupOf N with hS
  have hSp : IsPGroup 3 S := hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWX).symm
  have hmod := hSp.card_modEq_card_fixedPoints X
  have hsmul : ∀ (s : S) (x : X), ((s • x : X) : G) = (s : G) * x * (s : G)⁻¹ := by
    intro s x
    rfl
  have hfix : Nat.card (MulAction.fixedPoints S X) =
      Nat.card (X ⊓ centralizer (W : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), a.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
    · refine mem_centralizer_iff.mpr ?_
      intro w hw
      have hfixa := a.2 ⟨⟨w, hWX hw⟩, mem_subgroupOf.mpr hw⟩
      have := congrArg Subtype.val hfixa
      rw [hsmul] at this
      show w * (a.1 : G) = (a.1 : G) * w
      have h2 : w * (a.1 : G) * w⁻¹ = (a.1 : G) := this
      calc w * (a.1 : G) = w * (a.1 : G) * w⁻¹ * w := by group
        _ = (a.1 : G) * w := by rw [h2]
    · intro s
      apply Subtype.ext
      rw [hsmul]
      show (s : G) * x.1 * (s : G)⁻¹ = x.1
      have hsW : (s : G) ∈ W := mem_subgroupOf.mp s.2
      have hc := mem_centralizer_iff.mp x.2.2 (s : G) hsW
      calc (s : G) * x.1 * (s : G)⁻¹ = x.1 * (s : G) * (s : G)⁻¹ := by rw [hc]
        _ = x.1 := by group
  rw [hfix] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hX))

theorem card_le_three_of_isPGroup_le_sup {P₀ O Y : Subgroup G} (hP₀ : Nat.card P₀ = 3)
    (hOcop : Nat.Coprime 3 (Nat.card O)) (hPO : P₀ ≤ normalizer (O : Set G))
    (hYp : IsPGroup 3 Y) (hY : Y ≤ O ⊔ P₀) : Nat.card Y ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbot : O ⊓ P₀ = ⊥ := (Subgroup.disjoint_of_coprime_natCard
    (by rw [hP₀]; exact hOcop.symm)).eq_bot
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPO
  rw [hbot, Subgroup.card_bot, mul_one, hP₀] at hcard
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hYp
  have hdvd : 3 ^ k ∣ Nat.card (O ⊔ P₀ : Subgroup G) := hk ▸ Subgroup.card_dvd_of_le hY
  rw [hcard] at hdvd
  have hcop : Nat.Coprime (3 ^ k) (Nat.card O) := Nat.Coprime.pow_left k hOcop
  have h3 : 3 ^ k ∣ 3 := hcop.dvd_of_dvd_mul_left hdvd
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h3


theorem zmod_three_mul_self_add_one_ne_zero : ∀ x : ZMod 3, x * x + 1 ≠ 0 := by decide

theorem exists_center3_of_normal_order_three {M O W D P₀ : Subgroup G} (hWM : W ≤ M)
    (hWp : IsPGroup 3 W) (hOcop : Nat.Coprime 3 (Nat.card O))
    (hMO : M ≤ normalizer (O : Set G)) (hDW : D ≤ W) (hDN : W ≤ normalizer (D : Set G))
    (hDel : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) (hP₀W : P₀ ≤ W) (hP₀ : Nat.card P₀ = 3)
    (hnorm : M ≤ normalizer ((O ⊔ P₀ : Subgroup G) : Set G)) {s : G} (hsM : s ∈ M)
    (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D) (hs2 : ∀ d ∈ D, s ^ 2 * d * (s ^ 2)⁻¹ = d⁻¹) :
    ∃ E : Subgroup G, E ≤ W ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ w ∈ W, ∀ e ∈ E, w * e = e * w := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPO : P₀ ≤ normalizer (O : Set G) := hP₀W.trans (hWM.trans hMO)
  have hP₀p : IsPGroup 3 P₀ := IsPGroup.of_card (n := 1) (by rw [hP₀]; simp)
  have hY : Nat.card ((O ⊔ P₀ : Subgroup G) ⊓ W : Subgroup G) ≤ 3 :=
    card_le_three_of_isPGroup_le_sup hP₀ hOcop hPO (hWp.to_le inf_le_right) inf_le_left
  have hYP : P₀ = (O ⊔ P₀ : Subgroup G) ⊓ W :=
    Subgroup.eq_of_le_of_card_ge (le_inf le_sup_right hP₀W) (by rw [hP₀]; exact hY)
  have hWP : ∀ w ∈ W, ∀ p ∈ P₀, w * p * w⁻¹ ∈ P₀ := by
    intro w hw p hp
    rw [hYP]
    refine ⟨?_, W.mul_mem (W.mul_mem hw (hP₀W hp)) (W.inv_mem hw)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hnorm (hWM hw)) p).mp (Subgroup.mem_sup_right hp)
  have hWN : W ≤ normalizer (P₀ : Set G) := fun w hw => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hWP w hw x hx, fun hx => ?_⟩
    have := hWP w⁻¹ (W.inv_mem hw) _ hx
    simpa [mul_assoc] using this
  have hP₀C : P₀ ≤ centralizer (W : Set G) := by
    have hd := three_dvd_card_inf_centralizer hWp hWN (by rw [hP₀])
    have hle : Nat.card (P₀ ⊓ centralizer (W : Set G) : Subgroup G) ≤ Nat.card P₀ :=
      Subgroup.card_le_of_le inf_le_left
    have hpos : 0 < Nat.card (P₀ ⊓ centralizer (W : Set G) : Subgroup G) := Nat.card_pos
    have h3 : Nat.card (P₀ ⊓ centralizer (W : Set G) : Subgroup G) = 3 := by
      have := Nat.le_of_dvd hpos hd
      omega
    have heq : P₀ ⊓ centralizer (W : Set G) = P₀ :=
      Subgroup.eq_of_le_of_card_ge (H := P₀ ⊓ centralizer (W : Set G)) (K := P₀) inf_le_left
        (by rw [h3, hP₀])
    exact heq ▸ inf_le_right
  have hP₀D : P₀ ⊓ D = ⊥ := by
    by_contra hne
    obtain ⟨p, hp1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hpP : (p : G) ∈ P₀ := p.2.1
    have hpD : (p : G) ∈ D := p.2.2
    have hp3 : (p : G) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := P₀) (x := ⟨p, hpP⟩)
      rw [hP₀] at h
      simpa using congrArg Subtype.val h
    have hp1' : (p : G) ≠ 1 := fun h => hp1 (Subtype.ext h)
    have hpo : orderOf (p : G) = 3 := orderOf_eq_prime hp3 hp1'
    have hzP : Subgroup.zpowers (p : G) = P₀ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hpP) ?_
      rw [Nat.card_zpowers, hpo, hP₀]
    have hP₀D' : P₀ ≤ D := hzP ▸ Subgroup.zpowers_le.mpr hpD
    have hspD := hsD p hpD
    have hspO : s * p * s⁻¹ ∈ (O ⊔ P₀ : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hsM) p).mp (Subgroup.mem_sup_right hpP)
    have hY' : Nat.card ((O ⊔ P₀ : Subgroup G) ⊓ D : Subgroup G) ≤ 3 :=
      card_le_three_of_isPGroup_le_sup hP₀ hOcop hPO (hWp.to_le (inf_le_right.trans hDW))
        inf_le_left
    have hYP' : P₀ = (O ⊔ P₀ : Subgroup G) ⊓ D :=
      Subgroup.eq_of_le_of_card_ge (le_inf le_sup_right hP₀D') (by rw [hP₀]; exact hY')
    have hsp : s * p * s⁻¹ ∈ P₀ := by
      have h : s * p * s⁻¹ ∈ (O ⊔ P₀ : Subgroup G) ⊓ D := ⟨hspO, hspD⟩
      rwa [← hYP'] at h
    have hsp' : s * p * s⁻¹ ∈ Subgroup.zpowers (p : G) := by
      rw [hzP]
      exact hsp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsp'
    have h2 : s ^ 2 * p * (s ^ 2)⁻¹ = (p : G) ^ (k * k) := by
      have e1 : s ^ 2 * p * (s ^ 2)⁻¹ = s * (s * p * s⁻¹) * s⁻¹ := by
        rw [pow_two]
        group
      rw [e1, ← hk, ← conj_zpow, ← hk, ← zpow_mul]
    have h3 := hs2 p hpD
    rw [h2] at h3
    have h4 : (p : G) ^ (k * k + 1) = 1 := by
      rw [zpow_add_one, h3, inv_mul_cancel]
    have h5 := (orderOf_dvd_iff_zpow_eq_one).mpr h4
    rw [hpo] at h5
    have h6 : ((k * k + 1 : ℤ) : ZMod 3) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h5
    push_cast at h6
    exact zmod_three_mul_self_add_one_ne_zero _ h6
  obtain ⟨z, hzDC, hz1⟩ : ∃ z ∈ D ⊓ centralizer (W : Set G), z ≠ 1 := by
    have hd := three_dvd_card_inf_centralizer hWp hDN (by rw [hD9]; norm_num)
    have hne : (D ⊓ centralizer (W : Set G) : Subgroup G) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hd
      omega
    obtain ⟨z', hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨z'.1, z'.2, fun h => hz1 (Subtype.ext h)⟩
  have hzD : z ∈ D := hzDC.1
  have hzC : z ∈ centralizer (W : Set G) := hzDC.2
  have hz3 : z ^ 3 = 1 := hDel.2 z hzD
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzW : Subgroup.zpowers z ≤ W := Subgroup.zpowers_le.mpr (hDW hzD)
  have hzCW : Subgroup.zpowers z ≤ centralizer (W : Set G) := Subgroup.zpowers_le.mpr hzC
  have hzCP : z ∈ centralizer (P₀ : Set G) :=
    mem_centralizer_iff.mpr fun p hp => mem_centralizer_iff.mp hzC p (hP₀W hp)
  have hzN : Subgroup.zpowers z ≤ normalizer (P₀ : Set G) :=
    (Subgroup.zpowers_le.mpr hzCP).trans (Subgroup.centralizer_le_normalizer _)
  have hEW : P₀ ⊔ Subgroup.zpowers z ≤ W := sup_le hP₀W hzW
  have hEC : P₀ ⊔ Subgroup.zpowers z ≤ centralizer (W : Set G) := sup_le hP₀C hzCW
  have hP₀3 : ∀ p ∈ P₀, p ^ 3 = 1 := fun p hp => by
    have h := pow_card_eq_one' (G := P₀) (x := ⟨p, hp⟩)
    rw [hP₀] at h
    simpa using congrArg Subtype.val h
  refine ⟨P₀ ⊔ Subgroup.zpowers z, hEW, ?_, ?_, fun w hw e he =>
    mem_centralizer_iff.mp (hEC he) w hw⟩
  · have hE_eq : P₀ ⊔ Subgroup.zpowers z =
        Subgroup.closure ((P₀ : Set G) ∪ (Subgroup.zpowers z : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [hE_eq]
    refine CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.isElemAbelian_closure (p := 3) ?_ ?_
    · intro a ha b hb
      have haE : a ∈ P₀ ⊔ Subgroup.zpowers z := by
        rcases ha with ha | ha
        · exact Subgroup.mem_sup_left ha
        · exact Subgroup.mem_sup_right ha
      have hbE : b ∈ P₀ ⊔ Subgroup.zpowers z := by
        rcases hb with hb | hb
        · exact Subgroup.mem_sup_left hb
        · exact Subgroup.mem_sup_right hb
      exact (mem_centralizer_iff.mp (hEC haE) b (hEW hbE)).symm
    · rintro a (ha | ha)
      · exact hP₀3 a ha
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  · have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hzN
    have hinf : P₀ ⊓ Subgroup.zpowers z = ⊥ :=
      le_bot_iff.mp (hP₀D ▸ inf_le_inf_left P₀ (Subgroup.zpowers_le.mpr hzD))
    rw [hinf, Subgroup.card_bot, mul_one, hP₀, Nat.card_zpowers, hzo] at hcard
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
