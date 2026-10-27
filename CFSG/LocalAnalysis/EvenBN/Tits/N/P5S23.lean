module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N
open scoped commutatorElement

section Basic

variable {Γ : Type*} [Group Γ]

theorem commImg_one_eq_bot {S : Type*} [Group S] : commImg (1 : MulAut S) = ⊥ := by
  refine le_bot_iff.1 ((closure_le _).2 ?_)
  rintro _ ⟨w, rfl⟩
  simp

theorem actFun_mul_self_eq_one (W : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (W : Set Γ))
    (hgg : g * g = 1) : actFun W g * actFun W g = 1 := by
  rw [← actFun_mul W hg hg, hgg, actFun_one]

theorem map_commImg_actFun_le (W : Subgroup Γ) {j : Γ} (hj : j ∈ normalizer (W : Set Γ)) :
    (commImg (actFun W j)).map W.subtype ≤ ⁅W, zpowers j⁆ := by
  rw [commImg, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  have h : W.subtype (w * (actFun W j w)⁻¹) = ⁅(w : Γ), j⁆ := by
    change (w : Γ) * ((actFun W j w : ↥W) : Γ)⁻¹ = _
    rw [actFun_apply_coe W hj, commutatorElement_def]
    group
  rw [SetLike.mem_coe, h]
  exact commutator_mem_commutator w.2 (mem_zpowers j)

end Basic

section Card

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem card_commImg_actFun_le (W : Subgroup Γ) {j : Γ} (hj : j ∈ normalizer (W : Set Γ)) :
    Nat.card (commImg (actFun W j)) ≤ Nat.card (⁅W, zpowers j⁆ : Subgroup Γ) :=
  (card_map_of_injective W.subtype_injective).symm.trans_le
    (card_le_of_le (map_commImg_actFun_le W hj))

theorem card_imgIn_mul_card_inf_of_le {W Sb K : Subgroup Γ} (hSN : Sb ≤ normalizer (W : Set Γ))
    (hCS : Sb ⊓ centralizer (W : Set Γ) = W) (hK : K ≤ Sb) :
    Nat.card (imgIn W K) * Nat.card (K ⊓ W : Subgroup Γ) = Nat.card K := by
  have h1 : K ⊓ centralizer (W : Set Γ) = K ⊓ W :=
    calc K ⊓ centralizer (W : Set Γ) = K ⊓ Sb ⊓ centralizer (W : Set Γ) := by rw [inf_eq_left.2 hK]
      _ = K ⊓ W := by rw [inf_assoc, hCS]
  have h2 : K ⊓ normalizer (W : Set Γ) = K := inf_eq_left.2 (hK.trans hSN)
  have h := card_imgIn_mul_card W K
  rwa [h1, h2] at h

theorem card_inf_mul_card_commImg_le {W D : Subgroup Γ} (hWab : IsElemAbelian 2 W)
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {j : Γ} (hjD : j ∈ D)
    (hjN : j ∈ normalizer (W : Set Γ)) :
    Nat.card (D ⊓ W : Subgroup Γ) * Nat.card (commImg (actFun W j)) ≤ Nat.card W := by
  have hc : ∀ a b : ↥W, a * b = b * a := fun a b => Subtype.ext (hWab.comm a.2 b.2)
  have h2 : ∀ w : ↥W, w * w = 1 := fun w => Subtype.ext (hWab.mul_self_eq_one w.2)
  rw [← card_fixSub_mul_card_commImg hc h2 (actFun W j)]
  refine Nat.mul_le_mul_right _ ?_
  let f : ↥(D ⊓ W) → ↥(fixSub (actFun W j)) := fun u =>
    ⟨⟨u, (mem_inf.1 u.2).2⟩, mem_fixSub.2 ((actFun_fixes_iff W hjN _).2 (hDc j hjD u (mem_inf.1 u.2).1))⟩
  refine Nat.card_le_card_of_injective f fun u v huv => ?_
  exact Subtype.ext (congrArg (fun x : ↥(fixSub (actFun W j)) => ((x : ↥W) : Γ)) huv)

theorem eq_or_card_lt_of_isElemAbelian {W Sb : Subgroup Γ} (hWab : IsElemAbelian 2 W)
    (hW : Nat.card W = 256) (hSN : Sb ≤ normalizer (W : Set Γ))
    (hCS : Sb ⊓ centralizer (W : Set Γ) = W)
    (hP1 : ∀ j ∈ imgIn W Sb, j * j = 1 → j ≠ 1 → 4 ≤ Nat.card (commImg (S := ↥W) j))
    (hP2 : ∀ F ≤ imgIn W Sb, IsElemAbelian 2 F → Nat.card F = 4 →
      ∃ j ∈ F, 16 ≤ Nat.card (commImg (S := ↥W) j))
    (hE2 : ∀ F ≤ imgIn W Sb, IsElemAbelian 2 F → Nat.card F ≤ 8)
    {D : Subgroup Γ} (hDS : D ≤ Sb) (hD : IsElemAbelian 2 D) : D = W ∨ Nat.card D < 256 := by
  have hcard := card_imgIn_mul_card_inf_of_le hSN hCS hDS
  have hDbar : IsElemAbelian 2 (imgIn W D) := isElemAbelian_imgIn W hD
  have hle : imgIn W D ≤ imgIn W Sb := imgIn_mono W hDS
  have h8 : Nat.card (imgIn W D) ≤ 8 := hE2 _ hle hDbar
  have hfix : ∀ j ∈ D, Nat.card (D ⊓ W : Subgroup Γ) * Nat.card (commImg (actFun W j)) ≤ 256 :=
    fun j hj => (card_inf_mul_card_commImg_le hWab (fun a ha b hb => hD.comm ha hb) hj
      (hSN (hDS hj))).trans_eq hW
  rcases Nat.lt_or_ge (Nat.card (imgIn W D)) 2 with h1 | h2
  ·
    have hpos : 0 < Nat.card (imgIn W D) := Nat.card_pos
    have hone : Nat.card (imgIn W D) = 1 := by omega
    rw [hone, one_mul] at hcard
    have hDW : D ≤ W := by
      have := eq_of_le_of_card_ge (inf_le_left : D ⊓ W ≤ D) hcard.ge
      rw [← this]
      exact inf_le_right
    by_cases hlt : Nat.card D < 256
    · exact Or.inr hlt
    · exact Or.inl (eq_of_le_of_card_ge hDW (by omega))
  · right
    rcases Nat.lt_or_ge (Nat.card (imgIn W D)) 4 with h3 | h4
    ·
      obtain ⟨x, hx, hx1⟩ : ∃ x ∈ imgIn W D, x ≠ 1 := by
        rcases bot_or_exists_ne_one (imgIn W D) with hb | hb
        · rw [hb, card_bot] at h2
          omega
        · exact hb
      obtain ⟨j, hjD, hjN, rfl⟩ := (mem_imgIn_iff W D).1 hx
      have hj4 := hP1 _ (hle hx) (actFun_mul_self_eq_one W hjN (hD.mul_self_eq_one hjD)) hx1
      have hb := hfix j hjD
      have hb' := Nat.mul_le_mul_left (Nat.card (D ⊓ W : Subgroup Γ)) hj4
      have hDW : Nat.card (D ⊓ W : Subgroup Γ) ≤ 64 := by omega
      have : Nat.card (imgIn W D) * Nat.card (D ⊓ W : Subgroup Γ) ≤ 3 * 64 :=
        Nat.mul_le_mul (by omega) hDW
      omega
    ·
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hDbar.isPGroup
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have : 2 ^ k ≤ 2 := (Nat.pow_le_pow_right (by norm_num) (by omega : k ≤ 1)).trans_eq (pow_one 2)
        omega
      have hdvd : 2 ^ 2 ∣ Nat.card (imgIn W D) := by
        rw [hk]
        exact pow_dvd_pow 2 hk2
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
      obtain ⟨F, hFle, hF4⟩ : ∃ F ≤ imgIn W D, Nat.card F = 4 :=
        ⟨K.map (imgIn W D).subtype, map_subtype_le K, by
          rw [card_map_of_injective (subtype_injective _), hK]
          norm_num⟩
      obtain ⟨x, hxF, hx16⟩ := hP2 F (hFle.trans hle) (hDbar.mono hFle) hF4
      obtain ⟨j, hjD, hjN, rfl⟩ := (mem_imgIn_iff W D).1 (hFle hxF)
      have hb := hfix j hjD
      have hb' := Nat.mul_le_mul_left (Nat.card (D ⊓ W : Subgroup Γ)) hx16
      have hDW : Nat.card (D ⊓ W : Subgroup Γ) ≤ 16 := by omega
      have : Nat.card (imgIn W D) * Nat.card (D ⊓ W : Subgroup Γ) ≤ 8 * 16 :=
        Nat.mul_le_mul h8 hDW
      omega

theorem six23 {W Sb : Subgroup Γ} (hWab : IsElemAbelian 2 W) (hW : Nat.card W = 256)
    (hWS : W ≤ Sb) (hSN : Sb ≤ normalizer (W : Set Γ)) (hCS : Sb ⊓ centralizer (W : Set Γ) = W)
    (hP1 : ∀ j ∈ imgIn W Sb, j * j = 1 → j ≠ 1 → 4 ≤ Nat.card (commImg (S := ↥W) j))
    (hP2 : ∀ F ≤ imgIn W Sb, IsElemAbelian 2 F → Nat.card F = 4 →
      ∃ j ∈ F, 16 ≤ Nat.card (commImg (S := ↥W) j))
    (hE2 : ∀ F ≤ imgIn W Sb, IsElemAbelian 2 F → Nat.card F ≤ 8) :
    maxElemAbelian2 Sb = {W} ∧
    (∀ g : Γ, W.map (MulAut.conj g).toMonoidHom ≤ Sb → W.map (MulAut.conj g).toMonoidHom = W) ∧
    (∀ j ∈ Sb, j ∉ W → j * j = 1 → 4 ≤ Nat.card (⁅W, zpowers j⁆ : Subgroup Γ)) ∧
    (∀ F : Subgroup Γ, F ≤ Sb → W ≤ F → W.relIndex F = 4 → (∀ p ∈ F, p * p ∈ W) →
      ∃ j ∈ F, j ∉ W ∧ 16 ≤ Nat.card (⁅W, zpowers j⁆ : Subgroup Γ)) ∧
    (∀ B : Subgroup Γ, B ≤ Sb → IsElemAbelian 2 B → W.relIndex B ≤ 8) := by
  have hWC : W ≤ centralizer (W : Set Γ) := le_centralizer_iff_isMulCommutative.2 hWab.1
  have key : ∀ D : Subgroup Γ, D ≤ Sb → IsElemAbelian 2 D → D = W ∨ Nat.card D < 256 :=
    fun D hDS hD => eq_or_card_lt_of_isElemAbelian hWab hW hSN hCS hP1 hP2 hE2 hDS hD
  have hmax : maxElemAbelian2 Sb = {W} := by
    ext E
    simp only [maxElemAbelian2, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hES, hE, hEmax⟩
      rcases key E hES hE with h | h
      · exact h
      · have := hEmax W hWS hWab
        omega
    · rintro rfl
      refine ⟨hWS, hWab, fun D hDS hD => ?_⟩
      rcases key D hDS hD with h | h
      · exact h ▸ le_rfl
      · omega
  refine ⟨hmax, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    have hcard : Nat.card (W.map (MulAut.conj g).toMonoidHom) = 256 := by
      rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective, hW]
    rcases key _ hg (hWab.map _) with h | h
    · exact h
    · omega
  ·
    intro j hjS hjW hjj
    have hjN := hSN hjS
    refine le_trans ?_ (card_commImg_actFun_le W hjN)
    refine hP1 _ (actFun_mem_imgIn hjS hjN) (actFun_mul_self_eq_one W hjN hjj) fun h1 => hjW ?_
    have : j ∈ Sb ⊓ centralizer (W : Set Γ) := mem_inf.2 ⟨hjS, (actFun_eq_one_iff W hjN).1 h1⟩
    rwa [hCS] at this
  ·
    intro F hFS hWF hrel hsq
    have hFbar := card_imgIn_mul_card_inf_of_le hSN hCS hFS
    rw [inf_eq_right.2 hWF] at hFbar
    have hFc := relIndex_mul_card W F
    rw [hrel, inf_eq_left.2 hWF] at hFc
    have hF4 : Nat.card (imgIn W F) = 4 := by
      have := hFbar.trans hFc.symm
      rw [hW] at this
      omega
    have hsqbar : ∀ x ∈ imgIn W F, x * x = 1 := by
      intro x hx
      obtain ⟨p, hpF, hpN, rfl⟩ := (mem_imgIn_iff W F).1 hx
      rw [← actFun_mul W hpN hpN]
      exact (actFun_eq_one_iff W (mul_mem hpN hpN)).2 (hWC (hsq p hpF))
    have hinv : ∀ x ∈ imgIn W F, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsqbar x hx)
    have hFab : IsElemAbelian 2 (imgIn W F) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [pow_two]; exact hsqbar x hx⟩
      calc (a : MulAut ↥W) * b = ((a : MulAut ↥W) * b)⁻¹ := (hinv _ (mul_mem a.2 b.2)).symm
        _ = (b : MulAut ↥W)⁻¹ * (a : MulAut ↥W)⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [hinv _ b.2, hinv _ a.2]
    obtain ⟨x, hx, hx16⟩ := hP2 _ (imgIn_mono W hFS) hFab hF4
    obtain ⟨j, hjF, hjN, rfl⟩ := (mem_imgIn_iff W F).1 hx
    refine ⟨j, hjF, fun hjW => ?_, hx16.trans (card_commImg_actFun_le W hjN)⟩
    rw [(actFun_eq_one_iff W hjN).2 (hWC hjW), commImg_one_eq_bot, card_bot] at hx16
    omega
  ·
    intro B hBS hB
    have h1 := card_imgIn_mul_card_inf_of_le hSN hCS hBS
    have h2 := relIndex_mul_card W B
    rw [inf_comm] at h2
    have hpos : 0 < Nat.card (B ⊓ W : Subgroup Γ) := Nat.card_pos
    have h3 : W.relIndex B = Nat.card (imgIn W B) := Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)
    rw [h3]
    exact hE2 _ (imgIn_mono W hBS) (isElemAbelian_imgIn W hB)

end Card

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
