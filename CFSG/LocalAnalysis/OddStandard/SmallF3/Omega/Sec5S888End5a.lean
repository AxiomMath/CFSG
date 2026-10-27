module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldY
public import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp

public section

open CFSG.Open CFSG.Goldschmidt Subgroup CFSG.GH74.GLS.Th2.P412
open CFSG.GH74.GLS.Th2.HY

namespace CFSG.OddStandard.SmallF3.Omega

private theorem s888_sup_centralizer_eq_top {Y : Type} [Group Y] [Finite Y]
    (hlayer : goldschmidtLayer Y = ⊤) {J : Subgroup Y} (hJ : IsComponentOf J ⊤) :
    J ⊔ Subgroup.centralizer (J : Set Y) = ⊤ := by
  rw [eq_top_iff, ← hlayer, goldschmidtLayer.eq_sSup]
  refine sSup_le ?_
  intro K hK
  by_cases hKJ : K = J
  · subst hKJ
    exact le_sup_left
  · have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne K J hK hJ hKJ
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans le_sup_right

private theorem s888_inf_centralizer_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hlayer : goldschmidtLayer Y = ⊤) (hZ : Subgroup.center Y = ⊥) {J : Subgroup Y}
    (hJ : IsComponentOf J ⊤) :
    J ⊓ Subgroup.centralizer (J : Set Y) = ⊥ := by
  have hZJ := GoldY.component_center_eq_bot hZ hlayer hJ
  rw [eq_bot_iff]
  rintro x ⟨hxJ, hxC⟩
  have hcenter : (⟨x, hxJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxC k k.2
  rw [hZJ, Subgroup.mem_bot] at hcenter
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcenter)

private theorem s888_le_normalizer_centralizer {Y : Type} [Group Y] (J : Subgroup Y) :
    J ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set Y) : Set Y) :=
  (Subgroup.le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _)

private theorem s888_inf_le_normalizer_inf_centralizer {Y : Type} [Group Y] (D J : Subgroup Y) :
    D ⊓ J ≤
      Subgroup.normalizer ((D ⊓ Subgroup.centralizer (J : Set Y) : Subgroup Y) : Set Y) := by
  refine (Subgroup.le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_iff.mp hx.2 y hy.2

theorem sylow_le_sup_inf_component {Y : Type} [Group Y] [Finite Y]
    (hlayer : goldschmidtLayer Y = ⊤) (hZ : Subgroup.center Y = ⊥) {J : Subgroup Y}
    (hJ : IsComponentOf J ⊤) (D : Sylow 2 Y) :
    (D : Subgroup Y) ≤
      ((D : Subgroup Y) ⊓ J) ⊔ ((D : Subgroup Y) ⊓ Subgroup.centralizer (J : Set Y)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup Y := Subgroup.centralizer (J : Set Y)
  haveI hJnormal : J.Normal := GoldY.component_normal hlayer hJ
  haveI hCnormal : C.Normal := by
    change (Subgroup.centralizer (J : Set Y)).Normal
    infer_instance
  have hD : CFSG.ABGLocalTools.IsSylowOf 2 (D : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, D.isPGroup', by rw [Subgroup.relIndex_top_right]; exact D.not_dvd_index⟩
  have hDJ : CFSG.ABGLocalTools.IsSylowOf 2 ((D : Subgroup Y) ⊓ J) J :=
    hD.inf_of_le_normalizer (N := J) le_top (by rw [Subgroup.normalizer_eq_top])
  have hDC : CFSG.ABGLocalTools.IsSylowOf 2 ((D : Subgroup Y) ⊓ C) C :=
    hD.inf_of_le_normalizer (N := C) le_top (by rw [Subgroup.normalizer_eq_top])
  have htop : J ⊔ C = ⊤ := s888_sup_centralizer_eq_top hlayer hJ
  have hbot : J ⊓ C = ⊥ := s888_inf_centralizer_eq_bot hlayer hZ hJ
  have hJN : J ≤ Subgroup.normalizer (C : Set Y) := s888_le_normalizer_centralizer J
  have hcardY : Nat.card J * Nat.card C = Nat.card Y := by
    have h := card_sup_mul_card_inf_of_le_normalizer hJN
    rw [htop, hbot, Subgroup.card_top, Subgroup.card_bot, mul_one] at h
    exact h.symm
  have hPbot : ((D : Subgroup Y) ⊓ J) ⊓ ((D : Subgroup Y) ⊓ C) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hxJ⟩, ⟨-, hxC⟩⟩
    have hx : x ∈ J ⊓ C := ⟨hxJ, hxC⟩
    rw [hbot, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr hx
  have hPN : (D : Subgroup Y) ⊓ J ≤
      Subgroup.normalizer (((D : Subgroup Y) ⊓ C : Subgroup Y) : Set Y) :=
    s888_inf_le_normalizer_inf_centralizer (D : Subgroup Y) J
  have hcardP : Nat.card ↥(((D : Subgroup Y) ⊓ J) ⊔ ((D : Subgroup Y) ⊓ C)) =
      Nat.card ↥((D : Subgroup Y) ⊓ J) * Nat.card ↥((D : Subgroup Y) ⊓ C) := by
    have h := card_sup_mul_card_inf_of_le_normalizer hPN
    rw [hPbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hfJ : Nat.card J ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, J.one_mem⟩, inferInstance⟩
  have hfC : Nat.card C ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, C.one_mem⟩, inferInstance⟩
  have hfact : (Nat.card J * Nat.card C).factorization 2 =
      (Nat.card J).factorization 2 + (Nat.card C).factorization 2 := by
    rw [Nat.factorization_mul hfJ hfC, Finsupp.add_apply]
  have hcardD : Nat.card ↥(D : Subgroup Y) = 2 ^ (Nat.card Y).factorization 2 := by
    rw [hD.card_eq, Subgroup.card_top]
  have hcard : Nat.card ↥(((D : Subgroup Y) ⊓ J) ⊔ ((D : Subgroup Y) ⊓ C)) =
      Nat.card ↥(D : Subgroup Y) := by
    rw [hcardP, hDJ.card_eq, hDC.card_eq, hcardD, ← hcardY, hfact, pow_add]
  have hPeq : ((D : Subgroup Y) ⊓ J) ⊔ ((D : Subgroup Y) ⊓ C) = (D : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (le_of_eq hcard.symm)
  exact le_of_eq hPeq.symm

theorem conj_mem_of_mem_component {Y : Type} [Group Y] [Finite Y]
    (hlayer : goldschmidtLayer Y = ⊤) (hZ : Subgroup.center Y = ⊥) {J : Subgroup Y}
    (hJ : IsComponentOf J ⊤) (D : Sylow 2 Y) {d : Y} (hd : d ∈ J)
    (hdJ : ∀ x ∈ (D : Subgroup Y) ⊓ J, d * x * d⁻¹ ∈ (D : Subgroup Y) ⊓ J) :
    ∀ x ∈ (D : Subgroup Y), d * x * d⁻¹ ∈ (D : Subgroup Y) := by
  classical
  let C : Subgroup Y := Subgroup.centralizer (J : Set Y)
  have hle := sylow_le_sup_inf_component hlayer hZ hJ D
  have hPN : (D : Subgroup Y) ⊓ J ≤
      Subgroup.normalizer (((D : Subgroup Y) ⊓ C : Subgroup Y) : Set Y) :=
    s888_inf_le_normalizer_inf_centralizer (D : Subgroup Y) J
  intro x hx
  have hxP : x ∈ ((D : Subgroup Y) ⊓ J) ⊔ ((D : Subgroup Y) ⊓ C) := hle hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hPN).mp hxP
  have hda : d * a * d⁻¹ ∈ (D : Subgroup Y) ⊓ J := hdJ a ha
  have hdb : d * b * d⁻¹ = b := by
    have hcomm : d * b = b * d := Subgroup.mem_centralizer_iff.mp hb.2 d hd
    rw [hcomm]
    simp
  have hmul : d * (a * b) * d⁻¹ = (d * a * d⁻¹) * b := by
    rw [show d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) by group, hdb]
  rw [hmul]
  exact (D : Subgroup Y).mul_mem hda.1 hb.1

end CFSG.OddStandard.SmallF3.Omega
