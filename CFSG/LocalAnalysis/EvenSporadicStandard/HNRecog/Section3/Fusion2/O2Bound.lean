module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

private theorem natCard_elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  change Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem natCard_of_isShapeTwoTwoTimesTwoFourA5 {X : Type} [Group X]
    (h : IsShapeTwoTwoTimesTwoFourA5 X) : Nat.card X = 4 * (16 * 60) := by
  obtain ⟨Y, _, hshape, hiso⟩ := h
  obtain ⟨e⟩ := hiso
  have hY : Nat.card Y = 16 * 60 := by
    obtain ⟨N, hN, hNiso, hQiso⟩ := hshape
    haveI : N.Normal := hN
    obtain ⟨eN⟩ := hNiso
    obtain ⟨eQ⟩ := hQiso
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
      Nat.card_congr eN.toEquiv, natCard_elem2 4, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_elem2 2, hY]
  norm_num

theorem card_le_of_normal_isPGroup {G : Type} [Group G] {X : Subgroup G}
    (hX : IsShapeTwoTwoTimesTwoFourA5 ↥X) (P : Subgroup G) (hPX : P ≤ X)
    (hnorm : ∀ g ∈ X, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hP : IsPGroup 2 ↥P) : Nat.card ↥P ≤ 64 := by
  classical
  have hXcard : Nat.card ↥X = 3840 := by
    have := natCard_of_isShapeTwoTwoTimesTwoFourA5 hX
    norm_num at this
    exact this
  obtain ⟨Y, _, ⟨N, hNnorm, hNiso, hQiso⟩, ⟨e⟩⟩ := hX
  haveI : N.Normal := hNnorm
  obtain ⟨eQ⟩ := hQiso
  set π : ↥X →* alternatingGroup (Fin 5) :=
    (eQ.toMonoidHom).comp ((QuotientGroup.mk' N).comp
      ((MonoidHom.snd (Elem2 2) Y).comp e.toMonoidHom)) with hπ
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨q, hq⟩ := eQ.surjective y
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨x, hx⟩ := e.surjective (1, z)
    refine ⟨x, ?_⟩
    rw [hπ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
    simp [hz, hq]
  let P' : Subgroup ↥X := P.subgroupOf X
  have hP'card : Nat.card ↥P = Nat.card ↥P' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv).symm
  have hP'2 : IsPGroup 2 ↥P' := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  have hP'normal : P'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm (g : G) g.2 (n : G) hn
  haveI : (P'.map π).Normal := hP'normal.map π hsurj
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P'.map π) with hbot | htop
  ·
    have hleker : P' ≤ π.ker := (Subgroup.map_eq_bot_iff (H := P') (f := π)).mp hbot
    haveI : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
    haveI : Finite ↥π.ker := Subtype.finite
    have hle := Subgroup.card_le_of_le hleker
    have hker : Nat.card ↥π.ker = 64 := by
      have h := Subgroup.card_ker_mul_card_of_surjective (f := π) hsurj
      rw [hXcard, nat_card_alternatingGroup, Nat.card_fin] at h
      norm_num at h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))
    calc Nat.card ↥P = Nat.card ↥P' := hP'card
      _ ≤ Nat.card ↥π.ker := hle
      _ = 64 := hker
  ·
    exfalso
    have htop2 : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) := htop ▸ hP'2.map π
    obtain ⟨n, hn⟩ := htop2.exists_card_eq
    rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hn
    norm_num at hn
    have hnle : n ≤ 6 := by
      by_contra h
      simp only [not_le] at h
      have hle : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hn] at hle
      norm_num at hle
    interval_cases n <;> norm_num at hn

end CFSG.EvenSporadicStandard.HNRecog.Section3
