module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L67S
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec67_isElemAb2_conjugate {E : Subgroup G} {k : ℕ} (hE : IsElemAb2 E k) (g : G) :
    IsElemAb2 (CFSG.conjugate E g) k := by
  unfold CFSG.conjugate
  refine ⟨CFSG.Open.IsElemAbelian.map hE.1 (MulAut.conj g⁻¹).toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact hE.2

theorem sec67_part_i [Finite G] (h36 : Asc82Lemma36) (h66 : Asc82Lemma66) (h82 : Asc82Lemma82)
    (hM : Asc82Tab6M) (h67a : Asc82Lemma67a) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) (hHyp : Asc82Hyp62 G) {E : Subgroup G}
    (hE : IsElemAb2 E 8)
    (hi3 : ∀ y : G, orderOf y = 2 → (∃ α : ℤˣ, InducesTypeSome L y 6 (-1) 3 α) → IsConj t y)
    {z : G} (hz2 : orderOf z = 2) (hzL : z ∈ L) {y : G} (hy2 : orderOf y = 2)
    (hyN : y ∈ normalizer (L : Set G)) (hyz : ∀ l ∈ L, l⁻¹ * z * l ≠ y) :
    CFSG.Open.pRank 2 (E ⊓ centralizer ({y} : Set G)) < 6 := by
  by_contra h
  obtain ⟨K, hK, hKF⟩ := sec67_exists_fstar h36 h66 h82 hM hS hL6 hi3 hz2 hzL hy2 hyN hyz
  exact h67a G t L hS hL6 hHyp E hE y hy2 (not_lt.mp h) K hK hKF

theorem sec67_part_ii [Finite G] (h36 : Asc82Lemma36) (h66 : Asc82Lemma66) (h82 : Asc82Lemma82)
    (hM : Asc82Tab6M) (h67a : Asc82Lemma67a) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) (hHyp : Asc82Hyp62 G) {E : Subgroup G}
    (hE : IsElemAb2 E 8)
    (hi3 : ∀ y : G, orderOf y = 2 → (∃ α : ℤˣ, InducesTypeSome L y 6 (-1) 3 α) → IsConj t y)
    {z : G} (hz2 : orderOf z = 2) (hzL : z ∈ L) :
    ∀ s : G, IsConj t s → ∀ y ∈ E ⊓ centralizer ({s} : Set G), y ≠ 1 → IsConj z y := by
  intro s hts y hy hy1
  obtain ⟨c, hc⟩ := isConj_iff.mp hts
  have hycomm : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
  rw [← hc] at hycomm
  let E' : Subgroup G := CFSG.conjugate E c
  let y' : G := c⁻¹ * y * c
  have hE' : IsElemAb2 E' 8 := sec67_isElemAb2_conjugate hE c
  have hy'E' : y' ∈ E' := by
    change c⁻¹ * y * c ∈ CFSG.conjugate E c
    rw [mem_conjugate_iff]
    show c * (c⁻¹ * y * c) * c⁻¹ ∈ E
    rw [show c * (c⁻¹ * y * c) * c⁻¹ = y from by group]
    exact hy.1
  have hy'C : y' ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    change c⁻¹ * y * c * t = t * (c⁻¹ * y * c)
    calc c⁻¹ * y * c * t
        = c⁻¹ * (y * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * y) * c := by rw [hycomm]
      _ = t * (c⁻¹ * y * c) := by group
  have hconv : c * y' * c⁻¹ = y := by
    change c * (c⁻¹ * y * c) * c⁻¹ = y
    group
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hy1
    rw [← hconv, h]
    group
  have hy'sq : y' ^ 2 = 1 := hE'.1.2 y' hy'E'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy'2 : orderOf y' = 2 := orderOf_eq_prime hy'sq hy'1
  have hy'N : y' ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS y' hy'C)
  have hz : IsConj z y' := by
    by_contra hnc
    have hyz : ∀ l ∈ L, l⁻¹ * z * l ≠ y' := by
      intro l _ hlz
      exact hnc (isConj_iff.mpr ⟨l⁻¹, by rwa [inv_inv]⟩)
    have h6 : CFSG.Open.pRank 2 (E' ⊓ centralizer ({y'} : Set G)) < 6 :=
      sec67_part_i h36 h66 h82 hM h67a hS hL6 hHyp hE' hi3 hz2 hzL hy'2 hy'N hyz
    have hEle : E' ≤ centralizer ({y'} : Set G) := by
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (CFSG.Open.IsElemAbelian.comm hE'.1 hx hy'E')
    have h8 : 8 ≤ CFSG.Open.pRank 2 (E' ⊓ centralizer ({y'} : Set G)) :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) (le_inf le_rfl hEle) hE'.1 hE'.2
    omega
  exact hz.trans (isConj_iff.mpr ⟨c, hconv⟩)

theorem asc82Lemma67b_of (h36 : Asc82Lemma36) (h66 : Asc82Lemma66) (h82 : Asc82Lemma82)
    (hM : Asc82Tab6M) (h67a : Asc82Lemma67a) : Asc82Lemma67b := by
  intro G _ _ t L hS hL6 hHyp E hE z hz2 hzL hi3
  exact ⟨fun y hy2 hyN hyz =>
    sec67_part_i h36 h66 h82 hM h67a hS hL6 hHyp hE hi3 hz2 hzL hy2 hyN hyz,
    sec67_part_ii h36 h66 h82 hM h67a hS hL6 hHyp hE hi3 hz2 hzL⟩

end CFSG.OddStandard.SmallF3.Omega
