module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Basic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Lemma29
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem oddCore_le_fusionGen {Γ : Set G} {E : Subgroup G} (hE4 : Nat.card E = 4)
    (hEe : IsElemAbelian 2 E) (hEΓ : ∀ e ∈ E, e ≠ 1 → e ∈ Γ) :
    CFSG.Assembly.oddCore G ≤ fusionGen Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Assembly.oddCore G with hNdef
  have : CFSG.IsElementaryAbelian 2 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hEe
  let φ : E →* MulAut N := (MulAut.conjNormal (H := N)).comp E.subtype
  let _ : MulDistribMulAction E N := MulDistribMulAction.compHom N φ
  have hsmul : ∀ (a : E) (y : N), ((a • y : N) : G) = (a : G) * y * (a : G)⁻¹ := fun _ _ => rfl
  have hodd : ¬ 2 ∣ Nat.card N := fun h =>
    (Nat.not_even_iff_odd.mpr (odd_card_oddCore G)) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := E) (H := N)
    (by rw [hE4]; norm_num) hodd
  have hle : ⨆ (a : E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (zpowers a) N ≤
      (fusionGen Γ).comap N.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hya : (a : G) * y * (a : G)⁻¹ = y := by
      rw [← hsmul, hy]
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    apply centralizer_le_fusionGen (hEΓ a a.2 ha1)
    rw [mem_centralizer_singleton_iff]
    calc (y : G) * a = a * y * (a : G)⁻¹ * a := by rw [hya]
      _ = a * y := by group
  intro x hx
  have hx' : (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) := mem_top _
  rw [← hgen] at hx'
  exact hle hx'

theorem exists_four_le {R : Subgroup G} (h : 1 < Open.pRank 2 R) :
    ∃ E : Subgroup G, E ≤ R ∧ Nat.card E = 4 ∧ IsElemAbelian 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hFR, hFe, hFcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two R
  have hdvd : 2 ^ 2 ∣ Nat.card F := by
    rw [hFcard]
    exact pow_dvd_pow 2 h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨K.map F.subtype, (map_subtype_le K).trans hFR, ?_, ?_⟩
  · rw [card_map_of_injective F.subtype_injective, hK]
    norm_num
  · have := hFe.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← ha, ← hb]
      exact congrArg Subtype.val (mul_comm' a' b')
    · obtain ⟨x', -, rfl⟩ := hx
      exact hFe.2 _ x'.2

omit [Finite G] in
theorem exists_orderOf_eq_four {R : Subgroup G} (hR : IsPGroup 2 R) (h : ¬ IsElemAbelian 2 R) :
    ∃ r ∈ R, orderOf r = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : ∃ x ∈ R, x ^ 2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply h
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hcon⟩
    have hsq : ∀ y ∈ R, y * y = 1 := fun y hy => by rw [← sq]; exact hcon y hy
    have hab := hsq _ (R.mul_mem a.2 b.2)
    have ha := hsq _ a.2
    have hb := hsq _ b.2
    change (a : G) * b = b * a
    calc (a : G) * b = (a : G) * b * (b * a * (b * a)) := by
          rw [show (b : G) * a * (b * a) = 1 from hsq _ (R.mul_mem b.2 a.2), mul_one]
      _ = a * (b * b) * a * (b * a) := by group
      _ = b * a := by rw [hb, mul_one, ha, one_mul]
  obtain ⟨x, hxR, hx2⟩ := hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨x, hxR⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    apply hx2
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hk]
    calc 2 ^ k ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
      _ = 2 := pow_one 2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine ⟨x ^ 2 ^ j, R.pow_mem hxR _, ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hk]; exact pow_dvd_pow 2 (by omega)),
    hk, pow_add, Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
  norm_num

end CFSG.ComponentClassification.Asc76.L26
