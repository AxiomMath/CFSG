module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadicBase
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant
  isoInvariant_card_quotient_center)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace QSporadic

theorem suz_qFree :
    QFree .Suz := by
  intro D _ _ hD hs n α J d
  obtain ⟨e⟩ := hs
  have hX : T_U3 n (J ⧸ center J) := ⟨d.two_le, d.model⟩
  by_cases hα : α ∈ inner D
  · refine false_of_inner_comps hD d hα (isoInvariant_card_quotient_center {20160}) ?_
      fun t ht B hB =>
        CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t
          ht B hB
    rw [Set.mem_singleton_iff]
    exact SporadicBender.ne_of_check_U3 hX (e := 6) (h := 315) (by norm_num) (by decide)
      (by decide)
  · rcases Sporadic.suz_outer_card e α d.orderOf_eq hα with hc | hc
    · exact SporadicBender.not_dvd_of_check_U3 hX (e := 7) (h := 1485) (by norm_num) (by decide)
        (by decide) (hc ▸ d.card_quotient_dvd_card_fixed)
    · exact SporadicBender.not_dvd_of_check_U3 hX (e := 8) (h := 4725) (by norm_num) (by decide)
        (by decide) (hc ▸ d.card_quotient_dvd_card_fixed)

open CFSG.Sporadic.RuSchreier in
open CFSG.ComponentClassification.RestrictedStd.Spor (isoInvariant_not_three_dvd
  compsSatisfy_centralizer_of_mulEquiv ru_centralizerIn_comps mem_inner_of_mulEquiv) in
theorem ru_qFree :
    QFree .Ru := by
  have hinner : ∀ (D : Type) [Group D], Nonempty (D ≃* NativeSporadic.Carrier .Ru) →
      ∀ α : MulAut D, α ∈ inner D :=
    fun D _ ⟨e⟩ α => mem_inner_of_mulEquiv (e.trans ruEquivP) mulAut_inner α
  have h3 : ∀ (n : ℕ) (X : Type) [Group X], LieModel (X ⧸ center X) .PSU 3 2 n →
      ¬ ¬ 3 ∣ Nat.card X := fun n X _ hm =>
    not_not_intro ((three_dvd_card_of_lieModel_PSU3 hm).trans
      (Subgroup.card_quotient_dvd_card (center X)))
  exact qFree_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    (fun n X _ _ hm => ⟨h3 n X hm, h3 n X hm⟩)
    (fun _ _ _ _ ⟨e⟩ t ht => compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd
      ru_centralizerIn_comps (e.trans ruEquivP) t ht)
    (fun G _ _ _ hG β _ hβ => absurd (hinner G hG β) hβ)

theorem qc_inf_centralizer_eq_bot {D : Type} [Group D] [Finite D] {n : ℕ} {α : MulAut D}
    {J : Subgroup D} (d : QFixedRootDatum D n α J) (hout : α ∉ inner D) {t : D} (htJ : t ∈ J)
    (hcore : CFSG.oddCore ↥(α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer ({t} : Set D)) = ⊥) :
    α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (J : Set D) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D) with hCdef
  have hJC : J ≤ C := d.le_fixed
  have hnorm : ∀ c ∈ C, ∀ s ∈ J, c * s * c⁻¹ ∈ J := by
    intro c hc s hs
    have := d.normal.conj_mem ⟨s, hJC hs⟩ (by rw [mem_subgroupOf]; exact hs) ⟨c, hc⟩
    rwa [mem_subgroupOf] at this
  set Z := C ⊓ centralizer (J : Set D) with hZdef
  have hZodd : Odd (Nat.card Z) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 hev
    have hP : zpowers (z : D) ≤ C ⊓ centralizer (J : Set D) := zpowers_le.2 z.2
    have hPp : IsPGroup 2 (zpowers (z : D)) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hbot := (d.rankOne _ hP hPp).2 hout
    have hz1 : (z : D) = 1 := by
      have : (z : D) ∈ zpowers (z : D) := mem_zpowers _
      rwa [hbot, mem_bot] at this
    rw [show z = 1 from Subtype.ext hz1, orderOf_one] at hz
    omega
  have hZle : Z ≤ C ⊓ centralizer ({t} : Set D) := by
    intro z hz
    refine mem_inf.2 ⟨(mem_inf.1 hz).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.1 (mem_inf.1 hz).2) t htJ).symm
  have hZn : (Z.subgroupOf (C ⊓ centralizer ({t} : Set D))).Normal := by
    refine ⟨fun z hz c => ?_⟩
    rw [mem_subgroupOf] at hz ⊢
    obtain ⟨hzC, hzS⟩ := mem_inf.1 hz
    have hcC : (c : D) ∈ C := (mem_inf.1 c.2).1
    refine mem_inf.2 ⟨?_, ?_⟩
    · simp only [coe_mul, coe_inv]
      exact C.mul_mem (C.mul_mem hcC hzC) (C.inv_mem hcC)
    · rw [mem_centralizer_iff]
      intro s hs
      have hs' : (c : D)⁻¹ * s * (c : D) ∈ J := by
        have := hnorm _ (C.inv_mem hcC) s hs
        rwa [inv_inv] at this
      have h1 := (mem_centralizer_iff.1 hzS) _ hs'
      simp only [coe_mul, coe_inv]
      calc s * ((c : D) * z * (c : D)⁻¹)
          = (c : D) * ((c : D)⁻¹ * s * (c : D) * z) * (c : D)⁻¹ := by group
        _ = (c : D) * (z * ((c : D)⁻¹ * s * (c : D))) * (c : D)⁻¹ := by rw [h1]
        _ = (c : D) * z * (c : D)⁻¹ * s := by group
  have hle : Z.subgroupOf (C ⊓ centralizer ({t} : Set D)) ≤
      CFSG.oddCore ↥(C ⊓ centralizer ({t} : Set D)) :=
    le_sSup ⟨hZn, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv]; exact hZodd⟩
  rw [hcore, le_bot_iff, subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hZle] at hle
  exact hle

theorem qc_on_outer_center_eq_bot
    {D : Type} [Group D] [Finite D] (hON : NativeSporadic.IsSporadic D .ONan) {n : ℕ}
    {α : MulAut D} {J : Subgroup D} (d : QFixedRootDatum D n α J) (hout : α ∉ inner D) :
    center J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card J :=
    (dvd_pow_self 2 (by have := d.two_le; omega : 3 * n ≠ 0)).trans d.two_pow_dvd_card
  obtain ⟨s, hs2⟩ : ∃ s : J, orderOf s = 2 := exists_prime_orderOf_dvd_card' 2 h2
  have htJ : (s : D) ∈ J := s.2
  have ht : orderOf (s : D) = 2 := by rw [Subgroup.orderOf_coe, hs2]
  obtain ⟨hcore, -⟩ := SporadicBender.on_outer_fixed_centralizer hON d.orderOf_eq hout ht
    (d.le_fixed htJ)
  have hB := qc_inf_centralizer_eq_bot d hout htJ hcore
  rw [eq_bot_iff]
  intro z hz
  have hzZ : (z : D) ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (J : Set D) := by
    refine mem_inf.2 ⟨d.le_fixed z.2, mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val ((mem_center_iff.1 hz) ⟨h, hh⟩)
  rw [hB, mem_bot] at hzZ
  exact mem_bot.2 (Subtype.ext hzZ)

open CFSG.Sporadic.ONOddCore
  (cti_on_involution_local_components_projective_linear_quotient_order) in
theorem on_qFree :
    QFree .ONan := by
  intro D _ _ hD hs n α J d
  by_cases hα : α ∈ inner D
  · refine false_of_inner_comps hD d hα (isoInvariant_card_quotient_center {20160}) ?_
      fun t ht B hB => Set.mem_singleton_iff.2
        (cti_on_involution_local_components_projective_linear_quotient_order hs t ht B hB)
    rw [Set.mem_singleton_iff]
    exact SporadicBender.ne_of_check_U3 (⟨d.two_le, d.model⟩ : T_U3 n (J ⧸ center J)) (e := 6)
      (h := 315) (by norm_num) (by decide) (by decide)
  · exact SporadicBender.on_outer_U3_false hs
      (d.toFixedRootDatumOf (qc_on_outer_center_eq_bot hs d hα)) hα

end QSporadic

end CFSG.LocalAnalysis.EvenBN.GMSK
