module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSocle
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open MulAction Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_isPrimePow_twentyOne : ¬ IsPrimePow 21 := fun h => by
  have := (Nat.Coprime.isPrimePow_dvd_mul (by norm_num : Nat.Coprime 3 7) h).1 (by norm_num)
  omega

theorem false_of_two_pretransitive
    {P Ω Q : Type} [Group P] [Finite P] [MulAction P Ω]
    [FaithfulSMul P Ω] [Finite Ω] [Group Q] [IsSimpleGroup Q] (hΩ : Nat.card Ω = 21)
    (h2 : IsMultiplyPretransitive P Ω 2) (hdvd : Nat.card P ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7)
    (hge : 20160 * 12 < Nat.card P)
    (hcat : ∀ T : Subgroup P, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      CFSG.Blueprint.Catalog T)
    (ι : Q →* P) (hι : Function.Injective ι) (hQ : Nat.card Q = 20160)
    (hQout : Nat.card (Outer Q) ∣ 12) : False := by
  have : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
  have : IsPreprimitive P Ω := isPreprimitive_of_is_two_pretransitive h2
  have h49 : ¬ 7 ^ 2 ∣ Nat.card P := fun h49 => absurd (h49.trans hdvd) (by norm_num)
  obtain ⟨T, hTn, hTs, hTnonab, hTdvd, -, hTc⟩ := exists_simple_normal_of_isPreprimitive
    (by norm_num : Nat.Prime 7) (by rw [hΩ]; norm_num) h49 (hΩ ▸ not_isPrimePow_twentyOne)
  have hT7 : 7 ∣ Nat.card T := (by norm_num : 7 ∣ 21).trans (hΩ ▸ hTdvd)
  have hTP : Nat.card T ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7 := (card_subgroup_dvd_card T).trans hdvd
  have hTmem := CatalogOrders.c1_card_mem (hcat T hTs hTnonab) hTnonab hTP hT7
  set K := ι.range
  let eQ : Q ≃* K := MonoidHom.ofInjective hι
  have : IsSimpleGroup K := eQ.symm.isSimpleGroup
  have hKc : Nat.card K = 20160 := by rw [← hQ]; exact (Nat.card_congr eQ.toEquiv).symm
  have hKT : K ≤ T := by
    have hne : T ⊓ K ≠ ⊥ := fun hb => by
      have h1 : 7 * 20160 ∣ Nat.card T * Nat.card K := Nat.mul_dvd_mul hT7 (hKc ▸ dvd_rfl)
      exact absurd ((h1.trans (card_mul_card_dvd_of_inf_eq_bot hb)).trans hdvd) (by norm_num)
    rcases Subgroup.Normal.eq_bot_or_eq_top (T.subgroupOf K) with hb | ht
    · exact absurd (disjoint_iff.1 (subgroupOf_eq_bot.1 hb)) hne
    · exact subgroupOf_eq_top.1 ht
  have hTc' : Nat.card T = 20160 := by
    have hle : 20160 ≤ Nat.card T := hKc ▸ card_le_of_le hKT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTmem
    omega
  have hTK : T = K := (eq_of_le_of_card_ge hKT (by rw [hTc', hKc])).symm
  let eT : T ≃* Q := (MulEquiv.subgroupCongr hTK).trans eQ.symm
  have hO : Nat.card (Outer T) ≤ 12 := by
    rw [Nat.card_congr (ComponentClassification.OuterAutomorphisms.equivalence eT).toEquiv]
    exact Nat.le_of_dvd (by norm_num) hQout
  have hinj : Function.Injective (MulAut.conjNormal : P →* MulAut T) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ centralizer (T : Set P) := by
      rw [mem_centralizer_iff]
      intro x hx
      have := congrArg (fun φ : MulAut T => ((φ ⟨x, hx⟩ : T) : P)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rwa [hTc, mem_bot] at hgc
  have : Finite (MulAut T) :=
    Finite.of_injective (fun φ : MulAut T => (φ : T → T)) fun a b hab => MulEquiv.ext (congrFun hab)
  have hle : Nat.card P ≤ Nat.card (MulAut T) := Nat.card_le_card_of_injective _ hinj
  have hA := CatalogOrders.card_mulAut_le T
  rw [hTc'] at hA
  have : Nat.card P ≤ 20160 * 12 := hle.trans (hA.trans (Nat.mul_le_mul_left _ hO))
  omega

end CFSG.EvenSmallLie.UnitarySix.Yamada
