module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

private theorem s888_card_sl23 : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem s888_card_of_iso {G : Type*} [Group G] {K : Subgroup G} (e : ↥K ≃* SL23) :
    Nat.card ↥K = 24 :=
  (Nat.card_congr e.toEquiv).trans s888_card_sl23

private theorem s888_eq_of_le_of_card {G : Type*} [Group G] [Finite G] {P K : Subgroup G}
    (hle : P ≤ K) (hP : Nat.card ↥P = 24) (hK : Nat.card ↥K = 24) : P = K :=
  Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem asc82FactPocketsTwo_of : Asc82FactPocketsTwo := by
  intro G _ _ X z K₁ K₂ P hz2 hK₁ hK₂ _hne hcomm hM hE₁ hE₂ hP hPle
  have hzsq : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzne : z ≠ 1 := by intro h; rw [h, orderOf_one] at hz2; omega
  have hp : Sec5Pair K₁ K₂ z :=
    { comm := fun a ha b hb => commutatorElement_eq_one_iff_mul_comm.mp (by
        have hmem : ⁅a, b⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator ha hb
        rwa [hcomm, Subgroup.mem_bot] at hmem)
      iso₁ := hE₁
      iso₂ := hE₂
      z_mem₁ := hK₁.1
      z_mem₂ := hK₂.1
      z_sq := hzsq
      z_ne := hzne }
  have hMY : K₁ ⊔ K₂ ≤ X ⊓ centralizer ({z} : Set G) := by
    rw [hM]
    exact (Subgroup.closure_le (K := X ⊓ centralizer ({z} : Set G))).2 fun _ hx => hx.1
  have hsn : (P.subgroupOf (K₁ ⊔ K₂)).IsSubnormal := by
    rw [← Subgroup.comap_inclusion_subgroupOf hMY P]
    exact Subgroup.IsSubnormal.comap (Subgroup.inclusion hMY) hP.2.2.1
  have hO : CFSG.oddCore ↥P = ⊥ := hp.oddCore_subnormal hPle hsn
  obtain ⟨eP₀⟩ := hP.2.2.2
  let eP : ↥P ≃* SL23 :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm.trans eP₀
  obtain ⟨P₂, hP₂le, hP₂sn, hP₂mem⟩ := hp.proj_subnormal hPle hsn
  have hPle' : P ≤ K₂ ⊔ K₁ := sup_comm K₁ K₂ ▸ hPle
  have hsn' : (P.subgroupOf (K₂ ⊔ K₁)).IsSubnormal := by rwa [sup_comm]
  obtain ⟨P₁, hP₁le, hP₁sn, hP₁mem⟩ := hp.symm.proj_subnormal hPle' hsn'
  obtain ⟨e₁⟩ := hE₁
  obtain ⟨e₂⟩ := hE₂
  rcases sec5_subnormal_dichotomy e₂ hP₂le hP₂sn with hP₂eq | hP₂q8
  · rcases sec5_subnormal_dichotomy e₁ hP₁le hP₁sn with hP₁eq | hP₁q8
    · exact (hp.case_full hPle eP
        (fun b hb => ((hP₂mem b).mp (by rw [hP₂eq]; exact hb)).2)
        (fun a ha => by
          obtain ⟨b, hb, hba⟩ := ((hP₁mem a).mp (by rw [hP₁eq]; exact ha)).2
          exact ⟨b, hb, by rwa [hp.comm a ha b hb]⟩)).elim
    · right
      refine s888_eq_of_le_of_card (hp.symm.case_odd hPle' eP ?_)
        (s888_card_of_iso eP) (s888_card_of_iso e₂)
      intro b hb h
      obtain ⟨a, ha, hab⟩ := h
      exact hP₁q8 b ((hP₁mem b).mpr ⟨hb, a, ha, hab⟩)
  · left
    refine s888_eq_of_le_of_card (hp.case_odd hPle eP ?_)
      (s888_card_of_iso eP) (s888_card_of_iso e₁)
    intro b hb h
    obtain ⟨a, ha, hab⟩ := h
    exact hP₂q8 b ((hP₂mem b).mpr ⟨hb, a, ha, hab⟩)

end CFSG.OddStandard.SmallF3.Omega
