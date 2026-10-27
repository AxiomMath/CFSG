module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
open CFSG.RankThreeEvenClassification.Helpers
open Subgroup

theorem oPPrimeHull_le (p : ℕ) {X : Type*} [Group X] (A : Subgroup X) :
    oPPrimeHull p A ≤ A := by
  rw [oPPrimeHull, Subgroup.closure_le]
  exact fun _ hx => hx.1

theorem map_oPPrimeHull_eq_bot_of_not_dvd_card {G : Type*} [Group G] {B : Type*} [Group B]
    [Finite B] {d : ℕ} (hd : d.Prime) {A : Subgroup G} (φ : G →* B)
    (h : ¬ d ∣ Nat.card ((oPPrimeHull d A).map φ)) :
    (oPPrimeHull d A).map φ = ⊥ := by
  rw [Subgroup.map_eq_bot_iff]
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨hxA, k, hk⟩
  change φ x = 1
  have hmem : φ x ∈ (oPPrimeHull d A).map φ :=
    Subgroup.mem_map_of_mem φ (Subgroup.subset_closure ⟨hxA, k, hk⟩)
  have hdvd : orderOf (φ x) ∣ d ^ k := hk ▸ orderOf_map_dvd φ x
  have hdvd_card : orderOf (φ x) ∣ Nat.card ((oPPrimeHull d A).map φ) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have hcop : Nat.Coprime d (Nat.card ((oPPrimeHull d A).map φ)) :=
    hd.coprime_iff_not_dvd.mpr h
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) hdvd hdvd_card)

section Perfect

variable {G : Type} [Group G] [Finite G]

private theorem sup_commutator_primeComplementCore_eq_of_simple {d : ℕ} (hd : d.Prime)
    {Y : Subgroup G} (hY : oPPrimeHull d Y = Y)
    [IsSimpleGroup (modPrimeComplement d Y)]
    (hQ : ¬ IsMulCommutative (modPrimeComplement d Y)) :
    ⁅Y, Y⁆ ⊔ (primeComplementCore (G := ↥Y) d).map Y.subtype = Y := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  let Nc : Subgroup ↥Y := primeComplementCore (G := ↥Y) d
  let D : Subgroup G := ⁅Y, Y⁆
  let π : ↥Y →* modPrimeComplement d Y := QuotientGroup.mk' Nc
  haveI hDnorm : (D.subgroupOf Y).Normal := by
    have h : (⁅Y, Y⁆.subgroupOf (Y ⊔ Y)).Normal :=
      Subgroup.normal_subgroupOf_commutator_sup Y Y
    rwa [sup_idem] at h
  haveI hDmap_normal : ((D.subgroupOf Y).map π).Normal :=
    hDnorm.map π (QuotientGroup.mk'_surjective Nc)
  have hDmap_ne_bot : (D.subgroupOf Y).map π ≠ ⊥ := by
    intro hbot
    have hle : D.subgroupOf Y ≤ Nc := by
      simpa only [π, QuotientGroup.ker_mk'] using
        (Subgroup.map_eq_bot_iff (D.subgroupOf Y)).mp hbot
    have hcommD : _root_.commutator ↥Y ≤ D.subgroupOf Y := by
      rw [← Subgroup.map_le_map_iff_of_injective Y.subtype_injective]
      rw [Subgroup.map_subtype_commutator,
        Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self Y)]
    exact hQ (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (hcommD.trans hle))
  have hDmap_top : (D.subgroupOf Y).map π = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((D.subgroupOf Y).map π) with h | h
    · exact absurd h hDmap_ne_bot
    · exact h
  have hsup : D.subgroupOf Y ⊔ Nc = ⊤ := by
    have htop : (⊤ : Subgroup ↥Y).map π = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Nc)]
    have h := hDmap_top
    rw [← htop, Subgroup.map_eq_map_iff, QuotientGroup.ker_mk', top_sup_eq] at h
    exact h
  have hmap := congrArg (Subgroup.map Y.subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self Y),
    Subgroup.map_top, Subgroup.range_subtype] at hmap
  exact hmap

private theorem coprime_card_quot_commutator_of_sup_eq {d : ℕ} (hd : d.Prime)
    {Y : Subgroup G}
    (hYDN : ⁅Y, Y⁆ ⊔ (primeComplementCore (G := ↥Y) d).map Y.subtype = Y) :
    Nat.Coprime d (Nat.card (↥Y ⧸ (⁅Y, Y⁆).subgroupOf Y)) := by
  classical
  let Nc : Subgroup ↥Y := primeComplementCore (G := ↥Y) d
  let D : Subgroup G := ⁅Y, Y⁆
  haveI hDnorm : (D.subgroupOf Y).Normal := by
    have h : (⁅Y, Y⁆.subgroupOf (Y ⊔ Y)).Normal :=
      Subgroup.normal_subgroupOf_commutator_sup Y Y
    rwa [sup_idem] at h
  let Q' := ↥Y ⧸ D.subgroupOf Y
  let π' : ↥Y →* Q' := QuotientGroup.mk' (D.subgroupOf Y)
  have hsup : D.subgroupOf Y ⊔ Nc = ⊤ := by
    refine Subgroup.map_injective Y.subtype_injective ?_
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self Y),
      Subgroup.map_top, Subgroup.range_subtype]
    exact hYDN
  have hNcmap_top : Nc.map π' = ⊤ := by
    have htop : (⊤ : Subgroup ↥Y).map π' = ⊤ := by
      rw [Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (D.subgroupOf Y))]
    rw [← htop, Subgroup.map_eq_map_iff, QuotientGroup.ker_mk', top_sup_eq, sup_comm]
    exact hsup
  have hcard : Nat.card Q' ∣ Nat.card Nc := by
    have h := Subgroup.card_map_dvd (H := Nc) π'
    rwa [hNcmap_top, Subgroup.card_top] at h
  have hcopNc : Nat.Coprime d (Nat.card Nc) :=
    hd.coprime_iff_not_dvd.mpr (primeComplementCore_properties (↥Y) d hd).2
  exact Nat.Coprime.of_dvd_right hcard hcopNc

theorem commutator_eq_self_of_simple_modPrimeComplement_of_not_isMulCommutative {d : ℕ}
    (hd : d.Prime) {Y : Subgroup G} (hY : oPPrimeHull d Y = Y)
    [IsSimpleGroup (modPrimeComplement d Y)]
    (hQ : ¬ IsMulCommutative (modPrimeComplement d Y)) :
    ⁅Y, Y⁆ = Y := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  let D : Subgroup G := ⁅Y, Y⁆
  haveI hDnorm : (D.subgroupOf Y).Normal := by
    have h : (⁅Y, Y⁆.subgroupOf (Y ⊔ Y)).Normal :=
      Subgroup.normal_subgroupOf_commutator_sup Y Y
    rwa [sup_idem] at h
  let Nc : Subgroup ↥Y := primeComplementCore (G := ↥Y) d
  let Q' := ↥Y ⧸ D.subgroupOf Y
  have hYDN : D ⊔ Nc.map Y.subtype = Y :=
    sup_commutator_primeComplementCore_eq_of_simple hd hY hQ
  have hcop : Nat.Coprime d (Nat.card Q') :=
    coprime_card_quot_commutator_of_sup_eq hd hYDN
  have hQtop : oPPrimeHull d (⊤ : Subgroup Q') = ⊤ := by
    have hYtop : oPPrimeHull d (⊤ : Subgroup ↥Y) = ⊤ := oPPrimeHull_top_of_eq (p := d) hY
    let π' : ↥Y →* Q' := QuotientGroup.mk' (D.subgroupOf Y)
    have h := map_oPPrimeHull (p := d) π' (⊤ : Subgroup ↥Y)
    rw [hYtop, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (D.subgroupOf Y))] at h
    exact h.symm
  have hnotdvd : ¬ d ∣ Nat.card Q' := by
    intro hdvd
    exact hd.ne_one (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl d) hdvd)
  have htopbot : (⊤ : Subgroup Q') = ⊥ := by
    by_contra hne
    have hdvd : d ∣ Nat.card (⊤ : Subgroup Q') :=
      dvd_card_of_oPPrimeHull_of_ne_bot (p := d) hQtop hne
    rw [Subgroup.card_top] at hdvd
    exact hnotdvd hdvd
  have hsub : Subsingleton Q' :=
    Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp htopbot.symm)
  have hDtop : D.subgroupOf Y = ⊤ :=
    QuotientGroup.subgroup_eq_top_of_subsingleton (D.subgroupOf Y) hsub
  have hD : D = Y := by
    change ⁅Y, Y⁆ = Y
    rw [← Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self Y)]
    change (D.subgroupOf Y).map Y.subtype = Y
    rw [hDtop, Subgroup.map_top, Subgroup.range_subtype]
  exact hD

theorem commutator_eq_self_of_simple_modPrimeComplement_of_not_solvable {d : ℕ}
    (hd : d.Prime) {Y : Subgroup G} (hY : oPPrimeHull d Y = Y)
    [IsSimpleGroup (modPrimeComplement d Y)]
    (hQ : ¬ Group.IsSolvable (modPrimeComplement d Y)) :
    ⁅Y, Y⁆ = Y := by
  refine commutator_eq_self_of_simple_modPrimeComplement_of_not_isMulCommutative hd hY ?_
  intro hcomm
  exact hQ (Group.isSolvable_of_comm fun a b => mul_comm' a b)

end Perfect

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
