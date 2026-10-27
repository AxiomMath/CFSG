module

public import CFSG.GF2Type.Smith1979.CaseIIDLayer
public import CFSG.GF2Type.Smith1979.CaseIIDQuot
public import CFSG.GF2Type.Smith1979.CaseI25Layer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open CFSG.ComponentClassification
open CFSG.Assembly (InCatalog KProper)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

variable (D : Data S g t)
include D

theorem subgroupOf_Rder_le_layer (hS : SchreierFor InCatalog) (hK : KProper InCatalog G)
    (hM : S.M ≠ ⊤) (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) (hCE : S4.CentralExtInput.{0}) :
    (Rder S g t).subgroupOf S.Mbar ≤ timmesfeldLayer S.Mbar := by
  obtain ⟨-, -, -, h4, -, -, -, -, h9, -⟩ := Rbar_structure_II D hCE
  have hperfR : ⁅Rder S g t, Rder S g t⁆ = Rder S g t := Subgroup.isPerfect_iff.mp h9
  have hRE' : Rder S g t ≤ (timmesfeldLayer S.Mbar).map S.Mbar.subtype :=
    Case25.perfect_le_layer_map hS hK hM hq hodd (h4.trans Rbar_le_Mbar) hperfR
  intro x hx
  obtain ⟨e, he, hex⟩ := hRE' (mem_subgroupOf.mp hx)
  have : e = x := Subtype.ext hex
  exact this ▸ he

theorem tM_mul_self : CaseI25Transfer.tM D.ht * CaseI25Transfer.tM D.ht = 1 :=
  Subtype.ext (mul_self_of_mem_Lbar S D.H.conj_mem D.ht)

theorem mem_Rder_of_layer_comm (hCE : S4.CentralExtInput.{0})
    (hRE : (Rder S g t).subgroupOf S.Mbar ≤ timmesfeldLayer S.Mbar) (e : timmesfeldLayer S.Mbar)
    (he : CaseI25Transfer.tM D.ht * (e : S.Mbar) * (CaseI25Transfer.tM D.ht)⁻¹ = (e : S.Mbar)) :
    ((e : S.Mbar) : S.O) ∈ Rder S g t := by
  obtain ⟨h1, -⟩ := Rbar_structure_II D hCE
  have hRE' : Rder S g t ≤ (timmesfeldLayer S.Mbar).map S.Mbar.subtype := by
    intro x hx
    obtain ⟨-, -, -, h4, -⟩ := Rbar_structure_II D hCE
    exact ⟨⟨x, (h4.trans Rbar_le_Mbar) hx⟩, hRE (mem_subgroupOf.mpr hx), rfl⟩
  have hx : ((e : S.Mbar) : S.O) ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype :=
    ⟨e, e.2, rfl⟩
  have h' : t * ((e : S.Mbar) : S.O) * t⁻¹ = ((e : S.Mbar) : S.O) := congrArg Subtype.val he
  have hxc : ((e : S.Mbar) : S.O) ∈ centralizer ({t} : Set S.O) ⊓ S.Mbar :=
    ⟨mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h').symm, (e : S.Mbar).2⟩
  rw [h1] at hxc
  rw [← D.layer_inf_Rbar hCE hRE']
  exact ⟨hx, hxc⟩

theorem tM_conj_eq_of_mem_subgroupOf_Rder (hCE : S4.CentralExtInput.{0}) {r : S.Mbar}
    (hr : r ∈ (Rder S g t).subgroupOf S.Mbar) :
    CaseI25Transfer.tM D.ht * r * (CaseI25Transfer.tM D.ht)⁻¹ = r := by
  obtain ⟨-, -, -, h4, -⟩ := Rbar_structure_II D hCE
  have hcomm := commute_of_mem_Rbar D.H.conj_mem (h4 (mem_subgroupOf.mp hr))
  apply Subtype.ext
  show t * (r : S.O) * t⁻¹ = (r : S.O)
  rw [← hcomm]
  group

theorem eq_one_of_central_subgroupOf_Rder (hCE : S4.CentralExtInput.{0}) {r : S.Mbar}
    (hr : r ∈ (Rder S g t).subgroupOf S.Mbar)
    (hcomm : ∀ s ∈ (Rder S g t).subgroupOf S.Mbar, s * r = r * s) : r = 1 := by
  obtain ⟨-, -, -, h4, -⟩ := Rbar_structure_II D hCE
  refine Subtype.ext (D.eq_one_of_central_Rder hCE (mem_subgroupOf.mp hr) fun s hs => ?_)
  exact congrArg Subtype.val (hcomm ⟨s, (h4.trans Rbar_le_Mbar) hs⟩ (mem_subgroupOf.mpr hs))

theorem not_layer_le_subgroupOf_Rder (hCE : S4.CentralExtInput.{0})
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hRE : (Rder S g t).subgroupOf S.Mbar ≤ timmesfeldLayer S.Mbar) :
    ¬ timmesfeldLayer S.Mbar ≤ (Rder S g t).subgroupOf S.Mbar := by
  intro hER
  obtain ⟨-, -, -, h4, -, -, -, h8, -, h10, -⟩ := Rbar_structure_II D hCE
  have hRM : Rder S g t ≤ S.Mbar := h4.trans Rbar_le_Mbar
  have hS₀R : (Rder S g t ⊓ Nbar S g t).subgroupOf S.Mbar ≤ (Rder S g t).subgroupOf S.Mbar :=
    fun x hx => mem_subgroupOf.mpr (mem_subgroupOf.mp hx).1
  have hS₀E : (Rder S g t ⊓ Nbar S g t).subgroupOf S.Mbar ≤ timmesfeldLayer S.Mbar :=
    hS₀R.trans hRE
  haveI hS₁ : (((Rder S g t ⊓ Nbar S g t).subgroupOf S.Mbar).subgroupOf
      (timmesfeldLayer S.Mbar)).Normal := ⟨fun n hn g' => by
    rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
    exact D.conj_mem_Rder_inf_Nbar hCE (mem_subgroupOf.mp (hER g'.2)) hn⟩
  have hcard : Nat.card (((Rder S g t ⊓ Nbar S g t).subgroupOf S.Mbar).subgroupOf
      (timmesfeldLayer S.Mbar)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀E).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans hRM : Rder S g t ⊓ Nbar S g t ≤ S.Mbar)).toEquiv]
    exact h10
  rcases Quasisimple.normal_le_center_or_eq_top hq
    (((Rder S g t ⊓ Nbar S g t).subgroupOf S.Mbar).subgroupOf (timmesfeldLayer S.Mbar))
    with hle | htop
  · have h8d := (Subgroup.card_dvd_of_le hle).trans (Case25.card_center_layer_dvd hodd)
    rw [hcard] at h8d
    exact absurd (Nat.le_of_dvd (by norm_num) h8d) (by norm_num)
  · have h1 := Subgroup.card_le_of_le hRE
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, h8] at h1
    rw [htop, Subgroup.card_top] at hcard
    omega

end Data

theorem critII_X_strong (D : Data S g t) (hCE : S4.CentralExtInput.{0})
    (hS : SchreierFor InCatalog) (hK : KProper InCatalog G) (hM : S.M ≠ ⊤)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) :
    ∃ σ : MulAut (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)),
      σ * σ = 1 ∧ (∀ x, σ ≠ MulAut.conj x) ∧
      (∀ e e' : timmesfeldLayer S.Mbar,
        (e' : S.Mbar) = CaseI25Transfer.tM D.ht * (e : S.Mbar) * (CaseI25Transfer.tM D.ht)⁻¹ →
          σ (QuotientGroup.mk e) = QuotientGroup.mk e') ∧
      ∃ j : Rder S g t →* (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)),
        Function.Injective j ∧ (∀ x, σ x = x ↔ x ∈ j.range) ∧
        ∀ (r : Rder S g t) (e : timmesfeldLayer S.Mbar),
          ((e : S.Mbar) : S.O) = (r : S.O) → j r = QuotientGroup.mk e := by
  haveI hEN : (timmesfeldLayer S.Mbar).Normal := Layer.normal S.Mbar
  have hRM : Rder S g t ≤ S.Mbar := (Rbar_structure_II D hCE).2.2.2.1.trans Rbar_le_Mbar
  have hRE := D.subgroupOf_Rder_le_layer hS hK hM hq hodd hCE
  have htt := D.tM_mul_self
  have hEperf : ⁅timmesfeldLayer S.Mbar, timmesfeldLayer S.Mbar⁆ = timmesfeldLayer S.Mbar :=
    Subgroup.isPerfect_iff.mp (Layer.perfect S.Mbar)
  have hZ : ∀ z ∈ center (timmesfeldLayer S.Mbar), z ^ 3 = 1 := fun z hz =>
    orderOf_dvd_iff_pow_eq_one.mp
      ((Subgroup.orderOf_dvd_natCard _ hz).trans (Case25.card_center_layer_dvd hodd))
  have hC1 : ∀ e : timmesfeldLayer S.Mbar,
      CaseI25Transfer.tM D.ht * (e : S.Mbar) * (CaseI25Transfer.tM D.ht)⁻¹ = (e : S.Mbar) →
        (e : S.Mbar) ∈ (Rder S g t).subgroupOf S.Mbar := fun e he =>
    mem_subgroupOf.mpr (D.mem_Rder_of_layer_comm hCE hRE e he)
  have hC2 : ∀ r ∈ (Rder S g t).subgroupOf S.Mbar,
      CaseI25Transfer.tM D.ht * r * (CaseI25Transfer.tM D.ht)⁻¹ = r := fun r hr =>
    D.tM_conj_eq_of_mem_subgroupOf_Rder hCE hr
  have hRc : ∀ r ∈ (Rder S g t).subgroupOf S.Mbar,
      (∀ s ∈ (Rder S g t).subgroupOf S.Mbar, s * r = r * s) → r = 1 := fun r hr hc =>
    D.eq_one_of_central_subgroupOf_Rder hCE hr hc
  have hRZ : ∀ r : (Rder S g t).subgroupOf S.Mbar,
      (⟨r.1, hRE r.2⟩ : timmesfeldLayer S.Mbar) ∈ center (timmesfeldLayer S.Mbar) → r = 1 := by
    intro r hr
    refine Subtype.ext (hRc r.1 r.2 fun s hs => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hr ⟨s, hRE hs⟩)
  have hER := D.not_layer_le_subgroupOf_Rder hCE hq hodd hRE
  refine ⟨inducedAut (timmesfeldLayer S.Mbar) (CaseI25Transfer.tM D.ht),
    inducedAut_mul_self htt,
    fun x => inducedAut_ne_conj htt hRE hZ hC1 hC2 hEperf hRc hRZ hER x, ?_, ?_⟩
  · intro e e' he'
    rw [inducedAut_mk]
    congr 1
    exact Subtype.ext he'.symm
  · let iso : Rder S g t ≃* (Rder S g t).subgroupOf S.Mbar :=
      (Subgroup.subgroupOfEquivOfLe hRM).symm
    let j : Rder S g t →* (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) :=
      (embedQuot (timmesfeldLayer S.Mbar) _ hRE).comp iso.toMonoidHom
    have hj : Function.Injective j := fun a b hab =>
      iso.injective (embedQuot_injective hRE hRZ hab)
    have hjr : ∀ x, x ∈ (embedQuot (timmesfeldLayer S.Mbar) _ hRE).range ↔ x ∈ j.range := by
      intro x
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨iso.symm r, by simp [j]⟩
      · rintro ⟨r, rfl⟩
        exact ⟨iso r, rfl⟩
    refine ⟨j, hj, fun x => ?_, ?_⟩
    · exact (inducedAut_fix_iff htt hRE hZ hC1 hC2 x).trans (hjr x)
    · intro r e he
      show QuotientGroup.mk (⟨((iso r : (Rder S g t).subgroupOf S.Mbar) : S.Mbar),
        hRE (iso r).2⟩ : timmesfeldLayer S.Mbar) = QuotientGroup.mk e
      congr 1
      exact Subtype.ext (Subtype.ext he.symm)

theorem critII_X (D : Data S g t) (hCE : S4.CentralExtInput.{0})
    (hS : SchreierFor InCatalog) (hK : KProper InCatalog G) (hM : S.M ≠ ⊤)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) :
    CritII (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∧
      1344 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := by
  obtain ⟨σ, hσ2, hσi, -, j, hj, hfix, -⟩ := critII_X_strong D hCE hS hK hM hq hodd
  have hR : Nat.card (Rder S g t) = 1344 := (Rbar_structure_II D hCE).2.2.2.2.2.2.2.1
  have hcard : Nat.card (Rder S g t) = Nat.card j.range :=
    Nat.card_congr (MonoidHom.ofInjective hj).toEquiv
  refine ⟨⟨σ, hσ2, hσi, ?_⟩, ?_⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight hfix), ← hcard, hR]
  · rw [← hR]
    exact Subgroup.card_dvd_of_injective j hj

end CFSG.GF2Type.Smith1979.Case2
