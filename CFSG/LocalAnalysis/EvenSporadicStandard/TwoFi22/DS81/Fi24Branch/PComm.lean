module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.RinN

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

theorem comm_P_eq (c : Core1 E t z) (rp : RPData E t z) :
    ⁅Pg E z, Pg E z⁆ = Rg t z ⊓ E := by
  have hCNz_le_normP : CNz E z ≤ normalizer (Pg E z : Set G) := by
    haveI : ((Pg E z).subgroupOf (CNz E z)).Normal := TwoB.normal_subgroupOf_O2In (CNz E z)
    exact Subgroup.le_normalizer_of_normal_subgroupOf (Pg_le_CNz E z)
  have hDinv : InvUnder (CNz E z) ⁅Pg E z, Pg E z⁆ := by
    intro n hn u hu
    rw [Subgroup.commutator_def] at hu
    have hnP : ∀ a ∈ Pg E z, n * a * n⁻¹ ∈ Pg E z :=
      (Subgroup.le_set_normalizer_iff.mp hCNz_le_normP) n hn
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      rw [conjugate_commutatorElement]
      exact Subgroup.commutator_mem_commutator (hnP a ha) (hnP b hb)
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [show n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) by group]
      exact mul_mem ihx ihy
    | inv x _ ihx =>
      rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
      exact inv_mem ihx
  have hDE : ⁅Pg E z, Pg E z⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h := c.cocode.P_comm a ha b hb
    simpa [commutatorElement_def] using h
  have hDR : ⁅Pg E z, Pg E z⁆ ≤ Rg t z := by
    have hP_le_normR : Pg E z ≤ normalizer (Rg t z : Set G) :=
      rp.P_le_J.trans (Subgroup.le_set_normalizer_iff.mpr c.jr.R_normal)
    haveI : ((Rg t z).subgroupOf (Pg E z)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hP_le_normR
    have hEcomm : IsMulCommutative (E.subgroupOf (Pg E z)) := by
      rw [isMulCommutative_iff]
      intro a b
      exact Subtype.ext (Subtype.ext
        (sq_eq_one_comm c.m24.E_sq (a.1 : G) (Subgroup.mem_subgroupOf.mp a.2)
          (b.1 : G) (Subgroup.mem_subgroupOf.mp b.2)))
    have hsup : (Rg t z).subgroupOf (Pg E z) ⊔ (E.subgroupOf (Pg E z)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨r, hr, e, he, hre⟩ := rp.P_decomp x.1 x.2
      have hx : x = ⟨r, rp.R_le_P hr⟩ * ⟨e, rp.E_le_P he⟩ := Subtype.ext hre
      rw [hx]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hr))
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr he))
    have hcomm := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hEcomm
    have h2 := Subgroup.map_mono (f := (Pg E z).subtype) hcomm
    rw [Subgroup.map_subtype_commutator, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr rp.R_le_P] at h2
    exact h2
  have hlat := c.cocode.lattice ⁅Pg E z, Pg E z⁆ hDE hDinv
  have hD_ne_bot : ⁅Pg E z, Pg E z⁆ ≠ ⊥ := by
    intro hbot
    have hPleCP : Pg E z ≤ centralizer (Pg E z : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Pg E z) (H₂ := Pg E z)).mp hbot
    have hRle_zp : Rg t z ≤ zpowers z := by
      intro x hx
      exact (c.jr.center_R x hx).mp (fun y hy =>
        (mem_centralizer_iff.mp (hPleCP (rp.R_le_P hx)) y (rp.R_le_P hy)).symm)
    have hcard := Subgroup.card_le_of_le hRle_zp
    have hcardz : Nat.card ↥(zpowers z) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime c.klein.z_sq c.klein.z_ne]
    rw [c.jr.card_R, hcardz] at hcard
    norm_num at hcard
  have hD_ne_zp : ⁅Pg E z, Pg E z⁆ ≠ zpowers z := by
    intro hDzp
    have hQle : ⁅E, Pg E z⁆ ≤ zpowers z :=
      (Subgroup.commutator_mono rp.E_le_P le_rfl).trans (le_of_eq hDzp)
    by_cases hQbot : ⁅E, Pg E z⁆ = ⊥
    · have hPleCE : Pg E z ≤ centralizer (E : Set G) := by
        have hPEbot : ⁅Pg E z, E⁆ = ⊥ := (Subgroup.commutator_comm (Pg E z) E).trans hQbot
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Pg E z) (H₂ := E)).mp hPEbot
      have hPleE : Pg E z ≤ E := by rwa [c.m24.centralizer_eq] at hPleCE
      have hcard := Subgroup.card_le_of_le hPleE
      rw [c.cocode.card_P, c.m24.card_E] at hcard
      norm_num at hcard
    · have hcardz : Nat.card ↥(zpowers z) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime c.klein.z_sq c.klein.z_ne]
      have hQcardle : Nat.card ↥(⁅E, Pg E z⁆) ≤ Nat.card ↥(zpowers z) :=
        Subgroup.card_le_of_le hQle
      rw [hcardz] at hQcardle
      have hQlt : 1 < Nat.card ↥(⁅E, Pg E z⁆) :=
        (Subgroup.one_lt_card_iff_ne_bot (⁅E, Pg E z⁆)).mpr hQbot
      have hQcard : Nat.card ↥(⁅E, Pg E z⁆) = 2 := by omega
      exact c.cocode.comm_ne (Subgroup.eq_of_le_of_card_ge hQle (by rw [hcardz, hQcard]))
  have hDleRE : ⁅Pg E z, Pg E z⁆ ≤ Rg t z ⊓ E := le_inf hDR hDE
  rcases hlat with hbot | hzp | hcard | hE
  · exact absurd hbot hD_ne_bot
  · exact absurd hzp hD_ne_zp
  · exact Subgroup.eq_of_le_of_card_ge hDleRE (by rw [hcard, rp.card_RE])
  · exfalso
    have hcard := Subgroup.card_le_of_le hDleRE
    rw [hE, c.m24.card_E, rp.card_RE] at hcard
    norm_num at hcard

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
