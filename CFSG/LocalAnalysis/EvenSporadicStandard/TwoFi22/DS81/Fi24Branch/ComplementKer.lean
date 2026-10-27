module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ComplementDefs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

theorem exists_normKer {P E U : Subgroup G} {r : G} (h : NormSetting P E U r) :
    ∃ S : Subgroup G, S ≤ P ∧ U ≤ S ∧ (∀ x, x ∈ S ↔ x ∈ P ∧ normOf r x ∈ U) ∧
      S ⊓ E = U ∧ ∀ p ∈ P, ∃ s ∈ S, ∃ e ∈ E, p = s * e := by
  have hUP : U ≤ P := h.U_le_E.trans h.E_le_P
  have hUnorm : (U.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUP]
    intro u p hu hp
    have hmem : p * u * p⁻¹ ∈ U := by
      rw [show p * u * p⁻¹ = (p * u * p⁻¹ * u⁻¹) * u by group]
      exact U.mul_mem (h.PP p hp u (hUP hu)) hu
    exact hmem
  letI : (U.subgroupOf P).Normal := hUnorm
  let Q := ↥P ⧸ U.subgroupOf P
  let q : ↥P →* Q := QuotientGroup.mk' _
  let σ : ↥P →* ↥P :=
    { toFun := fun x => ⟨r * (x : G) * r⁻¹, h.r_P (x : G) x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change r * ((x : G) * (y : G)) * r⁻¹ =
          (r * (x : G) * r⁻¹) * (r * (y : G) * r⁻¹)
        group }
  have hσU : U.subgroupOf P ≤ (U.subgroupOf P).comap σ := by
    intro u hu
    exact h.r_U (u : G) hu
  let ρ : Q →* Q := QuotientGroup.map _ _ σ hσU
  haveI hQcomm : IsMulCommutative Q := by
    change IsMulCommutative (↥P ⧸ U.subgroupOf P)
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    change ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ ≤ U.subgroupOf P
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using
      h.PP (a : G) a.2 (b : G) b.2
  have hnormP : ∀ x ∈ P, normOf r x ∈ P := by
    intro x hx
    have hrx : r * x * r⁻¹ ∈ P := h.r_P x hx
    have hr2x : r ^ 2 * x * (r ^ 2)⁻¹ ∈ P := by
      have h' := h.r_P (r * x * r⁻¹) hrx
      rwa [show r * (r * x * r⁻¹) * r⁻¹ = r ^ 2 * x * (r ^ 2)⁻¹ by
        rw [pow_two]; group] at h'
    exact P.mul_mem (P.mul_mem hx hrx) hr2x
  let nrm : ↥P → Q := fun x => q x * ρ (q x) * ρ (ρ (q x))
  have hnrm_apply : ∀ x : ↥P, nrm x = q ⟨normOf r x, hnormP x x.2⟩ := by
    intro x
    have h1 : ρ (q x) = q (σ x) := QuotientGroup.map_mk' _ _ _ _ x
    have h2 : ρ (ρ (q x)) = q (σ (σ x)) := by
      rw [h1]
      exact QuotientGroup.map_mk' _ _ _ _ (σ x)
    simp only [nrm]
    rw [h2, h1]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (x : G) * (r * (x : G) * r⁻¹) * (r * (r * (x : G) * r⁻¹) * r⁻¹) = normOf r x
    unfold normOf
    group
  have hnrm_mul : ∀ a b : ↥P, nrm (a * b) = nrm a * nrm b := by
    intro a b
    simp only [nrm, map_mul]
    ac_rfl
  have hnrm_one : nrm 1 = 1 := by
    simp [nrm]
  have hnrm_inv : ∀ a : ↥P, nrm a⁻¹ = (nrm a)⁻¹ := by
    intro a
    have hh : nrm a * nrm a⁻¹ = 1 := by
      rw [← hnrm_mul, mul_inv_cancel, hnrm_one]
    exact eq_inv_of_mul_eq_one_right hh
  have hρ3 : ∀ y : Q, ρ (ρ (ρ y)) = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) y
    have e1 : ρ (q x) = q (σ x) := QuotientGroup.map_mk' _ _ _ _ x
    have e2 : ρ (q (σ x)) = q (σ (σ x)) := QuotientGroup.map_mk' _ _ _ _ (σ x)
    have e3 : ρ (q (σ (σ x))) = q (σ (σ (σ x))) :=
      QuotientGroup.map_mk' _ _ _ _ (σ (σ x))
    rw [e1, e2, e3]
    change QuotientGroup.mk (σ (σ (σ x))) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hcube : ((σ (σ (σ x))) : G) = (x : G) := by
      have hr3 : r * r * r = 1 := by
        have h3 := h.r_cube
        rw [pow_three] at h3
        rwa [← mul_assoc] at h3
      calc r * (r * (r * (x : G) * r⁻¹) * r⁻¹) * r⁻¹
          = (r * r * r) * (x : G) * (r * r * r)⁻¹ := by group
        _ = (x : G) := by rw [hr3]; group
    rw [hcube, inv_mul_cancel]
    exact U.one_mem
  have hρe : ∀ (e : G) (he : e ∈ E), ρ (q ⟨e, h.E_le_P he⟩) = q ⟨e, h.E_le_P he⟩ := by
    intro e he
    rw [QuotientGroup.map_mk']
    change QuotientGroup.mk (σ ⟨e, h.E_le_P he⟩) = QuotientGroup.mk (⟨e, h.E_le_P he⟩ : ↥P)
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    rw [Subgroup.coe_div]
    show (r * e * r⁻¹) / e ∈ U
    rw [div_eq_mul_inv]
    exact h.r_E e he
  have hL3 : ∀ (e : G) (he : e ∈ E), q ⟨normOf r e, hnormP e (h.E_le_P he)⟩ =
      q ⟨e, h.E_le_P he⟩ := by
    intro e he
    have hρe' := hρe e he
    have h3 : nrm ⟨e, h.E_le_P he⟩ = q ⟨e, h.E_le_P he⟩ := by
      simp only [nrm]
      rw [show ρ (ρ (q ⟨e, h.E_le_P he⟩)) = q ⟨e, h.E_le_P he⟩ from by
        simp only [hρe'], hρe']
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (e : G) * e * e = e
      have he2 : (e : G) * e = 1 := by
        have := h.E_sq e he
        rwa [pow_two] at this
      rw [he2, one_mul]
    rw [← hnrm_apply ⟨e, h.E_le_P he⟩]
    exact h3
  have hL4 : ∀ p ∈ P, normOf r p ∈ E := by
    intro p hp
    apply h.r_fpf (normOf r p) (hnormP p hp)
    have hyP : normOf r p ∈ P := hnormP p hp
    have hρN : ρ (nrm ⟨p, hp⟩) = nrm ⟨p, hp⟩ := by
      simp only [nrm, map_mul]
      rw [hρ3]
      ac_rfl
    have hqσ : q (σ ⟨normOf r p, hyP⟩) = q ⟨normOf r p, hyP⟩ := by
      change (↑(σ ⟨normOf r p, hyP⟩) : Q) = (↑(⟨normOf r p, hyP⟩ : ↥P) : Q)
      have h1 : ρ (q (⟨normOf r p, hyP⟩ : ↥P)) = (↑(σ ⟨normOf r p, hyP⟩) : Q) :=
        QuotientGroup.map_mk' _ _ _ _ (⟨normOf r p, hyP⟩ : ↥P)
      rw [← h1]
      change ρ (q ⟨normOf r p, hnormP p hp⟩) = q ⟨normOf r p, hnormP p hp⟩
      rw [← hnrm_apply ⟨p, hp⟩]
      exact hρN
    have hconj : r * normOf r p * r⁻¹ * (normOf r p)⁻¹ ∈ U := by
      have h' : (r * normOf r p * r⁻¹) / (normOf r p) ∈ U := by
        have h'' := (QuotientGroup.eq_iff_div_mem.mp hqσ)
        change (σ ⟨normOf r p, hyP⟩ : G) / (normOf r p : G) ∈ U at h''
        change (r * normOf r p * r⁻¹) / (normOf r p) ∈ U at h''
        exact h''
      rwa [div_eq_mul_inv] at h'
    exact hconj
  let S : Subgroup G :=
    { carrier := {x | x ∈ P ∧ normOf r x ∈ U}
      mul_mem' := by
        rintro x y ⟨hxP, hxU⟩ ⟨hyP, hyU⟩
        refine ⟨P.mul_mem hxP hyP, ?_⟩
        have hx1 : nrm ⟨x, hxP⟩ = 1 := by
          rw [hnrm_apply]
          exact (QuotientGroup.eq_one_iff _).mpr hxU
        have hy1 : nrm ⟨y, hyP⟩ = 1 := by
          rw [hnrm_apply]
          exact (QuotientGroup.eq_one_iff _).mpr hyU
        have hxy : nrm (⟨x, hxP⟩ * ⟨y, hyP⟩) = 1 := by
          rw [hnrm_mul, hx1, hy1, mul_one]
        have hxy' : nrm (⟨x * y, P.mul_mem hxP hyP⟩ : ↥P) = 1 := by
          rw [show (⟨x * y, P.mul_mem hxP hyP⟩ : ↥P) = ⟨x, hxP⟩ * ⟨y, hyP⟩ from
            Subtype.ext rfl]
          exact hxy
        rw [hnrm_apply] at hxy'
        have hxyU : (⟨normOf r (x * y), hnormP (x * y) (P.mul_mem hxP hyP)⟩ : ↥P) ∈
            U.subgroupOf P := (QuotientGroup.eq_one_iff _).mp hxy'
        exact hxyU
      one_mem' := by
        refine ⟨P.one_mem, ?_⟩
        have h1 : normOf r (1 : G) = 1 := by simp [normOf]
        rw [h1]
        exact U.one_mem
      inv_mem' := by
        rintro x ⟨hxP, hxU⟩
        refine ⟨P.inv_mem hxP, ?_⟩
        have hx1 : nrm ⟨x, hxP⟩ = 1 := by
          rw [hnrm_apply]
          exact (QuotientGroup.eq_one_iff _).mpr hxU
        have hxi : nrm (⟨x, hxP⟩⁻¹) = 1 := by rw [hnrm_inv, hx1, inv_one]
        have hxi' : nrm (⟨x⁻¹, P.inv_mem hxP⟩ : ↥P) = 1 := by
          rw [show (⟨x⁻¹, P.inv_mem hxP⟩ : ↥P) = ⟨x, hxP⟩⁻¹ from Subtype.ext rfl]
          exact hxi
        rw [hnrm_apply] at hxi'
        have hxiU : (⟨normOf r x⁻¹, hnormP x⁻¹ (P.inv_mem hxP)⟩ : ↥P) ∈
            U.subgroupOf P := (QuotientGroup.eq_one_iff _).mp hxi'
        exact hxiU }
  have hUS : U ≤ S := by
    intro u hu
    refine ⟨hUP hu, ?_⟩
    have hu1 : r * u * r⁻¹ ∈ U := h.r_U u hu
    have hu2 : r ^ 2 * u * (r ^ 2)⁻¹ ∈ U := by
      have h' := h.r_U (r * u * r⁻¹) hu1
      rwa [show r * (r * u * r⁻¹) * r⁻¹ = r ^ 2 * u * (r ^ 2)⁻¹ by
        rw [pow_two]; group] at h'
    simpa only [normOf] using U.mul_mem (U.mul_mem hu hu1) hu2
  refine ⟨S, fun x hx => hx.1, hUS, fun x => Iff.rfl, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro x hx
      obtain ⟨hxS, hxE⟩ := hx
      obtain ⟨hxP, hxU⟩ := hxS
      have hρx : ρ (q ⟨x, hxP⟩) = q ⟨x, hxP⟩ := by
        rw [show (⟨x, hxP⟩ : ↥P) = ⟨x, h.E_le_P hxE⟩ from Subtype.ext rfl]
        exact hρe x hxE
      have h3 : nrm ⟨x, hxP⟩ = q ⟨x, hxP⟩ := by
        simp only [nrm]
        rw [show ρ (ρ (q ⟨x, hxP⟩)) = q ⟨x, hxP⟩ from by simp only [hρx], hρx]
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show (x : G) * x * x = x
        have hx2 : (x : G) * x = 1 := by
          have := h.E_sq x hxE
          rwa [pow_two] at this
        rw [hx2, one_mul]
      have hq : q ⟨x, hxP⟩ = 1 := by
        have h1 : nrm ⟨x, hxP⟩ = q ⟨normOf r x, hnormP x hxP⟩ := hnrm_apply _
        rw [h3] at h1
        rw [h1]
        exact (QuotientGroup.eq_one_iff _).mpr hxU
      have hxU' : (⟨x, hxP⟩ : ↥P) ∈ U.subgroupOf P :=
        (QuotientGroup.eq_one_iff (⟨x, hxP⟩ : ↥P)).mp hq
      exact hxU'
    · exact le_inf hUS h.U_le_E
  ·
    intro p hp
    let e0 : G := normOf r p
    have he0E : e0 ∈ E := hL4 p hp
    have he0P : e0 ∈ P := h.E_le_P he0E
    refine ⟨p * e0⁻¹, ?_, e0, he0E, ?_⟩
    · refine ⟨P.mul_mem hp (P.inv_mem he0P), ?_⟩
      have hs : (⟨p * e0⁻¹, P.mul_mem hp (P.inv_mem he0P)⟩ : ↥P) =
          ⟨p, hp⟩ * (⟨e0, he0P⟩ : ↥P)⁻¹ := Subtype.ext rfl
      have hkey : nrm (⟨p, hp⟩ * (⟨e0, he0P⟩ : ↥P)⁻¹) = 1 := by
        rw [hnrm_mul, hnrm_inv, hnrm_apply, hnrm_apply, hL3 e0 he0E]
        rw [show (⟨normOf r p, hnormP p hp⟩ : ↥P) = ⟨e0, h.E_le_P he0E⟩ from
          Subtype.ext rfl]
        rw [mul_inv_cancel]
      have h1 : nrm (⟨p * e0⁻¹, P.mul_mem hp (P.inv_mem he0P)⟩ : ↥P) = 1 := by
        rw [hs]
        exact hkey
      rw [hnrm_apply] at h1
      have hsU : (⟨normOf r (p * e0⁻¹), hnormP (p * e0⁻¹)
          (P.mul_mem hp (P.inv_mem he0P))⟩ : ↥P) ∈ U.subgroupOf P :=
        (QuotientGroup.eq_one_iff _).mp h1
      exact hsU
    · group

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
