module

public import CFSG.LargeExtraspecial.S6TwoB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem add_add_add_add_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (x y z : W) :
    x + y + z + y + x = z := by
  rw [show x + y + z + y + x = z + (x + x) + (y + y) by abel, vec_add_self, vec_add_self,
    add_zero, add_zero]

section A6

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hA : A6Case H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include H C ht ht1 hVQ hA hh hb

theorem exists_conj_R0bar :
    ∃ r ∈ R0bar S g h, S.Lbar ((h : G) * g) = (S.Lbar g).map (MulAut.conj r).toMonoidHom := by
  obtain ⟨Q, hQ, hpolβ, hQa, hQb, ⟨u, hau, hbu, hQu⟩, hEa, hEb, -⟩ :=
    exists_minus_form_a6 H C ht ht1 hVQ hA hh hb
  have hth := mem_Lbar_of_pair H ht hh
  set β := beta H C ht ht1 hVQ with hβdef
  have hβa : β.IsAlt := beta_isAlt H C ht ht1 hVQ
  have hpol : ∀ x y, polar Q x y = β x y := fun x y => by
    rw [← polarBilin_apply_apply, hpolβ]
  have hab : β (aV ht) (bV hth) = 1 := beta_aV_bV H C ht ht1 hVQ hh hb
  have hba : β (bV hth) (aV ht) = 1 := by rw [isAlt_symm hβa, hab]
  have hua : β u (aV ht) = 0 := by rw [isAlt_symm hβa, hau]
  have hub : β u (bV hth) = 0 := by rw [isAlt_symm hβa, hbu]
  have hEaN : eichler Q (aV ht) u ∈ LmodN S g t :=
    hEa ▸ eichler_mem_pointRadical hQa (by rw [hpol]; exact hau)
  have hEbN : eichler Q (bV hth) u ∈ LhmodN S g t h :=
    hEb ▸ eichler_mem_pointRadical hQb (by rw [hpol]; exact hbu)
  have hmove : eichler Q (aV ht) u (eichler Q (bV hth) u (aV ht)) = bV hth := by
    rw [eichler_apply_zmod2 hQb (by rw [hpol]; exact hbu),
      eichler_apply_zmod2 hQa (by rw [hpol]; exact hau)]
    simp only [hpol, map_add, LinearMap.add_apply, hab, hba, hua, hau, hbu, hQu,
      hβa.self_eq_zero, mul_one, add_zero, zero_add, one_smul]
    exact add_add_add_add_eq _ _ _
  rw [← map_subgroupOf_resV H.conj_mem ht] at hEaN
  rw [← map_subgroupOf_resV_mul H.conj_mem hth] at hEbN
  obtain ⟨⟨l, hlR⟩, hl, hle⟩ := hEaN
  obtain ⟨⟨l', hl'R⟩, hl', hle'⟩ := hEbN
  have hl0 : l ∈ S.Lbar g := mem_subgroupOf.mp hl
  have hl0' : l' ∈ S.Lbar ((h : G) * g) := mem_subgroupOf.mp hl'
  refine ⟨l * l', mul_mem (mem_sup_left hl0) (mem_sup_right hl0'), ?_⟩
  obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (mul_mem hlR hl'R))
  rw [← hj, ← Lbar_mul S j g]
  have hcl : S.cl ((j : G) * g * S.z * ((j : G) * g)⁻¹) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S j H.conj_mem, hj, ← coe_bV hth, ← hmove, ← hle, ← hle']
    rfl
  exact (Lbar_eq_of_cl_eq S (H.mul h).conj_mem (H.mul h).conj_ne (H.mul j).conj_mem hcl).symm

variable (hCE : CentralExtInput.{u})
include hCE

theorem R0bar_inf_Nbar_le_N0bar : R0bar S g h ⊓ Nbar S g t ≤ N0bar S g t := by
  obtain ⟨Q, hQ, hpolβ, hQa, hQb, ⟨u, hau, hbu, hQu⟩, hEa, hEb, hR0⟩ :=
    exists_minus_form_a6 H C ht ht1 hVQ hA hh hb
  have hth := mem_Lbar_of_pair H ht hh
  have haQ := H.conj_mem
  have hR0R : R0bar S g h ≤ Rbar S g t := sup_le (Lbar_le_Rbar ht) (Lbar_mul_le_Rbar hth)
  have hD := dtEqConj_of_transitive H ht hA.transitive
  obtain ⟨φ, hφ⟩ : ∃ φ : R0bar S g h →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t),
      φ = (resV haQ t).comp (Subgroup.inclusion hR0R) := ⟨_, rfl⟩
  have hrange : φ.range = omegaGroup Q hQ := by
    rw [hφ, ← MonoidHom.map_range, Subgroup.inclusion_range, hR0]
  have hmapL : ((S.Lbar g).subgroupOf (R0bar S g h)).map φ = pointRadical Q (aV ht) := by
    rw [← hEa, ← map_subgroupOf_resV haQ ht, hφ]
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hR0R x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, mem_sup_left (mem_subgroupOf.mp hx)⟩, hx, rfl⟩
  have hpair : NaturalPair (omegaGroup Q hQ) (pointRadical Q (aV ht)) (aV ht) :=
    Or.inr (Or.inr (Or.inr ⟨by rw [hA.finrank_eq], Q, hQ, hQa, rfl, rfl⟩))
  have hN0 : ∀ r ∈ R0bar S g h, ∀ x ∈ R0bar S g h ⊓ N0bar S g t,
      r * x * r⁻¹ ∈ R0bar S g h ⊓ N0bar S g t := fun r hr x hx =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hr (Subgroup.mem_inf.mp hx).1) (inv_mem hr),
      conj_mem_N0bar haQ (hR0R hr) (Subgroup.mem_inf.mp hx).2⟩
  have hker : ∀ x : R0bar S g h, φ x = 1 ↔ (x : S.O) ∈ R0bar S g h ⊓ Nbar S g t := fun x => by
    rw [hφ, MonoidHom.comp_apply, resV_eq_one_iff, Subgroup.coe_inclusion]
    exact ⟨fun h => Subgroup.mem_inf.mpr ⟨x.2, h⟩, fun h => (Subgroup.mem_inf.mp h).2⟩
  have hcomm : ∀ n ∈ R0bar S g h ⊓ Nbar S g t, ∀ r ∈ R0bar S g h,
      n * r * n⁻¹ * r⁻¹ ∈ R0bar S g h ⊓ N0bar S g t := fun n hn r hr =>
    Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem (mul_mem (Subgroup.mem_inf.mp hn).1 hr)
        (inv_mem (Subgroup.mem_inf.mp hn).1)) (inv_mem hr),
      commutator_mem_N0bar H hD (Subgroup.mem_inf.mp hn).2 (hR0R hr)⟩
  have hLN : S.Lbar g ⊓ (R0bar S g h ⊓ Nbar S g t) ≤ R0bar S g h ⊓ N0bar S g t := fun x hx =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1,
      Lbar_inf_Nbar_le_N0bar (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2⟩)⟩
  have hgen : R0bar S g h ≤
      closure {u | ∃ r ∈ R0bar S g h, ∃ l ∈ S.Lbar g, u = r * l * r⁻¹} := by
    refine sup_le (fun l hl => subset_closure ⟨1, one_mem _, l, hl, by simp⟩) ?_
    obtain ⟨r, hr, hLb⟩ := exists_conj_R0bar H C ht ht1 hVQ hA hh hb
    rw [hLb]
    rintro _ ⟨l, hl, rfl⟩
    exact subset_closure ⟨r, hr, l, hl, rfl⟩
  have hnorm : ∀ x : R0bar S g h, φ x (aV ht) = aV ht →
      (x : S.O) ∈ normalizer (S.Lbar g : Set S.O) := fun x hx => by
    have hfix : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
      have := congrArg Subtype.val hx
      rwa [hφ, MonoidHom.comp_apply, coe_resV_apply] at this
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) haQ H.conj_ne
      (Rbar_le_Mbar (hR0R x.2)) (by simpa using hfix)
    simpa using this
  have hwc : ∀ r ∈ R0bar S g h, (∀ y ∈ (S.Lbar g).map (MulAut.conj r).toMonoidHom,
      ∀ l ∈ S.Lbar g, ∃ l' ∈ S.Lbar g, l'⁻¹ * (y * l * y⁻¹) ∈ R0bar S g h ⊓ N0bar S g t) →
      (S.Lbar g).map (MulAut.conj r).toMonoidHom = S.Lbar g := fun r hr hconj => by
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (hR0R hr))
    rw [← Lbar_mul S k g] at hconj ⊢
    exact Lbar_conj_eq_of_conj_mem H C ht (hR0R hr) fun y hy l hl => by
      obtain ⟨l', hl', hmem⟩ := hconj y hy l hl
      exact ⟨l', hl', (Subgroup.mem_inf.mp hmem).2⟩
  rcases eq_of_centralExtInput hCE (inf_le_inf_left _ N0bar_le_Nbar) inf_le_left le_sup_left
      hN0 φ hker (aV_ne_zero H ht) hpair hrange hmapL hcomm hLN hgen hnorm hwc with
    h1 | ⟨hA6, -⟩
  · intro x hx
    have hx' : x ∈ (S.Lbar g ⊔ S.Lbar ((h : G) * g)) ⊓ Nbar S g t := hx
    rw [h1] at hx'
    exact (Subgroup.mem_inf.mp hx').2
  · exfalso
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [map_zero] at hQu
      exact zero_ne_one hQu
    obtain ⟨x, hx, hxa⟩ := transitive_of_a6Pair hA6 (aV_ne_zero H ht) hu0
    have := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (mem_omegaGroup.mp hx).1
      (aV ht)
    rw [hxa, hQa, hQu] at this
    exact one_ne_zero this

theorem R0bar_inf_Nbar_apply_sub_mem_Vt {x : S.O} (hx : x ∈ R0bar S g h ⊓ Nbar S g t)
    {w : S.Qt} (hw : w ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ hA.tau_not_mem
  have hP := clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR
  exact apply_sub_mem_Vt_of_mem_N0bar H
    (fun k hk w hw => apply_sub_mem_Vt_a H C ht ht1 hVQ hh hb hP hk hw)
    (R0bar_inf_Nbar_le_N0bar H C ht ht1 hVQ hA hh hb hCE hx) hw

end A6

end CFSG.LargeExtraspecial.S6
