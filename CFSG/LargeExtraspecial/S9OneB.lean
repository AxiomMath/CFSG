module

public import CFSG.LargeExtraspecial.S9One
public import CFSG.LargeExtraspecial.S9Cent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem eq_of_finrank_le_one {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {D : Submodule (ZMod 2) U} [FiniteDimensional (ZMod 2) D] (hD : finrank (ZMod 2) D ≤ 1)
    {u v : U} (hu : u ∈ D) (hv : v ∈ D) (hu0 : u ≠ 0) (hv0 : v ≠ 0) : u = v := by
  by_contra huv
  have hli : LinearIndependent (ZMod 2) ![u, v] := linearIndependent_pair_iff.mpr ⟨hu0, hv0, huv⟩
  have h1 := finrank_span_eq_card hli
  have hle : Submodule.span (ZMod 2) (Set.range ![u, v]) ≤ D := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hv
  have h2 := Submodule.finrank_mono hle
  simp only [Fintype.card_fin] at h1
  omega

section Three

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hSp

theorem exists_mem_Abar_conj (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t))
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) {x : S.O}
    (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) :
    ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ x * t * x⁻¹ ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t := by
  by_contra hβ
  push Not at hβ
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have haQ := H.conj_mem
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hxM hβ
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hτV := fix_Vt_of_inf_eq_bot H hτM hτt hinf
  have hW1 : ∀ w ∈ Wone S g t g ((h : G) * g),
      ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g) :=
    fun w hw => apply_sub_mem_Vone_of_fix hCE H hNo C ht ht1 hVQ hSp hh hb h6 hxM hτt hτV hw
  set τ : S.O := x * t * x⁻¹ with hτdef
  set D : Submodule (ZMod 2) S.Qt :=
    Vone S g t g ((h : G) * g) ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hDdef
  have hD1 : finrank (ZMod 2) D ≤ 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq D (Vt S g t)
    have h2 : D ⊓ Vt S g t = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      rintro v ⟨⟨-, hv⟩, hvV⟩
      exact ⟨hvV, hv⟩
    have h3 : D ⊔ Vt S g t ≤ Vone S g t g ((h : G) * g) :=
      sup_le inf_le_left (Vt_le_Vone _ _)
    have h4 := Submodule.finrank_mono h3
    have h5 := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
    rw [h2, finrank_bot] at h1
    omega
  obtain ⟨k, hk, hkD⟩ : ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧
      ∀ w ∈ D, w ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) → w = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w₀, hw₀D, -, hw₀0⟩ := hcon 1 (by rw [map_one]; exact one_mem _)
    apply hw₀0
    refine eq_zero_of_forall_mem_clSub H C ht ht1 hVQ fun k hk => ?_
    obtain ⟨w, hwD, hwP, hw0⟩ := hcon k hk
    rw [← eq_of_finrank_le_one hD1 hwD hw₀D hw0 hw₀0]
    exact hwP
  have hkt := commute_of_mem_Rbar haQ hk
  set τ' : S.O := (S.ρ k)⁻¹ * τ * S.ρ k with hτ'def
  have hτ'x : τ' = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by
    rw [hτ'def, hτdef]
    calc (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k =
        ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ * ((S.ρ k)⁻¹ * S.ρ k) := by group
      _ = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by rw [inv_mul_cancel, mul_one]
  have hkxM : (S.ρ k)⁻¹ * x ∈ S.Mbar := S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM
  have hτ'M : τ' ∈ S.Mbar := by
    rw [hτ'x]
    exact S.Mbar.mul_mem (S.Mbar.mul_mem hkxM (S.Lbar_le_Mbar g ht)) (inv_mem hkxM)
  have hτ't : τ' * t = t * τ' := by
    have hkt' : (S.ρ k)⁻¹ * t = t * (S.ρ k)⁻¹ := by
      calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hkt]
        _ = t * (S.ρ k)⁻¹ := by group
    calc τ' * t = (S.ρ k)⁻¹ * τ * (S.ρ k * t) := by rw [hτ'def]; group
      _ = (S.ρ k)⁻¹ * (τ * t) * S.ρ k := by rw [hkt]; group
      _ = (S.ρ k)⁻¹ * (t * τ) * S.ρ k := by rw [hτt]
      _ = ((S.ρ k)⁻¹ * t) * τ * S.ρ k := by group
      _ = t * τ' := by rw [hkt', hτ'def]; group
  have hτ'V : ∀ v ∈ Vt S g t, (τ' : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    rw [hτ'def, coe_mul_apply, coe_mul_apply, hτV _ (apply_mem_Vt_of_mem_Rbar haQ hk hv),
      inv_apply_apply_O]
  have hτ'P : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t,
      (τ' : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro w hw
    have hwW1 := clSub_inf_Wt_le_Wone H C ht ht1 hVQ hh hb hw
    have hkw1 := apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hk hwW1
    have hkwP := apply_mem_clSub_Qa_mul k hw.1
    have hkQ := conj_mem_QG' S k.2 haQ
    have hτP : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈
        S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) :=
      apply_mem_clSub_of_fix hkQ (conj_ne_z' S k.2 H.conj_ne) hτM
        (hτV _ (cl_mem_Vt (mem_Lbar_mul_of_mem_Rbar H ht hk))) hkwP
    have h1 := hkD _ ⟨hW1 _ hkw1, sub_mem_commSpace _ _⟩ (sub_mem hτP hkwP)
    rw [sub_eq_zero] at h1
    rw [hτ'def, coe_mul_apply, coe_mul_apply, h1, inv_apply_apply_O]
  have hτ'L := commute_Lbar_of_fix hCE H hNo C ht ht1 hVQ hSp hh hb h6 hτ'M hτ't hτ'V hτ'P
  have hτ'mem : τ' ∈ S.Lbar g := by
    rw [hτ'x]
    refine mem_Lbar_of_commute H C ht hkxM fun l hl => ?_
    rw [← hτ'x]
    exact hτ'L l hl
  have hτ'N := hL _ hkxM (hτ'x ▸ hτ'mem)
  rw [← hτ'x] at hτ'N
  apply hβ k hk
  have e : τ = S.ρ k * τ' * (S.ρ k)⁻¹ := by rw [hτ'def]; group
  rw [e]
  exact ⟨conj_mem_Lbar_mul S k hτ'mem, conj_mem_Nbar haQ hkt hτ'N⟩

end Three

end CFSG.LargeExtraspecial.S9
