module

public import CFSG.LargeExtraspecial.S9IIa
public import CFSG.LargeExtraspecial.S9OneB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Cent

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem not_forall_apply_sub_mem_Vone
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    ¬ ∀ w ∈ Wone S g t g ((h : G) * g),
      ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g) := by
  intro htriv
  have haQ := H.conj_mem
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hxM hβ
  have hτV := fix_Vt_of_inf_eq_bot H hτM hτt hinf
  generalize hτe : x * t * x⁻¹ = τ at hτM hτt hβ htriv hinf hτV
  have hDdim : finrank (ZMod 2) ↥(Vone S g t g ((h : G) * g) ⊓
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 1 := by
    have hdisj : Vt S g t ⊓ (Vone S g t g ((h : G) * g) ⊓
        commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu' : u ∈ Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hu.1, hu.2.2⟩
      rwa [hinf] at hu'
    have hsup : Vt S g t ⊔ (Vone S g t g ((h : G) * g) ⊓
        commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ Vone S g t g ((h : G) * g) :=
      sup_le (Vt_le_Vone _ _) inf_le_left
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
      (Vone S g t g ((h : G) * g) ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    rw [hdisj, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_mono hsup
    have h3 := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
    omega
  have hk : ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ ∀ u ∈ Vone S g t g ((h : G) * g) ⊓
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt), u ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) → u = 0 := by
    by_cases hD : ∃ w ∈ Vone S g t g ((h : G) * g) ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt), w ≠ 0
    · obtain ⟨w, hwD, hw0⟩ := hD
      by_contra hcon
      push Not at hcon
      apply hw0
      refine eq_zero_of_forall_mem_clSub H C ht ht1 hVQ fun k hk => ?_
      obtain ⟨u, huD, huP, hu0⟩ := hcon k hk
      rwa [eq_of_finrank_le_one hDdim hwD huD hw0 hu0]
    · push Not at hD
      exact ⟨1, by rw [map_one]; exact one_mem _, fun u hu _ => hD u hu⟩
  obtain ⟨k, hkR, hkD⟩ := hk
  have hkt : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar haQ hkR
  have hkit : (S.ρ k)⁻¹ * t = t * (S.ρ k)⁻¹ := by
    calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hkt]
      _ = t * (S.ρ k)⁻¹ := by group
  have hτ'M : (S.ρ k)⁻¹ * τ * S.ρ k ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hkR)) hτM) (Rbar_le_Mbar hkR)
  have hτ't : (S.ρ k)⁻¹ * τ * S.ρ k * t = t * ((S.ρ k)⁻¹ * τ * S.ρ k) := by
    rw [mul_assoc, hkt, ← mul_assoc, mul_assoc _ τ t, hτt, ← mul_assoc, mul_assoc _ t τ,
      ← mul_assoc, hkit]
    group
  have hτ'V : ∀ v ∈ Vt S g t, (((S.ρ k)⁻¹ * τ * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    rw [coe_mul_apply, coe_mul_apply, hτV _ (apply_mem_Vt_of_mem_Rbar haQ hkR hv),
      inv_apply_apply_O]
  have hτ'a := hτ'V _ (cl_a_mem_Vt ht)
  have happ : ∀ w, (((S.ρ k)⁻¹ * τ * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
          (S.ρ k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    intro w
    rw [coe_mul_apply, coe_mul_apply, map_sub, inv_apply_apply_O]
  have htriv' : ∀ w ∈ Wone S g t g ((h : G) * g),
      (((S.ρ k)⁻¹ * τ * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
        Vone S g t g ((h : G) * g) := by
    intro w hw
    rw [happ]
    exact apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb (inv_mem hkR)
      (htriv _ (apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hkR hw))
  have hint' : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g) ⊓
      commSpace ((((S.ρ k)⁻¹ * τ * S.ρ k : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨⟨huP, huV⟩, huC⟩
    rw [Submodule.mem_bot]
    obtain ⟨q, rfl⟩ := mem_commSpace.mp huC
    have h0 := hkD ((S.ρ k : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((S.ρ k)⁻¹ * τ * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q)) ⟨?_, ?_⟩ ?_
    · rw [map_eq_zero_iff _ (S.ρ k : S.Qt ≃ₗ[ZMod 2] S.Qt).injective] at h0
      exact h0
    · exact apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hkR huV
    · rw [happ, apply_inv_apply_O]
      exact sub_mem_commSpace _ _
    · exact apply_mem_clSub_Qa_mul k huP
  have hτ'P : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t,
      (((S.ρ k)⁻¹ * τ * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro w hw
    have hmem : (((S.ρ k)⁻¹ * τ * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
        S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g) ⊓
          commSpace ((((S.ρ k)⁻¹ * τ * S.ρ k : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      ⟨⟨sub_mem (apply_mem_clSub_of_fix haQ H.conj_ne hτ'M hτ'a hw.1) hw.1,
        htriv' w (clSub_inf_Wt_le_Wone H C ht ht1 hVQ hh hb hw)⟩, sub_mem_commSpace _ w⟩
    rw [hint', Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  have hτ'A := commute_Abar_of_fix hCE H hNo C ht ht1 hVQ hSp hh hb hτ'M hτ't hτ'V hτ'P
  have hτ'Pa := fix_clSub_of_commute_Abar hCE H hNo C ht ht1 hVQ hSp hh hb hτ'M hτ'a hτ'A hint'
  have hτ'L := commute_Lbar_of_fix_clSub H C hτ'M hτ'a hτ'Pa
  have hx' : (S.ρ k)⁻¹ * x * t * ((S.ρ k)⁻¹ * x)⁻¹ = (S.ρ k)⁻¹ * τ * S.ρ k := by
    rw [← hτe]
    group
  have hx'M : (S.ρ k)⁻¹ * x ∈ S.Mbar := S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hkR)) hxM
  have hmemL := mem_Lbar_of_commute H C ht hx'M (fun l hl => by rw [hx']; exact hτ'L l hl)
  have hmemN := hL _ hx'M hmemL
  rw [hx'] at hmemL hmemN
  have e : S.ρ k * ((S.ρ k)⁻¹ * τ * S.ρ k) * (S.ρ k)⁻¹ = τ := by group
  refine hβ k hkR ⟨?_, ?_⟩
  · have := conj_mem_Lbar_mul S k hmemL
    rwa [e] at this
  · have := conj_mem_Nbar haQ hkt hmemN
    rwa [e] at this

end Cent

end CFSG.LargeExtraspecial.S9
