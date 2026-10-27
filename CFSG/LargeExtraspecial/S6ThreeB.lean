module

public import CFSG.LargeExtraspecial.S6ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_Vt_le_width (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) :
    finrank (ZMod 2) (Vt S g t) ≤ S.width := by
  have h1 := finrank_Wt (S := S) (g := g) (t := t)
  have h2 := Submodule.finrank_mono (Vt_le_Wt H ht1)
  have h3 := S.finrank_Qt_eq_two_mul_width
  omega

section Sp

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
include H C ht ht1 hVQ hSp

theorem card_Lbar_inf_Nbar_sp :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) =
      2 ^ (S.width - finrank (ZMod 2) (Vt S g t)) := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have h1 := card_Lbar_eq_mul H.conj_mem ht (t := t)
  rw [C.card_Lbar, hSp.LmodN_eq, card_spPointRadical (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (aV_ne_zero H ht)] at h1
  have h2 := finrank_Vt_le_width H ht1
  have h3 : 0 < finrank (ZMod 2) (Vt S g t) :=
    Nat.pos_of_ne_zero fun h0 => Vt_ne_bot H ht (Submodule.finrank_eq_zero.mp h0)
  have e : 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) * 2 ^ (S.width - finrank (ZMod 2) (Vt S g t)) =
      2 ^ (S.width - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← e] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm

theorem finrank_fixSub_sp {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓
      fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t)) = finrank (ZMod 2) (Vt S g t) := by
  have h1 := card_mul_two_pow_finrank_fix (H.mul k) (C.mul k)
    (inf_le_left : S.Lbar ((k : G) * g) ⊓ Nbar S g t ≤ S.Lbar ((k : G) * g))
  rw [card_Lbar_mul_inf_Nbar H hk, card_Lbar_inf_Nbar_sp H C ht ht1 hVQ hSp, ← pow_add] at h1
  have h2 := finrank_Vt_le_width H ht1
  have := Nat.pow_right_injective le_rfl h1
  omega

variable {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
  (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g))
include hk hk' hkk'

omit hSp in
theorem Vone_inf_le_fixSub :
    Vone S g t ((k : G) * g) ((k' : G) * g) ⊓ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ≤
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t) := by
  intro v hv
  refine ⟨hv.2, fun x hx => ?_⟩
  have hv1 := hv.1
  rw [Vone_eq H C ht ht1 hVQ hk hk' hkk'] at hv1
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv1
  rw [map_add, fix_of_mem_inf' H ht hk' hkk' hx hw, (mem_Nbar.mp hx.2).2 u hu]

theorem finrank_Vone_le :
    finrank (ZMod 2) (Vone S g t ((k : G) * g) ((k' : G) * g)) ≤
      finrank (ZMod 2) (Vt S g t) + 1 := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have h2 := finrank_clSub_inf_Vt (H.mul k) (C.mul k) htk ht1 (not_V_le_Qa_mul H hVQ hk)
  rw [Vt_mul] at h2
  have h3 := Submodule.finrank_mono (Vone_inf_le_fixSub H C ht ht1 hVQ hk hk' hkk')
  rw [finrank_fixSub_sp H C ht ht1 hVQ hSp hk] at h3
  set P := S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) with hP
  set X := Vone S g t ((k : G) * g) ((k' : G) * g) with hX
  have hmod : X = Vt S g t ⊔ P ⊓ X := by
    have hle : X ≤ P ⊔ Vt S g t := inf_le_left
    rw [← sup_inf_assoc_of_le P (Vt_le_Vone _ _), sup_comm, inf_eq_right.mpr hle]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t) (P ⊓ X)
  rw [← hmod] at h1
  have e : Vt S g t ⊓ (P ⊓ X) = P ⊓ Vt S g t := by
    rw [inf_comm P X, ← inf_assoc, inf_eq_left.mpr (Vt_le_Vone _ _), inf_comm]
  rw [e] at h1
  have h4 : finrank (ZMod 2) ↥(P ⊓ X) = finrank (ZMod 2) ↥(X ⊓ P) := by rw [inf_comm]
  omega

omit hSp in
theorem Nbar_fix_Vone
    (hN : Nbar S g t = (S.Lbar ((k : G) * g) ⊓ Nbar S g t) ⊔ (S.Lbar ((k' : G) * g) ⊓ Nbar S g t))
    {x : S.O} (hx : x ∈ Nbar S g t) {v : S.Qt}
    (hv : v ∈ Vone S g t ((k : G) * g) ((k' : G) * g)) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hkk'' : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa ((k' : G) * g) := by
    intro hmem
    have hne : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ≠ (k : G) * g * S.z * ((k : G) * g)⁻¹ :=
      fun e => hkk' (e ▸ S.conj_z_mem_Qa _)
    exact hkk' (S.mem_Qa_symm hne.symm hmem)
  let K : Subgroup S.O :=
    { carrier := {x | ∀ v ∈ Vone S g t ((k : G) * g) ((k' : G) * g),
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
      mul_mem' := fun {x y} hx hy v hv => by rw [coe_mul_apply, hy v hv, hx v hv]
      one_mem' := fun v _ => rfl
      inv_mem' := fun {x} hx v hv => by
        conv_lhs => rw [← hx v hv]
        exact inv_apply_apply_O x v }
  have hle : Nbar S g t ≤ K := by
    rw [hN]
    refine sup_le (fun x hx v hv => ?_) (fun x hx v hv => ?_)
    · rw [Vone_eq H C ht ht1 hVQ hk hk' hkk'] at hv
      obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, fix_of_mem_inf' H ht hk' hkk' hx hw, (mem_Nbar.mp hx.2).2 u hu]
    · rw [Vone_eq H C ht ht1 hVQ hk hk' hkk'] at hv
      obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, fix_of_mem_inf' H ht hk hkk'' hx (by rw [inf_comm]; exact hw),
        (mem_Nbar.mp hx.2).2 u hu]
  exact hle hx v hv

end Sp

theorem exists_mem_Rbar_pair (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    {k₁ k₂ k₃ k₄ : S.M} (h1 : S.ρ k₁ ∈ Rbar S g t) (h2 : S.ρ k₂ ∈ Rbar S g t)
    (h3 : S.ρ k₃ ∈ Rbar S g t) (h4 : S.ρ k₄ ∈ Rbar S g t)
    (h12 : (k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹ ∉ S.Qa ((k₁ : G) * g))
    (h34 : (k₄ : G) * g * S.z * ((k₄ : G) * g)⁻¹ ∉ S.Qa ((k₃ : G) * g)) :
    ∃ j : S.M, S.ρ j ∈ Rbar S g t ∧
      S.cl ((j : G) * ((k₁ : G) * g) * S.z * ((j : G) * ((k₁ : G) * g))⁻¹) =
        S.cl ((k₃ : G) * g * S.z * ((k₃ : G) * g)⁻¹) ∧
      S.cl ((j : G) * ((k₂ : G) * g) * S.z * ((j : G) * ((k₂ : G) * g))⁻¹) =
        S.cl ((k₄ : G) * g * S.z * ((k₄ : G) * g)⁻¹) := by
  set β := beta H C ht ht1 hVQ with hβ
  have hβa := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  have ht1' := mem_Lbar_mul_of_mem_Rbar H ht h1
  have ht2' := mem_Lbar_mul_of_mem_Rbar H ht h2
  have ht3' := mem_Lbar_mul_of_mem_Rbar H ht h3
  have ht4' := mem_Lbar_mul_of_mem_Rbar H ht h4
  obtain ⟨r, hr, hr1, hr2⟩ := S2.exists_mem_spRadGen_apply_eq_pair hβa hnd (F := ⊥) (by simp)
    (p := bV ht1') (p₁ := bV ht2') (p' := bV ht3') (p₁' := bV ht4') (by simp) (by simp)
    (by simp) (by simp) (bV_ne_zero H ht1') (bV_ne_zero H ht3')
    (beta_bV_bV H C ht ht1 hVQ h1 h2 h12) (beta_bV_bV H C ht ht1 hVQ h3 h4 h34)
  have hrR : r ∈ RmodN S g t := by
    rw [hSp.eq_sp, ← S2.spFix_bot]
    exact S2.spRadGen_le_spFix _ hr
  rw [← range_resV H.conj_mem t] at hrR
  obtain ⟨⟨x, hx⟩, rfl⟩ := hrR
  obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  refine ⟨j, hx, ?_, ?_⟩
  · have := congrArg Subtype.val hr1
    rw [coe_resV_apply, coe_bV, coe_bV, ρ_cl_conj_z S j (H.mul k₁).conj_mem] at this
    simpa [mul_assoc] using this
  · have := congrArg Subtype.val hr2
    rw [coe_resV_apply, coe_bV, coe_bV, ρ_cl_conj_z S j (H.mul k₂).conj_mem] at this
    simpa [mul_assoc] using this

end CFSG.LargeExtraspecial.S6
