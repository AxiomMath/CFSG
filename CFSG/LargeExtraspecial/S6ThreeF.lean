module

public import CFSG.LargeExtraspecial.S6ThreeE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Vone_mul (k : S.M) {t : S.O} (g₁ g₂ : G) :
    Vone S ((k : G) * g) t g₁ g₂ = Vone S g t g₁ g₂ := by
  unfold Vone
  rw [Vt_mul]

theorem Wone_mul (k : S.M) {t : S.O} (g₁ g₂ : G) :
    Wone S ((k : G) * g) t g₁ g₂ = Wone S g t g₁ g₂ := by
  unfold Wone
  rw [Vone_mul]

theorem cl_mem_of_Lbar_invariant (H : Hyp4 S g) {A : Submodule (ZMod 2) S.Qt}
    (hA : ∀ l ∈ S.Lbar g, ∀ v ∈ A, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ A) (hA0 : A ≠ ⊥) :
    S.cl (g * S.z * g⁻¹) ∈ A := by
  obtain ⟨u, hu, hu0, hufix⟩ := exists_fixed_of_isPGroup S (isPGroup_Lbar S H.conj_mem) hA hA0
  have hfx : u ∈ fixSub S (S.Lbar g) := hufix
  have hua : u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := H.fixSub_eq ▸ hfx
  rcases mem_span_cl_iff.mp hua with h0 | rfl
  · exact absurd h0 hu0
  · exact hu

section PairGen

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
  (hk' : S.ρ k' ∈ Rbar S g t)
  (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g))
include H C ht ht1 hVQ hk hk' hkk'

omit [Finite G] H C ht ht1 hVQ hk hk' hkk' in
theorem coe_mul_inv_mul :
    ((k' * k⁻¹ : S.M) : G) * ((k : G) * g) = (k' : G) * g := by
  simp [mul_assoc]

omit H C ht ht1 hVQ hkk' in
theorem mul_inv_mem_Rbar_mul : S.ρ (k' * k⁻¹) ∈ Rbar S ((k : G) * g) t := by
  rw [Rbar_mul, map_mul, map_inv]
  exact mul_mem hk' (inv_mem hk)

theorem clSub_inf_clSub_le_Wt_pair :
    S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ≤ Wt S g t := by
  have := clSub_inf_clSub_le_Wt (H.mul k) (C.mul k) (mem_Lbar_mul_of_mem_Rbar H ht hk) ht1
    (not_V_le_Qa_mul H hVQ hk) (mul_inv_mem_Rbar_mul hk hk')
    (by rw [coe_mul_inv_mul]; exact hkk')
  rwa [coe_mul_inv_mul, Wt_mul] at this

theorem finrank_clSub_inf_clSub_pair :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓
      S.clSub (S.QG ⊓ S.Qa ((k' : G) * g))) + 2 =
      finrank (ZMod 2) (Vone S g t ((k : G) * g) ((k' : G) * g)) := by
  have := finrank_clSub_inf_clSub (H.mul k) (C.mul k) (mem_Lbar_mul_of_mem_Rbar H ht hk) ht1
    (not_V_le_Qa_mul H hVQ hk) (mul_inv_mem_Rbar_mul hk hk')
    (by rw [coe_mul_inv_mul]; exact hkk')
  rwa [coe_mul_inv_mul, Vone_mul] at this

theorem clSub_inf_Wt_le_Wone_pair :
    S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t ≤
      Wone S g t ((k : G) * g) ((k' : G) * g) := by
  have := clSub_inf_Wt_le_Wone (H.mul k) (C.mul k) (mem_Lbar_mul_of_mem_Rbar H ht hk) ht1
    (not_V_le_Qa_mul H hVQ hk) (mul_inv_mem_Rbar_mul hk hk')
    (by rw [coe_mul_inv_mul]; exact hkk')
  rwa [coe_mul_inv_mul, Wt_mul, Wone_mul] at this

theorem clSub_inf_Wt_le_Wone_pair' :
    S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t ≤
      Wone S g t ((k : G) * g) ((k' : G) * g) := by
  have := clSub_inf_Wt_le_Wone' (H.mul k) (C.mul k) (mem_Lbar_mul_of_mem_Rbar H ht hk) ht1
    (not_V_le_Qa_mul H hVQ hk) (mul_inv_mem_Rbar_mul hk hk')
    (by rw [coe_mul_inv_mul]; exact hkk')
  rwa [coe_mul_inv_mul, Wt_mul, Wone_mul] at this

theorem Vone_le_Wone_pair :
    Vone S g t ((k : G) * g) ((k' : G) * g) ≤ Wone S g t ((k : G) * g) ((k' : G) * g) := by
  have := Vone_le_Wone (H.mul k) (C.mul k) (mem_Lbar_mul_of_mem_Rbar H ht hk) ht1
    (not_V_le_Qa_mul H hVQ hk) (mul_inv_mem_Rbar_mul hk hk')
    (by rw [coe_mul_inv_mul]; exact hkk')
  rwa [coe_mul_inv_mul, Vone_mul, Wone_mul] at this

theorem Vone_le_Wt_pair : Vone S g t ((k : G) * g) ((k' : G) * g) ≤ Wt S g t := by
  have := Vone_le_Wt (H.mul k) (C.mul k) (mem_Lbar_mul_of_mem_Rbar H ht hk) ht1
    (not_V_le_Qa_mul H hVQ hk) (mul_inv_mem_Rbar_mul hk hk')
    (by rw [coe_mul_inv_mul]; exact hkk')
  rwa [coe_mul_inv_mul, Vone_mul, Wt_mul] at this

end PairGen

theorem Vone_indecomposable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (h : S.M)
    {A B : Submodule (ZMod 2) S.Qt}
    (hA : ∀ x ∈ Rbar S g t, ∀ v ∈ A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ A)
    (hB : ∀ x ∈ Rbar S g t, ∀ v ∈ B, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ B)
    (_hsup : A ⊔ B = Vone S g t g ((h : G) * g)) (hinf : A ⊓ B = ⊥) : A = ⊥ ∨ B = ⊥ := by
  by_contra hne
  push Not at hne
  have ha := cl_mem_of_Lbar_invariant H (fun l hl => hA l (Lbar_le_Rbar ht hl)) hne.1
  have hb' := cl_mem_of_Lbar_invariant H (fun l hl => hB l (Lbar_le_Rbar ht hl)) hne.2
  have : S.cl (g * S.z * g⁻¹) ∈ A ⊓ B := ⟨ha, hb'⟩
  rw [hinf, Submodule.mem_bot] at this
  exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this

theorem Qt_Wone_indecomposable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (h : S.M)
    {A B : Submodule (ZMod 2) S.Qt}
    (hA : ∀ x ∈ Rbar S g t, ∀ v ∈ A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ A)
    (hB : ∀ x ∈ Rbar S g t, ∀ v ∈ B, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ B)
    (hsup : A ⊔ B = ⊤) (hinf : A ⊓ B = Wone S g t g ((h : G) * g)) :
    A = Wone S g t g ((h : G) * g) ∨ B = Wone S g t g ((h : G) * g) := by
  set A' := LinearMap.BilinForm.orthogonal S.q.polarBilin A with hA'
  set B' := LinearMap.BilinForm.orthogonal S.q.polarBilin B with hB'
  have hmem : ∀ {D : Submodule (ZMod 2) S.Qt} {v : S.Qt},
      v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin D ↔ ∀ u ∈ D, polar S.q u v = 0 := by
    intro D v
    simp [LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply]
  have hinv : ∀ {D : Submodule (ZMod 2) S.Qt},
      (∀ x ∈ Rbar S g t, ∀ v ∈ D, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ D) →
      ∀ l ∈ S.Lbar g, ∀ v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin D,
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin D := by
    intro D hD l hl v hv
    rw [hmem] at hv ⊢
    intro u hu
    have hlR : l ∈ Rbar S g t := Lbar_le_Rbar ht hl
    have := hv _ (hD _ (inv_mem hlR) u hu)
    rwa [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup l.2, apply_inv_apply_O]
      at this
  have hAB : A' ⊓ B' = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvA, hvB⟩
    rw [Submodule.mem_bot]
    refine S.q_nondegenerate.1 v fun u => ?_
    have hu : u ∈ A ⊔ B := hsup ▸ Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
    rw [polarBilin_apply_apply, polar_comm, polar_add_left, (hmem.mp hvA) x hx,
      (hmem.mp hvB) y hy, add_zero]
  have hcases : A' = ⊥ ∨ B' = ⊥ := by
    by_contra hne
    push Not at hne
    have ha := cl_mem_of_Lbar_invariant H (hinv hA) hne.1
    have hb' := cl_mem_of_Lbar_invariant H (hinv hB) hne.2
    have : S.cl (g * S.z * g⁻¹) ∈ A' ⊓ B' := ⟨ha, hb'⟩
    rw [hAB, Submodule.mem_bot] at this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this
  have htop : ∀ {D : Submodule (ZMod 2) S.Qt},
      LinearMap.BilinForm.orthogonal S.q.polarBilin D = ⊥ → D = ⊤ := by
    intro D hD
    have := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate D
    rw [hD, finrank_bot] at this
    have h2 := Submodule.finrank_le D
    exact Submodule.eq_top_of_finrank_eq (by omega)
  rcases hcases with h0 | h0
  · right
    rw [← hinf, htop h0, top_inf_eq]
  · left
    rw [← hinf, htop h0, inf_top_eq]

section Sp

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hSp

theorem Wone_eq_sup_pair {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t) ⊔
        (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t) =
      Wone S g t ((k : G) * g) ((k' : G) * g) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have dA := finrank_clSub_inf_Wt (H.mul k) (C.mul k) htk ht1 (not_V_le_Qa_mul H hVQ hk)
  have dB := finrank_clSub_inf_Wt (H.mul k') (C.mul k') htk' ht1 (not_V_le_Qa_mul H hVQ hk')
  rw [Wt_mul] at dA dB
  have dP := finrank_clSub_inf_clSub_pair H C ht ht1 hVQ hk hk' hkk'
  have dV := finrank_Vone_eq hCE H hNo C ht ht1 hVQ hSp hk hk' hkk'
  have dW := finrank_Wone (S := S) (g := g) (t := t) ((k : G) * g) ((k' : G) * g)
  have dQ := S.finrank_Qt_eq_two_mul_width
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t)
    (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t)
  have e : (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t) =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) := by
    rw [← inf_inf_distrib_right,
      inf_eq_left.mpr (clSub_inf_clSub_le_Wt_pair H C ht ht1 hVQ hk hk' hkk')]
  rw [e] at hs
  refine Submodule.eq_of_le_of_finrank_le
    (sup_le (clSub_inf_Wt_le_Wone_pair H C ht ht1 hVQ hk hk' hkk')
      (clSub_inf_Wt_le_Wone_pair' H C ht ht1 hVQ hk hk' hkk')) ?_
  omega

theorem Wone_eq_Wone {k₁ k₂ k₃ k₄ : S.M} (h1 : S.ρ k₁ ∈ Rbar S g t)
    (h2 : S.ρ k₂ ∈ Rbar S g t) (h3 : S.ρ k₃ ∈ Rbar S g t) (h4 : S.ρ k₄ ∈ Rbar S g t)
    (h12 : (k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹ ∉ S.Qa ((k₁ : G) * g))
    (h34 : (k₄ : G) * g * S.z * ((k₄ : G) * g)⁻¹ ∉ S.Qa ((k₃ : G) * g)) :
    Wone S g t ((k₁ : G) * g) ((k₂ : G) * g) = Wone S g t ((k₃ : G) * g) ((k₄ : G) * g) := by
  unfold Wone
  rw [Vone_eq_Vone hCE H hNo C ht ht1 hVQ hSp h1 h2 h3 h4 h12 h34]

section Fixed

variable {h : S.M} (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hh hb

theorem Vone_pair_eq {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    Vone S g t ((k : G) * g) ((k' : G) * g) = Vone S g t g ((h : G) * g) := by
  have h1 := pair_one (t := t) hb
  have := Vone_eq_Vone hCE H hNo C ht ht1 hVQ hSp hk hk' h1.1 hh hkk' h1.2
  simpa using this

theorem Wone_pair_eq {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    Wone S g t ((k : G) * g) ((k' : G) * g) = Wone S g t g ((h : G) * g) := by
  unfold Wone
  rw [Vone_pair_eq hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk']

theorem apply_mem_Wone {x : S.O} (hx : x ∈ Rbar S g t) {w : S.Qt}
    (hw : w ∈ Wone S g t g ((h : G) * g)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wone S g t g ((h : G) * g) := by
  rw [mem_Wone] at hw ⊢
  intro u hu
  have hu' := apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb (inv_mem hx) hu
  have := hw _ hu'
  rwa [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2, apply_inv_apply_O] at this

end Fixed

end Sp

end CFSG.LargeExtraspecial.S6
