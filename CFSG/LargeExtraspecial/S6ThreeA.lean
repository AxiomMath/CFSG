module

public import CFSG.LargeExtraspecial.S6Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem clSub_eq_of_cl_eq {g₁ g₂ : G} (h1Q : g₁ * S.z * g₁⁻¹ ∈ S.QG)
    (h1z : g₁ * S.z * g₁⁻¹ ≠ S.z) (h2Q : g₂ * S.z * g₂⁻¹ ∈ S.QG)
    (hcl : S.cl (g₁ * S.z * g₁⁻¹) = S.cl (g₂ * S.z * g₂⁻¹)) :
    S.clSub (S.QG ⊓ S.Qa g₁) = S.clSub (S.QG ⊓ S.Qa g₂) := by
  rcases (S.cl_eq_cl_iff h1Q h2Q).mp hcl with h | h
  · rw [S.Qa_eq_of_conj_eq h.symm]
  · rw [S.QG_inf_Qa_eq_of_conj_eq_mul_z h1Q h1z h]

variable (S g) in
@[expose] noncomputable def Vone (t : S.O) (g₁ g₂ : G) : Submodule (ZMod 2) S.Qt :=
  (S.clSub (S.QG ⊓ S.Qa g₁) ⊔ Vt S g t) ⊓ (S.clSub (S.QG ⊓ S.Qa g₂) ⊔ Vt S g t)

theorem Vt_le_Vone {t : S.O} (g₁ g₂ : G) : Vt S g t ≤ Vone S g t g₁ g₂ :=
  le_inf le_sup_right le_sup_right

theorem inf_le_Vone {t : S.O} (g₁ g₂ : G) :
    S.clSub (S.QG ⊓ S.Qa g₁) ⊓ S.clSub (S.QG ⊓ S.Qa g₂) ≤ Vone S g t g₁ g₂ :=
  le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans le_sup_left)

theorem Vone_comm {t : S.O} (g₁ g₂ : G) : Vone S g t g₁ g₂ = Vone S g t g₂ g₁ :=
  inf_comm _ _

theorem map_Vone (H : Hyp4 S g) {t : S.O} {k : S.M} (hk : S.ρ k ∈ Rbar S g t) (g₁ g₂ : G) :
    (Vone S g t g₁ g₂).map ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap =
      Vone S g t ((k : G) * g₁) ((k : G) * g₂) := by
  set e := ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with he
  have hP : ∀ g' : G, (S.clSub (S.QG ⊓ S.Qa g')).map e.toLinearMap =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g')) := by
    intro g'
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact apply_mem_clSub_Qa_mul k hw
    · intro hv
      refine ⟨(((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, (mem_clSub_Qa_mul_iff k).mp hv, ?_⟩
      exact apply_inv_apply_O _ v
  have hV : (Vt S g t).map e.toLinearMap = Vt S g t := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq e _)
    rintro _ ⟨v, hv, rfl⟩
    exact apply_mem_Vt_of_mem_Rbar H.conj_mem hk hv
  unfold Vone
  rw [Submodule.map_inf _ e.injective, Submodule.map_sup, Submodule.map_sup, hP, hP, hV]

section Pair

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
  (hk' : S.ρ k' ∈ Rbar S g t)
  (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g))
include H C ht ht1 hVQ hk hk' hkk'

theorem exists_add_mem_clSub {v : S.Qt} (hv : v ∈ Vt S g t) :
    ∃ ε : ZMod 2, v + ε • S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have hcd := beta_bV_bV H C ht ht1 hVQ hk hk' hkk'
  rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ (bV htk) ⟨v, hv⟩) with h0 | h1
  · refine ⟨0, ?_⟩
    rw [zero_smul, add_zero]
    exact (beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk ⟨v, hv⟩).mp h0
  · refine ⟨1, ?_⟩
    rw [one_smul]
    have h2 : beta H C ht ht1 hVQ (bV htk) (⟨v, hv⟩ + bV htk') = 0 := by
      rw [map_add, h1, hcd]
      rfl
    exact (beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk _).mp h2

theorem Vone_eq :
    Vone S g t ((k : G) * g) ((k' : G) * g) =
      (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g))) ⊔
        Vt S g t := by
  have hkk'' : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa ((k' : G) * g) := by
    intro hmem
    have hne : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ≠ (k : G) * g * S.z * ((k : G) * g)⁻¹ :=
      fun e => hkk' (e ▸ S.conj_z_mem_Qa _)
    exact hkk' (S.mem_Qa_symm hne.symm hmem)
  refine le_antisymm (fun x hx => ?_) (sup_le (inf_le_Vone _ _) (Vt_le_Vone _ _))
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hxa
  obtain ⟨ε, hε⟩ := exists_add_mem_clSub H C ht ht1 hVQ hk hk' hkk' hv
  obtain ⟨p', hp', v', hv', hpv⟩ := Submodule.mem_sup.mp hxb
  obtain ⟨δ, hδ⟩ := exists_add_mem_clSub H C ht ht1 hVQ hk' hk hkk'' hv'
  set c := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hc
  set d := S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) with hd
  have hcP : c ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) :=
    cl_mem_clSub_self (H.mul k).conj_mem
  have hdP : d ∈ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) :=
    cl_mem_clSub_self (H.mul k').conj_mem
  have hcV : c ∈ Vt S g t := cl_mem_Vt (mem_Lbar_mul_of_mem_Rbar H ht hk)
  have hdV : d ∈ Vt S g t := cl_mem_Vt (mem_Lbar_mul_of_mem_Rbar H ht hk')
  have hmem : p + v - ε • d - δ • c ∈
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) := by
    constructor
    · have e : p + v - ε • d - δ • c = p + (v + ε • d) + δ • c := by
        rw [vec_sub, vec_sub]; abel
      rw [e]
      exact add_mem (add_mem hp hε) (Submodule.smul_mem _ _ hcP)
    · rw [← hpv]
      have e : p' + v' - ε • d - δ • c = p' + (v' + δ • c) + ε • d := by
        rw [vec_sub, vec_sub]; abel
      rw [e]
      exact add_mem (add_mem hp' hδ) (Submodule.smul_mem _ _ hdP)
  have e : p + v = (p + v - ε • d - δ • c) + (ε • d + δ • c) := by abel
  rw [e]
  exact add_mem (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right
    (add_mem (Submodule.smul_mem _ _ hdV) (Submodule.smul_mem _ _ hcV)))

omit C ht1 hVQ hk in
theorem fix_of_mem_inf' {x : S.O} (hx : x ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g))) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have h1 := Lbar_apply_sub_mem_span' (H.mul k).conj_mem hv.1 hx.1
  have h2 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) :=
    sub_mem (Nbar_apply_mem_clSub (H.mul k').conj_mem (H.mul k').conj_ne (cl_mem_Vt htk')
      hx.2 hv.2) hv.2
  have hcoe : ((k' * k⁻¹ : S.M) : G) * ((k : G) * g) = (k' : G) * g := by simp [mul_assoc]
  have hcd : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∉
      S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) := by
    have := S.cl_not_mem_clSub_of_not_mem_Qa (g := (k : G) * g) (h := ((k' * k⁻¹ : S.M) : G))
      (H.mul k).conj_mem (H.mul k).conj_ne (k' * k⁻¹).2 (by rw [hcoe]; exact hkk')
    rwa [hcoe] at this
  rcases mem_span_cl_iff.mp h1 with h0 | ha
  · exact sub_eq_zero.mp h0
  · exact absurd (ha ▸ h2) hcd

end Pair

end CFSG.LargeExtraspecial.S6
