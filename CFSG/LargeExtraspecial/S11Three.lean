module

public import CFSG.LargeExtraspecial.S11ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M} {u : G}

theorem Conf.commutator_facts (hy : Hyp S g) (K : Conf S g t τ u) {y : G} (hyQ : y ∈ S.QG) :
    y * τ * y⁻¹ * (τ : G)⁻¹ ∈ S.QG ∧
      S.cl (y * τ * y⁻¹ * (τ : G)⁻¹) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) - S.cl y ∧
      (y * τ * y⁻¹ * (τ : G)⁻¹) * (y * τ * y⁻¹ * (τ : G)⁻¹) = 1 ∧
      y * τ * y⁻¹ = τ * (y * τ * y⁻¹ * (τ : G)⁻¹) := by
  set c := y * τ * y⁻¹ * (τ : G)⁻¹ with hc
  have hcQ : c ∈ S.QG := by
    have := S.commutator_mem_QG' τ.2 hyQ
    simpa using this
  have hcl : S.cl c = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) - S.cl y := by
    rw [hc, S.cl_commutator' τ.2 hyQ, ← K.rho_eq]
  have hcc : c * c = 1 := by
    have h1 : S.q (S.cl c) = 0 := by
      rw [hcl]
      exact K.q_eq_zero hy (sub_mem_commSpace _ _)
    rw [← pow_two]
    exact (S.q_cl_eq_zero_iff hcQ).mp h1
  have hττ : (τ : G) * τ = 1 := by rw [K.conj_eq]; exact conj_z_mul_self S u
  have hτi : (τ : G)⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have e1 : (τ : G) * c * τ = c⁻¹ := by
    rw [hc, show (τ : G) * (y * τ * y⁻¹ * (τ : G)⁻¹) * τ = τ * y * τ * y⁻¹ by group,
      show (y * (τ : G) * y⁻¹ * (τ : G)⁻¹)⁻¹ = τ * y * (τ : G)⁻¹ * y⁻¹ by group, hτi]
  have e2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hτc : (τ : G) * c = c * τ := by
    calc (τ : G) * c = τ * c * τ * (τ : G)⁻¹ := by group
      _ = c * τ := by rw [e1, e2, hτi]
  refine ⟨hcQ, hcl, hcc, ?_⟩
  rw [hτc, hc]
  group

theorem Conf.timmesfeld_11_3 (hy : Hyp S g) (K : Conf S g t τ u) :
    S.clSub (S.QG ⊓ S.Qa u) = Vt S g t := by
  refine le_antisymm ?_ (K.Vt_le hy)
  intro v hvE
  by_contra hvV
  obtain ⟨α, hα, hαQ, rfl⟩ := S.mem_clSub_iff.mp hvE
  have hτQ : (τ : G) ∉ S.QG := K.not_mem_QG
  have hα0 : S.cl α ≠ 0 := fun h => hvV (h ▸ zero_mem _)
  have hα1 : α ≠ 1 := fun h => hα0 (by rw [h, S.cl_one])
  have hαz : ∀ j : G, j * S.z * j⁻¹ ≠ α := fun j hj => hvV (K.cl_mem_Vt_of_conj hy hα hj)
  have hα2 : α * α = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_inf S τ.2 K.conj_eq hτQ hα
  have hαT : S.cl α ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) → S.cl α ∈ Tt S g t :=
    fun h => K.inf_commSpace_le_Tt hy ⟨hvE, h⟩
  have hVT : Vt S g t ≤ Tt S g t := Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin
  have hVα : ∀ v' ∈ Vt S g t, ∃ w, polar S.q (S.cl α) w = 0 ∧
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = v' := by
    intro v' hv'
    by_cases hU : S.cl α ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
    · exact K.exists_orth_of_mem_Tt hy (hαT hU) hv'
    · exact exists_orth_of_not_mem_commSpace K.mul_self hU (Tt_le_commSpace (hVT hv'))
  have hconj : ∀ {y x : G}, y ∈ S.QG → polar S.q (S.cl α) (S.cl y) = 0 → x ∈ S.QG →
      S.cl x = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) - S.cl y →
      y * α = α * y ∧ (y * τ * y⁻¹ = τ * x ∨ y * τ * y⁻¹ = τ * x * S.z) := by
    intro y x hyQ hyα hxQ hxcl
    obtain ⟨hcQ, hccl, -, hcτ⟩ := K.commutator_facts hy hyQ
    refine ⟨((S.polar_cl_eq_zero_iff hyQ hαQ).mp (by rwa [polar_comm])), ?_⟩
    rcases (S.cl_eq_cl_iff hxQ hcQ).mp (hccl.trans hxcl.symm).symm with e | e
    · left
      rw [hcτ, e]
    · right
      rw [hcτ, e, mul_assoc]
  have hxL : ∀ {x : G}, x ∈ S.QG → S.cl x ∉ Tt S g t →
      ∀ j : G, (j * S.z * j⁻¹ = x ∨ j * S.z * j⁻¹ = x * S.z) → (τ : G) ∉ S.La j := by
    intro x hxQ hxT j hj hτj
    have hjQ : j * S.z * j⁻¹ ∈ S.QG := by
      rcases hj with h | h <;> rw [h]
      · exact hxQ
      · exact S.QG.mul_mem hxQ S.z_mem_QG
    have hjcl : S.cl (j * S.z * j⁻¹) = S.cl x := by
      rcases hj with h | h <;> rw [h]
      exact S.cl_mul_z hxQ
    have hjz : j * S.z * j⁻¹ ≠ S.z := fun h => hxT (by
      rw [← hjcl, h, S.cl_z]
      exact zero_mem _)
    exact hxT (hjcl ▸ hVT (K.cl_mem_Vt_of_mem_La hy hjQ hjz hτj))
  have hxα : ∀ {x : G}, S.cl x ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →
      S.cl x ∉ Tt S g t → S.cl x ∉ (ZMod 2) ∙ S.cl α := by
    intro x hxU hxT hxs
    rcases mem_span_cl_iff.mp hxs with h | h
    · exact hxT (h ▸ zero_mem _)
    · exact hxT (h ▸ hαT (h ▸ hxU))
  obtain ⟨w₀, hw₀α, hw₀T⟩ := K.exists_sub_not_mem_Tt hy hα0
  obtain ⟨y₀, hy₀Q, rfl⟩ := S.exists_cl w₀
  obtain ⟨hxQ, hxcl, hx2, -⟩ := K.commutator_facts hy hy₀Q
  set x := y₀ * τ * y₀⁻¹ * (τ : G)⁻¹ with hx
  have hxT : S.cl x ∉ Tt S g t := by rw [hxcl]; exact hw₀T
  have hxU : S.cl x ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [hxcl]
    exact sub_mem_commSpace _ _
  obtain ⟨hy₀α, hy₀τ⟩ := hconj hy₀Q hw₀α hxQ hxcl
  obtain ⟨j₁, hj₁, hαj₁⟩ := exists_conj_mul_of_conj S τ.2 K.conj_eq hτQ hα hα1 hαz hxQ hx2
    (hxα hxU hxT) (hxL hxQ hxT) hy₀α hy₀τ
  have hx0 : S.cl x ≠ 0 := fun h => hxT (h ▸ zero_mem _)
  have hx1 : x ≠ 1 := fun h => hx0 (by rw [h, S.cl_one])
  obtain ⟨k, hkE, hkV, hxk⟩ : ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u ∧
      S.cl (k * S.z * k⁻¹) ∈ Vt S g t ∧ S.cl x ∉ S.clSub (S.QG ⊓ S.Qa k) := by
    by_contra h
    push Not at h
    exact hxT (K.mem_Tt_of_forall hy hxU fun k hk hkV => h k hk hkV)
  obtain ⟨hkz, -⟩ := K.base_of_mem hkE
  have hτQ' : u * S.z * u⁻¹ ∉ S.QG := K.conj_eq ▸ hτQ
  have hne : u * S.z * u⁻¹ ≠ S.z := fun h => hτQ' (by rw [h]; exact S.z_mem_QG)
  have hαb : α * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * α := S.QG_inf_Qa_comm hne hα hkE
  have hαk : α ∈ S.Qa k := hy.mem_Qa_of_commute hkE.1 hkz hτQ' hkE.2 hα hαb
  have hxk' : x ∉ S.Qa k := fun h => hxk (S.cl_mem_clSub ⟨hxQ, h⟩ hxQ)
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hαx : α * x = x * α := by
    have h1 : α * x * (α * x) = 1 := by rw [← hj₁]; exact conj_z_mul_self S j₁
    rw [show x * α = (α * x)⁻¹ by rw [mul_inv_rev, hαi, hxi], inv_eq_of_mul_eq_one_right h1]
  have hbU : S.cl (k * S.z * k⁻¹) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Tt_le_commSpace (hVT hkV)
  have hbx : x * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * x :=
    (S.polar_cl_eq_zero_iff hxQ hkE.1).mp (K.polar_eq_zero hxU hbU)
  have hτ'Q : α * x ∉ S.Qa k := fun h => hxk' (by
    have := mul_mem (inv_mem hαk) h
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hb2 : k * S.z * k⁻¹ * (k * S.z * k⁻¹) = 1 := conj_z_mul_self S k
  have hxbQ : x * (k * S.z * k⁻¹) ∈ S.QG := S.QG.mul_mem hxQ hkE.1
  have hxb2 : x * (k * S.z * k⁻¹) * (x * (k * S.z * k⁻¹)) = 1 := by
    calc x * (k * S.z * k⁻¹) * (x * (k * S.z * k⁻¹)) =
          x * (k * S.z * k⁻¹ * x) * (k * S.z * k⁻¹) := by group
      _ = x * x * ((k * S.z * k⁻¹) * (k * S.z * k⁻¹)) := by rw [← hbx]; group
      _ = 1 := by rw [hx2, hb2, one_mul]
  have hxbcl : S.cl (x * (k * S.z * k⁻¹)) = S.cl x + S.cl (k * S.z * k⁻¹) :=
    S.cl_mul hxQ hkE.1
  have hxbT : S.cl (x * (k * S.z * k⁻¹)) ∉ Tt S g t := by
    rw [hxbcl]
    intro h
    apply hxT
    have := sub_mem h (hVT hkV)
    rwa [add_sub_cancel_right] at this
  have hxbU : S.cl (x * (k * S.z * k⁻¹)) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [hxbcl]
    exact add_mem hxU hbU
  obtain ⟨wb, hwbα, hwb⟩ := hVα _ hkV
  obtain ⟨yb, hybQ, rfl⟩ := S.exists_cl wb
  have hy' : polar S.q (S.cl α) (S.cl (y₀ * yb)) = 0 := by
    rw [S.cl_mul hy₀Q hybQ, polar_add_right, hw₀α, hwbα, add_zero]
  have hxb' : S.cl (x * (k * S.z * k⁻¹)) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (y₀ * yb)) - S.cl (y₀ * yb) := by
    rw [hxbcl, hxcl, ← hwb, S.cl_mul hy₀Q hybQ, map_add]
    abel
  obtain ⟨hy'α, hy'τ⟩ := hconj (S.QG.mul_mem hy₀Q hybQ) hy' hxbQ hxb'
  obtain ⟨j₂, hj₂, hαj₂⟩ := exists_conj_mul_of_conj S τ.2 K.conj_eq hτQ hα hα1 hαz hxbQ hxb2
    (hxα hxbU hxbT) (hxL hxbQ hxbT) hy'α hy'τ
  have hxb1 : x * (k * S.z * k⁻¹) ≠ 1 := fun h => hxbT (by rw [h, S.cl_one]; exact zero_mem _)
  set Tb := S.conjBy k with hTb
  have hτ'M : α * x ∈ Tb.M := by
    rw [Tb.mem_M_iff]
    change α * x * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * (α * x)
    rw [mul_assoc, hbx, ← mul_assoc, hαb, mul_assoc]
  have hτ'u : α * x = (j₁ * k⁻¹) * Tb.z * (j₁ * k⁻¹)⁻¹ := by
    change α * x = (j₁ * k⁻¹) * (k * S.z * k⁻¹) * (j₁ * k⁻¹)⁻¹
    rw [← hj₁]
    group
  have hαTb : α ∈ Tb.QG ⊓ Tb.Qa (j₁ * k⁻¹) :=
    ⟨hαk, by rw [hTb, S.Qa_conjBy, inv_mul_cancel_right]; exact hαj₁⟩
  by_cases hU : Tb.cl α ∈ Tb.commQt (α * x)
  · obtain ⟨y₁, -, -, hy₁⟩ := exists_conj_of_mem_commQt Tb hτ'M hτ'u hτ'Q hαTb hU
    rcases hy₁ with h | h
    · obtain ⟨j, hj⟩ := exists_conj_of_conj_mul' S hj₁.symm hαj₁ hα1
        (fun e => hx1 (by
          calc x = α⁻¹ * (α * x) := by group
            _ = 1 := by rw [← e, inv_mul_cancel]))
        (k := y₁ * j₁) (by rw [show y₁ * j₁ * S.z * (y₁ * j₁)⁻¹ = y₁ * (j₁ * S.z * j₁⁻¹) * y₁⁻¹
          by group, hj₁, h])
      exact hαz j hj
    · obtain ⟨j, hj⟩ := exists_conj_of_conj_mul' S hj₂.symm hαj₂ hα1
        (fun e => hxb1 (by
          calc x * (k * S.z * k⁻¹) = α⁻¹ * (α * (x * (k * S.z * k⁻¹))) := by group
            _ = 1 := by rw [← e, inv_mul_cancel]))
        (k := y₁ * j₁) (by
          rw [show y₁ * j₁ * S.z * (y₁ * j₁)⁻¹ = y₁ * (j₁ * S.z * j₁⁻¹) * y₁⁻¹ by group, hj₁, h]
          change α * x * α * (k * S.z * k⁻¹) = α * (x * (k * S.z * k⁻¹)) * α
          rw [mul_assoc (α * x) α, hαb]
          group)
      exact hαz j hj
  · obtain ⟨h, -, hhτ, hhα⟩ := exists_conj_of_not_mem_commQt Tb hτ'M hτ'u hτ'Q hαTb hU
    have h1 : α * (k * S.z * k⁻¹) ∈ S.Qa (h * j₁) := by
      have := conj_mem_Qa_mul S (h := h) hαj₁
      rwa [hhα] at this
    have h2 : S.Qa (h * j₁) = S.Qa j₂ := by
      apply S.Qa_eq_of_conj_eq
      rw [show h * j₁ * S.z * (h * j₁)⁻¹ = h * (j₁ * S.z * j₁⁻¹) * h⁻¹ by group, hj₁, hhτ, hj₂]
      change α * x * (k * S.z * k⁻¹) = α * (x * (k * S.z * k⁻¹))
      group
    have hbj₂ : k * S.z * k⁻¹ ∈ S.Qa j₂ := by
      rw [h2] at h1
      have := mul_mem (inv_mem hαj₂) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have hne' : k * S.z * k⁻¹ ≠ j₂ * S.z * j₂⁻¹ := by
      rw [hj₂]
      intro e
      have : α * x = 1 := by
        calc α * x = α * (x * (k * S.z * k⁻¹)) * (k * S.z * k⁻¹)⁻¹ := by group
          _ = 1 := by rw [← e, mul_inv_cancel]
      exact conj_z_ne_one S j₁ (hj₁.trans this)
    have h3 := S.mem_Qa_symm hne' hbj₂
    rw [hj₂] at h3
    apply hτ'Q
    have := mul_mem h3 (inv_mem (S.conj_z_mem_Qa k))
    rwa [show α * (x * (k * S.z * k⁻¹)) * (k * S.z * k⁻¹)⁻¹ = α * x by group] at this

theorem Conf.exists_conj (hy : Hyp S g) (K : Conf S g t τ u) {e : G}
    (he : e ∈ S.QG ⊓ S.Qa u) (he1 : e ≠ 1) : ∃ j : G, j * S.z * j⁻¹ = e := by
  have h1 : S.cl e ∈ Vt S g t := by
    rw [← K.timmesfeld_11_3 hy]
    exact S.cl_mem_clSub he he.1
  exact exists_conj_eq_of_mem_V hy.hyp4 K.lin (S.mem_clPre.mpr ⟨he.1, h1⟩) he1

theorem Conf.QG_inf_Qa_le_V (hy : Hyp S g) (K : Conf S g t τ u) :
    S.QG ⊓ S.Qa u ≤ V S g t := fun e he =>
  S.mem_clPre.mpr ⟨he.1, by rw [← K.timmesfeld_11_3 hy]; exact S.cl_mem_clSub he he.1⟩

theorem Conf.card_QG_inf_Qa (hy : Hyp S g) (K : Conf S g t τ u) :
    Nat.card (S.QG ⊓ S.Qa u : Subgroup G) = 2 ^ finrank (ZMod 2) (Vt S g t) := by
  rw [card_eq_card_clSub inf_le_left fun h => K.z_not_mem h.2, K.timmesfeld_11_3 hy,
    S.card_submodule]

end CFSG.LargeExtraspecial.S11
