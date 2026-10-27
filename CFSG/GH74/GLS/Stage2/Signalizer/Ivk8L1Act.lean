module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

section Act

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}

theorem small_normal_cases (hfr : AFrame A zb Sb Vb) {N : Subgroup A} (hNS : N ≤ Sb)
    (hNn : ∀ s ∈ Sb, ∀ x ∈ N, s * x * s⁻¹ ∈ N) (hN2 : Nat.card ↥N ≤ 2) :
    ∀ x ∈ N, x = 1 ∨ x = zb := by
  intro x hx
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  have hP : IsPGroup 2 ↥Sb := hfr.sylow.isPGroup
  have hnorm : (N.subgroupOf Sb).Normal := ⟨fun y hy t => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simpa using hNn t.1 t.2 y.1 hy⟩
  have hne : N.subgroupOf Sb ≠ ⊥ := by
    intro h
    have : (⟨x, hNS hx⟩ : ↥Sb) ∈ N.subgroupOf Sb := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact hx1 (congrArg Subtype.val this)
  obtain ⟨u, hu, huc, hu2⟩ := Gen.exists_involution_center_of_normal hP hne
  have huz : ((u : ↥Sb) : A) = zb :=
    hfr.zcen _ u.2 (fun s hs => congrArg Subtype.val (Subgroup.mem_center_iff.mp huc ⟨s, hs⟩))
      (by rw [Subgroup.orderOf_coe]; exact hu2)
  have hzbN : zb ∈ N := by
    rw [← huz]
    exact Subgroup.mem_subgroupOf.mp hu
  by_contra hxz
  have hzb1 : zb ≠ 1 := fun h => by
    have h0 := hfr.zb_ord
    rw [h, orderOf_one] at h0
    exact absurd h0 (by norm_num)
  let f : Fin 3 → ↥N := ![1, ⟨zb, hzbN⟩, ⟨x, hx⟩]
  have hinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Subtype.ext_iff]
  have := Nat.card_le_card_of_injective f hinj
  simp at this
  omega

omit [Finite A] in
theorem inf_centralizer_normal {J : Subgroup A} (hsw : Sb ≤ normalizer (J : Set A)) :
    ∀ s ∈ Sb, ∀ x ∈ Sb ⊓ centralizer (J : Set A), s * x * s⁻¹ ∈ Sb ⊓ centralizer (J : Set A) := by
  intro s hs x hx
  obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨Sb.mul_mem (Sb.mul_mem hs hxS) (Sb.inv_mem hs), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hsn : ∀ g ∈ Sb, ∀ h ∈ J, g * h * g⁻¹ ∈ J := fun g hg h hh =>
    (Subgroup.mem_normalizer_iff.mp (hsw hg) h).mp hh
  have hj' : s⁻¹ * j * s ∈ J := by
    have := hsn s⁻¹ (Sb.inv_mem hs) j hj
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hxC _ hj'
  calc j * (s * x * s⁻¹) = s * ((s⁻¹ * j * s) * x) * s⁻¹ := by group
    _ = s * (x * (s⁻¹ * j * s)) * s⁻¹ := by rw [hc]
    _ = s * x * s⁻¹ * j := by group

@[expose] noncomputable def actOn (J : Subgroup A) (hsw : Sb ≤ normalizer (J : Set A)) :
    ↥Sb →* MulAut ↥J :=
  J.normalizerMonoidHom.comp (Subgroup.inclusion hsw)

omit [Finite A] in
theorem actOn_apply (J : Subgroup A) (hsw : Sb ≤ normalizer (J : Set A)) (s : ↥Sb) (x : ↥J) :
    ((actOn J hsw s x : ↥J) : A) = (s : A) * (x : A) * (s : A)⁻¹ := rfl

omit [Finite A] in
theorem mem_centralizer_of_actOn_eq_one (J : Subgroup A) (hsw : Sb ≤ normalizer (J : Set A))
    {s : ↥Sb} (h : actOn J hsw s = 1) : (s : A) ∈ centralizer (J : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 : ((actOn J hsw s ⟨j, hj⟩ : ↥J) : A) = j := by rw [h]; rfl
  rw [actOn_apply] at h1
  calc j * (s : A) = ((s : A) * j * (s : A)⁻¹) * (s : A) := by rw [h1]
    _ = (s : A) * j := by group

end Act

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
