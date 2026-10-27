module

public import CFSG.GH74.GLS.IVK.L2.Twist
public import CFSG.GH74.GLS.IVK.L2.Lemma13f

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section Twist

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem innDiagHom_twist (e : K ≃* L2 F) (α : MulAut K) (g : PGL2 F) :
    innDiagHom (twistEquiv e α) g = α⁻¹ * innDiagHom e g * α := by
  ext k
  apply α.injective
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have h1 := toPGL_toPSL_innDiagHom (twistEquiv e α) g k
  have h2 := toPGL_toPSL_innDiagHom e g (α k)
  rw [toPSL_twist, toPSL_twist] at h1
  have h3 : α ((α⁻¹ * innDiagHom e g * α) k) = innDiagHom e g (α k) := by
    simp [MulAut.mul_apply]
  rw [h3, h2]
  exact h1

omit [Finite K] in
theorem innDiagSub_twist (e : K ≃* L2 F) (α : MulAut K) :
    innDiagSub (twistEquiv e α) = innDiagSub e := by
  have hN := innDiagSub_normal e
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    rw [innDiagHom_twist]
    have := hN.conj_mem (innDiagHom e g) ⟨g, rfl⟩ α⁻¹
    simpa using this
  · intro hx
    obtain ⟨g', hg'⟩ := hN.conj_mem x hx α
    refine ⟨g', ?_⟩
    rw [innDiagHom_twist, hg']
    group

omit [Finite K] [Finite F] in
theorem fieldAutSub_twist (e : K ≃* L2 F) (α : MulAut K) :
    fieldAutSub (twistEquiv e α) = (fieldAutSub e).map (MulAut.conj α⁻¹).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨fieldAutHom e σ, ⟨σ, rfl⟩, ?_⟩
    rw [fieldAutHom_twist]
    simp
  · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    rw [fieldAutHom_twist]
    simp

omit [Finite K] [Finite F] in
theorem mem_fieldAutSub_twist_iff (e : K ≃* L2 F) (h : MulAut K) (x : MulAut K) :
    x ∈ fieldAutSub (twistEquiv e h⁻¹) ↔ h⁻¹ * x * h ∈ fieldAutSub e := by
  rw [fieldAutSub_twist]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : h⁻¹ * ((MulAut.conj h⁻¹⁻¹).toMonoidHom y) * h = y := by
      simp [MulAut.conj_apply]; group
    rw [this]; exact hy
  · intro hx
    refine ⟨h⁻¹ * x * h, hx, ?_⟩
    simp [MulAut.conj_apply]; group

theorem isFourSubgroup_of {G : Type} [Group G] {U : Subgroup G}
    (hc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hs : ∀ x ∈ U, x * x = 1) (hcard : Nat.card U = 4) :
    IsFourSubgroup U := by
  refine ⟨?_, hcard⟩
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc _ a.2 _ b.2)⟩⟩, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro a
  apply Subtype.ext
  have := hs _ a.2
  simpa [pow_two] using this

theorem isFourSubgroup_map {G : Type} [Group G] {U : Subgroup G} (h : G) (hU : IsFourSubgroup U) :
    IsFourSubgroup (U.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨hc, hs⟩ := isFourSubgroup_props hU
  refine isFourSubgroup_of ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
      _ = h * (b * a) * h⁻¹ := by rw [hc a ha b hb]
      _ = h * b * h⁻¹ * (h * a * h⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
      _ = 1 := by rw [hs a ha]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hU.2

end Twist

section Conj

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] {e : K ≃* L2 F}

theorem mem_sylow_smul {G : Type*} [Group G] {p : ℕ} (T : Sylow p G) (h x : G) :
    x ∈ (h • T : Sylow p G) ↔ h⁻¹ * x * h ∈ (T : Subgroup G) := by
  show x ∈ ((h • T : Sylow p G) : Subgroup G) ↔ _
  rw [Sylow.coe_subgroup_smul]
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : h⁻¹ * (MulAut.conj h • y) * h = y := by simp [MulAut.smul_def]; group
    rw [this]; exact hy
  · intro hx
    exact ⟨h⁻¹ * x * h, hx, by simp [MulAut.smul_def]; group⟩

omit [Finite K] in
theorem orderOf_mul_mul_inv_eq (h t : MulAut K) : orderOf (h * t * h⁻¹) = orderOf t := by
  have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective t
  simpa [MulAut.conj_apply] using this

noncomputable def L2Notation.conj (N : L2Notation e) (h : MulAut K) :
    L2Notation (twistEquiv e h⁻¹) where
  T := h • N.T
  t := h * N.t * h⁻¹
  t_mem := by
    refine (mem_sylow_smul N.T h _).mpr ?_
    have : h⁻¹ * (h * N.t * h⁻¹) * h = N.t := by group
    rw [this]; exact N.t_mem
  t_order := by rw [orderOf_mul_mul_inv_eq, N.t_order]
  t_mem_diag := by
    rw [innDiagSub_twist]
    exact (innDiagSub_normal e).conj_mem _ N.t_mem_diag h
  t_not_mem_inn := by
    intro hc
    apply N.t_not_mem_inn
    have := (innAut_normal (K := K)).conj_mem _ hc h⁻¹
    have e1 : h⁻¹ * (h * N.t * h⁻¹) * h⁻¹⁻¹ = N.t := by group
    rwa [e1] at this
  T_inv := by
    intro φ' hφ'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hφ : h⁻¹ * φ' * h ∈ fieldAutSub e := (mem_fieldAutSub_twist_iff e h φ').mp hφ'
    have hnorm := Subgroup.mem_normalizer_iff.mp (N.T_inv hφ) (h⁻¹ * x * h)
    have e1 : h⁻¹ * (φ' * x * φ'⁻¹) * h =
        (h⁻¹ * φ' * h) * (h⁻¹ * x * h) * (h⁻¹ * φ' * h)⁻¹ := by group
    refine ((mem_sylow_smul N.T h x).trans ?_).trans (mem_sylow_smul N.T h _).symm
    rw [e1]
    exact hnorm
  R_cent := by
    rintro f' ⟨hfT', hfF'⟩ hf2 x ⟨hxT', hxI⟩
    have hfT : h⁻¹ * f' * h ∈ (N.T : Subgroup (MulAut K)) := (mem_sylow_smul N.T h f').mp hfT'
    have hfF : h⁻¹ * f' * h ∈ fieldAutSub e := (mem_fieldAutSub_twist_iff e h f').mp hfF'
    have hf2' : orderOf (h⁻¹ * f' * h) = 2 := by
      have := orderOf_mul_mul_inv_eq h⁻¹ f'
      simpa [this] using (by rw [orderOf_mul_mul_inv_eq]; exact hf2 : orderOf (h⁻¹ * f' * h⁻¹⁻¹) = 2)
    have hxT : h⁻¹ * x * h ∈ (N.T : Subgroup (MulAut K)) := (mem_sylow_smul N.T h x).mp hxT'
    have hxI' : h⁻¹ * x * h ∈ innAut K := by
      have := (innAut_normal (K := K)).conj_mem _ hxI h⁻¹
      simpa using this
    have hc := N.R_cent _ ⟨hfT, hfF⟩ hf2' _ ⟨hxT, hxI'⟩
    calc x * f' = h * ((h⁻¹ * x * h) * (h⁻¹ * f' * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * f' * h) * (h⁻¹ * x * h)) * h⁻¹ := by rw [hc]
      _ = f' * x := by group
  F_odd_cent := by
    intro f' hfF' hodd x hxT'
    have hfF : h⁻¹ * f' * h ∈ fieldAutSub e := (mem_fieldAutSub_twist_iff e h f').mp hfF'
    have hodd' : Odd (orderOf (h⁻¹ * f' * h)) := by
      have := orderOf_mul_mul_inv_eq h⁻¹ f'
      simpa [this] using (by rw [orderOf_mul_mul_inv_eq]; exact hodd : Odd (orderOf (h⁻¹ * f' * h⁻¹⁻¹)))
    have hxT : h⁻¹ * x * h ∈ (N.T : Subgroup (MulAut K)) := (mem_sylow_smul N.T h x).mp hxT'
    have hc := N.F_odd_cent _ hfF hodd' _ hxT
    calc x * f' = h * ((h⁻¹ * x * h) * (h⁻¹ * f' * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * f' * h) * (h⁻¹ * x * h)) * h⁻¹ := by rw [hc]
      _ = f' * x := by group
  four_cent := by
    obtain ⟨U, hUle, hU4, hUc⟩ := N.four_cent
    refine ⟨U.map (MulAut.conj h).toMonoidHom, ?_, isFourSubgroup_map h hU4, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨huT, huI⟩ := hUle hu
      refine ⟨?_, ?_⟩
      · refine (mem_sylow_smul N.T h _).mpr ?_
        have : h⁻¹ * ((MulAut.conj h).toMonoidHom u) * h = u := by simp [MulAut.conj_apply]; group
        rw [this]; exact huT
      · have := (innAut_normal (K := K)).conj_mem u huI h
        simpa [MulAut.conj_apply] using this
    · rintro φ' hφ' _ ⟨u, hu, rfl⟩
      have hφ : h⁻¹ * φ' * h ∈ fieldAutSub e := (mem_fieldAutSub_twist_iff e h φ').mp hφ'
      have hc := hUc _ hφ u hu
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc φ' * (h * u * h⁻¹) = h * ((h⁻¹ * φ' * h) * u) * h⁻¹ := by group
        _ = h * (u * (h⁻¹ * φ' * h)) * h⁻¹ := by rw [hc]
        _ = h * u * h⁻¹ * φ' := by group

theorem exists_notation_of_exists (N : L2Notation e) (T : Sylow 2 (MulAut K)) :
    ∃ (e' : K ≃* L2 F) (N' : L2Notation e'), N'.T = T := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (MulAut K) N.T T
  exact ⟨twistEquiv e h⁻¹, N.conj h, hh⟩

end Conj

end CFSG.GH74.GLS.IVK
