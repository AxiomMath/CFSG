module

public import CFSG.LargeExtraspecial.DW4Levi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W3

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.DW.W4
open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X] (T : Setting X)

structure Hyp (W₁ W₂ : Submodule (ZMod 2) T.Qt) : Prop where
  compl : IsCompl W₁ W₂
  inv₁ : ∀ m : T.M, ∀ w ∈ W₁, ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₁
  inv₂ : ∀ m : T.M, ∀ w ∈ W₂, ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₂
  ts₁ : ∀ w ∈ W₁, T.q w = 0
  ts₂ : ∀ w ∈ W₂, T.q w = 0
  width : T.width = 3

variable {T}

namespace Hyp

variable {W₁ W₂ : Submodule (ZMod 2) T.Qt}

theorem symm (H : Hyp T W₁ W₂) : Hyp T W₂ W₁ :=
  ⟨H.compl.symm, H.inv₂, H.inv₁, H.ts₂, H.ts₁, H.width⟩

variable (H : Hyp T W₁ W₂)
include H

theorem polar_eq_zero {u v : T.Qt} (hu : u ∈ W₁) (hv : v ∈ W₁) : polar T.q u v = 0 :=
  polar_eq_zero_of_ts H.ts₁ hu hv

theorem exists_add_eq (y : T.Qt) : ∃ a ∈ W₁, ∃ b ∈ W₂, a + b = y :=
  Submodule.mem_sup.mp (H.compl.sup_eq_top ▸ Submodule.mem_top : y ∈ W₁ ⊔ W₂)

theorem eq_zero_of_polar {v : T.Qt} (hv : v ∈ W₂) (h : ∀ u ∈ W₁, polar T.q v u = 0) : v = 0 := by
  refine T.q_nondegenerate.1 v fun y => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := H.exists_add_eq y
  rw [polarBilin_apply_apply, polar_add_right, h a ha, H.symm.polar_eq_zero hv hb, add_zero]

theorem finrank₁ : finrank (ZMod 2) W₁ = 3 := by
  have h1 := finrank_le_width_of_ts H.ts₁
  have h2 := finrank_le_width_of_ts H.ts₂
  have h3 := Submodule.finrank_add_eq_of_isCompl H.compl
  rw [T.finrank_Qt_eq_two_mul_width, H.width] at h3
  rw [H.width] at h1 h2
  omega

theorem card₁ : Nat.card W₁ = 2 ^ 3 := by rw [T.card_submodule, H.finrank₁]

theorem card_clPre₁ : Nat.card (T.clPre W₁) = 2 ^ 4 := by
  rw [T.card_clPre, H.card₁]
  norm_num

theorem eq_one_or_z_of_mem {x : X} (h1 : x ∈ T.clPre W₁) (h2 : x ∈ T.clPre W₂) :
    x = 1 ∨ x = T.z := by
  have h : T.cl x ∈ W₁ ⊓ W₂ := ⟨h1.2, h2.2⟩
  rw [H.compl.inf_eq_bot, Submodule.mem_bot] at h
  exact (T.cl_eq_zero_iff h1.1).mp h

theorem ρ_eq_one_of_fix {m : T.M}
    (h : ∀ u ∈ W₁, ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) u = u) : T.ρ m = 1 := by
  set e := ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) with he
  have h2 : ∀ w ∈ W₂, e w = w := by
    intro w hw
    have hd : e w - w ∈ W₂ := W₂.sub_mem (H.inv₂ m w hw) hw
    have := H.eq_zero_of_polar hd fun u hu => by
      have h3 : polar T.q (e w) u = polar T.q w u :=
        calc polar T.q (e w) u = polar T.q (e w) (e u) := by rw [h u hu]
          _ = polar T.q w u :=
            TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (T.ρ m).2 w u
      rw [polar_sub_left, h3, sub_self]
    exact sub_eq_zero.mp this
  refine Subtype.ext (LinearEquiv.ext fun y => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := H.exists_add_eq y
  change e (a + b) = a + b
  rw [map_add, h a ha, h2 b hb]

omit H in
@[expose] noncomputable def res (H : Hyp T W₁ W₂) : T.M →* (W₁ ≃ₗ[ZMod 2] W₁) :=
  S4.restrictHom (T.O.subtype.comp T.ρ) W₁ fun m u hu => H.inv₁ m u hu

theorem coe_res_apply (m : T.M) (u : W₁) :
    ((H.res m u : W₁) : T.Qt) = ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) u := rfl

theorem mem_QG_of_res_eq_one {m : T.M} (h : H.res m = 1) : (m : X) ∈ T.QG := by
  refine (T.ρ_eq_one_iff m).mp (H.ρ_eq_one_of_fix fun u hu => ?_)
  have := congrArg (fun f : W₁ ≃ₗ[ZMod 2] W₁ => ((f ⟨u, hu⟩ : W₁) : T.Qt)) h
  exact this

theorem res_eq_one_of_mem_QG {m : T.M} (h : (m : X) ∈ T.QG) : H.res m = 1 := by
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  rw [coe_res_apply, (T.ρ_eq_one_iff m).mpr h]
  rfl

theorem mem_clPre_of_commute {x : X} (hx : x ∈ T.QG)
    (h : ∀ y ∈ T.clPre W₁, x * y = y * x) : x ∈ T.clPre W₁ := by
  obtain ⟨a, ha, b, hb, hab⟩ := H.exists_add_eq (T.cl x)
  have hb0 : b = 0 := H.eq_zero_of_polar hb fun u hu => by
    obtain ⟨y, hy, rfl⟩ := T.exists_cl u
    have h1 : polar T.q (T.cl x) (T.cl y) = 0 :=
      (T.polar_cl_eq_zero_iff hx hy).mpr (h y ⟨hy, hu⟩)
    rw [← hab, polar_add_left, H.polar_eq_zero ha hu, zero_add] at h1
    exact h1
  refine ⟨hx, ?_⟩
  rw [← hab, hb0, add_zero]
  exact ha

theorem mem_clPre_of_mem_M {g : X} (hg : g ∈ T.M) (h : ∀ y ∈ T.clPre W₁, g * y = y * g) :
    g ∈ T.clPre W₁ := by
  have hρ : T.ρ ⟨g, hg⟩ = 1 := H.ρ_eq_one_of_fix fun u hu => by
    obtain ⟨y, hy, rfl⟩ := T.exists_cl u
    rw [T.ρ_cl ⟨g, hg⟩ hy]
    change T.cl (g * y * g⁻¹) = T.cl y
    rw [h y ⟨hy, hu⟩, mul_inv_cancel_right]
  exact H.mem_clPre_of_commute ((T.ρ_eq_one_iff _).mp hρ) h

theorem conj_mem_clPre {g : X} (hg : g ∈ T.M) {x : X} (hx : x ∈ T.clPre W₁) :
    g * x * g⁻¹ ∈ T.clPre W₁ :=
  ⟨T.conj_mem_QG hg hx.1, by rw [← T.ρ_cl ⟨g, hg⟩ hx.1]; exact H.inv₁ _ _ hx.2⟩

theorem fix_of_fix {e : T.Qt ≃ₗ[ZMod 2] T.Qt} (h1 : ∀ a ∈ W₁, e a ∈ W₁)
    (h2 : ∀ b ∈ W₂, e b ∈ W₂) {a b : T.Qt} (ha : a ∈ W₁) (hb : b ∈ W₂) (h : e (a + b) = a + b) :
    e a = a ∧ e b = b := by
  have hd : e a - a ∈ W₁ ⊓ W₂ := by
    refine ⟨W₁.sub_mem (h1 a ha) ha, ?_⟩
    have : e a - a = b - e b := by
      rw [map_add] at h
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]
    exact W₂.sub_mem hb (h2 b hb)
  rw [H.compl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at hd
  refine ⟨hd, ?_⟩
  rw [map_add, hd] at h
  exact add_left_cancel h

theorem exists_polar_eq (ψ : W₁ →ₗ[ZMod 2] ZMod 2) :
    ∃ v ∈ W₂, ∀ u : W₁, polar T.q v u = ψ u := by
  let Φ : W₂ →ₗ[ZMod 2] Module.Dual (ZMod 2) W₁ :=
    LinearMap.domRestrict₁₂ T.q.polarBilin W₂ W₁
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 := H.eq_zero_of_polar v.2 fun u hu => LinearMap.congr_fun hv ⟨u, hu⟩
    exact Subtype.ext h0
  have hfin : finrank (ZMod 2) W₂ = finrank (ZMod 2) (Module.Dual (ZMod 2) W₁) := by
    rw [Subspace.dual_finrank_eq, H.finrank₁, H.symm.finrank₁]
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj ψ
  exact ⟨v, v.2, fun u => LinearMap.congr_fun hv u⟩

theorem conj_eq_of_mem {x y : X} (hx : x ∈ T.clPre W₁) (hy : y ∈ T.clPre W₁) :
    x * y * x⁻¹ = y :=
  conj_eq_of_polar_eq_zero hx.1 hy.1 (H.polar_eq_zero hx.2 hy.2)

theorem exists_conj_mem {U U' : Subgroup X} (hU : IsZCompl U (T.clPre W₁) T.z)
    (hU' : IsZCompl U' (T.clPre W₁) T.z) :
    ∃ v ∈ T.clPre W₂, ∀ u ∈ U, v * u * v⁻¹ ∈ U' := by
  classical
  have hlift : ∀ w : W₁, ∃ u ∈ U, T.cl u = w := fun w => hU.exists_cl_eq w.2
  choose s hsU hscl using hlift
  let ε : X → ZMod 2 := fun u => if u ∈ U' then 0 else 1
  have hε : ∀ {x y : X}, x ∈ T.clPre W₁ → y ∈ T.clPre W₁ → ε (x * y) = ε x + ε y := by
    intro x y hx hy
    by_cases hxU : x ∈ U' <;> by_cases hyU : y ∈ U'
    · simp [ε, hxU, hyU, U'.mul_mem hxU hyU]
    · have : x * y ∉ U' := fun h => hyU (by simpa using U'.mul_mem (U'.inv_mem hxU) h)
      simp [ε, hxU, hyU, this]
    · have : x * y ∉ U' := fun h => hxU (by simpa using U'.mul_mem h (U'.inv_mem hyU))
      simp [ε, hxU, hyU, this]
    · have hx' := (hU'.cover x hx).resolve_left hxU
      have hy' := (hU'.cover y hy).resolve_left hyU
      have hxy : x * y ∈ U' := by
        have e : x * T.z * (y * T.z) = x * y :=
          calc x * T.z * (y * T.z) = x * (T.z * y) * T.z := by group
            _ = x * (y * T.z) * T.z := by rw [← T.z_comm_QG hy.1]
            _ = x * y * (T.z * T.z) := by group
            _ = x * y := by rw [T.z_mul_z, mul_one]
        rw [← e]
        exact U'.mul_mem hx' hy'
      simp only [ε, hxU, hyU, hxy, ite_true, ite_false]
      decide
  have hs_add : ∀ w w' : W₁, s (w + w') = s w * s w' := fun w w' =>
    hU.eq_of_cl_eq (hsU _) (U.mul_mem (hsU w) (hsU w')) (by
      rw [hscl, T.cl_mul (hU.mem_QG (hsU w)) (hU.mem_QG (hsU w')), hscl, hscl]
      rfl)
  let ψ₀ : W₁ →+ ZMod 2 := AddMonoidHom.mk' (fun w => ε (s w)) fun w w' => by
    rw [hs_add]
    exact hε (hU.le (hsU w)) (hU.le (hsU w'))
  obtain ⟨v, hvW, hv⟩ := H.exists_polar_eq (ψ₀.toZModLinearMap 2)
  obtain ⟨ν, hν, rfl⟩ := T.exists_cl v
  refine ⟨ν, ⟨hν, hvW⟩, fun u hu => ?_⟩
  have hsu : s ⟨T.cl u, hU.cl_mem hu⟩ = u :=
    hU.eq_of_cl_eq (hsU _) hu (hscl _)
  have hpol : polar T.q (T.cl ν) (T.cl u) = ε u := by
    have := hv ⟨T.cl u, hU.cl_mem hu⟩
    rw [this]
    change ε (s ⟨T.cl u, hU.cl_mem hu⟩) = ε u
    rw [hsu]
  by_cases huU : u ∈ U'
  · have h0 : polar T.q (T.cl ν) (T.cl u) = 0 := by rw [hpol]; simp [ε, huU]
    rw [conj_eq_of_polar_eq_zero hν (hU.mem_QG hu) h0]
    exact huU
  · have h1 : polar T.q (T.cl ν) (T.cl u) ≠ 0 := by rw [hpol]; simp [ε, huU]
    rw [conj_eq_mul_z_of_polar_ne_zero hν (hU.mem_QG hu) h1]
    exact (hU'.cover u (hU.le hu)).resolve_left huU

theorem exists_mul_mem_normalizer {U₀ U₀' : Subgroup X} (hU₀ : IsZCompl U₀ (T.clPre W₁) T.z)
    (hU₀' : IsZCompl U₀' (T.clPre W₂) T.z) {m : X} (hm : m ∈ T.M) :
    ∃ ν ∈ T.QG, ν * m ∈ normalizer (U₀ : Set X) ∧ ν * m ∈ normalizer (U₀' : Set X) := by
  obtain ⟨ν₂, hν₂, h₂⟩ := H.exists_conj_mem (hU₀.map_conj H.inv₁ hm) hU₀
  obtain ⟨ν₁, hν₁, h₁⟩ := H.symm.exists_conj_mem (hU₀'.map_conj H.inv₂ hm) hU₀'
  refine ⟨ν₁ * ν₂, T.QG.mul_mem hν₁.1 hν₂.1, mem_normalizer_of_conj_mem fun u hu => ?_,
    mem_normalizer_of_conj_mem fun w hw => ?_⟩
  · have h1 : ν₂ * (m * u * m⁻¹) * ν₂⁻¹ ∈ U₀ := h₂ _ ⟨u, hu, rfl⟩
    have e : ν₁ * ν₂ * m * u * (ν₁ * ν₂ * m)⁻¹ =
        ν₁ * (ν₂ * (m * u * m⁻¹) * ν₂⁻¹) * ν₁⁻¹ := by group
    rw [e, H.conj_eq_of_mem hν₁ (hU₀.le h1)]
    exact h1
  · have hw' : m * w * m⁻¹ ∈ T.clPre W₂ := H.symm.conj_mem_clPre hm (hU₀'.le hw)
    have h1 : ν₁ * (m * w * m⁻¹) * ν₁⁻¹ ∈ U₀' := h₁ _ ⟨w, hw, rfl⟩
    have e : ν₁ * ν₂ * m * w * (ν₁ * ν₂ * m)⁻¹ =
        ν₁ * (ν₂ * (m * w * m⁻¹) * ν₂⁻¹) * ν₁⁻¹ := by group
    rw [e, H.symm.conj_eq_of_mem hν₂ hw']
    exact h1

theorem eq_one_or_z_of_mem_normalizer {U₀ U₀' : Subgroup X}
    (hU₀ : IsZCompl U₀ (T.clPre W₁) T.z) (hU₀' : IsZCompl U₀' (T.clPre W₂) T.z) {ν : X}
    (hν : ν ∈ T.QG) (h1 : ν ∈ normalizer (U₀ : Set X)) (h2 : ν ∈ normalizer (U₀' : Set X)) :
    ν = 1 ∨ ν = T.z := by
  have key : ∀ {U : Subgroup X} {W : Submodule (ZMod 2) T.Qt}, IsZCompl U (T.clPre W) T.z →
      ν ∈ normalizer (U : Set X) → ∀ w ∈ W, polar T.q (T.cl ν) w = 0 := by
    intro U W hU hn w hw
    obtain ⟨u, hu, rfl⟩ := hU.exists_cl_eq hw
    by_contra hne
    have h4 : ν * u * ν⁻¹ ∈ U := (mem_normalizer_iff.mp hn u).mp hu
    rw [conj_eq_mul_z_of_polar_ne_zero hν (hU.mem_QG hu) hne] at h4
    exact hU.not_mem (by simpa using U.mul_mem (U.inv_mem hu) h4)
  have h0 : T.cl ν = 0 := T.q_nondegenerate.1 _ fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := H.exists_add_eq y
    rw [polarBilin_apply_apply, polar_add_right, key hU₀ h1 a ha, key hU₀' h2 b hb, add_zero]
  exact (T.cl_eq_zero_iff hν).mp h0

end Hyp

end CFSG.LargeExtraspecial.DW.W3
