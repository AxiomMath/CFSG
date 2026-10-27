module

public import CFSG.LargeExtraspecial.DW4Data

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W4

open Subgroup Module QuadraticMap
open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X] {T : Setting X}

theorem mem_normalizer_of_conj_mem {U : Subgroup X} {g : X} (h : ∀ u ∈ U, g * u * g⁻¹ ∈ U) :
    g ∈ normalizer (U : Set X) := by
  refine mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  let f : U → U := fun u => ⟨g * u * g⁻¹, h u u.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [f] using this)
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hf ⟨_, hx⟩
  have : (u : X) = x := by
    have := congrArg Subtype.val hu
    simpa [f] using this
  exact this ▸ u.2

theorem IsZCompl.map_conj {W : Submodule (ZMod 2) T.Qt}
    (hW : ∀ m : T.M, ∀ w ∈ W, ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W) {U : Subgroup X}
    (hU : IsZCompl U (T.clPre W) T.z) {m : X} (hm : m ∈ T.M) :
    IsZCompl (U.map (MulAut.conj m).toMonoidHom) (T.clPre W) T.z := by
  have hconj : ∀ {g : X}, g ∈ T.M → ∀ {x : X}, x ∈ T.clPre W → g * x * g⁻¹ ∈ T.clPre W :=
    fun hg _ hx => ⟨T.conj_mem_QG hg hx.1, by rw [← T.ρ_cl ⟨_, hg⟩ hx.1]; exact hW _ _ hx.2⟩
  have hmz : m * T.z * m⁻¹ = T.z := by rw [T.z_comm hm, mul_inv_cancel_right]
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hconj hm (hU.le hu)
  · rintro ⟨u, hu, hzu⟩
    apply hU.not_mem
    have : u = T.z := by
      have h1 : m * u * m⁻¹ = m * T.z * m⁻¹ := by rw [hmz]; exact hzu
      simpa using h1
    exact this ▸ hu
  · rcases hU.cover _ (hconj (inv_mem hm) hx) with h | h
    · left
      refine ⟨_, h, ?_⟩
      change m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x
      group
    · right
      refine ⟨_, h, ?_⟩
      change m * (m⁻¹ * x * m⁻¹⁻¹ * T.z) * m⁻¹ = x * T.z
      calc m * (m⁻¹ * x * m⁻¹⁻¹ * T.z) * m⁻¹ = x * (m * T.z * m⁻¹) := by group
        _ = x * T.z := by rw [hmz]

namespace Hyp

variable {W₁ W₂ : Submodule (ZMod 2) T.Qt} (H : Hyp T W₁ W₂)
include H

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

end CFSG.LargeExtraspecial.DW.W4
