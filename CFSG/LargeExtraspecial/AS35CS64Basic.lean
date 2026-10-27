module

public import CFSG.LargeExtraspecial.AS35CSmith
public import CFSG.LargeExtraspecial.DWSm77Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

section Group

variable {G : Type} [Group G]

theorem conj_comm_eq_inv {x : G} (hx2 : x * x = 1) (c : G) :
    x * (c * x * c⁻¹ * x⁻¹) * x⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [hx]
  calc x * (c * x * c⁻¹ * x) * x = x * c * x * c⁻¹ * (x * x) := by group
    _ = x * c * x * c⁻¹ := by rw [hx2, mul_one]
    _ = (c * x * c⁻¹ * x)⁻¹ := by
      rw [show (c * x * c⁻¹ * x)⁻¹ = x⁻¹ * c * x⁻¹ * c⁻¹ by group, hx]

end Group

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem weaklyClosed_conjBy (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (h : G) : ∀ g : G, g * (S.conjBy h).z * g⁻¹ ∈ (S.conjBy h).QG →
      g * (S.conjBy h).z * g⁻¹ = (S.conjBy h).z := by
  intro g hg
  rw [DW.Sm77.mem_conjBy_QG_iff, conjBy_z] at hg
  rw [conjBy_z]
  have e : h⁻¹ * g * h * S.z * (h⁻¹ * g * h)⁻¹ = h⁻¹ * (g * (h * S.z * h⁻¹) * g⁻¹) * h := by
    group
  have h1 := hW (h⁻¹ * g * h) (by rw [e]; exact hg)
  calc g * (h * S.z * h⁻¹) * g⁻¹ = h * (h⁻¹ * g * h * S.z * (h⁻¹ * g * h)⁻¹) * h⁻¹ := by group
    _ = h * S.z * h⁻¹ := by rw [h1]

omit [Finite G] in
theorem conj_mul_self (g : G) : g * S.z * g⁻¹ * (g * S.z * g⁻¹) = 1 := by
  calc g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ := by group
    _ = 1 := by rw [S.z_mul_z]; group

omit [Finite G] in
theorem comm_mem_QG {x c : G} (hxM : x ∈ S.M) (hcQ : c ∈ S.QG) :
    c * x * c⁻¹ * x⁻¹ ∈ S.QG := by
  have h := mul_mem hcQ (S.conj_mem_QG hxM (inv_mem hcQ))
  simpa [mul_assoc] using h

theorem cl_comm {x c : G} (hxM : x ∈ S.M) (hcQ : c ∈ S.QG) :
    S.cl (c * x * c⁻¹ * x⁻¹) =
      S.cl c + ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) := by
  have e : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
  rw [e, S.cl_mul hcQ (S.conj_mem_QG hxM (inv_mem hcQ)), S.ρ_cl ⟨x, hxM⟩ hcQ]
  congr 1
  change S.cl (x * c⁻¹ * x⁻¹) = S.cl (x * c * x⁻¹)
  rw [show x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ by group,
    S.cl_inv (S.conj_mem_QG hxM hcQ)]

theorem commute_of_fix {x : G} (hxM : x ∈ S.M) (hlam : ∀ e ∈ S.QG, e * x * e⁻¹ ≠ x * S.z)
    {a : G} (haQ : a ∈ S.QG)
    (hfix : ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) = S.cl a) :
    a * x = x * a := by
  rw [S.ρ_cl ⟨x, hxM⟩ haQ] at hfix
  rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG hxM haQ)).mp hfix.symm with h | h
  · change x * a * x⁻¹ = a at h
    calc a * x = x * a * x⁻¹ * x := by rw [h]
      _ = x * a := by group
  · exfalso
    change x * a * x⁻¹ = a * S.z at h
    apply hlam a⁻¹ (inv_mem haQ)
    calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹) * x := by group
      _ = a⁻¹ * (a * S.z) * x := by rw [h]
      _ = S.z * x := by group
      _ = x * S.z := (S.z_comm hxM).symm

theorem commSpace_eq_orthogonal {σ : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) (h2 : σ * σ = 1) :
    commSpace σ = LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace σ) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate hO h2,
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl]

theorem width_le_finrank_fixSpace {σ : S.Qt ≃ₗ[ZMod 2] S.Qt} (h2 : σ * σ = 1) :
    S.width ≤ finrank (ZMod 2) (fixSpace σ) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have h1 := finrank_commSpace_add_finrank_fixSpace σ
  have h3 := Submodule.finrank_mono (commSpace_le_fixSpace h2)
  rw [S.finrank_Qt_eq_two_mul_width] at h1
  omega

theorem exists_singular_of_two_le {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ u ∈ U, ∀ v ∈ U, polar S.q u v = 0) (h2 : 2 ≤ finrank (ZMod 2) U) :
    ∃ u ∈ U, u ≠ 0 ∧ S.q u = 0 := by
  obtain ⟨u₁, hu₁, hu₁0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra! h
    have hb : U = ⊥ := (Submodule.eq_bot_iff U).mpr h
    rw [hb, finrank_bot] at h2
    omega
  obtain ⟨u₂, hu₂, hu₂0, hu₂1⟩ : ∃ u ∈ U, u ≠ 0 ∧ u ≠ u₁ := by
    by_contra! h
    have hle : finrank (ZMod 2) U ≤ 1 := by
      refine finrank_le_one ⟨u₁, hu₁⟩ fun w => ?_
      by_cases hw : (w : S.Qt) = 0
      · exact ⟨0, Subtype.ext (by simp [hw])⟩
      · exact ⟨1, Subtype.ext (by simp [h w w.2 hw])⟩
    omega
  by_cases hq₁ : S.q u₁ = 0
  · exact ⟨u₁, hu₁, hu₁0, hq₁⟩
  by_cases hq₂ : S.q u₂ = 0
  · exact ⟨u₂, hu₂, hu₂0, hq₂⟩
  refine ⟨u₁ + u₂, U.add_mem hu₁ hu₂, ?_, ?_⟩
  · intro h
    apply hu₂1
    calc u₂ = u₁ + u₂ + u₁ := by
          rw [add_comm u₁ u₂, add_assoc, add_self_vec (ZMod 2), add_zero]
      _ = u₁ := by rw [h, zero_add]
  · rw [map_add_eq, hU u₁ hu₁ u₂ hu₂, add_zero]
    rcases zmod2_cases (S.q u₁) with h | h
    · exact absurd h hq₁
    rcases zmod2_cases (S.q u₂) with h' | h'
    · exact absurd h' hq₂
    rw [h, h']
    decide

theorem exists_conj_comm_eq (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g y : G} (hgy : g * S.z * g⁻¹ = y) (hyM : y ∈ S.M) (hyz : y ≠ S.z)
    (hlam : ∀ e ∈ S.QG, e * y * e⁻¹ ≠ y * S.z) {d : G} (hdQ : d ∈ S.QG) (hda : d ∈ S.Qa g) :
    ∃ e ∈ S.QG, e * y * e⁻¹ * y⁻¹ = d ∨ e * y * e⁻¹ * y⁻¹ = d * S.z := by
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  have hy2 : y ^ 2 = 1 := by rw [← hgy, pow_two]; exact S.conj_mul_self g
  have h2 : σ * σ = 1 := S.ρ_mul_self hyM hy2
  have hO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (S.ρ ⟨y, hyM⟩).2
  have hzQa : S.z ∉ S.Qa g := S.z_not_mem_Qa hW (by rw [hgy]; exact hyz)
  have hd : S.cl d ∈ commSpace σ := by
    rw [S.commSpace_eq_orthogonal hO h2, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [mem_fixSpace] at hw
    obtain ⟨a, haQ, rfl⟩ := S.exists_cl w
    have hay : a * y = y * a := S.commute_of_fix hyM hlam haQ hw
    have haM : a ∈ (S.conjBy g).M := by
      rw [(S.conjBy g).mem_M_iff, conjBy_z, hgy]
      exact hay
    have hcomm : a * d * a⁻¹ * d⁻¹ ∈ S.Qa g :=
      mul_mem ((S.conjBy g).conj_mem_QG haM hda) (inv_mem hda)
    have had : a * d = d * a := by
      rcases S.commutator_eq_one_or_z haQ hdQ with h | h
      · calc a * d = a * d * a⁻¹ * d⁻¹ * (d * a) := by group
          _ = d * a := by rw [h, one_mul]
      · exact absurd (h ▸ hcomm) hzQa
    rw [polarBilin_apply_apply]
    exact (S.polar_cl_eq_zero_iff haQ hdQ).mpr had
  obtain ⟨v, hv⟩ := mem_commSpace.mp hd
  obtain ⟨e, heQ, rfl⟩ := S.exists_cl v
  refine ⟨e, heQ, ?_⟩
  have hj : S.cl (e * y * e⁻¹ * y⁻¹) = S.cl d := by
    rw [S.cl_comm hyM heQ, ← hv, sub_eq_add_vec (ZMod 2), add_comm]
  rcases (S.cl_eq_cl_iff (S.comm_mem_QG hyM heQ) hdQ).mp hj with h | h
  · exact Or.inl h.symm
  · right
    rw [h, mul_assoc (e * y * e⁻¹ * y⁻¹) S.z S.z, S.z_mul_z, mul_one]

end Setting

end CFSG.LargeExtraspecial
