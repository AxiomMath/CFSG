module

public import CFSG.LargeExtraspecial.S3bEleven
public import CFSG.LargeExtraspecial.DW2AAlpha

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Alpha

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}
  (hA : Hyp S W) {h : G} (hx : IsDx S W h)
include hA hx

theorem eq_of_mem_clPre_Qa {c : G} (hcA : c ∈ S.clPre W) (hcQ : c ∈ S.Qa h) :
    c = 1 ∨ c = S.z := by
  obtain ⟨u, -, huz, hux⟩ := S.exists_swap rfl hx.1 hx.ne_z
  have hM := M_le_normalizer_clPre hA.inv
  have hu2 : u * u ∈ S.M := by
    have e : (u * u) * S.z * (u * u)⁻¹ = S.z := by
      calc (u * u) * S.z * (u * u)⁻¹ = u * (u * S.z * u⁻¹) * u⁻¹ := by group
        _ = S.z := by rw [huz, hux]
    rw [S.mem_M_iff]
    calc (u * u) * S.z = (u * u) * S.z * (u * u)⁻¹ * (u * u) := by group
      _ = S.z * (u * u) := by rw [e]
  have hQa : S.Qa h = S.Qa u := S.Qa_eq_of_conj_eq huz.symm
  have hconj : conjSub (S.clPre W) h = conjSub (S.clPre W) u :=
    conjSub_eq_of_conj_eq hM huz.symm
  have h1 : u⁻¹ * c * u ∈ S.QG := by
    rw [hQa, Setting.Qa_eq_map] at hcQ
    obtain ⟨q, hq, hqe⟩ := hcQ
    have e : u⁻¹ * c * u = q := by
      rw [← hqe]
      simp [mul_assoc]
    rw [e]
    exact hq
  have h2 : u⁻¹ * c * u ∈ conjSub (S.clPre W) h := by
    rw [hconj, mem_conjSub]
    have e : u⁻¹ * (u⁻¹ * c * u) * u = (u * u)⁻¹ * c * ((u * u)⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [e]
    exact (mem_normalizer_iff.mp (hM (S.M.inv_mem hu2)) c).mp hcA
  rcases eq_of_mem_conjSub_QG hA.inv hx.1 hx.2 h2 h1 with e | e
  · left
    calc c = u * (u⁻¹ * c * u) * u⁻¹ := by group
      _ = 1 := by rw [e]; group
  · right
    calc c = u * (u⁻¹ * c * u) * u⁻¹ := by group
      _ = S.z := by rw [e, hux]

theorem Lbar_fix {s : S.O} (hs : s ∈ S.Lbar h) {w : S.Qt} (hw : w ∈ W) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
  obtain ⟨a, haQ, rfl⟩ := S.exists_cl w
  have haA : a ∈ S.clPre W := ⟨haQ, hw⟩
  rw [S.ρ_cl y haQ]
  set c := (y : G) * a * (y : G)⁻¹ * a⁻¹ with hc
  have hcA : c ∈ S.clPre W :=
    mul_mem ((mem_normalizer_iff.mp (M_le_normalizer_clPre hA.inv y.2) a).mp haA) (inv_mem haA)
  have hax : a * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * a :=
    (S.polar_cl_eq_zero_iff haQ hx.1).mp (mem_perp.mp (hA.cl_mem_perp hx.1) _ hw)
  have hcQ : c ∈ S.Qa h := by
    have haM : a ∈ (S.conjBy h).M := by
      rw [(S.conjBy h).mem_M_iff, Setting.conjBy_z]
      exact hax
    have h1 : a * (y : G)⁻¹ * a⁻¹ ∈ S.Qa h := (S.conjBy h).conj_mem_QG haM ((S.Qa h).inv_mem hy.1)
    have e : c = (y : G) * (a * (y : G)⁻¹ * a⁻¹) := by rw [hc]; group
    rw [e]
    exact (S.Qa h).mul_mem hy.1 h1
  rcases eq_of_mem_clPre_Qa hA hx hcA hcQ with e | e
  · have : (y : G) * a * (y : G)⁻¹ = a := by
      calc (y : G) * a * (y : G)⁻¹ = c * a := by rw [hc]; group
        _ = a := by rw [e, one_mul]
    rw [this]
  · have : (y : G) * a * (y : G)⁻¹ = S.z * a := by
      calc (y : G) * a * (y : G)⁻¹ = c * a := by rw [hc]; group
        _ = S.z * a := by rw [e]
    rw [this, S.cl_mul S.z_mem_QG haQ, S.cl_z, zero_add]

omit hA in
theorem Lbar_fix_x {s : S.O} (hs : s ∈ S.Lbar h) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹) :=
  S.mem_fixLbar.mp (S.cl_mem_fixLbar_self hx.1) s hs

theorem Lbar_faith {s : S.O} (hs : s ∈ S.Lbar h)
    (h1 : ∀ v ∈ perp S W, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ W) : s = 1 := by
  have hy : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Ybar S := ⟨s, S.Lbar_le_Mbar h hs, rfl⟩
  exact Subtype.ext (eq_one_of_trivial_perp hA.inv hy (fun w hw => Lbar_fix hA hx hs hw) h1)

variable (S W h) in
@[expose] noncomputable def Rx : Submodule (ZMod 2) S.Qt :=
  (S.clSub (S.QG ⊓ S.Qa h) ⊓ perp S W) ⊔ W

omit hA hx in
theorem Rx_le_perp (hWW : W ≤ perp S W) : Rx S W h ≤ perp S W :=
  sup_le inf_le_right hWW

theorem Lbar_sub_mem_Rx {s : S.O} (hs : s ∈ S.Lbar h) {v : S.Qt} (hv : v ∈ perp S W)
    (hvx : polar S.q v (S.cl (h * S.z * h⁻¹)) = 0) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Rx S W h := by
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hcx : c * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * c :=
    (S.polar_cl_eq_zero_iff hcQ hx.1).mp hvx
  refine Submodule.mem_sup_left ⟨S.sub_mem_clSub_of_mem_Lbar hx.1 hx.ne_z hs hcQ hcx, ?_⟩
  exact sub_mem_perp_of_fix (fun _ hw => Lbar_fix hA hx hs hw) _

theorem Lbar_sub_mem_Rx_sup {s : S.O} (hs : s ∈ S.Lbar h) {r : S.Qt} (hr : r ∈ Rx S W h) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) r - r ∈ (ZMod 2 ∙ S.cl (h * S.z * h⁻¹)) ⊔ W := by
  obtain ⟨r₁, hr₁, w, hw, rfl⟩ := Submodule.mem_sup.mp hr
  have e : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (r₁ + w) - (r₁ + w) =
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) r₁ - r₁ := by
    rw [map_add, Lbar_fix hA hx hs hw]
    abel
  rw [e]
  exact Submodule.mem_sup_left (S.sub_mem_span_of_mem_clSub hs hr₁.1)

theorem mem_sup_of_Lbar_fix {r : S.Qt} (hr : r ∈ Rx S W h)
    (hfix : ∀ s ∈ S.Lbar h, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) r - r ∈ W) :
    r ∈ (ZMod 2 ∙ S.cl (h * S.z * h⁻¹)) ⊔ W := by
  obtain ⟨r₁, hr₁, w, hw, rfl⟩ := Submodule.mem_sup.mp hr
  refine add_mem ?_ (Submodule.mem_sup_right hw)
  obtain ⟨c, hcX, hcQ, rfl⟩ := S.mem_clSub_iff.mp hr₁.1
  have hfix' : ∀ y ∈ S.L0 h, S.cl (y * c * y⁻¹) = S.cl c := by
    intro y hy
    have hs := S.ρ_mem_Lbar hy
    have h1 := hfix _ hs
    have e : ((S.ρ ⟨y, S.L0_le_M h hy⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c + w) -
        (S.cl c + w) = ((S.ρ ⟨y, S.L0_le_M h hy⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) -
          S.cl c := by
      rw [map_add, Lbar_fix hA hx hs hw]
      abel
    rw [e] at h1
    have h2 := S.sub_mem_span_of_mem_clSub hs hr₁.1
    rw [S.ρ_cl _ hcQ] at h1 h2
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h2
    rcases zmod2_cases μ with rfl | rfl
    · rw [zero_smul, eq_comm, sub_eq_zero] at hμ
      exact hμ
    · rw [← hμ, one_smul] at h1
      exact absurd h1 hx.2
  rcases S.mem_of_cl_fixed_by_L0 hx.1 hx.ne_z hcX hfix' with e | e | e | e
  · rw [e, (S.cl_eq_zero_iff S.QG.one_mem).mpr (Or.inl rfl)]
    exact zero_mem _
  · rw [e]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  · rw [e, S.cl_z]
    exact zero_mem _
  · rw [e, S.cl_mul S.z_mem_QG hx.1, S.cl_z, zero_add]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)

end Alpha

end CFSG.LargeExtraspecial.DW
