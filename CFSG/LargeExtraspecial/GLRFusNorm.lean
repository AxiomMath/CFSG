module

public import CFSG.LargeExtraspecial.GLRLinInv
public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

structure Data (S : Setting G) (X : Subgroup S.O) (A B : Submodule (ZMod 2) S.Qt) (g : G) :
    Prop where
  pair : Pair S X A B
  four_le : 4 ≤ S.width
  le_Mbar : X ≤ S.Mbar
  relIndex_eq : X.relIndex S.Mbar = 2
  map_A : ∀ σ ∈ S.Mbar, σ ∉ X →
    A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B
  conj_mem : g * S.z * g⁻¹ ∈ S.QG
  conj_ne : g * S.z * g⁻¹ ≠ S.z
  cl_mem : S.cl (g * S.z * g⁻¹) ∈ A
  card_Lbar : Nat.card (S.Lbar g) = 2 ^ (S.width - 1)
  fusion : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG →
    S.cl (k * S.z * k⁻¹) ∈ A ∨ S.cl (k * S.z * k⁻¹) ∈ B

namespace Data

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {g : G}

theorem exists_outer (hD : Data S X A B g) : ∃ σ ∈ S.Mbar, σ ∉ X := by
  by_contra hc
  push Not at hc
  have h1 : X.relIndex S.Mbar = 1 := Subgroup.relIndex_eq_one.mpr hc
  have := hD.relIndex_eq
  omega

theorem cl_ne_zero (hD : Data S X A B g) : S.cl (g * S.z * g⁻¹) ≠ 0 :=
  S.s12_cl_ne_zero_of_conj hD.conj_mem hD.conj_ne

theorem conj_mul (m : S.M) {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG) :
    ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ∈ S.QG ∧
      S.cl (((m : G) * k) * S.z * ((m : G) * k)⁻¹) =
        ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) := by
  rw [S.s12_mul_conj_z, S.ρ_cl m hk]
  exact ⟨S.conj_mem_QG m.2 hk, rfl⟩

theorem conj_A (hD : Data S X A B g) {v : S.Qt} (hv : v ∈ A) (hv0 : v ≠ 0) :
    ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ∧ S.cl (k * S.z * k⁻¹) = v := by
  obtain ⟨x, hx, hxa⟩ := hD.pair.exists_apply_eq_of_ne_zero hD.cl_mem hv hD.cl_ne_zero hv0
  obtain ⟨m, rfl⟩ := hD.le_Mbar hx
  obtain ⟨h1, h2⟩ := conj_mul m hD.conj_mem
  exact ⟨(m : G) * g, h1, h2.trans hxa⟩

theorem conj_B (hD : Data S X A B g) {v : S.Qt} (hv : v ∈ B) (hv0 : v ≠ 0) :
    ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ∧ S.cl (k * S.z * k⁻¹) = v := by
  obtain ⟨σ, hσ, hσX⟩ := hD.exists_outer
  have hv' : v ∈ A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    rw [hD.map_A σ hσ hσX]; exact hv
  obtain ⟨u, hu, rfl⟩ := hv'
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hv0 (map_zero _)
  obtain ⟨k, hk, hku⟩ := hD.conj_A hu hu0
  obtain ⟨m, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := conj_mul m hk
  exact ⟨(m : G) * k, h1, by rw [h2, hku]; rfl⟩

theorem not_le_A_B (hD : Data S X A B g) : ¬ A ≤ B := by
  intro hle
  have h1 : A ⊓ B = A := inf_eq_left.mpr hle
  rw [hD.pair.inf_eq] at h1
  have h2 := hD.pair.finrank_A
  rw [← h1, finrank_bot] at h2
  have := hD.four_le
  omega

theorem not_le_B_A (hD : Data S X A B g) : ¬ B ≤ A := by
  intro hle
  have h1 : A ⊓ B = B := inf_eq_right.mpr hle
  rw [hD.pair.inf_eq] at h1
  have h2 := hD.pair.finrank_B
  rw [← h1, finrank_bot] at h2
  have := hD.four_le
  omega

theorem conj_mem_clPre (hD : Data S X A B g) {m : S.M} (hm : S.ρ m ∈ X) {x : G}
    (hx : x ∈ S.clPre A) : (m : G) * x * (m : G)⁻¹ ∈ S.clPre A := by
  refine ⟨S.conj_mem_QG m.2 hx.1, ?_⟩
  rw [← S.ρ_cl m hx.1]
  exact hD.pair.apply_A _ hm _ hx.2

theorem centralizer_eq (hD : Data S X A B g) :
    centralizer (S.clPre A : Set G) = S.clPre A := by
  refine le_antisymm (fun y hy => ?_) (fun x hx => ?_)
  · have hyM : y ∈ S.M := by
      rw [S.mem_M_iff]
      exact ((mem_centralizer_iff.mp hy) S.z (S.z_mem_clPre A)).symm
    have hfix : ∀ v ∈ A, ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      intro v hv
      obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
      rw [S.ρ_cl ⟨y, hyM⟩ hxQ]
      congr 1
      change y * x * y⁻¹ = x
      rw [← (mem_centralizer_iff.mp hy) x ⟨hxQ, hv⟩]
      group
    have hX : S.ρ ⟨y, hyM⟩ ∈ X := by
      by_contra hX
      apply hD.not_le_A_B
      rw [← hD.map_A _ ⟨_, rfl⟩ hX]
      intro v hv
      exact ⟨v, hv, hfix v hv⟩
    have h1 : S.ρ ⟨y, hyM⟩ = 1 := hD.pair.ext_of_eqOn hX X.one_mem fun v hv => (hfix v hv)
    have hyQ : y ∈ S.QG := (S.ρ_eq_one_iff ⟨y, hyM⟩).mp h1
    have hyC : y ∈ S.QG ⊓ centralizer (S.clPre A : Set G) := ⟨hyQ, hy⟩
    rw [S.centralizer_inf_QG_eq_clPre (S.clPre_le_QG A), S.clSub_clPre] at hyC
    refine ⟨hyQ, hD.pair.mem_A_of_polar fun a ha => ?_⟩
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hyC.2) a ha
  · rw [mem_centralizer_iff]
    intro y hy
    exact (S.polar_cl_eq_zero_iff hy.1 hx.1).mp (hD.pair.polar_A hy.2 hx.2)

theorem normalizer_inf_M (hD : Data S X A B g) :
    normalizer (S.clPre A : Set G) ⊓ S.M = (X.comap S.ρ).map S.M.subtype := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨hyN, hyM⟩ := hy
    refine ⟨⟨y, hyM⟩, ?_, rfl⟩
    change S.ρ ⟨y, hyM⟩ ∈ X
    by_contra hX
    apply hD.not_le_B_A
    rw [← hD.map_A _ ⟨_, rfl⟩ hX]
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
    show ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) ∈ A
    rw [S.ρ_cl ⟨y, hyM⟩ hxQ]
    exact ((mem_normalizer_iff.mp hyN x).mp ⟨hxQ, hv⟩).2
  · rintro _ ⟨m, hm, rfl⟩
    refine ⟨mem_normalizer_iff.mpr fun x => ⟨fun hx => hD.conj_mem_clPre hm hx, fun hx => ?_⟩,
      m.2⟩
    have := hD.conj_mem_clPre (m := m⁻¹) (by rw [map_inv]; exact X.inv_mem hm) hx
    simpa [mul_assoc] using this

end Data

end CFSG.LargeExtraspecial.GLR
