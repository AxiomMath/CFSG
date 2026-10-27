module

public import CFSG.GF2Type.Smith1980Orth.S3Bad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

namespace Bad

variable {S : Setting G} {k : G}

theorem inv (h : Bad S k) : Bad S k⁻¹ := by
  refine ⟨?_, ?_, fun a ha haD => ?_⟩
  · rw [S.mem_M_iff, inv_inv]
    have hx := S.mem_M_iff.mp h.mem_M
    have hx' : S.z * (k⁻¹ * S.z * k) = (k⁻¹ * S.z * k) * S.z := by
      calc S.z * (k⁻¹ * S.z * k)
          = k⁻¹ * ((k * S.z * k⁻¹) * S.z) * k := by group
        _ = k⁻¹ * (S.z * (k * S.z * k⁻¹)) * k := by rw [hx]
        _ = (k⁻¹ * S.z * k) * S.z := by group
    exact hx'.symm
  · intro hQ
    have hzQa : S.z ∈ S.Qa k := by
      have h := (S.mem_Qa_mul_iff (g := 1) (h := k)).mpr (by
        rw [S.Qa_one]
        simpa using hQ)
      simpa using h
    exact S14.SMK.z_not_mem_Qa S h.not_mem_QG hzQa
  · have hconjQ : k * a * k⁻¹ ∈ S.QG := by
      have h := S.conj_mem_Qa_mul (g := k⁻¹) (h := k) (x := a) haD.2
      simpa [S.Qa_one] using h
    have hQa : k * a * k⁻¹ ∈ S.Qa k := by
      have h := (S.mem_Qa_mul_iff (g := 1) (h := k) (x := k * a * k⁻¹)).mpr
        (by rw [S.Qa_one]; simpa [mul_assoc] using haD.1)
      simpa using h
    exact h.not_mem (ha.trans (isConj_iff.mpr ⟨k, rfl⟩)) ⟨hconjQ, hQa⟩

end Bad

@[expose] def OKComm (S : Setting G) : Prop :=
  ∀ k : G, Bad S k → ∀ a ∈ S.Lbar k, ∀ b ∈ S.Lbar k, a * b = b * a

theorem lbar_comm_of_mul_left {S : Setting G} {m k : G} (hm : m ∈ S.M)
    (h : ∀ a ∈ S.Lbar (m * k), ∀ b ∈ S.Lbar (m * k), a * b = b * a) :
    ∀ a ∈ S.Lbar k, ∀ b ∈ S.Lbar k, a * b = b * a := by
  set r : S.O := S.ρ ⟨m, hm⟩
  have hr : ∀ x ∈ S.Lbar k, r * x * r⁻¹ ∈ S.Lbar (m * k) := by
    intro x hx
    rw [S.Lbar_mul hm]
    exact ⟨x, hx, rfl⟩
  intro a ha b hb
  have hcomm := h _ (hr a ha) _ (hr b hb)
  calc a * b = r⁻¹ * (r * a * r⁻¹ * (r * b * r⁻¹)) * r := by group
    _ = r⁻¹ * (r * b * r⁻¹ * (r * a * r⁻¹)) * r := by rw [hcomm]
    _ = b * a := by group

theorem commute_of_bad_of_oKComm {S : Setting G} (hK : OKComm S) {k : G} (hbad : Bad S k) :
    ∀ u ∈ S.QG ⊓ Subgroup.centralizer ({k * S.z * k⁻¹} : Set G),
      ∀ v ∈ S.QG ⊓ Subgroup.centralizer ({k * S.z * k⁻¹} : Set G), u * v = v * u := by
  intro u hu v hv
  have hux : u * (k * S.z * k⁻¹) = (k * S.z * k⁻¹) * u :=
    Subgroup.mem_centralizer_singleton_iff.mp hu.2
  have hvx : v * (k * S.z * k⁻¹) = (k * S.z * k⁻¹) * v :=
    Subgroup.mem_centralizer_singleton_iff.mp hv.2
  have huM : k⁻¹ * u * k ∈ S.M := by
    rw [S.mem_M_iff]
    calc (k⁻¹ * u * k) * S.z = k⁻¹ * (u * (k * S.z * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * S.z * k⁻¹) * u) * k := by rw [hux]
      _ = S.z * (k⁻¹ * u * k) := by group
  have hvM : k⁻¹ * v * k ∈ S.M := by
    rw [S.mem_M_iff]
    calc (k⁻¹ * v * k) * S.z = k⁻¹ * (v * (k * S.z * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * S.z * k⁻¹) * v) * k := by rw [hvx]
      _ = S.z * (k⁻¹ * v * k) := by group
  have huQa : k⁻¹ * u * k ∈ S.Qa k⁻¹ := by
    have h := S.conj_mem_Qa_mul (g := 1) (h := k⁻¹) (x := u) (by rw [S.Qa_one]; exact hu.1)
    simpa using h
  have hvQa : k⁻¹ * v * k ∈ S.Qa k⁻¹ := by
    have h := S.conj_mem_Qa_mul (g := 1) (h := k⁻¹) (x := v) (by rw [S.Qa_one]; exact hv.1)
    simpa using h
  have huL : S.ρ ⟨k⁻¹ * u * k, huM⟩ ∈ S.Lbar k⁻¹ :=
    S.ρ_mem_Lbar (g := k⁻¹) (y := k⁻¹ * u * k) ⟨huQa, huM⟩
  have hvL : S.ρ ⟨k⁻¹ * v * k, hvM⟩ ∈ S.Lbar k⁻¹ :=
    S.ρ_mem_Lbar (g := k⁻¹) (y := k⁻¹ * v * k) ⟨hvQa, hvM⟩
  have hcomm := hK k⁻¹ hbad.inv _ huL _ hvL
  have hcM : k⁻¹ * u * k * (k⁻¹ * v * k) * (k⁻¹ * u * k)⁻¹ * (k⁻¹ * v * k)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.mul_mem huM hvM) (S.M.inv_mem huM)) (S.M.inv_mem hvM)
  have h2 : S.ρ ⟨k⁻¹ * u * k * (k⁻¹ * v * k) * (k⁻¹ * u * k)⁻¹ * (k⁻¹ * v * k)⁻¹, hcM⟩ = 1 := by
    have hcast : (⟨k⁻¹ * u * k * (k⁻¹ * v * k) * (k⁻¹ * u * k)⁻¹ * (k⁻¹ * v * k)⁻¹, hcM⟩ : S.M) =
        ⟨k⁻¹ * u * k, huM⟩ * ⟨k⁻¹ * v * k, hvM⟩ * (⟨k⁻¹ * u * k, huM⟩ : S.M)⁻¹ *
          (⟨k⁻¹ * v * k, hvM⟩ : S.M)⁻¹ := rfl
    rw [hcast, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have h3 : k⁻¹ * u * k * (k⁻¹ * v * k) * (k⁻¹ * u * k)⁻¹ * (k⁻¹ * v * k)⁻¹ ∈ S.QG :=
    (S.ρ_eq_one_iff ⟨_, hcM⟩).mp h2
  have h3Qa : u * v * u⁻¹ * v⁻¹ ∈ S.Qa k := by
    have hkey : k * (k⁻¹ * u * k * (k⁻¹ * v * k) * (k⁻¹ * u * k)⁻¹ * (k⁻¹ * v * k)⁻¹) * k⁻¹ =
        u * v * u⁻¹ * v⁻¹ := by group
    rw [← hkey]
    have hQ1 : k⁻¹ * u * k * (k⁻¹ * v * k) * (k⁻¹ * u * k)⁻¹ * (k⁻¹ * v * k)⁻¹ ∈ S.Qa 1 := by
      rw [S.Qa_one]
      exact h3
    simpa using S.conj_mem_Qa_mul (g := 1) (h := k) hQ1
  rcases S.commutator_eq_one_or_z hu.1 hv.1 with e | e
  · calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
      _ = v * u := by rw [e, one_mul]
  · exfalso
    rw [e] at h3Qa
    exact S14.SMK.z_not_mem_Qa S hbad.not_mem_QG h3Qa

end CFSG.GF2Type.Smith1980Orth
