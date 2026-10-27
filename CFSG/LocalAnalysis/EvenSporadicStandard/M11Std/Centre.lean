module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Sub

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem central_mem_W {s : G} (hs : s ∈ H.S) (hc : ∀ s' ∈ H.S, s * s' = s' * s) : s ∈ H.W := by
  obtain ⟨x, rfl⟩ := (mem_S H).1 hs
  refine ⟨x, ?_, rfl⟩
  rw [← SMod.isCentral_iff]
  intro y
  apply H.psi_injective
  rw [H.psi_mul, H.psi_mul]
  exact hc _ (H.psi_mem_S y)

theorem W_central {w : G} (hw : w ∈ H.W) : ∀ s ∈ H.S, w * s = s * w := by
  obtain ⟨x, hx, rfl⟩ := hw
  intro s hs
  obtain ⟨y, rfl⟩ := (mem_S H).1 hs
  rw [← H.psi_mul, ← H.psi_mul]
  congr 1
  exact (SMod.isCentral_iff x).2 hx y

theorem not_sq_t {s : G} (hs : s ∈ H.S) : s * s ≠ H.t := by
  obtain ⟨x, rfl⟩ := (mem_S H).1 hs
  intro h
  rw [← H.psi_mul, ← H.psi_tt] at h
  have := congrArg (fun y => y.1.val) (H.psi_injective h)
  have h0 := SMod.sq_fst x
  simp only [SMod.tt] at this
  rw [h0] at this
  simp at this

theorem z_eq_sq : H.a ^ 4 = H.a ^ 2 * H.a ^ 2 := by rw [← pow_add]

theorem psi_tz : H.psi (1, 0, 4) = H.t * H.a ^ 4 := by
  simp [psi, psiN]

theorem conj_t_cases {x : G} (hx : x ∈ Subgroup.normalizer (H.S : Set G)) :
    x * H.t * x⁻¹ = H.t ∨ x * H.t * x⁻¹ = H.a ^ 4 ∨ x * H.t * x⁻¹ = H.t * H.a ^ 4 := by
  have hxn := Subgroup.mem_normalizer_iff.1 hx
  have hxS : x * H.t * x⁻¹ ∈ H.S := (hxn _).1 H.t_mem_S
  have hc : ∀ s' ∈ H.S, (x * H.t * x⁻¹) * s' = s' * (x * H.t * x⁻¹) := by
    intro s' hs'
    have h1 : x⁻¹ * s' * x ∈ H.S :=
      (hxn _).2 (by rw [show x * (x⁻¹ * s' * x) * x⁻¹ = s' by group]; exact hs')
    have h2 := H.W_central H.t_mem_W _ h1
    calc x * H.t * x⁻¹ * s' = x * (H.t * (x⁻¹ * s' * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * s' * x) * H.t) * x⁻¹ := by rw [h2]
      _ = s' * (x * H.t * x⁻¹) := by group
  obtain ⟨w, hw, hψ⟩ := H.central_mem_W hxS hc
  have hne : x * H.t * x⁻¹ ≠ 1 := by
    intro h
    apply H.t_ne
    calc H.t = x⁻¹ * (x * H.t * x⁻¹) * x := by group
      _ = x⁻¹ * 1 * x := by rw [h]
      _ = 1 := by group
  rcases SMod.inW_cases w hw with rfl | rfl | rfl | rfl
  · exact absurd (hψ.symm.trans H.psi_one) hne
  · exact Or.inl (hψ.symm.trans H.psi_tt)
  · exact Or.inr (Or.inl (hψ.symm.trans H.psi_zz))
  · exact Or.inr (Or.inr (hψ.symm.trans H.psi_tz))

theorem conj_t_ne_z {x : G} (hx : x ∈ Subgroup.normalizer (H.S : Set G)) :
    x * H.t * x⁻¹ ≠ H.a ^ 4 := by
  intro h
  have hxn := Subgroup.mem_normalizer_iff.1 hx
  have hs : x⁻¹ * H.a ^ 2 * x ∈ H.S := by
    refine (hxn _).2 ?_
    rw [show x * (x⁻¹ * H.a ^ 2 * x) * x⁻¹ = H.a ^ 2 by group]
    have := H.psi_mem_S (0, 0, 2)
    simpa [psi, psiN] using this
  apply H.not_sq_t hs
  have : x⁻¹ * H.a ^ 4 * x = H.t := by
    rw [← h]; group
  rw [← this, H.z_eq_sq]
  group

end Setting

end CFSG.EvenSporadicStandard.M11Std
