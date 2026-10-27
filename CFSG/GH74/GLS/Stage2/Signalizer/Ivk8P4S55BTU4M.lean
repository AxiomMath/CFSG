module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4T2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4T
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4C
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4C2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4P2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher BS4 BL4
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem false_of_point_u4 (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    {I Q : Subgroup (hypPSU h 2 0)} (hI : ⁅I, I⁆ = I) (hQI : Q ≤ I)
    (hQ : IVK.IsFourSubgroup Q) {N : Submodule K (HypIndex 2 0 → K)} {g : hypSU h 2 0}
    (hg : g • hypFlag h 2 0 1 = N)
    (hIN : ∀ s ∈ I.comap (hypProj h 2 0), ∀ v ∈ N,
      (((s : hypSU h 2 0) : GL (HypIndex 2 0) K) : MH K) *ᵥ v ∈ N) : False := by
  set ψ := ψU h (g : GL (HypIndex 2 0) K) with hψ
  set G' := (I.comap (hypProj h 2 0)).map ψ with hG'
  have hgU : (g : GL (HypIndex 2 0) K) ∈ hypUnitary h 2 0 :=
    mem_hypUnitary.mpr (mem_hypSU.mp g.2).1
  have hG : ∀ x ∈ G', ∃ c : K, (x : MB K) *ᵥ e0 = c • e0 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [coe_ψU]
    exact cv_e0 hg (hIN s hs)
  have hGu : ∀ x ∈ G', ((x : MB K).map h.bar)ᵀ * jU * (x : MB K) = jU := by
    rintro _ ⟨s, -, rfl⟩
    rw [coe_ψU]
    exact cv_herm _ hgU (mem_hypSU.mp s.2).1
  have hcomm : ⁅G', G'⁆ = (Hu h I).map ψ := (Subgroup.map_commutator _ _ _).symm
  have hπ : (Hu h I).map (hypProj h 2 0) = I := by
    show (⁅I.comap (hypProj h 2 0), I.comap (hypProj h 2 0)⁆).map (hypProj h 2 0) = I
    rw [Subgroup.map_commutator, map_comap_eq_self_of_surjective (hypProj_surjective h 2 0), hI]
  obtain ⟨a, ha, b, hb, ha1, hb1, hab1, haa, hbb, habab⟩ := exists_pair_four hQ
  obtain ⟨s₁, hs₁, rfl⟩ : ∃ s ∈ Hu h I, hypProj h 2 0 s = a := by
    rw [← Subgroup.mem_map, hπ]
    exact hQI ha
  obtain ⟨s₂, hs₂, rfl⟩ : ∃ s ∈ Hu h I, hypProj h 2 0 s = b := by
    rw [← Subgroup.mem_map, hπ]
    exact hQI hb
  have hsc : ∀ s : hypSU h 2 0, hypProj h 2 0 s = 1 →
      ∃ c : K, ((ψ s : GL (Fin 2 ⊕ Fin 2) K) : MB K) = c • 1 := by
    intro s hs
    have hk : s ∈ hypScalars h 2 0 := by
      rw [← ker_hypProj]
      exact hs
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hk
    exact ⟨c, by rw [coe_ψU, hc, cv_scalar]⟩
  have hne : ∀ s : hypSU h 2 0, hypProj h 2 0 s ≠ 1 → ψ s ≠ 1 := by
    intro s hs h1
    have : s = 1 := ψU_injective _ (h1.trans (map_one ψ).symm)
    exact hs (by rw [this, map_one])
  have hmem : ∀ s ∈ Hu h I, ψ s ∈ ⁅G', G'⁆ := fun s hs => hcomm ▸ ⟨s, hs, rfl⟩
  refine false_of_pointU (φ := h.bar) h2 hG hGu (hmem _ hs₁) (hmem _ hs₂) ?_ ?_ ?_ (hne _ ha1)
    (hne _ hb1) ?_
  · rw [← map_mul]
    exact hsc _ (by rw [map_mul, haa])
  · rw [← map_mul]
    exact hsc _ (by rw [map_mul, hbb])
  · simp only [← map_mul]
    exact hsc _ (by simp only [map_mul]; exact habab)
  · rw [← map_mul]
    exact hne _ (by rw [map_mul]; exact hab1)

theorem semi_mul_semi {h : UnitaryFieldData p f K} {A₁ A₂ A₃ : GL (HypIndex 2 0) K}
    {σ₁ σ₂ σ₃ : K ≃+* K} (hσ₁ : ∀ c, σ₁ c = h.bar c) (hσ₂ : ∀ c, σ₂ c = h.bar c)
    (hσ₃ : ∀ c, σ₃ c = h.bar c)
    (hx₁ : (⟨A₁, σ₁⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hx₂ : (⟨A₂, σ₂⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hx₃ : (⟨A₃, σ₃⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (he : semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx₃⟩ =
      semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx₁⟩ *
        semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx₂⟩) : False := by
  rw [← map_mul] at he
  obtain ⟨hr, -⟩ := eq_of_semilinearAutHom_eq he
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have e := congrArg (fun τ : K ≃+* K => τ c) hr
  simp only [Subgroup.coe_mul, SemidirectProduct.mul_right, RingAut.mul_apply] at e
  rw [hσ₃, hσ₁, hσ₂, h.bar_bar] at e
  exact hc e

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
