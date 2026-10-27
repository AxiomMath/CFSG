module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrGF

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]

@[expose] def GFrame.map (f : Γ₁ →* Γ₂) (gf : GFrame Γ₁) : GFrame Γ₂ :=
  ⟨f gf.a₁, f gf.b₁, f gf.a₂, f gf.b₂, f gf.h₀, f gf.σ⟩

private theorem centIn_map_of_injective {f : Γ₁ →* Γ₂} (hf : Function.Injective f)
    (V X : Subgroup Γ₁) : centIn (V.map f) (X.map f) = (centIn V X).map f := by
  ext y
  constructor
  · intro hy
    simp only [centIn, Subgroup.mem_inf] at hy
    obtain ⟨hyV, hyC⟩ := hy
    obtain ⟨x, hxV, rfl⟩ := Subgroup.mem_map.mp hyV
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    simp only [centIn, Subgroup.mem_inf]
    refine ⟨hxV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply hf
    rw [map_mul, map_mul]
    exact hyC (f t) (Subgroup.mem_map_of_mem f ht)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    simp only [centIn, Subgroup.mem_inf] at hx
    obtain ⟨hxV, hxC⟩ := hx
    simp only [centIn, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map_of_mem f hxV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hh
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxC t ht]

namespace GFrame

variable (f : Γ₁ →* Γ₂) (gf : GFrame Γ₁)

@[simp] private theorem map_a₁ : (gf.map f).a₁ = f gf.a₁ := rfl
@[simp] private theorem map_b₁ : (gf.map f).b₁ = f gf.b₁ := rfl
@[simp] private theorem map_a₂ : (gf.map f).a₂ = f gf.a₂ := rfl
@[simp] private theorem map_b₂ : (gf.map f).b₂ = f gf.b₂ := rfl
@[simp] private theorem map_h₀ : (gf.map f).h₀ = f gf.h₀ := rfl
@[simp] private theorem map_σ : (gf.map f).σ = f gf.σ := rfl

theorem map_z : (gf.map f).z = f gf.z := by
  simp [GFrame.z]

theorem map_Z : (gf.map f).Z = gf.Z.map f := by
  simp [GFrame.Z, map_z]

theorem map_S : (gf.map f).S = gf.S.map f := by
  simp [GFrame.S, MonoidHom.map_closure]

theorem map_A : (gf.map f).A = gf.A.map f := by
  simp [GFrame.A, MonoidHom.map_closure]

theorem map_Sσ : (gf.map f).Sσ = gf.Sσ.map f := by
  simp [GFrame.Sσ, MonoidHom.map_closure]

theorem map_E : (gf.map f).E = gf.E.map f := by
  simp [GFrame.E, MonoidHom.map_closure, map_z, map_mul]

theorem map_F : (gf.map f).F = gf.F.map f := by
  simp [GFrame.F, MonoidHom.map_closure, map_z, map_mul]

theorem map_B (hf : Function.Injective f) : (gf.map f).B = gf.B.map f := by
  have hs : closure ({f gf.b₁ * f gf.b₂} : Set Γ₂)
      = (closure ({gf.b₁ * gf.b₂} : Set Γ₁)).map f := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp [map_mul]
  rw [GFrame.B, GFrame.B, map_S, ← centIn_map_of_injective hf]
  simp only [map_b₁, map_b₂]
  exact congrArg (centIn (gf.S.map f)) hs

theorem map_classes12 (i : Fin 7) : (gf.map f).classes12 i = f '' gf.classes12 i := by
  fin_cases i <;> simp [GFrame.classes12, map_z, map_mul]

theorem map_reps13 (i : Fin 7) : (gf.map f).reps13 i = f (gf.reps13 i) := by
  fin_cases i <;> simp [GFrame.reps13, map_z, map_mul]

end GFrame

end CFSG.OddStandard.HigherRank.YamadaG23
