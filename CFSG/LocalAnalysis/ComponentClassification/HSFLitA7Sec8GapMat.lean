module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapCoord
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8BCase

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

namespace MB

theorem QC_normal_aux : ∀ g x : MB, inQC x = true → inQC (g * x * g⁻¹) = true := by
  decide +kernel

end MB

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

@[expose] noncomputable def Φ (a : Fin 3 → ZMod 4) : X := A.ι (MB.coord a)

theorem Φ_def (a : Fin 3 → ZMod 4) : A.Φ a = A.ι (MB.coord a) := rfl

theorem Φ_add (a b : Fin 3 → ZMod 4) : A.Φ (a + b) = A.Φ a * A.Φ b := by
  rw [Φ, Φ, Φ, MB.coord_add, map_mul]

theorem Φ_zero : A.Φ 0 = 1 := by rw [Φ, MB.coord_zero, map_one]

theorem Φ_neg (a : Fin 3 → ZMod 4) : A.Φ (-a) = (A.Φ a)⁻¹ := by
  rw [Φ, Φ, MB.coord_neg, map_inv]

theorem Φ_sub (a b : Fin 3 → ZMod 4) : A.Φ (a - b) = A.Φ a * (A.Φ b)⁻¹ := by
  rw [sub_eq_add_neg, Φ_add, Φ_neg]

theorem Φ_nsmul (n : ℕ) (a : Fin 3 → ZMod 4) : A.Φ (n • a) = A.Φ a ^ n := by
  rw [Φ, Φ, MB.coord_nsmul, map_pow]

theorem Φ_injective : Function.Injective A.Φ :=
  A.ι_injective.comp MB.coord_injective

theorem Φ_comm (a b : Fin 3 → ZMod 4) : A.Φ a * A.Φ b = A.Φ b * A.Φ a := by
  rw [← Φ_add, ← Φ_add, add_comm]

@[expose] noncomputable def AA : Subgroup X := MB.QC.map A.ι

theorem mem_AA {g : X} : g ∈ A.AA ↔ ∃ a, A.Φ a = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := MB.exists_coord hx
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, MB.inQC_coord a, rfl⟩

theorem Φ_mem (a : Fin 3 → ZMod 4) : A.Φ a ∈ A.AA := A.mem_AA.mpr ⟨a, rfl⟩

theorem AA_le_S₁ : A.AA ≤ A.D₁.S₁ := by
  rw [AA, ← A.range_ι]; exact map_le_range _ _

theorem AA_comm {g h : X} (hg : g ∈ A.AA) (hh : h ∈ A.AA) : g * h = h * g := by
  obtain ⟨a, rfl⟩ := A.mem_AA.mp hg
  obtain ⟨b, rfl⟩ := A.mem_AA.mp hh
  exact A.Φ_comm a b

theorem t_conj_Φ (a : Fin 3 → ZMod 4) : S.t * A.Φ a * S.t⁻¹ = A.Φ (-a) := by
  rw [Φ, Φ, ← A.ι_t, ← map_inv, ← map_mul, ← map_mul, MB.t_conj_coord]

theorem u_conj_Φ (a : Fin 3 → ZMod 4) :
    A.D₁.u * A.Φ a * A.D₁.u⁻¹ = A.Φ (MB.uvec a) := by
  rw [Φ, Φ, ← A.ι_u, ← map_inv, ← map_mul, ← map_mul, MB.u_conj_coord]

theorem Φ_e0 : A.Φ ![1, 0, 0] = A.V₁.w₁N := by rw [Φ, MB.coord_e0, A.ι_w₁]
theorem Φ_e1 : A.Φ ![0, 1, 0] = A.D₁.w₂ := by rw [Φ, MB.coord_e1, A.ι_w₂]
theorem Φ_e2 : A.Φ ![0, 0, 1] = S.t * A.V₁.vN := by
  rw [Φ, MB.coord_e2, MB.c, map_mul, A.ι_t, A.ι_v]
theorem Φ_z : A.Φ ![2, 0, 0] = S.z := by rw [Φ, MB.coord_z, A.ι_z]
theorem Φ_y : A.Φ ![0, 2, 0] = F.yF := by rw [Φ, MB.coord_y, A.ι_y]
theorem Φ_k : A.Φ ![0, 0, 2] = F.kF := by rw [Φ, MB.coord_k, A.ι_k]

theorem S₁_le_normalizer : A.D₁.S₁ ≤ normalizer (A.AA : Set X) := by
  rw [← A.range_ι]
  rintro _ ⟨g, rfl⟩
  rw [mem_normalizer_iff]
  have key : ∀ g : MB, ∀ h ∈ A.AA, A.ι g * h * (A.ι g)⁻¹ ∈ A.AA := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨g * x * g⁻¹, MB.QC_normal_aux g x hx, by rw [map_mul, map_mul, map_inv]⟩
  intro h
  refine ⟨key g h, fun hh => ?_⟩
  have := key g⁻¹ _ hh
  rwa [map_inv, inv_inv, show (A.ι g)⁻¹ * (A.ι g * h * (A.ι g)⁻¹) * A.ι g = h by group] at this

@[expose] noncomputable def NA : Subgroup X := normalizer (A.AA : Set X)

theorem conj_mem_AA {g : X} (hg : g ∈ A.NA) {h : X} (hh : h ∈ A.AA) : g * h * g⁻¹ ∈ A.AA :=
  (mem_normalizer_iff.mp hg h).mp hh

theorem exists_conj (g : A.NA) (a : Fin 3 → ZMod 4) :
    ∃ b, A.Φ b = (g : X) * A.Φ a * (g : X)⁻¹ :=
  A.mem_AA.mp (A.conj_mem_AA g.2 (A.Φ_mem a))

noncomputable def actFun (g : A.NA) (a : Fin 3 → ZMod 4) : Fin 3 → ZMod 4 :=
  Classical.choose (A.exists_conj g a)

theorem Φ_actFun (g : A.NA) (a : Fin 3 → ZMod 4) :
    A.Φ (A.actFun g a) = (g : X) * A.Φ a * (g : X)⁻¹ :=
  Classical.choose_spec (A.exists_conj g a)

noncomputable def actAdd (g : A.NA) : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) where
  toFun := A.actFun g
  map_zero' := by
    apply A.Φ_injective
    rw [Φ_actFun, Φ_zero, mul_one, mul_inv_cancel]
  map_add' a b := by
    apply A.Φ_injective
    rw [Φ_actFun, Φ_add, Φ_add, Φ_actFun, Φ_actFun]
    group

noncomputable def mat (g : A.NA) : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  LinearMap.toMatrix' ((A.actAdd g).toZModLinearMap 4)

theorem conj_Φ (g : A.NA) (a : Fin 3 → ZMod 4) :
    (g : X) * A.Φ a * (g : X)⁻¹ = A.Φ (A.mat g *ᵥ a) := by
  rw [mat, LinearMap.toMatrix'_mulVec]
  exact (A.Φ_actFun g a).symm

theorem mat_eq_of {g : A.NA} {M : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (h : ∀ a, (g : X) * A.Φ a * (g : X)⁻¹ = A.Φ (M *ᵥ a)) : A.mat g = M := by
  rw [Matrix.ext_iff_mulVec]
  intro a
  apply A.Φ_injective
  rw [← conj_Φ, h]

theorem mat_one : A.mat 1 = 1 :=
  A.mat_eq_of fun a => by rw [Matrix.one_mulVec]; simp

theorem mat_mul (g h : A.NA) : A.mat (g * h) = A.mat g * A.mat h :=
  A.mat_eq_of fun a => by
    rw [← Matrix.mulVec_mulVec, ← conj_Φ, ← conj_Φ]
    simp only [Subgroup.coe_mul]
    group

@[expose] noncomputable def matHom : A.NA →* Matrix (Fin 3) (Fin 3) (ZMod 4) where
  toFun := A.mat
  map_one' := A.mat_one
  map_mul' := A.mat_mul

theorem matHom_apply (g : A.NA) : A.matHom g = A.mat g := rfl

theorem mat_eq_one_iff (g : A.NA) : A.mat g = 1 ↔ (g : X) ∈ centralizer (A.AA : Set X) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := A.mem_AA.mp hx
    have := A.conj_Φ g a
    rw [h, Matrix.one_mulVec] at this
    calc A.Φ a * (g : X) = (g : X) * A.Φ a * (g : X)⁻¹ * (g : X) := by rw [this]
      _ = (g : X) * A.Φ a := by group
  · intro h
    refine A.mat_eq_of fun a => ?_
    rw [Matrix.one_mulVec, (mem_centralizer_iff.mp h _ (A.Φ_mem a)).symm, mul_inv_cancel_right]

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
