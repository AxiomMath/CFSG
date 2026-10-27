module

public import CFSG.LargeExtraspecial.AS35KAut
public import CFSG.LargeExtraspecial.AS35KRbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35K

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.AxisFlag
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

@[expose] noncomputable def semi (A : GL (Fin m) K) (φ : K ≃+* K) (x : Fin m → K) : Fin m → K :=
  (A : Matrix (Fin m) (Fin m) K) *ᵥ (φ ∘ x)

theorem semi_add (A : GL (Fin m) K) (φ : K ≃+* K) (x y : Fin m → K) :
    semi A φ (x + y) = semi A φ x + semi A φ y := by
  have h : (φ ∘ (x + y)) = φ ∘ x + φ ∘ y := by
    funext i
    simp
  rw [semi, semi, semi, h, mulVec_add]

theorem semi_smul (A : GL (Fin m) K) (φ : K ≃+* K) (c : K) (x : Fin m → K) :
    semi A φ (c • x) = φ c • semi A φ x := by
  have h : (φ ∘ (c • x)) = φ c • (φ ∘ x) := by
    funext i
    simp
  rw [semi, semi, h, mulVec_smul]

theorem semi_ne_zero (A : GL (Fin m) K) (φ : K ≃+* K) {x : Fin m → K} (hx : x ≠ 0) :
    semi A φ x ≠ 0 := by
  intro h
  apply hx
  have h1 : φ ∘ x = 0 := by
    have h2 := congrArg (fun y => ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ y) h
    simp only [semi, mulVec_mulVec, mulVec_zero] at h2
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h2
  funext i
  have := congrFun h1 i
  simpa using this

theorem herm_semi {A : GL (Fin m) K} (hA : A ∈ primeFormUnitary AS35U.hF
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) (φ : K ≃+* K) (x y : Fin m → K) :
    herm frob (semi A φ x) (semi A φ y) = φ (herm frob x y) := by
  rw [semi, semi, herm_mulVec_of_unitary hA, herm_comp]

theorem semi_smul_of_conj {A : GL (Fin m) K} {φ : K ≃+* K} {a : SUid frob m}
    (h : A * glAut φ (a : GL (Fin m) K) * A⁻¹ = a) (x : Fin m → K) :
    semi A φ (a • x) = a • semi A φ x := by
  have h1 : A * glAut φ (a : GL (Fin m) K) = a * A := by
    calc A * glAut φ (a : GL (Fin m) K) = A * glAut φ (a : GL (Fin m) K) * A⁻¹ * A := by group
      _ = a * A := by rw [h]
  have h2 := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K) *ᵥ (φ ∘ x)) h1
  simp only [Units.val_mul, ← mulVec_mulVec, glAut_mulVec] at h2
  rw [semi, semi, CFSG.ClassicalGroups.Unitary.smul_def, CFSG.ClassicalGroups.Unitary.smul_def]
  exact h2

theorem tvU_mem_Rhat (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) :
    tvU e ∈ Rhat m e := by
  have he' : AS35U.hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨-, hT, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  change AS35U.ι m (tvU e) ∈ axisKernel (AS35U.hermB m) e
  rw [AS35U.ι_tvU he']
  exact hT

theorem exists_flag_mem_Rhat (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0)
    (he : herm frob e e = 0) {u : Fin m → K} (heu : herm frob e u = 0) {c : K}
    (hc : c + frob c = herm frob u u) :
    ∃ a ∈ Rhat m e, ∀ x, a • x =
      x + (herm frob u x + c * herm frob e x) • e + herm frob e x • u := by
  have he' : AS35U.hermB m e e = 0 := he
  have heu' : AS35U.hermB m e u = 0 := heu
  have htr : AS35U.hF.trace c = AS35U.hermB m u u := by
    rw [UnitaryFieldData.trace, AS35U.bar_eq, AS35U.hermB_apply]
    exact hc
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hSU, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  have hg := flagGL_mem AS35U.hermB_isSymm he' heu' htr
  obtain ⟨a, ha⟩ := AS35U.exists_ι_eq (hSU hg)
  refine ⟨a, ?_, fun x => ?_⟩
  · change AS35U.ι m a ∈ axisKernel (AS35U.hermB m) e
    rw [ha]
    exact hg
  · rw [← AS35U.ι_apply, ha, coe_flagGL, flagMap_apply]
    rfl

theorem isPGroup_Rhat (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) :
    IsPGroup 2 (Rhat m e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he' : AS35U.hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, hcard, -, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  refine IsPGroup.of_card (n := 1 + 2 * (Module.finrank K (Fin m → K) - 2)) ?_
  rw [← Subgroup.card_map_of_injective (K := Rhat m e) (f := AS35U.ι m) AS35U.ι_injective,
    map_Rhat_ι hm he0 he, hcard]

end CFSG.LargeExtraspecial.AS35K
