module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTwoSetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.x_pt (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    (q : Option (Fin 7)) :
    ∃ q' : Option (Fin 7), x * sec4MPt t φ q * x⁻¹ = sec4FD t φ x q' := by
  obtain ⟨ρ, hρ⟩ := h.exists_realizes (hT.PM hT.x2)
  refine ⟨ρ q, ?_⟩
  rw [sec4FD, ← hρ q]
  group

theorem Sec4FSetup.K_to_d (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {p : G}
    (hp : p ∈ P) (a : Option (Fin 7)) :
    ∃ e : Option (Fin 7), (x * p) * sec4MPt t φ a * (x * p)⁻¹ = sec4FD t φ x e := by
  have hpM : p ∈ normalizer (A : Set G) := hT.PM hp
  have hA : p * sec4MPt t φ a * p⁻¹ ∈ A :=
    (Subgroup.mem_set_normalizer_iff.mp hpM (sec4MPt t φ a)).mp (sec4MPt_mem_A h.data a)
  obtain ⟨k, hk⟩ := (conj_iff_mem_conjClassIn_top (t := t)).mpr (h.pt_mem_conj a)
  have hconj : p * sec4MPt t φ a * p⁻¹ = (k * p⁻¹)⁻¹ * t * (k * p⁻¹) := by
    rw [hk]; group
  obtain ⟨a'', ha''⟩ := h.exists_pt_of_conj ⟨k * p⁻¹, hconj⟩ hA
  obtain ⟨q', hq'⟩ := h.x_pt hT a''
  refine ⟨q', ?_⟩
  rw [show (x * p) * sec4MPt t φ a * (x * p)⁻¹
        = x * (p * sec4MPt t φ a * p⁻¹) * x⁻¹ by group, ha'', hq']

theorem Sec4FSetup.K_to_pt (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {p : G}
    (hp : p ∈ P) (c : Option (Fin 7)) :
    ∃ q : Option (Fin 7), (x * p) * sec4FD t φ x c * (x * p)⁻¹ = sec4MPt t φ q := by
  have hmP : x * p * x⁻¹ ∈ P := (Subgroup.mem_set_normalizer_iff.mp hT.xP p).mp hp
  have hmM : x * p * x⁻¹ ∈ normalizer (A : Set G) := hT.PM hmP
  have hkey : (x * p) * sec4FD t φ x c * (x * p)⁻¹
      = (x * p * x⁻¹) * sec4MPt t φ c * (x * p * x⁻¹)⁻¹ := by
    rw [sec4FD]; group
  have hA : (x * p * x⁻¹) * sec4MPt t φ c * (x * p * x⁻¹)⁻¹ ∈ A :=
    (Subgroup.mem_set_normalizer_iff.mp hmM (sec4MPt t φ c)).mp (sec4MPt_mem_A h.data c)
  obtain ⟨k, hk⟩ := (conj_iff_mem_conjClassIn_top (t := t)).mpr (h.pt_mem_conj c)
  have hconj : (x * p * x⁻¹) * sec4MPt t φ c * (x * p * x⁻¹)⁻¹
      = (k * (x * p * x⁻¹)⁻¹)⁻¹ * t * (k * (x * p * x⁻¹)⁻¹) := by
    rw [hk]; group
  obtain ⟨q, hq⟩ := h.exists_pt_of_conj ⟨k * (x * p * x⁻¹)⁻¹, hconj⟩ hA
  exact ⟨q, by rw [hkey, hq]⟩

end CFSG.OddStandard.SmallF3.Omega
