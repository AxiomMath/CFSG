module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

namespace M4

variable [Finite G]

omit [Finite G] in
theorem z_mem_secCent_comp (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    z ∈ secCent K (O K) :=
  secCent_of_central (h.core K hK).le (fun _ hk => (centralizer_comm (h.K_le_C
    (h.comp_le hK hk))).symm)

omit [Finite G] in
theorem unique_inv_D (h : M4 O FA SD z S K₁ K₂) {t : G} (htC : t ∈ centralizer ({z} : Set G))
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂)
    (hR : Rk1 (centralizer ({z, t} : Set G) ⊓ secCent K (O K))) {y : G}
    (hy : y ∈ secCent K (O K)) (hyz : y * z = z * y) (hyt : y * t = t * y) (hy2 : y * y = 1) :
    y = 1 ∨ y = z := by
  have hzc : z ∈ centralizer ({z, t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hw with rfl | hw
    · rfl
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact (centralizer_comm htC)
  have hyc : y ∈ centralizer ({z, t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hw with rfl | hw
    · exact hyz.symm
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact hyt.symm
  have hzD : z ∈ centralizer ({z, t} : Set G) ⊓ secCent K (O K) :=
    ⟨hzc, h.z_mem_secCent_comp hK⟩
  have hyD : y ∈ centralizer ({z, t} : Set G) ⊓ secCent K (O K) := ⟨hyc, hy⟩
  rcases hR y hyD z hzD hy2 h.z_sq hyz with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1 h.z_ne
  · exact Or.inr h1

end M4

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
