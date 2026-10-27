module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six3a
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellTwoTools
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem exists_conj_mem_inf_Six3b {x : G} (hx : x ∈ Hone S)
    (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1) :
    ∃ c ∈ Hone S, c⁻¹ * x * c ∈ (S : Subgroup G) ⊓ Hone S := by
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_inf_of_normal S (Hone S)
  have hx2' : ∃ n : ℕ, (⟨x, hx⟩ : ↥(Hone S)) ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hx2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow hx2' P
  refine ⟨(c : G), c.2, ?_⟩
  have hmem : (((c⁻¹ * (⟨x, hx⟩ : ↥(Hone S)) * c : ↥(Hone S)) : G)) ∈
      (S : Subgroup G) ⊓ Hone S := by
    have h2 := Subgroup.mem_map_of_mem (Hone S).subtype hc
    rwa [hP] at h2
  simpa using hmem

theorem two_element_conjugate_commutationJ (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    {g x : G} (hg : g ∈ Hone S) (hx : x ∈ Hone S) (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (g * x)⁆ = ⊥ := by
  obtain ⟨c, hcH, hcS⟩ := exists_conj_mem_inf_Six3b hx hx2
  have h1 := conj_commute_of_mem_sylowJ h hΛ hα (g := g * c) (t := c⁻¹ * x * c)
    (mul_mem hg hcH) hcS
  have e : g * c * (c⁻¹ * x * c) = g * x * c := by group
  rw [e, ← cj_cj, ← cj_cj, ← cj_commutator] at h1
  calc ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
        cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (g * x)⁆
      = cj (cj ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
          cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (g * x)⁆
          c) c⁻¹ := cj_inv_cj.symm
    _ = cj ⊥ c⁻¹ := by rw [h1]
    _ = ⊥ := cj_bot

end CFSG.QuasithinUnique.Setup.CampbellJ

end
