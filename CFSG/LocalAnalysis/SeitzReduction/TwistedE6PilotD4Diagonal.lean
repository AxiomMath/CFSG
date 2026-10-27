module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6YBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance twistedE6PilotD4DiagonalNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

section DiagonalWords

variable {K : Type} [Field K]

private theorem rootDiagUnit_mulSingle_sq_eq {K : Type} [Field K] (j : Fin Tag.E6.rank)
    (c : Kˣ) (a b : ℤ) (e : Fin Tag.E6.rank → ℤ)
    (he : ∀ l, (if l = j then (2 : ℤ) else 0) =
      centralExp a b l + ∑ i, e i * Tag.E6.cartan i l) :
    rootDiagUnit Tag.E6 (Pi.mulSingle j (c ^ 2)) =
      rootDiagUnit Tag.E6 (d4CentralDiag (c ^ a) (c ^ b)) *
        ((List.finRange Tag.E6.rank).map fun i => torusElt Tag.E6 K i (c ^ e i)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_zpow', ← rootDiagUnit_mul,
    d4CentralDiag_zpow]
  congr 1
  funext l
  rw [Pi.mul_apply, ← zpow_add, ← he l]
  by_cases hl : l = j
  · subst hl
    simp
  · simp [hl]

private theorem d4Node_exps : ∀ l : Fin Tag.E6.rank,
    ((if l = 1 then (2 : ℤ) else 0) =
        centralExp 1 1 l + ∑ i, (![0, 2, 1, 2, 1, 0] : Fin 6 → ℤ) i * Tag.E6.cartan i l) ∧
      ((if l = 2 then (2 : ℤ) else 0) =
        centralExp 2 1 l + ∑ i, (![0, 1, 2, 2, 1, 0] : Fin 6 → ℤ) i * Tag.E6.cartan i l) ∧
      ((if l = 3 then (2 : ℤ) else 0) =
        centralExp 2 2 l + ∑ i, (![0, 2, 2, 4, 2, 0] : Fin 6 → ℤ) i * Tag.E6.cartan i l) ∧
      ((if l = 4 then (2 : ℤ) else 0) =
        centralExp 1 2 l + ∑ i, (![0, 1, 1, 2, 2, 0] : Fin 6 → ℤ) i * Tag.E6.cartan i l) := by
  decide

private theorem rootDiagUnit_mulSingle_mem_d4CentralTorus_sup
    (hsq : ∀ u : Kˣ, ∃ c : Kˣ, c ^ 2 = u) (j : Fin Tag.E6.rank) (u : Kˣ) :
    rootDiagUnit Tag.E6 (Pi.mulSingle j u) ∈ d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD := by
  obtain ⟨c, rfl⟩ := hsq u
  have hZ : ∀ a b : ℤ, rootDiagUnit Tag.E6 (d4CentralDiag (c ^ a) (c ^ b)) ∈
      d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD :=
    fun a b => Subgroup.mem_sup_left (mem_d4CentralTorus.2 ⟨_, _, rfl⟩)
  have key : ∀ (a b : ℤ) (e : Fin Tag.E6.rank → ℤ), e 0 = 0 → e 5 = 0 →
      (∀ l, (if l = j then (2 : ℤ) else 0) =
        centralExp a b l + ∑ i, e i * Tag.E6.cartan i l) →
      rootDiagUnit Tag.E6 (Pi.mulSingle j (c ^ 2)) ∈
        d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD := by
    intro a b e h0 h5 he
    rw [rootDiagUnit_mulSingle_sq_eq j c a b e he]
    exact mul_mem (hZ a b) (Subgroup.mem_sup_right (prod_torusElt_mem_d4Levi c h0 h5))
  fin_cases j
  · exact key 2 0 0 rfl rfl (by decide)
  · exact key 1 1 ![0, 2, 1, 2, 1, 0] rfl rfl fun l => (d4Node_exps l).1
  · exact key 2 1 ![0, 1, 2, 2, 1, 0] rfl rfl fun l => (d4Node_exps l).2.1
  · exact key 2 2 ![0, 2, 2, 4, 2, 0] rfl rfl fun l => (d4Node_exps l).2.2.1
  · exact key 1 2 ![0, 1, 1, 2, 2, 0] rfl rfl fun l => (d4Node_exps l).2.2.2
  · exact key 0 2 0 rfl rfl (by decide)

theorem rootDiagUnit_mem_d4CentralTorus_sup
    (hsq : ∀ u : Kˣ, ∃ c : Kˣ, c ^ 2 = u) (b : Fin Tag.E6.rank → Kˣ) :
    rootDiagUnit Tag.E6 b ∈ d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD := by
  rw [← Finset.univ_prod_mulSingle b]
  refine Finset.prod_induction _ (fun b => rootDiagUnit Tag.E6 b ∈
    d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD) (fun x y hx hy => ?_) ?_ fun j _ =>
      rootDiagUnit_mulSingle_mem_d4CentralTorus_sup hsq j (b j)
  · rw [rootDiagUnit_mul]
    exact mul_mem hx hy
  · rw [rootDiagUnit_one]
    exact one_mem _

end DiagonalWords

noncomputable def d4AntiTorus (K : Type) [Field K] : Subgroup (ModGL Tag.E6 K) :=
  ((rootDiagUnitHom Tag.E6 K).comp
    ((d4CentralHom K).comp ((MonoidHom.id Kˣ).prod invMonoidHom))).range

theorem mem_d4AntiTorus {K : Type} [Field K] {g : ModGL Tag.E6 K} :
    g ∈ d4AntiTorus K ↔ ∃ a : Kˣ, rootDiagUnit Tag.E6 (d4CentralDiag a a⁻¹) = g :=
  Iff.rfl

theorem isCyclic_d4AntiTorus (K : Type) [Field K] [Finite K] : IsCyclic (d4AntiTorus K) := by
  haveI : IsCyclic Kˣ := instIsCyclicUnitsOfFinite
  exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

section Normalizer

theorem d4AntiTorus_le_normalizer (K : Type) [Field K] :
    d4AntiTorus K ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 K setD : Set (ModGL Tag.E6 K)) := by
  rintro _ ⟨a, rfl⟩
  have hz : rootDiagUnit Tag.E6 (d4CentralDiag a a⁻¹) ∈ d4CentralTorus K :=
    mem_d4CentralTorus.2 ⟨_, _, rfl⟩
  exact Subgroup.centralizer_le_normalizer _ (d4CentralTorus_le_centralizer hz)

end Normalizer

theorem d4CentralDiag_apply_zero {K : Type} [Field K] (μ ν : Kˣ) :
    d4CentralDiag μ ν 0 = μ := by
  change (Pi.mulSingle (0 : Fin 6) μ * Pi.mulSingle (5 : Fin 6) ν : Fin 6 → Kˣ) 0 = μ
  simp

theorem d4CentralDiag_apply_five {K : Type} [Field K] (μ ν : Kˣ) :
    d4CentralDiag μ ν 5 = ν := by
  change (Pi.mulSingle (0 : Fin 6) μ * Pi.mulSingle (5 : Fin 6) ν : Fin 6 → Kˣ) 5 = ν
  simp

theorem d4CentralDiag_pow {K : Type} [Field K] (μ ν : Kˣ) (k : ℕ) :
    d4CentralDiag μ ν ^ k = d4CentralDiag (μ ^ k) (ν ^ k) := by
  change d4CentralHom K (μ, ν) ^ k = d4CentralHom K (μ ^ k, ν ^ k)
  rw [← map_pow]
  rfl

end CFSG.SeitzReduction.TwistedE6Pilot

end
