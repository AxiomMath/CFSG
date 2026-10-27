module

public import CFSG.LieType.Ree.RelWeylRee
public import CFSG.LieType.Chevalley.ParabolicRootFactorData

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable (t : ReeTag)

theorem weylPerm_smul_eq_dualRoot
    (w : WeylGroup t.tag) {β : Fin t.tag.rank → ℤ}
    (hβ : IsRoot t.tag β) : t.weylPerm w • β = t.dualRoot (w • t.dualRoot β) := by
  rw [dualRoot_smul w (isRoot_dualRoot hβ), dualRoot_dualRoot hβ]

@[expose] def fixedOrbitCount : ReeTag → ℕ
  | G2 => 1
  | F4 => 2

@[expose] def fixedOrbitSet : (t : ReeTag) → Fin t.fixedOrbitCount → Set (Fin t.tag.rank)
  | G2, _ => ({0, 1} : Set (Fin 2))
  | F4, j => if j.val = 0 then ({0, 3} : Set (Fin 4)) else ({1, 2} : Set (Fin 4))

@[expose] def fixedOrbitWord : (t : ReeTag) → Fin t.fixedOrbitCount → List (Fin t.tag.rank)
  | G2, _ => ([0, 1, 0, 1, 0, 1] : List (Fin 2))
  | F4, j => if j.val = 0 then ([0, 3] : List (Fin 4)) else ([1, 2, 1, 2] : List (Fin 4))

@[expose] def fixedOrbitElement
    (j : Fin t.fixedOrbitCount) : WeylGroup t.tag :=
  (coxeterSystem t.tag).wordProd (t.fixedOrbitWord j)

@[expose] def fixedOrbitWeyl
    (j : Fin t.fixedOrbitCount) : Subgroup (WeylGroup t.tag) :=
  parabolicWeylGroup t.tag (t.fixedOrbitSet j)

@[expose] def fixedOrbitRoots (j : Fin t.fixedOrbitCount) : Set (Fin t.tag.rank → ℤ) :=
  parabolicPosRoots t.tag (t.fixedOrbitSet j)

@[expose] def fixedOrbitComplementRoots (j : Fin t.fixedOrbitCount) :
    Set (Fin t.tag.rank → ℤ) :=
  parabolicRadicalRoots t.tag (t.fixedOrbitSet j)

theorem mem_fixedOrbitRoots {j : Fin t.fixedOrbitCount} {α : Fin t.tag.rank → ℤ} :
    α ∈ t.fixedOrbitRoots j ↔
      (IsRoot t.tag α ∧ 0 < height α) ∧ ∀ i ∉ t.fixedOrbitSet j, α i = 0 :=
  ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1⟩⟩

theorem fixedOrbitComplementRoots_eq (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitComplementRoots j =
      {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α} \ t.fixedOrbitRoots j :=
  rfl

theorem ree_fixed_Weyl_data :
    (∀ (w : WeylGroup t.tag) (β : Fin t.tag.rank → ℤ), IsRoot t.tag β →
      t.weylPerm w • β = t.dualRoot (w • t.dualRoot β)) ∧
    (∀ w : WeylGroup t.tag, w ∈ t.relWeylRee ↔ t.weylPerm w = w) ∧
    (∀ j, t.fixedOrbitWeyl j = Subgroup.closure (simple t.tag '' t.fixedOrbitSet j)) ∧
    (∀ j, t.fixedOrbitElement j = (coxeterSystem t.tag).wordProd (t.fixedOrbitWord j)) ∧
    (∀ j (α : Fin t.tag.rank → ℤ), α ∈ t.fixedOrbitRoots j ↔
      (IsRoot t.tag α ∧ 0 < height α) ∧ ∀ i ∉ t.fixedOrbitSet j, α i = 0) ∧
    ∀ j, t.fixedOrbitComplementRoots j =
      {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α} \ t.fixedOrbitRoots j :=
  ⟨fun w _ hβ => t.weylPerm_smul_eq_dualRoot w hβ, fun _ => Iff.rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ => t.mem_fixedOrbitRoots, t.fixedOrbitComplementRoots_eq⟩

end ReeTag

end CFSG.LieType.Ree
