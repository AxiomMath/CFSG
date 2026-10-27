module

public import CFSG.Fischer.Classification.Recognition.SymOOrth
import CFSG.Fischer.Classification.Symplectic.OrthoGen
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs

public section

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

namespace SymO

section Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem componentOrder_orthogonalMatrix {G : Type} [Group G] {D : Set G} {m : ℕ}
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (φ : G ≃* (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x))
    (hφ : ∀ g : G, g ∈ D ↔ (φ g : GL (Fin (2 * m)) (ZMod 2)) ∈
      fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)
    {d : G} (hd : d ∈ D) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders := by
  obtain ⟨v, hv, hdv⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections ((hφ d).mp hd)
  have hH : (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x).map
      (toLinEquiv (Fin (2 * m)) (ZMod 2) : GL (Fin (2 * m)) (ZMod 2) →* _) =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [fischerMatrixGroup_isometry_eq_comap]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ _).surjective _
  set Φ := φ.trans (((toLinEquiv (Fin (2 * m)) (ZMod 2)).subgroupMap _).trans
    (MulEquiv.subgroupCongr hH))
  have hΦd : ∀ x, ((Φ d : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x = x + polar Q x v • v := by
    intro x
    change toLinEquiv (Fin (2 * m)) (ZMod 2) (φ d : GL (Fin (2 * m)) (ZMod 2)) x = _
    rw [hdv, toLinEquiv_orthTransvectionGL, reflect_apply_of_map_eq_one hv]
  have hK' : IsComponentOf (K.map Φ.toMonoidHom) (Subgroup.centralizer {Φ d}) := by
    rw [← map_centralizer_singleton]
    exact IsComponentOf.map_mulEquiv Φ hK
  rw [← card_quotient_center_map_mulEquiv Φ K]
  refine componentOrder_orthogonal ⟨fun x hx => hnd x fun y => ?_, fun y hy => hnd y fun x => ?_⟩
    hv (Φ d) hΦd hK'
  · rw [← polarBilin_apply_apply]
    exact hx y
  · rw [polar_comm, ← polarBilin_apply_apply]
    exact hy x

end Matrix

end SymO

theorem componentOrder_case3 {G : Type} [Group G] {D : Set G}
    (hN : ∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1))
    {d : G} (hd : d ∈ D) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders := by
  obtain ⟨m, -, Q, hnd, -, φ, hφ⟩ := hN
  exact SymO.componentOrder_orthogonalMatrix Q hnd φ hφ hd hK

end CFSG.Fischer.Classification.Recognition
