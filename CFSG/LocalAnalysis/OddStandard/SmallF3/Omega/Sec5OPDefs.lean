module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def sec5op_Y (t z : G) : Subgroup G :=
  Subgroup.closure (conjClassIn (centralizer ({z} : Set G)) t)

@[expose] def Asc82FactQCentTwo6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L → IsI4PlusIn L z →
    ∀ K₁ K₂ : Subgroup G, Sl23PocketIn L z K₁ → Sl23PocketIn L z K₂ → K₁ ≠ K₂ →
      Nonempty (↥(twoCoreIn K₁) ≃* QuaternionGroup 2) →
      Nonempty (↥(twoCoreIn K₂) ≃* QuaternionGroup 2) →
      ⁅twoCoreIn K₁, twoCoreIn K₂⁆ = ⊥ → Nat.card ↥(twoCoreIn K₁ ⊔ twoCoreIn K₂) = 32 →
      centerIn (twoCoreIn K₁ ⊔ twoCoreIn K₂) = zpowers z →
        ∀ x : G, x ∈ normalizer (L : Set G) → x ∈ centralizer ({z} : Set G) →
          x ∈ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) →
            ∀ n ∈ twoRes (L ⊓ centralizer ({z} : Set G)), x * n * x⁻¹ * n⁻¹ ∈ oddCoreIn L

@[expose] def Asc82P510TE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r ρ : G) (B A : Subgroup G)
    (φ : (Fin 6 → ZMod 2) → G) (K₁ K₂ : Subgroup G) (a b : G),
    Sec510Ctx G t L S z r ρ B A φ → Sec510Stage1 G t L S z φ A K₁ K₂ a b →
    sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = sec5p510_E t a b →
      ∃ K : Subgroup G, Sl23PocketIn L z K ∧
        ⁅K, sec5op_Y t z⁆ ≤ oddCoreIn (sec5op_Y t z)

@[expose] def Asc82P510TR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r ρ : G) (B A : Subgroup G)
    (φ : (Fin 6 → ZMod 2) → G) (K₁ K₂ : Subgroup G) (a b : G),
    Sec510Ctx G t L S z r ρ B A φ → Sec510Stage1 G t L S z φ A K₁ K₂ a b →
    sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) =
        sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) →
      ∃ K : Subgroup G, Sl23PocketIn L z K ∧
        ⁅K, sec5op_Y t z⁆ ≤ oddCoreIn (sec5op_Y t z)

theorem sec5op_Y_le {t z : G} (ht : t ∈ centralizer ({z} : Set G)) :
    sec5op_Y t z ≤ centralizer ({z} : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨h, hh, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh ht) (Subgroup.inv_mem _ hh)

theorem sec5op_Y_normal (t z : G) :
    ∀ h ∈ centralizer ({z} : Set G), ∀ y ∈ sec5op_Y t z, h * y * h⁻¹ ∈ sec5op_Y t z := by
  intro h hh y hy
  have hmap : (sec5op_Y t z).map (MulAut.conj h).toMonoidHom ≤ sec5op_Y t z := by
    rw [sec5op_Y, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨g, hg, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨h * g, Subgroup.mul_mem _ hh hg, ?_⟩
    simp [mul_assoc]
  exact hmap (Subgroup.mem_map.mpr ⟨y, hy, by simp⟩)

theorem sec5op_t_mem_Y (t z : G) : t ∈ sec5op_Y t z :=
  Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by simp⟩

end CFSG.OddStandard.SmallF3.Omega
