module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Linear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup

variable {Y V : Type} [Group Y] [AddCommGroup V] [Module (ZMod 2) V]

theorem commSub_closure_le [Finite V] (ρ : Representation (ZMod 2) Y V) (S : Set Y) :
    commSub ρ (Subgroup.closure S) ≤ ⨆ s ∈ S, LinearMap.range (ρ s - 1) := by
  set U : Submodule (ZMod 2) V := ⨆ s ∈ S, LinearMap.range (ρ s - 1) with hU
  have key : ∀ m ∈ Subgroup.closure S,
      LinearMap.range (ρ m - 1) ≤ U ∧ ∀ u ∈ U, ρ m u ∈ U := by
    intro m hm
    refine Subgroup.closure_induction
      (p := fun m _ => LinearMap.range (ρ m - 1) ≤ U ∧ ∀ u ∈ U, ρ m u ∈ U) ?_ ?_ ?_ ?_ hm
    · intro s hs
      have hle : LinearMap.range (ρ s - 1) ≤ U :=
        le_iSup₂ (f := fun s (_ : s ∈ S) => LinearMap.range (ρ s - 1)) s hs
      refine ⟨hle, fun u hu => ?_⟩
      have : ρ s u = u + (ρ s - 1) u := by simp
      rw [this]
      exact U.add_mem hu (hle ⟨u, rfl⟩)
    · refine ⟨?_, fun u hu => ?_⟩
      · rintro _ ⟨v, rfl⟩
        simp
      · simpa using hu
    · rintro x y _ _ ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
      refine ⟨?_, fun u hu => ?_⟩
      · rintro _ ⟨v, rfl⟩
        have : (ρ (x * y) - 1) v = ρ x ((ρ y - 1) v) + (ρ x - 1) v := by
          simp only [LinearMap.sub_apply, Module.End.one_apply, map_mul, Module.End.mul_apply,
            map_sub]
          abel
        rw [this]
        exact U.add_mem (hx2 _ (hy1 ⟨v, rfl⟩)) (hx1 ⟨v, rfl⟩)
      · rw [map_mul, Module.End.mul_apply]
        exact hx2 _ (hy2 u hu)
    · rintro x _ ⟨hx1, hx2⟩
      have hinv : ∀ u ∈ U, ρ x⁻¹ u ∈ U := by
        intro u hu
        let f : U → U := fun v => ⟨ρ x v, hx2 v v.2⟩
        have hf : Function.Injective f := by
          intro a b hab
          have h1 : ρ x (a : V) = ρ x (b : V) := congrArg Subtype.val hab
          have h2 := congrArg (ρ x⁻¹) h1
          simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] at h2
          exact Subtype.ext h2
        obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
        have h1 : ρ x v = u := congrArg Subtype.val hv
        have h3 : ρ x⁻¹ u = v := by
          rw [← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]
        rw [h3]
        exact v.2
      refine ⟨?_, hinv⟩
      rintro _ ⟨v, rfl⟩
      have : (ρ x⁻¹ - 1) v = -(ρ x⁻¹ ((ρ x - 1) v)) := by
        simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← Module.End.mul_apply,
          ← map_mul, inv_mul_cancel, map_one, neg_sub]
      rw [this]
      exact U.neg_mem (hinv _ (hx1 ⟨v, rfl⟩))
  exact iSup₂_le fun m hm => (key m hm).1

theorem rho_conj_apply (ρ : Representation (ZMod 2) Y V) (y t : Y) (v : V) :
    ρ (y * t * y⁻¹) v = ρ y (ρ t (ρ y⁻¹ v)) := by
  rw [map_mul, map_mul]
  rfl

theorem rho_mul_inv (ρ : Representation (ZMod 2) Y V) (y : Y) (v : V) : ρ y (ρ y⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_mul (ρ : Representation (ZMod 2) Y V) (y : Y) (v : V) : ρ y⁻¹ (ρ y v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem range_conj (ρ : Representation (ZMod 2) Y V) (y t : Y) :
    LinearMap.range (ρ (y * t * y⁻¹) - 1) =
      (LinearMap.range (ρ t - 1)).map (repEquiv ρ y : V →ₗ[ZMod 2] V) := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨(ρ t - 1) (ρ y⁻¹ v), ⟨ρ y⁻¹ v, rfl⟩, ?_⟩
    change ρ y ((ρ t - 1) (ρ y⁻¹ v)) = (ρ (y * t * y⁻¹) - 1) v
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, rho_conj_apply, rho_mul_inv]
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨ρ y v, ?_⟩
    change (ρ (y * t * y⁻¹) - 1) (ρ y v) = ρ y ((ρ t - 1) v)
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, rho_conj_apply, rho_inv_mul]

theorem finrank_range_conj [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) Y V)
    (y t : Y) : Module.finrank (ZMod 2) (LinearMap.range (ρ (y * t * y⁻¹) - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  rw [range_conj]
  exact LinearEquiv.finrank_map_eq (repEquiv ρ y) _

theorem finrank_inf_conj [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) Y V)
    (y a b : Y) : Module.finrank (ZMod 2) (LinearMap.range (ρ (y * a * y⁻¹) - 1) ⊓
        LinearMap.range (ρ (y * b * y⁻¹) - 1) : Submodule (ZMod 2) V) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1) ⊓ LinearMap.range (ρ b - 1) :
        Submodule (ZMod 2) V) := by
  rw [range_conj, range_conj, ← Submodule.map_inf _ (repEquiv ρ y).injective]
  exact LinearEquiv.finrank_map_eq (repEquiv ρ y) _

theorem finrank_sup_four_le [Module.Finite (ZMod 2) V] {A A' B B' : Submodule (ZMod 2) V}
    (hA : Module.finrank (ZMod 2) A = 20) (hA' : Module.finrank (ZMod 2) A' = 20)
    (hB : Module.finrank (ZMod 2) B = 20) (hB' : Module.finrank (ZMod 2) B' = 20)
    (hAB : 16 ≤ Module.finrank (ZMod 2) (A ⊓ B : Submodule (ZMod 2) V))
    (hA'B' : 16 ≤ Module.finrank (ZMod 2) (A' ⊓ B' : Submodule (ZMod 2) V))
    (hAA' : 12 ≤ Module.finrank (ZMod 2) (A ⊓ A' : Submodule (ZMod 2) V)) :
    Module.finrank (ZMod 2) (A ⊔ (A' ⊔ (B ⊔ B')) : Submodule (ZMod 2) V) ≤ 36 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq A' B'
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (A' ⊔ B')
  have h4 : A ⊔ (A' ⊔ (B ⊔ B')) = (A ⊔ B) ⊔ (A' ⊔ B') := by
    rw [sup_sup_sup_comm]
    simp only [sup_assoc, sup_comm, sup_left_comm]
  have h5 : A ⊓ A' ≤ (A ⊔ B) ⊓ (A' ⊔ B') :=
    inf_le_inf le_sup_left le_sup_left
  have h6 := Submodule.finrank_mono h5
  rw [h4]
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
