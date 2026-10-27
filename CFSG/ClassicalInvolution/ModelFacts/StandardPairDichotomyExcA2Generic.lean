module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2SL2
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts

section Reflect

theorem iform_reflect_single {τ : Tag} (j l : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    iform (reflect τ j v) (Pi.single l 1) =
      iform v (Pi.single l 1) - iform v (Pi.single j 1) * τ.cartan j l := by
  have hx : reflect τ j v = v - (∑ m, τ.cartan j m * v m) • Pi.single j 1 := rfl
  have h1 : iform (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single l 1) =
      τ.symmetrizer j j * τ.cartan j l := by
    rw [iform_single_left]
    congr 1
    simp [Pi.single_apply]
  rw [hx, iform_sub_left, iform_smul_left, h1, iform_single_right v j]
  ring

end Reflect

section Rank1

variable {F : Type} [Field F]

theorem rootSL2_HSL_conj_uSL (τ : Tag) (β : Fin τ.rank → ℤ) (s : Fˣ) (z : F) :
    rootSL2 τ F β (HSL s) * rootSL2 τ F β (uSL z) * (rootSL2 τ F β (HSL s))⁻¹ =
      rootSL2 τ F β (uSL ((s : F) ^ 2 * z)) := by
  rw [← map_inv, ← map_mul, ← map_mul, HSL_conj_uSL_A2]

theorem rootSL2_HSL_conj_vSL (τ : Tag) (β : Fin τ.rank → ℤ) (s : Fˣ) (z : F) :
    rootSL2 τ F β (HSL s) * rootSL2 τ F β (vSL z) * (rootSL2 τ F β (HSL s))⁻¹ =
      rootSL2 τ F β (vSL (((s⁻¹ : Fˣ) : F) ^ 2 * z)) := by
  rw [← map_inv, ← map_mul, ← map_mul, HSL_conj_vSL_A2]

theorem commute_rootSL2_of_commute_uv {τ : Tag} {β : Fin τ.rank → ℤ} {g : ModGL τ F}
    (hu : ∀ z : F, g * rootSL2 τ F β (uSL z) = rootSL2 τ F β (uSL z) * g)
    (hv : ∀ z : F, g * rootSL2 τ F β (vSL z) = rootSL2 τ F β (vSL z) * g) (A : SL2 F) :
    g * rootSL2 τ F β A = rootSL2 τ F β A * g := by
  have hA : A ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hu c
    · exact hv c
  | one => simp
  | mul x y _ _ hx hy =>
    rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | inv x _ ih =>
    rw [map_inv]
    calc g * (rootSL2 τ F β x)⁻¹ = (rootSL2 τ F β x)⁻¹ * (rootSL2 τ F β x * g) *
        (rootSL2 τ F β x)⁻¹ := by group
      _ = (rootSL2 τ F β x)⁻¹ * (g * rootSL2 τ F β x) * (rootSL2 τ F β x)⁻¹ := by rw [ih]
      _ = _ := by group

end Rank1

section Pinned

theorem commute_rootSL2_iff_pinnedX {τ : Tag} {F : Type} [Field F] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (g : ModGL τ F) :
    (∀ A : SL2 F, g * rootSL2 τ F β A = rootSL2 τ F β A * g) ↔
      (∀ a : F, g * pinnedX τ F β a = pinnedX τ F β a * g) ∧
        ∀ a : F, g * pinnedX τ F (-β) a = pinnedX τ F (-β) a * g := by
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := F) hβ
  have hσ : ∀ z : F, (pinnedData τ β).2.2 • (pinnedData τ β).2.2 • z = z := fun z => by
    rcases pinnedSign_eq τ β with h | h <;> rw [h] <;> simp
  constructor
  · intro h
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have := h (uSL ((pinnedData τ β).2.2 • a))
      rwa [rootSL2_uSL_eq, hσ] at this
    · have := h (vSL (ε * a))
      rwa [hv, ← mul_assoc, hε, one_mul] at this
  · rintro ⟨hu, hv'⟩
    refine commute_rootSL2_of_commute_uv (fun z => ?_) (fun z => ?_)
    · rw [rootSL2_uSL_eq]
      exact hu _
    · rw [hv]
      exact hv' _

end Pinned

section Linear

variable {G : Type*} [Group G]

theorem a2_map_conj_inv_map_conj (g : G) (R : Subgroup G) :
    (R.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = R := by
  rw [Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  rw [this, Subgroup.map_id]

theorem map_conj_mem_longestFundamental {K : Type} [Group K] {D : UniversalRootDatum K}
    (g : K) {R : Subgroup K} (hR : R ∈ longestFundamental D) :
    R.map (MulAut.conj g).toMonoidHom ∈ longestFundamental D := by
  obtain ⟨h, γ, hγ, rfl⟩ := hR
  refine ⟨g * h, γ, hγ, ?_⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Linear

section Order

theorem a2_orderOf_conj_eq_two {G : Type*} [Group G] {c : G} (hc : orderOf c = 2) (g : G) :
    orderOf (g * c * g⁻¹) = 2 := by
  rw [← hc]
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
  simpa [MulAut.conj_apply] using this

end Order

end CFSG.ClassicalInvolution.ModelFacts.Levi
