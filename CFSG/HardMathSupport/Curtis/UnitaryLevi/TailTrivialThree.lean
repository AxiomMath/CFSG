module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LinePiece
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearHermGram
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction

namespace TailThree

section TailForm

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[σ] V →ₗ[K] K} {W : Submodule K V}

theorem tailForm_aux (hB : B.IsSymm) (x y : ↥(W.orthogonalBilin B))
    (hy : y ∈ W.comap (W.orthogonalBilin B).subtype) : B x y = 0 := by
  rw [hB.eq_iff]
  exact Submodule.mem_orthogonalBilin.mp x.2 _ hy

theorem tailForm_aux' (x y : ↥(W.orthogonalBilin B))
    (hx : x ∈ W.comap (W.orthogonalBilin B).subtype) : B x y = 0 :=
  Submodule.mem_orthogonalBilin.mp y.2 _ hx

variable (W)

@[expose] noncomputable def tailLift (hB : B.IsSymm) (x : ↥(W.orthogonalBilin B)) :
    PieceQ W (W.orthogonalBilin B) →ₗ[K] K :=
  Submodule.liftQ (W.comap (W.orthogonalBilin B).subtype)
    (B.domRestrict₁₂ (W.orthogonalBilin B) (W.orthogonalBilin B) x)
    (fun y hy => tailForm_aux hB x y hy)

theorem tailLift_mk (hB : B.IsSymm) (x y : ↥(W.orthogonalBilin B)) :
    tailLift W hB x (Submodule.Quotient.mk y) = B x y := rfl

@[expose] noncomputable def tailForm (hB : B.IsSymm) :
    PieceQ W (W.orthogonalBilin B) →ₛₗ[σ] PieceQ W (W.orthogonalBilin B) →ₗ[K] K :=
  Submodule.liftQ (W.comap (W.orthogonalBilin B).subtype)
    { toFun := tailLift W hB
      map_add' := fun x y => by
        refine LinearMap.ext fun q => ?_
        induction q using Submodule.Quotient.induction_on with
        | H v => simp [tailLift_mk]
      map_smul' := fun c x => by
        refine LinearMap.ext fun q => ?_
        induction q using Submodule.Quotient.induction_on with
        | H v => simp [tailLift_mk] }
    (fun x hx => by
      refine LinearMap.ext fun q => ?_
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        show tailLift W hB x (Submodule.Quotient.mk v) = 0
        rw [tailLift_mk]; exact tailForm_aux' x v hx)

theorem tailForm_mk (hB : B.IsSymm) (x y : ↥(W.orthogonalBilin B)) :
    tailForm W hB (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := rfl

theorem tailForm_isSymm (hB : B.IsSymm) : (tailForm W hB).IsSymm := by
  refine ⟨fun p q => ?_⟩
  induction p using Submodule.Quotient.induction_on with
  | H x =>
    induction q using Submodule.Quotient.induction_on with
    | H y => rw [tailForm_mk W, tailForm_mk W]; exact hB.eq x y

theorem tailForm_separatingLeft [FiniteDimensional K V] (hσ : Function.Involutive σ)
    (hB : B.IsSymm) (hBs : B.SeparatingLeft) : (tailForm W hB).SeparatingLeft := by
  intro p hp
  induction p using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    have h2 : (x : V) ∈ (W.orthogonalBilin B).orthogonalBilin B := by
      refine Submodule.mem_orthogonalBilin.mpr fun n hn => ?_
      have := hp (Submodule.Quotient.mk ⟨n, hn⟩)
      rw [tailForm_mk W] at this
      exact hB.eq_iff.mp this
    rwa [SesqShear.orthogonalBilin_orthogonalBilin_eq hσ hB hBs W] at h2

end TailForm

section Aux

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem apply_mem_orthogonalBilin {B : V →ₛₗ[σ] V →ₗ[K] K} {W : Submodule K V}
    {d : LinearMap.GeneralLinearGroup K V}
    (hd : ∀ v w, B ((d : Module.End K V) v) ((d : Module.End K V) w) = B v w)
    (hinv : ∀ v ∈ W, ((d⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ W)
    {v : V} (hv : v ∈ W.orthogonalBilin B) : (d : Module.End K V) v ∈ W.orthogonalBilin B := by
  refine Submodule.mem_orthogonalBilin.mpr fun w hw => ?_
  have hw' : (d : Module.End K V)
      (((d⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) = w := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]; rfl
  have := hd (((d⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) v
  rw [hw'] at this
  rw [this]
  exact Submodule.mem_orthogonalBilin.mp hv _ (hinv w hw)

end Aux

end TailThree

section Solvable

variable {K : Type*} [Field K]

theorem isSolvable_sesqUnitaryGroup_of_finrank_le_three (h : UnitaryFieldData 2 1 K) {M : Type*}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] {β : M →ₛₗ[h.bar] M →ₗ[K] K}
    (hβ : β.IsSymm) (hβs : β.SeparatingLeft) (hn : finrank K M ≤ 3) :
    Group.IsSolvable (sesqUnitaryGroup β) := by
  have := h.finite
  have : Finite M := Module.finite_of_finite K
  have : Finite (sesqUnitaryGroup β) := by
    have : Finite (LinearMap.GeneralLinearGroup K M) := by
      have : Finite (Module.End K M) :=
        Finite.of_injective (fun f : Module.End K M => (f : M → M)) DFunLike.coe_injective
      infer_instance
    infer_instance
  have := Fintype.ofFinite (sesqUnitaryGroup β)
  interval_cases hr : finrank K M
  · have : Subsingleton M := Module.finrank_zero_iff.mp hr
    have : Subsingleton (sesqUnitaryGroup β) :=
      ⟨fun a b => Subtype.ext (Units.ext (LinearMap.ext fun x => Subsingleton.elim _ _))⟩
    infer_instance
  · have h1 := (CFSG.LinearGroups.unitary_full_group_order h hβ hβs hr (le_refl 1)).1
    have hc : Fintype.card (sesqUnitaryGroup β) = 2 ^ 0 * 3 ^ 1 := by
      norm_num [Finset.Icc_self] at h1
      exact_mod_cast h1
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) hc
  · have h1 := (CFSG.LinearGroups.unitary_full_group_order h hβ hβs hr (by norm_num)).1
    have hc : Fintype.card (sesqUnitaryGroup β) = 2 ^ 1 * 3 ^ 2 := by
      rw [show Finset.Icc 1 2 = {1, 2} from rfl] at h1
      norm_num [Finset.prod_pair] at h1
      exact_mod_cast h1
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) hc
  · have h1 := (CFSG.LinearGroups.unitary_full_group_order h hβ hβs hr (by norm_num)).1
    have hc : Fintype.card (sesqUnitaryGroup β) = 2 ^ 3 * 3 ^ 4 := by
      rw [show Finset.Icc 1 3 = {1, 2, 3} from rfl] at h1
      norm_num [Finset.prod_insert] at h1
      exact_mod_cast h1
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) hc

end Solvable

section Main

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

open TailThree

theorem isometry_perfect_trivial_on_tail' (h : UnitaryFieldData 2 1 K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBs : B.SeparatingLeft)
    {W : Submodule K V} (_hW : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hm : finrank K (PieceQ W (W.orthogonalBilin B)) ≤ 3)
    (Δ : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hΔ : ∀ d ∈ Δ, (∀ v w, B ((d : Module.End K V) v) ((d : Module.End K V) w) = B v w) ∧
      ∀ v ∈ W, (d : Module.End K V) v ∈ W)
    (hperf : ⁅Δ, Δ⁆ = Δ) :
    ∀ d ∈ Δ, ∀ v ∈ W.orthogonalBilin B, (d : Module.End K V) v - v ∈ W := by
  have hmem : ∀ d ∈ Δ, d ∈ stabPair W (W.orthogonalBilin B) := by
    intro d hd
    have hd' := hΔ d hd
    have hd'' := hΔ d⁻¹ (Δ.inv_mem hd)
    refine ⟨hd'.2, fun v hv => apply_mem_orthogonalBilin hd'.1 hd''.2 hv, hd''.2,
      fun v hv => ?_⟩
    exact apply_mem_orthogonalBilin hd''.1 (by simpa using hd'.2) hv
  have hle : Δ ≤ stabPair W (W.orthogonalBilin B) := hmem
  have : Group.IsPerfect Δ := Subgroup.isPerfect_iff.mpr hperf
  let ψ : Δ →* LinearMap.GeneralLinearGroup K (PieceQ W (W.orthogonalBilin B)) :=
    (quotGL W (W.orthogonalBilin B)).comp (Subgroup.inclusion hle)
  have hψ : ∀ g : Δ, ψ g ∈ sesqUnitaryGroup (tailForm W hB) := by
    intro g p q
    induction p using Submodule.Quotient.induction_on with
    | H x =>
      induction q using Submodule.Quotient.induction_on with
      | H y =>
        change tailForm W hB
          (quotEnd W (W.orthogonalBilin B) ⟨(g : LinearMap.GeneralLinearGroup K V), hle g.2⟩
            (Submodule.Quotient.mk x))
          (quotEnd W (W.orthogonalBilin B) ⟨(g : LinearMap.GeneralLinearGroup K V), hle g.2⟩
            (Submodule.Quotient.mk y)) = tailForm W hB (Submodule.Quotient.mk x)
              (Submodule.Quotient.mk y)
        rw [quotEnd_mk, quotEnd_mk, tailForm_mk, tailForm_mk]
        exact (hΔ g g.2).1 x y
  have hsolv : Group.IsSolvable (sesqUnitaryGroup (tailForm W hB)) :=
    isSolvable_sesqUnitaryGroup_of_finrank_le_three h (tailForm_isSymm W hB)
      (tailForm_separatingLeft W (fun c => h.bar_bar c) hB hBs) hm
  let φ := ψ.codRestrict _ hψ
  intro d hd v hv
  have h1 : ψ ⟨d, hd⟩ = 1 := by
    have := perfect_hom_eq_one φ ⟨d, hd⟩
    exact congrArg Subtype.val this
  have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (PieceQ W (W.orthogonalBilin B)) =>
    (g : Module.End K (PieceQ W (W.orthogonalBilin B)))
      (Submodule.Quotient.mk (⟨v, hv⟩ : ↥(W.orthogonalBilin B)))) h1
  simp only [Units.val_one, Module.End.one_apply] at h2
  change quotEnd W (W.orthogonalBilin B) ⟨d, hmem d hd⟩ (Submodule.Quotient.mk ⟨v, hv⟩) = _ at h2
  rw [quotEnd_mk, Submodule.Quotient.eq] at h2
  simpa [Submodule.mem_comap] using h2

end Main

end CFSG.HardMathSupport.Curtis.UnitaryLevi
