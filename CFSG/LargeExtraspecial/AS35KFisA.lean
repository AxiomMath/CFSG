module

public import CFSG.Assembly.Subnormal
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Fischer.Classification.Symplectic.OrthoGen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.Literature.FSmithOrthogonal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Open CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Recognition
  CFSG.Fischer.Classification.Unitary
open scoped commutatorElement

namespace AS35K

variable {X : Type*} [Group X]

theorem map_eq_one_of_simple [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    {A : Type*} [CommGroup A] (f : X →* A) (g : X) : f g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · obtain ⟨x, y, hxy⟩ := hna
    refine (hxy ((MonoidHom.ker_eq_bot_iff f).mp h ?_)).elim
    rw [map_mul, map_mul, mul_comm]
  · exact (h ▸ mem_top g : g ∈ f.ker)

theorem center_eq_bot_of_simple [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) :
    center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab

theorem commutator_eq_top_of_simple [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) :
    _root_.commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hc : ⁅a, b⁆ ∈ _root_.commutator X := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hab hc
  · exact h

theorem closure_isConj_eq_top [IsSimpleGroup X] {d : X} (hd : d ≠ 1) :
    closure {g | IsConj d g} = ⊤ := by
  have hn : (closure {g | IsConj d g}).Normal := by
    refine ⟨fun x hx c => ?_⟩
    induction hx using closure_induction with
    | mem y hy =>
      exact subset_closure ((hy : IsConj d y).trans (isConj_iff.mpr ⟨c, rfl⟩))
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show c * (x * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ by group]
      exact inv_mem hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (closure {g | IsConj d g}) with h | h
  · exfalso
    have : d ∈ closure {g | IsConj d g} := subset_closure (IsConj.refl d)
    rw [h, mem_bot] at this
    exact hd this
  · exact h

theorem false_of_perm [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) {m : ℕ}
    (φ : X ≃* Equiv.Perm (Fin m)) {d : X} (hφ : (φ d).IsSwap) : False := by
  have h := map_eq_one_of_simple hna (Equiv.Perm.sign.comp φ.toMonoidHom) d
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφ.sign_eq] at h
  exact absurd h (by decide)

theorem false_of_orthogonalGroup [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (Φ : X ≃* TauCeti.QuadraticMap.orthogonalGroup Q) {d : X} {v : V} (hv : Q v = 1)
    (hΦ : ((Φ d : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q v) : False := by
  have h := map_eq_one_of_simple hna ((dicksonHom Q hQ).comp Φ.toMonoidHom) d
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, dicksonHom_apply, hΦ,
    CFSG.RankThree.Literature.FSmith.finrank_commSpace_reflect hQ hv, Nat.cast_one,
    ofAdd_eq_one] at h
  exact one_ne_zero h

open Matrix in
theorem false_of_case3 [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) {D : Set X}
    {d : X} (hd : d ∈ D) {m : ℕ} {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (h : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨v, hv, hdv⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections ((hφ d).mp hd)
  set T := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)
  have hH : (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x).map
      (T : GL (Fin (2 * m)) (ZMod 2) →* _) = TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [fischerMatrixGroup_isometry_eq_comap]
    exact Subgroup.map_comap_eq_self_of_surjective T.surjective _
  have hnd' : (polarBilin Q).Nondegenerate := by
    refine ⟨fun x hx => hnd x fun y => ?_, fun y hy => hnd y fun x => ?_⟩
    · rw [← polarBilin_apply_apply]
      exact hx y
    · rw [polar_comm, ← polarBilin_apply_apply]
      exact hy x
  refine false_of_orthogonalGroup hna hnd' (φ.trans ((T.subgroupMap _).trans
    (MulEquiv.subgroupCongr hH))) (d := d) hv ?_
  change T (φ d : GL (Fin (2 * m)) (ZMod 2)) = _
  rw [hdv, toLinEquiv_orthTransvectionGL]

variable {Y : Type*} [Group Y]

theorem isSubnormal_trans {A B C : Subgroup X} (h1 : IsSubnormal A B) (h2 : IsSubnormal B C) :
    IsSubnormal A C :=
  h1.trans h2

theorem isSubnormal_map (f : X →* Y) {A B : Subgroup X} (h : IsSubnormal A B) :
    IsSubnormal (A.map f) (B.map f) :=
  h.map f

theorem isQuasisimple_map (f : X →* Y) (hf : Function.Injective f) {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple K) : CFSG.Open.IsQuasisimple (K.map f) := by
  set e : K ≃* K.map f := K.equivMapOfInjective f hf
  obtain ⟨hp, hs⟩ := hK
  have hc : (Subgroup.center K).map (e : K →* K.map f) = Subgroup.center (K.map f) :=
    Subgroup.map_center_eq e
  let e' := QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : K →* K.map f) e.surjective,
    ← Subgroup.map_commutator, hp]

end AS35K

end CFSG.LargeExtraspecial
