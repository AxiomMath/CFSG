module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}

private theorem zmod_two_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

private theorem alt_symm (hB : B.IsAlt) (x y : V) : B x y = B y x :=
  ((by decide : ∀ a : ZMod 2, -a = a) (B x y)).symm.trans (hB.neg_eq x y)

private def tvf (B : LinearMap.BilinForm (ZMod 2) V) (v : V) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (B.flip v).smulRight v

private theorem tvf_apply (v x : V) : tvf B v x = x + B x v • v := rfl

private theorem tvf_invol (hB : B.IsAlt) (v : V) : Function.Involutive (tvf B v) := fun x => by
  have h1 : tvf B v (tvf B v x) = x + (B x v + B x v) • v := by
    simp only [tvf_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hB.self_eq_zero v, mul_zero, add_zero, zero_smul, add_smul, add_assoc]
  rw [h1, zmod_two_add_self, zero_smul, add_zero]

private def transvec (hB : B.IsAlt) (v : V) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofInvolutive (tvf B v) (tvf_invol hB v)

private theorem transvec_apply (hB : B.IsAlt) (v x : V) : transvec hB v x = x + B x v • v := rfl

private theorem transvec_isom (hB : B.IsAlt) (v x y : V) :
    B (transvec hB v x) (transvec hB v y) = B x y := by
  simp only [transvec_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hB.self_eq_zero v, mul_zero, add_zero, alt_symm hB v y]
  generalize B x y = c
  generalize B x v = a
  generalize B y v = b
  revert a b c
  decide

private theorem transvec_comm (hB : B.IsAlt) {v v' : V} (h : B v v' = 0) (x : V) :
    transvec hB v (transvec hB v' x) = transvec hB v' (transvec hB v x) := by
  have h' : B v' v = 0 := by rw [alt_symm hB]; exact h
  simp only [transvec_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, h, h', mul_zero, zero_smul, add_zero]
  abel

private theorem transvec_conj (hB : B.IsAlt) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ u w, B (e u) (e w) = B u w) (v x : V) :
    e (transvec hB v (e.symm x)) = transvec hB (e v) x := by
  have h1 : B (e.symm x) v = B x (e v) := by
    rw [← he (e.symm x) v, LinearEquiv.apply_symm_apply]
  simp only [transvec_apply, map_add, map_smul, LinearEquiv.apply_symm_apply, h1]

private theorem exists_ne_transvec (hnd : B.Nondegenerate) (hB : B.IsAlt) {v : V} (hv : v ≠ 0) :
    ∃ x, transvec hB v x ≠ x := by
  by_contra hcon
  have hcon' : ∀ x, transvec hB v x = x := fun x => by
    by_contra h
    exact hcon ⟨x, h⟩
  have hx : ∀ x, B x v = 0 := fun x => by
    have h := hcon' x
    rw [transvec_apply, add_eq_left] at h
    by_contra hne
    have : B x v = 1 := by
      have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact this _ hne
    rw [this, one_smul] at h
    exact hv h
  first
    | exact hv (hnd.1 v fun y => by rw [alt_symm hB]; exact hx y)
    | exact hv (hnd.2 v fun y => by rw [alt_symm hB]; exact hx y)
    | exact hv (hnd.2 v fun y => hx y)
    | exact hv (hnd.1 v fun y => hx y)

variable {G : Type*} [Group G]

theorem exists_centralized_two_group {ψ : G →* (V ≃ₗ[ZMod 2] V)} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hψ : Function.Injective ψ)
    (hrange : ∀ g : V ≃ₗ[ZMod 2] V, (∀ u v, B (g u) (g v) = B u v) → ∃ x, ψ x = g)
    (hiso : ∀ x u v, B (ψ x u) (ψ x v) = B u v) {Bb : Subgroup G} {d : G}
    {I : Submodule (ZMod 2) V} (hI0 : I ≠ ⊥) (hIiso : ∀ u ∈ I, ∀ v ∈ I, B u v = 0)
    (hIb : ∀ b ∈ Bb, ∀ v ∈ I, ψ b v ∈ I) (hId : ∀ v ∈ I, ψ d v = v) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 W ∧ W ≤ Subgroup.centralizer ({d} : Set G) ∧
      Bb ≤ Subgroup.normalizer (W : Set G) := by
  classical
  let S : Set G := {g | ∃ v ∈ I, v ≠ 0 ∧ ψ g = transvec hB v}
  have hsq : ∀ g ∈ S, g * g = 1 := by
    rintro g ⟨v, -, -, hg⟩
    apply hψ
    rw [map_mul, hg, map_one]
    exact LinearEquiv.ext fun x => tvf_invol hB v x
  have hcom : ∀ g ∈ S, ∀ g' ∈ S, g * g' = g' * g := by
    rintro g ⟨v, hv, -, hg⟩ g' ⟨v', hv', -, hg'⟩
    apply hψ
    rw [map_mul, map_mul, hg, hg']
    exact LinearEquiv.ext fun x => transvec_comm hB (hIiso v hv v' hv') x
  have hcen : ∀ g ∈ S, d * g = g * d := by
    rintro g ⟨v, hv, -, hg⟩
    apply hψ
    rw [map_mul, map_mul, hg]
    refine LinearEquiv.ext fun x => ?_
    have h1 : B (ψ d x) v = B x v := by
      have := hiso d x v
      rwa [hId v hv] at this
    simp only [LinearEquiv.mul_apply, transvec_apply, map_add, map_smul, hId v hv, h1]
  have hconj : ∀ b ∈ Bb, ∀ g ∈ S, b * g * b⁻¹ ∈ S := by
    rintro b hb g ⟨v, hv, hv0, hg⟩
    refine ⟨ψ b v, hIb b hb v hv, fun h => hv0 ((ψ b).map_eq_zero_iff.mp h), ?_⟩
    rw [map_mul, map_mul, hg, map_inv]
    exact LinearEquiv.ext fun x => transvec_conj hB (ψ b) (hiso b) v x
  have hcommS : S.Pairwise Commute := fun g hg g' hg' _ => hcom g hg g' hg'
  letI : CommGroup ↥(Subgroup.closure S) := Subgroup.closureCommGroupOfComm hcommS
  have hsqW : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x * x = 1) (fun x hx => hsq x hx) ?_
      (fun x y hx hy ihx ihy => ?_) (fun x _ ihx => ?_) hx
    · simp
    · have hxy : x * y = y * x :=
        congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    · calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ihx, inv_one]
  refine ⟨Subgroup.closure S, ?_, fun x => ⟨1, Subtype.ext ?_⟩, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨g, hg⟩ := hrange (transvec hB v) (transvec_isom hB v)
    intro hbot
    have hg1 : g ∈ Subgroup.closure S := Subgroup.subset_closure ⟨v, hv, hv0, hg⟩
    rw [hbot, Subgroup.mem_bot] at hg1
    obtain ⟨x, hx⟩ := exists_ne_transvec hnd hB hv0
    apply hx
    have := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) (hg.symm.trans (by rw [hg1, map_one]))
    exact this
  · simpa [pow_two] using hsqW x x.2
  · refine (Subgroup.closure_le _).mpr fun g hg => ?_
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hcen g hg
  · intro b hb
    have key : ∀ b ∈ Bb, ∀ h ∈ Subgroup.closure S, b * h * b⁻¹ ∈ Subgroup.closure S := by
      intro b hb h hh
      refine Subgroup.closure_induction (p := fun h _ => b * h * b⁻¹ ∈ Subgroup.closure S)
        (fun g hg => Subgroup.subset_closure (hconj b hb g hg)) (by simp)
        (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hh
      · have : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      · have : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ hx
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key b hb h, fun hh => ?_⟩
    have := key b⁻¹ (Subgroup.inv_mem _ hb) _ hh
    simpa [mul_assoc] using this

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
