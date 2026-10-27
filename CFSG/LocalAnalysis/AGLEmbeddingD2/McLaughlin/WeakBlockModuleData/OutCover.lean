module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutAlt
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement

variable {Q : Type*} [Group Q]

theorem mem_centralizer_of_trivial_mod_center {A : Subgroup Q} (hA : ⁅A, A⁆ = A) {c : Q}
    (hc : c ∈ Subgroup.normalizer (A : Set Q))
    (hZ : ∀ x ∈ A, ∀ a ∈ A, a * (c * x * c⁻¹ * x⁻¹) = (c * x * c⁻¹ * x⁻¹) * a) :
    c ∈ Subgroup.centralizer (A : Set Q) := by
  have hmem : ∀ x ∈ A, c * x * c⁻¹ * x⁻¹ ∈ A := fun x hx =>
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hc x).mp hx) (A.inv_mem hx)
  have hmul' : ∀ x ∈ A, ∀ y ∈ A,
      c * (x * y) * c⁻¹ * (x * y)⁻¹ = (c * x * c⁻¹ * x⁻¹) * (c * y * c⁻¹ * y⁻¹) := by
    intro x hx y hy
    have hcomm : x * (c * y * c⁻¹ * y⁻¹) = (c * y * c⁻¹ * y⁻¹) * x := hZ y hy x hx
    calc c * (x * y) * c⁻¹ * (x * y)⁻¹
        = (c * x * c⁻¹ * x⁻¹) * (x * (c * y * c⁻¹ * y⁻¹) * x⁻¹) := by group
      _ = (c * x * c⁻¹ * x⁻¹) * (c * y * c⁻¹ * y⁻¹) := by rw [hcomm]; group
  let lam : A →* Q :=
    { toFun := fun x => c * x * c⁻¹ * x⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        simpa using hmul' (x : Q) x.2 (y : Q) y.2 }
  have hlam_comm : ∀ x y : A, lam x * lam y = lam y * lam x := by
    intro x y
    exact hZ y y.2 (lam x) (hmem x x.2)
  have hperf : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hA
  have hle : (⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆) ≤ lam.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hlam_comm x y)
  have htop : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = ⊤ := by
    have := Group.isPerfect_def.mp hperf
    rwa [commutator_def] at this
  rw [htop] at hle
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : lam ⟨x, hx⟩ = 1 := hle (Subgroup.mem_top _)
  have h2 : c * x * c⁻¹ * x⁻¹ = 1 := h1
  calc x * c = (c * x * c⁻¹ * x⁻¹)⁻¹ * (c * x) := by group
    _ = c * x := by rw [h2]; simp

theorem conjOnNormalizer_iterate (A : Subgroup Q) (u : Q)
    (hu : u ∈ Subgroup.normalizer (A : Set Q)) (j : ℕ) (a : A) :
    (((conjOnNormalizer A u hu)^[j] a : A) : Q) = u ^ j * a * (u ^ j)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', conjOnNormalizer_apply, ih]
    simp [pow_succ', mul_assoc]

@[expose] def AutThreePowInner (X : Type*) [Group X] : Prop :=
  ∀ (ψ : X ≃* X) (k : ℕ), (∀ x, ψ^[3 ^ k] x = x) → ∃ a : X, ∀ x, ψ x = a * x * a⁻¹

theorem mem_sup_centralizer_of_three_pow_normalizer_cover {X : Type*} [Group X]
    (hX : AutThreePowInner X) (A : Subgroup Q) (hA : ⁅A, A⁆ = A)
    (e : A ⧸ Subgroup.center A ≃* X) {u : Q} (hu : u ∈ Subgroup.normalizer (A : Set Q))
    {k : ℕ} (huk : u ^ (3 ^ k) = 1) : u ∈ A ⊔ Subgroup.centralizer (A : Set Q) := by
  set ψ0 : A ≃* A := conjOnNormalizer A u hu with hψ0
  have hcen : (Subgroup.center A).map ψ0.toMonoidHom = Subgroup.center A := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_center_iff.mp hw
      refine Subgroup.mem_center_iff.mpr fun a => ?_
      have := hw' (ψ0.symm a)
      have h2 := congrArg ψ0 this
      simpa using h2
    · intro hz
      have hz' := Subgroup.mem_center_iff.mp hz
      refine ⟨ψ0.symm z, Subgroup.mem_center_iff.mpr fun a => ?_, by simp⟩
      have := hz' (ψ0 a)
      have h2 := congrArg ψ0.symm this
      simpa using h2
  set ψ1 : A ⧸ Subgroup.center A ≃* A ⧸ Subgroup.center A :=
    QuotientGroup.congr (Subgroup.center A) (Subgroup.center A) ψ0 hcen with hψ1
  set ψ : X ≃* X := (e.symm.trans ψ1).trans e with hψ
  have hψ1k : ∀ y, ψ1^[3 ^ k] y = y := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    have hit : ∀ j : ℕ, ψ1^[j] (a : A ⧸ Subgroup.center A) =
        ((ψ0^[j] a : A) : A ⧸ Subgroup.center A) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        rfl
    rw [hit]
    congr 1
    apply Subtype.ext
    rw [hψ0, conjOnNormalizer_iterate, huk]
    simp
  have hψk : ∀ x, ψ^[3 ^ k] x = x := by
    intro x
    have hit : ∀ j : ℕ, ψ^[j] x = e (ψ1^[j] (e.symm x)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        simp [hψ]
    rw [hit, hψ1k]
    simp
  obtain ⟨a, ha⟩ := hX ψ k hψk
  obtain ⟨a', ha'⟩ := QuotientGroup.mk_surjective (e.symm a)
  have hz : ∀ x : A, ∃ z : A, z ∈ Subgroup.center A ∧
      ((u * (x : Q) * u⁻¹ : Q)) = (a' : Q) * x * (a' : Q)⁻¹ * z := by
    intro x
    have h1 := ha (e (x : A ⧸ Subgroup.center A))
    have h2 : ψ (e (x : A ⧸ Subgroup.center A)) =
        e ((ψ0 x : A) : A ⧸ Subgroup.center A) := by
      simp [hψ, hψ1]
      rfl
    rw [h2] at h1
    have hae : a = e (a' : A ⧸ Subgroup.center A) := by rw [ha']; simp
    have h3 : ((ψ0 x : A) : A ⧸ Subgroup.center A) =
        ((a' * x * a'⁻¹ : A) : A ⧸ Subgroup.center A) := by
      apply e.injective
      calc e ((ψ0 x : A) : A ⧸ Subgroup.center A) = a * e (x : A ⧸ Subgroup.center A) * a⁻¹ := h1
        _ = e ((a' * x * a'⁻¹ : A) : A ⧸ Subgroup.center A) := by
          rw [hae]; simp [map_mul]
    have h4 := QuotientGroup.eq.mp h3.symm
    refine ⟨(a' * x * a'⁻¹)⁻¹ * ψ0 x, h4, ?_⟩
    have hψx := conjOnNormalizer_apply A u hu x
    simp only [hψ0, Subgroup.coe_mul, Subgroup.coe_inv, hψx]
    group
  have hc : (a' : Q)⁻¹ * u ∈ Subgroup.centralizer (A : Set Q) := by
    refine mem_centralizer_of_trivial_mod_center hA ?_ ?_
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer a'.2)) hu
    · intro x hx b hb
      obtain ⟨z, hzc, hzx⟩ := hz ⟨x, hx⟩
      have hzc' := Subgroup.mem_center_iff.mp hzc
      have : (a' : Q)⁻¹ * u * x * ((a' : Q)⁻¹ * u)⁻¹ * x⁻¹ = (z : Q) := by
        have e1 : (a' : Q)⁻¹ * u * x * ((a' : Q)⁻¹ * u)⁻¹ * x⁻¹ =
            (a' : Q)⁻¹ * (u * x * u⁻¹) * a' * x⁻¹ := by group
        rw [e1]
        simp only at hzx
        rw [hzx]
        have e2 : (a' : Q)⁻¹ * ((a' : Q) * x * (a' : Q)⁻¹ * z) * a' * x⁻¹ =
            x * ((a' : Q)⁻¹ * z * a') * x⁻¹ := by group
        rw [e2]
        have e3 : ((a' : Q)⁻¹ * z * a') = z := by
          have h5 : ((a' : Q) * z) = (z : Q) * a' := congrArg Subtype.val (hzc' a')
          calc (a' : Q)⁻¹ * z * a' = (a' : Q)⁻¹ * ((z : Q) * a') := by group
            _ = (a' : Q)⁻¹ * ((a' : Q) * z) := by rw [h5]
            _ = z := by group
        rw [e3]
        have h6 : (x : Q) * z = (z : Q) * x := congrArg Subtype.val (hzc' ⟨x, hx⟩)
        calc (x : Q) * z * x⁻¹ = ((z : Q) * x) * x⁻¹ := by rw [h6]
          _ = z := by group
      rw [this]
      exact congrArg Subtype.val (hzc' ⟨b, hb⟩)
  have : u = (a' : Q) * ((a' : Q)⁻¹ * u) := by group
  rw [this]
  exact Subgroup.mul_mem_sup a'.2 hc

open Equiv in
theorem autThreePowInner_alt {N : ℕ} (hN : 5 ≤ N) (hN6 : N ≠ 6) :
    AutThreePowInner (alternatingGroup (Fin N)) := by
  intro ψ k hψ
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj N hN hN6
  obtain ⟨σ, hσ⟩ := hbij.2 ψ
  have hψx : ∀ x : alternatingGroup (Fin N),
      ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) = σ * (x : Perm (Fin N)) * σ⁻¹ := by
    intro x
    have := congrArg (fun φ : MulAut (alternatingGroup (Fin N)) =>
      ((φ x : alternatingGroup (Fin N)) : Perm (Fin N))) hσ
    simpa [MulAut.conjNormal_apply] using this.symm
  have hiter : ∀ (j : ℕ) (x : alternatingGroup (Fin N)),
      ((ψ^[j] x : alternatingGroup (Fin N)) : Perm (Fin N)) =
        σ ^ j * (x : Perm (Fin N)) * (σ ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', hψx, ih]
      simp [pow_succ', mul_assoc]
  have hσk : σ ^ (3 ^ k) = 1 := by
    apply hbij.1
    rw [map_one]
    apply MulEquiv.ext
    intro x
    have h := hiter (3 ^ k) x
    rw [hψ x] at h
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    exact h.symm
  have hsign : Perm.sign σ = 1 := by
    have h := congrArg Perm.sign hσk
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by
        have : Odd (3 ^ k) := Odd.pow (by decide)
        rw [this.neg_one_pow]; decide)
  have hσA : σ ∈ alternatingGroup (Fin N) := Perm.mem_alternatingGroup.mpr hsign
  refine ⟨⟨σ, hσA⟩, fun x => ?_⟩
  apply Subtype.ext
  rw [hψx]
  simp

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
