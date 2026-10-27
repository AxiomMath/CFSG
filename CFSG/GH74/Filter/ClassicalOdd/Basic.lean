module

public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowBasic

public section

namespace CFSG.GH74.Filter.ClassicalOdd

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem not_gen4_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {H : Subgroup (GL ι F)} {K A : Type*} [Group K] [Finite K] [Group A]
    (α : K →* GL ι F) (hα : ∀ k, α k ∈ H) (β : K →* A) (hβ : Function.Surjective β)
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1)
    (hcard : 2 ^ 4 < Nat.card A)
    (hscal : ∀ (k : K) (c : F), (α k : Matrix ι ι F) = scalar ι c → β k = 1) :
    ¬ Gen4 (StatedProj H) := by
  refine not_gen4_of_surjection
    ((QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)).comp (α.codRestrict H hα)) β hβ hcomm
    hsq hcard fun k hk => ?_
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hk
  obtain ⟨c, hc⟩ := hk
  refine MonoidHom.mem_ker.2 (hscal k (c : F) ?_)
  rw [← GeneralLinearGroup.coe_scalar, hc]
  rfl

abbrev Q8 : Type := QuaternionGroup 2

abbrev V4 : Type := Multiplicative (ZMod 2 × ZMod 2)

@[expose] def q8Frattini : Q8 →* V4 where
  toFun
    | .a k => Multiplicative.ofAdd ((k.val : ZMod 2), (0 : ZMod 2))
    | .xa k => Multiplicative.ofAdd ((k.val : ZMod 2), (1 : ZMod 2))
  map_one' := by decide
  map_mul' := by decide

theorem q8Frattini_surjective : Function.Surjective q8Frattini := by decide

theorem card_V4 : Nat.card V4 = 4 := by
  simp [Nat.card_eq_fintype_card]

theorem card_V4_cube : Nat.card (V4 × V4 × V4) = 64 := by
  simp [Nat.card_eq_fintype_card]

theorem card_V4_sq_V2 : Nat.card ((V4 × V4) × Multiplicative (ZMod 2)) = 32 := by
  simp [Nat.card_eq_fintype_card]

structure QuatRep (F : Type*) [Field F] where
  ρ : Q8 →* Matrix (Fin 2) (Fin 2) F
  det_eq : ∀ g, (ρ g).det = 1
  scalar_eq : ∀ g c, ρ g = scalar (Fin 2) c → q8Frattini g = 1 ∧ (c = 1 ∨ c = -1)

theorem quatRep_scalar_aux {F : Type*} [Field F] (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F)
    (hinj : Function.Injective ρ) (ha2 : ρ (.a 2) = -1) (g : Q8) (c : F)
    (h : ρ g = scalar (Fin 2) c) : q8Frattini g = 1 ∧ (c = 1 ∨ c = -1) := by
  have hcomm : ∀ x, g * x = x * g := by
    intro x
    apply hinj
    rw [map_mul, map_mul, h]
    exact (scalar_commute c (fun _ => Commute.all _ _) (ρ x)).eq
  rcases quaternion_center g hcomm with rfl | rfl
  · refine ⟨map_one _, Or.inl ?_⟩
    have := congrFun (congrFun h 0) 0
    simpa using this.symm
  · refine ⟨by decide, Or.inr ?_⟩
    rw [ha2] at h
    have := congrFun (congrFun h 0) 0
    simpa using this.symm

@[expose] noncomputable def QuatRep.ofSq {F : Type*} [Field F] (hF : ringChar F ≠ 2) {a b : F}
    (h : a ^ 2 + b ^ 2 = -1) : QuatRep F where
  ρ :=
    { toFun := fun g =>
        ((quatHom h g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      map_one' := by rw [map_one, Matrix.SpecialLinearGroup.coe_one]
      map_mul' := fun g g' => by rw [map_mul, Matrix.SpecialLinearGroup.coe_mul] }
  det_eq g := Matrix.SpecialLinearGroup.det_coe (quatHom h g)
  scalar_eq g c hg := quatRep_scalar_aux _
    (fun g g' hgg' => quatHom_injective hF h (Subtype.ext hgg')) (quatHom_a_two h) g c hg

theorem exists_quatRep {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    Nonempty (QuatRep F) := by
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hF).1
  exact ⟨QuatRep.ofSq hF h⟩

section Block

variable {F : Type*} [Field F] {k m : ℕ}

theorem diagBlock_apply_inl (X : Matrix (Fin k) (Fin k) F) (Y : Matrix (Fin m) (Fin m) F)
    (i j : Fin k) :
    diagBlock X Y (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = X i j := by
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₁₁]

theorem diagBlock_apply_inr (X : Matrix (Fin k) (Fin k) F) (Y : Matrix (Fin m) (Fin m) F)
    (i j : Fin m) :
    diagBlock X Y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = Y i j := by
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₂₂]

theorem det_diagBlock (X : Matrix (Fin k) (Fin k) F) (Y : Matrix (Fin m) (Fin m) F) :
    (diagBlock X Y).det = X.det * Y.det := by
  rw [diagBlock, det_reindex_self, det_fromBlocks_zero₁₂]

theorem eq_scalar_of_diagBlock_eq {X : Matrix (Fin k) (Fin k) F} {Y : Matrix (Fin m) (Fin m) F}
    {c : F} (h : diagBlock X Y = scalar (Fin (k + m)) c) :
    X = scalar (Fin k) c ∧ Y = scalar (Fin m) c := by
  constructor
  · ext i j
    have := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) (finSumFinEquiv (Sum.inl j))
    rw [diagBlock_apply_inl, scalar_apply_finSumFinEquiv] at this
    rw [this, scalar_apply, diagonal_apply]
    simp
  · ext i j
    have := congrFun (congrFun h (finSumFinEquiv (Sum.inr i))) (finSumFinEquiv (Sum.inr j))
    rw [diagBlock_apply_inr, scalar_apply_finSumFinEquiv] at this
    rw [this, scalar_apply, diagonal_apply]
    simp

theorem smul_scalar_fin_two (a c : F) :
    a • (scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) F) = scalar (Fin 2) (a * c) := by
  ext i j
  simp [scalar_apply, diagonal_apply]

end Block

@[expose] def zChar {F : Type*} [Field F] (u : Fˣ) (N : ℕ) [NeZero N] (hu : u ^ N = 1) :
    Multiplicative (ZMod N) →* Fˣ where
  toFun k := u ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hu, pow_add]

@[expose] def zRed (N : ℕ) (h : 2 ∣ N) : Multiplicative (ZMod N) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod 2)).toAddMonoidHom

theorem zRed_eq_one_iff (N : ℕ) [NeZero N] (h : 2 ∣ N) (k : Multiplicative (ZMod N)) :
    zRed N h k = 1 ↔ 2 ∣ (Multiplicative.toAdd k).val := by
  change Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) (Multiplicative.toAdd k)) = 1 ↔ _
  rw [ofAdd_eq_one, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

theorem zRed_surjective (N : ℕ) (h : 2 ∣ N) : Function.Surjective (zRed N h) := by
  intro b
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod 2)) (Multiplicative.toAdd b)
  exact ⟨Multiplicative.ofAdd a, congrArg Multiplicative.ofAdd ha⟩

theorem zChar_pow_imp {F : Type*} [Field F] {u : Fˣ} {N m : ℕ} [NeZero N] (hN : N = 2 * m)
    (hm : 0 < m) (hu : orderOf u = N) (hu' : u ^ N = 1) (k : Multiplicative (ZMod N))
    (h : (((zChar u N hu') k : Fˣ) : F) ^ m = 1) : 2 ∣ (Multiplicative.toAdd k).val := by
  have h1 : (zChar u N hu' k) ^ m = 1 := by
    apply Units.val_injective
    simpa using h
  change (u ^ (Multiplicative.toAdd k).val) ^ m = 1 at h1
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one] at h1
  have h2 : orderOf u = 2 * m := hu.trans hN
  rw [h2] at h1
  exact Nat.dvd_of_mul_dvd_mul_right hm h1

theorem exists_units_orderOf {F : Type*} [Field F] [Finite F] {d : ℕ} (hd : d ∣ Nat.card F - 1) :
    ∃ u : Fˣ, orderOf u = d :=
  CFSG.BrauerLinearThree.exists_orderOf_eq_of_dvd_natCard (by rwa [Nat.card_units])

end CFSG.GH74.Filter.ClassicalOdd
