module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.NatSchur
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Nat

open Matrix Multiplicative
open scoped MatrixGroups

abbrev Mg (F : Type*) [Field F] : Type _ := Multiplicative (Matrix (Fin 2) (Fin 2) F)

theorem hom_trivial_of_perfect {Γ M : Type*} [Group Γ] [Group.IsPerfect Γ] [CommGroup M]
    (f : Γ →* M) (g : Γ) : f g = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  have h : (⟨f g, g, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

section Coordinates

variable {V : Type} [CommGroup V] {F : Type} [Field F] {K K' : Subgroup (MulAut V)}

@[expose] def KEquivariant (θ : ↥K ≃* SL(2, F)) (e : V ≃* Mg F) : Prop :=
  ∀ (k : ↥K) (v : V),
    e ((k : MulAut V) v) = ofAdd ((θ k : Matrix (Fin 2) (Fin 2) F) * toAdd (e v))

variable (θ : ↥K ≃* SL(2, F)) (e : V ≃* Mg F)

theorem symm_smul (he : KEquivariant θ e) (s : SL(2, F)) (M : Matrix (Fin 2) (Fin 2) F) :
    e.symm (ofAdd ((s : Matrix (Fin 2) (Fin 2) F) * M)) =
      ((θ.symm s : ↥K) : MulAut V) (e.symm (ofAdd M)) := by
  apply e.injective
  rw [MulEquiv.apply_symm_apply, he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    toAdd_ofAdd]

noncomputable def rmat (g : MulAut V) : Matrix (Fin 2) (Fin 2) F :=
  toAdd (e (g (e.symm (ofAdd 1))))

theorem rmat_spec (he : KEquivariant θ e) {g : MulAut V}
    (hg : ∀ k : ↥K, g * (k : MulAut V) = (k : MulAut V) * g) (v : V) :
    e (g v) = ofAdd (toAdd (e v) * rmat e g) := by
  have hadd : ∀ M N : Matrix (Fin 2) (Fin 2) F,
      toAdd (e (g (e.symm (ofAdd (M + N))))) =
        toAdd (e (g (e.symm (ofAdd M)))) + toAdd (e (g (e.symm (ofAdd N)))) := by
    intro M N
    rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]
  have hequiv : ∀ (s : SL(2, F)) (M : Matrix (Fin 2) (Fin 2) F),
      toAdd (e (g (e.symm (ofAdd ((s : Matrix (Fin 2) (Fin 2) F) * M))))) =
        (s : Matrix (Fin 2) (Fin 2) F) * toAdd (e (g (e.symm (ofAdd M)))) := by
    intro s M
    rw [symm_smul θ e he s M]
    have h1 : g (((θ.symm s : ↥K) : MulAut V) (e.symm (ofAdd M))) =
        ((θ.symm s : ↥K) : MulAut V) (g (e.symm (ofAdd M))) :=
      congrArg (fun φ : MulAut V => φ (e.symm (ofAdd M))) (hg (θ.symm s))
    rw [h1, he, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have key := schur_mat (fun M => toAdd (e (g (e.symm (ofAdd M))))) hadd hequiv (toAdd (e v))
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at key
  rw [rmat, ← key]
  simp

theorem rmat_one : rmat e (1 : MulAut V) = 1 := by
  simp [rmat]

theorem rmat_mul {g₁ : MulAut V}
    (h₁ : ∀ v, e (g₁ v) = ofAdd (toAdd (e v) * rmat e g₁)) (g₂ : MulAut V) :
    rmat e (g₁ * g₂) = rmat e g₂ * rmat e g₁ := by
  have h := h₁ (g₂ (e.symm (ofAdd 1)))
  rw [rmat, MulAut.mul_apply, h, toAdd_ofAdd]
  rfl

theorem exists_rightAction [Finite F] (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hperf : ⁅K', K'⁆ = K') (hcard : Nat.card ↥K' = Nat.card ↥K) (he : KEquivariant θ e) :
    ∃ C : ↥K' ≃* SL(2, F), ∀ (g : ↥K') (v : V),
      e ((g : MulAut V) v) = ofAdd (toAdd (e v) * (C g : Matrix (Fin 2) (Fin 2) F).transpose) := by
  have hgK : ∀ g : ↥K', ∀ k : ↥K, (g : MulAut V) * k = k * g := fun g k =>
    (hcomm k k.2 g g.2).symm
  have hspec : ∀ (g : ↥K') v, e ((g : MulAut V) v) = ofAdd (toAdd (e v) * rmat e g) :=
    fun g v => rmat_spec θ e he (hgK g) v
  let rho : ↥K' →* Matrix (Fin 2) (Fin 2) F :=
    { toFun := fun g => (rmat e g).transpose
      map_one' := by simp [rmat_one]
      map_mul' := fun g h => by
        show (rmat e ((g * h : ↥K') : MulAut V)).transpose =
          (rmat e g).transpose * (rmat e h).transpose
        rw [Subgroup.coe_mul, rmat_mul e (hspec g), Matrix.transpose_mul] }
  have : Group.IsPerfect ↥K' := Subgroup.isPerfect_iff.mpr hperf
  have hdet : ∀ g, (rho g).det = 1 := by
    intro g
    have := hom_trivial_of_perfect ((Matrix.detMonoidHom.comp rho).toHomUnits) g
    simpa using congrArg Units.val this
  let C0 : ↥K' →* SL(2, F) :=
    { toFun := fun g => ⟨rho g, hdet g⟩
      map_one' := Subtype.ext (map_one rho)
      map_mul' := fun g h => Subtype.ext (map_mul rho g h) }
  have hinj : Function.Injective C0 := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : (rmat e g).transpose = 1 := congrArg Subtype.val hg
    have h2 : rmat e g = 1 := by simpa using congrArg Matrix.transpose h1
    apply Subtype.ext
    ext v
    have := hspec g v
    rw [h2, mul_one, ofAdd_toAdd] at this
    exact e.injective this
  have hbij : Function.Bijective C0 :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_congr θ.toEquiv])
  refine ⟨MulEquiv.ofBijective C0 hbij, fun g v => ?_⟩
  have hC : ((MulEquiv.ofBijective C0 hbij g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (rmat e g).transpose := rfl
  rw [hspec, hC, Matrix.transpose_transpose]

theorem mem_of_forall_sub (T : AddSubgroup (Matrix (Fin 2) (Fin 2) F))
    (hT : ∀ (s : SL(2, F)) (N : Matrix (Fin 2) (Fin 2) F),
      (s : Matrix (Fin 2) (Fin 2) F) * N - N ∈ T) (M : Matrix (Fin 2) (Fin 2) F) : M ∈ T := by
  have hu : ∀ (t : F) (N : Matrix (Fin 2) (Fin 2) F), !![1, t; 0, 1] * N - N ∈ T := fun t N =>
    hT ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩ N
  have hl : ∀ (t : F) (N : Matrix (Fin 2) (Fin 2) F), !![1, 0; t, 1] * N - N ∈ T := fun t N =>
    hT ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩ N
  have h11 : (!![M 0 0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ T := by
    convert hu (M 0 0) !![0, 0; 1, 0] using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h12 : (!![0, M 0 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ T := by
    convert hu (M 0 1) !![0, 0; 0, 1] using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h21 : (!![0, 0; M 1 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ T := by
    convert hl (M 1 0) !![1, 0; 0, 0] using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h22 : (!![0, 0; 0, M 1 1] : Matrix (Fin 2) (Fin 2) F) ∈ T := by
    convert hl (M 1 1) !![0, 1; 0, 0] using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hM : M = !![M 0 0, 0; 0, 0] + !![0, M 0 1; 0, 0] + !![0, 0; M 1 0, 0] +
      !![0, 0; 0, M 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hM]
  exact add_mem (add_mem (add_mem h11 h12) h21) h22

end Coordinates

end CFSG.CGT.PushingUpLit.CGT6.Diag.Nat
