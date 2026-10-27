module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreOrth

public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.DefChar.Orth

section End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Z : Module.End K V}

theorem inFlag_one_add {E : Module.End K V} (hc : E * Z = Z * E)
    (hb : ∀ x ∈ LinearMap.ker Z, E x ∈ LinearMap.ker Z ⊓ LinearMap.range Z)
    (hw : ∀ x ∈ LinearMap.ker Z ⊓ LinearMap.range Z, E x = 0) : InFlag Z (1 + E) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h := LinearMap.congr_fun hc x
    simp only [Module.End.mul_apply] at h
    simp [h]
  · simpa using hb x hx
  · simp [hw x hx]

theorem inFlag_comm {f : Module.End K V} (hf : InFlag Z f) : f * Z = Z * f :=
  LinearMap.ext fun x => hf.1 x

end End

section Flag

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Γ : Type*} [Group Γ]

@[expose] def flagSub (ρ : Γ →* Module.End K V) (Z : Module.End K V) : Subgroup Γ where
  carrier := {γ | InFlag Z (ρ γ)}
  one_mem' := by
    show InFlag Z (ρ 1)
    rw [map_one]
    exact InFlag.one
  mul_mem' {a b} ha hb := by
    show InFlag Z (ρ (a * b))
    rw [map_mul]
    exact InFlag.mul ha hb
  inv_mem' {a} ha := by
    show InFlag Z (ρ a⁻¹)
    refine InFlag.inv_of_mul ha ?_ ?_
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]

theorem mem_flagSub {ρ : Γ →* Module.End K V} {Z : Module.End K V} {γ : Γ} :
    γ ∈ flagSub ρ Z ↔ InFlag Z (ρ γ) :=
  Iff.rfl

theorem isPGroup_flagSub [Nontrivial V] {p : ℕ} [Fact p.Prime] [CharP K p]
    {ρ : Γ →* Module.End K V} (hρ : Function.Injective ρ) {Z : Module.End K V}
    (hZ : IsNilpotent Z) : IsPGroup p (flagSub ρ Z) := by
  haveI : CharP (Module.End K V) p :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K V)).injective p
  intro ⟨h, hh⟩
  obtain ⟨m, hm⟩ := hZ
  have hnil : IsNilpotent (ρ h - 1) := by
    refine isNilpotent_of_ker (Z := Z) (n := m) hm ?_ ?_
    · have := inFlag_comm (mem_flagSub.1 hh)
      rw [sub_mul, mul_sub, this]; simp
    · intro x hx
      exact InFlag.sq_apply (mem_flagSub.1 hh) hx
  obtain ⟨k, hk⟩ := hnil
  obtain ⟨e, he⟩ := exists_pow_prime_pow_ge (p := p) (m := k) (Fact.out : p.Prime).one_lt
  refine ⟨e, ?_⟩
  have h1 : (ρ h) ^ p ^ e = 1 := pow_prime_pow_eq_one hk he
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply hρ
  rw [map_pow, h1, map_one]

theorem isPGroup_closure_of_subset_map [Nontrivial V] {p : ℕ} [Fact p.Prime] [CharP K p]
    {ρ : Γ →* Module.End K V} (hρ : Function.Injective ρ) {Z : Module.End K V}
    (hZ : IsNilpotent Z) {Y : Type*} [Group Y] (π : Γ →* Y) {M : Set Y}
    (hM : M ⊆ (flagSub ρ Z).map π) : IsPGroup p (Subgroup.closure M) :=
  ((isPGroup_flagSub hρ hZ).map π).to_le ((Subgroup.closure_le _).2 hM)

end Flag

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem toLin'_mul_eq (A B : Matrix ι ι K) :
    Matrix.toLin' A * Matrix.toLin' B = Matrix.toLin' (A * B) := by
  rw [Matrix.toLin'_mul, Module.End.mul_eq_comp]

variable (ι K) in
@[expose] def glRep : GL ι K →* Module.End K (ι → K) where
  toFun s := Matrix.toLin' (s : Matrix ι ι K)
  map_one' := by
    rw [Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' a b := by
    rw [Units.val_mul, ← toLin'_mul_eq]

theorem glRep_injective : Function.Injective (glRep ι K) := fun a b h =>
  Units.ext (Matrix.toLin'.injective h)

theorem isNilpotent_toLin' {N : Matrix ι ι K} (hN : IsNilpotent N) :
    IsNilpotent (Matrix.toLin' N) := by
  obtain ⟨m, hm⟩ := hN
  exact ⟨m, by rw [← Matrix.toLin'_pow, hm]; exact map_zero _⟩

end Mat

end CFSG.HardMathSupport.Dickson.KD
