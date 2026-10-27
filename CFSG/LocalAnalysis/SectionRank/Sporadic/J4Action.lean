module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.J3.F2Spec
public import Certificates.Data.CFSGNative.SectionRank.J4Local
public meta import Certificates.Data.CFSGNative.SectionRank.J4Local
public meta import Certificates.Data.CFSGNative.J3.Basic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4ActionInputs
public import Certificates.Certificate8023
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.SectionRank.J4Order

open CFSG.Blueprint CFSG.SectionRank.LocalWitness CFSG.Sporadic.J3 CFSG.Sporadic.J3.Native
  CFSG.SectionRank.Native
open scoped Matrix

abbrev G : Type := NativeSporadic.J4

abbrev S : Submonoid (Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  NativeSporadic.seedMonoid 2 112 1 NativeSporadic.J4Seed1 NativeSporadic.J4Seed2

noncomputable abbrev ν : G →* Matrix (Fin 112) (Fin 112) (ZMod 2) := valHom S

theorem ν_injective : Function.Injective ν := valHom_injective S

theorem ν_mem (g : G) : ν g ∈ S := ((g : Sˣ) : S).2

noncomputable abbrev mA : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  NativeSporadic.decode 2 112 1 NativeSporadic.J4Seed1

noncomputable abbrev mB : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  NativeSporadic.decode 2 112 1 NativeSporadic.J4Seed2

private theorem seedA_eq : j4Sylow3Data.seedA = NativeSporadic.J4Seed1 := rfl

private theorem seedB_eq : j4Sylow3Data.seedB = NativeSporadic.J4Seed2 := rfl

theorem rowsMatrix_rowsA : rowsMatrix 112 rowsA = mA := by
  rw [rowsMatrix_rowsOfPayload, seedA_eq]

theorem rowsMatrix_rowsB : rowsMatrix 112 rowsB = mB := by
  rw [rowsMatrix_rowsOfPayload, seedB_eq]

theorem powRows_A : powRows 112 rowsA 2 = idRows 112 :=
  Certificates.certificate8023.1

theorem powRows_B : powRows 112 rowsB 4 = idRows 112 :=
  Certificates.certificate8023.2

theorem mA_sq : mA ^ 2 = 1 := by
  have := congrArg (rowsMatrix 112) powRows_A
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsA] at this

theorem mB_pow_four : mB ^ 4 = 1 := by
  have := congrArg (rowsMatrix 112) powRows_B
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsB] at this

theorem mA_mem : mA ∈ S := Submonoid.subset_closure (Set.mem_insert _ _)

theorem mB_mem : mB ∈ S := Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def a :
    G := unitOf S mA_mem two_ne_zero mA_sq

@[expose] noncomputable def b :
    G := unitOf S mB_mem four_ne_zero mB_pow_four

theorem ν_a : ν a = mA := valHom_unitOf S mA_mem two_ne_zero mA_sq

theorem ν_b :
    ν b = mB := valHom_unitOf S mB_mem four_ne_zero mB_pow_four

theorem a_sq : a ^ 2 = 1 := unitOf_pow S mA_mem two_ne_zero mA_sq

theorem b_pow_four :
    b ^ 4 = 1 := unitOf_pow S mB_mem four_ne_zero mB_pow_four

theorem ν_a_inv : ν a⁻¹ = mA := by
  rw [valHom_inv_of_pow S two_ne_zero a_sq, ν_a, pow_one]

theorem ν_b_inv : ν b⁻¹ = mB ^ 3 := by
  rw [valHom_inv_of_pow S four_ne_zero b_pow_four, ν_b]

theorem ν_a_eq :
    ν a = rowsMatrix 112 (rowsOfPayload 112 NativeSporadic.J4Seed1) := by
  rw [ν_a, rowsMatrix_rowsOfPayload]

theorem ν_b_eq :
    ν b = rowsMatrix 112 (rowsOfPayload 112 NativeSporadic.J4Seed2) := by
  rw [ν_b, rowsMatrix_rowsOfPayload]

theorem ν_inv_a : ν a⁻¹ = ν a := by rw [ν_a_inv, ν_a]

theorem ν_inv_b : ν b⁻¹ = ν b ^ 3 := by rw [ν_b_inv, ν_b]

theorem closure_ab : Subgroup.closure ({a, b} : Set G) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hS : S ≤ (Subgroup.closure ({a, b} : Set G)).toSubmonoid.map ν := by
    refine Submonoid.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact ⟨a, Subgroup.subset_closure (Set.mem_insert _ _), ν_a⟩
    · exact ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), ν_b⟩
  obtain ⟨g', hg', he⟩ := hS (ν_mem g)
  rwa [ν_injective he] at hg'

@[expose] noncomputable def letter : ℕ → G
  | 0 => a
  | 1 => b
  | _ => b⁻¹

@[simp] theorem letter_zero : letter 0 = a := rfl

@[simp] theorem letter_one : letter 1 = b := rfl

@[simp] theorem letter_two : letter 2 = b⁻¹ := rfl

theorem letter_mem
    (k : ℕ) : letter k ∈ Subgroup.closure ({a, b} : Set G) := by
  rw [closure_ab]; exact Subgroup.mem_top _

@[expose] def letterRows : ℕ → Array ℕ
  | 0 => rowsA
  | 1 => powRows 112 rowsB 3
  | _ => rowsB

theorem letterRows_zero : letterRows 0 = rowsA := rfl

theorem letterRows_one : letterRows 1 = powRows 112 rowsB 3 := rfl

theorem letterRows_add_two (k : ℕ) : letterRows (k + 2) = rowsB := rfl

theorem letter_add_two (k : ℕ) : letter (k + 2) = b⁻¹ := rfl

@[ext] structure Vec where
  val : Fin 112 → ZMod 2
deriving DecidableEq

theorem Vec.val_injective : Function.Injective Vec.val := fun _ _ => Vec.ext

instance : Finite Vec := Finite.of_injective _ Vec.val_injective

noncomputable instance vecAction : MulAction G Vec where
  smul g w := ⟨w.val ᵥ* ν g⁻¹⟩
  one_smul w := by
    ext1
    show w.val ᵥ* ν 1⁻¹ = w.val
    rw [inv_one, map_one, Matrix.vecMul_one]
  mul_smul g h w := by
    ext1
    show w.val ᵥ* ν (g * h)⁻¹ = (w.val ᵥ* ν h⁻¹) ᵥ* ν g⁻¹
    rw [mul_inv_rev, map_mul, Matrix.vecMul_vecMul]

theorem smul_val (g : G) (w : Vec) : (g • w).val = w.val ᵥ* ν g⁻¹ := rfl

@[expose] def vec (x : ℕ) : Vec := ⟨toVecD 112 x⟩

theorem vec_val (x : ℕ) : (vec x).val = toVecD 112 x := rfl

theorem vec_injective {x y : ℕ} (hx : x < 2 ^ 112) (hy : y < 2 ^ 112) (h : vec x = vec y) :
    x = y :=
  toVecD_injective hx hy (congrArg Vec.val h)

theorem smul_vec (g : G) (x : ℕ) {R : Array ℕ} (hR : rowsMatrix 112 R = ν g⁻¹) :
    g • vec x = vec (vecMulN 112 R x) := by
  ext1
  rw [smul_val, vec_val, vec_val, ← hR]
  exact (toVecD_vecMulN 112 R x).symm

theorem rowsMatrix_letterRows
    (k : ℕ) : rowsMatrix 112 (letterRows k) = ν (letter k)⁻¹ := by
  match k with
  | 0 => rw [letterRows_zero, letter_zero, rowsMatrix_rowsA, ν_a_inv]
  | 1 => rw [letterRows_one, letter_one, rowsMatrix_powRows, rowsMatrix_rowsB, ν_b_inv]
  | k + 2 => rw [letterRows_add_two, letter_add_two, inv_inv, rowsMatrix_rowsB, ν_b]

theorem letter_smul_vec
    (k x : ℕ) : letter k • vec x = vec (vecMulN 112 (letterRows k) x) :=
  smul_vec _ x (rowsMatrix_letterRows k)

@[expose] def baseBits : ℕ := 0x443b193d248ccde2bb47c46a7f7d

@[expose] def v₀ : Vec := vec baseBits

end CFSG.SectionRank.J4Order
