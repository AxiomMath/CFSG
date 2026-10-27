module

public import CFSG.LieType.Chevalley.AllRootWeylInfinitesimal

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem baseChange_pinnedCoeff
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (α : Fin τ.rank → ℤ) (k : ℕ) : BaseChange f (pinnedCoeff τ R α k) (pinnedCoeff τ S α k) := by
  have hW := baseChange_prod_reverse_weylElt (τ := τ) f (pinnedData τ α).2.1
  have hx := BaseChange.xCoeff (τ := τ) (f := f) (pinnedData τ α).1 k
  simp only [pinnedCoeff, pinnedWeyl]
  exact ((hW.mul hx).mul (BaseChange.units_inv hW)).intCast_smul _

theorem pow_mul_pow_eq_of_mul_self {a b c : ℤ} (hc : c * c = 1) (k : ℕ) :
    a ^ k * b ^ k = (a * b * c) ^ k * c ^ k := by
  rw [mul_pow (a * b) c, mul_assoc, ← mul_pow c c, hc, one_pow, mul_one, mul_pow]

theorem weylElt_mul_pinnedCoeff_mul_inv_of_type
    (R : Type) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (k : ℕ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * pinnedCoeff τ R α k *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      ((allRootWeylSign τ i α ^ k : ℤ) : R) • pinnedCoeff τ R (reflect τ i α) k := by
  set F := rootOperatorFamily τ
  have hβ : IsRoot τ (reflect τ i α) := IsRoot.reflect i hα
  have hsm : simple τ i • (⟨α, hα⟩ : Root τ) = ⟨reflect τ i α, hβ⟩ :=
    Subtype.ext (simple_smul i α)
  have hss : F.pinnedFamilySign (reflect τ i α) * F.pinnedFamilySign (reflect τ i α) = 1 := by
    rcases F.pinnedFamilySign_eq (reflect τ i α) with h | h <;> rw [h] <;> norm_num
  rw [F.pinnedCoeff_eq_smul_D R hα, mul_smul_comm, smul_mul_assoc, F.weylElt_mul_D_mul_inv, hsm,
    F.pinnedCoeff_eq_smul_D R hβ, smul_smul, smul_smul, allRootWeylSign_eq hα i, ← Int.cast_mul,
    ← Int.cast_mul, pow_mul_pow_eq_of_mul_self hss k]

theorem weylElt_mul_pinnedCoeff_mul_inv
    (R : Type*) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (k : ℕ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * pinnedCoeff τ R α k *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      ((allRootWeylSign τ i α ^ k : ℤ) : R) • pinnedCoeff τ R (reflect τ i α) k := by
  have hZ := weylElt_mul_pinnedCoeff_mul_inv_of_type ℤ i hα k
  rw [Int.cast_id] at hZ
  set f := Int.castRingHom R
  have hL := ((BaseChange.weylElt_one (f := f) i).mul (baseChange_pinnedCoeff f α k)).mul
    (BaseChange.units_inv (BaseChange.weylElt_one (f := f) i))
  have hR := (baseChange_pinnedCoeff (τ := τ) f (reflect τ i α) k).intCast_smul
    (allRootWeylSign τ i α ^ k)
  rw [Int.cast_id, ← hZ] at hR
  exact hL.unique hR

theorem weylElt_one_mul_pinnedX_mul_inv
    (R : Type*) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : R) :
    weylElt τ R i 1 * pinnedX τ R α c * (weylElt τ R i 1)⁻¹ =
      pinnedX τ R (reflect τ i α) ((allRootWeylSign τ i α : R) * c) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, pinnedX_eq_sum, pinnedX_eq_sum, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, weylElt_mul_pinnedCoeff_mul_inv R i hα k, smul_smul, mul_pow,
    Int.cast_pow, mul_comm]

theorem all_root_weyl_conjugation
    (τ : Tag) (R : Type*) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (t : Rˣ) (c : R) :
    weylElt τ R i t * pinnedX τ R α c * (weylElt τ R i t)⁻¹ =
      pinnedX τ R (reflect τ i α)
        ((allRootWeylSign τ i α : R) * ((t ^ (-∑ j, τ.cartan i j * α j) : Rˣ) : R) * c) := by
  have hβ : IsRoot τ (reflect τ i α) := IsRoot.reflect i hα
  rw [← torusElt_mul_weylElt_one τ R i t]
  calc torusElt τ R i t * weylElt τ R i 1 * pinnedX τ R α c *
        (torusElt τ R i t * weylElt τ R i 1)⁻¹ =
      torusElt τ R i t * (weylElt τ R i 1 * pinnedX τ R α c * (weylElt τ R i 1)⁻¹) *
        (torusElt τ R i t)⁻¹ := by group
    _ = torusElt τ R i t * pinnedX τ R (reflect τ i α) ((allRootWeylSign τ i α : R) * c) *
        (torusElt τ R i t)⁻¹ := by rw [weylElt_one_mul_pinnedX_mul_inv R i hα c]
    _ = pinnedX τ R (reflect τ i α) (((t ^ (∑ j, τ.cartan i j * reflect τ i α j) : Rˣ) : R) *
        ((allRootWeylSign τ i α : R) * c)) := root_torus_conjugation i hβ t _
    _ = _ := by
        rw [sum_cartan_mul_reflect]
        congr 1
        ring

end CFSG.LieType.Chevalley
