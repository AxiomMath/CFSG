module

public import CFSG.LieType.Steinberg.Adjoint.Family
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

@[expose] def BaseChange (A : Module.End R (RootModule τ R)) (B : Module.End S (RootModule τ S)) :
    Prop :=
  ∀ b : Label τ, Finsupp.mapRange f f.map_zero (A (Finsupp.single b 1)) = B (Finsupp.single b 1)

theorem mapRange_smul' (r : R) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (r • x) = f r • Finsupp.mapRange f f.map_zero x := by
  ext a
  simp

namespace BaseChange

variable {f}

theorem apply {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (A x) = B (Finsupp.mapRange f f.map_zero x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.mapRange_add (map_add f), hx, hy, Finsupp.mapRange_add (map_add f),
      map_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, mapRange_smul', h b, mapRange_smul', map_smul]
    simp

theorem unique {A : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A B') : B = B' :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [← h b, h' b])

theorem eq_of_injective (hf : Function.Injective f) {A A' : Module.End R (RootModule τ R)}
    {B : Module.End S (RootModule τ S)} (h : BaseChange f A B) (h' : BaseChange f A' B) :
    A = A' :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    exact Finsupp.mapRange_injective f f.map_zero hf ((h b).trans (h' b).symm))

theorem one : BaseChange (τ := τ) f 1 1 := fun b => by simp

theorem zero : BaseChange (τ := τ) f 0 0 := fun b => by simp

theorem mul {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A' B') : BaseChange f (A * A') (B * B') := fun b => by
  rw [Module.End.mul_apply, h.apply, h' b, Module.End.mul_apply]

theorem add {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A' B') : BaseChange f (A + A') (B + B') := fun b => by
  rw [LinearMap.add_apply, Finsupp.mapRange_add (map_add f), h b, h' b, LinearMap.add_apply]

theorem smul {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (r : R) : BaseChange f (r • A) (f r • B) := fun b => by
  rw [LinearMap.smul_apply, mapRange_smul', h b, LinearMap.smul_apply]

theorem intCast_smul {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (n : ℤ) : BaseChange f ((n : R) • A) ((n : S) • B) := by
  have := h.smul (n : R)
  rwa [map_intCast] at this

theorem sum {ι : Type*} (s : Finset ι) {A : ι → Module.End R (RootModule τ R)}
    {B : ι → Module.End S (RootModule τ S)} (h : ∀ i ∈ s, BaseChange f (A i) (B i)) :
    BaseChange f (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (τ := τ) (f := f))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem units_inv {u : (Module.End R (RootModule τ R))ˣ} {v : (Module.End S (RootModule τ S))ˣ}
    (h : BaseChange f (u : Module.End R (RootModule τ R)) (v : Module.End S (RootModule τ S))) :
    BaseChange f ((u⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      ((v⁻¹ : (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := fun b => by
  have hv : Function.Injective (v : Module.End S (RootModule τ S)) := by
    intro x y hxy
    have := congrArg (((v⁻¹ : (Module.End S (RootModule τ S))ˣ) :
      Module.End S (RootModule τ S))) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply, Module.End.one_apply] at this
  apply hv
  rw [← h.apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]
  simp

theorem xCoeff (i : Fin τ.rank) (k : ℕ) : BaseChange f (xCoeff τ R i k) (xCoeff τ S i k) :=
  fun b => mapRange_xCoeff_single f i k b

theorem yCoeff (i : Fin τ.rank) (k : ℕ) : BaseChange f (yCoeff τ R i k) (yCoeff τ S i k) :=
  fun b => mapRange_yCoeff_single f i k b

theorem xOp (i : Fin τ.rank) (c : R) : BaseChange f (xOp τ R i c) (xOp τ S i (f c)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
  refine sum _ fun k _ => ?_
  rw [← map_pow]
  exact (xCoeff i k).smul _

theorem yOp (i : Fin τ.rank) (c : R) : BaseChange f (yOp τ R i c) (yOp τ S i (f c)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
  refine sum _ fun k _ => ?_
  rw [← map_pow]
  exact (yCoeff i k).smul _

theorem weylElt (i : Fin τ.rank) (t : Rˣ) :
    BaseChange f (CFSG.Blueprint.Chevalley.weylElt τ R i t : Module.End R (RootModule τ R))
      (CFSG.Blueprint.Chevalley.weylElt τ S i (Units.map f.toMonoidHom t) :
        Module.End S (RootModule τ S)) := by
  rw [coe_weylElt, coe_weylElt]
  have h1 := xOp (τ := τ) (f := f) i t
  have h2 := yOp (τ := τ) (f := f) i (-((t⁻¹ : Rˣ) : R))
  rw [map_neg] at h2
  exact (h1.mul (by simpa using h2)).mul (by simpa using h1)

theorem weylElt_one (i : Fin τ.rank) :
    BaseChange f (CFSG.Blueprint.Chevalley.weylElt τ R i 1 : Module.End R (RootModule τ R))
      (CFSG.Blueprint.Chevalley.weylElt τ S i 1 : Module.End S (RootModule τ S)) := by
  simpa using weylElt (τ := τ) (f := f) i 1

theorem prod_weylElt (w : List (Fin τ.rank)) :
    BaseChange f
      (((w.map fun i => CFSG.Blueprint.Chevalley.weylElt τ R i 1).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      (((w.map fun i => CFSG.Blueprint.Chevalley.weylElt τ S i 1).prod :
        (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := by
  induction w with
  | nil => simpa using (one (τ := τ) (f := f))
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    exact (weylElt_one i).mul ih

theorem D (F : RootOperatorFamily τ) {R S : Type} [CommRing R] [CommRing S] {f : R →+* S}
    (α : Root τ) (k : ℕ) : BaseChange f (F.D R α k) (F.D S α k) := by
  obtain ⟨j, ε, w, -, h⟩ := RootOperatorFamily'.exists_D_eq_word F α
  rw [h R k, h S k]
  exact ((((prod_weylElt w).mul (xCoeff j k)).mul
    (units_inv (prod_weylElt w))).intCast_smul _)

theorem elt (F : RootOperatorFamily τ) {R S : Type} [CommRing R] [CommRing S] {f : R →+* S}
    (α : Root τ) (c : R) : BaseChange f (F.elt R α c) (F.elt S α (f c)) := by
  simp only [RootOperatorFamily.elt]
  refine sum _ fun k _ => ?_
  rw [← map_pow]
  exact (D F α k).smul _

end BaseChange

end CFSG.LieType.Steinberg.Adjoint
