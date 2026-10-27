module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Kron
public import Mathlib.Algebra.DualNumber

public section

open Matrix TrivSqZeroExt DualNumber

namespace CFSG.LieType.SpecialLinear.ExteriorModel

variable {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

@[expose] noncomputable def kronDer (P : ι → Prop) [DecidablePred P] (X : Matrix (Fin n) (Fin n) R) :
    Matrix (KIdx n d) (KIdx n d) R :=
  (kronMinor (R := DualNumber R) (d := d)
    (fun i => if P i then 1 + (ε : DualNumber R) • X.map inl else 1)).map snd

theorem inr_eq_eps_mul_inl {T : Type*} [CommRing T] (x : T) :
    (TrivSqZeroExt.inr x : DualNumber T) = (DualNumber.eps : DualNumber T) * TrivSqZeroExt.inl x := by
  ext <;> simp

theorem map_fst_add_eps_smul_map_snd {T : Type*} [CommRing T] {m : Type*}
    (A : Matrix m m (DualNumber T)) :
    A = (A.map TrivSqZeroExt.fst).map TrivSqZeroExt.inl +
      (DualNumber.eps : DualNumber T) • (A.map TrivSqZeroExt.snd).map TrivSqZeroExt.inl := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  have h := TrivSqZeroExt.inl_fst_add_inr_snd_eq (A i j)
  rw [inr_eq_eps_mul_inl] at h
  exact h.symm

theorem map_fst_eps_smul {T : Type*} [CommRing T] {m : Type*}
    (M : Matrix m m (DualNumber T)) :
    ((DualNumber.eps : DualNumber T) • M).map TrivSqZeroExt.fst = 0 := by
  ext a b
  change TrivSqZeroExt.fst ((DualNumber.eps : DualNumber T) * M a b) = 0
  rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul]

theorem map_snd_eps_smul {T : Type*} [CommRing T] {m : Type*}
    (M : Matrix m m (DualNumber T)) :
    ((DualNumber.eps : DualNumber T) • M).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst := by
  ext a b
  change TrivSqZeroExt.snd ((DualNumber.eps : DualNumber T) * M a b) = TrivSqZeroExt.fst (M a b)
  rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, one_mul, zero_add]

theorem map_fst_map_inl {T : Type*} [CommRing T] {m : Type*} (M : Matrix m m T) :
    (M.map (TrivSqZeroExt.inl : T → DualNumber T)).map TrivSqZeroExt.fst = M := by
  ext a b
  simp only [Matrix.map_apply, TrivSqZeroExt.fst_inl]

theorem map_snd_map_inl {T : Type*} [CommRing T] {m : Type*} (M : Matrix m m T) :
    (M.map (TrivSqZeroExt.inl : T → DualNumber T)).map TrivSqZeroExt.snd = 0 := by
  ext a b
  simp only [Matrix.map_apply, TrivSqZeroExt.snd_inl, Matrix.zero_apply]

theorem map_snd_one {T : Type*} [CommRing T] {m : Type*} [DecidableEq m] :
    ((1 : Matrix m m (DualNumber T)).map TrivSqZeroExt.snd) = 0 := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.map_apply, h]

theorem map_fst_one {T : Type*} [CommRing T] {m : Type*} [DecidableEq m] :
    ((1 : Matrix m m (DualNumber T)).map TrivSqZeroExt.fst) = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.map_apply, Matrix.one_apply, h]

theorem map_snd_one_add_eps_smul_map_inl {T : Type*} [CommRing T] {m : Type*} [DecidableEq m]
    (A : Matrix m m T) :
    ((1 : Matrix m m (DualNumber T)) +
      (DualNumber.eps : DualNumber T) • A.map (TrivSqZeroExt.inl : T → DualNumber T)).map TrivSqZeroExt.snd = A := by
  rw [Matrix.map_add TrivSqZeroExt.snd (fun a b => rfl), map_snd_one, map_snd_eps_smul,
    map_fst_map_inl, zero_add]

theorem map_fst_one_add_eps_smul_map_inl {T : Type*} [CommRing T] {m : Type*} [DecidableEq m]
    (A : Matrix m m T) :
    ((1 : Matrix m m (DualNumber T)) +
      (DualNumber.eps : DualNumber T) • A.map (TrivSqZeroExt.inl : T → DualNumber T)).map TrivSqZeroExt.fst = 1 := by
  rw [Matrix.map_add TrivSqZeroExt.fst (fun a b => rfl), map_fst_one, map_fst_eps_smul,
    add_zero]

omit [DecidableEq ι] in
theorem kronMinor_eq_one_add_eps_smul_map_snd {T : Type*} [CommRing T]
    (G : ι → Matrix (Fin n) (Fin n) (DualNumber T))
    (hG : ∀ i, (G i).map TrivSqZeroExt.fst = 1) :
    kronMinor (d := d) G =
      1 + (DualNumber.eps : DualNumber T) •
        ((kronMinor (d := d) G).map TrivSqZeroExt.snd).map TrivSqZeroExt.inl := by
  have hfst : (kronMinor (d := d) G).map (⇑(TrivSqZeroExt.fstHom T T T).toRingHom) = 1 := by
    rw [← kronMinor_map (d := d) (φ := (TrivSqZeroExt.fstHom T T T).toRingHom) G]
    change kronMinor (d := d) (fun i => (G i).map TrivSqZeroExt.fst) = 1
    simp only [hG]
    exact kronMinor_one (d := d)
  have hfst' : (kronMinor (d := d) G).map TrivSqZeroExt.fst = 1 := by
    change (kronMinor (d := d) G).map (⇑(TrivSqZeroExt.fstHom T T T).toRingHom) = 1
    exact hfst
  refine Eq.trans (map_fst_add_eps_smul_map_snd (A := kronMinor (d := d) G)) ?_
  rw [hfst', Matrix.map_one TrivSqZeroExt.inl (by simp) (by simp)]

omit [DecidableEq ι] in
theorem kronMinor_one_add_eps_smul (P : ι → Prop) [DecidablePred P]
    (X : Matrix (Fin n) (Fin n) R) :
    kronMinor (d := d) (fun i => if P i then
        1 + (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) =
      1 + (ε : DualNumber R) • (kronDer (d := d) P X).map inl := by
  have h := kronMinor_eq_one_add_eps_smul_map_snd (d := d) (T := R)
    (fun i => if P i then
      1 + (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) ?_
  · simpa only [kronDer] using h
  · intro i
    by_cases hP : P i
    · rw [if_pos hP]
      exact map_fst_one_add_eps_smul_map_inl (m := Fin n) (T := R) X
    · rw [if_neg hP, Matrix.map_one TrivSqZeroExt.fst (by simp) (by simp)]

noncomputable def dualLiftAlgHom {S : Type*} [CommRing S] [Algebra R S] {η : S}
    (hη : η * η = 0) : DualNumber R →ₐ[R] S :=
  DualNumber.lift ⟨(Algebra.ofId R S, η), hη, fun _ => Commute.all _ _⟩

@[simp] theorem dualLiftAlgHom_apply_eps {S : Type*} [CommRing S] [Algebra R S] {η : S}
    (hη : η * η = 0) : dualLiftAlgHom (R := R) hη (DualNumber.eps) = η := by
  rw [dualLiftAlgHom, DualNumber.lift_apply_eps]

@[simp] theorem dualLiftAlgHom_apply_inl {S : Type*} [CommRing S] [Algebra R S] {η : S}
    (hη : η * η = 0) (r : R) :
    dualLiftAlgHom (R := R) hη (TrivSqZeroExt.inl r) = algebraMap R S r := by
  rw [dualLiftAlgHom, DualNumber.lift_apply_inl, Algebra.ofId_apply]

omit [DecidableEq ι] in
theorem kronMinor_one_add_nilsq {S : Type*} [CommRing S] [Algebra R S] {η : S} (hη : η * η = 0)
    (P : ι → Prop) [DecidablePred P] (X : Matrix (Fin n) (Fin n) R) :
    kronMinor (d := d) (fun i => if P i then 1 + η • X.map (algebraMap R S) else 1) =
      1 + η • (kronDer (d := d) P X).map (algebraMap R S) := by
  let G : ι → Matrix (Fin n) (Fin n) (DualNumber R) :=
    fun i => if P i then
      1 + (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1
  let Gη : ι → Matrix (Fin n) (Fin n) S :=
    fun i => if P i then 1 + η • X.map (algebraMap R S) else 1
  have hfam : ∀ i, (G i).map (dualLiftAlgHom hη).toRingHom = Gη i := by
    intro i
    by_cases hP : P i
    · ext a b
      by_cases hab : a = b <;>
        simp [G, Gη, hP, hab, Matrix.smul_apply, map_add, map_mul, dualLiftAlgHom_apply_eps,
          dualLiftAlgHom_apply_inl]
    · simp [G, Gη, hP]
  have h1 : kronMinor (d := d) Gη = (kronMinor (d := d) G).map (dualLiftAlgHom hη).toRingHom := by
    rw [← kronMinor_map (d := d) (φ := (dualLiftAlgHom hη).toRingHom) G]
    congr 1
    funext i
    exact (hfam i).symm
  change kronMinor (d := d) Gη = 1 + η • (kronDer (d := d) P X).map (algebraMap R S)
  rw [h1, kronMinor_one_add_eps_smul]
  ext a b
  by_cases hab : a = b <;>
    simp [hab, Matrix.smul_apply, map_add, map_mul, dualLiftAlgHom_apply_eps,
      dualLiftAlgHom_apply_inl]

theorem one_add_smul_mul_one_sub_smul {T : Type*} [CommRing T] {m : Type*} [Fintype m]
    [DecidableEq m] {a : T} (ha : a * a = 0) (A : Matrix m m T) :
    (1 + a • A) * (1 - a • A) = 1 := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ha, zero_smul, sub_zero, sub_add_cancel]

theorem one_add_smul_mul_mul_one_sub_smul {T : Type*} [CommRing T] {m : Type*} [Fintype m]
    [DecidableEq m] {a : T} (ha : a * a = 0) (A B : Matrix m m T) :
    (1 + a • A) * B * (1 - a • A) = B + a • (A * B - B * A) := by
  have h1 : (1 + a • A) * B = B + a • (A * B) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have h2 : (B + a • (A * B)) * (a • A) = a • (B * A) := by
    rw [Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha,
      zero_smul, add_zero]
  rw [h1, Matrix.mul_sub, Matrix.mul_one, h2, smul_sub]
  abel

theorem one_add_smul_mul_one_add_smul {T : Type*} [CommRing T] {m : Type*} [Fintype m]
    [DecidableEq m] {a : T} (ha : a * a = 0) (A B : Matrix m m T) :
    (1 + a • A) * (1 + a • B) = 1 + a • (A + B) := by
  have h : (a • A) * (a • B) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha, zero_smul]
  have h1 : (1 + a • A) * (1 + a • B) = (1 + a • B) + ((a • A) + (a • A) * (a • B)) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
  rw [h1, h, add_zero, smul_add]
  abel

theorem one_add_smul_group_commutator {T : Type*} [CommRing T] {m : Type*} [Fintype m] [DecidableEq m]
    {e₁ e₂ : T} (h₁ : e₁ * e₁ = 0) (h₂ : e₂ * e₂ = 0) (A B : Matrix m m T) :
    (1 + e₁ • A) * (1 + e₂ • B) * (1 - e₁ • A) * (1 - e₂ • B) =
      1 + (e₁ * e₂) • (A * B - B * A) := by
  have hstep : (1 + e₁ • A) * (1 + e₂ • B) * (1 - e₁ • A) =
      1 + e₂ • B + (e₁ * e₂) • (A * B - B * A) := by
    rw [one_add_smul_mul_mul_one_sub_smul h₁ A (1 + e₂ • B)]
    have h2 : A * (1 + e₂ • B) - (1 + e₂ • B) * A = e₂ • (A * B - B * A) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.mul_smul,
        Matrix.smul_mul]
      rw [smul_sub]
      abel
    rw [h2, smul_smul]
  have hXZ : (e₂ • B) * (e₂ • B) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h₂, zero_smul]
  have hYZ : ((e₁ * e₂) • (A * B - B * A)) * (e₂ • B) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc, h₂, mul_zero, zero_smul]
  rw [hstep, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.mul_one, Matrix.mul_one, hXZ, hYZ, sub_zero, sub_zero]
  abel

omit [DecidableEq ι] in
theorem kronDer_eq_zero_of_forall_not {P : ι → Prop} [DecidablePred P]
    (hP : ∀ i, ¬ P i) (X : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) P X = 0 := by
  rw [kronDer]
  have hfam : (fun i => if P i then
      1 + (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) =
      fun _ => (1 : Matrix (Fin n) (Fin n) (DualNumber R)) := by
    funext i
    rw [if_neg (hP i)]
  rw [hfam, kronMinor_one]
  ext a b
  by_cases hab : a = b <;> simp [hab]

omit [Fintype ι] [DecidableEq ι] in
theorem eq_of_one_add_eps_smul_map_inl_eq {T : Type*} [CommRing T] [DecidableEq (KIdx n d)]
    {A B : Matrix (KIdx n d) (KIdx n d) T}
    (h : ((1 : Matrix (KIdx n d) (KIdx n d) (DualNumber T)) +
        (DualNumber.eps : DualNumber T) • A.map (TrivSqZeroExt.inl : T → DualNumber T)) =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber T)) +
        (DualNumber.eps : DualNumber T) • B.map (TrivSqZeroExt.inl : T → DualNumber T)) :
    A = B := by
  have h' := congrArg (fun M => M.map TrivSqZeroExt.snd) h
  simpa only [map_snd_one_add_eps_smul_map_inl] using h'

theorem kronDer_add (P : ι → Prop) [DecidablePred P] (X Y : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) P (X + Y) = kronDer P X + kronDer P Y := by
  have hsum : (kronDer P X).map (inl : R → DualNumber R) +
      (kronDer P Y).map (inl : R → DualNumber R) =
      (kronDer P X + kronDer P Y).map (inl : R → DualNumber R) :=
    (Matrix.map_add (fun x : R => (TrivSqZeroExt.inl x : DualNumber R))
      (fun a b => by simp) (kronDer (d := d) P X) (kronDer (d := d) P Y)).symm
  have h1a : kronMinor (d := d) (fun i => if P i then
      (1 : Matrix (Fin n) (Fin n) (DualNumber R)) + (ε : DualNumber R) •
        ((X + Y).map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) + (ε : DualNumber R) •
        ((kronDer P X).map (inl : R → DualNumber R) +
          (kronDer P Y).map (inl : R → DualNumber R)) := by
    calc kronMinor (d := d) (fun i => if P i then
          (1 : Matrix (Fin n) (Fin n) (DualNumber R)) + (ε : DualNumber R) •
            ((X + Y).map inl : Matrix (Fin n) (Fin n) (DualNumber R))
          else 1)
        = kronMinor (d := d) (fun i =>
            (if P i then 1 + (ε : DualNumber R) •
              (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) *
            (if P i then 1 + (ε : DualNumber R) •
              (Y.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1)) := by
          congr 1
          funext i
          by_cases hP : P i
          · rw [if_pos hP, if_pos hP, if_pos hP,
              one_add_smul_mul_one_add_smul (DualNumber.eps_mul_eps),
              Matrix.map_add (f := TrivSqZeroExt.inl) (fun a b => by simp)]
          · rw [if_neg hP, if_neg hP, if_neg hP, mul_one]
      _ = kronMinor (d := d) (fun i => if P i then
            1 + (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R))
            else 1) *
          kronMinor (d := d) (fun i => if P i then
            1 + (ε : DualNumber R) • (Y.map inl : Matrix (Fin n) (Fin n) (DualNumber R))
            else 1) := kronMinor_mul _ _
      _ = (1 + (ε : DualNumber R) • (kronDer P X).map inl) *
          (1 + (ε : DualNumber R) • (kronDer P Y).map inl) := by
          rw [kronMinor_one_add_eps_smul, kronMinor_one_add_eps_smul]
      _ = (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) + (ε : DualNumber R) •
          ((kronDer P X).map inl + (kronDer P Y).map inl) :=
          one_add_smul_mul_one_add_smul DualNumber.eps_mul_eps _ _
  have h1 : kronMinor (d := d) (fun i => if P i then
      (1 : Matrix (Fin n) (Fin n) (DualNumber R)) + (ε : DualNumber R) •
        ((X + Y).map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) + (ε : DualNumber R) •
        ((kronDer P X + kronDer P Y).map (inl : R → DualNumber R)) :=
    h1a.trans (congrArg (fun M => (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
      (ε : DualNumber R) • M) hsum)
  exact eq_of_one_add_eps_smul_map_inl_eq
    ((kronMinor_one_add_eps_smul P (X + Y)).symm.trans h1)

theorem eps_mul_inl_smul_map {T : Type*} [CommRing T] {m : Type*} (c : T) (M : Matrix m m T) :
    ((DualNumber.eps : DualNumber T) * TrivSqZeroExt.inl c) •
      (M.map (algebraMap T (DualNumber T))) =
    (DualNumber.eps : DualNumber T) • ((c • M).map (TrivSqZeroExt.inl : T → DualNumber T)) := by
  apply Matrix.ext
  intro a b
  apply TrivSqZeroExt.ext
  · simp [Matrix.map_apply, Matrix.smul_apply]
  · simp [Matrix.map_apply, Matrix.smul_apply, TrivSqZeroExt.snd_mul, mul_assoc,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]

omit [DecidableEq ι] in
theorem kronDer_smul (P : ι → Prop) [DecidablePred P] (c : R) (X : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) P (c • X) = c • kronDer P X := by
  have hη : ((ε : DualNumber R) * TrivSqZeroExt.inl c) *
      ((ε : DualNumber R) * TrivSqZeroExt.inl c) = 0 := by
    calc ((ε : DualNumber R) * TrivSqZeroExt.inl c) * ((ε : DualNumber R) * TrivSqZeroExt.inl c)
        = (ε * ε) * (TrivSqZeroExt.inl c * TrivSqZeroExt.inl c) := by ring
      _ = 0 := by rw [DualNumber.eps_mul_eps, zero_mul]
  have h := kronMinor_one_add_nilsq (d := d) (R := R) hη P X
  have hfam : (fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
      ((ε : DualNumber R) * TrivSqZeroExt.inl c) • (X.map (algebraMap R (DualNumber R))) else 1) =
      fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • ((c • X).map (TrivSqZeroExt.inl : R → DualNumber R)) else 1 := by
    funext i
    by_cases hP : P i
    · rw [if_pos hP, if_pos hP, eps_mul_inl_smul_map]
    · rw [if_neg hP, if_neg hP]
  rw [hfam] at h
  have h2 : (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
      ((ε : DualNumber R) * TrivSqZeroExt.inl c) •
        (kronDer (d := d) P X).map (algebraMap R (DualNumber R)) =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
        (ε : DualNumber R) • ((c • kronDer (d := d) P X).map
          (TrivSqZeroExt.inl : R → DualNumber R)) := by
    rw [eps_mul_inl_smul_map]
  rw [h2] at h
  exact eq_of_one_add_eps_smul_map_inl_eq
    ((kronMinor_one_add_eps_smul P (c • X)).symm.trans h)

omit [DecidableEq ι] in
theorem kronDer_zero (P : ι → Prop) [DecidablePred P] :
    kronDer (d := d) P (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  have h := kronDer_smul (d := d) P (0 : R) (0 : Matrix (Fin n) (Fin n) R)
  simpa using h

@[expose] noncomputable def kronDerLin (P : ι → Prop) [DecidablePred P] :
    Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (KIdx n d) (KIdx n d) R where
  toFun := kronDer P
  map_add' := fun X Y => kronDer_add (d := d) P X Y
  map_smul' := fun c X => kronDer_smul (d := d) P c X

theorem kronDerLin_apply (P : ι → Prop) [DecidablePred P] (X : Matrix (Fin n) (Fin n) R) :
    kronDerLin (d := d) P X = kronDer P X := rfl

omit [DecidableEq ι] in
theorem kronDer_transpose (P : ι → Prop) [DecidablePred P] (X : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) P Xᵀ = (kronDer P X)ᵀ := by
  have htrans : kronMinor (d := d) (fun i =>
      ((if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) :
        Matrix (Fin n) (Fin n) (DualNumber R))ᵀ) =
      (kronMinor (d := d) (fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1))ᵀ :=
    kronMinor_transpose _
  have h1 : kronMinor (d := d) (fun i => if P i then
        (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
          (ε : DualNumber R) • ((Xᵀ).map (inl : R → DualNumber R)) else 1) =
      (kronMinor (d := d) (fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1))ᵀ := by
    rw [← htrans]
    congr 1
    funext i
    by_cases hP : P i
    · rw [if_pos hP, if_pos hP, Matrix.transpose_add, Matrix.transpose_one,
        Matrix.transpose_smul, ← Matrix.transpose_map]
    · simp [hP]
  have h2 : (kronMinor (d := d) (fun i => if P i then
        (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1))ᵀ =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
        (ε : DualNumber R) • ((kronDer P X)ᵀ).map (inl : R → DualNumber R) := by
    rw [kronMinor_one_add_eps_smul, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_smul, ← Matrix.transpose_map]
  have hstd : kronMinor (d := d) (fun i => if P i then
        (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
          (ε : DualNumber R) • ((Xᵀ).map (inl : R → DualNumber R)) else 1) =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
        (ε : DualNumber R) • (kronDer (d := d) P Xᵀ).map (inl : R → DualNumber R) :=
    kronMinor_one_add_eps_smul P Xᵀ
  exact eq_of_one_add_eps_smul_map_inl_eq
    (hstd.symm.trans (h1.trans h2))

@[expose] def dualNumberMap {T U : Type*} [CommRing T] [CommRing U] (φ : T →+* U) :
    DualNumber T →+* DualNumber U where
  toFun x := TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd)
  map_one' := by simp
  map_mul' := by
    intro x y
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_mul, mul_add, TrivSqZeroExt.inl_mul_inl,
        TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.inr_mul_inl, TrivSqZeroExt.inr_mul_inr,
        map_mul, add_zero]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_mul,
        add_mul, mul_add,
        TrivSqZeroExt.inl_mul_inl, TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.inr_mul_inl,
        TrivSqZeroExt.inr_mul_inr, map_add, map_mul, smul_eq_mul, op_smul_eq_mul,
        add_zero, zero_add]
      abel
  map_zero' := by simp
  map_add' := by
    intro x y
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add,
      TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel

@[simp] theorem dualNumberMap_eps {T U : Type*} [CommRing T] [CommRing U] (φ : T →+* U) :
    dualNumberMap φ (DualNumber.eps : DualNumber T) = (DualNumber.eps : DualNumber U) := by
  simp [dualNumberMap]

@[simp] theorem dualNumberMap_inl {T U : Type*} [CommRing T] [CommRing U] (φ : T →+* U) (r : T) :
    dualNumberMap φ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r) := by
  simp [dualNumberMap]

theorem map_dualNumberMap_one_add_eps {T U : Type*} [CommRing T] [CommRing U]
    (φ : T →+* U) (X : Matrix (Fin n) (Fin n) T) (a b : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) (DualNumber T)) +
        (DualNumber.eps : DualNumber T) •
          (X.map (TrivSqZeroExt.inl : T → DualNumber T))).map (dualNumberMap φ) a b =
      ((1 : Matrix (Fin n) (Fin n) (DualNumber U)) +
        (DualNumber.eps : DualNumber U) •
          ((X.map φ).map (TrivSqZeroExt.inl : U → DualNumber U))) a b := by
  by_cases hab : a = b <;>
    simp [hab, Matrix.smul_apply, dualNumberMap, inr_eq_eps_mul_inl,
      -DualNumber.inr_eq_smul_eps]

omit [DecidableEq ι] in
theorem kronDer_map {S : Type*} [CommRing S] (φ : R →+* S) (P : ι → Prop) [DecidablePred P]
    (X : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) P (X.map φ) = (kronDer P X).map φ := by
  have hfam : (fun i => ((if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1)).map
        (⇑(dualNumberMap φ))) =
      fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber S)) + (ε : DualNumber S) •
        ((X.map φ).map inl : Matrix (Fin n) (Fin n) (DualNumber S)) else 1 := by
    funext i
    by_cases hP : P i
    · rw [if_pos hP, if_pos hP]
      apply Matrix.ext
      intro a b
      exact map_dualNumberMap_one_add_eps φ X a b
    · rw [if_neg hP, if_neg hP, Matrix.map_one _ (by simp) (by simp)]
  have h1 : kronMinor (d := d) (fun i => if P i then
        (1 : Matrix (Fin n) (Fin n) (DualNumber S)) + (ε : DualNumber S) •
          ((X.map φ).map inl) else 1) =
      ((1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
        (ε : DualNumber R) • (kronDer P X).map inl).map (⇑(dualNumberMap φ)) := by
    rw [← kronMinor_one_add_eps_smul (d := d) (P := P) (X := X)]
    rw [← kronMinor_map (d := d) (φ := dualNumberMap φ)
      (fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • (X.map inl) else 1)]
    rw [show (fun i => ((if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
        (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1)).map (⇑(dualNumberMap φ)))
        = _ from hfam]
  have h2 : ((1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
        (ε : DualNumber R) • (kronDer P X).map inl).map (⇑(dualNumberMap φ)) =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber S)) + (ε : DualNumber S) •
        ((kronDer P X).map φ).map inl := by
    rw [Matrix.map_add (fun x => dualNumberMap φ x)
      (fun a b => map_add (dualNumberMap φ) a b), Matrix.map_one _ (by simp) (by simp)]
    rw [Matrix.map_smul' (dualNumberMap φ) (DualNumber.eps : DualNumber R) _
      (fun a b => map_mul (dualNumberMap φ) a b)]
    rw [dualNumberMap_eps]
    congr 1
    rw [Matrix.map_map, Matrix.map_map]
    have hfun : (⇑(dualNumberMap φ) ∘ TrivSqZeroExt.inl) = (TrivSqZeroExt.inl ∘ ⇑φ) := by
      funext x
      exact dualNumberMap_inl φ x
    rw [hfun]
  have hstd : kronMinor (d := d) (fun i => if P i then
        (1 : Matrix (Fin n) (Fin n) (DualNumber S)) + (ε : DualNumber S) •
          ((X.map φ).map inl) else 1) =
      (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber S)) +
        (ε : DualNumber S) • (kronDer (d := d) P (X.map φ)).map inl :=
    kronMinor_one_add_eps_smul P (X.map φ)
  exact eq_of_one_add_eps_smul_map_inl_eq
    (hstd.symm.trans (h1.trans h2))

theorem map_inl_one {m : Type*} [Fintype m] [DecidableEq m] :
    ((1 : Matrix m m R).map (TrivSqZeroExt.inl : R → DualNumber R)) = 1 := by
  change ((1 : Matrix m m R).map (⇑(TrivSqZeroExt.inlHom R R))) = (1 : Matrix m m (DualNumber R))
  rw [Matrix.map_one _ (by simp) (by simp)]

theorem map_inl_mul {m : Type*} [Fintype m] (A B : Matrix m m R) :
    ((A * B).map (TrivSqZeroExt.inl : R → DualNumber R)) =
      A.map inl * B.map (TrivSqZeroExt.inl : R → DualNumber R) := by
  change ((A * B).map (⇑(TrivSqZeroExt.inlHom R R))) =
    A.map (⇑(TrivSqZeroExt.inlHom R R)) * B.map (⇑(TrivSqZeroExt.inlHom R R))
  rw [Matrix.map_mul]

omit [DecidableEq ι] in
theorem kronMinor_map_inl (g : ι → Matrix (Fin n) (Fin n) R) :
    kronMinor (d := d) (fun i => (g i).map (TrivSqZeroExt.inl : R → DualNumber R)) =
      (kronMinor (d := d) g).map (TrivSqZeroExt.inl : R → DualNumber R) := by
  change kronMinor (d := d) (fun i => (g i).map (⇑(TrivSqZeroExt.inlHom R R))) =
    (kronMinor (d := d) g).map (⇑(TrivSqZeroExt.inlHom R R))
  exact kronMinor_map (d := d) (TrivSqZeroExt.inlHom R R) g

theorem matrix_mul_smul {T : Type*} [CommRing T] {m : Type*} [Fintype m] (a : T)
    (M N : Matrix m m T) : M * (a • N) = a • (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem matrix_smul_mul {T : Type*} [CommRing T] {m : Type*} [Fintype m] (a : T)
    (M N : Matrix m m T) : (a • M) * N = a • (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem kronMinor_mul_kronDer_mul_kronMinor (P : ι → Prop) [DecidablePred P]
    {g g' : ι → Matrix (Fin n) (Fin n) R} (hgg' : ∀ i, g i * g' i = 1)
    {g₀ g₀' : Matrix (Fin n) (Fin n) R} (hg : ∀ i, P i → g i = g₀) (hg' : ∀ i, P i → g' i = g₀')
    (X : Matrix (Fin n) (Fin n) R) :
    kronMinor (d := d) g * kronDer P X * kronMinor g' = kronDer P (g₀ * X * g₀') := by
  by_cases hP : ∃ i, P i
  · obtain ⟨i₀, hi₀⟩ := hP
    have hg₀ : g₀ * g₀' = 1 := by
      rw [← hg i₀ hi₀, ← hg' i₀ hi₀]
      exact hgg' i₀
    let D : ι → Matrix (Fin n) (Fin n) (DualNumber R) :=
      fun i => if P i then
        1 + (ε : DualNumber R) • (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1
    let G : ι → Matrix (Fin n) (Fin n) (DualNumber R) :=
      fun i => (g i).map inl * D i * (g' i).map inl
    have hGD : G = fun i => if P i then
        1 + (ε : DualNumber R) • ((g₀ * X * g₀').map inl) else 1 := by
      funext i
      by_cases hPi : P i
      · simp only [G, D, hPi, if_true]
        rw [hg i hPi, hg' i hPi]
        calc (g₀.map (TrivSqZeroExt.inl : R → DualNumber R)) *
              (1 + (ε : DualNumber R) • (X.map inl)) * (g₀'.map inl)
            = (g₀.map (TrivSqZeroExt.inl : R → DualNumber R) +
                (ε : DualNumber R) • ((g₀ * X).map (TrivSqZeroExt.inl : R → DualNumber R))) *
                (g₀'.map inl) := by
                rw [Matrix.mul_add, Matrix.mul_one, matrix_mul_smul, ← map_inl_mul]
          _ = g₀.map (TrivSqZeroExt.inl : R → DualNumber R) * (g₀'.map inl) +
                ((ε : DualNumber R) • ((g₀ * X).map (TrivSqZeroExt.inl : R → DualNumber R))) *
                (g₀'.map inl) := Matrix.add_mul _ _ _
          _ = (g₀ * g₀').map (TrivSqZeroExt.inl : R → DualNumber R) +
                (ε : DualNumber R) • (((g₀ * X) * g₀').map
                  (TrivSqZeroExt.inl : R → DualNumber R)) := by
                rw [← map_inl_mul, matrix_smul_mul, ← map_inl_mul]
          _ = 1 + (ε : DualNumber R) • (((g₀ * X) * g₀').map
                (TrivSqZeroExt.inl : R → DualNumber R)) := by
                rw [hg₀, map_inl_one]
      · simp only [G, D, hPi, if_false]
        rw [Matrix.mul_one, ← map_inl_mul, hgg' i, map_inl_one]
    have h2 : kronMinor (d := d) G =
        1 + (ε : DualNumber R) • ((kronDer P (g₀ * X * g₀')).map inl) := by
      rw [hGD]
      exact kronMinor_one_add_eps_smul P (g₀ * X * g₀')
    have hG : kronMinor (d := d) G =
        kronMinor (d := d) (fun i => (g i).map inl * D i) *
          (kronMinor (d := d) g').map inl := by
      rw [show G = fun i => ((g i).map inl * D i) * (g' i).map inl from rfl,
        kronMinor_mul, kronMinor_map_inl]
    have hA : kronMinor (d := d) (fun i => (g i).map inl * D i) =
        (kronMinor (d := d) g).map inl * ((1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
          (ε : DualNumber R) • (kronDer P X).map inl) := by
      rw [kronMinor_mul, kronMinor_map_inl, kronMinor_one_add_eps_smul]
    have hmul : kronMinor (d := d) g * kronMinor (d := d) g' = 1 :=
      kronMinor_mul_eq_one hgg'
    have h3 : kronMinor (d := d) G =
        1 + (ε : DualNumber R) • ((kronMinor g * kronDer P X * kronMinor g').map inl) := by
      rw [hG, hA]
      have hAA : (kronMinor (d := d) g).map inl * (kronMinor (d := d) g').map inl =
          (1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) := by
        rw [← map_inl_mul, hmul, map_inl_one]
      have hstep : ((kronMinor (d := d) g).map inl *
            ((1 : Matrix (KIdx n d) (KIdx n d) (DualNumber R)) +
              (ε : DualNumber R) • (kronDer P X).map inl)) *
            ((kronMinor (d := d) g').map inl) =
          (kronMinor (d := d) g).map inl * (kronMinor (d := d) g').map inl +
            (ε : DualNumber R) •
              (((kronMinor (d := d) g) * kronDer P X * kronMinor (d := d) g').map inl) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
          matrix_mul_smul, matrix_smul_mul, ← map_inl_mul, ← map_inl_mul, ← map_inl_mul]
      rw [hstep, hAA]
    exact (eq_of_one_add_eps_smul_map_inl_eq (h2.symm.trans h3)).symm
  · simp only [not_exists] at hP
    rw [kronDer_eq_zero_of_forall_not hP X, kronDer_eq_zero_of_forall_not hP (g₀ * X * g₀')]
    simp

theorem kronDer_or {P Q : ι → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ i, P i → ¬ Q i) (X : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) (fun i => P i ∨ Q i) X = kronDer P X + kronDer Q X := by
  have hsum : (kronDer P X).map (inl : R → DualNumber R) +
      (kronDer Q X).map (inl : R → DualNumber R) =
      (kronDer P X + kronDer Q X).map (inl : R → DualNumber R) :=
    (Matrix.map_add (fun x : R => (TrivSqZeroExt.inl x : DualNumber R))
      (fun a b => by simp) (kronDer (d := d) P X) (kronDer (d := d) Q X)).symm
  have hfam : (fun i => if P i ∨ Q i then
      (1 : Matrix (Fin n) (Fin n) (DualNumber R)) + (ε : DualNumber R) •
        (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) =
      fun i => (if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
          (ε : DualNumber R) • (X.map inl) else 1) *
        (if Q i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
          (ε : DualNumber R) • (X.map inl) else 1) := by
    funext i
    by_cases hP : P i
    · rw [if_pos (Or.inl hP), if_pos hP, if_neg (hPQ i hP), mul_one]
    · by_cases hQ : Q i
      · rw [if_pos (Or.inr hQ), if_neg hP, if_pos hQ, one_mul]
      · rw [if_neg (not_or.mpr ⟨hP, hQ⟩), if_neg hP, if_neg hQ, mul_one]
  have hmain : kronMinor (d := d) (fun i => if P i ∨ Q i then
      (1 : Matrix (Fin n) (Fin n) (DualNumber R)) + (ε : DualNumber R) •
        (X.map inl : Matrix (Fin n) (Fin n) (DualNumber R)) else 1) =
      1 + (ε : DualNumber R) • ((kronDer P X + kronDer Q X).map (inl : R → DualNumber R)) := by
    rw [hfam, kronMinor_mul, kronMinor_one_add_eps_smul, kronMinor_one_add_eps_smul,
      one_add_smul_mul_one_add_smul DualNumber.eps_mul_eps, hsum]
  exact eq_of_one_add_eps_smul_map_inl_eq
    ((kronMinor_one_add_eps_smul (fun i => P i ∨ Q i) X).symm.trans hmain)

theorem inl_eps_mul_self :
    (TrivSqZeroExt.inl (DualNumber.eps : DualNumber R) : DualNumber (DualNumber R)) *
      TrivSqZeroExt.inl (DualNumber.eps : DualNumber R) = 0 := by
  apply TrivSqZeroExt.ext <;>
    simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.snd_inl, DualNumber.eps_mul_eps]

theorem map_snd_snd_one_add_inr_eps_smul {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m (DualNumber (DualNumber R))) :
    (((1 : Matrix m m (DualNumber (DualNumber R))) + (TrivSqZeroExt.inr (DualNumber.eps : DualNumber R) :
        DualNumber (DualNumber R)) • M).map
        (TrivSqZeroExt.snd : DualNumber (DualNumber R) → DualNumber R)).map
        (TrivSqZeroExt.snd : DualNumber R → R) =
      (M.map (TrivSqZeroExt.fst : DualNumber (DualNumber R) → DualNumber R)).map
        (TrivSqZeroExt.fst : DualNumber R → R) := by
  ext a b
  by_cases hab : a = b <;>
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, hab,
      if_true, if_false, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one,
      TrivSqZeroExt.snd_inr,
      TrivSqZeroExt.fst_inr,
      DualNumber.snd_eps, DualNumber.fst_eps, smul_eq_mul,
      op_smul_eq_mul, one_mul, zero_mul, zero_add]

theorem kronDer_mul_sub_mul (P : ι → Prop) [DecidablePred P]
    (X Y : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) P X * kronDer P Y - kronDer P Y * kronDer P X =
      kronDer P (X * Y - Y * X) := by
  let S := DualNumber (DualNumber R)
  let : Algebra R S := TrivSqZeroExt.algebra' R (DualNumber R) (DualNumber R)
  let e₁ : S := TrivSqZeroExt.inl (DualNumber.eps : DualNumber R)
  let e₂ : S := (DualNumber.eps : S)
  have h₁ : e₁ * e₁ = 0 := inl_eps_mul_self (R := R)
  have h₂ : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  have h₁' : (-e₁) * (-e₁) = 0 := by
    rw [show (-e₁) * (-e₁) = e₁ * e₁ by ring, h₁]
  have h₂' : (-e₂) * (-e₂) = 0 := by
    rw [show (-e₂) * (-e₂) = e₂ * e₂ by ring, h₂]
  have he12 : e₁ * e₂ = (TrivSqZeroExt.inr (DualNumber.eps : DualNumber R) : S) := by
    show (TrivSqZeroExt.inl (DualNumber.eps : DualNumber R) : S) * (DualNumber.eps : S) =
      (TrivSqZeroExt.inr (DualNumber.eps : DualNumber R) : S)
    rw [show (DualNumber.eps : S) = TrivSqZeroExt.inr (1 : DualNumber R) from rfl,
      TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]
  have h12 : (e₁ * e₂) * (e₁ * e₂) = 0 := by
    calc (e₁ * e₂) * (e₁ * e₂) = (e₁ * e₁) * (e₂ * e₂) := by ring
      _ = 0 := by rw [h₁, h₂, mul_zero]
  let XS : Matrix (Fin n) (Fin n) S := X.map (algebraMap R S)
  let YS : Matrix (Fin n) (Fin n) S := Y.map (algebraMap R S)
  let G1 : ι → Matrix (Fin n) (Fin n) S := fun i => if P i then 1 + e₁ • XS else 1
  let G2 : ι → Matrix (Fin n) (Fin n) S := fun i => if P i then 1 + e₂ • YS else 1
  let G1' : ι → Matrix (Fin n) (Fin n) S := fun i => if P i then 1 + (-e₁) • XS else 1
  let G2' : ι → Matrix (Fin n) (Fin n) S := fun i => if P i then 1 + (-e₂) • YS else 1
  have hG1 : kronMinor (d := d) G1 = 1 + e₁ • (kronDer P X).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₁ P X
  have hG2 : kronMinor (d := d) G2 = 1 + e₂ • (kronDer P Y).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₂ P Y
  have hG1' : kronMinor (d := d) G1' = 1 + (-e₁) • (kronDer P X).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₁' P X
  have hG2' : kronMinor (d := d) G2' = 1 + (-e₂) • (kronDer P Y).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₂' P Y
  have hfam : (fun i => G1 i * G2 i * G1' i * G2' i) =
      fun i => if P i then 1 + (e₁ * e₂) • ((X * Y - Y * X).map (algebraMap R S)) else 1 := by
    funext i
    by_cases hP : P i
    · rw [if_pos hP]
      simp only [G1, G2, G1', G2', if_pos hP, neg_smul, ← sub_eq_add_neg]
      rw [one_add_smul_group_commutator h₁ h₂ XS YS]
      have hinner : XS * YS - YS * XS = (X * Y - Y * X).map (algebraMap R S) := by
        rw [show XS = X.map (algebraMap R S) from rfl,
          show YS = Y.map (algebraMap R S) from rfl,
          ← Matrix.map_mul, ← Matrix.map_mul]
        exact (Matrix.map_sub _ (map_sub (algebraMap R S)) (X * Y) (Y * X)).symm
      rw [hinner]
    · simp [G1, G2, G1', G2', if_neg hP]
  have hL : kronMinor (d := d) G1 * kronMinor G2 * kronMinor G1' * kronMinor G2' =
      1 + (e₁ * e₂) • ((kronDer P (X * Y - Y * X)).map (algebraMap R S)) := by
    rw [← kronMinor_mul, ← kronMinor_mul, ← kronMinor_mul, hfam]
    exact kronMinor_one_add_nilsq h12 P (X * Y - Y * X)
  have hR : kronMinor (d := d) G1 * kronMinor G2 * kronMinor G1' * kronMinor G2' =
      1 + (e₁ * e₂) • (((kronDer P X * kronDer P Y - kronDer P Y * kronDer P X)).map
        (algebraMap R S)) := by
    rw [hG1, hG2, hG1', hG2']
    rw [show (1 + (-e₁) • (kronDer P X).map (algebraMap R S)) =
        1 - e₁ • (kronDer P X).map (algebraMap R S) by rw [neg_smul, sub_eq_add_neg],
      show (1 + (-e₂) • (kronDer P Y).map (algebraMap R S)) =
        1 - e₂ • (kronDer P Y).map (algebraMap R S) by rw [neg_smul, sub_eq_add_neg]]
    rw [one_add_smul_group_commutator h₁ h₂ ((kronDer (d := d) P X).map (algebraMap R S))
      ((kronDer (d := d) P Y).map (algebraMap R S))]
    have hinner : (kronDer (d := d) P X).map (algebraMap R S) *
          (kronDer (d := d) P Y).map (algebraMap R S) -
          (kronDer (d := d) P Y).map (algebraMap R S) *
            (kronDer (d := d) P X).map (algebraMap R S) =
        (kronDer (d := d) P X * kronDer (d := d) P Y -
          kronDer (d := d) P Y * kronDer (d := d) P X).map (algebraMap R S) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact (Matrix.map_sub _ (map_sub (algebraMap R S)) _ _).symm
    rw [hinner]
  have heq : 1 + (e₁ * e₂) • (((kronDer P X * kronDer P Y - kronDer P Y * kronDer P X)).map
        (algebraMap R S)) =
      1 + (e₁ * e₂) • ((kronDer P (X * Y - Y * X)).map (algebraMap R S)) :=
    hR.symm.trans hL
  rw [he12] at heq
  have hext := congrArg (fun M : Matrix (KIdx n d) (KIdx n d) S =>
      (M.map (TrivSqZeroExt.snd : S → DualNumber R)).map
        (TrivSqZeroExt.snd : DualNumber R → R)) heq
  rw [map_snd_snd_one_add_inr_eps_smul, map_snd_snd_one_add_inr_eps_smul] at hext
  have hL' : ((((kronDer (d := d) P X * kronDer (d := d) P Y - kronDer (d := d) P Y * kronDer (d := d) P X)).map
        (algebraMap R S)).map (TrivSqZeroExt.fst : S → DualNumber R)).map
        (TrivSqZeroExt.fst : DualNumber R → R) =
      kronDer P X * kronDer P Y - kronDer P Y * kronDer P X := by
    rw [Matrix.map_map, Matrix.map_map]
    have hcomp : ((TrivSqZeroExt.fst : DualNumber R → R) ∘
        (TrivSqZeroExt.fst : S → DualNumber R)) ∘ (algebraMap R S) = id := rfl
    rw [hcomp]
    simp
  have hR' : (((kronDer (d := d) P (X * Y - Y * X)).map (algebraMap R S)).map
        (TrivSqZeroExt.fst : S → DualNumber R)).map
        (TrivSqZeroExt.fst : DualNumber R → R) = kronDer (d := d) P (X * Y - Y * X) := by
    rw [Matrix.map_map, Matrix.map_map]
    have hcomp : ((TrivSqZeroExt.fst : DualNumber R → R) ∘
        (TrivSqZeroExt.fst : S → DualNumber R)) ∘ (algebraMap R S) = id := rfl
    rw [hcomp]
    simp
  rw [hL', hR'] at hext
  exact hext

theorem eps_smul_map_inl_single (a b : Fin n) :
    (ε : DualNumber R) • (Matrix.single a b (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R) =
      Matrix.single a b (ε : DualNumber R) := by
  refine Matrix.ext fun x y => ?_
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem one_add_eps_smul_single_self (a : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (DualNumber R)) + (ε : DualNumber R) •
      (Matrix.single a a (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R) =
      Matrix.diagonal (fun x => if x = a then 1 + (ε : DualNumber R) else 1) := by
  rw [eps_smul_map_inl_single]
  refine Matrix.ext fun x y => ?_
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = a
    · subst hx
      simp
    · simp [hx, Ne.symm hx]
  · have h : ¬ (a = x ∧ a = y) := fun h => hxy (h.1.symm.trans h.2)
    simp [hxy, h]

omit [DecidableEq ι] in
theorem kronDer_single_self_apply (P : ι → Prop) [DecidablePred P] (a : Fin n) (s t : KIdx n d) :
    kronDer (d := d) P (Matrix.single a a (1 : R)) s t =
      if s = t then
        ((Finset.univ.filter fun i =>
          P i ∧ a ∈ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n))).card : R)
      else 0 := by
  have hfamily : (fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
      (ε : DualNumber R) • ((Matrix.single a a (1 : R)).map inl) else 1) =
      fun i => Matrix.diagonal (fun x => if P i ∧ x = a then
        (1 + (ε : DualNumber R)) else 1) := by
    funext i
    by_cases hP : P i
    · rw [if_pos hP]
      rw [one_add_eps_smul_single_self]
      congr 1
      funext x
      simp [hP]
    · rw [if_neg hP]
      ext x y <;> (by_cases hxy : x = y <;> simp [Matrix.one_apply,
        hxy, hP, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_zero, TrivSqZeroExt.fst_one,
        TrivSqZeroExt.fst_zero])
  rw [kronDer, hfamily, kronMinor_diagonal]
  by_cases hst : s = t
  · subst hst
    rw [Matrix.map_apply, Matrix.diagonal_apply_eq]
    have hprod : (∏ i, ∏ b ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)),
        (if P i ∧ b = a then (1 + (ε : DualNumber R)) else 1)) =
        (1 + (ε : DualNumber R)) ^ (Finset.univ.filter (fun i => P i ∧
          a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)))).card := by
      have hinner : ∀ i, (∏ b ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)),
          (if P i ∧ b = a then (1 + (ε : DualNumber R)) else 1)) =
          (if P i ∧ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) then
            (1 + (ε : DualNumber R)) else 1) := by
        intro i
        by_cases hP : P i
        · simp only [hP, true_and, Finset.prod_ite_eq']
        · simp [hP]
      rw [Finset.prod_congr rfl fun i _ => hinner i, ← Finset.prod_filter]
      simp [Finset.prod_const]
    rw [hprod]
    rw [TrivSqZeroExt.snd_pow]
    simp
  · rw [Matrix.map_apply, Matrix.diagonal_apply_ne
      (fun s => ∏ i, ∏ a_1 ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)),
        if P i ∧ a_1 = a then 1 + (ε : DualNumber R) else 1) hst]
    simp [hst]

theorem kronDer_mul_comm_of_disjoint {P Q : ι → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ i, P i → ¬ Q i) (X Y : Matrix (Fin n) (Fin n) R) :
    kronDer (d := d) P X * kronDer Q Y = kronDer Q Y * kronDer P X := by
  let S := DualNumber (DualNumber R)
  let : Algebra R S := TrivSqZeroExt.algebra' R (DualNumber R) (DualNumber R)
  let e₁ : S := TrivSqZeroExt.inl (DualNumber.eps : DualNumber R)
  let e₂ : S := (DualNumber.eps : S)
  have h₁ : e₁ * e₁ = 0 := inl_eps_mul_self (R := R)
  have h₂ : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  have h₁' : (-e₁) * (-e₁) = 0 := by rw [show (-e₁) * (-e₁) = e₁ * e₁ by ring, h₁]
  have h₂' : (-e₂) * (-e₂) = 0 := by rw [show (-e₂) * (-e₂) = e₂ * e₂ by ring, h₂]
  have he12 : e₁ * e₂ = (TrivSqZeroExt.inr (DualNumber.eps : DualNumber R) : S) := by
    show (TrivSqZeroExt.inl (DualNumber.eps : DualNumber R) : S) * (DualNumber.eps : S) =
      (TrivSqZeroExt.inr (DualNumber.eps : DualNumber R) : S)
    rw [show (DualNumber.eps : S) = TrivSqZeroExt.inr (1 : DualNumber R) from rfl,
      TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]
  let XS : Matrix (Fin n) (Fin n) S := X.map (algebraMap R S)
  let YS : Matrix (Fin n) (Fin n) S := Y.map (algebraMap R S)
  let G1 : ι → Matrix (Fin n) (Fin n) S := fun i => if P i then 1 + e₁ • XS else 1
  let G2 : ι → Matrix (Fin n) (Fin n) S := fun i => if Q i then 1 + e₂ • YS else 1
  let G1' : ι → Matrix (Fin n) (Fin n) S := fun i => if P i then 1 + (-e₁) • XS else 1
  let G2' : ι → Matrix (Fin n) (Fin n) S := fun i => if Q i then 1 + (-e₂) • YS else 1
  have hG1 : kronMinor (d := d) G1 = 1 + e₁ • (kronDer P X).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₁ P X
  have hG2 : kronMinor (d := d) G2 = 1 + e₂ • (kronDer Q Y).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₂ Q Y
  have hG1' : kronMinor (d := d) G1' = 1 + (-e₁) • (kronDer P X).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₁' P X
  have hG2' : kronMinor (d := d) G2' = 1 + (-e₂) • (kronDer Q Y).map (algebraMap R S) :=
    kronMinor_one_add_nilsq h₂' Q Y
  have hfam : (fun i => G1 i * G2 i * G1' i * G2' i) =
      fun _ => (1 : Matrix (Fin n) (Fin n) S) := by
    funext i
    by_cases hP : P i
    · have hQ : ¬ Q i := hPQ i hP
      simp only [G1, G2, G1', G2', if_pos hP, if_neg hQ, neg_smul, ← sub_eq_add_neg,
        Matrix.mul_one]
      exact one_add_smul_mul_one_sub_smul h₁ XS
    · by_cases hQ : Q i
      · simp only [G1, G2, G1', G2', if_neg hP, if_pos hQ, neg_smul, ← sub_eq_add_neg,
          Matrix.one_mul, Matrix.mul_one]
        exact one_add_smul_mul_one_sub_smul h₂ YS
      · simp [G1, G2, G1', G2', if_neg hP, if_neg hQ]
  have hL : kronMinor (d := d) G1 * kronMinor G2 * kronMinor G1' * kronMinor G2' =
      (1 : Matrix (KIdx n d) (KIdx n d) S) := by
    rw [← kronMinor_mul, ← kronMinor_mul, ← kronMinor_mul, hfam, kronMinor_one]
  have hR : kronMinor (d := d) G1 * kronMinor G2 * kronMinor G1' * kronMinor G2' =
      1 + (e₁ * e₂) • (((kronDer P X * kronDer Q Y - kronDer Q Y * kronDer P X)).map
        (algebraMap R S)) := by
    rw [hG1, hG2, hG1', hG2']
    rw [show (1 + (-e₁) • (kronDer P X).map (algebraMap R S)) =
        1 - e₁ • (kronDer P X).map (algebraMap R S) by rw [neg_smul, sub_eq_add_neg],
      show (1 + (-e₂) • (kronDer Q Y).map (algebraMap R S)) =
        1 - e₂ • (kronDer Q Y).map (algebraMap R S) by rw [neg_smul, sub_eq_add_neg]]
    rw [one_add_smul_group_commutator h₁ h₂ ((kronDer (d := d) P X).map (algebraMap R S))
      ((kronDer (d := d) Q Y).map (algebraMap R S))]
    have hinner : (kronDer (d := d) P X).map (algebraMap R S) *
          (kronDer (d := d) Q Y).map (algebraMap R S) -
          (kronDer (d := d) Q Y).map (algebraMap R S) *
            (kronDer (d := d) P X).map (algebraMap R S) =
        (kronDer (d := d) P X * kronDer (d := d) Q Y -
          kronDer (d := d) Q Y * kronDer (d := d) P X).map (algebraMap R S) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact (Matrix.map_sub _ (map_sub (algebraMap R S)) _ _).symm
    rw [hinner]
  have heq : 1 + (e₁ * e₂) • (((kronDer P X * kronDer Q Y - kronDer Q Y * kronDer P X)).map
        (algebraMap R S)) = 1 := hR.symm.trans hL
  rw [he12] at heq
  have hext := congrArg (fun M : Matrix (KIdx n d) (KIdx n d) S =>
      (M.map (TrivSqZeroExt.snd : S → DualNumber R)).map
        (TrivSqZeroExt.snd : DualNumber R → R)) heq
  rw [map_snd_snd_one_add_inr_eps_smul] at hext
  have hzero : (((1 : Matrix (KIdx n d) (KIdx n d) S)).map
      (TrivSqZeroExt.snd : S → DualNumber R)).map
      (TrivSqZeroExt.snd : DualNumber R → R) = 0 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, hij,
      TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_zero]
  rw [hzero] at hext
  have hL' : ((((kronDer (d := d) P X * kronDer (d := d) Q Y - kronDer (d := d) Q Y * kronDer (d := d) P X)).map
        (algebraMap R S)).map (TrivSqZeroExt.fst : S → DualNumber R)).map
        (TrivSqZeroExt.fst : DualNumber R → R) =
      kronDer P X * kronDer Q Y - kronDer Q Y * kronDer P X := by
    rw [Matrix.map_map, Matrix.map_map]
    have hcomp : ((TrivSqZeroExt.fst : DualNumber R → R) ∘
        (TrivSqZeroExt.fst : S → DualNumber R)) ∘ (algebraMap R S) = id := rfl
    rw [hcomp]
    simp
  rw [hL'] at hext
  exact sub_eq_zero.mp hext

theorem kronDer_mulVec_single_ktop (P : ι → Prop) [DecidablePred P]
    {X : Matrix (Fin n) (Fin n) R} (hX : ∀ a b, b ≤ a → X a b = 0) (hd : ∀ i, d i ≤ n) :
    kronDer (d := d) P X *ᵥ Pi.single (ktop hd) 1 = 0 := by
  let G : ι → Matrix (Fin n) (Fin n) (DualNumber R) :=
    fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
      (ε : DualNumber R) • X.map inl else 1
  have hg : ∀ i a b, b < a → G i a b = 0 := by
    intro i a b hba
    change ((if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
      (ε : DualNumber R) • X.map inl else 1) : Matrix (Fin n) (Fin n) (DualNumber R)) a b = 0
    by_cases hP : P i
    · rw [if_pos hP]
      have hXab : X a b = 0 := hX a b (le_of_lt hba)
      simp [hXab, ne_of_gt hba]
    · rw [if_neg hP]
      simp [ne_of_gt hba]
  have hg1 : ∀ i a, G i a a = 1 := by
    intro i a
    change ((if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
      (ε : DualNumber R) • X.map inl else 1) : Matrix (Fin n) (Fin n) (DualNumber R)) a a = 1
    by_cases hP : P i
    · rw [if_pos hP]
      have hXaa : X a a = 0 := hX a a le_rfl
      simp [hXaa]
    · rw [if_neg hP]
      simp
  have hfix := kronMinor_mulVec_single_ktop (g := G) hg hg1 hd
  have hdecomp : kronMinor (d := d) G = 1 + (ε : DualNumber R) • (kronDer (d := d) P X).map inl :=
    kronMinor_one_add_eps_smul P X
  rw [hdecomp, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hfix
  have hzero : (ε : DualNumber R) •
      (((kronDer (d := d) P X).map (TrivSqZeroExt.inl : R → DualNumber R)) *ᵥ
        Pi.single (ktop hd) 1) = 0 := by
    have h := hfix
    have h' : Pi.single (ktop hd) 1 + (ε : DualNumber R) •
        ((((kronDer (d := d) P X).map (TrivSqZeroExt.inl : R → DualNumber R)) *ᵥ
          Pi.single (ktop hd) 1)) = Pi.single (ktop hd) 1 + 0 := by
      simpa using h
    exact add_left_cancel h'
  funext s
  have hs := congrFun hzero s
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hs
  have h2 := congrArg (fun z => TrivSqZeroExt.snd z) hs
  simp only [TrivSqZeroExt.snd_mul, DualNumber.snd_eps, DualNumber.fst_eps, zero_mul,
    one_mul, zero_add, op_smul_eq_mul, smul_eq_mul, TrivSqZeroExt.snd_zero] at h2
  let vD : KIdx n d → DualNumber R := Pi.single (ktop hd) (1 : DualNumber R)
  let vR : KIdx n d → R := Pi.single (ktop hd) (1 : R)
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at h2 ⊢
  change (∑ i, TrivSqZeroExt.inl (kronDer (d := d) P X s i) * vD i).fst = 0 at h2
  change ∑ i, kronDer (d := d) P X s i * vR i = 0
  have hsum : (∑ i, TrivSqZeroExt.inl (kronDer (d := d) P X s i) * vD i).fst =
      ∑ i, kronDer (d := d) P X s i * vR i := by
    change (TrivSqZeroExt.fstHom R R R).toRingHom
      (∑ i, TrivSqZeroExt.inl (kronDer (d := d) P X s i) * vD i) =
        ∑ i, kronDer (d := d) P X s i * vR i
    rw [map_sum (TrivSqZeroExt.fstHom R R R).toRingHom]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = ktop hd <;>
      simp [vD, vR, hi, TrivSqZeroExt.fst_inl]
  rw [hsum] at h2
  exact h2

theorem fst_prod_eq_prod_fst {T κ : Type*} [CommRing T] (S : Finset κ) (c : κ → DualNumber T) :
    (∏ i ∈ S, c i).fst = ∏ i ∈ S, (c i).fst := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, TrivSqZeroExt.fst_mul, ih]

theorem snd_prod_eq_sum {T κ : Type*} [CommRing T] [DecidableEq κ] (S : Finset κ)
    (c : κ → DualNumber T) :
    (∏ i ∈ S, c i).snd = ∑ i ∈ S, (c i).snd * ∏ j ∈ S.erase i, (c j).fst := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, DualNumber.snd_mul, ih, fst_prod_eq_prod_fst,
      Finset.sum_insert hk, Finset.erase_insert hk, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hki : k ≠ i := by
      rintro rfl
      exact hk hi
    rw [Finset.erase_insert_of_ne hki,
      Finset.prod_insert fun h => hk (Finset.mem_of_mem_erase h)]
    ring

theorem snd_prod_ite_eps {T κ : Type*} [CommRing T] [Fintype κ] [DecidableEq κ]
    (E Q : κ → Prop) [DecidablePred E] [DecidablePred Q] (hQE : ∀ i, Q i → ¬ E i) :
    (∏ i, (if E i then (1 : DualNumber T) else if Q i then ε else 0)).snd =
      if ∃ i, Q i ∧ ∀ j, j ≠ i → E j then 1 else 0 := by
  rw [snd_prod_eq_sum]
  have hfst : ∀ j, (if E j then (1 : DualNumber T) else if Q j then ε else 0).fst =
      if E j then 1 else 0 := by
    intro j
    by_cases hE : E j
    · simp [hE]
    · by_cases hQ : Q j <;> simp [hE, hQ]
  have hsnd : ∀ i, (if E i then (1 : DualNumber T) else if Q i then ε else 0).snd =
      if Q i then 1 else 0 := by
    intro i
    by_cases hE : E i
    · have hQ : ¬ Q i := fun h => hQE i h hE
      simp [hE, hQ]
    · by_cases hQ : Q i <;> simp [hE, hQ]
  simp only [hfst, hsnd]
  by_cases hex : ∃ i, Q i ∧ ∀ j, j ≠ i → E j
  · obtain ⟨i₀, hQ₀, hE₀⟩ := hex
    rw [if_pos ⟨i₀, hQ₀, hE₀⟩, Finset.sum_eq_single i₀]
    · rw [if_pos hQ₀, one_mul]
      exact Finset.prod_eq_one fun j hj => if_pos (hE₀ j (Finset.ne_of_mem_erase hj))
    · intro i _ hi
      rw [if_neg fun h => hQE i h (hE₀ i hi), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  · rw [if_neg hex]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hQ : Q i
    · rw [if_pos hQ, one_mul]
      have hj : ∃ j ∈ Finset.univ.erase i, ¬ E j := by
        by_contra hall
        push Not at hall
        exact hex ⟨i, hQ, fun j hji => hall j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)⟩
      obtain ⟨j, hjmem, hjne⟩ := hj
      exact Finset.prod_eq_zero hjmem (if_neg hjne)
    · rw [if_neg hQ, zero_mul]

theorem kronDer_single_apply (h2 : (2 : R) = 0) (P : ι → Prop) [DecidablePred P] {a b : Fin n}
    (hab : a ≠ b) (s t : KIdx n d) :
    kronDer P (Matrix.single a b (1 : R)) s t =
      if ∃ i, P i ∧ (∀ j, j ≠ i → s j = t j) ∧
          b ∈ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) ∧
          a ∉ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) ∧
          ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) =
            insert a (((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)).erase b)
        then 1 else 0 := by
  have h2' : (2 : DualNumber R) = 0 := by
    rw [← one_add_one_eq_two, ← TrivSqZeroExt.inl_one, ← TrivSqZeroExt.inl_add,
      one_add_one_eq_two, h2, TrivSqZeroExt.inl_zero]
  have hfam : (fun i => if P i then (1 : Matrix (Fin n) (Fin n) (DualNumber R)) +
      (ε : DualNumber R) • (Matrix.single a b (1 : R)).map inl else 1) =
      fun i => 1 + Matrix.single a b (if P i then (ε : DualNumber R) else 0) := by
    funext i
    by_cases hP : P i
    · rw [if_pos hP, if_pos hP, eps_smul_map_inl_single]
    · rw [if_neg hP, if_neg hP, Matrix.single_zero, add_zero]
  rw [kronDer, hfam, Matrix.map_apply, kronMinor_one_add_single h2' hab]
  simp only [← ite_and]
  rw [snd_prod_ite_eps]
  · refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨i, ⟨hC, hP⟩, hE⟩
      exact ⟨i, hP, hE, hC⟩
    · rintro ⟨i, hP, hE, hC⟩
      exact ⟨i, ⟨hC, hP⟩, hE⟩
  · rintro i ⟨⟨_, hat, hst⟩, _⟩ heq
    have has : a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) := by
      rw [hst]
      exact Finset.mem_insert_self _ _
    rw [heq] at has
    exact hat has

end CFSG.LieType.SpecialLinear.ExteriorModel
