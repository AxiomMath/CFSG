module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4OutC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProj
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls2Frame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups QuadraticAlgebra

section Theta

variable {F : Type} [Field F]

@[expose] def kaNSΘ (c : F) (Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) :
    Matrix (Fin 4) (Fin 4) F :=
  !![(Z 0 0).re, c * (Z 0 0).im, (Z 0 1).re, c * (Z 0 1).im;
    (Z 0 0).im, (Z 0 0).re, (Z 0 1).im, (Z 0 1).re;
    (Z 1 0).re, c * (Z 1 0).im, (Z 1 1).re, c * (Z 1 1).im;
    (Z 1 0).im, (Z 1 0).re, (Z 1 1).im, (Z 1 1).re]

theorem kaNSΘ_mul (c : F) (Z W : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) :
    kaNSΘ c (Z * W) = kaNSΘ c Z * kaNSΘ c W := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kaNSΘ, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]
  all_goals ring

theorem kaNSΘ_one (c : F) :
    kaNSΘ c (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaNSΘ]

theorem kaNSΘ_smul (c : F) (u : F) (W : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) :
    kaNSΘ c (u • W) = u • kaNSΘ c W := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaNSΘ]
  all_goals ring

theorem kaNSΘ_injective (c : F) : Function.Injective (kaNSΘ c) := by
  intro Z W h
  have e : ∀ i j, kaNSΘ c Z i j = kaNSΘ c W i j := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e10 := e 1 0
  have e02 := e 0 2
  have e12 := e 1 2
  have e20 := e 2 0
  have e30 := e 3 0
  have e22 := e 2 2
  have e32 := e 3 2
  simp [kaNSΘ] at e00 e10 e02 e12 e20 e30 e22 e32
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply QuadraticAlgebra.ext <;> simpa

theorem kaNSΘ_comm (c : F) (Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) :
    kaNSΘ c Z * stdN c = stdN c * kaNSΘ c Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaNSΘ, stdN, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem exists_kaNSΘ_of_comm {c : F} (hc : c ≠ 0) {X : Matrix (Fin 4) (Fin 4) F}
    (h : X * stdN c = stdN c * X) : ∃ Z, kaNSΘ c Z = X := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e03 := congrFun (congrFun h 0) 3
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  have e22 := congrFun (congrFun h 2) 2
  have e23 := congrFun (congrFun h 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, stdN] at e00 e01 e02 e03 e20 e21 e22 e23
  have h11 : X 1 1 = X 0 0 := mul_left_cancel₀ hc (by linear_combination -e01)
  have h13 : X 1 3 = X 0 2 := mul_left_cancel₀ hc (by linear_combination -e03)
  have h31 : X 3 1 = X 2 0 := mul_left_cancel₀ hc (by linear_combination -e21)
  have h33 : X 3 3 = X 2 2 := mul_left_cancel₀ hc (by linear_combination -e23)
  refine ⟨!![⟨X 0 0, X 1 0⟩, ⟨X 0 2, X 1 2⟩; ⟨X 2 0, X 3 0⟩, ⟨X 2 2, X 3 2⟩], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaNSΘ, e00, e02, e20, e22, h11, h13, h31, h33]

end Theta

section Psi

variable {F : Type} [Field F] (c : F)

theorem kaNS_det_eq_one (hperf : Group.IsPerfect SL(2, QuadraticAlgebra F c 0))
    (s : SL(2, QuadraticAlgebra F c 0)) :
    (kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))).det = 1 := by
  let χ0 : SL(2, QuadraticAlgebra F c 0) →* F :=
    { toFun := fun s => (kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))).det
      map_one' := by simp [kaNSΘ_one]
      map_mul' := fun s t => by simp [kaNSΘ_mul, Matrix.det_mul] }
  let χ : SL(2, QuadraticAlgebra F c 0) →* Fˣ := χ0.toHomUnits
  have hker : χ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    simp [commutatorElement_def]
  have h1 : χ s = 1 := by
    have : s ∈ χ.ker := by rw [hker]; trivial
    exact this
  have h2 : (χ s : F) = 1 := by rw [h1]; rfl
  exact h2

theorem kaNS_exists_psi (hperf : Group.IsPerfect SL(2, QuadraticAlgebra F c 0)) :
    ∃ ψ : SL(2, QuadraticAlgebra F c 0) →* SL(4, F), ∀ s : SL(2, QuadraticAlgebra F c 0),
      ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) :=
  ⟨{ toFun := fun s => ⟨kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)),
        kaNS_det_eq_one c hperf s⟩
     map_one' := Subtype.ext (by simp [kaNSΘ_one])
     map_mul' := fun s t => Subtype.ext (by
       show kaNSΘ c ((s * t : SL(2, QuadraticAlgebra F c 0)) :
         Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) = kaNSΘ c s * kaNSΘ c t
       rw [Matrix.SpecialLinearGroup.coe_mul, kaNSΘ_mul]) }, fun s => rfl⟩

end Psi

section Struct

variable {F : Type} [Field F] {c : F}

@[expose] def kaNSt (c : F) : SL(2, QuadraticAlgebra F c 0) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def kaNSs (c : F) : SL(2, QuadraticAlgebra F c 0) :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem kaNS_comm_psi {ψ : SL(2, QuadraticAlgebra F c 0) →* SL(4, F)}
    (hψ : ∀ s : SL(2, QuadraticAlgebra F c 0), ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)))
    (s : SL(2, QuadraticAlgebra F c 0)) :
    ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * stdN c =
      stdN c * ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
  rw [hψ]
  exact kaNSΘ_comm c _

theorem kaNS_lift (hc : c ≠ 0) (E : Subgroup SL(4, F))
    (hE : ∀ g : SL(4, F), g ∈ E ↔
      (g : Matrix (Fin 4) (Fin 4) F) * stdN c = stdN c * (g : Matrix (Fin 4) (Fin 4) F))
    {g : SL(4, F)} (hg : g ∈ E) :
    ∃ Z Z' : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0),
      kaNSΘ c Z = (g : Matrix (Fin 4) (Fin 4) F) ∧
      kaNSΘ c Z' = ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) ∧ Z * Z' = 1 ∧ Z' * Z = 1 := by
  obtain ⟨Z, hZ⟩ := exists_kaNSΘ_of_comm hc ((hE g).1 hg)
  obtain ⟨Z', hZ'⟩ := exists_kaNSΘ_of_comm hc ((hE g⁻¹).1 (E.inv_mem hg))
  refine ⟨Z, Z', hZ, hZ', ?_, ?_⟩
  · apply kaNSΘ_injective c
    rw [kaNSΘ_mul, kaNSΘ_one, hZ, hZ', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  · apply kaNSΘ_injective c
    rw [kaNSΘ_mul, kaNSΘ_one, hZ, hZ', ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]

theorem kaNS_conj_mem (hc : c ≠ 0) (E : Subgroup SL(4, F))
    (hE : ∀ g : SL(4, F), g ∈ E ↔
      (g : Matrix (Fin 4) (Fin 4) F) * stdN c = stdN c * (g : Matrix (Fin 4) (Fin 4) F))
    {ψ : SL(2, QuadraticAlgebra F c 0) →* SL(4, F)}
    (hψ : ∀ s : SL(2, QuadraticAlgebra F c 0), ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)))
    {g : SL(4, F)} (hg : g ∈ E) (s : SL(2, QuadraticAlgebra F c 0)) :
    ∃ s' : SL(2, QuadraticAlgebra F c 0), ψ s' = g * ψ s * g⁻¹ := by
  obtain ⟨Z, Z', hZ, hZ', hZZ', -⟩ := kaNS_lift hc E hE hg
  have hdet : (Z * (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) * Z').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, hZZ', Matrix.det_one]
  refine ⟨⟨Z * (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) * Z', hdet⟩, ?_⟩
  apply Subtype.ext
  have h1 : ((ψ (⟨Z * (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) * Z', hdet⟩ :
      SL(2, QuadraticAlgebra F c 0)) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      kaNSΘ c (Z * (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) * Z') := hψ _
  rw [h1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hψ s, ← hZ,
    ← hZ', kaNSΘ_mul, kaNSΘ_mul]

theorem kaNS_comm_of_smul_comm (h2 : (2 : F) ≠ 0)
    {Z Z' : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)} (hZ : Z * Z' = 1)
    (hZ' : Z' * Z = 1) {W : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)}
    (htr : W.trace = 2) {u : F} (h : W * Z = u • (Z * W)) : W * Z = Z * W := by
  have h1 : W = u • (Z * W * Z') := by
    calc W = W * (Z * Z') := by rw [hZ, Matrix.mul_one]
      _ = (W * Z) * Z' := by rw [Matrix.mul_assoc]
      _ = u • (Z * W * Z') := by rw [h, Matrix.smul_mul]
  have h3 : W.trace = u • W.trace := by
    conv_lhs => rw [h1]
    rw [Matrix.trace_smul]
    congr 1
    calc (Z * W * Z').trace = (Z * (W * Z')).trace := by rw [Matrix.mul_assoc]
      _ = ((W * Z') * Z).trace := Matrix.trace_mul_comm _ _
      _ = W.trace := by rw [Matrix.mul_assoc, hZ', Matrix.mul_one]
  rw [htr] at h3
  have h4 := congrArg QuadraticAlgebra.re h3
  simp at h4
  have h5 : u = 1 := mul_right_cancel₀ h2 (by linear_combination -h4)
  rw [h, h5, one_smul]

theorem kaNS_scalar_of_comm_tv {Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)}
    (ht : (kaNSt c : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) * Z =
      Z * (kaNSt c : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)))
    (hs : (kaNSs c : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) * Z =
      Z * (kaNSs c : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))) :
    Z = Z 0 0 • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) := by
  have t00 := congrFun (congrFun ht 0) 0
  have t01 := congrFun (congrFun ht 0) 1
  have s00 := congrFun (congrFun hs 0) 0
  simp [kaNSt, kaNSs, Matrix.mul_apply, Fin.sum_univ_two] at t00 t01 s00
  have h11 : Z 1 1 = Z 0 0 := by linear_combination t01
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [t00, s00, h11]

theorem kaNS_comm_of_proj_comm (h2 : (2 : F) ≠ 0)
    {ψ : SL(2, QuadraticAlgebra F c 0) →* SL(4, F)}
    (hψ : ∀ s : SL(2, QuadraticAlgebra F c 0), ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)))
    {g : SL(4, F)} {Z Z' : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)}
    (hZ : kaNSΘ c Z = (g : Matrix (Fin 4) (Fin 4) F)) (hZZ' : Z * Z' = 1) (hZ'Z : Z' * Z = 1)
    (w : SL(2, QuadraticAlgebra F c 0))
    (hw : Matrix.trace (w : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) = 2)
    (h : proj 4 F g * proj 4 F (ψ w) = proj 4 F (ψ w) * proj 4 F g) :
    (w : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) * Z =
      Z * (w : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) := by
  rw [← map_mul, ← map_mul] at h
  have hmem := proj_eq_proj_iff.mp h
  generalize hz0 : (g * ψ w)⁻¹ * (ψ w * g) = z at hmem
  have hz : ψ w * g = (g * ψ w) * z := by rw [← hz0]; group
  obtain ⟨u, -, hu⟩ := mem_scalars.mp hmem
  have hmat := congrArg (fun x : SL(4, F) => (x : Matrix (Fin 4) (Fin 4) F)) hz
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hmat
  rw [hu, hψ w, ← hZ, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one, ← kaNSΘ_mul, ← kaNSΘ_mul, ← kaNSΘ_smul] at hmat
  exact kaNS_comm_of_smul_comm h2 hZZ' hZ'Z hw (kaNSΘ_injective c hmat)

theorem kaNS_scalar_of_centralizes (h2 : (2 : F) ≠ 0) (hc : c ≠ 0) (E : Subgroup SL(4, F))
    (hE : ∀ g : SL(4, F), g ∈ E ↔
      (g : Matrix (Fin 4) (Fin 4) F) * stdN c = stdN c * (g : Matrix (Fin 4) (Fin 4) F))
    {ψ : SL(2, QuadraticAlgebra F c 0) →* SL(4, F)}
    (hψ : ∀ s : SL(2, QuadraticAlgebra F c 0), ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)))
    {g : SL(4, F)} (hg : g ∈ E)
    (ht : proj 4 F g * proj 4 F (ψ (kaNSt c)) = proj 4 F (ψ (kaNSt c)) * proj 4 F g)
    (hs : proj 4 F g * proj 4 F (ψ (kaNSs c)) = proj 4 F (ψ (kaNSs c)) * proj 4 F g) :
    ∃ z : QuadraticAlgebra F c 0, (g : Matrix (Fin 4) (Fin 4) F) =
      kaNSΘ c (z • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))) := by
  obtain ⟨Z, Z', hZ, -, hZZ', hZ'Z⟩ := kaNS_lift hc E hE hg
  have htr_t : Matrix.trace (kaNSt c : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) = 2 := by
    simp [kaNSt, Matrix.trace_fin_two, one_add_one_eq_two]
  have htr_s : Matrix.trace (kaNSs c : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) = 2 := by
    simp [kaNSs, Matrix.trace_fin_two, one_add_one_eq_two]
  have hct := kaNS_comm_of_proj_comm h2 hψ hZ hZZ' hZ'Z (kaNSt c) htr_t ht
  have hcs := kaNS_comm_of_proj_comm h2 hψ hZ hZZ' hZ'Z (kaNSs c) htr_s hs
  refine ⟨Z 0 0, ?_⟩
  rw [← hZ]
  exact congrArg (kaNSΘ c) (kaNS_scalar_of_comm_tv hct hcs)

@[expose] def kaNSz (c : F) (M : Matrix (Fin 4) (Fin 4) F) : QuadraticAlgebra F c 0 :=
  ⟨M 0 0, M 1 0⟩

theorem kaNSz_Θ (z : QuadraticAlgebra F c 0) :
    kaNSz c (kaNSΘ c (z • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)))) = z := by
  apply QuadraticAlgebra.ext <;> simp [kaNSz, kaNSΘ]

theorem kaNSz_one : kaNSz c (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  apply QuadraticAlgebra.ext <;> simp [kaNSz]

theorem kaNSΘ_smul_one_mul (z w : QuadraticAlgebra F c 0) :
    kaNSΘ c (z • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))) *
      kaNSΘ c (w • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))) =
      kaNSΘ c ((z * w) • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))) := by
  rw [← kaNSΘ_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul]

theorem kaNS_cyclic [Fact (¬ IsSquare c)] [Finite F] (h2 : (2 : F) ≠ 0) (hc : c ≠ 0)
    (E : Subgroup SL(4, F))
    (hE : ∀ g : SL(4, F), g ∈ E ↔
      (g : Matrix (Fin 4) (Fin 4) F) * stdN c = stdN c * (g : Matrix (Fin 4) (Fin 4) F))
    {ψ : SL(2, QuadraticAlgebra F c 0) →* SL(4, F)}
    (hψ : ∀ s : SL(2, QuadraticAlgebra F c 0), ((ψ s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      kaNSΘ c (s : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)))
    (X : Subgroup (projectiveSL 4 F)) (hXle : X ≤ E.map (proj 4 F))
    (hXc : ∀ x ∈ X, ∀ l ∈ ((proj 4 F).comp ψ).range, x * l = l * x) : IsCyclic ↥X := by
  classical
  let G₀ : Subgroup SL(4, F) := X.comap (proj 4 F) ⊓ E
  have hsc : ∀ g : ↥G₀, ∃ z : QuadraticAlgebra F c 0,
      ((g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        kaNSΘ c (z • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))) := fun g =>
    kaNS_scalar_of_centralizes h2 hc E hE hψ g.2.2 (hXc _ g.2.1 _ ⟨kaNSt c, rfl⟩)
      (hXc _ g.2.1 _ ⟨kaNSs c, rfl⟩)
  let ν : ↥G₀ →* QuadraticAlgebra F c 0 :=
    { toFun := fun g => kaNSz c ((g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
      map_one' := by
        show kaNSz c (((1 : SL(4, F)) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1
        rw [Matrix.SpecialLinearGroup.coe_one, kaNSz_one]
      map_mul' := fun g h => by
        obtain ⟨z, hz⟩ := hsc g
        obtain ⟨w, hw⟩ := hsc h
        have hgh : (((g * h : ↥G₀) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
            kaNSΘ c ((z * w) • (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0))) := by
          rw [← kaNSΘ_smul_one_mul, ← hz, ← hw]
          rfl
        show kaNSz c (((g * h : ↥G₀) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
          kaNSz c ((g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
            kaNSz c ((h : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
        rw [hgh, hz, hw, kaNSz_Θ, kaNSz_Θ, kaNSz_Θ] }
  have hν : Function.Injective ν := by
    intro g h hgh
    obtain ⟨z, hz⟩ := hsc g
    obtain ⟨w, hw⟩ := hsc h
    have hzw : z = w := by
      have := hgh
      change kaNSz c ((g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        kaNSz c ((h : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) at this
      rwa [hz, hw, kaNSz_Θ, kaNSz_Θ] at this
    exact Subtype.ext (Subtype.ext (by rw [hz, hw, hzw]))
  have hcyc : IsCyclic ↥G₀ := isCyclic_of_injective_ringHom ν hν
  let φ : ↥G₀ →* ↥X := ((proj 4 F).comp G₀.subtype).codRestrict X (fun g => g.2.1)
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨e, he, hex⟩ := hXle hx
    exact ⟨⟨e, by rw [Subgroup.mem_inf]; exact ⟨by rw [Subgroup.mem_comap, hex]; exact hx, he⟩⟩,
      Subtype.ext hex⟩
  exact isCyclic_of_surjective φ hφ

@[expose] def kaNSN : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

theorem kaNSN_ne_zero : (kaNSN : Matrix (Fin 4) (Fin 4) F) ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 2
  simp [kaNSN] at this

theorem kaNSN_mul_self : (kaNSN : Matrix (Fin 4) (Fin 4) F) * kaNSN = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaNSN, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def kaNSu (c a : F) : SL(2, QuadraticAlgebra F c 0) :=
  ⟨!![1, ⟨a, 0⟩; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem kaNSΘ_root (c a : F) :
    kaNSΘ c ((kaNSu c a : SL(2, QuadraticAlgebra F c 0)) :
      Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F c 0)) = 1 + a • kaNSN := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [kaNSΘ, kaNSu, kaNSN]

end Struct

section Frame

variable {F : Type} [Field F]

theorem kaNS_stdGL_sq (c : Fˣ) :
    stdGL c * stdGL c = GeneralLinearGroup.scalar (Fin 4) c :=
  Units.ext (by rw [Units.val_mul, coe_stdGL, stdN_mul_stdN, coe_scalar_gl])

theorem kaNS_kaSlCent (c : Fˣ) : kaSlCent (stdGL c) = commSub (c : F) := by
  ext g
  rw [mem_commSub]
  simp only [kaSlCent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · intro h
    have := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) h
    simpa [coe_stdGL] using this.symm
  · intro h
    refine Units.ext ?_
    simpa [coe_stdGL] using h.symm

theorem kaL4NS_frame [Finite F] (hodd : ringChar F ≠ 2) (c : Fˣ) (hc : ¬ IsSquare (c : F)) :
    KAAll (conjAut 4 F (stdGL c)) := by
  have : Fact (¬ IsSquare (c : F)) := ⟨hc⟩
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have : Finite (QuadraticAlgebra F (c : F) 0) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (c : F) 0).symm
  have hFcard : 3 ≤ Nat.card F := by
    have hoddc : Odd (Nat.card F) := by
      have : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)
    have hlt := Finite.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hoddc
    omega
  have hK4 : 4 ≤ Nat.card (QuadraticAlgebra F (c : F) 0) := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd (c : F) 0), Nat.card_prod]
    nlinarith
  have hqs : CFSG.IsQuasisimple SL(2, QuadraticAlgebra F (c : F) 0) :=
    CFSG.ComponentClassification.CatFactsSp4.isQuasisimple_SL2' hK4
  have hperf : Group.IsPerfect SL(2, QuadraticAlgebra F (c : F) 0) := hqs.1
  obtain ⟨ψ, hψ⟩ := kaNS_exists_psi (c : F) hperf
  let E : Subgroup SL(4, F) := commSub (c : F)
  have hE : ∀ g : SL(4, F), g ∈ E ↔ (g : Matrix (Fin 4) (Fin 4) F) * stdN (c : F) =
      stdN (c : F) * (g : Matrix (Fin 4) (Fin 4) F) := fun g => mem_commSub
  let φ : SL(2, QuadraticAlgebra F (c : F) 0) →* projectiveSL 4 F := (proj 4 F).comp ψ
  have hA : stdGL c * stdGL c = GeneralLinearGroup.scalar (Fin 4) c := kaNS_stdGL_sq c
  have hconj : ∀ g ∈ E, ∀ l ∈ φ.range, proj 4 F g * l * (proj 4 F g)⁻¹ ∈ φ.range := by
    intro g hg l hl
    obtain ⟨s, rfl⟩ := hl
    obtain ⟨s', hs'⟩ := kaNS_conj_mem hc0 E hE hψ hg s
    refine ⟨s', ?_⟩
    simp only [φ, MonoidHom.comp_apply, hs', map_mul, map_inv]
  refine ka_all_of_torus (ka_conj_inj_pl4 hodd) (E.map (proj 4 F)) φ.range ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (ka_rigid_proj (n := 4) (by norm_num) (fun A hA' => ka_conjAut_inner_of_odd_pl4 hodd A hA')
      φ.range kaNSN kaNSN_ne_zero kaNSN_mul_self fun a => ?_)
    (ka_outCentral_pl4 hodd (stdGL c) c hA)
  · rintro _ ⟨g, hg, rfl⟩
    exact proj_mem_fixSub_of_mem_commSub c hg
  · intro y hy ho
    have := ka_odd_mem_map_cent_pl4 (stdGL c) c hA (mem_fixSub.1 hy) ho
    rwa [kaNS_kaSlCent] at this
  · rintro _ ⟨s, rfl⟩
    exact ⟨ψ s, (hE _).2 (kaNS_comm_psi hψ s), rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact hconj g hg l hl
    · intro hl
      have := hconj g⁻¹ (E.inv_mem hg) _ hl
      simpa [mul_assoc] using this
  · exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range φ)
  · intro p hp hp2 M hML hMp hMn
    exact ka_central_of_quasisimple_image φ hqs hp M hML hMp hMn
  · intro p hp hp2 X hXp hXle hXc
    exact kaNS_cyclic h2 hc0 E hE hψ X hXle hXc
  · exact ⟨ψ (kaNSu (c : F) a), by rw [hψ, kaNSΘ_root], ⟨kaNSu (c : F) a, rfl⟩⟩

end Frame

theorem kaNS_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem kaL4NS_thm : KAL4NS := by
  intro F _ _ hodd A c hA hc
  obtain ⟨P, hP⟩ := exists_normal_form hA hc
  have h0 := kaL4NS_frame hodd c hc
  have h1 := KAAll.of_mulEquiv (conjAut 4 F P)⁻¹ h0
  have key : MulAut.congr (conjAut 4 F P)⁻¹ (conjAut 4 F (stdGL c)) = conjAut 4 F A := by
    rw [kaNS_congr_eq_mul, hP]
    group
  rwa [key] at h1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
