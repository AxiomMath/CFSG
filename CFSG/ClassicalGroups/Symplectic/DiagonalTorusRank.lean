module

public import CFSG.GroupTheory.CommutingMovingElemAbelian
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic

public section

namespace CFSG.ClassicalGroups.Symplectic

open Matrix

variable {m : ℕ} {F : Type} [Field F]

def threeToFinSp (hm : 3 ≤ m) : Fin 3 → Fin m := fun i => Fin.castLE hm i

theorem threeToFinSp_injective (hm : 3 ≤ m) : Function.Injective (threeToFinSp (m := m) hm) :=
  Fin.castLE_injective hm

noncomputable def diagUnitSp (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) : Fin m → Fˣ :=
  Pi.mulSingle (threeToFinSp hm i) t

@[simp]
theorem diagUnitSp_self (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) :
    diagUnitSp (m := m) (F := F) t hm i (threeToFinSp hm i) = t :=
  Pi.mulSingle_eq_same _ _

@[simp]
theorem diagUnitSp_of_ne (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) {j : Fin m}
    (hj : j ≠ threeToFinSp hm i) :
    diagUnitSp (m := m) (F := F) t hm i j = 1 := by
  change Pi.mulSingle (M := fun _ : Fin m => Fˣ) (threeToFinSp hm i) t j = 1
  exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Fˣ) hj t

theorem orderOf_diagUnitSp (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) :
    orderOf (diagUnitSp (m := m) (F := F) t hm i) = orderOf t := by
  rw [diagUnitSp, orderOf_piMulSingle]

noncomputable def diagGenSp (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) :
    TauCeti.GLSymplecticFin m F :=
  TauCeti.GLSymplecticFin.diagonal (diagUnitSp (m := m) (F := F) t hm i)

@[simp]
theorem coe_diagGenSp (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) :
    ((diagGenSp (m := m) (F := F) t hm i : TauCeti.GLSymplecticFin m F) :
        GL (Fin (m + m)) F) =
      TauCeti.diagGL (TauCeti.GLSymplecticFin.diagonalCoordinates
        (diagUnitSp (m := m) (F := F) t hm i)) := by
  rw [diagGenSp]
  exact TauCeti.GLSymplecticFin.coe_diagonal _

theorem diagGenSp_mem (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) :
    diagGenSp (m := m) (F := F) t hm i ∈ TauCeti.GLSymplecticFin.diagonalTorus F m := by
  rw [TauCeti.GLSymplecticFin.mem_diagonalTorus_iff_exists_diagonal]
  exact ⟨diagUnitSp (m := m) (F := F) t hm i, by rw [diagGenSp]⟩

theorem orderOf_diagGenSp (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) {q : ℕ}
    (ht : orderOf t = q) :
    orderOf (diagGenSp (m := m) (F := F) t hm i) = q := by
  rw [diagGenSp]
  calc
    orderOf (TauCeti.GLSymplecticFin.diagonal
        (diagUnitSp (m := m) (F := F) t hm i))
        = orderOf (diagUnitSp (m := m) (F := F) t hm i) :=
      orderOf_injective _ TauCeti.GLSymplecticFin.diagonal_injective _
    _ = orderOf t := orderOf_diagUnitSp t hm i
    _ = q := ht

theorem commute_diagGenSp (t : Fˣ) (hm : 3 ≤ m) (i j : Fin 3) :
    Commute (diagGenSp (m := m) (F := F) t hm i)
      (diagGenSp (m := m) (F := F) t hm j) := by
  rw [diagGenSp, diagGenSp]
  exact (Commute.all _ _).map TauCeti.GLSymplecticFin.diagonal

theorem diagGenSp_zpow (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) (a : ℤ) :
    (diagGenSp (m := m) (F := F) t hm i) ^ a =
      TauCeti.GLSymplecticFin.diagonal
        ((diagUnitSp (m := m) (F := F) t hm i) ^ a) := by
  rw [diagGenSp, ← map_zpow]

noncomputable def spAct (m : ℕ) (F : Type) [Field F] :
    TauCeti.GLSymplecticFin m F →* ((Fin (m + m) → F) ≃ₗ[F] (Fin (m + m) → F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin (m + m) → F)).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.toLin (n := Fin (m + m)) (R := F)).toMonoidHom.comp
      (Subgroup.subtype (TauCeti.GLSymplecticFin m F)))

theorem spAct_apply (A : TauCeti.GLSymplecticFin m F) (v : Fin (m + m) → F) :
    spAct (m := m) (F := F) A v =
      ((A : GL (Fin (m + m)) F) : Matrix (Fin (m + m)) (Fin (m + m)) F) *ᵥ v := by
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin (m + m) → F)
    (Matrix.GeneralLinearGroup.toLin (A : GL (Fin (m + m)) F))) v = _
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

theorem spAct_diagonal_single (d : Fin m → Fˣ) (j : Fin (m + m)) (x : F) :
    spAct (m := m) (F := F) (TauCeti.GLSymplecticFin.diagonal d) (Pi.single j x) =
      Pi.single j (TauCeti.GLSymplecticFin.diagonalCoordinates d j * x) := by
  rw [spAct_apply, TauCeti.GLSymplecticFin.coe_diagonal, TauCeti.diagGL_coe,
    Matrix.diagonal_mulVec_single]

theorem spAct_diagGenSp_zpow_single_self (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) (a : ℤ) :
    spAct (m := m) (F := F) ((diagGenSp (m := m) (F := F) t hm i) ^ a)
        (Pi.single (Fin.castAdd m (threeToFinSp hm i)) 1) =
      Pi.single (Fin.castAdd m (threeToFinSp hm i)) (((t ^ a : Fˣ) : F)) := by
  rw [diagGenSp_zpow, spAct_diagonal_single,
    TauCeti.GLSymplecticFin.diagonalCoordinates_castAdd, diagUnitSp,
    ← Pi.mulSingle_zpow (f := fun _ : Fin m => Fˣ),
    Pi.mulSingle_eq_same (M := fun _ : Fin m => Fˣ), mul_one]

theorem spAct_diagGenSp_single_of_ne (t : Fˣ) (hm : 3 ≤ m) {i j : Fin 3} (hij : i ≠ j) :
    spAct (m := m) (F := F) (diagGenSp (m := m) (F := F) t hm i)
        (Pi.single (Fin.castAdd m (threeToFinSp hm j)) 1) =
      Pi.single (Fin.castAdd m (threeToFinSp hm j)) 1 := by
  have hji : threeToFinSp hm j ≠ threeToFinSp hm i := by
    intro h
    exact hij (threeToFinSp_injective hm h).symm
  rw [diagGenSp, spAct_diagonal_single,
    TauCeti.GLSymplecticFin.diagonalCoordinates_castAdd, diagUnitSp,
    Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Fˣ) hji]
  simp

theorem dvd_of_diagGenSp_zpow_fixes (t : Fˣ) (hm : 3 ≤ m) (i : Fin 3) {q : ℕ}
    (ht : orderOf t = q) {a : ℤ}
    (h : spAct (m := m) (F := F) ((diagGenSp (m := m) (F := F) t hm i) ^ a)
        (Pi.single (Fin.castAdd m (threeToFinSp hm i)) 1) =
      Pi.single (Fin.castAdd m (threeToFinSp hm i)) 1) :
    (q : ℤ) ∣ a := by
  rw [spAct_diagGenSp_zpow_single_self] at h
  have hval : (((t ^ a : Fˣ) : F)) = 1 := by
    have := congrFun h (Fin.castAdd m (threeToFinSp hm i))
    simpa using this
  have hta : t ^ a = 1 := Units.ext hval
  rw [← ht, orderOf_dvd_iff_zpow_eq_one]
  exact hta

theorem three_le_pRank_diagonalTorus_sp {m : ℕ} (hm : 3 ≤ m) {F : Type} [Field F] [Finite F]
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    3 ≤ CFSG.Open.pRank q (TauCeti.GLSymplecticFin.diagonalTorus F m) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd' : q ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' q hdvd'
  obtain ⟨T, hTle, -, -, hTrank⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving (F := F) (X := Fin (m + m) → F)
      (G := TauCeti.GLSymplecticFin m F) (ι := Fin 3) (r := q) hq
      (fun i : Fin 3 => diagGenSp (m := m) (F := F) t hm i)
      (fun i : Fin 3 => Pi.single (Fin.castAdd m (threeToFinSp hm i)) 1)
      (spAct m F)
      (fun i => diagGenSp_mem t hm i)
      (fun i => orderOf_diagGenSp t hm i ht)
      (fun i j => commute_diagGenSp t hm i j)
      (fun i _ h => dvd_of_diagGenSp_zpow_fixes t hm i ht h)
      (fun i j hij => spAct_diagGenSp_single_of_ne t hm hij)
  have hcard : Nat.card (Fin 3) = 3 := by simp
  rw [hcard] at hTrank
  exact hTrank.trans (CFSG.SectionRank.pRank_mono hq.one_lt hTle)

end CFSG.ClassicalGroups.Symplectic

end
