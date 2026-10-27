module

public import CFSG.GroupTheory.CommutingMovingElemAbelian

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

variable {n : ℕ} {F : Type} [Field F]

noncomputable def diagGLHom (n : ℕ) (F : Type) [Field F] : (Fin n → Fˣ) →* GL (Fin n) F :=
  (Units.map (Matrix.diagonalRingHom (Fin n) F).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => F)).symm.toMonoidHom

@[simp]
theorem coe_diagGLHom (n : ℕ) (F : Type) [Field F] (d : Fin n → Fˣ) :
    (diagGLHom n F d : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun i => (d i : F)) := by
  ext i j
  change Matrix.diagonal (fun k => (((MulEquiv.piUnits (M := fun _ : Fin n => F)).symm d :
    (Fin n → F)ˣ) : Fin n → F) k) i j = Matrix.diagonal (fun k => (d k : F)) i j
  rfl

theorem det_diagGLHom (n : ℕ) (F : Type) [Field F] (d : Fin n → Fˣ) :
    (diagGLHom n F d : Matrix (Fin n) (Fin n) F).det = ((∏ i, d i : Fˣ) : F) := by
  rw [coe_diagGLHom, Matrix.det_diagonal, Units.coe_prod]

noncomputable def prodHom (n : ℕ) (F : Type) [Field F] : (Fin n → Fˣ) →* Fˣ where
  toFun d := ∏ i, d i
  map_one' := by simp
  map_mul' d e := by simp [Finset.prod_mul_distrib]

noncomputable def diagSLHom (n : ℕ) (F : Type) [Field F] :
    (prodHom n F).ker →* SpecialLinearGroup (Fin n) F where
  toFun d :=
    ⟨diagGLHom n F d, by
      rw [det_diagGLHom]
      exact congrArg Units.val d.2⟩
  map_one' := by
    apply Subtype.ext
    change (diagGLHom n F (1 : Fin n → Fˣ) : Matrix (Fin n) (Fin n) F) = 1
    rw [map_one]
    rfl
  map_mul' d e := by
    apply Subtype.ext
    change (diagGLHom n F ((d * e : (prodHom n F).ker) : Fin n → Fˣ) :
        Matrix (Fin n) (Fin n) F) =
      (diagGLHom n F (d : Fin n → Fˣ) : Matrix (Fin n) (Fin n) F) *
        (diagGLHom n F (e : Fin n → Fˣ) : Matrix (Fin n) (Fin n) F)
    rw [Subgroup.coe_mul, map_mul, Units.val_mul]

noncomputable def diagTorus (n : ℕ) (F : Type) [Field F] :
    Subgroup (SpecialLinearGroup (Fin n) F) :=
  (diagSLHom n F).range

@[simp]
theorem coe_diagSLHom (n : ℕ) (F : Type) [Field F] (d : (prodHom n F).ker) :
    (diagSLHom n F d : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun i => ((d : Fin n → Fˣ) i : F)) :=
  coe_diagGLHom n F d

theorem coe_diagSLHom_zpow (n : ℕ) (F : Type) [Field F] (d : (prodHom n F).ker) (a : ℤ) :
    ((diagSLHom n F d ^ a : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun i => (((d : Fin n → Fˣ) ^ a) i : F)) := by
  rw [← map_zpow (diagSLHom n F) d a, coe_diagSLHom, Subgroup.coe_zpow]

theorem mem_diagTorus_iff {g : SpecialLinearGroup (Fin n) F} :
    g ∈ diagTorus n F ↔ ∃ d : Fin n → Fˣ, (∏ i, d i = 1) ∧
      (g : Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun i => (d i : F)) := by
  constructor
  · intro hg
    rw [diagTorus, MonoidHom.mem_range] at hg
    obtain ⟨d, rfl⟩ := hg
    exact ⟨(d : Fin n → Fˣ), d.2, coe_diagSLHom n F d⟩
  · rintro ⟨d, hd, hg⟩
    rw [diagTorus, MonoidHom.mem_range]
    refine ⟨⟨d, hd⟩, ?_⟩
    ext i j
    simp [coe_diagSLHom, hg]

def threeToFin (hn : 4 ≤ n) : Fin 3 → Fin n := fun i => Fin.castLE (by omega : 3 ≤ n) i

def threeIndex (hn : 4 ≤ n) : Fin n := ⟨3, by omega⟩

theorem threeToFin_ne_threeIndex (hn : 4 ≤ n) (i : Fin 3) :
    threeToFin hn i ≠ threeIndex hn := by
  intro h
  have := congrArg Fin.val h
  simp [threeToFin, threeIndex] at this
  omega

theorem threeToFin_injective (hn : 4 ≤ n) : Function.Injective (threeToFin (n := n) hn) :=
  Fin.castLE_injective (by omega : 3 ≤ n)

noncomputable def diagUnit (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) : Fin n → Fˣ :=
  Function.update (Function.update 1 (threeIndex hn) (t⁻¹)) (threeToFin hn i) t

@[simp]
theorem diagUnit_self (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) :
    diagUnit (n := n) (F := F) t hn i (threeToFin hn i) = t := by
  simp [diagUnit, Function.update, threeToFin_ne_threeIndex hn i]

@[simp]
theorem diagUnit_threeIndex (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) :
    diagUnit (n := n) (F := F) t hn i (threeIndex hn) = t⁻¹ := by
  simp [diagUnit, Function.update, (threeToFin_ne_threeIndex hn i).symm]

theorem diagUnit_of_ne (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) {j : Fin n}
    (hjp : j ≠ threeToFin hn i) (hjq : j ≠ threeIndex hn) :
    diagUnit (n := n) (F := F) t hn i j = 1 := by
  simp [diagUnit, Function.update, hjp, hjq]

theorem prod_diagUnit (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) :
    (∏ j, diagUnit (n := n) (F := F) t hn i j) = 1 := by
  classical
  have hp : threeToFin hn i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hq : threeIndex hn ∈ (Finset.univ : Finset (Fin n)) \ {threeToFin hn i} := by
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨Finset.mem_univ _, (threeToFin_ne_threeIndex hn i).symm⟩
  rw [diagUnit, Finset.prod_update_of_mem hp, Finset.prod_update_of_mem hq]
  simp

noncomputable def diagGen (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) :
    SpecialLinearGroup (Fin n) F :=
  diagSLHom n F ⟨diagUnit t hn i, prod_diagUnit t hn i⟩

theorem coe_diagGen (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) :
    (diagGen t hn i : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun j => (diagUnit (n := n) (F := F) t hn i j : F)) :=
  coe_diagSLHom n F _

theorem coe_diagGen_pow (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) (k : ℕ) :
    ((diagGen t hn i ^ k : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun j => (((diagUnit (n := n) (F := F) t hn i) ^ k) j : F)) := by
  rw [diagGen, ← map_pow (diagSLHom n F) ⟨diagUnit t hn i, prod_diagUnit t hn i⟩ k,
    coe_diagSLHom, Subgroup.coe_pow]

theorem coe_diagGen_zpow (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) (a : ℤ) :
    ((diagGen t hn i ^ a : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun j => (((diagUnit (n := n) (F := F) t hn i) ^ a) j : F)) := by
  rw [diagGen, coe_diagSLHom_zpow]

theorem diagGen_mem_diagTorus (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) :
    diagGen (n := n) (F := F) t hn i ∈ diagTorus n F := by
  rw [diagTorus, MonoidHom.mem_range]
  exact ⟨⟨diagUnit t hn i, prod_diagUnit t hn i⟩, rfl⟩

theorem orderOf_diagGen (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) {q : ℕ}
    (hq : q.Prime) (ht : orderOf t = q) :
    orderOf (diagGen (n := n) (F := F) t hn i) = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have htq : t ^ q = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have htqi : (t⁻¹) ^ q = 1 := by
    rw [inv_pow, htq, inv_one]
  apply orderOf_eq_prime
  · apply Subtype.ext
    show ((diagGen t hn i ^ q : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = (1 : Matrix (Fin n) (Fin n) F)
    rw [coe_diagGen_pow, Matrix.diagonal_eq_one]
    funext j
    by_cases hj : j = threeToFin hn i
    · subst hj
      simp [htq]
    · by_cases hj' : j = threeIndex hn
      · subst hj'
        simp [hj, htqi]
      · simp [diagUnit_of_ne t hn i hj hj']
  · intro h
    have hmat : (diagUnit (n := n) (F := F) t hn i (threeToFin hn i) : F) = 1 := by
      have h' := congrArg (fun g : SpecialLinearGroup (Fin n) F =>
        (g : Matrix (Fin n) (Fin n) F) (threeToFin hn i) (threeToFin hn i)) h
      simpa [coe_diagGen, SpecialLinearGroup.coe_one, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq] using h'
    rw [diagUnit_self] at hmat
    have ht1 : t = 1 := Units.ext hmat
    rw [ht1] at ht
    rw [orderOf_one] at ht
    exact hq.ne_one ht.symm

theorem commute_diagGen (t : Fˣ) (hn : 4 ≤ n) (i j : Fin 3) :
    Commute (diagGen (n := n) (F := F) t hn i) (diagGen (n := n) (F := F) t hn j) := by
  apply Subtype.ext
  change (diagGen (n := n) (F := F) t hn i : Matrix (Fin n) (Fin n) F) *
      (diagGen (n := n) (F := F) t hn j : Matrix (Fin n) (Fin n) F) =
    (diagGen (n := n) (F := F) t hn j : Matrix (Fin n) (Fin n) F) *
      (diagGen (n := n) (F := F) t hn i : Matrix (Fin n) (Fin n) F)
  rw [coe_diagGen, coe_diagGen, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

theorem toLin'_diagGen_zpow_single (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) (a : ℤ) :
    SpecialLinearGroup.toLin' (diagGen (n := n) (F := F) t hn i ^ a)
        (Pi.single (threeToFin hn i) 1) =
      Pi.single (threeToFin hn i)
        (((diagUnit (n := n) (F := F) t hn i ^ a) (threeToFin hn i) : Fˣ) : F) := by
  rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, coe_diagGen_zpow,
    Matrix.diagonal_mulVec_single]
  simp

theorem dvd_of_diagGen_zpow_fixes (t : Fˣ) (hn : 4 ≤ n) (i : Fin 3) {q : ℕ}
    (ht : orderOf t = q) {a : ℤ}
    (h : SpecialLinearGroup.toLin' (diagGen (n := n) (F := F) t hn i ^ a)
        (Pi.single (threeToFin hn i) 1) = Pi.single (threeToFin hn i) 1) :
    (q : ℤ) ∣ a := by
  rw [toLin'_diagGen_zpow_single] at h
  have hval : (((diagUnit (n := n) (F := F) t hn i ^ a) (threeToFin hn i) : Fˣ) : F) = 1 := by
    have := congrFun h (threeToFin hn i)
    simpa using this
  have hval' : (diagUnit (n := n) (F := F) t hn i ^ a) (threeToFin hn i) = 1 :=
    Units.ext hval
  have hds : diagUnit (n := n) (F := F) t hn i (threeToFin hn i) = t := by
    simp [diagUnit, Function.update, threeToFin_ne_threeIndex hn i]
  have hta : t ^ a = 1 := by
    rw [← hds]
    change (diagUnit (n := n) (F := F) t hn i (threeToFin hn i)) ^ a = 1
    exact hval'
  rw [← ht]
  exact orderOf_dvd_iff_zpow_eq_one.mpr hta

theorem toLin'_diagGen_single_of_ne (t : Fˣ) (hn : 4 ≤ n) {i j : Fin 3} (hij : i ≠ j) :
    SpecialLinearGroup.toLin' (diagGen (n := n) (F := F) t hn i)
        (Pi.single (threeToFin hn j) 1) = Pi.single (threeToFin hn j) 1 := by
  have hpj : threeToFin hn i ≠ threeToFin hn j := by
    intro h
    exact hij (threeToFin_injective hn h)
  have hqj : threeIndex hn ≠ threeToFin hn j := by
    intro h
    have := congrArg Fin.val h
    simp [threeIndex, threeToFin] at this
    omega
  rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, coe_diagGen,
    Matrix.diagonal_mulVec_single]
  have hval : diagUnit (n := n) (F := F) t hn i (threeToFin hn j) = 1 :=
    diagUnit_of_ne t hn i hpj.symm hqj.symm
  rw [hval]
  simp

theorem three_le_pRank_diagTorus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    3 ≤ CFSG.Open.pRank q (diagTorus n F) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd' : q ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' q hdvd'
  obtain ⟨T, hTle, -, -, hTrank⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving (F := F) (X := Fin n → F)
      (G := SpecialLinearGroup (Fin n) F) (ι := Fin 3) (r := q) hq
      (fun i : Fin 3 => diagGen (n := n) (F := F) t hn i)
      (fun i : Fin 3 => Pi.single (threeToFin hn i) 1)
      (SpecialLinearGroup.toLin' : SpecialLinearGroup (Fin n) F →*
        ((Fin n → F) ≃ₗ[F] (Fin n → F)))
      (fun i => diagGen_mem_diagTorus t hn i)
      (fun i => orderOf_diagGen t hn i hq ht)
      (fun i j => commute_diagGen t hn i j)
      (fun i a h => dvd_of_diagGen_zpow_fixes t hn i ht h)
      (fun i j hij => toLin'_diagGen_single_of_ne t hn hij)
  have hcard : Nat.card (Fin 3) = 3 := by simp
  rw [hcard] at hTrank
  exact hTrank.trans (CFSG.SectionRank.pRank_mono hq.one_lt hTle)

end CFSG.ClassicalGroups.SpecialLinear

end
