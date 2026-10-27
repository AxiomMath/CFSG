module

public import CFSG.LargeExtraspecial.PSL10Axis
public import CFSG.LargeExtraspecial.DWModelMat
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.LargeExtraspecial.GLRCent
public import CFSG.LargeExtraspecial.OfFStar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Subgroup CFSG.Open Matrix CFSG.LargeExtraspecial.DW
open scoped MatrixGroups

variable {m : ℕ}

@[expose] def tZero (m : ℕ) : SL(m + 1 + 1, ZMod 2) :=
  cornerTransvection (N := m + 1 + 1) (by omega)

theorem coe_tZero :
    ((tZero m : SL(m + 1 + 1, ZMod 2)) : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)) =
      affMat (Pi.single 0 1) 1 :=
  coe_cornerTransvection_eq_affMat (m := m + 1) (by omega)

theorem vec_add_self_zmod_two {k : ℕ} (v : Fin k → ZMod 2) : v + v = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (v i)

theorem exists_affMat_of_mem (c : centralizer ({tZero m} : Set SL(m + 1 + 1, ZMod 2))) :
    ∃ w g, cmat c = affMat w g ∧ g *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  have hc : cmat c * (tZero m : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)) =
      (tZero m : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)) * cmat c :=
    congrArg (fun x : SL(m + 1 + 1, ZMod 2) =>
      (x : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)))
      (mem_centralizer_singleton_iff.mp c.2)
  have hdet : (cmat c).det ≠ 0 := by
    rw [cmat, (c : SL(m + 1 + 1, ZMod 2)).2]
    exact one_ne_zero
  obtain ⟨w, g, hwg⟩ := exists_eq_affMat_of_commute (m := m + 1) (by omega) hdet hc
  refine ⟨w, g, hwg, ?_⟩
  rw [coe_tZero, hwg, affMat_mul, affMat_mul, mul_one, one_mul, one_mulVec] at hc
  have h1 := (affMat_injective hc).1
  rw [add_comm (Pi.single 0 1) w] at h1
  exact add_left_cancel h1

@[expose] def inner (i : Fin m) : Fin (m + 1 + 1) :=
  i.succ.castSucc

theorem inner_injective : Function.Injective (inner (m := m)) := fun i j h => by
  simpa [inner] using h

@[expose] def leviBlock (c : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  c.submatrix inner inner

theorem leviBlock_affMat (w : Fin (m + 1) → ZMod 2)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) :
    leviBlock (affMat w g) = g.submatrix Fin.succ Fin.succ := by
  ext i j
  exact affMat_castSucc_castSucc w g i.succ j.succ

theorem col_zero_of_mulVec {g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hg : g *ᵥ Pi.single 0 1 = Pi.single 0 1) (a : Fin (m + 1)) :
    g a 0 = (Pi.single 0 1 : Fin (m + 1) → ZMod 2) a := by
  have h := congrFun hg a
  rwa [mulVec_single_one] at h

theorem submatrix_succ_mul {g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hg : g *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    (g * g').submatrix Fin.succ Fin.succ =
      g.submatrix Fin.succ Fin.succ * g'.submatrix Fin.succ Fin.succ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, col_zero_of_mulVec hg]

@[expose] noncomputable def leviMonoidHom :
    centralizer ({tZero m} : Set SL(m + 1 + 1, ZMod 2)) →* Matrix (Fin m) (Fin m) (ZMod 2) where
  toFun c := leviBlock (cmat c)
  map_one' := submatrix_one _ inner_injective
  map_mul' c d := by
    obtain ⟨w, g, hc, hg⟩ := exists_affMat_of_mem c
    obtain ⟨w', g', hd, -⟩ := exists_affMat_of_mem d
    rw [cmat_mul, hc, hd, affMat_mul, leviBlock_affMat, leviBlock_affMat, leviBlock_affMat,
      submatrix_succ_mul hg]

@[expose] noncomputable def leviHom :
    centralizer ({tZero m} : Set SL(m + 1 + 1, ZMod 2)) →* GL (Fin m) (ZMod 2) :=
  (leviMonoidHom (m := m)).toHomUnits

theorem coe_leviHom (c : centralizer ({tZero m} : Set SL(m + 1 + 1, ZMod 2))) :
    ((leviHom c : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) = leviBlock (cmat c) :=
  rfl

@[expose] def diagOne (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ZMod 2)
    (Fin.cases (motive := fun _ => ZMod 2) 1 (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => ZMod 2) 0 (fun j' => B i' j') j) i

@[simp] theorem diagOne_zero_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) : diagOne B 0 0 = 1 :=
  rfl

@[simp] theorem diagOne_succ_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i : Fin m) :
    diagOne B i.succ 0 = 0 :=
  rfl

theorem diagOne_mulVec (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    diagOne B *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  rw [mulVec_single_one]
  funext a
  cases a using Fin.cases <;> simp [diagOne, Matrix.col_apply]

theorem det_diagOne (B : Matrix (Fin m) (Fin m) (ZMod 2)) : (diagOne B).det = B.det := by
  have hsub : (diagOne B).submatrix Fin.succ Fin.succ = B := by
    ext i j
    simp [diagOne]
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove_zero, hsub]

theorem leviHom_surjective : Function.Surjective (leviHom (m := m)) := by
  intro B
  have hdet : (affMat 0 (diagOne (B : Matrix (Fin m) (Fin m) (ZMod 2)))).det = 1 := by
    rw [det_affMat, det_diagOne]
    exact det_eq_one_of_ne_zero_zmod_two ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
  let s : SL(m + 1 + 1, ZMod 2) := ⟨_, hdet⟩
  have hs : s * tZero m = tZero m * s := by
    apply Subtype.ext
    change affMat 0 _ * _ = _ * affMat 0 _
    rw [coe_tZero, affMat_mul, affMat_mul, diagOne_mulVec, mul_one, one_mul, mulVec_zero,
      zero_add, add_zero]
  refine ⟨⟨s, mem_centralizer_singleton_iff.mpr hs⟩, Units.ext ?_⟩
  rw [coe_leviHom]
  change leviBlock (affMat 0 _) = _
  rw [leviBlock_affMat]
  ext i j
  simp [diagOne]

theorem mul_self_eq_one_of_submatrix {g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hg : g *ᵥ Pi.single 0 1 = Pi.single 0 1) (h1 : g.submatrix Fin.succ Fin.succ = 1) :
    g * g = 1 := by
  have hc := col_zero_of_mulVec hg
  have hs : ∀ i j : Fin m, g i.succ j.succ = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) i j :=
    fun i j => congrFun (congrFun h1 i) j
  have hz : ∀ i : Fin m, ¬ (0 : Fin (m + 1)) = i.succ := fun i h => Fin.succ_ne_zero i h.symm
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hc, hs, hz, Matrix.one_apply,
      CharTwo.add_self_eq_zero]

theorem isPGroup_ker_leviHom : IsPGroup 2 (leviHom (m := m)).ker := by
  intro x
  refine ⟨2, ?_⟩
  obtain ⟨w, g, hc, hg⟩ := exists_affMat_of_mem (x : centralizer ({tZero m} : Set _))
  have h1 : g.submatrix Fin.succ Fin.succ = 1 := by
    have h := congrArg (fun u : GL (Fin m) (ZMod 2) => (u : Matrix (Fin m) (Fin m) (ZMod 2)))
      (MonoidHom.mem_ker.mp x.2)
    simp only [coe_leviHom, hc, leviBlock_affMat, Units.val_one] at h
    exact h
  have hgg := mul_self_eq_one_of_submatrix hg h1
  have h2 : affMat w g ^ 2 = affMat (w + g *ᵥ w) 1 := by rw [sq, affMat_mul, hgg]
  have h4 : cmat ((x : centralizer ({tZero m} : Set _)) ^ 2 ^ 2) = 1 := by
    rw [cmat_pow, hc, show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, h2, sq, affMat_mul, one_mulVec,
      one_mul, vec_add_self_zmod_two, affMat_zero_one]
  exact Subtype.ext (cmat_injective (by rw [Subgroup.coe_pow, h4]; rfl))

theorem conclusion_tZero : Conclusion (SL(8 + 1 + 1, ZMod 2)) (tZero 8) := by
  intro _ hcard K hK hperf hN
  have hsurj : Function.Surjective (leviHom (m := 8)) := leviHom_surjective
  have : IsSimpleGroup (GL (Fin 8) (ZMod 2)) := S45Q.isSimpleGroup_GL_zmod_two (by norm_num)
  have hGL : 2 ^ 28 ∣ Nat.card (GL (Fin 8) (ZMod 2)) := by
    have h := Nat.ordProj_dvd (Nat.card (GL (Fin 8) (ZMod 2))) 2
    rwa [GLR.factorization_card_GL_zmod_two] at h
  have hFker : timmesfeldFStar (centralizer ({tZero 8} : Set SL(8 + 1 + 1, ZMod 2))) ≤
      (leviHom (m := 8)).ker := by
    have : ((timmesfeldFStar _).map (leviHom (m := 8))).Normal :=
      (timmesfeldFStar_normal _).map _ hsurj
    rcases Subgroup.Normal.eq_bot_or_eq_top ((timmesfeldFStar _).map (leviHom (m := 8))) with
      h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h1 := card_map_dvd
        (timmesfeldFStar (centralizer ({tZero 8} : Set SL(8 + 1 + 1, ZMod 2)))) (leviHom (m := 8))
      rw [h, card_top, hcard] at h1
      have h2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp (hGL.trans h1)
      omega
  have hKtop : K.map (leviHom (m := 8)) = ⊤ := by
    have : (K.map (leviHom (m := 8))).Normal := hK.map _ hsurj
    rcases Subgroup.Normal.eq_bot_or_eq_top (K.map (leviHom (m := 8))) with h | h
    · exfalso
      have hK2 : IsPGroup 2 K := isPGroup_ker_leviHom.to_le ((Subgroup.map_eq_bot_iff _).mp h)
      rw [eq_bot_of_isPGroup_of_perfect hK2 hperf, le_bot_iff] at hN
      rw [hN, card_bot] at hcard
      norm_num at hcard
    · exact h
  have hsurjK : Function.Surjective ((leviHom (m := 8)).domRestrict K) := by
    intro y
    obtain ⟨x, hx, rfl⟩ : y ∈ K.map (leviHom (m := 8)) := hKtop ▸ mem_top y
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [← card_ker_mul_card_of_surjective hsurjK, MonoidHom.ker_domRestrict,
    show (2 : ℕ) ^ 45 = 2 ^ 17 * 2 ^ 28 by norm_num]
  refine Nat.mul_dvd_mul ?_ hGL
  rw [← hcard, ← Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv]
  exact card_dvd_of_le (subgroupOf_mono K hFker)

end CFSG.LargeExtraspecial.S14.PSLPSU10
