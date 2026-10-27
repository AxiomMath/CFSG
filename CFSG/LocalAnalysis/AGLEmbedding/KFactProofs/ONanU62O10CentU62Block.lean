module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Gram
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentFrame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentGroup

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
  CFSG.AGLEmbedding.U62ThreeCent

@[expose] noncomputable def unitEquiv : F4ˣ ≃* Multiplicative (ZMod 3) :=
  mulEquivOfCyclicCardEq (by
    rw [card_units_F4, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])

@[expose] noncomputable def rootUnit (t : ZMod 3) : F4ˣ := unitEquiv.symm (Multiplicative.ofAdd t)

theorem rootUnit_add (s t : ZMod 3) : rootUnit (s + t) = rootUnit s * rootUnit t := by
  simp only [rootUnit, ofAdd_add, map_mul]

theorem rootUnit_zero : rootUnit 0 = 1 := by
  simp [rootUnit]

theorem rootUnit_injective : Function.Injective rootUnit := fun s t h => by
  have := unitEquiv.symm.injective h
  exact Multiplicative.ofAdd.injective this

theorem exists_rootUnit (u : F4ˣ) : ∃ t, rootUnit t = u :=
  ⟨Multiplicative.toAdd (unitEquiv u), by simp [rootUnit]⟩

noncomputable abbrev dK (κ : Fin 6 → ZMod 3) : GL (Fin 6) F4 :=
  diagGL6 (fun i => rootUnit (κ i))

theorem entry_eq_zero_of_commute (κ : Fin 6 → ZMod 3) {g : GL (Fin 6) F4}
    (hg : g * dK κ = dK κ * g) {i k : Fin 6} (hik : κ i ≠ κ k) :
    (g : Matrix (Fin 6) (Fin 6) F4) i k = 0 := by
  have h := congrArg (fun m : GL (Fin 6) F4 => (m : Matrix (Fin 6) (Fin 6) F4) i k) hg
  simp only [Units.val_mul, coe_diagGL6, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hne : ((rootUnit (κ i) : F4ˣ) : F4) ≠ ((rootUnit (κ k) : F4ˣ) : F4) := fun h' =>
    hik (rootUnit_injective (Units.ext h'))
  have h2 : ((g : Matrix (Fin 6) (Fin 6) F4) i k) * (((rootUnit (κ k) : F4ˣ) : F4) -
      ((rootUnit (κ i) : F4ˣ) : F4)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hne

abbrev Fib (κ : Fin 6 → ZMod 3) (t : ZMod 3) : Type := {i : Fin 6 // κ i = t}

theorem sum_fib (κ : Fin 6 → ZMod 3) (t : ZMod 3) (F : Fin 6 → F4) (hF : ∀ l, κ l ≠ t → F l = 0) :
    ∑ l : Fib κ t, F l.1 = ∑ l : Fin 6, F l := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun l => κ l = t) (by simp)]
  exact Finset.sum_filter_of_ne fun l _ hl => by
    by_contra h
    exact hl (hF l h)

@[expose] def blk (κ : Fin 6 → ZMod 3) (t : ZMod 3) (A : Matrix (Fin 6) (Fin 6) F4) :
    Matrix (Fib κ t) (Fib κ t) F4 :=
  A.submatrix (fun i => i.1) (fun i => i.1)

theorem blk_apply (κ : Fin 6 → ZMod 3) (t : ZMod 3) (A : Matrix (Fin 6) (Fin 6) F4)
    (i k : Fib κ t) : blk κ t A i k = A i.1 k.1 :=
  rfl

theorem blk_one (κ : Fin 6 → ZMod 3) (t : ZMod 3) : blk κ t (1 : Matrix (Fin 6) (Fin 6) F4) = 1 :=
  Matrix.submatrix_one _ Subtype.val_injective

theorem blk_mul_of_vanish (κ : Fin 6 → ZMod 3) {A B : Matrix (Fin 6) (Fin 6) F4}
    (hA : ∀ i k, κ i ≠ κ k → A i k = 0) (hB : ∀ i k, κ i ≠ κ k → B i k = 0) (t : ZMod 3) :
    blk κ t (A * B) = blk κ t A * blk κ t B := by
  ext ⟨i, hi⟩ ⟨k, hk⟩
  simp only [blk_apply, Matrix.mul_apply]
  rw [sum_fib κ t (fun l => A i l * B l k)]
  intro l hl
  by_cases h : κ i = κ l
  · have : κ l ≠ κ k := by rw [hk]; exact hl
    rw [hB l k this, mul_zero]
  · rw [hA i l h, zero_mul]

variable {κ : Fin 6 → ZMod 3} {y : GU6}

theorem vanish_of_mem_centralizer (hy : (y : GL (Fin 6) F4) = dK κ)
    (g : Subgroup.centralizer ({y} : Set GU6)) :
    ∀ i k, κ i ≠ κ k → (((g : GU6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) i k = 0 := by
  intro i k hik
  have hg := Subgroup.mem_centralizer_singleton_iff.1 g.2
  have h := congrArg (fun m : GU6 => (m : GL (Fin 6) F4)) hg
  simp only [Subgroup.coe_mul] at h
  rw [hy] at h
  exact entry_eq_zero_of_commute κ h hik

@[expose] noncomputable def blockMat (hy : (y : GL (Fin 6) F4) = dK κ) (t : ZMod 3) :
    Subgroup.centralizer ({y} : Set GU6) →* Matrix (Fib κ t) (Fib κ t) F4 where
  toFun g := blk κ t (((g : GU6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  map_one' := by
    simp only [Subgroup.coe_one, Units.val_one]
    exact blk_one κ t
  map_mul' g g' := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact blk_mul_of_vanish κ (vanish_of_mem_centralizer hy g)
      (vanish_of_mem_centralizer hy g') t

theorem blockMat_unitary (hy : (y : GL (Fin 6) F4) = dK κ) (t : ZMod 3)
    (g : Subgroup.centralizer ({y} : Set GU6)) :
    ((blockMat hy t g).map uData.bar)ᵀ * 1 * blockMat hy t g = 1 := by
  set A : Matrix (Fin 6) (Fin 6) F4 := (((g : GU6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
    with hA
  have hu : (A.map uData.bar)ᵀ * A = 1 := by
    have := mem_primeFormUnitary.1 (g : GU6).2
    rwa [M6_eq_one, Matrix.mul_one] at this
  have hv := vanish_of_mem_centralizer hy g
  have hvT : ∀ i k, κ i ≠ κ k → (A.map uData.bar)ᵀ i k = 0 := fun i k hik => by
    simp [Matrix.transpose_apply, hA, hv k i hik.symm]
  have := blk_mul_of_vanish κ hvT hv t
  rw [hu, blk_one] at this
  rw [Matrix.mul_one]
  exact this.symm

@[expose] noncomputable def blockU (hy : (y : GL (Fin 6) F4) = dK κ) (t : ZMod 3) :
    Subgroup.centralizer ({y} : Set GU6) →* gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4) :=
  (MonoidHom.toHomUnits (blockMat hy t)).codRestrict _ fun g => by
    rw [mem_gramU]
    exact blockMat_unitary hy t g

@[expose] noncomputable def blockPi (hy : (y : GL (Fin 6) F4) = dK κ) :
    Subgroup.centralizer ({y} : Set GU6) →*
      ∀ t : ZMod 3, gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4) :=
  MonoidHom.pi fun t => blockU hy t

theorem blockPi_injective (hy : (y : GL (Fin 6) F4) = dK κ) :
    Function.Injective (blockPi hy) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  have hblk : ∀ (t : ZMod 3) (i k : Fib κ t),
      (((g : GU6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) i.1 k.1 =
        (1 : Matrix (Fib κ t) (Fib κ t) F4) i k := fun t i k => by
    have h1 := congrArg (fun f => ((f t : gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) :
      GL (Fib κ t) F4)) hg
    have h2 := congrArg (fun m : GL (Fib κ t) F4 => (m : Matrix (Fib κ t) (Fib κ t) F4) i k) h1
    exact h2
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i k
  by_cases hik : κ i = κ k
  · have := hblk (κ i) ⟨i, rfl⟩ ⟨k, hik.symm⟩
    rw [this]
    simp [Matrix.one_apply, Subtype.ext_iff]
  · rw [vanish_of_mem_centralizer hy g i k hik]
    simp [Matrix.one_apply]
    rintro rfl
    exact hik rfl

theorem card_centralizer_dvd_prod (hy : (y : GL (Fin 6) F4) = dK κ) :
    Nat.card (Subgroup.centralizer ({y} : Set GU6)) ∣
      ∏ t : ZMod 3, Nat.card (gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) := by
  have := Subgroup.card_dvd_of_injective (blockPi hy) (blockPi_injective hy)
  rwa [Nat.card_pi] at this

end CFSG.AGLEmbedding.U62O10Cent
