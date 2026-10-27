module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieHeart

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Equiv Subgroup
open scoped commutatorElement

@[expose] def mT (y : Fin 5 → ZMod 5) : M5 := monT (fun i => Multiplicative.ofAdd (y i))

theorem mT_add (y y' : Fin 5 → ZMod 5) : mT (y + y') = mT y * mT y' := by
  unfold mT
  rw [← monT_mul]
  rfl

theorem mT_zero : mT 0 = 1 := by
  unfold mT
  have : (fun i : Fin 5 => Multiplicative.ofAdd ((0 : Fin 5 → ZMod 5) i)) = 1 := by
    funext i
    rfl
  rw [this]
  exact map_one _

theorem mT_const (c : ZMod 5) : mT (fun _ => c) = monScalar C5 5 (Multiplicative.ofAdd c) := rfl

theorem conj_mT (x : M5) (y : Fin 5 → ZMod 5) :
    x * mT y * x⁻¹ = mT (fun i => y (x.right.symm i)) := by
  unfold mT
  rw [mon_conj_monT]
  rfl

theorem monT_eq_mT (t : Fin 5 → C5) : monT t = mT (fun i => Multiplicative.toAdd (t i)) := by
  unfold mT
  congr 1

variable {A : Type} [Group A] (Φ : M5 →* A)

@[expose] def KerSc : Prop := ∀ x : M5, Φ x = 1 ↔ ∃ c : C5, x = monScalar C5 5 c

variable {Φ}

theorem Phi_mT_sub_const (hΦ : KerSc Φ) (y : Fin 5 → ZMod 5) (c : ZMod 5) :
    Φ (mT (fun i => y i - c)) = Φ (mT y) := by
  have h1 : (fun i => y i - c) = y + (fun _ => -c) := by
    funext i
    simp [sub_eq_add_neg]
  rw [h1, mT_add, map_mul, mT_const]
  have : Φ (monScalar C5 5 (Multiplicative.ofAdd (-c))) = 1 := (hΦ _).mpr ⟨_, rfl⟩
  rw [this, mul_one]

@[expose] def eps (Φ : M5 →* A) (v : V3) : A := Φ (mT (ext5 v))

theorem eps_add (v w : V3) : eps Φ (v + w) = eps Φ v * eps Φ w := by
  unfold eps
  rw [← map_mul, ← mT_add]
  congr 2
  funext i
  exact ext5_add v w i

theorem eps_zero : eps Φ 0 = 1 := by
  unfold eps
  have : ext5 0 = 0 := by
    funext i
    fin_cases i <;> simp [ext5]
  rw [this, mT_zero, map_one]

theorem eps_neg (v : V3) : eps Φ (-v) = (eps Φ v)⁻¹ := by
  have h := eps_add (Φ := Φ) v (-v)
  rw [add_neg_cancel, eps_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem eps_conj (hΦ : KerSc Φ) (x : M5) (v : V3) :
    Φ x * eps Φ v * (Φ x)⁻¹ = eps Φ (act x.right v) := by
  have hs : ∑ i, ext5 v (x.right.symm i) = 0 := by
    rw [Equiv.sum_comp x.right.symm (ext5 v)]
    exact sum_ext5 v
  unfold eps
  rw [← map_inv, ← map_mul, ← map_mul, conj_mT]
  unfold act
  rw [ext5_ch5 hs, Phi_mT_sub_const hΦ]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
