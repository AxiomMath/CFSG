module

public import CFSG.LieType.Chevalley.RootOps.Comm
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem exists_cartan_pos {α : Fin τ.rank → ℤ} (hα : α ≠ 0) (hnn : ∀ j, 0 ≤ α j) :
    ∃ i, 0 < α i ∧ 0 < ∑ j, τ.cartan i j * α j := by
  by_contra hcon
  push Not at hcon
  have hd : ∀ i : Fin τ.rank, 0 < τ.symmetrizer i i := by
    cases τ <;> intro i <;> fin_cases i <;> decide
  have hsym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.symmetrizer i i * τ.cartan i j := by
    intro i j
    cases τ <;> fin_cases i <;> fin_cases j <;> decide
  set x : Fin τ.rank →₀ ℝ := Finsupp.equivFunOnFinite.symm fun j => (α j : ℝ)
  have hx : x ≠ 0 := by
    intro h
    apply hα
    funext j
    have := congrArg (fun y : Fin τ.rank →₀ ℝ => y j) h
    simpa [x] using this
  have hxv : ∀ j, x j = (α j : ℝ) := fun j => by simp [x]
  have hpos := (posDef_symmetrizedCartan τ).2 hx
  rw [Finsupp.sum_fintype _ _ (fun i => by simp)] at hpos
  simp only [hxv, star_trivial, Matrix.map_apply, hsym, Int.cast_mul] at hpos
  have hin : ∀ i, (x.sum fun j xj => (α i : ℝ) * ((τ.symmetrizer i i : ℝ) *
      (τ.cartan i j : ℝ)) * xj) =
      ∑ j, (α i : ℝ) * ((τ.symmetrizer i i : ℝ) * (τ.cartan i j : ℝ)) * (α j : ℝ) := fun i => by
    rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
    simp [hxv]
  simp only [hin] at hpos
  have hle : ∑ i, ∑ j, (α i : ℝ) * ((τ.symmetrizer i i : ℝ) * (τ.cartan i j : ℝ)) * (α j : ℝ) ≤
      0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    have : ∑ j, (α i : ℝ) * ((τ.symmetrizer i i : ℝ) * (τ.cartan i j : ℝ)) * (α j : ℝ) =
        (α i : ℝ) * (τ.symmetrizer i i : ℝ) * ∑ j, (τ.cartan i j : ℝ) * (α j : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    rcases (hnn i).lt_or_eq with h | h
    · have h1 : (0 : ℝ) < α i := by exact_mod_cast h
      have h2 : (0 : ℝ) < τ.symmetrizer i i := by exact_mod_cast hd i
      have h3 : ∑ j, (τ.cartan i j : ℝ) * (α j : ℝ) ≤ 0 := by
        exact_mod_cast hcon i h
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h3
    · rw [← h]
      simp
  linarith

theorem exists_reflect_height_lt {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hpos : 0 < height α)
    (hns : ∀ i, α ≠ Pi.single i 1) :
    ∃ i, IsRoot τ (reflect τ i α) ∧ 0 < height (reflect τ i α) ∧
      height (reflect τ i α) < height α := by
  have hnn := (IsRoot.height_pos_iff hα).1 hpos
  obtain ⟨i, -, hi⟩ := exists_cartan_pos hα.ne_zero hnn
  refine ⟨i, .reflect i hα, height_reflect_pos hα hpos (hns i), ?_⟩
  have : height (reflect τ i α) = height α - ∑ j, τ.cartan i j * α j := by
    simp only [height, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
    simp [Pi.single_apply]
  omega

variable (K : Type) [Field K]

theorem commContained_pos (α β : Root τ) (hα : 0 < height α.1) (hβ : 0 < height β.1)
    (hne : α ≠ β) : (rootOperatorFamily τ).CommContained K α β := by
  induction h : (height α.1).toNat using Nat.strong_induction_on generalizing α β with
  | _ n ih =>
    by_cases hs : ∃ i, α = simpleRoot τ i
    · obtain ⟨i, rfl⟩ := hs
      exact commContained_simpleRoot τ K i β hβ (Ne.symm hne)
    push Not at hs
    have hns : ∀ i, α.1 ≠ Pi.single i 1 := fun i h => hs i (Subtype.ext h)
    obtain ⟨i, hr, hrpos, hrlt⟩ := exists_reflect_height_lt α.2 hα hns
    by_cases hb : β = simpleRoot τ i
    · subst hb
      exact (commContained_simpleRoot τ K i α hα hne).symm
    have hβ' : 0 < height (reflect τ i β.1) :=
      height_reflect_pos β.2 hβ fun h => hb (Subtype.ext h)
    have hne' : simple τ i • α ≠ simple τ i • β := fun h => hne (smul_left_cancel _ h)
    have hrec := ih (height (reflect τ i α.1)).toNat (by omega) (simple τ i • α)
      (simple τ i • β) (by rw [coe_smul_root, simple_smul]; exact hrpos)
      (by rw [coe_smul_root, simple_smul]; exact hβ') hne' (by rw [coe_smul_root, simple_smul])
    have := (rootOperatorFamily τ).comm_transport i hrec
    rwa [smul_smul, (coxeterSystem τ).simple_mul_simple_self, one_smul, smul_smul,
      (coxeterSystem τ).simple_mul_simple_self, one_smul] at this

end CFSG.LieType.Chevalley
