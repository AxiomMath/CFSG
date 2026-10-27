module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag4
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section TwoElements

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem units_eq_one_of_card_two (hK : Nat.card K = 2) (c : Kˣ) : c = 1 :=
  Units.ext ((eq_zero_or_eq_one_of_card_two hK c).resolve_left c.ne_zero)

theorem scalars_eq_bot_of_card_two (hK : Nat.card K = 2) (m : ℕ) : scalars m K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  have hc : c = 1 := units_eq_one_of_card_two hK c
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hA, hc]
  simp

noncomputable def slEquivProj (hK : Nat.card K = 2) (m : ℕ) :
    SpecialLinearGroup (Fin m) K ≃* projectiveSL m K :=
  MulEquiv.ofBijective (proj m K) ⟨by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_bot_of_card_two hK], proj_surjective m K⟩

theorem sl_isSimple_of_card_two (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup (SpecialLinearGroup (Fin m) K) := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := m)
    (by omega) (Or.inl hm)
  exact ((slEquivProj hK m).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL m K).symm).isSimpleGroup

theorem sl_nonabelian_of_card_two (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    ∃ a b : SpecialLinearGroup (Fin m) K, a * b ≠ b * a := by
  have := sl_isSimple_of_card_two hK hm
  by_contra h
  push Not at h
  have hsolv : Group.IsSolvable (SpecialLinearGroup (Fin m) K) :=
    IsSimpleGroup.comm_iff_isSolvable.mp h
  have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) hm
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
    (G := SpecialLinearGroup (Fin m) K)).ne (Group.isPerfect_def.mp hperf)

theorem upperTriangular_le_unitriangular (hK : Nat.card K = 2) :
    upperTriangular n K ≤ unitriangular n K := by
  intro A hA
  refine ⟨fun i j hij => hA i j hij, fun i => ?_⟩
  have hdet := Matrix.det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hA)
  have h1 : (A : Matrix (Fin n) (Fin n) K).det = 1 := A.2
  rw [hdet] at h1
  have hne : (A : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
    intro h0
    have := Finset.prod_eq_zero (f := fun j => (A : Matrix (Fin n) (Fin n) K) j j)
      (Finset.mem_univ i) h0
    rw [this] at h1
    exact zero_ne_one h1
  exact (eq_zero_or_eq_one_of_card_two hK _).resolve_left hne

theorem isPGroup_ker_of_unitriangular [CharP K 2] (hn : 1 ≤ n)
    {N : Subgroup (SpecialLinearGroup (Fin n) K)} {S : Type*} [Group S] (f : ↥N →* S)
    (hf : ∀ x, f x = 1 → (x : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K) :
    IsPGroup 2 f.ker := by
  let φ : ↥f.ker →* ↥(unitriangular n K) :=
    ((Subgroup.subtype N).comp f.ker.subtype).codRestrict (unitriangular n K) fun x => hf x.1 x.2
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  exact IsPGroup.of_injective (isPGroup_unitriangular_charTwo hn) φ hinj

end TwoElements

section StatedModel

variable {K : Type} [Field K] [Finite K]

noncomputable def slEquivStatedProj (hK : Nat.card K = 2) (m : ℕ) :
    SpecialLinearGroup (Fin m) K ≃* StatedProj (StatedSL m K) :=
  (slEquivProj hK m).trans (statedSLEquivProjectiveSL m K).symm

end StatedModel

end CFSG.QuasithinUnique.Vol2Native.A312L
