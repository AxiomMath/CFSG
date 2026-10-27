module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankCore
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

@[expose] def fourRoots : Fin 4 → Fin Tag.E6.rank → ℤ :=
  ![![0, 1, 0, 0, 0, 0], ![0, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 2, 1]]

theorem fourRootsCheck :
    (∀ i, RootOps.isRootB Tag.E6 (fourRoots i) = true) ∧
    ∀ i j, i ≠ j → fourRoots i ≠ fourRoots j ∧ fourRoots i ≠ -fourRoots j ∧ RootOps.isRootB Tag.E6 (fourRoots i + fourRoots j) = false ∧
      RootOps.isRootB Tag.E6 (fourRoots i + -fourRoots j) = false ∧ RootOps.isRootB Tag.E6 (-fourRoots i + fourRoots j) = false ∧
      RootOps.isRootB Tag.E6 (-fourRoots i + -fourRoots j) = false := by
  decide +kernel


theorem commute_rootSubgroup {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hne : α ≠ β) (hne' : α ≠ -β) (hnot : ¬ IsRoot Tag.E6 (α + β))
    (F : Type) [Field F] :
    ∀ x ∈ rootSubgroup Tag.E6 F α, ∀ y ∈ rootSubgroup Tag.E6 F β, Commute x y :=
  ((simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) hα hβ hne hne').2 hnot) F

theorem commute_of_mem_rootPair (F : Type) [Field F] {i j : Fin 4} (hij : i ≠ j)
    {x y : ModGL Tag.E6 F}
    (hx : x ∈ rootSubgroup Tag.E6 F (fourRoots i) ⊔ rootSubgroup Tag.E6 F (-fourRoots i))
    (hy : y ∈ rootSubgroup Tag.E6 F (fourRoots j) ⊔ rootSubgroup Tag.E6 F (-fourRoots j)) :
    Commute x y := by
  obtain ⟨hroot, hpair⟩ := fourRootsCheck
  obtain ⟨hne, hne', h1, h2, h3, h4⟩ := hpair i j hij
  have hri : IsRoot Tag.E6 (fourRoots i) := RootOps.isRootB_iff.1 (hroot i)
  have hrj : IsRoot Tag.E6 (fourRoots j) := RootOps.isRootB_iff.1 (hroot j)
  have hnr : ∀ {v : Fin Tag.E6.rank → ℤ}, RootOps.isRootB Tag.E6 v = false → ¬ IsRoot Tag.E6 v :=
    fun {v} h hr => by
      rw [← RootOps.isRootB_iff, h] at hr
      exact Bool.false_ne_true hr
  have hn1 : -fourRoots i ≠ fourRoots j := fun h => hne' (neg_eq_iff_eq_neg.1 h)
  have hn2 : -fourRoots i ≠ -fourRoots j := fun h => hne (neg_inj.1 h)
  have hn3 : fourRoots i ≠ - -fourRoots j := by rw [neg_neg]; exact hne
  have hn4 : -fourRoots i ≠ - -fourRoots j := by rw [neg_neg]; exact hn1
  refine commute_of_sup (fun x hx y hy => ?_) (fun x hx y hy => ?_) (fun x hx y hy => ?_)
    (fun x hx y hy => ?_) _ hx _ hy
  · exact commute_rootSubgroup hri hrj hne hne' (hnr h1) F x hx y hy
  · exact commute_rootSubgroup hri (IsRoot.neg hrj) hne' hn3 (hnr h2) F x hx y hy
  · exact commute_rootSubgroup (IsRoot.neg hri) hrj hn1 hn2 (hnr h3) F x hx y hy
  · exact commute_rootSubgroup (IsRoot.neg hri) (IsRoot.neg hrj) hn2 hn4 (hnr h4) F x hx y hy

theorem commute_rootSL2 (F : Type) [Field F] {i j : Fin 4} (hij : i ≠ j)
    (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    Commute (rootSL2 Tag.E6 F (fourRoots i) A) (rootSL2 Tag.E6 F (fourRoots j) B) := by
  obtain ⟨hroot, -⟩ := fourRootsCheck
  have hri : IsRoot Tag.E6 (fourRoots i) := RootOps.isRootB_iff.1 (hroot i)
  have hrj : IsRoot Tag.E6 (fourRoots j) := RootOps.isRootB_iff.1 (hroot j)
  refine commute_of_mem_rootPair F hij ?_ ?_
  · rw [← range_rootSL2_of_isRoot hri]
    exact MonoidHom.mem_range.2 ⟨A, rfl⟩
  · rw [← range_rootSL2_of_isRoot hrj]
    exact MonoidHom.mem_range.2 ⟨B, rfl⟩

theorem exists_inverter_data_adjoint (F : Type) [Field F] [Finite F] (h3 : (3 : F) ≠ 0) :
    ∃ h w : Fin 4 → ↥(adjointGroup Tag.E6 F), (∀ i j, Commute (h i) (h j)) ∧
      (∀ i, orderOf (h i) = 3) ∧ (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      (∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) := by
  obtain ⟨e, u, he1, he3, heu⟩ := exists_order_three_inverter F h3
  let ψ : Fin 4 → Matrix.SpecialLinearGroup (Fin 2) F →* ↥(adjointGroup Tag.E6 F) := fun i =>
    (rootSL2 Tag.E6 F (fourRoots i)).codRestrict _
      (fun A => (exceptional_Lang_root_rank_one_data Tag.E6 F (fourRoots i)).2.2.2.2.1 A)
  have hψ : ∀ i A, ((ψ i A : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      rootSL2 Tag.E6 F (fourRoots i) A := fun i A => rfl
  have hinj : ∀ i, Function.Injective (ψ i) := fun i A B h =>
    rootSL2_injective_of_field (fourRoots i) (by
      simpa only [hψ] using congrArg (fun g : ↥(adjointGroup Tag.E6 F) => (g : ModGL Tag.E6 F)) h)
  have hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := fun i j hij A B =>
    Subtype.ext (commute_rootSL2 F hij A B).eq
  refine ⟨fun i => ψ i e, fun i => ψ i u, fun i j => ?_, fun i => ?_, fun i => ?_,
    fun i j hij => ?_⟩
  · by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij e e
  · exact orderOf_eq_prime (by rw [← map_pow, he3, map_one])
      fun h => he1 (hinj i (h.trans (map_one _).symm))
  · show ψ i u * ψ i e * (ψ i u)⁻¹ = (ψ i e)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, heu, map_inv]
  · rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm i j hij u e).eq

end CFSG.AGLEmbedding.KFactProofs.CoverE6
