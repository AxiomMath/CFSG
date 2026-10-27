module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CentralQuotient
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearInner
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

universe u

variable {n : ℕ} {k : Type u} [Field k] [Finite k]

private theorem isSolvable_pi_of_finite' {ι : Type*} [Finite ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  cases nonempty_fintype ι
  have hle : ∀ m : ℕ, derivedSeries (∀ i, G i) m ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (G i) m) := by
    intro m
    induction m with
    | zero =>
      simp only [derivedSeries_zero]
      rw [Subgroup.pi_top]
    | succ m ih =>
      rw [derivedSeries_succ]
      calc ⁅derivedSeries (∀ i, G i) m, derivedSeries (∀ i, G i) m⁆
          ≤ ⁅Subgroup.pi Set.univ (fun i => derivedSeries (G i) m),
              Subgroup.pi Set.univ (fun i => derivedSeries (G i) m)⁆ :=
            Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.pi Set.univ (fun i => ⁅derivedSeries (G i) m, derivedSeries (G i) m⁆) :=
            Subgroup.commutator_pi_pi_le _ _
        _ = Subgroup.pi Set.univ (fun i => derivedSeries (G i) (m + 1)) := by
            simp_rw [derivedSeries_succ]
  choose d hd using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup d, ?_⟩⟩
  rw [eq_bot_iff]
  refine (hle _).trans ?_
  rw [le_bot_iff, Subgroup.pi_eq_bot_iff]
  intro i
  rw [eq_bot_iff, ← hd i]
  exact derivedSeries_antitone (G i) (Finset.le_sup (f := d) (Finset.mem_univ i))

theorem linear_inner_components {p : ℕ} (hpk : (p : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A))) :
    ∃ h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h},
      K = (specialFactor A h.1.1).map (LinearFlag.proj n k) := by
  have hsq := squarefree_minpoly_glA hpk hA
  haveI : ∀ b : {b : primaryFactors (glA A : Module.End k (Fin n → k)) // ¬ IsGoodFactor A b},
      Group.IsSolvable (blockGL (glA A : Module.End k (Fin n → k)) b.1.1) := fun b =>
    isSolvable_blockGL_of_not_good b.1.2 b.2
  haveI : Group.IsSolvable ((b : primaryFactors (glA A : Module.End k (Fin n → k))) →
      (AdjoinRoot (b : k[X]))ˣ) := inferInstance
  haveI : Group.IsSolvable ((b : {b : primaryFactors (glA A : Module.End k (Fin n → k)) //
      ¬ IsGoodFactor A b}) → blockGL (glA A : Module.End k (Fin n → k)) b.1.1) :=
    isSolvable_pi_of_finite'
  exact components_of_centralQuotient (LinearFlag.proj n k) (LinearFlag.proj_surjective n k)
    (by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_center n k)
    (CatalogueBHigherLinearAction.slConjugation n k A) (LinearFlag.conjAut n k A)
    (fun x => (LinearFlag.conjAut_proj A x).symm)
    (fun h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h} =>
      specialFactor A h.1.1)
    (fun h => specialFactor_le_fixSubgroup A _) (fun h c' hc g hg => conj_mem_specialFactor hc hg)
    (fun h => isQuasisimple_specialFactor hsq h.1.2 h.2) (blockDetHom hsq)
    (mem_iSup_specialFactor_of_blockDetHom_eq_one hsq) K hK

theorem nonempty_mulEquiv_specialFactor {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) {h : k[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k))) :
    Nonempty (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h)) (AdjoinRoot h) ≃*
        specialFactor A h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  let b : Module.Basis (Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h))
      (AdjoinRoot h) (primaryComponent (glA A : Module.End k (Fin n → k)) h) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : linearSpecialBlock (glA A) h ≃*
      _root_.SpecialLinearGroup (AdjoinRoot h)
        (primaryComponent (glA A : Module.End k (Fin n → k)) h) :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict (glA A) h)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  have hle : linearSpecialBlock (glA A) h ≤ (slGL n k).range := fun _ hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  have hmap : (specialFactor A h).map (slGL n k) = linearSpecialBlock (glA A) h := by
    rw [specialFactor, Subgroup.map_comap_eq, inf_eq_right]
    exact hle
  exact ⟨((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm).trans
    ((Subgroup.equivMapOfInjective _ (slGL n k) slGL_injective).trans
      (MulEquiv.subgroupCongr hmap)).symm⟩

theorem exists_surjective_ker_le_center_map_proj {G : Type*} [Group G]
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin n) k)} (e : G ≃* S) :
    ∃ f : G →* ↥(S.map (LinearFlag.proj n k)), Function.Surjective f ∧
      f.ker ≤ Subgroup.center G := by
  refine ⟨((LinearFlag.proj n k).subgroupMap S).comp e.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ S).comp e.surjective, fun g hg => ?_⟩
  have h1 : LinearFlag.proj n k (e g : Matrix.SpecialLinearGroup (Fin n) k) = 1 :=
    congrArg Subtype.val hg
  have h2 : (e g : Matrix.SpecialLinearGroup (Fin n) k) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) :=
    LinearFlag.scalars_le_center n k (LinearFlag.proj_eq_one_iff.1 h1)
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (e y))

theorem linear_inner_component_type_card {p : ℕ} (hpk : (p : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A))) :
    ∃ (E : Type u) (_ : Field E) (_ : Fintype E) (m j : ℕ), 2 ≤ m ∧ 1 ≤ j ∧
      ringChar E = ringChar k ∧ Nat.card E = Nat.card k ^ j ∧ (m = 2 → 4 ≤ Nat.card E) ∧
      ∃ f : Matrix.SpecialLinearGroup (Fin m) E →* ↥K, Function.Surjective f ∧
        f.ker ≤ Subgroup.center _ := by
  obtain ⟨h, rfl⟩ := linear_inner_components hpk hA K hK
  have hsq := squarefree_minpoly_glA hpk hA
  have : Fact (Irreducible h.1.1) := ⟨irreducible_of_mem_primaryFactors h.1.2⟩
  have : Finite (AdjoinRoot h.1.1) := Module.finite_of_finite k
  obtain ⟨e⟩ := nonempty_mulEquiv_specialFactor hsq h.1.2
  obtain ⟨f, hf, hker⟩ := exists_surjective_ker_le_center_map_proj e
  have hcard : Nat.card (AdjoinRoot h.1.1) = Nat.card k ^ h.1.1.natDegree :=
    CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h.1.1
  have hj : 1 ≤ h.1.1.natDegree := (Fact.out : Irreducible h.1.1).natDegree_pos
  refine ⟨AdjoinRoot h.1.1, inferInstance, Fintype.ofFinite _,
    primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1, h.1.1.natDegree,
    ?_, hj, (Algebra.ringChar_eq k (AdjoinRoot h.1.1)).symm, hcard, ?_, f, hf, hker⟩
  · rcases h.2 with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  · intro hm2
    rcases h.2 with h3 | ⟨-, h4⟩
    · omega
    · exact h4

theorem linear_inner_component_type {p : ℕ} (hpk : (p : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A))) :
    ∃ (E : Type u) (_ : Field E) (_ : Fintype E) (m : ℕ), 2 ≤ m ∧ ringChar E = ringChar k ∧
      ∃ f : Matrix.SpecialLinearGroup (Fin m) E →* ↥K, Function.Surjective f ∧
        f.ker ≤ Subgroup.center _ := by
  obtain ⟨E, hE, hFE, m, -, hm, -, hchar, -, -, f, hf, hker⟩ :=
    linear_inner_component_type_card hpk hA K hK
  exact ⟨E, hE, hFE, m, hm, hchar, f, hf, hker⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
