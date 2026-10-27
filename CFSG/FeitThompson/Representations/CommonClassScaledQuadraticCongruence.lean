module

public import CFSG.FeitThompson.Representations.CentralCharacterHomomorphism
public import CFSG.FeitThompson.Representations.ClassSumsIntegerStructureConstants
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.CharacterValuesAlgebraicIntegers
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

def algIntegerMultiples (t : ℂ) : Submodule ℤ ℂ :=
  (Subalgebra.toSubmodule (integralClosure ℤ ℂ)).map (LinearMap.mulLeft ℤ t)

theorem mem_algIntegerMultiples_iff {t x : ℂ} :
    x ∈ algIntegerMultiples t ↔ ∃ r : ℂ, IsIntegral ℤ r ∧ x = t * r := by
  simp only [algIntegerMultiples, Submodule.mem_map, Subalgebra.mem_toSubmodule,
    LinearMap.mulLeft_apply, mem_integralClosure_iff]
  exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩

theorem mul_mem_algIntegerMultiples (t : ℂ) {r : ℂ} (hr : IsIntegral ℤ r) :
    t * r ∈ algIntegerMultiples t :=
  mem_algIntegerMultiples_iff.2 ⟨r, hr, rfl⟩

theorem algIntegerMultiples_le_integralClosure {t : ℂ} (ht : IsIntegral ℤ t) :
    algIntegerMultiples t ≤ Subalgebra.toSubmodule (integralClosure ℤ ℂ) := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := mem_algIntegerMultiples_iff.1 hx
  exact ht.mul hr

@[simp]
theorem algIntegerMultiples_one :
    algIntegerMultiples 1 = Subalgebra.toSubmodule (integralClosure ℤ ℂ) :=
  le_antisymm (algIntegerMultiples_le_integralClosure isIntegral_one) fun x hx =>
    mem_algIntegerMultiples_iff.2 ⟨x, hx, (one_mul x).symm⟩

theorem smodEq_algIntegerMultiples_iff {t a b : ℂ} :
    a ≡ b [SMOD algIntegerMultiples t] ↔ ∃ r : ℂ, IsIntegral ℤ r ∧ a - b = t * r := by
  rw [SModEq.sub_mem, mem_algIntegerMultiples_iff]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem coeff_conjClassSum {k : Type*} [Semiring k] (x g : G) :
    (conjClassSum k x).coeff g = if ConjClasses.mk g = ConjClasses.mk x then 1 else 0 := by
  rw [conjClassSum_def, MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rw [Finset.sum_ite_eq' (conjClassFinset x) g (fun _ => (1 : k))]
  simp only [mem_conjClassFinset, ConjClasses.mk_eq_mk_iff_isConj]
  exact if_congr isConj_comm rfl rfl

theorem classSum_eq_conjClassSum {k : Type*} [CommSemiring k] (x : G) :
    classSum k (ConjClasses.mk x) = conjClassSum k x := by
  refine MonoidAlgebra.coeff_inj.1 ?_
  ext g
  rw [coeff_classSum, coeff_conjClassSum]

theorem coe_centerClassSum_eq_conjClassSum (M : ConjClasses G) :
    (centerClassSum ℂ M : MonoidAlgebra ℂ G) = conjClassSum ℂ (classRep M) := by
  rw [coe_centerClassSum, ← classSum_eq_conjClassSum (classRep M), mk_classRep]

@[simp]
theorem centerClassSum_one : centerClassSum ℂ (1 : ConjClasses G) = 1 :=
  Subtype.ext (by simp)

variable (ρ : Representation ℂ G V) [ρ.IsIrreducible]

theorem centralCharacter_centerClassSum (M : ConjClasses G) :
    Representation.centralCharacter ρ (centerClassSum ℂ M)
      = (Nat.card M.carrier : ℂ) * ρ.character (classRep M) / ρ.character 1 := by
  have h : centerClassSum ℂ M
      = (⟨conjClassSum ℂ (classRep M), conjClassSum_mem_center ℂ (classRep M)⟩ :
          Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :=
    Subtype.ext (coe_centerClassSum_eq_conjClassSum M)
  rw [h, Representation.centralCharacter_conjClassSum, card_conjClassFinset, mk_classRep]

theorem character_one_mul_centralCharacter_centerClassSum (M : ConjClasses G) :
    ρ.character 1 * Representation.centralCharacter ρ (centerClassSum ℂ M)
      = (Nat.card M.carrier : ℂ) * ρ.character (classRep M) := by
  rw [centralCharacter_centerClassSum, mul_div_cancel₀ _ (character_one_ne_zero ρ)]

theorem centralCharacter_mul_centerClassSum (K L : ConjClasses G) :
    Representation.centralCharacter ρ (centerClassSum ℂ K) *
        Representation.centralCharacter ρ (centerClassSum ℂ L)
      = ∑ M, (classStructureConstant K L M : ℂ) *
          Representation.centralCharacter ρ (centerClassSum ℂ M) := by
  rw [← map_mul]
  have h : centerClassSum ℂ K * centerClassSum ℂ L
      = ∑ M, (classStructureConstant K L M : ℂ) • centerClassSum ℂ M := by
    refine Subtype.ext ?_
    simp only [Subalgebra.coe_mul, coe_centerClassSum, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, coe_centerClassSum]
    exact classSum_mul_classSum K L
  rw [h, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem Representation.character_one_mul_sq_smodEq {t n : ℕ} {I : Finset (ConjClasses G)}
    (hI1 : (1 : ConjClasses G) ∉ I) (hcard : ∀ M ∈ I, Nat.card M.carrier = n)
    (hdvd : ∀ K ∈ I, ∀ L ∈ I, ∀ M : ConjClasses G, M ∉ I → M ≠ 1 →
      t ∣ classStructureConstant K L M * Nat.card M.carrier)
    {c : ℂ} (hc : ∀ x : G, ConjClasses.mk x ∈ I → ρ.character x = c)
    {K L : ConjClasses G} (hK : K ∈ I) (hL : L ∈ I) :
    ρ.character 1 * ((n : ℂ) * c / ρ.character 1) ^ 2 ≡
      ρ.character 1 * (classStructureConstant K L 1 : ℂ)
        + ρ.character 1 * ((n : ℂ) * c / ρ.character 1) *
          ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ)
      [SMOD algIntegerMultiples (t : ℂ)] := by
  have hωI : ∀ M ∈ I, Representation.centralCharacter ρ (centerClassSum ℂ M)
      = (n : ℂ) * c / ρ.character 1 := by
    intro M hM
    rw [centralCharacter_centerClassSum, hcard M hM,
      hc (classRep M) (by rw [mk_classRep]; exact hM)]
  have hω1 : Representation.centralCharacter ρ (centerClassSum ℂ (1 : ConjClasses G)) = 1 := by
    rw [centerClassSum_one, map_one]
  have key : ρ.character 1 * ((n : ℂ) * c / ρ.character 1) ^ 2
      = ∑ M, ρ.character 1 * ((classStructureConstant K L M : ℂ) *
          Representation.centralCharacter ρ (centerClassSum ℂ M)) := by
    have h := centralCharacter_mul_centerClassSum ρ K L
    rw [hωI K hK, hωI L hL] at h
    rw [← Finset.mul_sum, ← h, sq]
  have hsplit := Finset.sum_sdiff (f := fun M => ρ.character 1 *
      ((classStructureConstant K L M : ℂ) *
        Representation.centralCharacter ρ (centerClassSum ℂ M)))
      (Finset.subset_univ (insert (1 : ConjClasses G) I))
  rw [Finset.sum_insert hI1] at hsplit
  have h1 : ρ.character 1 * ((classStructureConstant K L 1 : ℂ) *
      Representation.centralCharacter ρ (centerClassSum ℂ (1 : ConjClasses G)))
      = ρ.character 1 * (classStructureConstant K L 1 : ℂ) := by rw [hω1, mul_one]
  have h2 : ∑ M ∈ I, ρ.character 1 * ((classStructureConstant K L M : ℂ) *
        Representation.centralCharacter ρ (centerClassSum ℂ M))
      = ρ.character 1 * ((n : ℂ) * c / ρ.character 1) *
        ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun M hM => by rw [hωI M hM]; ring
  have hdiff : ρ.character 1 * ((n : ℂ) * c / ρ.character 1) ^ 2 -
      (ρ.character 1 * (classStructureConstant K L 1 : ℂ)
        + ρ.character 1 * ((n : ℂ) * c / ρ.character 1) *
          ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ))
      = ∑ M ∈ Finset.univ \ insert (1 : ConjClasses G) I, ρ.character 1 *
          ((classStructureConstant K L M : ℂ) *
            Representation.centralCharacter ρ (centerClassSum ℂ M)) := by
    rw [key, ← hsplit, ← h1, ← h2]
    ring
  rw [SModEq.sub_mem, hdiff]
  refine Submodule.sum_mem _ fun M hM => ?_
  rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hM
  obtain ⟨-, hM1, hMI⟩ := hM
  obtain ⟨s, hs⟩ := hdvd K hK L hL M hMI hM1
  have hcast : (classStructureConstant K L M : ℂ) * (Nat.card M.carrier : ℂ)
      = (t : ℂ) * (s : ℂ) := by rw [← Nat.cast_mul, ← Nat.cast_mul, hs]
  refine mem_algIntegerMultiples_iff.2 ⟨(s : ℂ) * ρ.character (classRep M), ?_, ?_⟩
  · exact (isIntegral_natCast s).mul (Representation.isIntegral_character ρ _)
  · calc ρ.character 1 * ((classStructureConstant K L M : ℂ) *
          Representation.centralCharacter ρ (centerClassSum ℂ M))
        = (classStructureConstant K L M : ℂ) *
            (ρ.character 1 * Representation.centralCharacter ρ (centerClassSum ℂ M)) := by ring
      _ = (classStructureConstant K L M : ℂ) *
            ((Nat.card M.carrier : ℂ) * ρ.character (classRep M)) := by
        rw [character_one_mul_centralCharacter_centerClassSum]
      _ = (t : ℂ) * ((s : ℂ) * ρ.character (classRep M)) := by
        rw [← mul_assoc, hcast, mul_assoc]

theorem Irr.character_one_mul_sq_smodEq {φ : G → ℂ} (hφ : φ ∈ Irr G) {t n : ℕ}
    {I : Finset (ConjClasses G)} (hI1 : (1 : ConjClasses G) ∉ I)
    (hcard : ∀ M ∈ I, Nat.card M.carrier = n)
    (hdvd : ∀ K ∈ I, ∀ L ∈ I, ∀ M : ConjClasses G, M ∉ I → M ≠ 1 →
      t ∣ classStructureConstant K L M * Nat.card M.carrier)
    {c : ℂ} (hc : ∀ x : G, ConjClasses.mk x ∈ I → φ x = c)
    {K L : ConjClasses G} (hK : K ∈ I) (hL : L ∈ I) :
    φ 1 * ((n : ℂ) * c / φ 1) ^ 2 ≡
      φ 1 * (classStructureConstant K L 1 : ℂ)
        + φ 1 * ((n : ℂ) * c / φ 1) *
          ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ)
      [SMOD algIntegerMultiples (t : ℂ)] := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hφ
  have _i : Representation.IsIrreducible W.ρ := hW
  exact Representation.character_one_mul_sq_smodEq _ hI1 hcard hdvd hc hK hL

end CFSG.FeitThompson
