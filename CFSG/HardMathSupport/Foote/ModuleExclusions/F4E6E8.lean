module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.G2General
public import CFSG.HardMathSupport.Foote.ModuleExclusions.ExcSigns
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.CGT6M

section Toral

variable {K L : Type} [Field K] [Field L]

theorem exc_invData_of_toral
    [CharP K 5] {τ : Tag} (ι : K →+* L) (w : ↥(adjointGroup τ K)) (a : Fin τ.rank → Lˣ)
    (hw : baseChangeGL ι (w : ModGL τ K) = rootDiagUnit τ a)
    (hpair : ∃ α β : Fin τ.rank → ℤ, IsRoot τ α ∧ IsRoot τ β ∧ 0 < height α ∧ 0 < height β ∧
      α ≠ β ∧ 0 ≤ iform α β ∧ ¬ IsRoot τ (α + β) ∧ rootChar a α = -1 ∧ rootChar a β = -1) :
    InvData ↥(adjointGroup τ K) w := by
  obtain ⟨α, β, hαr, hβr, hhα, hhβ, hne, h0, hnot, hα, hβ⟩ := hpair
  let X : ↥(adjointGroup τ K) := ⟨pinnedX τ K α 1, pinnedX_mem_adjointGroup α 1⟩
  let Y : ↥(adjointGroup τ K) := ⟨pinnedX τ K β 1, pinnedX_mem_adjointGroup β 1⟩
  have hXn : ∀ n : ℕ, ((X ^ n : ↥(adjointGroup τ K)) : ModGL τ K) =
      pinnedX τ K α (n : K) := fun n => by
    rw [Subgroup.coe_pow]
    exact pinnedX_one_pow K α n
  have hYn : ∀ n : ℕ, ((Y ^ n : ↥(adjointGroup τ K)) : ModGL τ K) =
      pinnedX τ K β (n : K) := fun n => by
    rw [Subgroup.coe_pow]
    exact pinnedX_one_pow K β n
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  refine invData_of_pair (X := X) (Y := Y) ?_ ?_ ?_ ?_ (toral_inverts_pinnedX ι w a hw hαr hα)
    (toral_inverts_pinnedX ι w a hw hβr hβ)
  · refine Subtype.ext ?_
    rw [hXn]
    simp [h5, pinnedX_zero]
  · refine Subtype.ext ?_
    rw [hYn]
    simp [h5, pinnedX_zero]
  · exact Subtype.ext (pinnedX_commute_of_iform_nonneg K hαr hβr hne h0 hnot 1 1)
  · intro i j hij
    have h1 : pinnedX τ K α ((i.val : ℕ) : K) * pinnedX τ K β ((j.val : ℕ) : K) =
        pinnedX τ K α 0 * pinnedX τ K β 0 := by
      rw [pinnedX_zero, pinnedX_zero, mul_one, ← hXn, ← hYn]
      exact congrArg Subtype.val hij
    obtain ⟨hi, hj⟩ := pinnedX_pair_inj K ⟨hαr, hhα⟩ ⟨hβr, hhβ⟩ hne h1
    exact ⟨zmod_eq_zero_of_cast_eq_zero hi, zmod_eq_zero_of_cast_eq_zero hj⟩

end Toral

section Main

variable {K : Type} [Field K] [Finite K]

theorem f4_invData_charFive
    {K : Type} [Field K] [Finite K] {f : ℕ} (hKc : Nat.card K = 5 ^ f)
    (t : ↥(adjointGroup Tag.F4 K)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    InvData ↥(adjointGroup Tag.F4 K) t := by
  have : CharP K 5 := charP_five_of_natCard hKc
  refine invData_charFive_of_toral (τ := Tag.F4) (by simp) hKc ?_ t ht1 ht2
  intro ι w a ha ha1 hw
  exact exc_invData_of_toral ι w a hw (exists_pair_rootChar f4_signCheck f4_length a ha ha1)

theorem coverInv_f4_charFive
    (hECS : ExceptionalCenterSmallPrimes) {f : ℕ} (Q : Type) [Group Q]
    (hQ : ChevalleyExceptionalModel Q .F4 5 f) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e0⟩⟩ := hQ
  obtain ⟨K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.F4
    (⟨K, hKf, hKfin, hKc, ⟨e0⟩⟩ : UntwistedChevalleyModel Q .F4 (5 ^ f))
  refine coverInv_of_invData hECS (t := .F4) (f := f) (by simp [chevalleyExceptionalTags])
    (fun L _ ⟨e'⟩ => ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e0⟩⟩) (fun w hw1 hw2 => ?_)
  have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
  have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  exact invData_of_equiv e (f4_invData_charFive hK'c (e w) hew1 hew2)

theorem e6_invData_charFive
    {K : Type} [Field K] [Finite K] {f : ℕ} (hKc : Nat.card K = 5 ^ f)
    (t : ↥(adjointGroup Tag.E6 K)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    InvData ↥(adjointGroup Tag.E6 K) t := by
  have : CharP K 5 := charP_five_of_natCard hKc
  refine invData_charFive_of_toral (τ := Tag.E6) (by simp) hKc ?_ t ht1 ht2
  intro ι w a ha ha1 hw
  exact exc_invData_of_toral ι w a hw (exists_pair_rootChar e6_signCheck e6_length a ha ha1)

theorem coverInv_e6_charFive
    (hECS : ExceptionalCenterSmallPrimes) {f : ℕ} (Q : Type) [Group Q]
    (hQ : ChevalleyExceptionalModel Q .E6 5 f) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e0⟩⟩ := hQ
  obtain ⟨K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E6
    (⟨K, hKf, hKfin, hKc, ⟨e0⟩⟩ : UntwistedChevalleyModel Q .E6 (5 ^ f))
  refine coverInv_of_invData hECS (t := .E6) (f := f) (by simp [chevalleyExceptionalTags])
    (fun L _ ⟨e'⟩ => ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e0⟩⟩) (fun w hw1 hw2 => ?_)
  have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
  have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  exact invData_of_equiv e (e6_invData_charFive hK'c (e w) hew1 hew2)

theorem e8_invData_charFive
    {K : Type} [Field K] [Finite K] {f : ℕ} (hKc : Nat.card K = 5 ^ f)
    (t : ↥(adjointGroup Tag.E8 K)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    InvData ↥(adjointGroup Tag.E8 K) t := by
  have : CharP K 5 := charP_five_of_natCard hKc
  refine invData_charFive_of_toral (τ := Tag.E8) (by simp) hKc ?_ t ht1 ht2
  intro ι w a ha ha1 hw
  exact exc_invData_of_toral ι w a hw (exists_pair_rootChar e8_signCheck e8_length a ha ha1)

theorem coverInv_e8_charFive
    (hECS : ExceptionalCenterSmallPrimes) {f : ℕ} (Q : Type) [Group Q]
    (hQ : ChevalleyExceptionalModel Q .E8 5 f) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e0⟩⟩ := hQ
  obtain ⟨K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E8
    (⟨K, hKf, hKfin, hKc, ⟨e0⟩⟩ : UntwistedChevalleyModel Q .E8 (5 ^ f))
  refine coverInv_of_invData hECS (t := .E8) (f := f) (by simp [chevalleyExceptionalTags])
    (fun L _ ⟨e'⟩ => ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e0⟩⟩) (fun w hw1 hw2 => ?_)
  have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
  have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  exact invData_of_equiv e (e8_invData_charFive hK'c (e w) hew1 hew2)

end Main

end CFSG.HardMathSupport.Foote.ModuleExclusions
