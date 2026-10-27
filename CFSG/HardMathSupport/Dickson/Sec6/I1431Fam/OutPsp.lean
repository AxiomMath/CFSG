module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Low
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.Sec66T
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (conjAut fieldAut gsp multiplier conjAut_mem_inner_of_isSquare)
open scoped commutatorElement

theorem t6outpsp_commutator_le_of_eq_mul_comm {G : Type*} [Group G] (N F : Subgroup G) [N.Normal]
    (hgen : ∀ g : G, ∃ n ∈ N, ∃ f ∈ F, g = n * f)
    (hF : ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ * f₂ = f₂ * f₁) :
    commutator G ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨n₁, hn₁, f₁, hf₁, rfl⟩ := hgen a
  obtain ⟨n₂, hn₂, f₂, hf₂, rfl⟩ := hgen b
  have hπ : ∀ n ∈ N, QuotientGroup.mk' N n = 1 := fun n hn => (QuotientGroup.eq_one_iff n).2 hn
  have h1 : (QuotientGroup.mk' N) ⁅n₁ * f₁, n₂ * f₂⁆ = 1 := by
    rw [map_commutatorElement, map_mul, map_mul, hπ n₁ hn₁, hπ n₂ hn₂, one_mul, one_mul,
      ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (hF f₁ hf₁ f₂ hf₂),
      map_one]
  exact (QuotientGroup.eq_one_iff _).1 h1

section Core

variable {K : Type} [Field K] [Finite K]

theorem t6outpsp_commutator_le_odd (hodd : ringChar K ≠ 2) :
    commutator (MulAut (StatedProj (StatedSp 2 K))) ≤ (conjAut 2 K).range := by
  haveI : ((conjAut 2 K).range : Subgroup (MulAut (StatedProj (StatedSp 2 K)))).Normal :=
    (stdPinnedPSp_two_stable hodd).normal
  refine t6outpsp_commutator_le_of_eq_mul_comm _ (fieldAut 2 K).range ?_ ?_
  · intro g
    obtain ⟨A, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd g
    exact ⟨_, ⟨A, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]

theorem t6outpsp_commutator_le_even [CharP K 2] :
    commutator (MulAut (StatedProj (StatedSp 2 K))) ≤ (conjAut 2 K).range := by
  haveI := range_conjAut_normal_of_charTwo (F := K)
  set τ₀ : MulAut (StatedProj (StatedSp 2 K)) := CFSG.QuasithinUnique.Lin2.Five.tauAut
  set S : Set (MulAut (StatedProj (StatedSp 2 K))) := Set.range (fieldAut 2 K) ∪ {τ₀}
  have hS : S.Pairwise Commute := by
    rintro a (⟨σ, rfl⟩ | rfl) b (⟨τ, rfl⟩ | rfl) -
    · change fieldAut 2 K σ * fieldAut 2 K τ = fieldAut 2 K τ * fieldAut 2 K σ
      rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
    · exact (tauAut_mul_fieldAut σ).symm
    · exact tauAut_mul_fieldAut τ
    · exact Commute.refl _
  have hcomm := Subgroup.isMulCommutative_closure hS
  have hσmem : ∀ σ : K ≃+* K, fieldAut 2 K σ ∈ Subgroup.closure S := fun σ =>
    Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
  have hτmem : τ₀ ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  refine t6outpsp_commutator_le_of_eq_mul_comm _ (Subgroup.closure S) ?_ ?_
  · intro g
    obtain ⟨A, σ, ε, -, rfl⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow g
    exact ⟨_, ⟨A, rfl⟩, fieldAut 2 K σ * τ₀ ^ ε, mul_mem (hσmem σ) (pow_mem hτmem ε),
      mul_assoc _ _ _⟩
  · intro f₁ hf₁ f₂ hf₂
    exact congrArg Subtype.val (hcomm.is_comm.comm (⟨f₁, hf₁⟩ : Subgroup.closure S) ⟨f₂, hf₂⟩)

theorem t6outpsp_commutator_le_conjAut_range :
    commutator (MulAut (StatedProj (StatedSp 2 K))) ≤ (conjAut 2 K).range := by
  by_cases h2 : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq h2
    exact t6outpsp_commutator_le_even
  · exact t6outpsp_commutator_le_odd h2

theorem t6outpsp_innAutDerived_le_conjAut_range :
    innAutDerived (StatedProj (StatedSp 2 K)) ≤ (conjAut 2 K).range :=
  sup_le (innAut_le_range_spConjAut 2 K) t6outpsp_commutator_le_conjAut_range

theorem t6outpsp_isInnerAut_of_mem_innAutDerived {τ : MulAut (StatedProj (StatedSp 2 K))}
    (hτ : τ ∈ innAutDerived (StatedProj (StatedSp 2 K))) (h3 : τ ^ 3 = 1) : IsInnerAut τ := by
  obtain ⟨A, rfl⟩ := t6outpsp_innAutDerived_le_conjAut_range hτ
  have h4A : conjAut 2 K A = conjAut 2 K (A ^ 2) ^ 2 := by
    rw [← map_pow, ← pow_mul, map_pow]
    calc conjAut 2 K A = conjAut 2 K A ^ 3 * conjAut 2 K A := by rw [h3, one_mul]
      _ = conjAut 2 K A ^ (2 * 2) := by rw [← pow_succ]
  rw [IsInnerAut, h4A]
  refine Subgroup.pow_mem _ (conjAut_mem_inner_of_isSquare ⟨(multiplier 2 K A : K), ?_⟩) 2
  rw [map_pow, Units.val_pow_eq_pow_val, sq]

end Core

theorem outDerived3_pspLow : OutDerived3At FamPspLow := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain ⟨rfl, rfl, -⟩ := hF
  have hC : StatedClassicalModel P .PSp 2 p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hC
  have h1 : MulAut.congr e τ ∈ innAutDerived (StatedProj (StatedSp 2 K)) :=
    (mem_innAutDerived_congr e).2 hτ
  have h3 : (MulAut.congr e τ) ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
  exact (isInnerAut_congr e τ).1 (t6outpsp_isInnerAut_of_mem_innAutDerived h1 h3)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
