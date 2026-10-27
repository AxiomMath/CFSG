module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.ClassicalInvolution

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OutcomeLocal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL

theorem noNonsolvableClassical_projectiveSL {f n : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n)
    {k : Type*} [Field k] (hk : Nat.card k = 2 ^ f) :
    NoNonsolvableClassical (projectiveSL n k) := by
  classical
  intro t ht
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin n) k) := inferInstance
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨s, rfl, hs⟩ := exists_sl_lift t htt
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  set U := flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs) with hUdef
  set Q := U.map (proj n k) with hQdef
  have hlift : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)),
      ∃ A : SpecialLinearGroup (Fin n) k, proj n k A = c ∧ A * s = s * A := by
    intro c hc
    obtain ⟨A, rfl⟩ := proj_surjective n k c
    exact ⟨A, rfl, commute_of_proj_commute hs (mem_centralizer_singleton_iff.mp hc)⟩
  have hQC : Q ≤ centralizer ({proj n k s} : Set (projectiveSL n k)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, commute_of_mem_flagKernel hs hu]
  have hQp : IsPGroup 2 Q := isPGroup_flagKernel.map (proj n k)
  have hnorm : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)), ∀ q ∈ Q,
      c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨A, rfl, hAs⟩ := hlift c hc
    obtain ⟨u, hu, rfl⟩ := hq
    exact ⟨A * u * A⁻¹, conj_mem_flagKernel hs hAs hu, by rw [map_mul, map_mul, map_inv]⟩
  refine (NoNonsolvableClassicalAt.of_normal_pGroup_le hQC hQp hnorm (fun c hc hcQ => ?_)) ht
  obtain ⟨A, rfl, hAs⟩ := hlift c hc
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  ·
    obtain rfl : n = 2 := by omega
    exact ⟨A, mem_flagKernel_of_commute_two hs hs1 hAs, rfl⟩
  · exact mem_map_flagKernel_of_commute hn3 hf hk (dispRange_ne_bot hs1)
      (dispRange_le_dispKer hs) (dispKer_ne_top hs1)
      fun u hu => hcQ _ ⟨u, hu, rfl⟩

theorem noNonsolvableClassical_of_psl_model {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSL n 2 f) : NoNonsolvableClassical X := by
  obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  let e' : X ≃* LinearFlag.projectiveSL n K :=
    eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  exact NoNonsolvableClassical.of_mulEquiv e' (noNonsolvableClassical_projectiveSL hf hn hK)

end CFSG.ClassicalInvolution
