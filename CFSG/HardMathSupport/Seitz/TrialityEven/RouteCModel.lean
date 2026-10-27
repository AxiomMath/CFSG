module

public import CFSG.HardMathSupport.Seitz.TrialityEven.Interface
public import CFSG.RankThree.PartOne.D4RC.Phi6
public import CFSG.RankThree.PartOne.SEITZ7.D4CentN

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Census3 (IsoLie)


theorem closure_cenGen_routeC_even {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrd : (r : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * ((2 ^ f : ℕ) : ℤ) + 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.IsElementaryAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  let q : PrimePower := ⟨2, f, Nat.prime_two, hf⟩
  have hv : (LieTypeIndex.trialityD4 q).Valid := LieTypeIndex.valid_trialityD4 q
  obtain ⟨e⟩ := nonempty_catEquiv_graphFixedRootGroup_even (q := q) rfl hv K hK σ hσ
  obtain ⟨-, hsimp⟩ := finite_isSimpleGroup_cat_trialityD4 hv
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulEquiv.isSimpleGroup e.symm
  have hiso : IsoLie (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (.trialityD4 q) :=
    ⟨hv, ⟨e.symm⟩⟩
  have hqc : q.card = 2 ^ f := PrimePower.card_def q
  have hp36 : r ∣ q.card ^ 2 + q.card + 1 ∨ r ∣ q.card ^ 2 - q.card + 1 := by
    rcases hε with rfl | rfl
    · left
      rw [hqc]
      have h : (r : ℤ) ∣ (((2 ^ f) ^ 2 + 2 ^ f + 1 : ℕ) : ℤ) := by
        push_cast at hrd ⊢
        simpa using hrd
      exact_mod_cast h
    · right
      rw [hqc]
      have hle : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
      have h : (r : ℤ) ∣ (((2 ^ f) ^ 2 - 2 ^ f + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub hle]
        push_cast at hrd ⊢
        simpa [sub_eq_add_neg] using hrd
      exact_mod_cast h
  exact SEITZ7.closure_cenGen_trialityD4_phi36_eq_top_N D4RC.rc6_max3D4CentN rfl hiso hr hr5 hp36
    E hE hEcard

end CFSG.HardMathSupport.Seitz.TrialityEven
