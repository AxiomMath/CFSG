module

public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwLift
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.LieType.Universal.Spin.PlusCT.Basic
public import CFSG.LieType.Universal.Spin.OddCT.Weyl
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainLModel
public import CFSG.ClassicalInvolution.Q3.Q3NHMain
public import CFSG.ClassicalInvolution.Q3.Q3NTUnitary
public import CFSG.ClassicalInvolution.Q3.Q3OFProd
public import CFSG.ClassicalInvolution.Q3.Q3OFUnique
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeShape
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd
public import CFSG.ClassicalInvolution.Q3.Q3URTransfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CliffordAlgebra QuadraticMap CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Frame

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

theorem neg_one_zpow_val_of_odd' {d : ℤ} (hd : Odd d) :
    (((-1 : Kˣ) ^ d : Kˣ) : K) = -1 := by
  rw [hd.neg_one_zpow]
  simp

theorem longSL2_congr' {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') {s t s' t' : Bool} (hs : s = s') (ht : t = t') :
    F.longSL2 hij s t = F.longSL2 hij' s' t' := by
  subst hi hj hs ht
  rfl

variable {a b c : Fin n}

theorem longWeyl_conj_torus_right (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    F.longWeyl hbc true false * F.longTorus hab true false (-1) * (F.longWeyl hbc true false)⁻¹ =
      F.longTorus hbc true false (-1) * F.longTorus hab true false (-1) := by
  have key := weylSL2_conj_of_conj (F.longSL2 hbc true false) (F.longTorus hab true false (-1))
    (-1) (fun c' => ?_) (fun c' => ?_)
  · have e : ((-1 : Kˣ))⁻¹ = -1 := by simp
    rw [e] at key
    exact key
  · rw [F.longSL2_upperSL2, F.longSL2_upperSL2,
      F.longTorus_conj_longRoot hab true false (-1) hbc true false c']
    have hexp : longCoroot a b true false b true + longCoroot a b true false c false = -1 := by
      simp [longCoroot, hab.symm, hac.symm, hbc.symm]
    rw [hexp, neg_one_zpow_val_of_odd' (by decide : Odd (-1 : ℤ))]
    simp
  · rw [F.longSL2_lowerSL2, F.longSL2_lowerSL2]
    simp only [Bool.not_false, Bool.not_true]
    rw [F.longTorus_conj_longRoot hab true false (-1) hbc.symm true false c']
    have hexp : longCoroot a b true false c true + longCoroot a b true false b false = 1 := by
      simp [longCoroot, hab.symm, hac.symm, hbc.symm]
    rw [hexp]
    simp

theorem longWeyl_conj_torus_left (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    F.longWeyl hab true false * F.longTorus hbc true false (-1) * (F.longWeyl hab true false)⁻¹ =
      F.longTorus hab true false (-1) * F.longTorus hbc true false (-1) := by
  have key := weylSL2_conj_of_conj (F.longSL2 hab true false) (F.longTorus hbc true false (-1))
    (-1) (fun c' => ?_) (fun c' => ?_)
  · have e : ((-1 : Kˣ))⁻¹ = -1 := by simp
    rw [e] at key
    exact key
  · rw [F.longSL2_upperSL2, F.longSL2_upperSL2,
      F.longTorus_conj_longRoot hbc true false (-1) hab true false c']
    have hexp : longCoroot b c true false a true + longCoroot b c true false b false = -1 := by
      simp [longCoroot, hab, hac, hbc]
    rw [hexp, neg_one_zpow_val_of_odd' (by decide : Odd (-1 : ℤ))]
    simp
  · rw [F.longSL2_lowerSL2, F.longSL2_lowerSL2]
    simp only [Bool.not_false, Bool.not_true]
    rw [F.longTorus_conj_longRoot hbc true false (-1) hab.symm true false c']
    have hexp : longCoroot b c true false b true + longCoroot b c true false a false = 1 := by
      simp [longCoroot, hab, hac, hbc]
    rw [hexp]
    simp

theorem torus_neg_one_sq (hab : a ≠ b) :
    F.longTorus hab true false (-1) * F.longTorus hab true false (-1) = 1 := by
  rw [← map_mul, neg_mul_neg, one_mul, map_one]

theorem torus_neg_one_ne_one (h2 : (2 : K) ≠ 0) (hab : a ≠ b) :
    F.longTorus hab true false (-1) ≠ 1 := by
  intro h
  have h1 := F.spinAction_longTorus_vec hab true false (-1) a true
  have hexp : longCoroot a b true false a true = 1 := by simp [longCoroot, hab]
  rw [h, map_one, hexp] at h1
  have h3 : F.vec a true = -F.vec a true := by simpa using h1
  have h4 : (2 : K) • F.vec a true = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h3]
    simp
  rcases smul_eq_zero.mp h4 with h5 | h5
  · exact h2 h5
  · have h6 := F.polar_vec_not a true
    rw [h5] at h6
    simp at h6

theorem torus_mem_range (hab : a ≠ b) :
    F.longTorus hab true false (-1) ∈ (F.longSL2 hab true false).range :=
  ⟨diagSL2 (-1), rfl⟩

end Frame

section Std


theorem parityData_of_klein {c : CompData} (hF : KindFund3 c) (hconj : FundConjClosed3 c)
    (hsingle : ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R)
    {R₀ : Subgroup c.G} (hR₀ : R₀ ∈ c.fund) {r₀ r₁ n₀ n₁ : c.G} (hr₀R : r₀ ∈ R₀)
    (hr₀2 : r₀ * r₀ = 1) (hr₀1 : r₀ ≠ 1) (hr₁2 : r₁ * r₁ = 1) (hcomm : r₀ * r₁ = r₁ * r₀)
    (hn₁ : n₁ * r₀ * n₁⁻¹ = r₁ * r₀) (hn₀ : n₀ * r₁ * n₀⁻¹ = r₀ * r₁) : ParityData c ⊥ := by
  refine ⟨hF, hconj, hsingle, bot_le, R₀, hR₀, r₀, hr₀R, hr₀2, hr₀1, {r₁, r₁ * r₀}, ?_, 1,
    Subgroup.one_mem _, ?_⟩
  · intro w hw
    rcases hw with hw | hw
    · rw [hw]
      refine ⟨⟨n₀⁻¹ * n₁, ?_⟩, ?_⟩
      · calc r₁ = n₀⁻¹ * (n₀ * r₁ * n₀⁻¹) * n₀ := by group
          _ = n₀⁻¹ * (r₁ * r₀) * n₀ := by rw [hn₀, hcomm]
          _ = n₀⁻¹ * (n₁ * r₀ * n₁⁻¹) * n₀ := by rw [hn₁]
          _ = n₀⁻¹ * n₁ * r₀ * (n₀⁻¹ * n₁)⁻¹ := by group
      · rw [Subgroup.mem_bot]
        calc r₁ * r₀ * r₁⁻¹ * r₀⁻¹ = (r₀ * r₁) * r₁⁻¹ * r₀⁻¹ := by rw [hcomm]
          _ = 1 := by group
    · rw [Set.mem_singleton_iff.mp hw]
      refine ⟨⟨n₁, hn₁.symm⟩, ?_⟩
      rw [Subgroup.mem_bot]
      calc r₁ * r₀ * r₀ * (r₁ * r₀)⁻¹ * r₀⁻¹ = r₁ * r₀ * r₁⁻¹ * r₀⁻¹ := by group
        _ = (r₀ * r₁) * r₁⁻¹ * r₀⁻¹ := by rw [← hcomm]
        _ = 1 := by group
  · refine Subgroup.subset_closure ⟨r₁, ?_, r₁ * r₀, ?_, ?_⟩
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · calc r₁ * (r₁ * r₀) = (r₁ * r₁) * r₀ := (mul_assoc _ _ _).symm
        _ = r₀ * 1 := by rw [hr₁2, one_mul, mul_one]

end Std

section Families

open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


theorem klein_std_odd {n : ℕ} (hn3 : 3 ≤ n)
    (hlong : IsLongestRoot (oddDatum n 𝔽₃) (Pi.single (⟨0, by omega⟩ : Fin n) 1)) :
    ∃ R₀ ∈ fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃), ∃ r₀ ∈ R₀,
      ∃ r₁ n₀ n₁ : spinGroup (quadOdd n 𝔽₃), r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧
        r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧ n₀ * r₁ * n₀⁻¹ = r₀ * r₁ := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  set F := (oddFrame n 𝔽₃).toHypFrame with hF
  have hk : (0 : ℕ) + 1 < n := by omega
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b = ⟨1, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c = ⟨2, by omega⟩ := ⟨_, rfl⟩
  have hab : a ≠ b := by rw [ha, hb]; simp [Fin.ext_iff]
  have hbc : b ≠ c := by rw [hb, hc]; simp [Fin.ext_iff]
  have hac : a ≠ c := by rw [ha, hc]; simp [Fin.ext_iff]
  have hr : rankOneB 𝔽₃ a = F.longSL2 hab true false :=
    rankOneB_of_lt 𝔽₃ (k := a) (by rw [ha]; exact hk) (j := b) (by rw [ha, hb]) hab
  refine ⟨rankOne (oddDatum n 𝔽₃).rootGroup a, ?_, F.longTorus hab true false (-1), ?_,
    F.longTorus hbc true false (-1), F.longWeyl hab true false, F.longWeyl hbc true false,
    torus_neg_one_sq F hab, torus_neg_one_ne_one F h2 hab, torus_neg_one_sq F hbc,
    (F.commute_longTorus_longTorus hab true false (-1) hbc true false (-1)).eq,
    longWeyl_conj_torus_right F hab hbc hac, longWeyl_conj_torus_left F hab hbc hac⟩
  · refine ⟨1, Pi.single a 1, Or.inl ?_, by ext y; simp [rankOne]⟩
    rw [ha]
    exact hlong
  · have := OddCT.rankOneB_mem_rankOne (K := 𝔽₃) a (diagSL2 (-1 : 𝔽₃ˣ))
    rw [hr] at this
    exact this

theorem klein_std_plus {n : ℕ} (hn3 : 3 ≤ n)
    (hlong : IsLongestRoot (plusDatum n 𝔽₃ hn3) (Pi.single (⟨0, by omega⟩ : Fin n) 1)) :
    ∃ R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum n 𝔽₃ hn3), ∃ r₀ ∈ R₀,
      ∃ r₁ n₀ n₁ : spinGroup (quadPlus n 𝔽₃), r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧
        r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧ n₀ * r₁ * n₀⁻¹ = r₀ * r₁ := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  set F := plusFrame n 𝔽₃ hn3 with hF
  have hk : (0 : ℕ) + 1 < n := by omega
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b = ⟨1, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c = ⟨2, by omega⟩ := ⟨_, rfl⟩
  have hab : a ≠ b := by rw [ha, hb]; simp [Fin.ext_iff]
  have hbc : b ≠ c := by rw [hb, hc]; simp [Fin.ext_iff]
  have hac : a ≠ c := by rw [ha, hc]; simp [Fin.ext_iff]
  have hk' : a.val + 1 < n := by rw [ha]; exact hk
  have hr : rankOneD 𝔽₃ hn3 a = F.longSL2 hab true false :=
    longSL2_congr' F (rootIdxD_ne n (by omega) a) hab (rootIdxD_of_lt n hk')
      (by apply Fin.ext; rw [rootIdxD'_of_lt n hk']; simp [ha, hb]) rfl (rootSignD_of_lt n hk')
  refine ⟨rankOne (plusDatum n 𝔽₃ hn3).rootGroup a, ?_, F.longTorus hab true false (-1), ?_,
    F.longTorus hbc true false (-1), F.longWeyl hab true false, F.longWeyl hbc true false,
    torus_neg_one_sq F hab, torus_neg_one_ne_one F h2 hab, torus_neg_one_sq F hbc,
    (F.commute_longTorus_longTorus hab true false (-1) hbc true false (-1)).eq,
    longWeyl_conj_torus_right F hab hbc hac, longWeyl_conj_torus_left F hab hbc hac⟩
  · refine ⟨1, Pi.single a 1, Or.inl ?_, by ext y; simp [rankOne]⟩
    rw [ha]
    exact hlong
  · have := PlusCT.rankOneD_mem_rankOne (K := 𝔽₃) hn3 a (diagSL2 (-1 : 𝔽₃ˣ))
    rw [hr] at this
    exact this

theorem klein_std_minus {n : ℕ} (hn4 : 4 ≤ n)
    (hlong : IsLongestRoot (Twisted.minusDatum n (minusCoeffs_irr 3 1))
      (Pi.single (⟨0, by omega⟩ : Fin (n - 1)) 1)) :
    ∃ R₀ ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr 3 1)),
      ∃ r₀ ∈ R₀, ∃ r₁ n₀ n₁ : spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧
        r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧ n₀ * r₁ * n₀⁻¹ = r₀ * r₁ := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  set F := (Twisted.minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame with hF
  have hk : (0 : ℕ) + 1 < n - 1 := by omega
  obtain ⟨a, ha⟩ : ∃ a : Fin (n - 1), a = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (n - 1), b = ⟨1, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (n - 1), c = ⟨2, by omega⟩ := ⟨_, rfl⟩
  have hab : a ≠ b := by rw [ha, hb]; simp [Fin.ext_iff]
  have hbc : b ≠ c := by rw [hb, hc]; simp [Fin.ext_iff]
  have hac : a ≠ c := by rw [ha, hc]; simp [Fin.ext_iff]
  have hk' : a.val + 1 < n - 1 := by rw [ha]; exact hk
  have hR := Twisted.rankOne_minusRootGroup_of_lt n (minusCoeffs_irr 3 1) hk'
  have hr : F.longSL2 (Twisted.succ_ne_of_lt n hk') true false = F.longSL2 hab true false :=
    longSL2_congr' F _ hab rfl (by apply Fin.ext; simp [ha, hb]) rfl rfl
  refine ⟨rankOne (Twisted.minusDatum n (minusCoeffs_irr 3 1)).rootGroup a, ?_,
    F.longTorus hab true false (-1), ?_, F.longTorus hbc true false (-1),
    F.longWeyl hab true false, F.longWeyl hbc true false,
    torus_neg_one_sq F hab, torus_neg_one_ne_one F h2 hab, torus_neg_one_sq F hbc,
    (F.commute_longTorus_longTorus hab true false (-1) hbc true false (-1)).eq,
    longWeyl_conj_torus_right F hab hbc hac, longWeyl_conj_torus_left F hab hbc hac⟩
  · refine ⟨1, Pi.single a 1, Or.inl ?_, by ext y; simp [rankOne]⟩
    rw [ha]
    exact hlong
  · show F.longTorus hab true false (-1) ∈ rankOne (Twisted.minusRootGroup n
      (minusCoeffs_irr 3 1)) a
    rw [hR, hr]
    exact torus_mem_range F hab

theorem parityData_pOmegaOdd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    ParityData (CompData.model .POmegaOdd n) ⊥ := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hft : IsFundTag .POmegaOdd := trivial
  have hF : KindFund3 (CompData.model .POmegaOdd n) :=
    kindFund3_model hft hadm (by decide) (by decide)
  have hconj : FundConjClosed3 (CompData.model .POmegaOdd n) := fundConjClosed3_model _ _
  have hsingle : ∀ R ∈ (CompData.model .POmegaOdd n).fund,
      ∀ R' ∈ (CompData.model .POmegaOdd n).fund,
        ∃ g : (CompData.model .POmegaOdd n).G, R' = conjSub g R :=
    Q3W.EX.singleClass_of_kind rfl hft hadm (by decide) (by decide)
  have hlong : ∀ k : Fin (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D.rank, k.val + 1 < n →
      IsLongestRoot (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k hk => ModelFacts.isLongestRoot_single .POmegaOdd n 3 1 Nat.prime_three trivial hadm k hk
  have hM : modelUniv .POmegaOdd n 3 1 Nat.prime_three =
      ⟨spinGroup (quadOdd n 𝔽₃), oddDatum n 𝔽₃⟩ := rfl
  obtain ⟨R₀, hR₀, r₀, hr₀R, r₁, n₀, n₁, h1, h2, h3, h4, h5, h6⟩ :
      ∃ R₀ ∈ (CompData.model .POmegaOdd n).fund, ∃ r₀ ∈ R₀,
        ∃ r₁ n₀ n₁ : (CompData.model .POmegaOdd n).G, r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧
          r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧ n₀ * r₁ * n₀⁻¹ = r₀ * r₁ := by
    suffices h : ∀ M : LieUniversal, M = ⟨spinGroup (quadOdd n 𝔽₃), oddDatum n 𝔽₃⟩ →
        (∀ k : Fin M.D.rank, k.val + 1 < n → IsLongestRoot M.D (Pi.single k 1)) →
        ∃ R₀ ∈ fundamentalSubgroups .POmegaOdd M.D, ∃ r₀ ∈ R₀, ∃ r₁ n₀ n₁ : M.K,
          r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧ r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧
            n₀ * r₁ * n₀⁻¹ = r₀ * r₁ from h _ hM hlong
    intro M hM' hlongM
    subst hM'
    exact klein_std_odd hn3 (hlongM ⟨0, by show 0 < n; omega⟩ (by show 0 + 1 < n; omega))
  exact parityData_of_klein hF hconj hsingle hR₀ hr₀R h1 h2 h3 h4 h5 h6

theorem parityData_pOmegaPlus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1) :
    ParityData (CompData.model .POmegaPlus n) ⊥ := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hft : IsFundTag .POmegaPlus := trivial
  have hF : KindFund3 (CompData.model .POmegaPlus n) :=
    kindFund3_model hft hadm (by decide) (by decide)
  have hconj : FundConjClosed3 (CompData.model .POmegaPlus n) := fundConjClosed3_model _ _
  have hsingle : ∀ R ∈ (CompData.model .POmegaPlus n).fund,
      ∀ R' ∈ (CompData.model .POmegaPlus n).fund,
        ∃ g : (CompData.model .POmegaPlus n).G, R' = conjSub g R :=
    Q3W.EX.singleClass_of_kind rfl hft hadm (by decide) (by decide)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k => ModelFacts.isLongestRoot_single .POmegaPlus n 3 1 Nat.prime_three trivial hadm k
      trivial
  have hM : modelUniv .POmegaPlus n 3 1 Nat.prime_three =
      ⟨spinGroup (quadPlus n 𝔽₃), plusDatum n 𝔽₃ hn3⟩ :=
    (rfl : modelUniv .POmegaPlus n 3 1 Nat.prime_three =
      ModelFacts.modelUniv .POmegaPlus n 3 1 Nat.prime_three).trans
      (ModelFacts.modelUniv_POmegaPlus hn3)
  obtain ⟨R₀, hR₀, r₀, hr₀R, r₁, n₀, n₁, h1, h2, h3, h4, h5, h6⟩ :
      ∃ R₀ ∈ (CompData.model .POmegaPlus n).fund, ∃ r₀ ∈ R₀,
        ∃ r₁ n₀ n₁ : (CompData.model .POmegaPlus n).G, r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧
          r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧ n₀ * r₁ * n₀⁻¹ = r₀ * r₁ := by
    suffices h : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n 𝔽₃), plusDatum n 𝔽₃ hn3⟩ →
        (∀ k : Fin M.D.rank, IsLongestRoot M.D (Pi.single k 1)) →
        ∃ R₀ ∈ fundamentalSubgroups .POmegaPlus M.D, ∃ r₀ ∈ R₀, ∃ r₁ n₀ n₁ : M.K,
          r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧ r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧
            n₀ * r₁ * n₀⁻¹ = r₀ * r₁ from h _ hM hlong
    intro M hM' hlongM
    subst hM'
    exact klein_std_plus hn3 (hlongM ⟨0, by show 0 < n; omega⟩)
  exact parityData_of_klein hF hconj hsingle hR₀ hr₀R h1 h2 h3 h4 h5 h6

theorem parityData_pOmegaMinus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    ParityData (CompData.model .POmegaMinus n) ⊥ := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hft : IsFundTag .POmegaMinus := trivial
  have hF : KindFund3 (CompData.model .POmegaMinus n) :=
    kindFund3_model hft hadm (by decide) (by decide)
  have hconj : FundConjClosed3 (CompData.model .POmegaMinus n) := fundConjClosed3_model _ _
  have hsingle : ∀ R ∈ (CompData.model .POmegaMinus n).fund,
      ∀ R' ∈ (CompData.model .POmegaMinus n).fund,
        ∃ g : (CompData.model .POmegaMinus n).G, R' = conjSub g R :=
    Q3W.EX.singleClass_of_kind rfl hft hadm (by decide) (by decide)
  have hlong : ∀ k : Fin (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D.rank, k.val + 2 < n →
      IsLongestRoot (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k hk => ModelFacts.isLongestRoot_single .POmegaMinus n 3 1 Nat.prime_three trivial hadm k
      hk
  have hM : modelUniv .POmegaMinus n 3 1 Nat.prime_three =
      ⟨spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        Twisted.minusDatum n (minusCoeffs_irr 3 1)⟩ := rfl
  obtain ⟨R₀, hR₀, r₀, hr₀R, r₁, n₀, n₁, h1, h2, h3, h4, h5, h6⟩ :
      ∃ R₀ ∈ (CompData.model .POmegaMinus n).fund, ∃ r₀ ∈ R₀,
        ∃ r₁ n₀ n₁ : (CompData.model .POmegaMinus n).G, r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧
          r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧ n₀ * r₁ * n₀⁻¹ = r₀ * r₁ := by
    suffices h : ∀ M : LieUniversal, M =
        ⟨spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
          Twisted.minusDatum n (minusCoeffs_irr 3 1)⟩ →
        (∀ k : Fin M.D.rank, k.val + 2 < n → IsLongestRoot M.D (Pi.single k 1)) →
        ∃ R₀ ∈ fundamentalSubgroups .POmegaMinus M.D, ∃ r₀ ∈ R₀, ∃ r₁ n₀ n₁ : M.K,
          r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₁ * r₁ = 1 ∧ r₀ * r₁ = r₁ * r₀ ∧ n₁ * r₀ * n₁⁻¹ = r₁ * r₀ ∧
            n₀ * r₁ * n₀⁻¹ = r₀ * r₁ from h _ hM hlong
    intro M hM' hlongM
    subst hM'
    exact klein_std_minus hn4 (hlongM ⟨0, by show 0 < n - 1; omega⟩
      (by show 0 + 2 < n; omega))
  exact parityData_of_klein hF hconj hsingle hR₀ hr₀R h1 h2 h3 h4 h5 h6

end Families

end CFSG.ClassicalInvolution.Q3.Q3OF
