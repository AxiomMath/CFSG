module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.LinHeisOdd
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo

section Linear

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem isLocallyBalancedAbs_two_projectiveSL_odd (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F) (hnp : p ∣ Nat.card F - 1 → n ≠ p)
    (hplane : ¬ p ∣ Nat.card F - 1 → InnerPlaneBalance p (projectiveSL n F)) :
    IsLocallyBalancedAbs p 2 (projectiveSL n F) := by
  have hHeis := linHeisenbergBalanceOdd_holds
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro D hD hcard H hH _
  by_cases hDl : D ≤ linearAutGroup n F
  · by_cases hq : p ∣ Nat.card F - 1
    · obtain ⟨y₁, hy₁D, y₂, hy₂D, hy₁, hy₂, hgen⟩ := exists_gens_of_plane hp hD hcard
      obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hDl hy₁D)
      obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 (hDl hy₂D)
      have hA' : conjAut n F A = y₁ := hA
      have hB' : conjAut n F B = y₂ := hB
      rw [hgen, ← hA', ← hB']
      rw [← hA'] at hy₁ hy₂
      rw [← hB'] at hy₂
      have hcomm : conjAut n F A * conjAut n F B = conjAut n F B * conjAut n F A := by
        rw [hA', hB']
        exact congrArg Subtype.val (hD.1.is_comm.comm ⟨y₁, hy₁D⟩ ⟨y₂, hy₂D⟩)
      have hAp : conjAut n F A ^ p = 1 := by rw [hA']; exact hD.2 y₁ hy₁D
      have hBp : conjAut n F B ^ p = 1 := by rw [hB']; exact hD.2 y₂ hy₂D
      by_cases hAB : A * B = B * A
      · exact localDeltaIn_eq_bot_of_comm_lifts hn hp hp2 hq hAB hAp hBp hy₁ hy₂ hH
      · exact hHeis n F hn p hp hp2 hq (hnp hq) A B hAB hcomm hAp hBp H hH
    · have hpg : ¬ p ∣ Nat.gcd n (Nat.card F - 1) := fun h => hq (h.trans (Nat.gcd_dvd_right _ _))
      refine hplane hq D (fun x hx => ?_) hD hcard H hH
      exact mem_innerAut_of_mem_linearAutGroup hn hp hpg (hDl hx) (hD.2 x hx)
  · exact localDeltaIn_eq_bot_of_not_le_linearAutGroup_two hn hp hp2 hpF hD hcard hDl hH

theorem innerPlaneBalance_projectiveSL_nonsplit_odd (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp4 : 3 < p ∨ 4 ≤ Nat.card F) (hpF : ¬ p ∣ Nat.card F) (hpq : ¬ p ∣ Nat.card F - 1) :
    InnerPlaneBalance p (projectiveSL n F) := by
  have e := LinearCover.projectiveSpecialLinearEquivProjectiveSL n F
  have hinjG := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) hn
  have hinjP := conjInjective_of_mulEquiv_lin e hinjG
  refine InnerPlaneBalance.of_mulEquiv e.symm ?_
  intro E hEin hE hEc H hH
  set E₁ := E.comap (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _) with hE₁def
  have hE₁ : E₁.map (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el := isElemAbelian_comap _ hinjP hE
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinjP, hE₁, hEc]
  rw [← hE₁]
  exact localDeltaIn_eq_bot_psl_nonsplit hp hp4 hpF hpq (by omega) hinjP E₁ hE₁el hE₁c hH

end Linear

@[expose] def regimeAOdd (p : ℕ) (idx : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧ 2 ≤ m ∧ (p = 3 → q.card ≠ 2)

theorem localTwoCrossFamAt_A_ge_two (p : ℕ) (hp : p = 3 ∨ p = 5) :
    LocalTwoCrossFamAt p .A (regimeAOdd p) := by
  rintro ⟨d, hv⟩ _ ⟨m, q, hd, hm2, hq3⟩ hc hnexc
  change d = _ at hd
  subst hd
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp with h | h <;> omega
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have h2 : 2 ≤ q.card := by
    have := q.prime_p.two_le
    have h3 : q.p ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact Nat.le_self_pow q.exponent_pos.ne' _
    omega
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hfour : 3 ≤ m + 1 := by omega
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpF : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcardF, TauCeti.PrimePower.card_def]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hpp q.prime_p).mp (hpp.dvd_of_dvd_pow hdvd))
  have hp4 : 3 < p ∨ 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rcases hp with rfl | rfl
    · right
      have hq' : q.card ≠ 2 := hq3 rfl
      rw [hcardF] at hpF ⊢
      omega
    · left
      norm_num
  have hnp : p ∣ Nat.card (GaloisField q.p q.exponent) - 1 → m + 1 ≠ p := by
    intro hdiv hmp
    have hq1 : q.card % p = 1 := by
      rw [hcardF] at hdiv
      obtain ⟨k, hk⟩ := hdiv
      have h4 : q.card = 1 + p * k := by omega
      rw [h4, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hpp.one_lt
    exact (hnexc ⟨.A m q, hv⟩ (Or.inl ⟨q, by simp [← hmp], hq1⟩)).false (MulEquiv.refl _)
  have e' := LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) (GaloisField q.p q.exponent)
  exact IsLocallyBalancedAbs.of_mulEquiv (e.trans e')
    (isLocallyBalancedAbs_two_projectiveSL_odd (n := m + 1) hfour hpp hp2 hpF hnp
      (fun hpq1 => innerPlaneBalance_projectiveSL_nonsplit_odd hfour hpp hp4 hpF hpq1))

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
