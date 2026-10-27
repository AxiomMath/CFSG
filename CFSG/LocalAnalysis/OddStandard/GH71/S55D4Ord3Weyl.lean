module

public import CFSG.RankThree.PartOne.KGD.D4Weyl
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

@[expose] def d4MatT (e : ℕ) : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  d4Mat e

@[expose] def d4ParityFix (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (c : Fin TwistTag.D4.tag.rank → ℤ) : Prop :=
  ∀ i : Fin TwistTag.D4.tag.rank, (∑ j, c j * (M ^ 2) j i - c i) % 2 = 0

instance (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (c : Fin TwistTag.D4.tag.rank → ℤ) : Decidable (d4ParityFix M c) := by
  unfold d4ParityFix
  infer_instance

@[expose] def d4RhoComm (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ) :
    Prop :=
  ∀ p : Fin TwistTag.D4.tag.rank × Fin TwistTag.D4.tag.rank,
    M (TwistTag.D4.perm p.1) (TwistTag.D4.perm p.2) = M p.1 p.2

instance (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ) :
    Decidable (d4RhoComm M) := by
  unfold d4RhoComm
  infer_instance

@[expose] def d4ParA : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 0, 1]

@[expose] def d4ParB : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 0]

theorem d4_tab_parity : ∀ e ∈ d4WeylTab, d4MatT e ^ 3 = 1 → d4MatT e ≠ 1 →
    d4RhoComm (d4MatT e) → ¬ (d4ParityFix (d4MatT e) d4ParA ∧ d4ParityFix (d4MatT e) d4ParB) := by
  decide +kernel

@[expose] def d4Sign (K : Type) [Field K] (c : Fin TwistTag.D4.tag.rank → ℤ) :
    Fin TwistTag.D4.tag.rank → Kˣ :=
  fun j => (-1 : Kˣ) ^ c j

theorem rootChar_d4Sign (K : Type) [Field K] (c v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (d4Sign K c) v = (-1 : Kˣ) ^ (∑ j, c j * v j) := by
  rw [rootChar]
  simp only [d4Sign, ← zpow_mul]
  rw [← Finset.prod_zpow_eq_zpow_sum]

theorem neg_one_zpow_eq_iff {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (m n : ℤ) :
    (-1 : Kˣ) ^ m = (-1 : Kˣ) ^ n ↔ (m - n) % 2 = 0 := by
  have hne : (-1 : Kˣ) ≠ 1 := by
    intro h
    apply h2
    have h' := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h'
    linear_combination -h'
  constructor
  · intro h
    have h1 : (-1 : Kˣ) ^ (m - n) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
    rcases Int.even_or_odd (m - n) with he | ho
    · exact Int.even_iff.1 he
    · exact absurd (by rwa [ho.neg_one_zpow] at h1) hne
  · intro h
    have h1 : (-1 : Kˣ) ^ (m - n) = 1 := (Int.even_iff.2 h).neg_one_zpow
    rw [zpow_sub, mul_inv_eq_one] at h1
    exact h1

theorem mulVec_single_one_apply' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (M *ᵥ (Pi.single j 1 : Fin n → ℤ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]


theorem d4_weyl_moves_sign {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4) (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) :
    weylTuple w (d4Sign K d4ParA) ≠ d4Sign K d4ParA ∨
      weylTuple w (d4Sign K d4ParB) ≠ d4Sign K d4ParB := by
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w
  have hpow : ∀ (n : ℕ) (v : Fin TwistTag.D4.tag.rank → ℤ), (w ^ n) • v = d4MatT e ^ n *ᵥ v :=
    fun n v => pow_smul_eq_d4Mat_pow_mulVec w hwe n v
  have hent : ∀ (n : ℕ) (i j : Fin TwistTag.D4.tag.rank),
      ((w ^ n) • (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ)) i = (d4MatT e ^ n) i j := by
    intro n i j
    rw [hpow]
    exact mulVec_single_one_apply' _ i j
  have hM3 : d4MatT e ^ 3 = 1 := by
    ext i j
    rw [← hent 3 i j, hw3, one_smul, Matrix.one_apply, Pi.single_apply]
  have hM1 : d4MatT e ≠ 1 := by
    intro h
    apply hw1
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun v => ?_
    rw [one_smul, ← pow_one w, hpow, pow_one, h, Matrix.one_mulVec]
  have hρ : d4RhoComm (d4MatT e) := by
    rintro ⟨i, j⟩
    have h := weylTwist_smul_permLattice (t := TwistTag.D4) w (Pi.single j 1)
    rw [(mem_relWeylTwist TwistTag.D4).1 hw] at h
    have h' := congrFun h (TwistTag.D4.perm i)
    have hs : permLattice TwistTag.D4.perm (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) =
        Pi.single (TwistTag.D4.perm j) 1 := by
      funext k
      rw [permLattice, Function.comp_apply, Pi.single_apply, Pi.single_apply]
      simp only [Equiv.symm_apply_eq]
    rw [hs] at h'
    simp only [permLattice, Function.comp_apply, Equiv.symm_apply_apply] at h'
    have e1 := hent 1 (TwistTag.D4.perm i) (TwistTag.D4.perm j)
    have e2 := hent 1 i j
    rw [pow_one, pow_one] at e1 e2
    rw [← e1, ← e2]
    exact h'
  have hpar := d4_tab_parity e he hM3 hM1 hρ
  have hwinv : w⁻¹ = w ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hw3
  have hfix : ∀ c : Fin TwistTag.D4.tag.rank → ℤ,
      weylTuple w (d4Sign K c) = d4Sign K c → d4ParityFix (d4MatT e) c := by
    intro c hc i
    have h := congrFun hc i
    simp only [weylTuple] at h
    rw [rootChar_d4Sign] at h
    have hc' : ∀ j, (w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) j =
        (d4MatT e ^ 2) j i := fun j => by
      rw [hwinv]
      exact hent 2 j i
    simp only [hc'] at h
    exact (neg_one_zpow_eq_iff h2 _ _).1 h
  by_contra hcon
  push Not at hcon
  exact hpar ⟨hfix _ hcon.1, hfix _ hcon.2⟩

end CFSG.OddStandard.GH71.S55
