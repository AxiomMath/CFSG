module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8D4D4Family
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCentralizer

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.AnisoE8

@[expose] def d8CharAdd : (Fin Tag.E8.rank → ℤ) →+ ZMod 2 where
  toFun v := (v 0 : ZMod 2)
  map_zero' := by simp
  map_add' u v := by simp

@[expose] def d8Char : Multiplicative (Fin Tag.E8.rank → ℤ) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative d8CharAdd

theorem d8Char_eq_one_iff (α : Fin Tag.E8.rank → ℤ) :
    d8Char (Multiplicative.ofAdd α) = 1 ↔ α 0 % 2 = 0 := by
  have h : d8Char (Multiplicative.ofAdd α) = Multiplicative.ofAdd (d8CharAdd α) := rfl
  have hz : ∀ n : ℤ, ((n : ℤ) : ZMod 2) = 0 ↔ n % 2 = 0 := fun n => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    omega
  rw [h, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  exact hz (α 0)

theorem kernelRoots_d8Char_eq :
    kernelRoots d8Char = {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ α 0 % 2 = 0} := by
  ext α
  show (IsRoot .E8 α ∧ d8Char (Multiplicative.ofAdd α) = 1) ↔
    (IsRoot .E8 α ∧ α 0 % 2 = 0)
  rw [d8Char_eq_one_iff]

theorem kernelRoots_d4d4Char_subset_d8Char :
    kernelRoots d4d4Char ⊆ kernelRoots d8Char := by
  intro α hα
  rw [kernelRoots_d8Char_eq]
  refine ⟨hα.1, ?_⟩
  have hfun : d4d4CharAdd α = 0 := by
    refine Multiplicative.ofAdd.injective ?_
    show d4d4Char (Multiplicative.ofAdd α) = 1
    exact hα.2
  have h0 : d4d4CharAdd α 0 = 0 := congrFun hfun 0
  have h0' : ((α 0 : ℤ) : ZMod 2) = 0 := by simpa [d4d4CharAdd] using h0
  have hz : ∀ n : ℤ, ((n : ℤ) : ZMod 2) = 0 ↔ n % 2 = 0 := fun n => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    omega
  exact (hz (α 0)).1 h0'

@[expose] def d6Roots : Set (Fin Tag.E8.rank → ℤ) :=
  {α | IsRoot .E8 α ∧ α 1 + α 2 = α 0 + α 4 ∧ 2 * α 3 = α 1 + α 2 + α 4}

@[expose] def d4d4WBase : Fin Tag.E8.rank → ℤ := ![0, 1, 1, 1, 0, 0, 0, 0]

@[expose] def d4d4WLambda : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def d6BaseCoeff : Fin Tag.E8.rank → ℤ := ![-1, 1, 1, 0, -1, 0, 0, 0]

@[expose] def d6DirCoeff : Fin Tag.E8.rank → ℤ := ![0, -1, -1, 2, -1, 0, 0, 0]

theorem d6BaseCoeff_eq_mulVec :
    d6BaseCoeff = Matrix.mulVec Tag.E8.symmetrizedCartan d4d4WBase := by
  decide +kernel

theorem d6DirCoeff_eq_mulVec :
    d6DirCoeff = Matrix.mulVec Tag.E8.symmetrizedCartan d4d4WLambda := by
  decide +kernel

@[expose] def d6EigenCoeff (p : ℕ) (lam : ZMod p) : Fin Tag.E8.rank → ℤ :=
  d6BaseCoeff + (lam.val : ℤ) • d6DirCoeff

theorem d6EigenCoeff_eq_mulVec (p : ℕ) (lam : ZMod p) :
    d6EigenCoeff p lam = Matrix.mulVec Tag.E8.symmetrizedCartan
      (d4d4WBase + (lam.val : ℤ) • d4d4WLambda) := by
  rw [d6EigenCoeff, d6BaseCoeff_eq_mulVec, d6DirCoeff_eq_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul]

theorem d6EigenCoeff_apply (p : ℕ) (lam : ZMod p) (i : Fin Tag.E8.rank) :
    d6EigenCoeff p lam i = d6BaseCoeff i + (lam.val : ℤ) * d6DirCoeff i := by
  simp [d6EigenCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

@[expose] def d6TorsionChar {K : Type} [Field K] (p : ℕ) (ζ : Kˣ) (lam : ZMod p) :
    Fin Tag.E8.rank → Kˣ :=
  fun i => ζ ^ (d6EigenCoeff p lam i)

theorem rootChar_d6TorsionChar {K : Type} [Field K] (p : ℕ) (ζ : Kˣ) (lam : ZMod p)
    (α : Fin Tag.E8.rank → ℤ) :
    rootChar (d6TorsionChar p ζ lam) α =
      ζ ^ ((α 1 + α 2 - α 0 - α 4) + (2 * α 3 - α 1 - α 2 - α 4) * (lam.val : ℤ)) := by
  rw [rootChar]
  simp only [d6TorsionChar]
  calc ∏ i, (ζ ^ d6EigenCoeff p lam i) ^ α i = ∏ i, ζ ^ (d6EigenCoeff p lam i * α i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [zpow_mul]
    _ = ζ ^ ∑ i, d6EigenCoeff p lam i * α i := Finset.prod_zpow_eq_zpow_sum _ _ _
    _ = ζ ^ ((α 1 + α 2 - α 0 - α 4) + (2 * α 3 - α 1 - α 2 - α 4) * (lam.val : ℤ)) := by
        congr 1
        simp only [d6EigenCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
        rw [Finset.sum_add_distrib, Fin.sum_univ_def, Fin.sum_univ_def]
        have hrange : List.finRange Tag.E8.rank = [0, 1, 2, 3, 4, 5, 6, 7] := by
          decide +kernel
        rw [hrange]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        simp [d6BaseCoeff, d6DirCoeff]
        ring

theorem d6_pair_bound :
    ∀ α ∈ rootFinset .E8,
      (α 1 + α 2 - α 0 - α 4) ^ 2 + (2 * α 3 - α 1 - α 2 - α 4) ^ 2 ≤ 4 := by
  decide +kernel

theorem int_add_mul_eq_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {lam : ZMod p}
    (hlam : lam * lam = -1) {A B : ℤ} (hbd : A ^ 2 + B ^ 2 ≤ 4)
    (h : (A : ZMod p) + (B : ZMod p) * lam = 0) : A = 0 ∧ B = 0 := by
  have hB : (B : ZMod p) = (A : ZMod p) * lam := by
    have h' : ((A : ZMod p) + (B : ZMod p) * lam) * lam = 0 := by rw [h, zero_mul]
    rw [add_mul, mul_assoc, hlam] at h'
    linear_combination -h'
  have hlam2 : lam ^ 2 = -1 := by rw [pow_two]; exact hlam
  have hsq : (A : ZMod p) ^ 2 + (B : ZMod p) ^ 2 = 0 := by
    rw [hB, mul_pow, hlam2]
    ring
  have hdvd : (p : ℤ) ∣ A ^ 2 + B ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hsq
  have hnonneg : 0 ≤ A ^ 2 + B ^ 2 := by positivity
  have hsum : A ^ 2 + B ^ 2 = 0 := by
    by_contra hne
    have hpos : (0 : ℤ) < A ^ 2 + B ^ 2 := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨k, hk⟩ := hdvd
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hk1 : (1 : ℤ) ≤ k := by nlinarith [hk, hpos, hp0]
    have hle : (p : ℤ) ≤ A ^ 2 + B ^ 2 := by nlinarith [hk, hp0, hk1]
    have h5' : (5 : ℤ) ≤ p := by exact_mod_cast h5
    omega
  constructor <;> nlinarith [sq_nonneg A, sq_nonneg B]

theorem d6_coord_even :
    ∀ α ∈ rootFinset .E8, α 1 + α 2 = α 0 + α 4 → 2 * α 3 = α 1 + α 2 + α 4 →
      α 0 % 2 = 0 := by
  decide +kernel

theorem d6Roots_subset_kernelRoots_d8Char :
    d6Roots ⊆ kernelRoots d8Char := by
  intro α hα
  rw [kernelRoots_d8Char_eq]
  exact ⟨hα.1, d6_coord_even α (mem_rootFinset.2 hα.1) hα.2.1 hα.2.2⟩

theorem rootCharKernel_d6TorsionChar {K : Type} [Field K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) {lam : ZMod p}
    (hlam : lam * lam = -1) :
    rootCharKernel (d6TorsionChar p ζ lam) = d6Roots := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h5 : 5 ≤ p := by
    refine hp.five_le_of_ne_two_of_ne_three hp2 ?_
    intro h3
    have h4 : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := lam) (by rw [pow_two]; exact hlam)
    rw [h3] at h4
    exact h4 (by norm_num)
  have hz : ∀ n : ℤ, ζ ^ n = 1 ↔ ((n : ℤ) : ZMod p) = 0 := fun n => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hζo, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  ext α
  show (IsRoot .E8 α ∧ rootChar (d6TorsionChar p ζ lam) α = 1) ↔
    (IsRoot .E8 α ∧ α 1 + α 2 = α 0 + α 4 ∧ 2 * α 3 = α 1 + α 2 + α 4)
  refine and_congr_right fun hα => ?_
  rw [rootChar_d6TorsionChar, hz]
  constructor
  · intro h
    have h' : ((α 1 + α 2 - α 0 - α 4 : ℤ) : ZMod p) +
        ((2 * α 3 - α 1 - α 2 - α 4 : ℤ) : ZMod p) * lam = 0 := by
      have hh := h
      push_cast at hh
      rw [ZMod.natCast_zmod_val] at hh
      push_cast
      exact hh
    have hb := int_add_mul_eq_zero hp h5 hlam (d6_pair_bound α (mem_rootFinset.2 hα)) h'
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    have hA : α 1 + α 2 - α 0 - α 4 = 0 := by omega
    have hB : 2 * α 3 - α 1 - α 2 - α 4 = 0 := by omega
    have hE : (α 1 + α 2 - α 0 - α 4) +
        (2 * α 3 - α 1 - α 2 - α 4) * (lam.val : ℤ) = 0 := by
      rw [hA, hB]
      ring
    rw [hE]
    simp

section Eigen

theorem d4d4W_smul_d4d4WBase :
    d4d4W • d4d4WBase = -d4d4WLambda := by
  rw [d4d4W, d4d4W_smul_foldr]
  decide +kernel

theorem d4d4W_smul_d4d4WLambda :
    d4d4W • d4d4WLambda = d4d4WBase := by
  rw [d4d4W, d4d4W_smul_foldr]
  decide +kernel

end Eigen

section Steinberg

theorem toralCentralizer_d6TorsionChar_le_sup_rootSpan {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) {lam : ZMod p}
    (hlam : lam * lam = -1) :
    toralCentralizer Tag.E8 K (d6TorsionChar p ζ lam) ≤
      torusGroup Tag.E8 K ⊔ rootSpan Tag.E8 K (kernelRoots d8Char) := by
  have hap : ∀ i, d6TorsionChar p ζ lam i ^ p = 1 := by
    intro i
    have hζp : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
    rw [d6TorsionChar]
    calc (ζ ^ d6EigenCoeff p lam i) ^ p
        = (ζ ^ d6EigenCoeff p lam i) ^ (p : ℤ) := (zpow_natCast _ p).symm
      _ = ζ ^ (d6EigenCoeff p lam i * (p : ℤ)) := (zpow_mul ζ _ (p : ℤ)).symm
      _ = ζ ^ ((p : ℤ) * d6EigenCoeff p lam i) := by rw [mul_comm]
      _ = (ζ ^ (p : ℤ)) ^ d6EigenCoeff p lam i := zpow_mul ζ (p : ℤ) _
      _ = (ζ ^ p) ^ d6EigenCoeff p lam i := by rw [zpow_natCast]
      _ = 1 := by rw [hζp, one_zpow]
  have hker : rootCharKernel (d6TorsionChar p ζ lam) ⊆ kernelRoots d8Char := by
    rw [rootCharKernel_d6TorsionChar hp hp2 hζo hlam]
    exact d6Roots_subset_kernelRoots_d8Char
  have hS : ∀ α ∈ kernelRoots d8Char, IsRoot .E8 α := fun α hα => hα.1
  have hSn : ∀ α ∈ kernelRoots d8Char, -α ∈ kernelRoots d8Char := by
    rintro α ⟨hα, hχ⟩
    rw [kernelRoots_d8Char_eq]
    refine ⟨IsRoot.neg hα, ?_⟩
    have h0 : α 0 % 2 = 0 := (d8Char_eq_one_iff α).1 hχ
    rw [Pi.neg_apply]
    omega
  have ha1 : d6TorsionChar p ζ lam ≠ 1 := by
    intro ha
    have h0 : ζ ^ (-1 : ℤ) = 1 := by
      have h := congrFun ha 0
      simpa [d6TorsionChar, d6EigenCoeff_apply, d6BaseCoeff, d6DirCoeff] using h
    have hζ1 : ζ = 1 := by simpa using h0
    rw [hζ1, orderOf_one] at hζo
    exact (Nat.Prime.one_lt hp).ne' hζo.symm
  by_cases h5 : p = 5
  · clear hζo
    subst p
    rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_E8_five
      K (d6TorsionChar 5 ζ lam) hap]
    exact sup_le_sup_left (rootSpan_mono hker) _
  · have h13 : 13 ≤ p := by
      have hne3 : p % 4 ≠ 3 := by
        haveI : Fact p.Prime := ⟨hp⟩
        exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := lam) (by rw [pow_two]; exact hlam)
      have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
      have hpmod : p % 4 = 1 := by omega
      have hp9 : p ≠ 9 := by
        intro h
        rw [h] at hp
        norm_num at hp
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hord : ¬ p ∣ Nat.card (WeylGroup .E8) :=
      CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp (by omega)
        (Or.inr (Or.inr rfl))
    exact CFSG.RankThree.PartOne.KE.toralCentralizer_le_sup_rootSpan hp hord hap ha1 hS hSn hker

end Steinberg

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
