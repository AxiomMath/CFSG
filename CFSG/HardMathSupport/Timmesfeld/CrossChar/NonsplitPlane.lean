module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagSplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix Polynomial Module
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Units

variable {F : Type} [Field F] [Finite F]

theorem exists_zpow_mul_pow_of_forall_pow_ne {p : ℕ} (hp : p.Prime) {a : Fˣ}
    (ha : ∀ d : Fˣ, d ^ p ≠ a) (b : Fˣ) : ∃ (k : ℤ) (d : Fˣ), b = a ^ k * d ^ p := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hγ a)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hγ b)
  have hpi : ¬ (p : ℤ) ∣ i := by
    rintro ⟨t, rfl⟩
    refine ha (γ ^ t) ?_
    rw [← hi, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
  have hcop : IsCoprime (p : ℤ) i :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).2 hpi
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨v * j, γ ^ (u * j), ?_⟩
  rw [← hi, ← hj, ← _root_.zpow_mul, ← zpow_natCast (γ ^ (u * j)) p, ← _root_.zpow_mul,
    ← _root_.zpow_add]
  congr 1
  linear_combination (-j) * huv

end Units

section Pair

variable {n : ℕ} {F : Type} [Field F]

theorem conjAut_scalar_mul (u : Fˣ) (A : GL (Fin n) F) :
    conjAut n F (GeneralLinearGroup.scalar (Fin n) u * A) = conjAut n F A := by
  rw [map_mul, conjAut_scalar, one_mul]

theorem scalar_mul_pow (u : Fˣ) (A : GL (Fin n) F) (p : ℕ) :
    (GeneralLinearGroup.scalar (Fin n) u * A) ^ p =
      GeneralLinearGroup.scalar (Fin n) (u ^ p) * A ^ p := by
  rw [(show Commute (GeneralLinearGroup.scalar (Fin n) u) A from
    GeneralLinearGroup.scalar_commute u A).mul_pow, map_pow]

variable [Finite F]

theorem exists_pow_eq_scalar (hn : 3 ≤ n) {p : ℕ} {A : GL (Fin n) F}
    (h : conjAut n F A ^ p = 1) : ∃ a : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a := by
  obtain ⟨a, ha⟩ := (eq_one_of_conjAut_mul_fieldAut_eq_one hn (A ^ p) 1
    (by rw [map_one, mul_one, map_pow, h])).2
  exact ⟨a, ha.symm⟩

theorem exists_nonsplit_pair (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) {A B : GL (Fin n) F}
    (hAB : A * B = B * A) (hA : conjAut n F A ^ p = 1) (hB : conjAut n F B ^ p = 1)
    (hA1 : conjAut n F A ≠ 1) (hBA : conjAut n F B ∉ Subgroup.zpowers (conjAut n F A))
    (hns : ¬ ((∃ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (c ^ p)) ∧
      ∃ d : Fˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (d ^ p))) :
    ∃ R S : GL (Fin n) F, R * S = S * R ∧
      (∃ c : Fˣ, R ^ p = GeneralLinearGroup.scalar (Fin n) c ∧ ∀ d : Fˣ, d ^ p ≠ c) ∧
      S ^ p = 1 ∧ conjAut n F S ≠ 1 ∧
      conjAut n F R ∈ Subgroup.closure {conjAut n F A, conjAut n F B} ∧
      conjAut n F S ∈ Subgroup.closure {conjAut n F A, conjAut n F B} := by
  obtain ⟨a, ha⟩ := exists_pow_eq_scalar hn hA
  obtain ⟨b, hb⟩ := exists_pow_eq_scalar hn hB
  have hAE : conjAut n F A ∈ Subgroup.closure {conjAut n F A, conjAut n F B} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hBE : conjAut n F B ∈ Subgroup.closure {conjAut n F A, conjAut n F B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hsc : ∀ (u : Fˣ) (M : GL (Fin n) F), GeneralLinearGroup.scalar (Fin n) u * M =
      M * GeneralLinearGroup.scalar (Fin n) u := fun u M => GeneralLinearGroup.scalar_commute u M
  by_cases hap : ∃ c : Fˣ, c ^ p = a
  · obtain ⟨c, rfl⟩ := hap
    have hbp : ∀ d : Fˣ, d ^ p ≠ b := fun d hd => hns ⟨⟨c, ha⟩, ⟨d, hd ▸ hb⟩⟩
    refine ⟨B, GeneralLinearGroup.scalar (Fin n) c⁻¹ * A, ?_, ⟨b, hb, hbp⟩, ?_, ?_, hBE, ?_⟩
    · rw [← mul_assoc, ← hsc, mul_assoc, hAB.symm, ← mul_assoc]
    · rw [scalar_mul_pow, ha, ← map_mul, inv_pow, inv_mul_cancel, map_one]
    · rwa [conjAut_scalar_mul]
    · rwa [conjAut_scalar_mul]
  · push Not at hap
    obtain ⟨k, d, hbk⟩ := exists_zpow_mul_pow_of_forall_pow_ne hp hap b
    have hcomm : Commute A B := hAB
    have hsA : Commute (GeneralLinearGroup.scalar (Fin n) d⁻¹) A := hsc d⁻¹ A
    refine ⟨A, GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-k), ?_, ⟨a, ha, hap⟩, ?_, ?_,
      hAE, ?_⟩
    · exact ((hsA.symm.mul_right hcomm).mul_right (Commute.self_zpow A (-k))).eq
    · have h2 : Commute (GeneralLinearGroup.scalar (Fin n) d⁻¹ * B) (A ^ (-k)) :=
        (hsA.zpow_right (-k)).mul_left (hcomm.symm.zpow_right (-k))
      rw [h2.mul_pow, scalar_mul_pow, hb]
      have h3 : (A ^ (-k)) ^ p = (A ^ p) ^ (-k) := by
        rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
      rw [h3, ha, ← map_mul, ← map_zpow, ← map_mul, hbk]
      have h4 : d⁻¹ ^ p * (a ^ k * d ^ p) * a ^ (-k) = 1 := by
        rw [inv_pow, _root_.zpow_neg, mul_comm (a ^ k) (d ^ p), ← mul_assoc, inv_mul_cancel,
          one_mul, mul_inv_cancel]
      rw [h4, map_one]
    · rw [map_mul, conjAut_scalar_mul, map_zpow]
      intro h1
      apply hBA
      rw [mul_eq_one_iff_eq_inv, ← _root_.zpow_neg, neg_neg] at h1
      rw [h1]
      exact Subgroup.zpow_mem_zpowers _ _
    · rw [map_mul, conjAut_scalar_mul, map_zpow]
      exact Subgroup.mul_mem _ hBE (Subgroup.zpow_mem _ hAE _)

end Pair

section Main

variable {n : ℕ} {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem exists_ne_mem_primaryFactors (hn : 0 < n) {p : ℕ} (hp : p ≠ 0) (hpF : (p : F) ≠ 0)
    {ω : F} (hω : IsPrimitiveRoot ω p) {S : GL (Fin n) F} (hS : S ^ p = 1)
    (hS1 : conjAut n F S ≠ 1) :
    ∃ a ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)),
      ∃ a' ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)), a ≠ a' := by
  classical
  set xS := Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) with hxS
  have hsq : Squarefree (minpoly F xS) := squarefree_minpoly_of_pow_eq_one hpF
    (toLin'_pow_eq_one hS)
  have hsum := sum_primaryProjection hsq
  by_contra hall
  push Not at hall
  obtain ⟨a₀, ha₀⟩ : (primaryFactors xS).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at hsum
    have h2 := congrFun (LinearMap.congr_fun hsum (Pi.single ⟨0, hn⟩ 1)) ⟨0, hn⟩
    simp at h2
  have hsingle : primaryFactors xS = {a₀} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨ha₀, fun a ha => hall a ha a₀ ha₀⟩
  obtain ⟨ζ, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp hω hS ha₀
  rw [hsingle, Finset.sum_singleton] at hsum
  have hxv : ∀ v, xS v = ζ • v := by
    intro v
    have hPv : primaryProjection xS (X - C ζ) v = v := by rw [hsum]; rfl
    have h1 := mem_primaryComponent.1 (primaryProjection_mem hsq ha₀ v)
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
      hPv] at h1
    exact sub_eq_zero.1 h1
  have hSmat : (S : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) ζ := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [← hxS, hxv]
    ext i
    simp [Matrix.mulVec_diagonal]
  have hζ : ζ ≠ 0 := by
    rintro rfl
    have h1 : ((S * S⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
      rw [mul_inv_cancel]; simp
    rw [Units.val_mul, hSmat] at h1
    simp at h1
  apply hS1
  have hSu : S = GeneralLinearGroup.scalar (Fin n) (Units.mk0 ζ hζ) := by
    ext i j
    rw [hSmat, GeneralLinearGroup.coe_scalar]
    rfl
  rw [hSu, conjAut_scalar]

theorem localDeltaIn_eq_bot_of_nonsplit_pair (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {R S : GL (Fin n) F} (hRS : R * S = S * R) {c : Fˣ}
    (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c) (hc : ∀ d : Fˣ, d ^ p ≠ c)
    (hS : S ^ p = 1) (hS1 : conjAut n F S ≠ 1) {H E : Subgroup (MulAut (projectiveSL n F))}
    (hH : innerAut (projectiveSL n F) ≤ H) (hRE : conjAut n F R ∈ E)
    (hSE : conjAut n F S ∈ E) : localDeltaIn p H E = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hq4 : 4 ≤ Nat.card F := by
    have := Nat.le_of_dvd (by omega) hpF
    have := hp.two_le
    omega
  have hpF' : ¬ p ∣ Nat.card F := by
    intro hd
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpF'
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartOne.CTP.exists_primitiveRoot_of_dvd hp hpF
  have hirr : Irreducible (X ^ p - C (c : F)) := by
    refine X_pow_sub_C_irreducible_of_prime hp fun b hb => ?_
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp0] at hb
      exact c.ne_zero hb.symm
    exact hc (Units.mk0 b hb0) (Units.ext (by simpa using hb))
  have hR1 : conjAut n F R ≠ 1 := by
    intro h1
    obtain ⟨d, hd⟩ := (eq_one_of_conjAut_mul_fieldAut_eq_one hn R 1
      (by rw [map_one, mul_one, h1])).2
    apply hc d
    apply glScalar_injective hn0
    rw [map_pow, hd, hR]
  set xR := Matrix.toLin' (R : Matrix (Fin n) (Fin n) F) with hxR
  set xS := Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) with hxS
  have hsqS : Squarefree (minpoly F xS) := squarefree_minpoly_of_pow_eq_one hpK
    (toLin'_pow_eq_one hS)
  have hh := mem_primaryFactors_X_pow_sub_C hn0 hp0 hirr hR
  obtain ⟨a, ha, a', ha', haa'⟩ := exists_ne_mem_primaryFactors hn0 hp0 hpK hω hS hS1
  obtain ⟨-, -, -, -, -, hmult⟩ :=
    exists_mixing_mem_blockImage hn0 hp0 hRS hirr hR hsqS ha ha' haa'
  have hgoodR : ∀ h : primaryFactors xR, GoodBlock h := by
    intro h
    have hh' : (h : F[X]) = X ^ p - C (c : F) := by
      have hirr' := irreducible_of_mem_primaryFactors h.2
      have hdvd : (h : F[X]) ∣ X ^ p - C (c : F) := (mem_primaryFactors.mp h.2).2.2.trans
        (minpoly.dvd F _ (aeval_X_pow_sub_C_eq_zero hR))
      exact eq_of_monic_of_associated (monic_of_mem_primaryFactors h.2)
        (monic_X_pow_sub_C _ hp0)
        (associated_of_dvd_dvd hdvd (hirr'.dvd_symm hirr hdvd))
    have hheq : h = ⟨X ^ p - C (c : F), hh⟩ := Subtype.ext hh'
    subst hheq
    right
    refine ⟨hmult, ?_⟩
    have : Fact (Irreducible (X ^ p - C (c : F))) := ⟨hirr⟩
    change 3 < Nat.card (AdjoinRoot (X ^ p - C (c : F)))
    rw [natCard_adjoinRoot, natDegree_X_pow_sub_C]
    calc 3 < Nat.card F := by omega
      _ = Nat.card F ^ 1 := (pow_one _).symm
      _ ≤ Nat.card F ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hgoodS : ∀ b : primaryFactors xS, GoodBlock b := by
    intro b
    left
    obtain ⟨ζ, hζ⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp0 hω hS b.2
    have hdeg : (b : F[X]).natDegree = 1 := by rw [hζ]; exact natDegree_X_sub_C ζ
    have h1 := finrank_primaryComponent xS (b : F[X])
    rw [hdeg, one_mul] at h1
    have h2 : p ≤ finrank F (primaryComponent xS (b : F[X])) :=
      le_finrank_primaryComponent hn0 hp0 hRS hirr hR hsqS b.2
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    change 3 ≤ finrank (AdjoinRoot (b : F[X])) (primaryComponent xS (b : F[X]))
    omega
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  apply eq_one_of_comap_fixSub_eq_top
  refine eq_top_of_nonsplit_blocks_le hn0 hp.two_le hpK hω hRS hirr hR hS _ ?_ ?_
  · intro hsq h
    exact blockImage_le_map_fixSub hn hp hp2 rfl hH hg hRE hR1 (hgoodR h) hω
  · intro hsq b
    exact blockImage_le_map_fixSub hn hp hp2 rfl hH hg hSE hS1 (hgoodS b) hω

theorem localDeltaIn_eq_bot_of_nonsplit (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {A B : GL (Fin n) F} (hAB : A * B = B * A)
    (hA : conjAut n F A ^ p = 1) (hB : conjAut n F B ^ p = 1) (hA1 : conjAut n F A ≠ 1)
    (hBA : conjAut n F B ∉ Subgroup.zpowers (conjAut n F A))
    (hns : ¬ ((∃ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (c ^ p)) ∧
      ∃ d : Fˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (d ^ p)))
    {H : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H) :
    localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥ := by
  obtain ⟨R, S, hRS, ⟨c, hR, hc⟩, hS, hS1, hRE, hSE⟩ :=
    exists_nonsplit_pair hn hp hAB hA hB hA1 hBA hns
  exact localDeltaIn_eq_bot_of_nonsplit_pair hn hp hp2 hpF hRS hR hc hS hS1 hH hRE hSE

end Main

theorem diagAbelianPlaneNonsplit_holds : DiagAbelianPlaneNonsplit := by
  intro n F _ _ hn p hp hp2 hpF _ A B hAB hA hB hA1 hBA hns H hH _
  exact localDeltaIn_eq_bot_of_nonsplit hn hp hp2 hpF hAB hA hB hA1 hBA hns hH

theorem diagAbelianPlaneBalance_holds : DiagAbelianPlaneBalance :=
  diagAbelianPlaneBalance_of_nonsplit diagAbelianPlaneNonsplit_holds

theorem diagLinearBalance_holds : DiagLinearBalance :=
  diagLinearBalance_of_plane diagAbelianPlaneBalance_holds

theorem crossCharFamCat_A : CrossCharFamCat .A :=
  crossCharFamCat_A_of_nonsplit diagAbelianPlaneNonsplit_holds

end CFSG.HardMathSupport.Timmesfeld.CrossChar
