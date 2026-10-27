module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitBlocks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagSplitTransvection
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearThreeTwoDiag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix Polynomial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.CTP.SeitzToral
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Diag

variable {n : ℕ} {F : Type} [Field F]

theorem glConj_pow_mul_eq_diagonal {P A B : GL (Fin n) F} {dA dB : Fin n → F}
    (hA : ((P * A * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal dA)
    (hB : ((P * B * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal dB)
    (k : ℕ) :
    ((P * (A ^ k * B) * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun l => dA l ^ k * dB l) := by
  have h1 : P * (A ^ k * B) * P⁻¹ = (P * A * P⁻¹) ^ k * (P * B * P⁻¹) := by
    rw [conj_pow]
    group
  rw [h1, Units.val_mul, Units.val_pow_eq_pow_val, hA, hB, Matrix.diagonal_pow,
    Matrix.diagonal_mul_diagonal]
  rfl

theorem glConj_eq_diagonal {P x : GL (Fin n) F}
    (hx : ∀ i j, i ≠ j → ((P * x * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :
    ((P * x * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun l => ((P * x * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l l) := by
  ext r s
  by_cases h : r = s
  · subst h; simp
  · simp [hx r s h, Matrix.diagonal_apply_ne _ h]

theorem closure_pair_comm_and_pow_eq_one {G : Type*} [Group G] {A B : G} (hAB : A * B = B * A)
    {p : ℕ} (hA : A ^ p = 1) (hB : B ^ p = 1) :
    (∀ x ∈ Subgroup.closure ({A, B} : Set G), ∀ y ∈ Subgroup.closure ({A, B} : Set G),
      x * y = y * x) ∧ ∀ x ∈ Subgroup.closure ({A, B} : Set G), x ^ p = 1 := by
  have hpair : ({A, B} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hAB
    · exact hAB.symm
    · exact Commute.refl _
  have hc := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ x ∈ Subgroup.closure ({A, B} : Set G), ∀ y ∈ Subgroup.closure ({A, B} : Set G),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hA
    · exact hB
  | one => exact one_pow p
  | mul y z hy hz ihy ihz =>
    rw [(show Commute y z from hcomm y hy z hz).mul_pow, ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

end Diag

section Plane

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem localDeltaIn_eq_bot_of_split (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {A B : GL (Fin n) F} (hAB : A * B = B * A) (hA : A ^ p = 1)
    (hB : B ^ p = 1) (hA1 : conjAut n F A ≠ 1)
    (hBA : conjAut n F B ∉ Subgroup.zpowers (conjAut n F A))
    {H : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H) :
    localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hF4 : 4 ≤ Nat.card F := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  have hpF : ¬ p ∣ Nat.card F := by
    intro hd
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpq
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpF
  obtain ⟨hcomm, hexp⟩ := closure_pair_comm_and_pow_eq_one hAB hA hB
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (exists_primitiveRoot_of_dvd hp hpq)
    (Subgroup.closure ({A, B} : Set (GL (Fin n) F))) hcomm hexp
  have hAmem : A ∈ Subgroup.closure ({A, B} : Set (GL (Fin n) F)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hBmem : B ∈ Subgroup.closure ({A, B} : Set (GL (Fin n) F)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set dA : Fin n → F := fun l => ((P * A * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l l
    with hdA
  set dB : Fin n → F := fun l => ((P * B * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l l
    with hdB
  have hAd : ((P * A * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal dA :=
    glConj_eq_diagonal (hP A hAmem)
  have hBd : ((P * B * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal dB :=
    glConj_eq_diagonal (hP B hBmem)
  have hpow : ∀ {x : GL (Fin n) F} {d : Fin n → F}, x ^ p = 1 →
      ((P * x * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal d →
      ∀ l, d l ^ p = 1 := by
    intro x d hx hd l
    have h1 : (P * x * P⁻¹) ^ p = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
    have h2 := congrArg (fun y : GL (Fin n) F => (y : Matrix (Fin n) (Fin n) F) l l) h1
    simp only [Units.val_pow_eq_pow_val, hd, Matrix.diagonal_pow, Units.val_one] at h2
    simpa using h2
  have hne0 : ∀ {d : Fin n → F}, (∀ l, d l ^ p = 1) → ∀ l, d l ≠ 0 := by
    intro d hd l h0
    have := hd l
    rw [h0, zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  have hdAp := hpow hA hAd
  have hdBp := hpow hB hBd
  have hpair : ∀ i j : Fin n, ∃ M : GL (Fin n) F, M ^ p = 1 ∧
      conjAut n F M ∈ Subgroup.closure {conjAut n F A, conjAut n F B} ∧ conjAut n F M ≠ 1 ∧
      ∃ d : Fin n → F, ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Matrix.diagonal d ∧ d i = d j := by
    intro i j
    by_cases hAij : dA i = dA j
    · exact ⟨A, hA, Subgroup.subset_closure (Set.mem_insert _ _), hA1, dA, hAd, hAij⟩
    · set α : F := dA i / dA j with hα
      have hα1 : α ≠ 1 := fun h => hAij ((div_eq_one_iff_eq (hne0 hdAp j)).1 h)
      have hαp : α ^ p = 1 := by rw [hα, div_pow, hdAp i, hdAp j, div_one]
      have hprim : IsPrimitiveRoot α p := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hαp hα1)
      have hβp : (dB j / dB i) ^ p = 1 := by rw [div_pow, hdBp j, hdBp i, div_one]
      obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hβp
      refine ⟨A ^ k * B, ?_, ?_, ?_, fun l => dA l ^ k * dB l,
        glConj_pow_mul_eq_diagonal hAd hBd k, ?_⟩
      · rw [(show Commute (A ^ k) B from (show Commute A B from hAB).pow_left k).mul_pow,
          ← pow_mul, mul_comm, pow_mul, hA, one_pow, hB, one_mul]
      · rw [map_mul, map_pow]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure
          (Set.mem_insert _ _)) k) (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      · rw [map_mul, map_pow]
        intro h1
        apply hBA
        rw [eq_inv_of_mul_eq_one_right h1]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
      · have hAj := hne0 hdAp j
        have hBi := hne0 hdBp i
        have hBj := hne0 hdBp j
        rw [hα, div_pow, div_eq_div_iff (pow_ne_zero k hAj) hBi] at hk
        change dA i ^ k * dB i = dA j ^ k * dB j
        rw [hk, mul_comm]
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd hp hpq
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  set 𝒢 : Subgroup (SpecialLinearGroup (Fin n) F) := (fixSub g).comap (proj n F) with h𝒢
  have hall : (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) ≤ 𝒢.comap (conjSL P⁻¹) := by
    rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n)
      (K := F), Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    obtain ⟨M, hMp, hMmem, hM1, d, hd, hdij⟩ := hpair t.i t.j
    have hdiagM : ∀ k l, k ≠ l →
        ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0 := by
      intro k l hkl
      rw [hd]
      exact Matrix.diagonal_apply_ne _ hkl
    have hentry : ∀ l, ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l l = d l :=
      fun l => by rw [hd, Matrix.diagonal_apply_eq]
    have hij : ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) t.i t.i =
        ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) t.j t.j := by
      rw [hentry, hentry, hdij]
    have hMx : (Matrix.toLin' (M : Matrix (Fin n) (Fin n) F)) ^ p = 1 := by
      rw [← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hMp, Units.val_one, Matrix.toLin'_one]
      rfl
    have hsq := squarefree_minpoly_of_pow_eq_one hpK hMx
    obtain ⟨hX, hmult, hmem⟩ := transvection_mem_blockImage_gl M P hdiagM t.hij hij t.c hsq
    set h' : primaryFactors (Matrix.toLin' (M : Matrix (Fin n) (Fin n) F)) :=
      ⟨X - C (((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) t.i t.i), hX⟩ with hh'
    have hcardE : Nat.card (Efac (Matrix.toLin' (M : Matrix (Fin n) (Fin n) F)) h') =
        Nat.card F := by
      have : Fact (Irreducible (X - C (((P * M * P⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) t.i t.i) : F[X])) := ⟨irreducible_X_sub_C _⟩
      change Nat.card (AdjoinRoot (X - C _)) = _
      rw [natCard_adjoinRoot, natDegree_X_sub_C, pow_one]
    have hgood : GoodBlock h' := Or.inr ⟨hmult, by rw [hcardE]; omega⟩
    have hfix := blockProj_le_fixSub (hsq := hsq) hn hp hp2 rfl hH hg hMmem hM1 hgood hζ
    set s : SpecialLinearGroup (Fin n) F := conjSL P⁻¹ t.toSpecialLinearGroup with hsdef
    have hsmat : (s : Matrix (Fin n) (Fin n) F) =
        ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 + Matrix.single t.i t.j t.c) *
          (P : Matrix (Fin n) (Fin n) F) := by
      rw [hsdef, conjSL_coe, inv_inv]
      rfl
    exact hfix ⟨s, hmem s hsmat, rfl⟩
  refine eq_one_of_comap_fixSub_eq_top (eq_top_iff.2 fun k _ => ?_)
  have h1 := hall (Subgroup.mem_top (conjSL P k))
  rw [Subgroup.mem_comap] at h1
  have h2 : conjSL P⁻¹ (conjSL P k) = k := by
    apply Subtype.ext
    rw [conjSL_coe, conjSL_coe, inv_inv]
    exact conj_cancel (G := (P : Matrix (Fin n) (Fin n) F))
      (Gi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) (unit_inv_mul P) _
  rw [h2] at h1
  exact h1

end Plane

section Balance

variable {n : ℕ} {F : Type} [Field F]

theorem glRescale_lift {p : ℕ} {A : GL (Fin n) F} {a : Fˣ}
    (hA : A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p)) :
    (GeneralLinearGroup.scalar (Fin n) a⁻¹ * A) ^ p = 1 ∧
      conjAut n F (GeneralLinearGroup.scalar (Fin n) a⁻¹ * A) = conjAut n F A := by
  refine ⟨?_, by rw [map_mul, conjAut_scalar, one_mul]⟩
  rw [(show Commute (GeneralLinearGroup.scalar (Fin n) a⁻¹) A from
    GeneralLinearGroup.scalar_commute _ A).mul_pow, hA, ← map_pow, ← map_mul, inv_pow,
    inv_mul_cancel, map_one]

theorem glScalar_mul_commute {A B : GL (Fin n) F} (hAB : A * B = B * A) (a b : Fˣ) :
    (GeneralLinearGroup.scalar (Fin n) a * A) * (GeneralLinearGroup.scalar (Fin n) b * B) =
      (GeneralLinearGroup.scalar (Fin n) b * B) * (GeneralLinearGroup.scalar (Fin n) a * A) := by
  have hc : ∀ (u : Fˣ) (X : GL (Fin n) F), Commute (GeneralLinearGroup.scalar (Fin n) u) X :=
    fun u X => GeneralLinearGroup.scalar_commute u X
  exact ((hc a _).mul_left ((hc b A).symm.mul_right (show Commute A B from hAB))).eq

variable [Finite F]

theorem diagAbelianPlaneBalance_split (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {A B : GL (Fin n) F} (hAB : A * B = B * A)
    (hAs : ∃ a : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p))
    (hBs : ∃ b : Fˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (b ^ p))
    (hA1 : conjAut n F A ≠ 1) (hBA : conjAut n F B ∉ Subgroup.zpowers (conjAut n F A))
    {H : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H) :
    localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥ := by
  obtain ⟨a, ha⟩ := hAs
  obtain ⟨b, hb⟩ := hBs
  obtain ⟨hA', hcA⟩ := glRescale_lift ha
  obtain ⟨hB', hcB⟩ := glRescale_lift hb
  have h := localDeltaIn_eq_bot_of_split hn hp hp2 hpF (glScalar_mul_commute hAB a⁻¹ b⁻¹) hA' hB'
    (by rwa [hcA]) (by rwa [hcA, hcB]) hH
  rwa [hcA, hcB] at h

@[expose] def DiagAbelianPlaneNonsplit : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ∣ Nat.card F - 1 → p ∣ n → ∀ A B : GL (Fin n) F, A * B = B * A →
      conjAut n F A ^ p = 1 → conjAut n F B ^ p = 1 → conjAut n F A ≠ 1 →
      conjAut n F B ∉ Subgroup.zpowers (conjAut n F A) →
      ¬ ((∃ a : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p)) ∧
        ∃ b : Fˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (b ^ p)) →
      ∀ H : Subgroup (MulAut (projectiveSL n F)), innerAut (projectiveSL n F) ≤ H →
        Subgroup.closure {conjAut n F A, conjAut n F B} ≤
          Subgroup.normalizer (H : Set (MulAut (projectiveSL n F))) →
        localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥

theorem diagAbelianPlaneBalance_of_nonsplit (h : DiagAbelianPlaneNonsplit) :
    DiagAbelianPlaneBalance := by
  intro n F _ _ hn p hp hp2 hpF hpn A B hAB hAp hBp hA1 hBA H hH hEH
  by_cases hs : (∃ a : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p)) ∧
      ∃ b : Fˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (b ^ p)
  · exact diagAbelianPlaneBalance_split hn hp hp2 hpF hAB hs.1 hs.2 hA1 hBA hH
  · exact h n F hn p hp hp2 hpF hpn A B hAB hAp hBp hA1 hBA hs H hH hEH

theorem crossCharFamCat_A_of_nonsplit (h : DiagAbelianPlaneNonsplit) : CrossCharFamCat .A :=
  crossCharFamCat_A_of_plane (diagAbelianPlaneBalance_of_nonsplit h)
    crossCharFamAt_A_regimeAThreeTwo

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
