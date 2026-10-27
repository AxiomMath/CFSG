module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharLev
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

section Independent

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

theorem exists_independent_scalar (hK : p ^ 2 ≤ Nat.card K) :
    ∃ y : K, ∀ i j : ℕ, (i : K) * 1 + (j : K) * y = 0 → p ∣ i ∧ p ∣ j := by
  classical
  obtain ⟨φ, -⟩ : ∃ φ : ZMod p →+* K, True := ⟨ZMod.castHom (dvd_refl p) K, trivial⟩
  have hrange : ∃ y : K, y ∉ Set.range φ := by
    by_contra hall
    push Not at hall
    have hu : Set.range φ = Set.univ := Set.eq_univ_of_forall hall
    have h1 : Nat.card K ≤ p := by
      calc Nat.card K = Nat.card (Set.range φ) := by rw [hu, Nat.card_univ]
        _ ≤ Nat.card (ZMod p) :=
          Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := φ))
        _ = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
    have h2 : p < p ^ 2 := by nlinarith [hp.out.two_le]
    omega
  obtain ⟨y, hy⟩ := hrange
  refine ⟨y, fun i j hij => ?_⟩
  have hj : (j : ZMod p) = 0 := by
    by_contra hj
    have hjK : (j : K) ≠ 0 := by
      intro h0
      apply hj
      apply φ.injective
      rw [map_natCast, h0, map_zero]
    have hy' : -(i : K) / (j : K) = y := by
      rw [div_eq_iff hjK]
      linear_combination (-1 : K) * hij
    have hi' : (i : K) ∈ φ.fieldRange := RingHom.mem_fieldRange.mpr ⟨(i : ZMod p), map_natCast φ i⟩
    have hj' : (j : K) ∈ φ.fieldRange := RingHom.mem_fieldRange.mpr ⟨(j : ZMod p), map_natCast φ j⟩
    have hmem : y ∈ φ.fieldRange := by
      rw [← hy']
      exact div_mem (neg_mem hi') hj'
    exact hy (RingHom.mem_fieldRange.mp hmem)
  have hjp : p ∣ j := (CharP.cast_eq_zero_iff (ZMod p) p j).mp hj
  have hjK : (j : K) = 0 := (CharP.cast_eq_zero_iff K p j).mpr hjp
  rw [hjK, zero_mul, add_zero, mul_one] at hij
  exact ⟨(CharP.cast_eq_zero_iff K p i).mp hij, hjp⟩

end Independent

section Siegel

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem exists_hypSiegel (hε : ε ≤ 1) {C : Matrix (Fin r) (Fin r) K}
    (hC : C + (C.map h.bar)ᵀ = 0) :
    ∃ g ∈ hypUnitriangular h r ε,
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) - 1 =
        blk3 0 0 C 0 0 0 := by
  have hA : IsUnitriangular (1 : Matrix (Fin r) (Fin r) K) :=
    ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  have hbar1 : barInvT h (1 : Matrix (Fin r) (Fin r) K) = 1 := by
    simp [barInvT, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · obtain ⟨g, hg, hgm⟩ :=
      (exists_mem_hypUnitriangular_even_iff (h := h) (evenMat h 1 C)).mpr ⟨1, C, hA, hC, rfl⟩
    refine ⟨g, hg, ?_⟩
    rw [hgm]
    ext (a | k | a) (b | l | b)
    all_goals first
      | exact isEmptyElim k
      | exact isEmptyElim l
      | simp [evenMat, hbar1, Matrix.one_apply]
  · have hC' : C + (C.map h.bar)ᵀ = -Matrix.vecMulVec (0 : Fin r → K)
        (fun j => h.bar ((0 : Fin r → K) j)) := by simp [hC]
    obtain ⟨g, hg, hgm⟩ :=
      (exists_mem_hypUnitriangular_odd_iff (h := h) (oddDiag h 1 1 * oddUni h 0 C)).mpr
        ⟨1, C, 0, hA, hC', rfl⟩
    refine ⟨g, hg, ?_⟩
    rw [hgm, oddDiag_mul_oddUni]
    ext (a | k | a) (b | l | b)
    all_goals simp [hbar1, Matrix.one_apply, Fin.fin_one_eq_zero]

end Siegel


section Main

variable {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem Lev_one_eq_hypUnitriangular (r ε : ℕ) :
    Lev (matrixHom (hypSU h r ε)) fullPos 1 le_rfl = hypUnitriangular h r ε := by
  ext g
  rw [mem_hypUnitriangular]
  exact mem_Lev_one_iff_blockTriangular fullPos_injective (hypSU h r ε) g

theorem hypSiegel_mem_Lev {C : Matrix (Fin r) (Fin r) K} {k : ℕ} (hk : 1 ≤ k)
    (hCk : ∀ i j : Fin r, C i j ≠ 0 → (i : ℕ) + k ≤ 2 * r + ε - 1 - j) {g : hypSU h r ε}
    (hg : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) - 1 =
      blk3 0 0 C 0 0 0) : g ∈ Lev (matrixHom (hypSU h r ε)) fullPos k hk := by
  rw [mem_Lev, matrixHom_apply, hg]
  rintro (a | a | a) (b | b | b) hab
  · simp
  · simp
  · by_contra hne
    have hCab : C a b ≠ 0 := by simpa using hne
    have := hCk a b hCab
    simp only [fullPos_inl, fullPos_inr_inr] at hab
    omega
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem rankThreeCent_psu {p n f : ℕ} [hp : Fact p.Prime] (hn : 4 ≤ n) {G : Type} [Group G]
    [Finite G] (hm : StatedClassicalModel G .PSU n p f) : RankThreeCent p G := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  letI := hKf
  letI := hKfin
  have hD : UnitaryFieldData p f K := ⟨hp.out, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K p := hD.charP
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  have hr : 2 ≤ r := by omega
  haveI : Nonempty (HypIndex r ε) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport hD (r := r) (ε := ε)
  obtain ⟨-, ⟨P, hP⟩, hUZ, -⟩ := unitary_order_and_Sylow hD (r := r) (ε := ε) (by omega) hε
  let eP := hypPSUEquivStatedProj hD hR (by omega : 1 ≤ 2 * r + ε)
  let π : ↥(hypSU hD r ε) →* G :=
    e.symm.toMonoidHom.comp (eP.toMonoidHom.comp (hypProj hD r ε))
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp (eP.surjective.comp (hypProj_surjective hD r ε))
  have hπinj : ∀ u ∈ Lev (matrixHom (hypSU hD r ε)) fullPos 1 le_rfl, π u = 1 → u = 1 := by
    intro u hu hu1
    rw [Lev_one_eq_hypUnitriangular] at hu
    have h1 : hypProj hD r ε u = 1 := by
      have h2 := e.symm.injective (hu1.trans (map_one e.symm).symm)
      exact eP.injective (h2.trans (map_one eP).symm)
    have hker : u ∈ hypScalars hD r ε := by
      rw [← ker_hypProj]
      exact h1
    have h3 : u ∈ hypUnitriangular hD r ε ⊓ hypScalars hD r ε := ⟨hu, hker⟩
    rw [hUZ] at h3
    exact Subgroup.mem_bot.mp h3
  have hidx : ¬ p ∣ (Lev (matrixHom (hypSU hD r ε)) fullPos 1 le_rfl).index := by
    rw [Lev_one_eq_hypUnitriangular, ← hP]
    exact P.not_dvd_index
  obtain ⟨i0, hi0⟩ : ∃ i : Fin r, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin r, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have h01 : i0 ≠ i1 := fun h' => by have := congrArg Fin.val h'; omega
  let siegC : K → Matrix (Fin r) (Fin r) K := fun x => Matrix.of fun a b =>
    if a = i0 ∧ b = i1 then x else if a = i1 ∧ b = i0 then -hD.bar x else 0
  have hsiegC : ∀ x, siegC x + ((siegC x).map hD.bar)ᵀ = 0 := by
    intro x
    ext a b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply,
      siegC, Matrix.of_apply]
    by_cases hab : a = i0 ∧ b = i1
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h01, h01.symm, hD.bar_bar]
    · by_cases hab' : a = i1 ∧ b = i0
      · obtain ⟨rfl, rfl⟩ := hab'
        simp [h01, h01.symm, hD.bar_bar]
      · have h3 : ¬ (b = i0 ∧ a = i1) := fun h' => hab' ⟨h'.2, h'.1⟩
        have h4 : ¬ (b = i1 ∧ a = i0) := fun h' => hab ⟨h'.2, h'.1⟩
        simp [hab, hab', h3, h4]
  obtain ⟨c, hc⟩ := hD.exists_bar_ne
  have hzbar : (c - hD.bar c) + hD.bar (c - hD.bar c) = 0 := by
    rw [map_sub, hD.bar_bar]
    ring
  have hz0 : c - hD.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  let zC : Matrix (Fin r) (Fin r) K :=
    Matrix.of fun a b => if a = i0 ∧ b = i0 then c - hD.bar c else 0
  have hzC : zC + (zC.map hD.bar)ᵀ = 0 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply,
      zC, Matrix.of_apply]
    by_cases hab : a = i0 ∧ b = i0
    · obtain ⟨rfl, rfl⟩ := hab
      simpa using hzbar
    · have h3 : ¬ (b = i0 ∧ a = i0) := fun h' => hab ⟨h'.2, h'.1⟩
      simp [hab, h3]
  have hpK : p ^ 2 ≤ Nat.card K := by
    rw [hK]
    exact Nat.pow_le_pow_left (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hadm.2.1) 2
  obtain ⟨y, hy⟩ := exists_independent_scalar (K := K) (p := p) hpK
  obtain ⟨g₁, hg₁U, hg₁⟩ := exists_hypSiegel hD hε (hsiegC 1)
  obtain ⟨g₂, hg₂U, hg₂⟩ := exists_hypSiegel hD hε (hsiegC y)
  obtain ⟨b₀, hb₀U, hb₀⟩ := exists_hypSiegel hD hε hzC
  have hk : 1 ≤ 2 * r + ε - 2 := by omega
  have hCk : ∀ x : K, ∀ i j : Fin r, siegC x i j ≠ 0 →
      (i : ℕ) + (2 * r + ε - 2) ≤ 2 * r + ε - 1 - j := by
    intro x i j hij
    by_cases hab : i = i0 ∧ j = i1
    · obtain ⟨rfl, rfl⟩ := hab
      omega
    · by_cases hab' : i = i1 ∧ j = i0
      · obtain ⟨rfl, rfl⟩ := hab'
        omega
      · exfalso
        apply hij
        simp [siegC, hab, hab']
  have hzk : ∀ i j : Fin r, zC i j ≠ 0 → (i : ℕ) + (2 * r + ε - 2 + 1) ≤ 2 * r + ε - 1 - j := by
    intro i j hij
    by_cases hab : i = i0 ∧ j = i0
    · obtain ⟨rfl, rfl⟩ := hab
      omega
    · exfalso
      apply hij
      simp [zC, hab]
  have hlt : ∀ a b : HypIndex r ε, fullPos b < fullPos a + 2 * (2 * r + ε - 2) := fun a b => by
    have := fullPos_lt b
    omega
  have h₁ : g₁ ∈ Lev (matrixHom (hypSU hD r ε)) fullPos (2 * r + ε - 2) hk :=
    hypSiegel_mem_Lev hD hk (hCk 1) hg₁
  have h₂ : g₂ ∈ Lev (matrixHom (hypSU hD r ε)) fullPos (2 * r + ε - 2) hk :=
    hypSiegel_mem_Lev hD hk (hCk y) hg₂
  have hb₀m : b₀ ∈ Lev (matrixHom (hypSU hD r ε)) fullPos (2 * r + ε - 2 + 1) (by omega) :=
    hypSiegel_mem_Lev hD (by omega) hzk hb₀
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun M : Matrix (HypIndex r ε) (HypIndex r ε) K =>
      M (Sum.inl i0) (Sum.inr (Sum.inr i0))) hb₀
    simp only [h1, OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply] at h2
    simp [zC] at h2
    exact hz0 h2.symm
  have hb : fullPos (Sum.inr (Sum.inr i1) : HypIndex r ε) =
      fullPos (Sum.inl i0 : HypIndex r ε) + (2 * r + ε - 2) := by
    simp only [fullPos_inl, fullPos_inr_inr]
    omega
  have e₁ : ((matrixHom (hypSU hD r ε) g₁) - 1) (Sum.inl i0) (Sum.inr (Sum.inr i1)) = 1 := by
    rw [matrixHom_apply, hg₁]
    simp [siegC]
  have e₂ : ((matrixHom (hypSU hD r ε) g₂) - 1) (Sum.inl i0) (Sum.inr (Sum.inr i1)) = y := by
    rw [matrixHom_apply, hg₂]
    simp [siegC]
  exact rankThreeCent_of_corner_ind (ρ := matrixHom (hypSU hD r ε)) (pos := fullPos)
    (matrixHom_injective _) hk hlt π hπ hπinj hidx h₁ h₂ hb₀m hb₀1
    (fun i j hmem => independent_of_entry hlt h₁ h₂ hb e₁ e₂ hy i j hmem)

end Main


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
