module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenSu2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
  CFSG.ClassicalInvolution.Phan CFSG.GH74.Generic.BProg.B2.GenLocU4Aux CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

namespace GenLocU4Out

variable {K : Type} [Field K] {p f : ℕ}

theorem anti_a_sq {A0 : Matrix (Fin 2) (Fin 2) K} (hA0sq : A0 * A0 = 1) (X : Matrix (Fin 2) (Fin 2) K) :
    A0 * (A0 * X * A0) * A0 = X := by
  calc A0 * (A0 * X * A0) * A0 = (A0 * A0) * X * (A0 * A0) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hA0sq, Matrix.one_mul, Matrix.mul_one]

theorem anti_b_sq {N : Matrix (Fin 2) (Fin 2) K} (hNsq : N * N = -1) (X : Matrix (Fin 2) (Fin 2) K) :
    N * (N * X * -N) * -N = X := by
  calc N * (N * X * -N) * -N = (N * N) * X * (N * N) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    _ = X := by rw [hNsq]; simp

theorem anti_comm {A0 N : Matrix (Fin 2) (Fin 2) K} (hanti : A0 * N = -(N * A0))
    (X : Matrix (Fin 2) (Fin 2) K) : A0 * (N * X * -N) * A0 = N * (A0 * X * A0) * -N := by
  have hQP : N * A0 = -(A0 * N) := by rw [hanti, neg_neg]
  calc A0 * (N * X * -N) * A0 = -((A0 * N) * X * (N * A0)) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -((N * A0) * X * (A0 * N)) := by
        rw [hQP]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    _ = N * (A0 * X * A0) * -N := by
        simp only [Matrix.mul_neg, Matrix.mul_assoc]

theorem anti_fix_a {A0 : Matrix (Fin 2) (Fin 2) K} (hA0sq : A0 * A0 = 1) {X : Matrix (Fin 2) (Fin 2) K}
    (h : A0 * X * A0 = X) : A0 * X = X * A0 := by
  calc A0 * X = A0 * X * (A0 * A0) := by rw [hA0sq, Matrix.mul_one]
    _ = (A0 * X * A0) * A0 := by simp only [Matrix.mul_assoc]
    _ = X * A0 := by rw [h]

theorem anti_fix_b {N : Matrix (Fin 2) (Fin 2) K} (hNsq : N * N = -1) {X : Matrix (Fin 2) (Fin 2) K}
    (h : N * X * -N = X) : N * X = X * N := by
  have e : N * X * -N * N = X * N := by rw [h]
  have e2 : N * X * -N * N = N * X := by
    calc N * X * -N * N = -(N * X * (N * N)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = N * X := by rw [hNsq]; simp
  rw [← e2, e]

theorem anti_fix_ab {A0 N : Matrix (Fin 2) (Fin 2) K} (hA0sq : A0 * A0 = 1) (hNsq : N * N = -1)
    (hanti : A0 * N = -(N * A0)) {X : Matrix (Fin 2) (Fin 2) K}
    (h : A0 * (N * X * -N) * A0 = X) : (A0 * N) * X = X * (A0 * N) := by
  have hQP : N * A0 = -(A0 * N) := by rw [hanti, neg_neg]
  have hPP : (A0 * N) * (A0 * N) = 1 := by
    calc (A0 * N) * (A0 * N) = A0 * (N * A0) * N := by simp only [Matrix.mul_assoc]
      _ = -(A0 * (A0 * N) * N) := by rw [hQP]; simp only [Matrix.mul_neg, Matrix.neg_mul]
      _ = -((A0 * A0) * (N * N)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA0sq, hNsq]; simp
  have hPXP : (A0 * N) * X * (A0 * N) = X := by
    have e : A0 * (N * X * -N) * A0 = (A0 * N) * X * (A0 * N) := by
      calc A0 * (N * X * -N) * A0 = -((A0 * N) * X * (N * A0)) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = (A0 * N) * X * (A0 * N) := by
            rw [hQP]; simp only [Matrix.mul_neg, neg_neg]
    rw [← e]
    exact h
  calc (A0 * N) * X = (A0 * N) * X * ((A0 * N) * (A0 * N)) := by rw [hPP, Matrix.mul_one]
    _ = ((A0 * N) * X * (A0 * N)) * (A0 * N) := by simp only [Matrix.mul_assoc]
    _ = X * (A0 * N) := by rw [hPXP]

section Anti

variable [Finite K] [Fact p.Prime] [CharP K p]

theorem su2_gen_of_anti
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    {G : Type} [Group G] (φ : Su K p f 2 →* G) (Γ : Subgroup G) (A0 N : Matrix (Fin 2) (Fin 2) K)
    (hA0u : (A0.map (· ^ (p ^ f)))ᵀ * A0 = 1) (hA0sq : A0 * A0 = 1)
    (hA0det : ∀ lam : K, lam ^ (p ^ f) * lam = 1 → lam * lam ≠ A0.det)
    (hNdet : N.det = 1) (hNu : (N.map (· ^ (p ^ f)))ᵀ * N = 1) (hNsq : N * N = -1)
    (hNs : ∀ lam : K, N ≠ lam • (1 : Matrix (Fin 2) (Fin 2) K)) (hanti : A0 * N = -(N * A0))
    (hI : ∀ x : Su K p f 2, A0 * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A0 → φ x ∈ Γ)
    (hII : ∀ x : Su K p f 2, N * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * N → φ x ∈ Γ)
    (hIII : ∀ x : Su K p f 2, (A0 * N) * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A0 * N) → φ x ∈ Γ) :
    ∀ x, φ x ∈ Γ := by
  have hp : p.Prime := Fact.out
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h5 := GenLocU4ExtCore.five_le_of_mod_four hK hq4
  let Agl : GL (Fin 2) K := ⟨A0, A0, hA0sq, hA0sq⟩
  have hAmem : Agl ∈ primeFormUnitary h (idGram K 2) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    exact hA0u
  let a : MulAut (Su K p f 2) := cU2 h Agl hAmem
  let n : Su K p f 2 := su2Mk (p := p) (f := f) N hNdet hNu
  let b : MulAut (Su K p f 2) := MulAut.conj n
  have hninv : (((n⁻¹ : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -N := by
    have e : ((((n : Su K p f 2) : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -N :=
      Units.inv_eq_of_mul_eq_one_left (by
        show -N * N = 1
        rw [Matrix.neg_mul, hNsq, neg_neg])
    exact e
  have coe_a : ∀ x : Su K p f 2, (((a x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      A0 * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A0 := by
    intro x
    rw [coe_cU2]
    rfl
  have coe_b : ∀ x : Su K p f 2, (((b x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      N * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * -N := by
    intro x
    show ((((n * x * n⁻¹ : Su K p f 2)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hninv]
    rfl
  have haa : a * a = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
    show (((a (a x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [coe_a, coe_a]
    exact anti_a_sq hA0sq _
  have hbb : b * b = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
    show (((b (b x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [coe_b, coe_b]
    exact anti_b_sq hNsq _
  have hab : a * b = b * a := by
    refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
    show (((a (b x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((b (a x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    rw [coe_a, coe_b, coe_b, coe_a]
    exact anti_comm hanti _
  have a_not_inner : ∀ s : Su K p f 2, MulAut.conj s ≠ a := by
    intro s
    refine GenLocU4Gen.conj_ne_of_det hK hp2 (by omega) Agl hA0u a ?_ hA0det s
    intro g
    rw [coe_a]
    rfl
  have ha1 : a ≠ 1 := fun h1 => a_not_inner 1 (by rw [map_one]; exact h1.symm)
  have hb1 : b ≠ 1 := by
    intro h1
    have hc : ∀ g : Su K p f 2, N * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * N := by
      intro g
      have e1 := congrArg (fun w : MulAut (Su K p f 2) =>
        (((w g : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1
      simp only [MulAut.one_apply] at e1
      have e2 : (((b g : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := e1
      rw [coe_b] at e2
      exact anti_fix_b hNsq e2
    obtain ⟨lam, hlam⟩ := GenLocU4Gen.commutant_su2_scalar hK hp2 (by omega) N hc
    exact hNs lam hlam
  have hne : a ≠ b := fun he => a_not_inner n he.symm
  let V : Subgroup (MulAut (Su K p f 2)) := FourGroup.kleinFourOf a b haa hbb hab
  have hVea : CFSG.IsElementaryAbelian 2 ↥V := FourGroup.isElementaryAbelian_kleinFourOf
  have hVcard : Nat.card ↥V = 4 := FourGroup.card_kleinFourOf ha1 hb1 hne
  have hrank : pRank 2 ↥V = 2 := by
    have h1 := GenLocBasic.card_eq_two_pow_pRank_type hVea
    rw [hVcard] at h1
    exact (Nat.pow_right_injective (le_refl 2) (by simpa using h1.symm : 2 ^ pRank 2 ↥V = 2 ^ 2))
  let β : ↥V →* MulAut (Su K p f 2) := V.subtype
  have haV : a ∈ V := FourGroup.left_mem_kleinFourOf
  have hmix : ¬ β.range ≤ (MulAut.conj : Su K p f 2 →* MulAut (Su K p f 2)).range := by
    intro hle
    obtain ⟨s, hs⟩ := hle ⟨⟨a, haV⟩, rfl⟩
    exact a_not_inner s hs
  have hgam : gammaAct β = ⊤ :=
    GenLocU4Gen.gammaAct_su2_mixed_rank2 hp2 hK h5 ⟨hVea, Or.inl hrank⟩ hrank β (Or.inr hmix)
  have hnontriv : ∀ E : Subgroup ↥V, pRank 2 ↥V - 1 ≤ pRank 2 ↥E → ∃ e ∈ E, e ≠ 1 := by
    intro E hE
    have hidx := (GenLocBasic.adm_iff_index hVea E).1 hE
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
    rw [hbot, Subgroup.index_bot, hVcard] at hidx
    omega
  have hle : gammaAct β ≤ Γ.comap φ := by
    refine iSup₂_le fun E hE w0 hw0 => ?_
    have hw0' := (GenLocBasic.mem_fixedIn_map β E w0).1 hw0
    obtain ⟨e, heE, he1⟩ := hnontriv E hE
    have hfix : (e : MulAut (Su K p f 2)) w0 = w0 := hw0' e heE
    show φ w0 ∈ Γ
    rcases FourGroup.mem_kleinFourOf.1 e.2 with h1 | h1 | h1 | h1
    · exact absurd (Subtype.ext h1) he1
    · rw [h1] at hfix
      have e1 := congrArg (fun w : Su K p f 2 => ((w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hfix
      simp only [coe_a] at e1
      exact hI w0 (anti_fix_a hA0sq e1)
    · rw [h1] at hfix
      have e1 := congrArg (fun w : Su K p f 2 => ((w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hfix
      simp only [coe_b] at e1
      exact hII w0 (anti_fix_b hNsq e1)
    · rw [h1] at hfix
      have e1 := congrArg (fun w : Su K p f 2 => ((w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hfix
      simp only [MulAut.mul_apply, coe_a, coe_b] at e1
      exact hIII w0 (anti_fix_ab hA0sq hNsq hanti e1)
  intro x
  exact hle (hgam ▸ Subgroup.mem_top x)

end Anti

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
