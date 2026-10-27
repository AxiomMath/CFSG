module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.WeakCT.Amalgam

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

variable (p f : ℕ) [Fact p.Prime]

theorem sl2_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    IsClassicalMember p f (⊤ : Subgroup SL(2, GaloisField p f)) (-1) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]; exact (Nat.Prime.odd_of_ne_two (Fact.out) hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  have h3 : 3 ≤ Nat.card (GaloisField p f) := by omega
  have hO : classicalInvolutionOddCore (↥(⊤ : Subgroup SL(2, GaloisField p f))) = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun N hN => ?_)
    exact (normal_odd_of_equiv_sl2 hodd h3 (Subgroup.topEquiv (G := SL(2, GaloisField p f))) N
      hN.1 hN.2).le
  refine ⟨sl2_orderOf_neg_one hodd, Subgroup.mem_top _, ?_, ?_, ?_⟩
  · exact isPerfect_of_equiv_sl2 h4 (Subgroup.topEquiv (G := SL(2, GaloisField p f)))
  · have : Subgroup.centralizer ({(-1 : SL(2, GaloisField p f))} : Set SL(2, GaloisField p f)) =
        ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      rintro x rfl
      exact (mem_center_sl2_iff _).mpr (Or.inr rfl)
    rw [this]
    exact IsSubnormal.refl _
  · exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans
      (Subgroup.topEquiv (G := SL(2, GaloisField p f)))⟩

theorem sl2_inClass (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    InClass p f ({⊤} : Set (Subgroup SL(2, GaloisField p f))) where
  nonempty := ⟨⊤, rfl⟩
  conjInvariant := by
    rintro n K rfl
    show conjSub n ⊤ = ⊤
    ext x
    simp [mem_conjSub_iff]
  generated := by simp
  classical := by
    rintro L rfl
    exact ⟨-1, sl2_isClassicalMember p f hp2 hq⟩

theorem blockMat_two_zero {F : Type} [Field F] (A : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 2 0 A = A := by
  have h : CFSG.ClassicalInvolution.Phan.blockSel F 2 2 0 = 1 := by
    ext a j
    simp [CFSG.ClassicalInvolution.Phan.blockSel_apply, Matrix.one_apply, Fin.ext_iff]
  simp [CFSG.ClassicalInvolution.Phan.blockMat, h]

theorem sl2_top_mem_fundamentalSubgroups :
    (⊤ : Subgroup SL(2, GaloisField p f)) ∈
      fundamentalSubgroups .PSL (SpecialLinear.rootDatum 1 (GaloisField p f)) := by
  have hroot : (Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ) ∈
      (SpecialLinear.rootDatum 1 (GaloisField p f)).roots := by
    refine Or.inl ⟨1, (0 : Fin 1), ?_⟩
    simp only [map_one, Module.End.one_apply]
    rfl
  refine ⟨1, (Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ), Or.inl ⟨hroot, ?_⟩, ?_⟩
  · rintro δ (⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩)
    · rw [CFSG.LieType.RootSystem.form_weylAction]
      have : i = (0 : Fin 1) := Fin.ext (by
        have := i.2
        have h1 : (SpecialLinear.rootDatum 1 (GaloisField p f)).rank = 1 := rfl
        omega)
      subst this
      exact le_rfl
    · exact (Set.notMem_empty _ hi).elim
  · rw [conjSub_one]
    have h2 : (WeakCT.blockSL2 (GaloisField p f) 1 (0 : Fin 1)).range = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact blockMat_two_zero (x : Matrix (Fin 2) (Fin 2) (GaloisField p f))
    exact h2.symm.trans (WeakCT.rankOne_eq_range (K := GaloisField p f) (0 : Fin 1)).symm

theorem sl2_lieSystemMod (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    LieSystemMod p f ({⊤} : Set (Subgroup SL(2, GaloisField p f))) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]; exact (Nat.Prime.odd_of_ne_two (Fact.out) hp2).pow
  have h3 : 3 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  have hO : classicalInvolutionOddCore SL(2, GaloisField p f) = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun N hN => ?_)
    exact (normal_odd_of_equiv_sl2 hodd h3 (MulEquiv.refl SL(2, GaloisField p f)) N
      hN.1 hN.2).le
  let mkQ : SL(2, GaloisField p f) →* SL(2, GaloisField p f) ⧸
      classicalInvolutionOddCore SL(2, GaloisField p f) :=
    QuotientGroup.mk' _
  have hmkQ : Function.Surjective mkQ := QuotientGroup.mk'_surjective _
  refine ⟨{
    card := 1
    tag := fun _ => .PSL
    rank := fun _ => 2
    exp := fun _ => f
    hom := fun _ => mkQ
    isFundTag := fun _ => trivial
    admissible := ?_
    exp_eq := ?_
    ker_le_center := ?_
    commute := ?_
    generate := ?_
    fundamental := ?_
    meets := ?_ }⟩
  · intro i
    refine ⟨Fact.out, ?_, ?_, ?_, ?_⟩
    · omega
    · exact le_rfl
    · simp [Prod.ext_iff]
      omega
    · simp [Prod.ext_iff]
      omega
  · intro i; exact Or.inl rfl
  · intro i
    have h : mkQ.ker ≤ Subgroup.center SL(2, GaloisField p f) := by
      rw [show mkQ.ker = classicalInvolutionOddCore SL(2, GaloisField p f) from
        QuotientGroup.ker_mk' _, hO]
      exact bot_le
    exact h
  · intro i j h; exact absurd (Subsingleton.elim i j) h
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hmkQ x
    exact Subgroup.mem_iSup_of_mem (0 : Fin 1) ⟨y, rfl⟩
  · rintro L ⟨L₀, hL₀, rfl⟩
    rw [Set.mem_singleton_iff] at hL₀
    subst hL₀
    exact ⟨0, ⊤, sl2_top_mem_fundamentalSubgroups p f, rfl⟩
  · intro i
    exact ⟨⊤, sl2_top_mem_fundamentalSubgroups p f, ⊤, rfl, rfl⟩

theorem modelClauseZero_sl2 (p e : ℕ) (hp : p.Prime)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p e) :
    CFSG.Open.IsQuasisimple (modelUniv .PSL 2 p e hp).K ∧
      CFSG.Blueprint.LieModel
        ((modelUniv .PSL 2 p e hp).K ⧸ Subgroup.center (modelUniv .PSL 2 p e hp).K)
        .PSL 2 p e := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, he, -, h22, h23⟩ := id hadm
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have h2 : 2 ≤ p ^ e := by
    have := Nat.one_lt_pow (show e ≠ 0 by omega) hp.one_lt
    omega
  have h22' : p ^ e ≠ 2 := fun h => h22 (by simp [h])
  have h23' : p ^ e ≠ 3 := fun h => h23 (by simp [h])
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by rw [hcard]; omega
  refine ⟨⟨(sl2_isPerfect h4).1, ?_⟩, Or.inl ⟨by decide, ?_⟩⟩
  · exact CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  · exact CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1
      (GaloisField p e) hadm hcard

end CFSG.ClassicalInvolution.Generic
