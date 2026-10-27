module

public import CFSG.ClassicalInvolution.Q3.TL4ExitDichM
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12A
public import CFSG.ClassicalInvolution.Q3.TL4MF163L33
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3Z
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Q3
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Q5

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace MF163

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}

omit [Finite X] in
theorem fstar_nonabelian_of_nontrivial [Nontrivial (FStarQuot X)] :
    ∃ a b : genFittingFStar X, a * b ≠ b * a := by
  by_contra hcomm
  simp only [not_exists, ne_eq, not_not] at hcomm
  obtain ⟨q, hq⟩ := exists_ne (1 : FStarQuot X)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  exact hq ((QuotientGroup.eq_one_iff n).mpr (Subgroup.mem_center_iff.mpr fun y => hcomm y n))

theorem card_fstarQuot_dvd_m12
    [IsSimpleGroup ↥(genFittingFStar X)] (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a)
    (he : Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12)) :
    Nat.card (FStarQuot X) ∣ 95040 := by
  obtain ⟨e⟩ := isSporadic_of_center_quot hnab he
  have hc : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  rw [← hc, ← Nat.card_congr e.toEquiv]
  exact MFMuZ2.card_fstarQuot_dvd

theorem concl163Syl_of_exit_psl3
    (hm : EdgelessMember3 R S z)
    (hout : ¬ TightActs3 R z ∨ Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))
    [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ} (hp2 : p ≠ 2)
    (hl : LieModel (FStarQuot X) .PSL 3 p f) : Concl163Syl R S z := by
  obtain ⟨hp, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hl
  have := (LieType.Simplicity.fam_PSL_simplicity _ 3 p f
    (CFSG.GH74.Generic.stated_of_lieModel_PSL hl)).1
  have hnab := fstar_nonabelian_of_nontrivial (X := X)
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
  by_cases hq3 : p ^ f = 3
  · exfalso
    obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
    rcases hout with h3 | he
    · obtain ⟨eQ⟩ := GH74.KGroups.L33.equiv_of_lieModel hl
      have : (genFittingFStar X).Normal := genFittingFStar_normal X
      exact h3 (tightActs3_of_l33 (centralizer_genFittingFStar_eq_bot hnab) (eF.trans eQ)
        hm.datum hm.cls)
    · have h1 := MFMuZ2.card_psl3_mul K
      rw [← Nat.card_congr e₀.toEquiv, hK] at h1
      have h2 := card_fstarQuot_dvd_m12 hnab he
      norm_num at h1
      rw [h1] at h2
      norm_num at h2
  · have h5 : 5 ≤ p ^ f := by
      have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      obtain ⟨k, hk⟩ := hodd
      omega
    let e₁ : FStarQuot X ≃* projectiveSL 3 K :=
      (e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
    exact L3.concl163Syl_of_psl3 hm hp hp2 hf hK h5 (eF.trans e₁)

theorem concl163Syl_of_exit_psu3
    (hm : EdgelessMember3 R S z)
    (hout : ¬ TightActs3 R z ∨ Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))
    [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (FStarQuot X) .PSU 3 p f) : Concl163Syl R S z := by
  obtain ⟨hp, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 p f
    (CFSG.GH74.Generic.stated_of_lieModel_PSU hL)).1
  have hnab := fstar_nonabelian_of_nontrivial (X := X)
  have hC := centralizer_genFittingFStar_eq_bot hnab
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
  by_cases h3q : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3q
    rcases hout with h3 | he
    · exact U3.concl163Syl_u3_three hm.datum hm.cls.1 hm.cls.2.1 h3 hC
        (MFMuZ2.lieModel_of_mulEquiv_classical eF (Or.inr rfl) hL)
    · exfalso
      have h1 := MFMuZ2.card_psu3_mul hp hf hK
      rw [← Nat.card_congr e₀.toEquiv] at h1
      have h2 := card_fstarQuot_dvd_m12 hnab he
      norm_num at h1
      rw [h1] at h2
      norm_num at h2
  · have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq3 : 3 ≤ p ^ f := by
      have h2 := hp.two_le
      have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      omega
    have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ p ^ f := by omega
    exact U3.concl163Syl_ge_five hm.datum hm.cls.1 hC h hp2 h5 (eF.trans e₀)

theorem concl163Syl_of_exit_m12
    (hm : EdgelessMember3 R S z)
    (hout : ¬ TightActs3 R z ∨ Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))
    [IsSimpleGroup ↥(genFittingFStar X)] (h : NativeSporadic.IsSporadic (FStarQuot X) .M12) :
    Concl163Syl R S z := by
  rcases hout with h3 | he
  · exact absurd (modelM12Acts3_proved X R S z hm inferInstance (index_le_two_of_m12 h) h) h3
  · obtain ⟨e⟩ := h
    have e' : FStarQuot X ≃* ↥NativeSporadic.M12 := e
    have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.1
    have : Nontrivial (FStarQuot X) := e'.toEquiv.nontrivial
    exact concl163Syl_m12 hm (isSporadic_of_center_quot fstar_nonabelian_of_nontrivial he)

theorem concl163Syl_of_exit
    (hm : EdgelessMember3 R S z)
    (hout : ¬ TightActs3 R z ∨ Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))
    [IsSimpleGroup ↥(genFittingFStar X)]
    (hF : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (LieModel (FStarQuot X) .PSL 3 p f ∨ LieModel (FStarQuot X) .PSU 3 p f)) ∨
      NativeSporadic.IsSporadic (FStarQuot X) .M12) : Concl163Syl R S z := by
  rcases hF with ⟨p, f, -, hp2, hl | hl⟩ | h
  · exact concl163Syl_of_exit_psl3 hm hout hp2 hl
  · exact concl163Syl_of_exit_psu3 hm hout hp2 hl
  · exact concl163Syl_of_exit_m12 hm hout h

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
