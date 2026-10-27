module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0c
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesAt

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isSolvable_of_card_two_pow_mul_three_pow_aux {H : Type} [Group H] [Finite H] {a b : ℕ}
    (h : Nat.card H = 2 ^ a * 3 ^ b) : Group.IsSolvable H := by
  let _ : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem gl_zmod3_isSolvable_aux (d : ℕ) (hd : d ≤ 2) : Group.IsSolvable (GL (Fin d) (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  interval_cases d
  · exact isSolvable_of_card_two_pow_mul_three_pow_aux (a := 0) (b := 0)
      (by rw [CFSG.SectionRank.Ccomm.card_GL_zmod]; simp)
  · exact isSolvable_of_card_two_pow_mul_three_pow_aux (a := 1) (b := 0)
      (by rw [CFSG.SectionRank.Ccomm.card_GL_zmod]; simp [Fin.prod_univ_one])
  · exact isSolvable_of_card_two_pow_mul_three_pow_aux (a := 4) (b := 1)
      (by rw [CFSG.SectionRank.Ccomm.card_GL_zmod]; simp [Fin.prod_univ_two])

theorem isSolvable_mulAut_of_isElemAbelian {Y : Type} [Group Y] [Finite Y] {F : Subgroup Y}
    (hF : IsElemAbelian 3 F) (hr : CFSG.Open.pRank 3 F ≤ 2) : Group.IsSolvable (MulAut ↥F) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a b : ↥F, a * b = b * a := fun a b => hF.1.is_comm.comm a b
  have hpow : ∀ a : ↥F, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hF.2 a a.2)
  have hF3 : IsPGroup 3 ↥F := fun w => ⟨1, by rw [pow_one, hpow]⟩
  obtain ⟨d, hd⟩ := hF3.exists_card_eq
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup Y, E ≤ F ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card F, ?_⟩
    rintro k ⟨E, hEF, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card F := Subgroup.card_le_of_le hEF
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    rw [hE] at h1
    exact le_of_lt (lt_of_lt_of_le h2 h1)
  have hdS : d ∈ {k : ℕ | ∃ E : Subgroup Y, E ≤ F ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} :=
    ⟨F, le_rfl, hF, hd⟩
  have hr' : sSup {k : ℕ | ∃ E : Subgroup Y, E ≤ F ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} ≤ 2 := hr
  have hd2 : d ≤ 2 := le_trans (le_csSup hbdd hdS) hr'
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hd
  haveI := gl_zmod3_isSolvable_aux d hd2
  exact solvable_of_solvable_injective (f := (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom)
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective

variable {X : Type} [Group X] [Finite X] {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_card_three_of_seven_gen {M : Subgroup G}
    (hO : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O812sixAt G M) (h7 : 7 ∈ sigmaM G M)
    {B : Subgroup G} (hBM : B ≤ M) (hB3 : Nat.card B = 3)
    (hr : 2 ≤ CFSG.Open.pRank 7 (M ⊓ Subgroup.centralizer (B : Set G)))
    (hns : ¬ CFSG.HallHigman.IsPSolvable 7 ↥(M ⊓ Subgroup.centralizer (B : Set G))) :
    Subgroup.normalizer (B : Set G) ≤ M := by
  have hB3p : IsPGroup 3 ↥B := IsPGroup.of_card (n := 1) (by simpa using hB3)
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB3
    norm_num at hB3
  exact hO 7 h7 (by norm_num)
    B hBM hB3p hBne (isSolvable_mulAut_of_card_three hB3) hr hns

end CFSG.LocalAnalysis.RankThreeUC.S15
