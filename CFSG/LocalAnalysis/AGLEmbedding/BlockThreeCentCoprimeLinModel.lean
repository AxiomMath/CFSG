module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeLin
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {K : Type} [Field K] {n : ℕ}

theorem units_eq_one_of_card_eq_two (hK : Nat.card K = 2) (c : Kˣ) : c = 1 := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _

theorem statedScalars_eq_bot_of_card_eq_two (hK : Nat.card K = 2) :
    StatedScalars (Fin n) K = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [units_eq_one_of_card_eq_two hK c, map_one]
  exact Subgroup.one_mem _

theorem center_gl_eq_bot_of_card_eq_two (hK : Nat.card K = 2) :
    Subgroup.center (GL (Fin n) K) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact statedScalars_eq_bot_of_card_eq_two hK

theorem statedSL_eq_top_of_card_eq_two (hK : Nat.card K = 2) : StatedSL n K = ⊤ := by
  rw [eq_top_iff]
  intro A _
  refine Subgroup.subset_closure ?_
  have h := units_eq_one_of_card_eq_two hK (Matrix.GeneralLinearGroup.det A)
  have h1 := congrArg Units.val h
  simpa using h1

noncomputable def statedProjSLEquivGL (hK : Nat.card K = 2) :
    StatedProj (StatedSL n K) ≃* GL (Fin n) K :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [statedScalars_eq_bot_of_card_eq_two hK, Subgroup.bot_subgroupOf])).trans
    ((QuotientGroup.quotientBot).trans
      ((MulEquiv.subgroupCongr (statedSL_eq_top_of_card_eq_two hK)).trans Subgroup.topEquiv))

theorem threeAutFixedTwoThree_gl_of_card_eq_two [Finite K] (hK : Nat.card K = 2)
    (h3 : ¬ 3 ∣ Nat.card (Outer (GL (Fin n) K))) : ThreeAutFixedTwoThree (GL (Fin n) K) := by
  intro α hα3 hfree x hx m hm hxm
  have hZ := center_gl_eq_bot_of_card_eq_two (n := n) hK
  rw [hZ, Subgroup.mem_bot] at hx hxm ⊢
  have hcop : (3 : ℕ).Coprime (Nat.card (Outer (GL (Fin n) K))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨a, rfl⟩ := exists_conj_eq_of_pow_eq_one_of_coprime hα3 hcop
  have ha3 : a ^ 3 = 1 := by
    have h1 := mem_center_of_mulAut_conj_eq_one (z := a ^ 3) (by rw [map_pow, hα3])
    rwa [hZ, Subgroup.mem_bot] at h1
  have hfree' : ∀ Q : Subgroup (GL (Fin n) K),
      Q ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) → ⁅Q, Q⁆ = Q → Q = ⊥ := by
    intro Q hQC hQ
    refine hfree Q hQ fun y hy => ?_
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp (hQC hy)
    rw [MulAut.conj_apply, ← hy', mul_inv_cancel_right]
  have hxC : x ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : MulAut.conj a x = x := (inv_mul_eq_one.mp hx).symm
    rw [MulAut.conj_apply] at h1
    calc x * a = a * x * a⁻¹ * a := by rw [h1]
      _ = a * x := by group
  exact eq_one_of_mem_centralizer_of_card_eq_two hK ha3 hfree' hxC
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxm) hm)

theorem not_three_dvd_of_dvd_two {m : ℕ} (h : m ∣ 2) : ¬ 3 ∣ m := fun h3 => by
  have := h3.trans h
  norm_num at this

theorem threeAutFixedTwoThree_of_model_psl_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL n 2 1) : ThreeAutFixedTwoThree X := by
  have h3 := not_three_dvd_of_dvd_two (card_outer_dvd_two_of_psl_two h)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  set e' : X ≃* GL (Fin n) K := e.trans (statedProjSLEquivGL hK)
  refine ThreeAutFixedTwoThree.of_mulEquiv e' (threeAutFixedTwoThree_gl_of_card_eq_two hK ?_)
  rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]

theorem threeAutFixedTwoThree_of_model_psl_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : ThreeAutFixedTwoThree X := by
  have h3 := not_three_dvd_of_dvd_two (card_outer_dvd_two_of_psl_seven h)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF, pow_one]
  let φ : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let f₁ : StatedProj (StatedSL 2 F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  set e' : X ≃* GL (Fin 3) (ZMod 2) := (e.trans f₁).trans e₄.symm
  refine ThreeAutFixedTwoThree.of_mulEquiv e'
    (threeAutFixedTwoThree_gl_of_card_eq_two (by rw [Nat.card_zmod]) ?_)
  rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]

theorem threeAutFixedTwoThree_lie_A_two (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ (r : ℕ) (q : TauCeti.PrimePower), q.card = 2 ∧ d.1 = .A r q) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp2, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv (MulEquiv.refl _)
  rw [hp2, hf] at h
  exact threeAutFixedTwoThree_of_model_psl_two h

theorem threeAutFixedTwoThree_lie_A_seven (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp7, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv (MulEquiv.refl _)
  rw [hp7, hf] at h
  exact threeAutFixedTwoThree_of_model_psl_seven h

end CFSG.AGLEmbedding
