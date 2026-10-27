module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSU
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding

open Polynomial Matrix CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section CharThree

variable {E : Type*} [Field E] [CharP E 3]

theorem cube_eq_one_imp_eq_one_charThree {u : E} (hu : u ^ 3 = 1) : u = 1 := by
  have h3 : (3 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 3
  have h : (u - 1) ^ 3 = 0 := by
    have : (u - 1) ^ 3 = u ^ 3 - 1 - 3 * (u ^ 2 - u) := by ring
    rw [this, hu, h3]
    ring
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h)

theorem eq_one_of_cube_eq_one_of_le_one {m : ℕ} (hm : m ≤ 1) {g : GL (Fin m) E}
    (hg : g ^ 3 = 1) : g = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
  · exact Units.ext (Subsingleton.elim _ _)
  · have h00 : ((g : Matrix (Fin 1) (Fin 1) E) 0 0) ^ 3 = 1 := by
      have h1 := congrArg (fun A : GL (Fin 1) E => (A : Matrix (Fin 1) (Fin 1) E) 0 0) hg
      simpa [pow_succ, Matrix.mul_apply] using h1
    have h := cube_eq_one_imp_eq_one_charThree h00
    refine Units.ext ?_
    ext i j
    fin_cases i
    fin_cases j
    simpa using h

end CharThree

theorem two_le_orderOf_nine_zmod {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    2 ≤ orderOf ((9 : ℕ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have h9 : ((9 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    interval_cases p <;> revert h hp <;> decide
  have h1 : ((9 : ℕ) : ZMod p) ≠ 1 := by
    intro h
    have h8 : ((8 : ℕ) : ZMod p) = 0 := by
      have h98 : ((9 : ℕ) : ZMod p) = ((8 : ℕ) : ZMod p) + 1 := by push_cast; ring
      rw [h98] at h
      exact add_eq_right.mp h
    rw [ZMod.natCast_eq_zero_iff] at h8
    have := Nat.le_of_dvd (by norm_num) h8
    interval_cases p <;> revert h8 hp <;> decide
  have hpos : 0 < orderOf ((9 : ℕ) : ZMod p) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one h9⟩)
  have hne1 : orderOf ((9 : ℕ) : ZMod p) ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
  omega

theorem exists_primaryFactor_ne_X_sub_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} (hx : Squarefree (minpoly K x)) (hx1 : x ≠ 1) :
    ∃ c ∈ primaryFactors x, c ≠ X - C 1 := by
  classical
  by_contra hall
  push Not at hall
  have hdvd : minpoly K x ∣ X - C 1 := by
    rw [← prod_primaryFactors hx]
    have hsub : primaryFactors x ⊆ {X - C 1} := fun c hc => Finset.mem_singleton.mpr (hall c hc)
    calc ∏ a ∈ primaryFactors x, a ∣ ∏ a ∈ ({X - C 1} : Finset K[X]), a :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
      _ = X - C 1 := Finset.prod_singleton _ _
  have h0 : aeval x (X - C (1 : K)) = 0 := by
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  apply hx1
  simpa [sub_eq_zero] using h0

variable {K : Type} [Field K] [Finite K]

open scoped _root_.Classical in
theorem eq_one_of_mem_centralizer_gl_three_nine (hK : Nat.card K = 9) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {y g : GL (Fin 3) K} (hy : y ^ p = 1) (hy1 : y ≠ 1)
    (hg : g ∈ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) (hg3 : g ^ 3 = 1) : g = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hpK : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 3]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  set x := Matrix.toLin' (y : Matrix (Fin 3) (Fin 3) K) with hxdef
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← toLinAlgEquiv'_eq_toLin', ← map_pow, ← Units.val_pow_eq_pow_val, hy,
      Units.val_one, map_one]
  have hx := squarefree_minpoly_of_pow_eq_one hpK hxp
  have hx1 : x ≠ 1 := by
    intro h
    apply hy1
    refine Units.ext ?_
    rw [Units.val_one]
    exact Matrix.toLin'.injective (hxdef.symm.trans (h.trans Matrix.toLin'_one.symm))
  obtain ⟨c, hc, hcne⟩ := exists_primaryFactor_ne_X_sub_one hx hx1
  have hdeg : 2 ≤ c.natDegree := by
    have h1 := orderOf_le_natDegree_of_mem_primaryFactors hp hxp hc hcne
    rw [hK] at h1
    exact (two_le_orderOf_nine_zmod hp hp5).trans h1
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx
  rw [Module.finrank_fin_fun] at hsum
  have hmc : 1 ≤ primaryMultiplicity x c := by
    by_contra h0
    have : Fact (Irreducible c) := ⟨irreducible_of_mem_primaryFactors hc⟩
    have hfr := finrank_primaryComponent x c
    rw [show Module.finrank (AdjoinRoot c) (primaryComponent x c) = 0 by
      change primaryMultiplicity x c = 0
      omega, mul_zero] at hfr
    exact primaryComponent_ne_bot hx hc (Submodule.finrank_eq_zero.mp hfr)
  have hle : ∀ s : Finset (primaryFactors x),
      ∑ i ∈ s, (i : K[X]).natDegree * primaryMultiplicity x (i : K[X]) ≤ 3 := fun s =>
    (Finset.sum_le_sum_of_subset (Finset.subset_univ s)).trans hsum.symm.le
  have hmult : ∀ b : primaryFactors x, mult x b ≤ 1 := by
    intro b
    change primaryMultiplicity x (b : K[X]) ≤ 1
    by_cases hbc : (b : K[X]) = c
    · have h1 := hle {b}
      rw [Finset.sum_singleton, hbc] at h1
      rw [hbc]
      by_contra h2
      nlinarith
    · have h1 := hle {b, ⟨c, hc⟩}
      rw [Finset.sum_pair (fun h => hbc (congrArg Subtype.val h))] at h1
      have hb1 : 1 ≤ (b : K[X]).natDegree :=
        (irreducible_of_mem_primaryFactors b.2).natDegree_pos
      change (b : K[X]).natDegree * primaryMultiplicity x (b : K[X]) +
        c.natDegree * primaryMultiplicity x c ≤ 3 at h1
      by_contra h2
      nlinarith
  have hgC : g ∈ (blockTheta hx).range := by
    rw [range_blockTheta hx, range_commutantUnitsToGL_eq_centralizer y hxdef.symm]
    exact hg
  obtain ⟨w, hw⟩ := hgC
  have hw3 : w ^ 3 = 1 := blockTheta_injective hx (by rw [map_pow, hw, hg3, map_one])
  have hw1 : w = 1 := by
    funext b
    have hb3 : (w b) ^ 3 = 1 := by
      have h1 := congrFun hw3 b
      simpa using h1
    have : CharP (Efac x b) 3 :=
      charP_of_injective_algebraMap (algebraMap K (Efac x b)).injective 3
    exact eq_one_of_cube_eq_one_of_le_one (hmult b) hb3
  rw [← hw, hw1, map_one]

omit [Finite K] in
theorem statedScalars_subgroupOf_statedSU_three_three (hK : Nat.card K = 9) (q : ℕ) :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨A, hA⟩ hAs
  rw [Subgroup.mem_subgroupOf] at hAs
  obtain ⟨c, hc⟩ := hAs
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin 3) c = A := hc
  have hdet := CFSG.AGLEmbedding.ParabPrime.det_eq_one_of_mem_statedSU hA
  rw [← hc'] at hdet
  have hc3 : c ^ 3 = 1 := by
    refine Units.ext ?_
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.det_smul] using hdet
  have hc8 : c ^ 8 = 1 := by
    have h1 : Nat.card Kˣ = 8 := by rw [Nat.card_units, hK]
    rw [← h1]
    exact pow_card_eq_one'
  have hc1 : c = 1 := by
    calc c = c ^ 9 * (c ^ 8)⁻¹ := by group
      _ = 1 := by rw [show c ^ 9 = (c ^ 3) ^ 3 by group, hc3, hc8]; group
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  simp [← hc', hc1]

noncomputable def statedProjSUThreeThreeEquiv (hK : Nat.card K = 9) (q : ℕ) :
    StatedProj (StatedSU 3 q K) ≃* StatedSU 3 q K :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSU_three_three hK q)).trans
    QuotientGroup.quotientBot

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag in
theorem card_outer_eq_two_of_model_psu_three_three {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1) : Nat.card (Outer X) = 2 := by
  obtain ⟨⟨hpp, hf, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 3 1 K := ⟨hpp, hf, by rw [hK]; ring⟩
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := fun ⟨_, h2⟩ => by norm_num at h2
  have h1 := (UnitaryHigher.unitary_full_diagonal_outer_order hU le_rfl hq).2.2.2.2.1
  have e' : X ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by omega)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv, h1]
  norm_num

theorem threeAutFixedTwoThree_of_model_psu_three_three {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1) : ThreeAutFixedTwoThree X := by
  have hout := card_outer_eq_two_of_model_psu_three_three h
  obtain ⟨⟨hpp, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨hpp⟩
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  set S := StatedSU 3 (3 ^ 1) K
  let eS : X ≃* S := e.trans (statedProjSUThreeThreeEquiv hK9 _)
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 3 1 hK 3 le_rfl
    (by norm_num)
  have : IsSimpleGroup S := (statedProjSUThreeThreeEquiv hK9 (3 ^ 1)).symm.isSimpleGroup
  have hperf : Group.IsPerfect S :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK le_rfl (by norm_num)
  refine ThreeAutFixedTwoThree.of_mulEquiv eS (threeAutFixedTwoThree_of_inner_prime
    (center_eq_bot_of_simple_of_perfect) ?_ ?_)
  · rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      eS).toEquiv, hout]
    norm_num
  · intro a ha3 hfree y hy p hp hp5 hyp
    have hnt : Nontrivial S := IsSimpleGroup.toNontrivial
    have ha1 : a ≠ 1 := by
      rintro rfl
      have h1 := hfree ⊤ (fun z _ => by
        rw [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul])
        Group.IsPerfect.commutator_eq_top
      exact (top_ne_bot (α := Subgroup S)) h1
    by_contra hy1
    apply ha1
    have hyGL : (y : GL (Fin 3) K) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
    have hcomm : (a : GL (Fin 3) K) ∈ Subgroup.centralizer ({(y : GL (Fin 3) K)} :
        Set (GL (Fin 3) K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)).symm
    refine Subtype.ext (eq_one_of_mem_centralizer_gl_three_nine hK9 hp hp5
      (y := (y : GL (Fin 3) K)) ?_ hyGL hcomm ?_)
    · rw [← Subgroup.coe_pow, hyp, Subgroup.coe_one]
    · rw [← Subgroup.coe_pow, ha3, Subgroup.coe_one]

theorem threeAutFixedTwoThree_lie_twistedA_three (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp3, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
  rw [hp3, hf] at h
  exact threeAutFixedTwoThree_of_model_psu_three_three h

end CFSG.AGLEmbedding
