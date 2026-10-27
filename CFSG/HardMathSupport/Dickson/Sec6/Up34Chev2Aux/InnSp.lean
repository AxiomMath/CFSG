module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnL3
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnSpGen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.RankThree.PartOne.KCPrimary
  CFSG.ComponentClassification.CatLeaf CFSG.RankThree.PartOne.Sec66T
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open scoped commutatorElement
open Up34Chev2

namespace Up34Chev2

section Blocks

variable {r f : ℕ} {K : Type} [Field K] [Finite K]

theorem ker_proj_eq_bot (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    (SymplecticFlag.proj r K).ker = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  rw [SymplecticHigher.ker_proj]
  exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot


theorem hno_sp_factor (hO : LieOrderFormulasInput) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks 2 f 3 x a)
    (h : primaryFactors (spEnd x))
    (hq : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆)
    (hL : IsLThreeFour (↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
        spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ ⧸
      Subgroup.center ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
        spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆)) :
    ∃ z : StatedSp r K,
      z ∈ ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
        spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ ∧
      (∀ g ∈ ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
        spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆, g * z = z * g) ∧
      z ^ 3 = 1 ∧ SymplecticFlag.proj r K z ≠ 1 := by
  classical
  have hker := ker_proj_eq_bot (r := r) hf hK
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO' : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO'] at hq hL ⊢
    exfalso
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      obtain ⟨s, hs2, ⟨E⟩⟩ :=
        CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
          (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
          (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      exact false_of_statedSp_block _ hf hs hK (φ.trans E) hL
    · obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact false_of_sesqU_block hO _ hE hHf hHfl φ hq hL
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    have hE : Nat.card (AdjoinRoot (h : K[X])) = 2 ^ (f * (h : K[X]).natDegree) := by
      rw [hP.card_field, ← pow_mul]
    have h4 : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      have hdeg : 1 ≤ (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      have hN : 2 ^ f ≤ (2 ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
      have hle := Nat.le_of_dvd (by omega) hP.dvd
      rw [hP.card_field]
      omega
    exact hno_gl_block hO (SymplecticFlag.proj r K) hker _ φ hE h4 hq hL

theorem hno_sp_orbit (hO : LieOrderFormulasInput) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks 2 f 3 x a)
    (O : reciprocalOrbits (spEnd x))
    (hq : CFSG.IsQuasisimple ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆)
    (hL : IsLThreeFour (↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ⧸
      Subgroup.center ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆)) :
    ∃ z : StatedSp r K, z ∈ ⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ∧
      (∀ g ∈ ⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆, g * z = z * g) ∧
      z ^ 3 = 1 ∧ SymplecticFlag.proj r K z ≠ 1 := by
  obtain ⟨O, h, hh, rfl⟩ := O
  exact hno_sp_factor hO hf hK hsq blocks ⟨h, hh⟩ hq hL

theorem noL34Layer_conj_sp (hO : LieOrderFormulasInput) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (hK : Nat.card K = 2 ^ f) (x : StatedSp r K) (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    NoL34Layer (MulAut.conj (SymplecticFlag.proj r K x)) := by
  classical
  have hker := ker_proj_eq_bot (r := r) hf hK
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [hker]
    exact bot_le
  have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h1 => hx1 (by
    have : x ∈ (SymplecticFlag.proj r K).ker := h1
    rwa [hker, Subgroup.mem_bot] at this)
  have ha : orderOf (SymplecticFlag.proj r K x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = 3 := orderOf_eq_prime hx hx1
  have blocks := (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
    Nat.prime_two hf hK Nat.prime_three (by norm_num) (by norm_num) hr _ ha).2 x rfl hxp
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    have := three_ne_zero_of_card_two_pow hf hK
    exact_mod_cast this
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  exact noL34Layer_conj_of_orbit_family (SymplecticFlag.proj r K) SymplecticHigher.proj_surjective
    hZc x (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => quasisimple_or_solvable_spSupported (ℓ := 2) (f := f) (p := 3) (by norm_num)
      hq2 hsq blocks O)
    (fun O hq hL => hno_sp_orbit hO hf hK hsq blocks O hq hL)

end Blocks

end Up34Chev2

section Family


theorem up34C2Inn_B_holds : Up34Chev2Inn FamB := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hc
    have hr2 : 2 ≤ r := (((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)).1
    have hm := blueprintLieModel_B r q hv hq2 e
    have hC : StatedClassicalModel S .PSp r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hC
    rw [hq2] at hK hadm
    haveI := hs
    obtain ⟨hx3, hx1, hnl⟩ := (up34Pumpup_iff _).1 hx
    have hcen : Subgroup.center S = ⊥ := up34_center_eq_bot_of_simple hnab
    have hxcube : x ^ 3 = 1 := by
      have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hx3
      have h2 : x ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut S => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      rw [hcen, Subgroup.mem_bot] at h2
      exact h2
    obtain ⟨x', hxy⟩ := SymplecticHigher.proj_surjective (e0 x)
    have hx'3 : x' ^ 3 = 1 := by
      have : x' ^ 3 ∈ (SymplecticFlag.proj r K).ker := by
        rw [MonoidHom.mem_ker, map_pow, hxy, ← map_pow, hxcube, map_one]
      rwa [ker_proj_eq_bot hadm.2.1 hK, Subgroup.mem_bot] at this
    have hx'1 : x' ≠ 1 := by
      rintro rfl
      apply hx1
      have h1 : e0 x = 1 := by rw [← hxy, map_one]
      have h2 : x = 1 := e0.injective (by rw [h1, map_one])
      rw [h2, map_one]
    haveI : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv S e0.toEquiv
    have h1 : NoL34Layer (MulAut.congr e0 (MulAut.conj x)) := by
      rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj, ← hxy]
      exact noL34Layer_conj_sp CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
        hadm.2.1 (by omega) hK x' hx'3 hx'1
    exact hnl (noL34Layer_congr e0 h1)
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
