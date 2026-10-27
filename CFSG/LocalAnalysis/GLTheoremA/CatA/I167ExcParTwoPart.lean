module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParDefs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoF4
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Root
import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoOrders
import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLangEnnola
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open

private theorem g1ord_val {k P g : ℕ} (hP : Odd P) (hg : g ∣ P) :
    padicValNat 2 (2 ^ k * P / g) = k := by
  have hgo : Odd g := hP.of_dvd_nat hg
  rw [padicValNat.div' (Nat.coprime_two_left.2 hgo) (Dvd.dvd.mul_left hg _),
    padicValNat.mul (by positivity) hP.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hP.not_two_dvd_nat, add_zero]

private theorem g1ord_even_pow {f i : ℕ} (hf : 1 ≤ f) (hi : 1 ≤ i) : Even ((2 ^ f) ^ i) :=
  Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by omega⟩

private theorem g1ord_odd_pow_sub {f i : ℕ} (hf : 1 ≤ f) (hi : 1 ≤ i) :
    Odd ((2 ^ f) ^ i - 1) :=
  Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 (by positivity)) (g1ord_even_pow hf hi) odd_one

private theorem g1ord_odd_pow_add {f i : ℕ} (hf : 1 ≤ f) (hi : 1 ≤ i) :
    Odd ((2 ^ f) ^ i + 1) :=
  (g1ord_even_pow hf hi).add_one

private theorem g1ord_odd_prod {s : Finset ℕ} {F : ℕ → ℕ} (h : ∀ i ∈ s, Odd (F i)) :
    Odd (∏ i ∈ s, F i) :=
  Finset.prod_induction F Odd (fun _ _ => Odd.mul) odd_one h

private theorem g1ord_odd_toNat {q i : ℕ} (hq : Even q) (hq0 : 0 < q) (hi : 1 ≤ i) :
    Odd ((q ^ i - (-1 : ℤ) ^ i).toNat) := by
  have h2 : (2 : ℤ) ∣ (q : ℤ) ^ i := by
    have : (2 : ℤ) ∣ (q : ℤ) := by exact_mod_cast even_iff_two_dvd.1 hq
    exact dvd_pow this (by omega)
  have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq0)
  have hneg := neg_one_pow_eq_or ℤ i
  rw [Nat.odd_iff]
  omega

private theorem g1ord_add_one_dvd_sub {q : ℕ} (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  exact ⟨m, Nat.sub_eq_of_eq_add (by ring)⟩

private theorem g1ord_add_one_dvd_toNat {q : ℕ} (hq : 1 ≤ q) :
    q + 1 ∣ ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : ((q ^ 2 : ℕ) : ℤ) = (q : ℤ) ^ 2 := Nat.cast_pow q 2
  have h : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    rw [neg_one_sq]
    omega
  rw [h]
  exact g1ord_add_one_dvd_sub hq

private theorem g1ord_assoc7 (a b c d e f g : ℕ) :
    a * b * c * d * e * f * g = a * (b * c * d * e * f * g) := by
  simp only [mul_assoc]

theorem padicValNat_two_ordA {n f : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    padicValNat 2 (ordA n (2 ^ f)) = f * (n * (n + 1) / 2) := by
  unfold ordA
  rw [← pow_mul (2 : ℕ) f (n * (n + 1) / 2)]
  refine g1ord_val (g1ord_odd_prod fun i hi => ?_) ?_
  · exact g1ord_odd_pow_sub hf (by have := (Finset.mem_Icc.1 hi).1; omega)
  · refine (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2).trans ?_)
    exact Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ i - 1)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)

theorem padicValNat_two_ordTwistedA {n f : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    padicValNat 2 (ordTwistedA n (2 ^ f)) = f * (n * (n + 1) / 2) := by
  have hq : Even (2 ^ f : ℕ) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hq0 : 1 ≤ (2 ^ f : ℕ) := Nat.one_le_two_pow
  unfold ordTwistedA
  rw [← pow_mul (2 : ℕ) f (n * (n + 1) / 2)]
  refine g1ord_val (g1ord_odd_prod fun i hi => ?_) ?_
  · exact g1ord_odd_toNat hq hq0 (by have := (Finset.mem_Icc.1 hi).1; omega)
  · refine (Nat.gcd_dvd_right _ _).trans ((g1ord_add_one_dvd_toNat hq0).trans ?_)
    exact Finset.dvd_prod_of_mem (fun i => (((2 ^ f : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)

theorem padicValNat_two_ordTwistedD {n f : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    padicValNat 2 (ordTwistedD n (2 ^ f)) = f * (n * (n - 1)) := by
  unfold ordTwistedD
  rw [mul_assoc, ← pow_mul (2 : ℕ) f (n * (n - 1))]
  refine g1ord_val ((g1ord_odd_pow_add hf hn).mul (g1ord_odd_prod fun i hi => ?_)) ?_
  · exact g1ord_odd_pow_sub hf (by have := (Finset.mem_Icc.1 hi).1; omega)
  · exact (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)

theorem padicValNat_two_ordTwistedE6 {f : ℕ} (hf : 1 ≤ f) :
    padicValNat 2 (ordTwistedE6 (2 ^ f)) = f * 36 := by
  have hq0 : 1 ≤ (2 ^ f : ℕ) := Nat.one_le_two_pow
  unfold ordTwistedE6
  rw [g1ord_assoc7, ← pow_mul (2 : ℕ) f 36]
  refine g1ord_val ?_ ?_
  · have h12 : Odd (((2 : ℕ) ^ f) ^ 12 - 1) := g1ord_odd_pow_sub hf (by norm_num)
    have h9 : Odd (((2 : ℕ) ^ f) ^ 9 + 1) := g1ord_odd_pow_add hf (by norm_num)
    have h8 : Odd (((2 : ℕ) ^ f) ^ 8 - 1) := g1ord_odd_pow_sub hf (by norm_num)
    have h6 : Odd (((2 : ℕ) ^ f) ^ 6 - 1) := g1ord_odd_pow_sub hf (by norm_num)
    have h5 : Odd (((2 : ℕ) ^ f) ^ 5 + 1) := g1ord_odd_pow_add hf (by norm_num)
    have h2 : Odd (((2 : ℕ) ^ f) ^ 2 - 1) := g1ord_odd_pow_sub hf (by norm_num)
    exact (((((h12.mul h9).mul h8).mul h6).mul h5).mul h2)
  · exact (Nat.gcd_dvd_right _ _).trans ((g1ord_add_one_dvd_sub hq0).trans (dvd_mul_left _ _))


section Kinds

open CFSG.Open.StatedAPI CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremA.RationalModel
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw


private theorem g1_twoPart_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {e : ℕ} (hq : S.D.q = 2 ^ e) (hq4 : 4 ≤ S.D.q)
    (hst : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    padicValNat 2 (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) =
      e * ((componentRoots (rootCharHom a) i).ncard / 2) := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ
  have hs1 := componentOrbitLength_eq_one hfin hst
  obtain ⟨σ, hfinK, hcardσ, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  haveI := hfinK
  rw [hs1, pow_one, hq] at hcardσ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · rw [hq] at hq4
      norm_num at hq4
    · exact h
  obtain ⟨t, ht0, ht2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card
    (fixSubfield σ) (by rw [hcardσ, ← hq]; exact hq4)
  have hperf := isPerfect_componentRootSpan_of_sq_ne_one
    (t := Units.mk0 t ht0) (fun h => ht2 (by simpa using congrArg Units.val h)) i
  obtain ⟨u, hu, hCQ⟩ := exists_odd_ggCQ_componentRootSpan i he hcardσ
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperf)) hf1
  have h := ggCQ_map_of_perfect f hker (Group.IsPerfect.top_iff.mpr hperf)
  rw [← MonoidHom.range_eq_map, hRf, ggCQ_top_subgroup] at h
  have h2N :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.ncard_eq_two_mul_ncard_posRoots hΨ hfin
  change padicValNat 2 (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) = _
  rw [h, hCQ, h2N, Nat.mul_div_cancel_left _ two_pos,
    padicValNat.mul (pow_ne_zero _ two_ne_zero) hu.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hu.not_two_dvd_nat, add_zero]

private theorem g1_ringChar_eq_two {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ e : ℕ}
    (S : LangSetup τ L p₀) (hq : S.D.q = 2 ^ e) : ringChar L = 2 := by
  have he : e ≠ 0 := by
    rintro rfl
    have h := S.hqpow.1
    rw [hq, pow_zero] at h
    exact not_isPrimePow_one h
  have h2 : ((2 : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff he).1 h
  haveI := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  exact ringChar.eq L 2

private theorem g1_typeA_model
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ f, 1 ≤ f ∧ ringChar L ^ f =
        S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      (StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
          .PSL (compRank (componentRoots (rootCharHom a) i) + 1) (ringChar L) f ∨
        StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
          .PSU (compRank (componentRoots (rootCharHom a) i) + 1) (ringChar L) f) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · obtain ⟨f, hf1, hfeq, hmodel⟩ :=
      rationalComponent_rankOne_model S hT i hr1 (by rw [hA.2, hr1]) hQS
    exact ⟨f, hf1, hfeq, Or.inl (by rw [hr1]; exact hmodel)⟩
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S hp hpL hTp i h2 hA.2
    have hcard : (frameRoots σ).ncard = ν * (ν - 1) := by
      have hinj : Set.InjOn (fun q : Fin ν × Fin ν => σ q.1 q.2) {q | q.1 ≠ q.2} := by
        rintro ⟨x, y⟩ hxy ⟨u, v⟩ huv h
        simp only [Set.mem_setOf_eq] at hxy huv
        obtain ⟨rfl, rfl⟩ := hψ.eq_of_eq hκ hnorm hxy huv h
        rfl
      have himg : frameRoots σ = (fun q : Fin ν × Fin ν => σ q.1 q.2) '' {q | q.1 ≠ q.2} := by
        ext r
        constructor
        · rintro ⟨x, y, hxy, rfl⟩
          exact ⟨(x, y), hxy, rfl⟩
        · rintro ⟨⟨x, y⟩, hxy, rfl⟩
          exact ⟨x, y, hxy, rfl⟩
      rw [himg, hinj.ncard_image]
      have hoff : ({q : Fin ν × Fin ν | q.1 ≠ q.2} : Set (Fin ν × Fin ν)) =
          ↑(Finset.univ.offDiag : Finset (Fin ν × Fin ν)) := by
        ext q
        simp [Finset.mem_offDiag]
      rw [hoff, Set.ncard_coe_finset, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
        Nat.mul_sub_left_distrib, mul_one]
    have hνr : ν = compRank (componentRoots (rootCharHom a) i) + 1 := by
      have h : ν * (ν - 1) = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) := by
        rw [← hcard, ← hΨ]
        exact hA.2
      generalize compRank (componentRoots (rootCharHom a) i) = r at h h2 ⊢
      obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
      rw [Nat.add_sub_cancel] at h
      have hm : m = r := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
      omega
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have hm1 : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have hm2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, hm1, rfl⟩
      rw [hs, hΨ] at hm2
      exact hm2
    have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
        (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · obtain ⟨f, hf1, hfeq, hmodel⟩ :=
        rationalComponent_splitFrame_model S hT i hν hψ hΨ π hπ
      exact ⟨f, hf1, hfeq, Or.inl (by rw [← hνr]; exact hmodel)⟩
    · obtain ⟨f, hf1, hfeq, hmodel⟩ :=
        rationalComponent_unitaryFrame_model S hT i hν hψ hΨ π hπ hQS
      exact ⟨f, hf1, hfeq, Or.inr (by rw [← hνr]; exact hmodel)⟩

private theorem g1_twoPart_typeA
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {e : ℕ} (hq : S.D.q = 2 ^ e) (hq4 : 4 ≤ S.D.q)
    (hst : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    padicValNat 2 (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) =
      e * ((componentRoots (rootCharHom a) i).ncard / 2) := by
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ
  obtain ⟨f, hf1, hfeq, hmodel⟩ := g1_typeA_model S hp hT hap h1 i hA hQS
  have h2 := g1_ringChar_eq_two S hq
  rw [componentOrbitLength_eq_one hfin hst, pow_one, hq, h2] at hfeq
  have hfe : f = e := Nat.pow_right_injective le_rfl hfeq
  rw [h2, hfe] at hmodel
  rw [hfe] at hf1
  rw [hA.2]
  rcases hmodel with h | h
  · rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
    show padicValNat 2 (ordA (compRank (componentRoots (rootCharHom a) i) + 1 - 1) (2 ^ e)) = _
    rw [Nat.add_sub_cancel, padicValNat_two_ordA hf1 hA.1]
  · rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
    show padicValNat 2
      (ordTwistedA (compRank (componentRoots (rootCharHom a) i) + 1 - 1) (2 ^ e)) = _
    rw [Nat.add_sub_cancel, padicValNat_two_ordTwistedA hf1 hA.1]

end Kinds


section TwoD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDMain
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDRecog
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw CFSG.Blueprint CFSG.Open.StatedAPI
open scoped MatrixGroups Matrix


private theorem g1_dClassTwisted {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    ∃ e : ℕ, ringChar L ^ e = S.D.q ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus
        (compRank (componentRoots (rootCharHom a) i)) (ringChar L) e := by
  classical
  obtain ⟨r, e, m, hr, hchar, hm5, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap⟩ :=
    CompsPTwoDExport.exists_twoD_export S hτ hTor i hkind h5
  haveI := hr
  haveI := hchar
  have hrc : ringChar L = r := ringChar.eq L r
  have hQ' : Q r (r ^ e) := by
    have h := hQ
    rw [hrc, hq] at h
    exact h
  have hR : CompsPTwoDDatumG.TwoDChainRecog r L D.e m := by
    rw [hDe]
    exact hrec r e m he hm5 hQ'
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hsl : ∀ β ∈ componentRoots (rootCharHom a) i, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hbroot : ∀ j : Fin m, IsRoot τ (ε.symm j : Fin τ.rank → ℤ) := fun j =>
    simpleRoots_isRoot (ε.symm j).2
  have hbinj : Function.Injective (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) :=
    fun j k h => ε.symm.injective (Subtype.ext h)
  have hG : ∀ j k : Fin m, iform (ε.symm j : Fin τ.rank → ℤ) (ε.symm k) =
      CFSG.LieType.Universal.Spin.cartanD m j k := by
    intro j k
    have h := hCart (ε.symm j) (ε.symm k)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    exact (CompsPTwoDBase.corootPair_eq_iform (hbroot j)
      (hsl _ (simpleRoots_subset (ε.symm j).2)) _).symm
  have hrange : Set.range (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) =
      ((simpleRoots (componentRoots (rootCharHom a) i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      exact (ε.symm j).2
    · intro hβ
      exact ⟨ε ⟨β, hβ⟩, by simp⟩
  have hsw := hswap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)
  have hlie := lieModel_orbitGroup_of_datum_four hτ D (by omega) hR
    (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) hbroot hbinj hG (hDs.trans hrange.symm) hfix
    hsw.1 hsw.2
    (fun j k hjk => exists_dFrames hτ K hK hT hadj hcheck hlt hcard hcount htrees hframes S hp hpL
      hTp i (by omega) hn ε hCart L j k hjk)
  let eR : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃* ↥D.orbitGroup :=
    ((rationalComponent S.ρ S.Γ (rootCharHom a) i).equivMapOfInjective
      (MulAut.conj z⁻¹).toMonoidHom (MulAut.conj z⁻¹).injective).trans (MulEquiv.subgroupCongr hRC)
  have hqiso : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
      ↥D.orbitGroup ⧸ Subgroup.center ↥D.orbitGroup :=
    QuotientGroup.congr _ _ eR (Subgroup.map_center_eq eR)
  have hmodel := (hlie.of_mulEquiv hqiso.symm).statedClassicalModel (by decide)
  have hmr : m = compRank (componentRoots (rootCharHom a) i) := by
    rw [compRank_eq_card hΨ]
    simpa using (Fintype.card_congr ε).symm
  refine ⟨e, by rw [hrc, hq], ?_⟩
  rw [hrc, ← hmr, ← hDe]
  exact hmodel

private theorem g1_twoD_model {p : ℕ} (hp : p.Prime) {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ e : ℕ, ringChar L ^ e = S.D.q ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus
        (compRank (componentRoots (rootCharHom a) i)) (ringChar L) e := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hkind : twistKind S.ρ (rootCharHom a) i = .twoD := by
    unfold twistKind
    rw [if_neg hout, if_neg, if_pos ⟨by omega, hn⟩]
    rintro (⟨h6, h72⟩ | ⟨h4', -, -⟩)
    · rw [hn, h6] at h72
      omega
    · omega
  have hr := compRank_le_rank (componentRoots (rootCharHom a) i)
  cases τ with
  | G2 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | F4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | D4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | E6 =>
    exact g1_dClassTwisted (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree
      e6_adj e6_check e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp
      hpL hT hTp i h5 hn hkind (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  | E7 =>
    exact g1_dClassTwisted (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7
      e7_tree e7_adj e7_check e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h)
      S hp hpL hT hTp i h5 hn hkind (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  | E8 =>
    exact g1_dClassTwisted (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8
      e8_tree e8_adj e8_check e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h)
      S hp hpL hT hTp i h5 hn hkind (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial

private theorem g1_twoPart_twoD {p : ℕ} (hp : p.Prime) {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {e : ℕ} (hq : S.D.q = 2 ^ e) (hq4 : 4 ≤ S.D.q)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    padicValNat 2 (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) =
      e * ((componentRoots (rootCharHom a) i).ncard / 2) := by
  obtain ⟨f, hf, hmodel⟩ := g1_twoD_model hp S hT hap h1 i h5 hn hout
  have h2 := g1_ringChar_eq_two S hq
  rw [h2, hq] at hf
  have hfe : f = e := Nat.pow_right_injective le_rfl hf
  rw [h2, hfe] at hmodel
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · rw [hq] at hq4
      norm_num at hq4
    · exact h
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hmodel, hn]
  show padicValNat 2 (ordTwistedD (compRank (componentRoots (rootCharHom a) i)) (2 ^ e)) = _
  rw [padicValNat_two_ordTwistedD he (by omega), mul_assoc, Nat.mul_div_cancel_left _ two_pos]

private theorem g1_twoPart_twistedE6 {p : ℕ} (hp : p.Prime) {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {e : ℕ} (hq : S.D.q = 2 ^ e) (hq4 : 4 ≤ S.D.q)
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (h72 : (componentRoots (rootCharHom a) i).ncard = 72)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    padicValNat 2 (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) =
      e * ((componentRoots (rootCharHom a) i).ncard / 2) := by
  have hpL : ((p : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (ringChar_ne_of_pow_eq_one hp hap h1)
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [h72, h6]
    rfl
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · rw [hq] at hq4
      norm_num at hq4
    · exact h
  have h2 := g1_ringChar_eq_two S hq
  have hr := compRank_le_rank (componentRoots (rootCharHom a) i)
  rw [h72]
  cases τ with
  | G2 => exact absurd (h6 ▸ hr) (by simp [Tag.rank])
  | F4 => exact absurd (h6 ▸ hr) (by simp [Tag.rank])
  | D4 => exact absurd (h6 ▸ hr) (by simp [Tag.rank])
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h72]; rfl)) h1
  | E7 =>
    obtain ⟨f, -, hf, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i (by omega) hn hout
    rw [h2, hq] at hf
    have hfe : f = e := Nat.pow_right_injective le_rfl hf
    rw [h2, hfe] at hlie
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (hlie.chevalleyExceptionalModel (by decide))]
    exact padicValNat_two_ordTwistedE6 he
  | E8 =>
    obtain ⟨f, -, hf, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i (by omega) hn hout
    rw [h2, hq] at hf
    have hfe : f = e := Nat.pow_right_injective le_rfl hf
    rw [h2, hfe] at hlie
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (hlie.chevalleyExceptionalModel (by decide))]
    exact padicValNat_two_ordTwistedE6 he

end TwoD


section D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE


private def g1d4_eps (τ : Tag) : Fin 4 → Fin τ.rank → ℤ
  | 0 => Pi.single (τ.idx 1) 1
  | 1 => Pi.single (τ.idx 2) 1
  | 2 => Pi.single (τ.idx 4) 1
  | 3 => reflect τ (τ.idx 3) (reflect τ (τ.idx 1) (reflect τ (τ.idx 2)
      (reflect τ (τ.idx 4) (Pi.single (τ.idx 3) 1))))

private def g1d4_refl {τ : Tag} (β x : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  x - corootPair β x • β

private theorem g1d4_isRoot (τ : Tag) (j : Fin 4) : IsRoot τ (g1d4_eps τ j) := by
  match j with
  | 0 => exact .basis _
  | 1 => exact .basis _
  | 2 => exact .basis _
  | 3 => exact .reflect _ (.reflect _ (.reflect _ (.reflect _ (.basis _))))

private theorem g1d4_main {τ : Tag} (ε : Fin 4 → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (ε j)) (hsupp : ∀ j (i : Fin τ.rank), i ∉ d4Nodes τ → ε j i = 0)
    (hneg : ∀ i ∈ d4Nodes τ, (rootReflection (ε 0) * rootReflection (ε 1) *
      rootReflection (ε 2) * rootReflection (ε 3)) • (Pi.single i 1 : Fin τ.rank → ℤ) =
        -Pi.single i 1)
    (v : WeylGroup τ) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ (fun α => v • α) ''
        parabolicRoots τ (d4Nodes τ), s = rootReflection γ},
      ∀ γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ), w • γ = -γ := by
  set u₀ : WeylGroup τ := rootReflection (ε 0) * rootReflection (ε 1) *
    rootReflection (ε 2) * rootReflection (ε 3) with hu₀
  have hmem : ∀ j, ε j ∈ parabolicRoots τ (d4Nodes τ) := fun j => ⟨hroot j, hsupp j⟩
  have hu₀neg : ∀ γ ∈ parabolicRoots τ (d4Nodes τ), u₀ • γ = -γ := by
    rintro γ ⟨-, hγ⟩
    have hsum : γ = ∑ i, γ i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    calc u₀ • γ = u₀ • ∑ i, γ i • (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [← hsum]
      _ = ∑ i, γ i • (u₀ • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = ∑ i, γ i • (-(Pi.single i 1 : Fin τ.rank → ℤ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i ∈ d4Nodes τ
          · rw [hneg i hi]
          · rw [hγ i hi, zero_smul, zero_smul]
      _ = -γ := by
          simp only [smul_neg, Finset.sum_neg_distrib]
          rw [← hsum]
  refine ⟨v * u₀ * v⁻¹, ?_, ?_⟩
  · have hr : ∀ j, v * rootReflection (ε j) * v⁻¹ ∈ Subgroup.closure
        {s : WeylGroup τ | ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ),
          s = rootReflection γ} := fun j => by
      rw [← rootReflection_smul_root v (hroot j)]
      exact Subgroup.subset_closure ⟨v • ε j, ⟨ε j, hmem j, rfl⟩, rfl⟩
    have e : v * u₀ * v⁻¹ = (v * rootReflection (ε 0) * v⁻¹) *
        (v * rootReflection (ε 1) * v⁻¹) * (v * rootReflection (ε 2) * v⁻¹) *
          (v * rootReflection (ε 3) * v⁻¹) := by
      rw [hu₀]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hr 0) (hr 1)) (hr 2)) (hr 3)
  · rintro _ ⟨γ₀, hγ₀, rfl⟩
    show (v * u₀ * v⁻¹) • (v • γ₀) = -(v • γ₀)
    rw [mul_smul, mul_smul, inv_smul_smul, hu₀neg γ₀ hγ₀, smul_neg]

theorem exists_neg_mem_closure_d4 {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (v : WeylGroup τ) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ (fun α => v • α) ''
        parabolicRoots τ (d4Nodes τ), s = rootReflection γ},
      ∀ γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ), w • γ = -γ := by
  have hcheck : (∀ i : Fin τ.rank, 1 ≤ i.val → i.val ≤ 4 →
      g1d4_refl (g1d4_eps τ 0) (g1d4_refl (g1d4_eps τ 1) (g1d4_refl (g1d4_eps τ 2)
        (g1d4_refl (g1d4_eps τ 3) (Pi.single i 1)))) = -Pi.single i 1) ∧
      ∀ (j : Fin 4) (i : Fin τ.rank), ¬ (1 ≤ i.val ∧ i.val ≤ 4) → g1d4_eps τ j i = 0 := by
    rcases hτ with rfl | rfl | rfl <;> decide +kernel
  refine g1d4_main (g1d4_eps τ) (g1d4_isRoot τ) hcheck.2 (fun i hi => ?_) v
  rw [mul_smul, mul_smul, mul_smul, rootReflection_smul (g1d4_isRoot τ 3),
    rootReflection_smul (g1d4_isRoot τ 2), rootReflection_smul (g1d4_isRoot τ 1),
    rootReflection_smul (g1d4_isRoot τ 0)]
  exact hcheck.1 i hi.1 hi.2

end D4

section Main

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.RootAut


private theorem g1_twistInner_of_neg {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)}
    (hneg : ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ}, ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ = -γ)
    (hen : ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ}, ∀ γ ∈ componentRoots (rootCharHom a) i, σ γ = -(u • γ)) :
    twistInner (componentRoots (rootCharHom a) i) σ := by
  obtain ⟨w, hw, hwneg⟩ := hneg
  obtain ⟨u, hu, hσ⟩ := hen
  refine ⟨w * u, mul_mem hw hu, fun γ hγ => ?_⟩
  rw [hσ γ hγ, mul_smul, hwneg _ ((f4Three_smul_mem_component_iff i hu γ).2 hγ)]

private theorem g1_twistInner_d4 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {p : ℕ} (hp : p.Prime) (hap : ∀ j, a j ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1)
    (hen : ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ}, ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    twistInner (componentRoots (rootCharHom a) i) S.ρ := by
  have hpL : ((p : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (ringChar_ne_of_pow_eq_one hp hap h1)
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
  cases τ with
  | G2 =>
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) h1
  | E6 =>
    obtain ⟨v, hv, -⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    refine g1_twistInner_of_neg i ?_ hen
    rw [hv]
    exact exists_neg_mem_closure_d4 (Or.inl rfl) v
  | E7 =>
    obtain ⟨v, hv, -⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    refine g1_twistInner_of_neg i ?_ hen
    rw [hv]
    exact exists_neg_mem_closure_d4 (Or.inr (Or.inl rfl)) v
  | E8 =>
    obtain ⟨v, hv, -⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    refine g1_twistInner_of_neg i ?_ hen
    rw [hv]
    exact exists_neg_mem_closure_d4 (Or.inr (Or.inr rfl)) v

private theorem g1_shape_of_not_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    (compRank (componentRoots (rootCharHom a) i) = 6 ∧
        (componentRoots (rootCharHom a) i).ncard = 72) ∨
      (compRank (componentRoots (rootCharHom a) i) = 4 ∧
        (componentRoots (rootCharHom a) i).ncard = 24) ∨
      (5 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1)) ∨
      (2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) := by
  classical
  by_contra hne
  apply hout
  refine twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i ?_
  unfold twistKind
  split_ifs with h₁ h₂ h₃
  all_goals try rfl
  · rcases h₁ with ⟨h6, h72⟩ | ⟨h4, h24, -⟩
    · exact absurd (Or.inl ⟨h6, h72⟩) hne
    · exact absurd (Or.inr (Or.inl ⟨h4, h24⟩)) hne
  · obtain ⟨h4, hn⟩ := h₂
    rcases Nat.lt_or_ge (compRank (componentRoots (rootCharHom a) i)) 5 with h | h
    · have h4' : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      exact absurd (Or.inr (Or.inl ⟨h4', by rw [hn, h4']⟩)) hne
    · exact absurd (Or.inr (Or.inr (Or.inl ⟨h, hn⟩))) hne
  · exact absurd (Or.inr (Or.inr (Or.inr h₃))) hne

theorem exc_rat_twoPart {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {e : ℕ} (hq : S.D.q = 2 ^ e) (hq4 : 4 ≤ S.D.q)
    (hst : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    {p : ℕ} (hp : p.Prime) (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hen : ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ}, ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ))
    (hQ : CFSG.IsQuasisimple ↥(excRatComp S a i)) :
    padicValNat 2 (Nat.card (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i))) =
      e * ((componentRoots (rootCharHom a) i).ncard / 2) := by
  classical
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact g1_twoPart_inner S hT i hq hq4 hst hin
  rcases g1_shape_of_not_inner S hT i hin with hE | hD4 | hD | hA
  · exact g1_twoPart_twistedE6 hp S hT hap h1 i hq hq4 hE.1 hE.2 hin
  · have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot τ).subset fun β hβ =>
        (isRootComponent_componentRoots (χ := rootCharHom a) i).isRoot β hβ
    rw [componentOrbitLength_eq_one hfin hst, Function.iterate_one] at hin
    exact absurd (g1_twistInner_d4 S hT i hp hap h1 hen hD4.1 hD4.2) hin
  · exact g1_twoPart_twoD hp S hT hap h1 i hq hq4 hD.1 hD.2 hin
  · exact g1_twoPart_typeA S hp hT hap h1 i hq hq4 hst ⟨by omega, hA.2⟩ hQ

end Main

end CFSG.LocalAnalysis.GLTheoremA.I167
