module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLinPairs
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResPairDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LieType.SeitzGeneration (RankLE2 HasThreeIndep)
open CFSG.Open (IsElemAbelian)

section Numerics

variable {K : Type} [Field K] [Finite K]

theorem dvd_card_GL_of_dvd_pow_sub_one {p e : ℕ} (he : 1 ≤ e) (hpe : p ∣ Nat.card K ^ e - 1) :
    p ∣ Nat.card (GL (Fin e) K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_GL_field]
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨0, he⟩ : Fin e)))
  rw [← Nat.card_eq_fintype_card]
  simpa using hpe

theorem orderOf_card_spec {p : ℕ} (hp : p.Prime) (hpc : ¬ p ∣ Nat.card K) :
    0 < orderOf (Nat.card K : ZMod p) ∧ p ∣ Nat.card K ^ orderOf (Nat.card K : ZMod p) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpc
  refine ⟨orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hz⟩), ?_⟩
  have h2 : ((Nat.card K : ℕ) : ZMod p) ^ orderOf (Nat.card K : ZMod p) = 1 :=
    pow_orderOf_eq_one _
  have h4 : Nat.card K ^ orderOf (Nat.card K : ZMod p) ≡ 1 [MOD p] := by
    refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
    push_cast
    exact h2
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).1 h4.symm

end Numerics

section Weir

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem two_mul_orderOf_le_of_elemAbelian (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K - 1) (hpc : ¬ p ∣ Nat.card K)
    {E : Subgroup (projectiveSL n K)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    2 * orderOf (Nat.card K : ZMod p) ≤ n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hconj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn
  set V : Subgroup (MulAut (projectiveSL n K)) :=
    E.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) with hV
  have hVc : Nat.card V = p ^ 2 := by
    rw [hV, Subgroup.card_map_of_injective hconj]
    exact hEc
  have hcomm : ∀ a b : ↥V, a * b = b * a := by
    intro a b
    obtain ⟨y₁, hy₁, ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y₂, hy₂, hb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : MulAut (projectiveSL n K)) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨y₁, hy₁⟩ : E) ⟨y₂, hy₂⟩)
  haveI hVe : CFSG.IsElementaryAbelian p ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => hcomm a b⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨y, hy, ha⟩ := Subgroup.mem_map.1 a.2
        apply Subtype.ext
        change (a : MulAut (projectiveSL n K)) ^ p = 1
        rw [← ha, ← map_pow, hE.2 y hy, map_one] }
  have hVD : ∀ v ∈ V, ∃ A : GL (Fin n) K, v = conjAut n K A := by
    intro v hv
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hv
    have hy : (MulAut.conj y : MulAut (projectiveSL n K)) ∈ linearAutGroup n K :=
      (standard_outer_quotients (n := n) (K := K)).1 ⟨y, rfl⟩
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 hy
    exact ⟨A, hA.symm⟩
  obtain ⟨W, hWe, hWc, -, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_lift_group hn hpK hVc hVD
  by_contra hlt
  push Not at hlt
  have hpos := (orderOf_card_spec (K := K) hp hpc).1
  have hdiv : n / orderOf (Nat.card K : ZMod p) ≤ 1 := by
    have := (Nat.div_lt_iff_lt_mul hpos).2 (by omega : n < 2 * orderOf (Nat.card K : ZMod p))
    omega
  haveI := hWe
  exact CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.false_of_sylow_cyclic W hWc
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isCyclic_sylow_gl_of_div (hp.odd_of_ne_two hp2) hpc hdiv)

end Weir

section Diagonal

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem dvd_of_mem_linearAut_not_inner (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {a : MulAut (projectiveSL n K)} (haD : a ∈ linearAutGroup n K)
    (hai : a ∉ inner (projectiveSL n K)) (hap : a ^ p = 1) :
    p ∣ n ∧ p ∣ Nat.card K - 1 := by
  haveI : (inner (projectiveSL n K)).Normal := inner_normal _
  have hIDle : inner (projectiveSL n K) ≤ linearAutGroup n K :=
    (standard_outer_quotients (n := n) (K := K)).1
  have hrel : p ∣ (inner (projectiveSL n K)).relIndex (linearAutGroup n K) := by
    by_contra hd
    exact hai (mem_of_pPow_eq_one_of_not_dvd_relIndex hp hIDle hd haD (k := 1)
      (by rw [pow_one]; exact hap))
  have hg := hrel.trans (UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := n)
    (by omega))
  exact ⟨hg.trans (Nat.gcd_dvd_left _ _), hg.trans (Nat.gcd_dvd_right _ _)⟩

theorem hasThreeIndep_projectiveSL (hn : 5 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) : HasThreeIndep (projectiveSL n K) p :=
  HasThreeIndep.of_mulEquiv (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
    (CFSG.LieType.SeitzGeneration.hasThreeIndep_psl hn hp hpq)

end Diagonal

theorem linear_outer_fixesPair {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnp : ¬ (n = 3 ∧ p = 3))
    (hle : RankLE2 p (projectiveSL n K))
    (hge : ∃ E : Subgroup (projectiveSL n K), IsElemAbelian p E ∧ Nat.card E = p ^ 2)
    {α : MulAut (projectiveSL n K)} (hα : α ∉ inner (projectiveSL n K)) (hαp : α ^ p = 1) :
    FixesIndepPair p α := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hα1 : α ≠ 1 := fun h => hα (h ▸ (inner (projectiveSL n K)).one_mem)
  have hao : orderOf α = p := orderOf_eq_prime hαp hα1
  have haE : α ∈ semilinearAutGroup n K := mem_semilinearAutGroup_of_pow_odd hn hpodd hαp
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hpc : ¬ p ∣ Nat.card K := by
    intro hd
    rw [hcard] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hpn : n < 5 → ¬ p ∣ n := by
    intro h5 hd
    have : n = 3 ∨ n = 4 := by omega
    rcases this with rfl | rfl
    · exact hnp ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd⟩
    · have h4 : p ∣ 2 ^ 2 := by simpa using hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  by_cases hD : α ∈ linearAutGroup n K
  ·
    exfalso
    obtain ⟨hdn, hdK⟩ := dvd_of_mem_linearAut_not_inner hn hp hD hα hαp
    by_cases h5 : 5 ≤ n
    · exact hasThreeIndep_false_of_rankLE2 hp (hasThreeIndep_projectiveSL h5 hp hdK) hle
    · exact hpn (by omega) hdn
  ·
    obtain ⟨-, σ, hσo, ⟨h, -, hah⟩, -⟩ :=
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
        (K := K) (n := n) (ℓ := 2) (f := (m : ℕ)) Nat.prime_two m.pos hn hcard hp α haE hD hao
    have hσp : σ ^ p = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
    have hpair : FixesIndepPair p (fieldAut n K σ) := by
      by_cases hpK : p ∣ Nat.card K - 1
      · by_cases h5 : 5 ≤ n
        · exact (hasThreeIndep_false_of_rankLE2 hp (hasThreeIndep_projectiveSL h5 hp hpK) hle).elim
        · obtain ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩ :=
            exists_two_indep_fixed_diag hp hn (hpn (by omega)) hpK hσp
          exact ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩
      · obtain ⟨E, hE, hEc⟩ := hge
        have h2e := two_mul_orderOf_le_of_elemAbelian hn hp hp2 hpK hpc hE hEc
        obtain ⟨hpos, hpe⟩ := orderOf_card_spec (K := K) hp hpc
        obtain ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩ :=
          exists_two_indep_fixed_blocks_of_dvd hp hpK hpos
            (dvd_card_GL_of_dvd_pow_sub_one hpos hpe) h2e hσp
        exact ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩
    rw [hah]
    exact hpair.map h

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
