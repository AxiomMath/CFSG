module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
import CFSG.FeitThompson.Local.NormalBetaSylowControlsFittingPrimes
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Representations.TINormalCentralSectionGeometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

variable {G : Type*} [Group G] [Finite G] {q : ℕ} {M : Subgroup G}

theorem mixedFitting_ne_bot_of_normal_sylow (hq : q ∈ betaPrimes ↥M) (S : Sylow q ↥M)
    (hSnormal : (S : Subgroup ↥M).Normal) : mixedFitting M ≠ ⊥ := by
  have hqp : q.Prime := prime_of_mem_betaPrimes hq
  have := Fact.mk hqp
  have hSbot : (S : Subgroup ↥M) ≠ ⊥ := by
    intro h
    have hcard : Nat.card (S : Subgroup ↥M) = q ^ (Nat.card ↥M).factorization q :=
      S.card_eq_multiplicity
    have hpos : 0 < (Nat.card ↥M).factorization q :=
      hqp.factorization_pos_of_dvd Nat.card_pos.ne' (dvd_card_of_mem_betaPrimes hq)
    rw [h, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow hpos.ne' hqp.one_lt).ne' hcard.symm
  have hle : (S : Subgroup ↥M) ≤ fittingRaw ↥M :=
    le_fittingRaw_of_isPGroup hqp hSnormal S.isPGroup'
  intro hbot
  rw [mixedFitting_eq] at hbot
  have h2 : (S : Subgroup ↥M).map M.subtype ≤ ⊥ := hbot ▸ Subgroup.map_mono hle
  exact hSbot ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 (le_bot_iff.1 h2))

omit [Finite G] in
theorem sharp_nonempty_of_ne_bot {F : Subgroup G} (h : F ≠ ⊥) : (sharp F).Nonempty := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  exact ⟨x, hx, by simpa using hx1⟩

omit [Finite G] in
theorem conjSet_inv_eq_conj_image (D : Set G) (g : G) :
    conjSet D g⁻¹ = MulAut.conj g '' D := by
  simp [conjSet, MulAut.conj]

theorem normalizer_sharp_mixedFitting_eq [IsSimpleGroup G] (hM : IsCoatom M)
    (hq : q ∈ betaPrimes ↥M) (S : Sylow q ↥M) (hSnormal : (S : Subgroup ↥M).Normal) :
    normalizer (sharp (mixedFitting M)) = M := by
  have hbot := mixedFitting_ne_bot_of_normal_sylow hq S hSnormal
  have hsharp : sharp (mixedFitting M) = (mixedFitting M : Set G) \ {1} := rfl
  rw [hsharp, normalizer_sdiff_singleton_one]
  exact normalizer_eq_of_isCoatom hM hbot (mixedFitting_le M) (le_normalizer_mixedFitting M)

theorem inter_conjSet_sharp_mixedFitting_eq_empty [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hq : q ∈ betaPrimes ↥M) (S : Sylow q ↥M) (hSnormal : (S : Subgroup ↥M).Normal)
    (hFS : mixedFitting M ≤ sigmaCore M) {g : G} (hg : g ∉ M) :
    sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hxF, hx1⟩, y, ⟨hyF, -⟩, rfl⟩
  set F : Subgroup G := mixedFitting M with hFdef
  set D : Subgroup G := F ⊓ MulAut.conj g⁻¹ • F with hDdef
  have hmemD : g⁻¹ * y * g ∈ D := by
    refine ⟨hxF, ?_⟩
    rw [conj_smul_eq_map_conj]
    exact ⟨y, hyF, by simp⟩
  have hne1 : g⁻¹ * y * g ≠ 1 := fun h => hx1 (by simp [h])
  have hDbot : D ≠ ⊥ := fun h => hne1 (Subgroup.mem_bot.1 (h ▸ hmemD))
  have hDlt : 1 < Nat.card ↥D :=
    lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hDbot (Subgroup.card_eq_one.1 h))
  obtain ⟨p, hpmem⟩ := Nat.nonempty_primeFactors.2 hDlt
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  obtain ⟨w, hwD, hwo⟩ := exists_mem_orderOf_eq_of_dvd hp (Nat.dvd_of_mem_primeFactors hpmem)
  set P : Subgroup G := zpowers w with hPdef
  have hPcard : Nat.card ↥P = p := by rw [hPdef, Nat.card_zpowers, hwo]
  have hPp : IsPGroup p ↥P := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hPF : P ≤ F := zpowers_le.2 hwD.1
  have hPg : P ≤ MulAut.conj g⁻¹ • F := zpowers_le.2 hwD.2
  have hpσ : p ∈ sigmaPrimes M := by
    refine isPiSubgroup_iff.1 ((isPiSubgroup_sigmaCore M).of_le (hPF.trans hFS)) p ?_
    exact Nat.mem_primeFactors.2 ⟨hp, hPcard ▸ dvd_rfl, by rw [hPcard]; exact hp.pos.ne'⟩
  have hPFraw : P ≤ (fittingRaw ↥M).map M.subtype := by rw [← mixedFitting_eq]; exact hPF
  have hCM : centralizer (P : Set G) ≤ M :=
    centralizer_le_of_natCard_eq_prime_of_le_fitting_of_sylow hna hodd hsolv hM hq S hSnormal
      hp hPFraw hPcard
  have hPM : P ≤ MulAut.conj (1 : G) • M := by
    simpa using hPF.trans (mixedFitting_le M)
  have hPMg : P ≤ MulAut.conj g⁻¹ • M := by
    refine hPg.trans ?_
    rw [conj_smul_eq_map_conj, conj_smul_eq_map_conj]
    exact Subgroup.map_mono (mixedFitting_le M)
  obtain ⟨c, hc, hconj⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes hna hodd hsolv hM
    hpσ hPp hPM hPMg
  have hcM : c ∈ M := hCM hc
  have hcfix : MulAut.conj c • M = M := mem_normalizer_iff_conj_smul_eq.1 (M.le_normalizer hcM)
  have hgM : MulAut.conj g⁻¹ • M = M := by
    rw [← hconj]
    simpa using hcfix
  refine hg ?_
  have hginv : g⁻¹ ∈ normalizer (M : Set G) := mem_normalizer_iff_conj_smul_eq.2 hgM
  have hg' : g ∈ normalizer (M : Set G) := by
    simpa using (normalizer (M : Set G)).inv_mem hginv
  rwa [normalizer_coe_eq_of_isCoatom hna hM] at hg'

theorem isTIWithNormalizer_sharp_mixedFitting
    (hMN : normalizer (sharp (mixedFitting M)) = M) (hbot : mixedFitting M ≠ ⊥)
    (hdisj : ∀ g : G, g ∉ M →
      sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g = ∅) :
    IsTIWithNormalizer (sharp (mixedFitting M)) M where
  nonempty := sharp_nonempty_of_ne_bot hbot
  one_notMem := one_notMem_sharp _
  normalizer_eq := hMN
  disjoint_conj_image g hg := by
    have hginv : g⁻¹ ∉ M := fun hc => hg (by simpa using M.inv_mem hc)
    rw [Set.disjoint_iff_inter_eq_empty, ← conjSet_inv_eq_conj_image]
    exact hdisj g⁻¹ hginv

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson Subgroup

universe u

theorem FBG_normal_beta_sylow_fitting_ti :
    Statements.FBG_normal_beta_sylow_fitting_ti.{u} := by
  intro G _ _ hG M hM q hq _ Q hQnormal hFS
  have := hG.isSimpleGroup
  refine ⟨normalizer_sharp_mixedFitting_eq hM hq Q hQnormal, fun g hg =>
    inter_conjSet_sharp_mixedFitting_eq_empty hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable hM hq Q hQnormal hFS hg⟩

end

end CFSG.FeitThompson.Proofs
