module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Typ
public import CFSG.ClassicalInvolution.Asc77.AscC5OM17

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 Matrix CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.ClassicalInvolution.Asc77.C5O.M
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

namespace C5

theorem card_scalars_subgroupOf_le {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Subgroup (GL ι K)) : Nat.card ((StatedScalars ι K).subgroupOf H) ≤ Nat.card K - 1 := by
  rw [← card_map_of_injective H.subtype_injective, subgroupOf_map_subtype]
  refine (card_le_of_le inf_le_left).trans (le_of_eq ?_)
  rw [StatedScalars, ← Nat.card_congr (MonoidHom.ofInjective scalar_injective).toEquiv,
    Nat.card_units]

end C5

open C5

theorem exists_psl2_block {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = r ^ f) :
    ∃ L : Subgroup (StatedProj (StatedSp 2 K)), L ≠ ⊤ ∧ IsQuasisimple ↥L ∧
      OddChev r (↥L ⧸ center ↥L) ∧ r ∣ Nat.card L ∧
      L.index ∣ 2 * ((r ^ f) ^ 2 * ((r ^ f) ^ 2 - 1)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact r.Prime := ⟨hr⟩
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K r]; exact hr2
  obtain ⟨μ, hμ⟩ := FiniteField.exists_nonsquare hchar
  have : Fact (¬ IsSquare μ) := ⟨hμ⟩
  have : Finite (QuadraticAlgebra K μ 0) := finite_quadAlg μ
  set φ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K with hφdef
  have hφ : φ.ker = CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 K :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj
  have h3 := three_le_pow (f := f) hr hr2 hf
  have hE : Nat.card (QuadraticAlgebra K μ 0) = r ^ (2 * f) := by
    rw [card_quadAlg, hK, ← pow_add, two_mul]
  have hE' : Nat.card (QuadraticAlgebra K μ 0) = (r ^ f) ^ 2 := by
    rw [hE, pow_mul']
  let e : ↥(φ.comp (phiSL μ)).range ≃* PSL(2, QuadraticAlgebra K μ 0) :=
    (QuotientGroup.quotientKerEquivRange (φ.comp (phiSL μ))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (ker_phiSL_comp μ φ hφ))
  have h4E : 4 ≤ Nat.card (QuadraticAlgebra K μ 0) := by rw [hE']; nlinarith
  have : IsSimpleGroup PSL(2, QuadraticAlgebra K μ 0) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4E
  have : IsSimpleGroup ↥(φ.comp (phiSL μ)).range := e.isSimpleGroup
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K r] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h')
  have hn := exists_not_comm_range_phiSL μ h2 φ hφ
  have hc : OddChev r ↥(φ.comp (phiSL μ)).range := by
    refine ⟨hr, hr2, Or.inl ⟨2 * f, by omega, Or.inl ⟨by decide, ⟨hr, by omega, le_rfl, ?_, ?_⟩,
      QuadraticAlgebra K μ 0, inferInstance, inferInstance, hE,
      ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 _)⟩⟩⟩⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      rw [pow_mul'] at h
      nlinarith
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      rw [pow_mul'] at h
      nlinarith
  obtain ⟨hQ, hC⟩ := typ_simple hn hc
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hr.odd_of_ne_two hr2).pow
  have hcard := card_range_phiSL μ hodd φ hφ
  rw [natCard_sl2, hE'] at hcard
  set q := r ^ f with hq
  have hY := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
  have hL := Subgroup.card_mul_index (φ.comp (phiSL μ)).range
  have hSp : Nat.card (StatedSp 2 K) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2, hK,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  rw [hSp] at hY
  have hZ := card_scalars_subgroupOf_le (K := K) (StatedSp 2 K)
  rw [hK] at hZ
  have e4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 4 q (by omega), Nat.one_le_pow 2 q (by omega)]
    ring
  have e4' : (q ^ 2) ^ 2 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by rw [← pow_mul]; exact e4
  rw [e4] at hY
  rw [e4'] at hcard
  have hA : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith)
  generalize q ^ 2 - 1 = A at hY hcard hA ⊢
  set idx := (φ.comp (phiSL μ)).range.index
  set z := Nat.card ↥((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
  set l := Nat.card ↥(φ.comp (phiSL μ)).range
  set y := Nat.card (StatedProj (StatedSp 2 K))
  have key : q ^ 2 * (A * (q ^ 2 + 1)) * (idx * z) =
      q ^ 2 * (A * (q ^ 2 + 1)) * (2 * (q ^ 2 * A)) := by
    calc q ^ 2 * (A * (q ^ 2 + 1)) * (idx * z) = 2 * l * idx * z := by rw [hcard]; ring
      _ = 2 * (y * z) := by rw [← hL]; ring
      _ = 2 * (q ^ 4 * (A * (A * (q ^ 2 + 1)))) := by rw [← hY]
      _ = _ := by ring
  have hkey := Nat.eq_of_mul_eq_mul_left (by positivity) key
  refine ⟨(φ.comp (phiSL μ)).range, ?_, hQ, hC, ?_, Dvd.intro z hkey⟩
  · intro htop
    have h1 : idx = 1 := by
      change (φ.comp (phiSL μ)).range.index = 1
      rw [htop, Subgroup.index_top]
    rw [h1, one_mul] at hkey
    have : q < 2 * (q ^ 2 * A) := by
      have : 1 ≤ A := hA
      nlinarith
    omega
  · have h2l : r ∣ 2 * l := by
      rw [hcard]
      exact Dvd.dvd.mul_right ((dvd_pow_of_one_le hf).trans (dvd_pow_self _ two_ne_zero)) _
    exact ((Nat.coprime_primes hr Nat.prime_two).mpr hr2).dvd_of_dvd_mul_left h2l

end CFSG.OddStandard.GH71.S55
