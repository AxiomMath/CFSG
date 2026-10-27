module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Cover
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.SectionRank.OddCover (scalar_injective exists_scalar_of_mem_scalars
  scalar_quotient_diagonal_torus_rank)

variable {K : Type} [Field K] [Finite K]

theorem isPerfect_linUni {p f n : ℕ} (hp : p.Prime) (hn : 4 ≤ n) {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K)) :
    Group.IsPerfect H := by
  rcases hH with ⟨-, rfl⟩ | ⟨hK, rfl⟩
  · have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := n)
      (by omega)
    exact Group.IsPerfect.ofSurjective
      (f := (specialLinearGroupEquivStatedSL n K).toMonoidHom)
      (specialLinearGroupEquivStatedSL n K).surjective
  · have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by
        rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    have := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (n := n)
      (by omega) (fun h => absurd h (by omega))
    have heq : CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution K p f) n = StatedSU n (p ^ f) K :=
      CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n
    exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr heq).toMonoidHom)
      (MulEquiv.subgroupCongr heq).surjective

theorem exists_unit_orderOf {d : ℕ} (hd : d ∣ Nat.card Kˣ) : ∃ ζ : Kˣ, orderOf ζ = d := by
  classical
  have := Fintype.ofFinite Kˣ
  rw [Nat.card_eq_fintype_card] at hd
  have h := IsCyclic.card_orderOf_eq_totient (α := Kˣ) hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd Fintype.card_pos
  have hpos : 0 < (Finset.univ.filter fun a : Kˣ => orderOf a = d).card := by
    rw [h]
    exact Nat.totient_pos.2 hd0
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
  exact ⟨a, (Finset.mem_filter.1 ha).2⟩

omit [Finite K] in
theorem scalar_mem_linUni {n q d : ℕ} (hq : q ≠ 0) {H : Subgroup (GL (Fin n) K)}
    (hH : (H = StatedSL n K ∧ d ∣ n) ∨ (H = StatedSU n q K ∧ d ∣ n ∧ d ∣ q + 1)) {ζ : Kˣ}
    (hζ : ζ ^ d = 1) : Matrix.GeneralLinearGroup.scalar (Fin n) ζ ∈ H := by
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin n) ζ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
    obtain ⟨dn, hdn⟩ : d ∣ n := by
      rcases hH with ⟨-, h⟩ | ⟨-, h, -⟩ <;> exact h
    have h1 : ζ ^ n = 1 := by rw [hdn, pow_mul, hζ, one_pow]
    have h2 : ((ζ : K)) ^ n = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h1
      simpa using this
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, h2]
  rcases hH with ⟨rfl, -⟩ | ⟨rfl, -, hdq⟩
  · exact Subgroup.subset_closure hdet
  · refine Subgroup.subset_closure ⟨hdet, ?_⟩
    obtain ⟨dq, hdq⟩ := hdq
    have h1 : ζ ^ (q + 1) = 1 := by rw [hdq, pow_mul, hζ, one_pow]
    have h2 : ((ζ : K)) ^ (q + 1) = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h1
      simpa using this
    ext i j
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, hq]
      rw [← pow_succ, h2]
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij, hq]

theorem dvd_card_scalars {n q d : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = q ∧ H = StatedSL n K ∧ d ∣ n ∧ d ∣ q - 1) ∨
      (Nat.card K = q ^ 2 ∧ H = StatedSU n q K ∧ d ∣ n ∧ d ∣ q + 1)) :
    d ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf H) := by
  have hcard : d ∣ Nat.card Kˣ := by
    rw [CFSG.SectionRank.OddCover.card_units_eq]
    rcases hH with ⟨hK, -, -, hd⟩ | ⟨hK, -, -, hd⟩
    · rw [hK]; exact hd
    · rw [hK, CFSG.SectionRank.OddCover.sq_sub_one_eq hq]
      exact Dvd.dvd.mul_right hd _
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf hcard
  have hζd : ζ ^ d = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) ζ ∈ H := by
    refine scalar_mem_linUni (q := q) (d := d) (by omega) ?_ hζd
    rcases hH with ⟨-, rfl, hdn, -⟩ | ⟨-, rfl, hdn, hd⟩
    · exact Or.inl ⟨rfl, hdn⟩
    · exact Or.inr ⟨rfl, hdn, hd⟩
  let y : (StatedScalars (Fin n) K).subgroupOf H :=
    ⟨⟨_, hmem⟩, ⟨ζ, rfl⟩⟩
  have hy : orderOf y = d := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    change orderOf (Matrix.GeneralLinearGroup.scalar (Fin n) ζ) = d
    rw [orderOf_injective (Matrix.GeneralLinearGroup.scalar (Fin n)) (scalar_injective hn) ζ, hζ]
  rw [← hy]
  exact orderOf_dvd_natCard y

omit [Finite K] in
theorem scalars_le_center {n : ℕ} (H : Subgroup (GL (Fin n) K)) :
    (StatedScalars (Fin n) K).subgroupOf H ≤ Subgroup.center H := by
  intro x hx
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_scalars hx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hmem : (x : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    rw [hc, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact (Subgroup.mem_center_iff.mp hmem (g : GL (Fin n) K))

theorem rank_of_cover {L : Type} [Group L] [Finite L] (hLperf : Group.IsPerfect L)
    {p f n r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2) (hn : 4 ≤ n)
    {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K ∧ r ∣ p ^ f - 1) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K ∧ r ∣ p ^ f + 1))
    (θ : L ⧸ Subgroup.center L ≃* StatedProj H) (hZ : IsPGroup r (Subgroup.center L))
    [Finite (hopfMultiplier (StatedProj H))]
    (hM : (Nat.card (hopfMultiplier (StatedProj H))).factorization r ≤
      (Nat.card ((StatedScalars (Fin n) K).subgroupOf H)).factorization r) :
    n - 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup L) := by
  have : Fact r.Prime := ⟨hr⟩
  have hHK : (Nat.card K = p ^ f ∧ H = StatedSL n K) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K) := by
    rcases hH with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hHperf := isPerfect_linUni hp hn hHK
  set D := (StatedScalars (Fin n) K).subgroupOf H with hD
  have hDc : D ≤ Subgroup.center H := scalars_le_center H
  let α : H →* StatedProj H := QuotientGroup.mk' D
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
  have hαk : α.ker = D := QuotientGroup.ker_mk' D
  let β : L →* StatedProj H := CFSG.GH74.Generic.centralQuotientMap θ
  have hβ : Function.Surjective β := CFSG.GH74.Generic.centralQuotientMap_surjective θ
  have hβk : β.ker = Subgroup.center L := CFSG.GH74.Generic.centralQuotientMap_ker θ
  obtain ⟨φ, hφs, hβφ⟩ := exists_hom_of_cover hHperf hLperf α hα (hαk ▸ hDc) β hβ hβk.le hr
    (by rw [hβk]; exact hZ) (by rw [hαk]; exact hM)
  have hkerφ : φ.ker ≤ D := by
    intro h hh
    have h1 : α h = 1 := by
      rw [← hβφ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hh, map_one]
    rw [← hαk]
    exact h1
  have hrank := (scalar_quotient_diagonal_torus_rank (K := K) hp (by omega) (r := r) hr2
    (H := H) (by
      rcases hH with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr ⟨h1, h2, h3⟩) φ.ker hkerφ).1
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)] at hrank
  exact hrank

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
