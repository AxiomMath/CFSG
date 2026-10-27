module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLinear
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Polynomial Module Matrix
open CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

theorem exists_split_lifts_of_commutator_eq_scalar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} {k : Type} [Field k] [Finite k] {A B : GL (Fin n) k}
    (hA : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hB : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b) {z : kˣ}
    (hz : IsPrimitiveRoot (z : k) p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin n) z)
    (hA1 : conjAut n k A ≠ 1) (hBA : conjAut n k B ∉ Subgroup.zpowers (conjAut n k A)) :
    ∃ (X Y : GL (Fin n) k) (w : kˣ), X ^ p = 1 ∧ IsPrimitiveRoot (w : k) p ∧
      Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) w * X ∧ conjAut n k X ≠ 1 ∧
      conjAut n k X ∈ Subgroup.closure {conjAut n k A, conjAut n k B} ∧
      conjAut n k Y ∈ Subgroup.closure {conjAut n k A, conjAut n k B} := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hz' : IsPrimitiveRoot z p := IsPrimitiveRoot.coe_units_iff.mp hz
  have hAE : conjAut n k A ∈ Subgroup.closure {conjAut n k A, conjAut n k B} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hBE : conjAut n k B ∈ Subgroup.closure {conjAut n k A, conjAut n k B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hsc : ∀ (u : kˣ) (M : GL (Fin n) k), GeneralLinearGroup.scalar (Fin n) u * M =
      M * GeneralLinearGroup.scalar (Fin n) u := fun u M => GeneralLinearGroup.scalar_commute u M
  have hABA : A * B * A⁻¹ = GeneralLinearGroup.scalar (Fin n) z * B :=
    mul_inv_eq_iff_eq_mul.mp hAB
  have hBAB : B * A * B⁻¹ = GeneralLinearGroup.scalar (Fin n) z⁻¹ * A :=
    CFSG.LinearAlgebra.conj_eq_scalar_inv (X := B) (Y := A) (z := z) hABA
  by_cases hap : ∃ u : kˣ, u ^ p = a
  ·
    obtain ⟨u, rfl⟩ := hap
    have hXu : (GeneralLinearGroup.scalar (Fin n) u⁻¹ * A) ^ p = 1 :=
      (glRescale_lift ha).1
    have hcX : conjAut n k (GeneralLinearGroup.scalar (Fin n) u⁻¹ * A) = conjAut n k A :=
      (glRescale_lift ha).2
    have hYX : B * (GeneralLinearGroup.scalar (Fin n) u⁻¹ * A) * B⁻¹ =
        GeneralLinearGroup.scalar (Fin n) z⁻¹ *
          (GeneralLinearGroup.scalar (Fin n) u⁻¹ * A) := by
      rw [CFSG.LinearAlgebra.conj_scalar_mul_conj u⁻¹ A B, hBAB]
      rw [← mul_assoc, ← mul_assoc]
      rw [hsc u⁻¹ (GeneralLinearGroup.scalar (Fin n) z⁻¹)]
    exact ⟨_, B, z⁻¹, hXu, by simpa [Units.val_inv_eq_inv_val] using hz'.inv, hYX,
      by rw [hcX]; exact hA1, by rw [hcX]; exact hAE, hBE⟩
  ·
    push Not at hap
    obtain ⟨m, d, hbm⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_zpow_mul_pow_of_forall_pow_ne hp hap b
    have hXp : (GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-m)) ^ p = 1 :=
      CFSG.LinearAlgebra.scalar_inv_mul_mul_zpow_neg_pow_eq_one (X := B) (Y := A) hp hp2
        hABA hz'.pow_eq_one hb ha hbm
    have hconj : A * (B * A ^ (-m)) * A⁻¹ =
        GeneralLinearGroup.scalar (Fin n) z * (B * A ^ (-m)) := by
      have hAinv : A * A ^ (-m) * A⁻¹ = A ^ (-m) := by
        rw [← conj_zpow]
        congr 1
        group
      calc A * (B * A ^ (-m)) * A⁻¹
          = (A * B * A⁻¹) * (A * A ^ (-m) * A⁻¹) := by group
        _ = (GeneralLinearGroup.scalar (Fin n) z * B) * (A * A ^ (-m) * A⁻¹) := by rw [hABA]
        _ = GeneralLinearGroup.scalar (Fin n) z * B * A ^ (-m) := by rw [hAinv]
        _ = GeneralLinearGroup.scalar (Fin n) z * (B * A ^ (-m)) := by group
    have hYX : A * (GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-m)) * A⁻¹ =
        GeneralLinearGroup.scalar (Fin n) z *
          (GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-m)) := by
      rw [show GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-m) =
        GeneralLinearGroup.scalar (Fin n) d⁻¹ * (B * A ^ (-m)) from by group]
      rw [CFSG.LinearAlgebra.conj_scalar_mul_conj d⁻¹ (B * A ^ (-m)) A, hconj]
      rw [← mul_assoc, ← mul_assoc]
      rw [hsc d⁻¹ (GeneralLinearGroup.scalar (Fin n) z)]
      group
    have hX1 : conjAut n k (GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-m)) ≠ 1 := by
      intro h1
      apply hBA
      have h3 : conjAut n k (GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-m)) =
          conjAut n k B * conjAut n k A ^ (-m) := by
        simp only [map_mul, map_zpow, conjAut_scalar, one_mul]
      rw [h3] at h1
      rw [mul_eq_one_iff_eq_inv] at h1
      rw [h1, ← _root_.zpow_neg, neg_neg]
      exact Subgroup.zpow_mem_zpowers _ _
    have hXmem : conjAut n k (GeneralLinearGroup.scalar (Fin n) d⁻¹ * B * A ^ (-m)) ∈
        Subgroup.closure {conjAut n k A, conjAut n k B} := by
      rw [map_mul, map_mul, map_zpow, conjAut_scalar, one_mul]
      exact Subgroup.mul_mem _ hBE (Subgroup.zpow_mem _ hAE _)
    exact ⟨_, A, z, hXp, hz, hYX, hX1, hXmem, hAE⟩

theorem exists_perfect_fixSubgroup_of_pow_eq_one_of_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} {k : Type} [Field k] [Finite k] (hpq : p ∣ Nat.card k - 1) {X : GL (Fin n) k}
    (hX : X ^ p = 1) (hpn : p < n) :
    ∃ Q : Subgroup (projectiveSL n k),
      Q ≤ fixSubgroup (conjAut n k X) ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd hp hpq
  have hXmem : X ∈ Subgroup.zpowers X := Subgroup.mem_zpowers X
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (n := n) (p := p) ⟨ζ, hζ⟩
    (Subgroup.zpowers X) (by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm])
    (by
      intro x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hX, _root_.one_zpow])
  set d : Fin n → k := fun l =>
    ((P * X * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) l l with hddef
  have hd : ((P * X * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal d :=
    glConj_eq_diagonal (hP X hXmem)
  have hdpow : ∀ l, d l ^ p = 1 := fun l => by
    simpa [hd] using
      CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.isDiag_entry_pow_eq_one
        (g := P * X * P⁻¹) (by rw [hd]; exact Matrix.isDiag_diagonal d)
        (by simp [hX]) l
  have hcard : (Polynomial.nthRootsFinset p (1 : k)).card ≤ p := by
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots p 1)
  have hmem : ∀ l : Fin n, d l ∈ Polynomial.nthRootsFinset p (1 : k) := by
    intro l
    rw [Polynomial.mem_nthRootsFinset hp.pos]
    exact hdpow l
  have hlt : Fintype.card {y : k // y ∈ Polynomial.nthRootsFinset p (1 : k)} <
      Fintype.card (Fin n) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun l : Fin n => (⟨d l, hmem l⟩ :
      {y : k // y ∈ Polynomial.nthRootsFinset p (1 : k)})) hlt
  have hdij : d i = d j := congrArg Subtype.val heq
  exact exists_perfect_fixSubgroup_of_diagonal_eq (P := P) hp hp2 hpq hX
    (fun r s hrs => by rw [hd]; exact Matrix.diagonal_apply_ne d hrs) hij
    (by simpa [hd] using hdij)

theorem mem_closure_of_mem_innAutDerived_of_commute_projectiveSL {p : ℕ} (hp : p.Prime)
    {n : ℕ} (hn : 2 ≤ n) (hnp : n = p) {k : Type} [Field k] [Finite k] {X Y : GL (Fin n) k}
    (hX : X ^ p = 1) {w : kˣ} (hw : IsPrimitiveRoot (w : k) p)
    (hYX : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) w * X)
    {β : MulAut (projectiveSL n k)} (hβ : β ∈ innAutDerived (projectiveSL n k))
    (hβX : β * conjAut n k X = conjAut n k X * β)
    (hβY : β * conjAut n k Y = conjAut n k Y * β) :
    β ∈ Subgroup.closure {conjAut n k X, conjAut n k Y} := by
  obtain ⟨G, hG⟩ := mem_linearAutGroup_iff.1
    (innAutDerived_projectiveSL_le_linearAutGroup hn hβ)
  have hGX : ∃ α : kˣ, G * X * G⁻¹ = GeneralLinearGroup.scalar (Fin n) α * X := by
    have hcomm : conjAut n k G * conjAut n k X = conjAut n k X * conjAut n k G := by
      rw [hG]
      exact hβX
    obtain ⟨α, hα⟩ := exists_commutator_eq_scalar_of_commute_conjAut (A := G) (B := X) hn hcomm
    exact ⟨α, mul_inv_eq_iff_eq_mul.mp hα⟩
  have hGY : ∃ α' : kˣ, G * Y * G⁻¹ = GeneralLinearGroup.scalar (Fin n) α' * Y := by
    have hcomm : conjAut n k G * conjAut n k Y = conjAut n k Y * conjAut n k G := by
      rw [hG]
      exact hβY
    obtain ⟨α', hα'⟩ := exists_commutator_eq_scalar_of_commute_conjAut (A := G) (B := Y) hn hcomm
    exact ⟨α', mul_inv_eq_iff_eq_mul.mp hα'⟩
  obtain ⟨α, hα⟩ := hGX
  obtain ⟨α', hα'⟩ := hGY
  obtain ⟨c, i, j, hGij⟩ :=
    CFSG.LinearAlgebra.exists_eq_scalar_mul_pow_mul_pow hp hw hX hYX hnp hα hα'
  have hβeq : β = conjAut n k (GeneralLinearGroup.scalar (Fin n) c * X ^ i * Y ^ j) := by
    rw [← hG, hGij]
  rw [hβeq]
  simp only [map_mul, map_pow, conjAut_scalar, one_mul]
  have hXmem : conjAut n k X ∈ Subgroup.closure {conjAut n k X, conjAut n k Y} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hYmem : conjAut n k Y ∈ Subgroup.closure {conjAut n k X, conjAut n k Y} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact Subgroup.mul_mem (Subgroup.closure {conjAut n k X, conjAut n k Y})
    (Subgroup.pow_mem _ hXmem i) (Subgroup.pow_mem _ hYmem j)

theorem innGoodAt_projectiveSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    {k : Type} [Field k] [Finite k] {q : TauCeti.PrimePower} (hcard : Nat.card k = q.card)
    (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    InnGoodAt p (.A (n - 1) q) (projectiveSL n k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro D hD hcardD hDle
  have hDl : D ≤ linearAutGroup n k :=
    hDle.trans (innAutDerived_projectiveSL_le_linearAutGroup hn)
  obtain ⟨A, B, hA_mem, hB_mem, hA1, hBA, ⟨a, ha⟩, ⟨b, hb⟩, z, hzp, hAB⟩ :=
    exists_lifts_of_le_linearAutGroup hp hn hD hcardD hDl
  have hpk : ¬ p ∣ Nat.card k := by
    rw [hcard, TauCeti.PrimePower.card_def]
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd))
  have hclosure_le : Subgroup.closure {conjAut n k A, conjAut n k B} ≤ D :=
    (Subgroup.closure_le D).2 (Set.pair_subset hA_mem hB_mem)
  by_cases hz1 : z = 1
  · have hcomm : A * B = B * A := by
      rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
      rw [hAB, hz1]
      rw [map_one]
    obtain ⟨β, hβmem, hβ1, Q, hQfix, hQperf, hQp⟩ :=
      exists_good_of_commuting_lifts hp hp2 hn hpk (by rwa [hcard]) hcomm ⟨a, ha⟩ ⟨b, hb⟩ hA1 hBA
    exact Or.inl ⟨β, hclosure_le hβmem, hβ1, Q, hQfix, hQperf, hQp⟩
  · have hzprim : IsPrimitiveRoot (z : k) p :=
      IsPrimitiveRoot.coe_units_iff.mpr
        (IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hzp hz1))
    obtain ⟨X, Y, w, hXp, hw, hYX, hX1, hXmem, hYmem⟩ :=
      exists_split_lifts_of_commutator_eq_scalar hp hp2 ⟨a, ha⟩ ⟨b, hb⟩ hzprim hAB hA1 hBA
    have hXD : conjAut n k X ∈ D := hclosure_le hXmem
    have hYD : conjAut n k Y ∈ D := hclosure_le hYmem
    have hpq' : p ∣ Nat.card k - 1 := by
      rw [← Nat.card_units k]
      rw [(IsPrimitiveRoot.coe_units_iff.mp hw).eq_orderOf]
      exact orderOf_dvd_natCard w
    have hpn : p ∣ n := CFSG.LinearAlgebra.dvd_of_conj_eq_scalar hp hw hXp hYX
    have hp_le_n : p ≤ n := Nat.le_of_dvd (by omega) hpn
    rcases lt_or_eq_of_le hp_le_n with hlt | heq
    · obtain ⟨Q, hQfix, hQperf, hQp⟩ :=
        exists_perfect_fixSubgroup_of_pow_eq_one_of_lt hp hp2 hpq' hXp hlt
      exact Or.inl ⟨conjAut n k X, hXD, hX1, Q, hQfix, hQperf, hQp⟩
    · right
      have hlp : lpEpsIdx p (.A (n - 1) q) := by
        refine ⟨q, Or.inl ⟨?_, ?_⟩⟩
        · rw [heq]
        · simpa [hcard] using hpq'
      refine ⟨hlp, ?_⟩
      ext β
      constructor
      · intro hβ
        rw [Subgroup.mem_inf] at hβ
        obtain ⟨hβinn, hβcent⟩ := hβ
        have hβX : β * conjAut n k X = conjAut n k X * β :=
          (Subgroup.mem_centralizer_iff.1 hβcent (conjAut n k X) hXD).symm
        have hβY : β * conjAut n k Y = conjAut n k Y * β :=
          (Subgroup.mem_centralizer_iff.1 hβcent (conjAut n k Y) hYD).symm
        have hclosureXY : Subgroup.closure {conjAut n k X, conjAut n k Y} ≤ D :=
          (Subgroup.closure_le D).2 (Set.pair_subset hXD hYD)
        exact hclosureXY
          (mem_closure_of_mem_innAutDerived_of_commute_projectiveSL hp hn heq.symm hXp hw
            hYX hβinn hβX hβY)
      · intro hβ
        exact le_inf hDle (Subgroup.le_centralizer_iff_isMulCommutative.mpr hD.1) hβ

theorem lieInnGood_linear : LieInnGood isLinearIdx := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨e, hd⟩ := d
  cases e with
  | A n q =>
    have hn1 : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hd).1).1
    have hpq : p ≠ q.p := by
      rw [TauCeti.LieTypeIndex.characteristic_A] at hpc
      exact hpc
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let k := GaloisField q.p q.exponent
    have hcard : Nat.card k = q.card := by
      dsimp only [k]
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
      exact (TauCeti.PrimePower.card_def q).symm
    have h32 : ¬ (p = 3 ∧ q.card = 2) := by
      simpa only [ov2Idx, fieldSize] using h3
    have eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hd⟩).Group ≃*
        LinearFlag.projectiveSL (n + 1) k :=
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) k)
    exact innGoodAt_of_mulEquiv eModel.symm
      (innGoodAt_projectiveSL (n := n + 1) hp hp2 (by omega) (q := q) hcard hpq h32)
  | _ => exact absurd hP (by simp [isLinearIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
