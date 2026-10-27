module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankSiegel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentRot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open QuadraticMap Module CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172C.Rank
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem isPlusType_iff_even_pred {n : ℕ} (htype : IsPlusType Q ↔ Odd n) (hn : 1 ≤ n) :
    IsPlusType Q ↔ Even (n - 1) := by
  rw [htype, Nat.odd_iff, Nat.even_iff]
  omega

private theorem exists_rotationFrame_of_type (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank F V = 2 * n) (hn : 2 ≤ n) (htype : IsPlusType Q ↔ Odd n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    ∃ (x y : Fin (n - 1) → V) (u v : V),
      (∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p) ∧
      (∀ i j, i ≠ j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧ polar Q (y i) (x j) = 0 ∧
        polar Q (y i) (y j) = 0) ∧
      Q u = 0 ∧ Q v = 0 ∧ polar Q u v = 1 ∧
      ∀ i, polar Q u (x i) = 0 ∧ polar Q u (y i) = 0 ∧ polar Q v (x i) = 0 ∧ polar Q v (y i) = 0 := by
  obtain ⟨a, b, e, f, hpair, hperp, he, hf, hef, horth⟩ :=
    exists_anisoPairFrame_aux (n - 1) hQ (by omega) (isPlusType_iff_even_pred htype (by omega))
  have hrot : ∀ i, ∃ x ∈ Submodule.span F {a i, b i}, ∃ y ∈ Submodule.span F {a i, b i},
      Q x ≠ 0 ∧ Q y ≠ 0 ∧ orderOf (reflect Q x * reflect Q y) = p := fun i =>
    exists_orderOf_reflect_mul_reflect_eq (hpair i).finrank_span_pair
      (fun x hx h => (hpair i).eq_zero_of_mem_span_pair hx h) hp hp2 hpq
  choose x hx y hy hQx hQy hord using hrot
  refine ⟨x, y, e, f, fun i => ⟨hQx i, hQy i, hord i⟩, fun i j hij => ?_, he, hf, hef, fun i => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hperp i j hij
    exact ⟨polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hx i) (hx j),
      polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hx i) (hy j),
      polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hy i) (hx j),
      polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hy i) (hy j)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := horth i
    exact ⟨polar_eq_zero_of_mem_span_pair h1 h2 (hx i), polar_eq_zero_of_mem_span_pair h1 h2 (hy i),
      polar_eq_zero_of_mem_span_pair h3 h4 (hx i), polar_eq_zero_of_mem_span_pair h3 h4 (hy i)⟩

private theorem exists_rotations_card_aux (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x y : Fin (n - 1) → V}
    (hrot : ∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p)
    (hperp : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧
      polar Q (y i) (x j) = 0 ∧ polar Q (y i) (y j) = 0) :
    ∃ ρ : Fin (n - 1) → ↥(orthDerived Q),
      (∀ i, (ρ i : V ≃ₗ[F] V) = reflect Q (x i) * reflect Q (y i)) ∧
      IsElemAbelian p (Subgroup.closure (Set.range ρ)) ∧
      Nat.card (Subgroup.closure (Set.range ρ)) = p ^ (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxy : ∀ i, polar Q (x i) (y i) ≠ 0 := fun i =>
    polar_ne_zero_of_orderOf_reflect_mul_reflect hp hp2 (hrot i).2.2
  let ρ : Fin (n - 1) → ↥(orthDerived Q) := fun i =>
    ⟨reflect Q (x i) * reflect Q (y i),
      reflect_mul_reflect_mem_orthDerived hQ (hrot i).1 (hrot i).2.1⟩
  refine ⟨ρ, fun i => rfl, ?_⟩
  have hcomm : ∀ i j, Commute (ρ i) (ρ j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · obtain ⟨h1, h2, h3, h4⟩ := hperp i j hij
      exact Subtype.ext (commute_reflect_mul_reflect_rot h1 h2 h3 h4).eq
  have hord : ∀ i, orderOf (ρ i) = p := fun i => by
    show orderOf (⟨_, _⟩ : ↥(orthDerived Q)) = p
    rw [Subgroup.orderOf_mk]
    exact (hrot i).2.2
  have hindep : ∀ i, ρ i ∉ Subgroup.closure (ρ '' {j | j ≠ i}) := by
    refine not_mem_closure_image_of_smul_ne (orthDerived Q).subtype ρ x (fun i => ?_)
      (fun i j hij => ?_)
    · exact reflect_mul_reflect_apply_ne (hrot i).1 (hrot i).2.1 (hxy i)
    · obtain ⟨h1, -, h3, -⟩ := hperp j i (Ne.symm hij)
      exact reflect_mul_reflect_apply_of_polar_eq_zero h1 h3
  exact isElemAbelian_card_closure_range ρ hcomm hord hindep

private theorem rotations_normalize_rootGroup_aux {n : ℕ} {x y : Fin (n - 1) → V} {u v : V} (hn : 2 ≤ n)
    (hrot : ∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p)
    (hporth : ∀ i, polar Q u (x i) = 0 ∧ polar Q u (y i) = 0 ∧ polar Q v (x i) = 0 ∧
      polar Q v (y i) = 0)
    (hu : Q u = 0) (huv : polar Q u v = 1) (hxu : ∀ i, polar Q (x i) u = 0)
    (hyu : ∀ i, polar Q (y i) u = 0) (hxy : ∀ i, polar Q (x i) (y i) ≠ 0)
    {ρ : Fin (n - 1) → ↥(orthDerived Q)}
    (hρ : ∀ i, (ρ i : V ≃ₗ[F] V) = reflect Q (x i) * reflect Q (y i)) :
    (rootGroup Q u).subgroupOf (orthDerived Q) ≠ ⊥ ∧
      Subgroup.closure (Set.range ρ) ≤
        Subgroup.normalizer ((rootGroup Q u).subgroupOf (orthDerived Q) : Set ↥(orthDerived Q)) := by
  have i0 : 0 < n - 1 := by omega
  constructor
  · have hB := hxy ⟨0, i0⟩
    refine subgroupOf_rootGroup_ne_bot (a := x ⟨0, i0⟩) (w := (Q (x ⟨0, i0⟩) / polar Q (x ⟨0, i0⟩)
      (y ⟨0, i0⟩)) • y ⟨0, i0⟩) (f := v) hu (hrot ⟨0, i0⟩).1 (hporth ⟨0, i0⟩).1 ?_ ?_ ?_ ?_
    · rw [polar_smul_right_eq, (hporth ⟨0, i0⟩).2.1, mul_zero]
    · rw [polar_smul_right_eq, div_mul_cancel₀ _ hB]
    · rw [polar_comm, huv]
    · exact (hporth ⟨0, i0⟩).2.2.1
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact mem_normalizer_subgroupOf_rootGroup
      (by rw [hρ i]; exact reflect_mul_reflect_apply_of_polar_eq_zero (hxu i) (hyu i))

theorem exists_elemAbelian_normalizing_twoGroup_of_type (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank F V = 2 * n) (hn : 2 ≤ n) (htype : IsPlusType Q ↔ Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) :
    ∃ E T : Subgroup ↥(orthDerived Q), IsElemAbelian p E ∧ Nat.card E = p ^ (n - 1) ∧ IsPGroup 2 T ∧
      T ≠ ⊥ ∧ E ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q)) := by
  obtain ⟨x, y, u, v, hrot, hperp, hu, -, huv, hporth⟩ :=
    exists_rotationFrame_of_type hQ hdim hn htype hp hp2 hpq
  have hxu : ∀ i, polar Q (x i) u = 0 := fun i => by rw [polar_comm]; exact (hporth i).1
  have hyu : ∀ i, polar Q (y i) u = 0 := fun i => by rw [polar_comm]; exact (hporth i).2.1
  have hxy : ∀ i, polar Q (x i) (y i) ≠ 0 := fun i =>
    polar_ne_zero_of_orderOf_reflect_mul_reflect hp hp2 (hrot i).2.2
  obtain ⟨ρ, hρ, hEA, hcard⟩ := exists_rotations_card_aux hQ hp hp2 hrot hperp
  obtain ⟨hTne, hTnorm⟩ := rotations_normalize_rootGroup_aux hn hrot hporth hu huv hxu hyu hxy hρ
  exact ⟨_, (rootGroup Q u).subgroupOf (orthDerived Q), hEA, hcard, isPGroup_two_subgroupOf_rootGroup u,
    hTne, hTnorm⟩

theorem card_le_pow_pred_of_isElemAbelian_of_type (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank F V = 2 * n) (htype : IsPlusType Q ↔ Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (n - 1) := by
  have hreg : CFSG.RankThree.PartOne.K159.RegOn Q ⊤ := fun u _ h =>
    hQ.1 u fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using h w Submodule.mem_top
  obtain ⟨r, U, hU⟩ := exists_planeDecomp hQ hp hp2 hpq hE ⊤ hreg fun _ _ _ _ => Submodule.mem_top
  have hle : Nat.card E ≤ p ^ r := hU.card_le_pow hE hp
  have hrn : r ≤ n := by
    have h1 := hU.toIsPlaneSystem.finrank_biSup Finset.univ
    have h2 := Submodule.finrank_le (⨆ j ∈ (Finset.univ : Finset (Fin r)), U j)
    rw [h1, Finset.card_univ, Fintype.card_fin, hdim] at h2
    omega
  have hrne : r ≠ n := by
    rintro rfl
    have h := hU.toIsPlaneSystem.isPlusType_iff_of_finrank hdim
    rcases Nat.even_or_odd r with he | ho
    · exact Nat.not_even_iff_odd.2 (htype.1 (h.2 he)) he
    · exact Nat.not_even_iff_odd.2 ho (h.1 (htype.2 ho))
  exact hle.trans (Nat.pow_le_pow_right hp.pos (by omega))

theorem glaTwoLocalRank_orthDerived_of_type [Finite ↥(orthDerived Q)] (hQ : (polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank F V = 2 * n) (hn : 2 ≤ n) (htype : IsPlusType Q ↔ Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) : GLATwoLocalRank p ↥(orthDerived Q) = n - 1 := by
  obtain ⟨E, T, hE, hcard, hT2, hT0, hET⟩ :=
    exists_elemAbelian_normalizing_twoGroup_of_type hQ hdim hn htype hp hp2 hpq
  refine le_antisymm ?_ ?_
  · show sSup {k' | ∃ H : Subgroup ↥(orthDerived Q), IsTwoLocal H ∧ CFSG.Open.pRank p H = k'} ≤ n - 1
    refine csSup_le' ?_
    rintro k' ⟨H, hH, rfl⟩
    obtain ⟨R, -, -, rfl⟩ := hH
    exact CFSG.SectionRank.pRank_le hp.one_lt fun E' _ hE' =>
      card_le_pow_pred_of_isElemAbelian_of_type hQ hdim htype hp hp2 hpq hE'
  · have h := card_le_pow_glaTwoLocalRank hp hE hT0 hT2 hET
    rw [hcard] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h

end CFSG.LocalAnalysis.GLTheoremA.T173U

end
