module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFix

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.PartOne.KCAlternating (IsSymplecticBasis)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply)

section Torus

variable {K : Type} [Field K] {r : ℕ}

@[expose] def torusSpEntry (i₀ : Fin r) (a : Kˣ) : Fin r ⊕ Fin r → Kˣ
  | .inl i => if i = i₀ then a else 1
  | .inr i => if i = i₀ then a⁻¹ else 1

@[expose] noncomputable def torusSpGL (i₀ : Fin r) (a : Kˣ) : GL (Fin r ⊕ Fin r) K where
  val := Matrix.diagonal fun x => ((torusSpEntry i₀ a x : Kˣ) : K)
  inv := Matrix.diagonal fun x => (((torusSpEntry i₀ a x)⁻¹ : Kˣ) : K)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    simp

theorem torusSpGL_mem (i₀ : Fin r) (a : Kˣ) : torusSpGL (K := K) i₀ a ∈ StatedSp r K := by
  apply Subgroup.subset_closure
  change Matrix.transpose (Matrix.diagonal _) * _ * Matrix.diagonal _ = _
  rw [Matrix.diagonal_transpose]
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases x with i | i <;> rcases y with j | j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply,
      torusSpEntry, mul_zero, zero_mul]
  · by_cases hij : i = j
    · subst hij
      split_ifs <;> simp
    · simp [hij]
  · by_cases hij : i = j
    · subst hij
      split_ifs <;> simp
    · simp [hij]

theorem toLin_torusSpGL {U : Type*} [AddCommGroup U] [Module K U] (c : Basis (Fin r ⊕ Fin r) K U)
    (i₀ : Fin r) (a : Kˣ) (x : Fin r ⊕ Fin r) :
    Matrix.toLin c c ((torusSpGL i₀ a : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (c x) = ((torusSpEntry i₀ a x : Kˣ) : K) • c x := by
  rw [Matrix.toLin_self]
  change ∑ j, Matrix.diagonal (fun x => ((torusSpEntry i₀ a x : Kˣ) : K)) j x • c j = _
  rw [Finset.sum_eq_single x (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ hj, zero_smul])
    (fun h => absurd (Finset.mem_univ x) h), Matrix.diagonal_apply_eq]

end Torus

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ : ℕ} (P : LowPairing n ℓ)

omit [Finite K] in
theorem wallForm_lowRep_isAlt :
    (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P)
      (polar_lowNil_left P)).IsAlt :=
  wallForm_isAlt _ _ _ fun x => by
    rw [polar_lowNil_left, QuadraticMap.polarBilin_apply_apply]
    exact polar_lowNil_self P x

omit [Finite K] in
theorem wallForm_lowRep_nondegenerate (hn : 3 ≤ n) :
    (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P)
      (polar_lowNil_left P)).Nondegenerate :=
  wallForm_nondegenerate _ _ _ (regular_coordinateQuadPlus n K hn).1

omit [Finite K] [CharP K 2] in
theorem lowForm_single_tau {i : Fin n} (hi : i.val < ℓ) :
    lowForm P (Pi.single (plusIndexEquiv n (.inl i)) (1 : K))
      (Pi.single (plusIndexEquiv n (.inl (P.τ i))) 1) = 1 := by
  rw [lowForm, Finset.sum_eq_single i]
  · rw [ite_eq_left hi, single_inl_apply_inl, ite_eq_left rfl, single_inl_apply_inl, ite_eq_left rfl, one_mul]
  · intro j _ hj
    split_ifs
    · rw [single_inl_apply_inl, ite_eq_right hj, zero_mul]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [Finite K] [CharP K 2] in
theorem leviLin_apply_of_mid (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    {m : Fin (2 * n) → K} (h1 : lowProj (K := K) (n := n) (ℓ := ℓ) m = 0) (h2 : lowNil P m = 0)
    (h3 : midProj (K := K) (n := n) (ℓ := ℓ) m = m) : leviLin P h m = m := by
  have h1' : lowProjU P m = 0 := Subtype.ext h1
  rw [leviLin_apply, h1', h2, map_zero, map_zero, map_zero, Submodule.coe_zero, map_zero, zero_add,
    zero_add, h3]

omit [Finite K] [CharP K 2] in
theorem mid_single_inl {k : Fin n} (hk : ℓ ≤ k.val) :
    lowProj (K := K) (n := n) (ℓ := ℓ) (Pi.single (plusIndexEquiv n (.inl k)) 1) = 0 ∧
      lowNil P (Pi.single (plusIndexEquiv n (.inl k)) (1 : K)) = 0 ∧
      midProj (K := K) (n := n) (ℓ := ℓ) (Pi.single (plusIndexEquiv n (.inl k)) 1) =
        Pi.single (plusIndexEquiv n (.inl k)) 1 := by
  refine ⟨ext_plus (fun i => ?_) fun i => ?_, lowNil_of_mem_lowPerp P fun i _ =>
    single_inl_apply_inr k i, ext_plus (fun i => ?_) fun i => ?_⟩
  · rw [lowProj_inl, single_inl_apply_inl]
    split_ifs with h1 h2 <;> first | rfl | omega
  · rw [lowProj_inr]
    rfl
  · rw [midProj_inl, single_inl_apply_inl]
    split_ifs with h1 h2 <;> first | rfl | (subst h2; omega)
  · rw [midProj_inr, single_inl_apply_inr]
    split_ifs <;> rfl

omit [Finite K] [CharP K 2] in
theorem mid_single_inr {k : Fin n} (hk : ℓ ≤ k.val) :
    lowProj (K := K) (n := n) (ℓ := ℓ) (Pi.single (plusIndexEquiv n (.inr k)) 1) = 0 ∧
      lowNil P (Pi.single (plusIndexEquiv n (.inr k)) (1 : K)) = 0 ∧
      midProj (K := K) (n := n) (ℓ := ℓ) (Pi.single (plusIndexEquiv n (.inr k)) 1) =
        Pi.single (plusIndexEquiv n (.inr k)) 1 := by
  refine ⟨ext_plus (fun i => ?_) fun i => ?_, lowNil_of_mem_lowPerp P fun i hi => ?_,
    ext_plus (fun i => ?_) fun i => ?_⟩
  · rw [lowProj_inl, single_inr_apply_inl]
    split_ifs <;> rfl
  · rw [lowProj_inr]
    rfl
  · rw [single_inr_apply_inr, ite_eq_right]
    rintro rfl
    omega
  · rw [midProj_inl, single_inr_apply_inl]
    split_ifs <;> rfl
  · rw [midProj_inr, single_inr_apply_inr]
    split_ifs with h1 h2 <;> first | rfl | (subst h2; omega)

theorem exists_torus_core (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) {i : Fin n} (hi : i.val < ℓ) (a : Kˣ) :
    ∃ (r : ℕ) (c : Basis (Fin (r + 1) ⊕ Fin (r + 1)) K (LinearMap.range (lowNil (K := K) P))),
      finrank K (LinearMap.range (lowNil (K := K) P)) = 2 * (r + 1) ∧
      ((c (.inl 0) : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K) =
        Pi.single (plusIndexEquiv n (.inl i)) 1 ∧
      ∃ x ∈ typeACore K P,
        projLift hQ x (Pi.single (plusIndexEquiv n (.inl i)) 1) =
          (a : K) • Pi.single (plusIndexEquiv n (.inl i)) 1 ∧
        (∀ m : Fin (2 * n) → K, lowProj (K := K) (n := n) (ℓ := ℓ) m = 0 → lowNil P m = 0 →
          midProj (K := K) (n := n) (ℓ := ℓ) m = m → projLift hQ x m = m) ∧
        ∀ j : Fin (r + 1), j ≠ 0 →
          projLift hQ x ((c (.inl j) : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K) =
            c (.inl j) := by
  have hβ := wallForm_lowRep_isAlt (K := K) P
  have hβn := wallForm_lowRep_nondegenerate (K := K) P hn
  let u : LinearMap.range (lowNil (K := K) P) :=
    ⟨Pi.single (plusIndexEquiv n (.inl i)) 1, by rw [range_lowNil]; exact single_inl_mem_lowSpan hi⟩
  let w : LinearMap.range (lowNil (K := K) P) :=
    ⟨Pi.single (plusIndexEquiv n (.inl (P.τ i))) 1, by
      rw [range_lowNil]; exact single_inl_mem_lowSpan ((P.lt_iff i).mpr hi)⟩
  have huw : wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P)
      (polar_lowNil_left P) u w = 1 := by
    rw [wallForm_eq_lowForm]
    exact lowForm_single_tau P hi
  obtain ⟨r, c, hdim, hc, hc0, -⟩ :=
    CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis_of_apply_eq_one hβ hβn huw
  let A : StatedSp (r + 1) K := ⟨torusSpGL 0 a, torusSpGL_mem 0 a⟩
  have key : ∀ y : Fin (r + 1) ⊕ Fin (r + 1),
      projLift hQ ((spLeviX P c hQ hc hq4 (by omega) A : typeACore K P) :
        matrixProjectiveDerived (coordinateQuadPlus n K))
          ((c y : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K) =
        ((torusSpEntry 0 a y : Kˣ) : K) • ((c y : LinearMap.range (lowNil (K := K) P)) :
          Fin (2 * n) → K) := by
    intro y
    rw [projLift_spLeviX, spLevi_apply, leviLin_apply_of_mem]
    change ((Matrix.toLin c c ((torusSpGL 0 a : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :
      Matrix _ _ K) (c y) : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K) = _
    rw [toLin_torusSpGL]
    rfl
  refine ⟨r, c, hdim, by rw [hc0], _, (spLeviX P c hQ hc hq4 (by omega) A).2, ?_, ?_, ?_⟩
  · have h := key (.inl 0)
    rw [hc0] at h
    simpa [torusSpEntry] using h
  · intro m h1 h2 h3
    rw [projLift_spLeviX, spLevi_apply]
    exact leviLin_apply_of_mid P _ h1 h2 h3
  · intro j hj
    have h := key (.inl j)
    simpa [torusSpEntry, hj] using h

omit [Finite K] [CharP K 2] in
theorem polar_single_inl (v : Fin (2 * n) → K) (i : Fin n) :
    polar (coordinateQuadPlus n K) v (Pi.single (plusIndexEquiv n (.inl i)) 1) =
      v (plusIndexEquiv n (.inr i)) := by
  rw [polar_comm]
  exact (isHypCoord_coordinateQuadPlus i).polar_left v

omit [Finite K] [CharP K 2] in
theorem polar_single_inr (v : Fin (2 * n) → K) (i : Fin n) :
    polar (coordinateQuadPlus n K) v (Pi.single (plusIndexEquiv n (.inr i)) 1) =
      v (plusIndexEquiv n (.inl i)) := by
  rw [polar_comm]
  exact (isHypCoord_coordinateQuadPlus i).polar_right v

omit [CharP K 2] in
theorem exists_unit_ne_one (hq4 : 4 ≤ Nat.card K) : ∃ a : Kˣ, a ≠ 1 := by
  have h3 : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp h3
  exact exists_ne 1

theorem exists_R_moving_of_mem_lowPerp (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K) (hℓ0 : 0 < ℓ)
    (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ)
    {m : Fin (2 * n) → K} (h1 : lowProj (K := K) (n := n) (ℓ := ℓ) m = 0) (h2 : lowNil P m = 0)
    (h3 : midProj (K := K) (n := n) (ℓ := ℓ) m = m) (hmP : m ∈ lowPerp K n ℓ)
    (hvm : polar (coordinateQuadPlus n K) v m ≠ 0) :
    ∃ y ∈ (rangeRestrictHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
      (kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker,
      projLift hQ ((y : typeACore K P) : matrixProjectiveDerived (coordinateQuadPlus n K)) v ≠
        v := by
  obtain ⟨a, ha⟩ := exists_unit_ne_one (K := K) hq4
  set i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨r, c, -, -, x, hx, hxu, hxm, -⟩ := exists_torus_core P hn hq4 hQ (i := i₀) hℓ0 a
  have hu : (Pi.single (plusIndexEquiv n (.inl i₀)) (1 : K) : Fin (2 * n) → K) ∈ lowSpan K n ℓ :=
    single_inl_mem_lowSpan hℓ0
  obtain ⟨y, hy, hylift⟩ := exists_mem_R_projLift_eq_eichler P hQ hn hx hu hmP hxu (hxm m h1 h2 h3)
  refine ⟨y, hy, fun heq => ?_⟩
  have hum : polar (coordinateQuadPlus n K) (Pi.single (plusIndexEquiv n (.inl i₀)) 1)
      (m - (a : K) • m) = 0 :=
    polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu (sub_mem hmP ((lowPerp K n ℓ).smul_mem _ hmP))
  rw [hylift, eichler_apply (coordinateQuadPlus_lowSpan hu) hum,
    polar_eq_zero_of_mem_lowPerp_of_mem_lowSpan hv hu, zero_smul, add_zero, mul_zero, add_zero,
    sub_eq_self, smul_eq_zero, polar_sub_right, polar_smul_right] at heq
  rcases heq with h | h
  · have h' : (1 - (a : K)) * polar (coordinateQuadPlus n K) v m = 0 := by
      rw [sub_mul, one_mul]
      rwa [smul_eq_mul] at h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact ha (Units.ext (sub_eq_zero.mp h'').symm)
    · exact hvm h''
  · have h0 := congrFun h (plusIndexEquiv n (.inl i₀))
    simp at h0

theorem exists_R_moving_of_not_mem_lowPerp (hn : 5 ≤ n) (hℓn : ℓ ≤ n) (hq4 : 4 ≤ Nat.card K)
    (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) {v : Fin (2 * n) → K} {i : Fin n} (hi : i.val < ℓ)
    (hvi : v (plusIndexEquiv n (.inr i)) ≠ 0) :
    ∃ y ∈ (rangeRestrictHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
      (kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker,
      projLift hQ ((y : typeACore K P) : matrixProjectiveDerived (coordinateQuadPlus n K)) v ≠
        v := by
  obtain ⟨a, ha⟩ := exists_unit_ne_one (K := K) hq4
  obtain ⟨r, c, hdim, hc0, x, hx, hxu, hxm, hxc⟩ := exists_torus_core P (by omega) hq4 hQ hi a
  have hu : (Pi.single (plusIndexEquiv n (.inl i)) (1 : K) : Fin (2 * n) → K) ∈ lowSpan K n ℓ :=
    single_inl_mem_lowSpan hi
  have ha1 : (1 - (a : K)) ≠ 0 := fun h => ha (Units.ext (sub_eq_zero.mp h).symm)
  rcases Nat.lt_or_ge ℓ n with hℓ | hℓ
  · set k : Fin n := ⟨ℓ, hℓ⟩ with hk
    obtain ⟨h1, h2, h3⟩ := mid_single_inl (K := K) P (k := k) le_rfl
    have hmP : (Pi.single (plusIndexEquiv n (.inl k)) (1 : K) : Fin (2 * n) → K) ∈ lowPerp K n ℓ :=
      fun j _ => single_inl_apply_inr k j
    obtain ⟨y, hy, hylift⟩ :=
      exists_mem_R_projLift_eq_eichler P hQ (by omega) hx hu hmP hxu (hxm _ h1 h2 h3)
    refine ⟨y, hy, fun heq => ?_⟩
    have hum := polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu
      (sub_mem hmP ((lowPerp K n ℓ).smul_mem (a : K) hmP))
    have h0 := congrFun heq (plusIndexEquiv n (.inl k))
    have hki : k ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp only [hk] at this
      omega
    rw [hylift, eichler_apply (coordinateQuadPlus_lowSpan hu) hum, polar_single_inl] at h0
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, single_inl_apply_inl,
      ite_eq_right hki, mul_zero, sub_zero, ite_true, mul_one] at h0
    exact mul_ne_zero hvi ha1 (by linear_combination h0)
  · have hr : 1 ≤ r := by
      rw [range_lowNil, finrank_lowSpan hℓn] at hdim
      omega
    set j : Fin (r + 1) := ⟨1, by omega⟩ with hjdef
    have hj0 : j ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp [hjdef] at this
    have hmS : ((c (.inl j) : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K) ∈
        lowSpan K n ℓ := mem_lowSpan_of_mem_range (c (.inl j)).2
    have hmP := lowSpan_le_lowPerp ℓ hmS
    obtain ⟨y, hy, hylift⟩ :=
      exists_mem_R_projLift_eq_eichler P hQ (by omega) hx hu hmP hxu (hxc j hj0)
    refine ⟨y, hy, fun heq => ?_⟩
    have hum := polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu
      (sub_mem hmP ((lowPerp K n ℓ).smul_mem (a : K) hmP))
    rw [hylift, eichler_apply (coordinateQuadPlus_lowSpan hu) hum, polar_single_inl] at heq
    set γ := polar (coordinateQuadPlus n K) v (((c (.inl j) : LinearMap.range (lowNil (K := K) P)) :
      Fin (2 * n) → K) - (a : K) • ((c (.inl j) : LinearMap.range (lowNil (K := K) P)) :
        Fin (2 * n) → K)) + coordinateQuadPlus n K (((c (.inl j) : LinearMap.range
          (lowNil (K := K) P)) : Fin (2 * n) → K) - (a : K) • ((c (.inl j) :
            LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K)) *
              v (plusIndexEquiv n (.inr i)) with hγ
    have hU : (v (plusIndexEquiv n (.inr i)) * (1 - (a : K))) • c (.inl j) - γ • c (.inl 0) =
        0 := by
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, hc0, Submodule.coe_zero]
      have h' := sub_eq_zero.mpr heq
      rw [← h']
      module
    have h3 := congrArg (fun z => c.repr z (.inl j)) hU
    simp only [map_sub, map_smul, Basis.repr_self, map_zero, Finsupp.coe_sub, Finsupp.coe_smul,
      Pi.sub_apply, Pi.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      Finsupp.coe_zero, Pi.zero_apply] at h3
    rw [Finsupp.single_eq_of_ne (by simp [hj0]), mul_zero, sub_zero] at h3
    exact mul_ne_zero hvi ha1 h3

theorem mem_range_lowNil_iff_forall_R (hn : 5 ≤ n) (hℓn : ℓ ≤ n) (hℓ0 : 0 < ℓ)
    (hq4 : 4 ≤ Nat.card K) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (v : Fin (2 * n) → K) :
    v ∈ LinearMap.range (lowNil (K := K) P) ↔
      ∀ y ∈ (rangeRestrictHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
        (kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker,
        projLift hQ ((y : typeACore K P) : matrixProjectiveDerived (coordinateQuadPlus n K)) v =
          v := by
  constructor
  · intro hv y hy
    have h1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hy).1
    have h := congrArg (fun f : Module.End K (LinearMap.range (lowNil (K := K) P)) =>
      ((f ⟨v, hv⟩ : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K)) h1
    simpa [rangeRestrictHom] using h
  · intro hall
    by_contra hv
    rw [range_lowNil] at hv
    by_cases hperp : v ∈ lowPerp K n ℓ
    · obtain ⟨k, hk, hvk⟩ : ∃ k : Fin n, ℓ ≤ k.val ∧
          (v (plusIndexEquiv n (.inl k)) ≠ 0 ∨ v (plusIndexEquiv n (.inr k)) ≠ 0) := by
        by_contra hno
        push Not at hno
        apply hv
        intro i
        by_cases hi : i.val < ℓ
        · exact ⟨hperp i hi, fun h => absurd h (by omega)⟩
        · exact ⟨(hno i (by omega)).2, fun _ => (hno i (by omega)).1⟩
      rcases hvk with h | h
      · obtain ⟨h1, h2, h3⟩ := mid_single_inr (K := K) P hk
        obtain ⟨y, hy, hyv⟩ := exists_R_moving_of_mem_lowPerp P (by omega) hq4 hℓ0 hQ hperp h1 h2
          h3 (fun j hj => by
            rw [single_inr_apply_inr, ite_eq_right]
            rintro rfl
            omega) (by rwa [polar_single_inr])
        exact hyv (hall y hy)
      · obtain ⟨h1, h2, h3⟩ := mid_single_inl (K := K) P hk
        obtain ⟨y, hy, hyv⟩ := exists_R_moving_of_mem_lowPerp P (by omega) hq4 hℓ0 hQ hperp h1 h2
          h3 (fun j _ => single_inl_apply_inr k j) (by rwa [polar_single_inl])
        exact hyv (hall y hy)
    · obtain ⟨i, hi, hvi⟩ : ∃ i : Fin n, i.val < ℓ ∧ v (plusIndexEquiv n (.inr i)) ≠ 0 := by
        by_contra hno
        push Not at hno
        exact hperp hno
      obtain ⟨y, hy, hyv⟩ := exists_R_moving_of_not_mem_lowPerp P hn hℓn hq4 hQ hi hvi
      exact hyv (hall y hy)

end Core

end CFSG.SeitzReduction.OmegaPilot
