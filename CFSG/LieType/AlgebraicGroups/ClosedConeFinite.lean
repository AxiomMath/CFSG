module

public import CFSG.LieType.AlgebraicGroups.ClosedCone
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

open MvPolynomial

universe u v

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

section Coordinates

variable {σ : Type*} [Fintype σ]

theorem aeval_smul_of_isHomogeneous {t : k} {x : σ → k} {q : MvPolynomial σ k} {m : ℕ}
    (hq : q.IsHomogeneous m) :
    MvPolynomial.aeval (t • x) q = t ^ m * MvPolynomial.aeval x q := by
  have hw : ∀ d : σ →₀ ℕ, Finsupp.weight (fun _ : σ => (1 : ℕ)) d = d.degree := by
    intro d
    simp [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum]
  revert m
  intro m hq
  refine MvPolynomial.IsWeightedHomogeneous.induction_on (w := fun _ : σ => (1 : ℕ)) (m := m)
    (motive := fun q _ => MvPolynomial.aeval (t • x) q = t ^ m * MvPolynomial.aeval x q)
    ?_ ?_ ?_ hq
  · simp
  · intro p q _ _ hpm hqm
    simp only [map_add, hpm, hqm, mul_add]
  · intro d r hr
    have hd : d.degree = m := by rw [← hw d]; exact hr
    have hprod : (∏ a, (t * x a) ^ d a) = t ^ d.degree * ∏ a, x a ^ d a := by
      rw [Finset.prod_congr rfl (fun a _ => mul_pow t (x a) (d a)), Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
    simp only [MvPolynomial.aeval_monomial, Finsupp.prod_pow, Pi.smul_apply, smul_eq_mul]
    rw [hprod, hd, Algebra.algebraMap_self, RingHom.id_apply]
    ring

theorem aeval_smul_eq_sum_homogeneousComponent (p : MvPolynomial σ k) (x : σ → k) (t : k) :
    MvPolynomial.aeval (t • x) p =
      ∑ m ∈ Finset.range (p.totalDegree + 1),
        t ^ m * MvPolynomial.aeval x (homogeneousComponent m p) := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  rw [MvPolynomial.aeval_sum]
  exact Finset.sum_congr rfl fun m _ =>
    aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous m p)

theorem homogeneousComponent_mem_vanishingIdeal [IsAlgClosed k] {Z : Set (σ → k)}
    (hZ : ∀ (c : k) (x : σ → k), x ∈ Z → c • x ∈ Z)
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.vanishingIdeal k Z) (m : ℕ) :
    homogeneousComponent m p ∈ MvPolynomial.vanishingIdeal k Z := by
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hp ⊢
  intro x hx
  have hzero : ∀ t : k, MvPolynomial.aeval (t • x) p = 0 := fun t => hp (t • x) (hZ t x hx)
  let P : Polynomial k := ∑ j ∈ Finset.range (p.totalDegree + 1),
      Polynomial.C (MvPolynomial.aeval x (homogeneousComponent j p)) * Polynomial.X ^ j
  have heval : ∀ t : k, P.eval t =
      ∑ j ∈ Finset.range (p.totalDegree + 1),
        t ^ j * MvPolynomial.aeval x (homogeneousComponent j p) := by
    intro t
    rw [show P.eval t = ∑ j ∈ Finset.range (p.totalDegree + 1),
        MvPolynomial.aeval x (homogeneousComponent j p) * t ^ j from by
      simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hP : P = 0 := by
    refine Polynomial.funext fun t => ?_
    rw [Polynomial.eval_zero, heval t, ← aeval_smul_eq_sum_homogeneousComponent p x t, hzero t]
  have hcoeff : P.coeff m = MvPolynomial.aeval x (homogeneousComponent m p) := by
    have hsum : P.coeff m = ∑ j ∈ Finset.range (p.totalDegree + 1),
        (Polynomial.C (MvPolynomial.aeval x (homogeneousComponent j p)) *
          Polynomial.X ^ j).coeff m := by
      change (∑ j ∈ Finset.range (p.totalDegree + 1),
        Polynomial.C (MvPolynomial.aeval x (homogeneousComponent j p)) *
          Polynomial.X ^ j).coeff m = _
      rw [Polynomial.finset_sum_coeff]
    rw [hsum]
    by_cases hm : m ∈ Finset.range (p.totalDegree + 1)
    · rw [Finset.sum_eq_single m]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro j _ hjm
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hjm), mul_zero]
      · exact fun h => absurd hm h
    · have hlt : p.totalDegree < m := by
        simp only [Finset.mem_range, not_lt] at hm
        omega
      have hz : homogeneousComponent m p = 0 := homogeneousComponent_eq_zero m p hlt
      rw [hz, map_zero, Finset.sum_eq_zero]
      intro j hj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun h : m = j => hm (h ▸ hj)), mul_zero]
  rw [← hcoeff, hP, Polynomial.coeff_zero]

theorem homogeneousComponent_eq_zero_of_isHomogeneous {R : Type*} [CommSemiring R] {σ : Type*}
    {p : MvPolynomial σ R} {m n : ℕ} (hp : p.IsHomogeneous m) (hmn : m ≠ n) :
    homogeneousComponent n p = 0 := by
  refine homogeneousComponent_eq_zero' n p fun d hd hdn => ?_
  exact MvPolynomial.mem_support_iff.mp hd (hp.coeff_eq_zero (by rw [hdn]; exact hmn.symm))

theorem homogeneousComponent_mul_of_isHomogeneous {σ : Type*} {R : Type*} [CommSemiring R]
    {p q : MvPolynomial σ R} {m : ℕ} (hp : p.IsHomogeneous m) (n : ℕ) :
    homogeneousComponent (m + n) (p * q) = p * homogeneousComponent n q := by
  conv_lhs => rw [← sum_homogeneousComponent q, Finset.mul_sum]
  rw [map_sum]
  have hzero : ∀ j ∈ Finset.range (q.totalDegree + 1), j ≠ n →
      homogeneousComponent (m + n) (p * homogeneousComponent j q) = 0 := by
    intro j _ hjn
    exact homogeneousComponent_eq_zero_of_isHomogeneous
      (hp.mul (homogeneousComponent_isHomogeneous j q)) (by omega)
  have hself : homogeneousComponent (m + n) (p * homogeneousComponent n q) =
      p * homogeneousComponent n q :=
    homogeneousComponent_eq_self (hp.mul (homogeneousComponent_isHomogeneous n q))
  by_cases hn : n ∈ Finset.range (q.totalDegree + 1)
  · rw [Finset.sum_eq_single n hzero (fun h => absurd hn h)]
    exact hself
  · have hlt : q.totalDegree < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    have hqn : homogeneousComponent n q = 0 := homogeneousComponent_eq_zero n q hlt
    rw [hqn, mul_zero, Finset.sum_eq_zero]
    intro j hj
    exact hzero j hj (by
      have := Finset.mem_range.mp hj
      omega)

def linearFormPoly [DecidableEq σ] (ψ : (σ → k) →ₗ[k] k) : MvPolynomial σ k :=
  ∑ i, MvPolynomial.C (ψ (Pi.single i (1 : k))) * MvPolynomial.X i

theorem aeval_linearFormPoly [DecidableEq σ] (ψ : (σ → k) →ₗ[k] k) (x : σ → k) :
    MvPolynomial.aeval x (linearFormPoly ψ) = ψ x := by
  have hsum : ψ x = ∑ i, ψ (Pi.single i (1 : k)) * x i := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (x i) = x i • (Pi.single i (1 : k) : σ → k) from by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]]
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hsum, linearFormPoly, MvPolynomial.aeval_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply]

theorem isHomogeneous_linearFormPoly [DecidableEq σ] (ψ : (σ → k) →ₗ[k] k) :
    (linearFormPoly ψ).IsHomogeneous 1 := by
  rw [linearFormPoly]
  exact MvPolynomial.IsHomogeneous.sum Finset.univ _ 1 fun i _ => isHomogeneous_C_mul_X _ i

theorem finsupp_degree_eq_sum (d : σ →₀ ℕ) : d.degree = d.sum (fun _ e => e) := by
  rw [Finsupp.degree_eq_sum, Finsupp.sum_fintype _ _ fun _ => rfl]

end Coordinates

section Finite

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem finite_setOf_mem_zeroLocus_and_apply_eq_one [IsAlgClosed k]
    {Z : Set (σ → k)} (I : Ideal (MvPolynomial σ k)) (hZ : Z = MvPolynomial.zeroLocus k I)
    (hcone : ∀ (t : k) (x : σ → k), x ∈ Z → t • x ∈ Z)
    (ψ : (σ → k) →ₗ[k] k) (hψ : ∀ x ∈ Z, ψ x = 0 → x = 0) :
    {x | x ∈ Z ∧ ψ x = 1}.Finite := by
  classical
  by_cases hσ : Nonempty σ
  · obtain ⟨i₀⟩ := hσ
    have hmemZ : ∀ x : σ → k, x ∈ Z ↔ x ∈ MvPolynomial.zeroLocus k I := fun x => by rw [hZ]
    let L : MvPolynomial σ k := linearFormPoly ψ
    have hLhom : L.IsHomogeneous 1 := isHomogeneous_linearFormPoly ψ
    have hLeval : ∀ x : σ → k, MvPolynomial.aeval x L = ψ x := fun x => aeval_linearFormPoly ψ x
    have hIZ : I ≤ MvPolynomial.vanishingIdeal k Z := by
      intro p hp
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      exact (MvPolynomial.mem_zeroLocus_iff.mp ((hmemZ x).mp hx)) p hp
    have hJzero : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Z) = Z := by
      refine le_antisymm ?_ (MvPolynomial.zeroLocus_vanishingIdeal_le Z)
      intro x hx
      refine (hmemZ x).mpr ((MvPolynomial.mem_zeroLocus_iff).mpr fun p hp => ?_)
      exact (MvPolynomial.mem_zeroLocus_iff.mp hx) p (hIZ hp)
    have hXL : ∀ i : σ, MvPolynomial.X i ∈
        (MvPolynomial.vanishingIdeal k Z ⊔ Ideal.span {L}).radical := by
      intro i
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)
        (I := MvPolynomial.vanishingIdeal k Z ⊔ Ideal.span {L})]
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      have hxZ : x ∈ Z := by
        rw [← hJzero]
        exact (MvPolynomial.mem_zeroLocus_iff).mpr fun p hp =>
          (MvPolynomial.mem_zeroLocus_iff.mp hx) p (Ideal.mem_sup_left hp)
      have hxψ : ψ x = 0 := by
        rw [← hLeval x]
        exact (MvPolynomial.mem_zeroLocus_iff.mp hx) L (Ideal.mem_sup_right (Ideal.subset_span rfl))
      rw [hψ x hxZ hxψ]
      simp
    choose N hN using fun i => Ideal.mem_radical_iff.mp (hXL i)
    have hNmem : ∀ i : σ, MvPolynomial.X i ^ (N i + 1) ∈
        (MvPolynomial.vanishingIdeal k Z ⊔ Ideal.span {L}) := by
      intro i
      rw [pow_succ']
      exact Ideal.mul_mem_left _ _ (hN i)
    set K : Ideal (MvPolynomial σ k) := MvPolynomial.vanishingIdeal k Z ⊔ Ideal.span {L - 1} with hK
    have hdrop : ∀ i : σ, ∃ g : MvPolynomial σ k, g.totalDegree ≤ N i ∧
        MvPolynomial.X i ^ (N i + 1) - g ∈ K := by
      intro i
      obtain ⟨y, hyJ, z, hzL, hyz⟩ := Submodule.mem_sup.mp (hNmem i)
      obtain ⟨g, rfl⟩ := dvd_def.mp (Ideal.mem_span_singleton.mp hzL)
      refine ⟨homogeneousComponent (N i) g, ?_, ?_⟩
      · exact (homogeneousComponent_isHomogeneous (N i) g).totalDegree_le
      · have hLg : homogeneousComponent (N i + 1) (L * g) = L * homogeneousComponent (N i) g := by
          rw [show N i + 1 = 1 + N i from Nat.add_comm _ _]
          exact homogeneousComponent_mul_of_isHomogeneous hLhom (N i)
        have hkey : MvPolynomial.X i ^ (N i + 1) =
            homogeneousComponent (N i + 1) y + L * homogeneousComponent (N i) g := by
          have h := congrArg (homogeneousComponent (N i + 1)) hyz.symm
          simp only [map_add] at h
          rwa [homogeneousComponent_eq_self (isHomogeneous_X_pow i (N i + 1)), hLg] at h
        have hmemJ : homogeneousComponent (N i + 1) y ∈ K := by
          rw [hK]
          exact Ideal.mem_sup_left (homogeneousComponent_mem_vanishingIdeal hcone hyJ (N i + 1))
        have hmul : (L - 1) * homogeneousComponent (N i) g ∈ K := by
          have hLm : L - 1 ∈ K := by
            rw [hK]
            exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
          have h' := Ideal.mul_mem_left K (homogeneousComponent (N i) g) hLm
          rwa [mul_comm (homogeneousComponent (N i) g) (L - 1)] at h'
        rw [hkey]
        have hEq : homogeneousComponent (N i + 1) y + L * homogeneousComponent (N i) g -
              homogeneousComponent (N i) g =
            homogeneousComponent (N i + 1) y + (L - 1) * homogeneousComponent (N i) g := by
          ring
        rw [hEq]
        exact Ideal.add_mem K hmemJ hmul
    let S : Set (MvPolynomial σ k) :=
      {q : MvPolynomial σ k | ∃ d : σ →₀ ℕ, d.degree < ∑ i, (N i + 1) ∧
        q = MvPolynomial.monomial d 1}
    let P : Submodule k (MvPolynomial σ k) := Submodule.span k S
    have hNt_pos : 0 < ∑ i, (N i + 1) := by
      have h := Finset.single_le_sum (f := fun i => N i + 1) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ i₀)
      omega
    have hmemP : ∀ q : MvPolynomial σ k, q.totalDegree < ∑ i, (N i + 1) → q ∈ P := by
      intro q hq
      nth_rewrite 1 [MvPolynomial.as_sum q]
      refine Submodule.sum_mem P fun d hd => ?_
      have hle : d.degree ≤ q.totalDegree := by
        rw [finsupp_degree_eq_sum]
        exact MvPolynomial.le_totalDegree hd
      have hlt : d.degree < ∑ i, (N i + 1) := lt_of_le_of_lt hle hq
      rw [show MvPolynomial.monomial d (q.coeff d) = q.coeff d • MvPolynomial.monomial d 1 by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem P _ (Submodule.subset_span ⟨d, hlt, rfl⟩)
    have hX : ∀ i : σ, MvPolynomial.X i =
        MvPolynomial.monomial (Finsupp.single i 1) (1 : k) := by
      intro i
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
    have hmono : ∀ (d : σ →₀ ℕ) (i : σ), d.degree < ∑ i, (N i + 1) →
        ∃ q ∈ P, MvPolynomial.monomial (d + Finsupp.single i 1) 1 - q ∈ K := by
      intro d i hd
      let m : σ →₀ ℕ := d + Finsupp.single i 1
      have hm : m = d + Finsupp.single i 1 := rfl
      have hstep : m.degree = d.degree + 1 := by
        rw [hm]
        simp [Finsupp.degree_eq_sum, Finset.sum_add_distrib]
      by_cases hcase : m.degree < ∑ i, (N i + 1)
      · exact ⟨_, Submodule.subset_span ⟨m, hcase, rfl⟩, by rw [← hm]; simp⟩
      · have hpigeon : ∃ j : σ, N j + 1 ≤ m j := by
          by_contra hcon
          simp only [not_exists, not_le] at hcon
          have hlt : (∑ j, m j) < ∑ j, (N j + 1) :=
            Finset.sum_lt_sum (fun j _ => le_of_lt (hcon j)) ⟨i₀, Finset.mem_univ i₀, hcon i₀⟩
          rw [← Finsupp.degree_eq_sum] at hlt
          exact absurd hlt hcase
        obtain ⟨j, hj⟩ := hpigeon
        obtain ⟨g, hgdeg, hgK⟩ := hdrop j
        set m' : σ →₀ ℕ := m - Finsupp.single j (N j + 1) with hm'
        have hsplit : m = m' + Finsupp.single j (N j + 1) := by
          rw [hm']
          ext a
          by_cases ha : a = j
          · subst ha
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
            omega
          · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne ha,
              Nat.sub_zero, add_zero]
        have hm'deg : m'.degree = m.degree - (N j + 1) := by
          have hsum := map_add Finsupp.degree m' (Finsupp.single j (N j + 1))
          rw [Finsupp.degree_single, ← hsplit] at hsum
          omega
        have hmono_eq : (MvPolynomial.monomial (d + Finsupp.single i 1) (1 : k) :
            MvPolynomial σ k) = MvPolynomial.monomial m' 1 * MvPolynomial.X j ^ (N j + 1) := by
          rw [← hm, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
            ← hsplit, mul_one]
        refine ⟨MvPolynomial.monomial m' 1 * g, hmemP _ ?_, ?_⟩
        · have ht1 : (MvPolynomial.monomial m' 1 : MvPolynomial σ k).totalDegree = m'.degree := by
            rw [MvPolynomial.totalDegree_monomial m' one_ne_zero, ← finsupp_degree_eq_sum]
          have ht2 := MvPolynomial.totalDegree_mul (MvPolynomial.monomial m' 1) g
          have hjNt : N j + 1 ≤ ∑ i, (N i + 1) :=
            Finset.single_le_sum (f := fun i => N i + 1) (fun i _ => Nat.zero_le _)
              (Finset.mem_univ j)
          omega
        · rw [hmono_eq]
          rw [← mul_sub]
          exact Ideal.mul_mem_left K _ hgK
    have hspan : ∀ p : MvPolynomial σ k, ∃ q ∈ P, p - q ∈ K := by
      intro p
      refine MvPolynomial.induction_on (motive := fun p => ∃ q ∈ P, p - q ∈ K) p ?_ ?_ ?_
      · intro a
        refine ⟨MvPolynomial.C a, hmemP _ ?_, by simp⟩
        rw [MvPolynomial.totalDegree_C]
        exact hNt_pos
      · intro p q hp hq
        obtain ⟨q₁, hq₁P, hq₁K⟩ := hp
        obtain ⟨q₂, hq₂P, hq₂K⟩ := hq
        refine ⟨q₁ + q₂, Submodule.add_mem P hq₁P hq₂P, ?_⟩
        have heq : p + q - (q₁ + q₂) = (p - q₁) + (q - q₂) := by ring
        rw [heq]
        exact Ideal.add_mem K hq₁K hq₂K
      · intro p i hp
        obtain ⟨q, hqP, hqK⟩ := hp
        have hall : ∀ r ∈ P, ∃ r' ∈ P, r * MvPolynomial.X i - r' ∈ K := by
          intro r hr
          refine Submodule.span_induction (s := S)
            (p := fun r _ => ∃ r' ∈ P, r * MvPolynomial.X i - r' ∈ K) ?_ ?_ ?_ ?_ hr
          · intro x hx
            obtain ⟨d, hd, rfl⟩ := hx
            have hone : (MvPolynomial.monomial d (1 : k) : MvPolynomial σ k) * MvPolynomial.X i =
                MvPolynomial.monomial (d + Finsupp.single i 1) 1 := by
              rw [hX i, MvPolynomial.monomial_mul_monomial, mul_one]
            obtain ⟨r', hr'P, hr'K⟩ := hmono d i hd
            exact ⟨r', hr'P, by rw [hone]; exact hr'K⟩
          · exact ⟨0, Submodule.zero_mem P, by simp⟩
          · intro x y _ _ hx hy
            obtain ⟨rx, hrxP, hrxK⟩ := hx
            obtain ⟨ry, hryP, hryK⟩ := hy
            refine ⟨rx + ry, Submodule.add_mem P hrxP hryP, ?_⟩
            have heq : (x + y) * MvPolynomial.X i - (rx + ry) =
                (x * MvPolynomial.X i - rx) + (y * MvPolynomial.X i - ry) := by ring
            rw [heq]
            exact Ideal.add_mem K hrxK hryK
          · intro c x _ hx
            obtain ⟨rx, hrxP, hrxK⟩ := hx
            refine ⟨c • rx, Submodule.smul_mem P c hrxP, ?_⟩
            have heq : (c • x) * MvPolynomial.X i - c • rx =
                c • (x * MvPolynomial.X i - rx) := by
              rw [smul_mul_assoc, smul_sub]
            rw [heq, Algebra.smul_def]
            exact Ideal.mul_mem_left K _ hrxK
        obtain ⟨q', hq'P, hq'K⟩ := hall q hqP
        have hdiff : p * MvPolynomial.X i - q * MvPolynomial.X i ∈ K := by
          have h' := Ideal.mul_mem_left K (MvPolynomial.X i) hqK
          rwa [mul_comm (MvPolynomial.X i) (p - q), sub_mul] at h'
        refine ⟨q', hq'P, ?_⟩
        have heq : p * MvPolynomial.X i - q' =
            (p * MvPolynomial.X i - q * MvPolynomial.X i) + (q * MvPolynomial.X i - q') := by
          ring
        rw [heq]
        exact Ideal.add_mem K hdiff hq'K
    have hPFG : P.FG := by
      refine Submodule.fg_span ?_
      have hSeq : S = (fun t : σ →₀ ℕ => MvPolynomial.monomial t (1 : k)) ''
          {d : σ →₀ ℕ | d.degree < ∑ i, (N i + 1)} := by
        ext q
        exact ⟨fun ⟨d, hd, hq⟩ => ⟨d, hd, hq.symm⟩, fun ⟨d, hd, hq⟩ => ⟨d, hd, hq.symm⟩⟩
      rw [hSeq]
      exact (Finsupp.finite_of_degree_lt _).image _
    have hPfin : Module.Finite k ↥P := Module.Finite.iff_fg.mpr hPFG
    let mk : MvPolynomial σ k →ₗ[k] (MvPolynomial σ k ⧸ K) := (Ideal.Quotient.mkₐ k K).toLinearMap
    have hmk : ∀ a : MvPolynomial σ k, mk a = Ideal.Quotient.mk K a := fun a => rfl
    have hmkK : ∀ a ∈ K, mk a = 0 := by
      intro a ha
      rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    have hmksurj : Function.Surjective mk := by
      intro y
      exact ⟨Quotient.out y, by rw [hmk, Ideal.Quotient.mk_out]⟩
    have hRfin : Module.Finite k (MvPolynomial σ k ⧸ K) := by
      have hcomp : Function.Surjective (mk.comp P.subtype) := by
        intro y
        obtain ⟨a, ha⟩ := hmksurj y
        obtain ⟨pP, hpP, hpK⟩ := hspan a
        refine ⟨⟨pP, hpP⟩, ?_⟩
        have hzero : mk (a - pP) = 0 := hmkK _ hpK
        have heq : mk a = mk pP := by
          rw [show a = pP + (a - pP) by ring, map_add, hzero, add_zero]
        show mk pP = y
        rw [← ha]
        exact heq.symm
      exact Module.Finite.of_surjective (hM := hPfin) (mk.comp P.subtype) hcomp
    have hker : ∀ x : {x : σ → k // x ∈ Z ∧ ψ x = 1}, ∀ a ∈ K,
        (MvPolynomial.aeval (R := k) (x : σ → k) : MvPolynomial σ k →+* k) a = 0 := by
      intro x a ha
      rw [hK] at ha
      obtain ⟨j, hjJ, z, hzL, hsum⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := dvd_def.mp (Ideal.mem_span_singleton.mp hzL)
      rw [← hsum]
      have h1 : MvPolynomial.aeval (x : σ → k) j = 0 := by
        rw [MvPolynomial.mem_vanishingIdeal_iff] at hjJ
        exact hjJ (x : σ → k) x.2.1
      have h2 : MvPolynomial.aeval (x : σ → k) L = 1 := by
        rw [hLeval]; exact x.2.2
      change MvPolynomial.aeval (x : σ → k) (j + (L - 1) * c) = 0
      rw [map_add, map_mul, map_sub, map_one, h1, h2]
      ring
    let ff : {x : σ → k // x ∈ Z ∧ ψ x = 1} → (MvPolynomial σ k ⧸ K) →+* k := fun x =>
      Ideal.Quotient.lift K (MvPolynomial.aeval (R := k) (x : σ → k) : MvPolynomial σ k →+* k)
        (hker x)
    let Φ : {x : σ → k // x ∈ Z ∧ ψ x = 1} → Ideal (MvPolynomial σ k ⧸ K) := fun x =>
      RingHom.ker (ff x)
    have hΦmax : ∀ x, (Φ x).IsMaximal := by
      intro x
      show (RingHom.ker (ff x)).IsMaximal
      refine RingHom.ker_isMaximal_of_surjective (ff x) ?_
      intro b
      refine ⟨Ideal.Quotient.mk K (MvPolynomial.C b), ?_⟩
      exact (Ideal.Quotient.lift_mk K _ (hker x)).trans (by simp)
    have hArt : IsArtinianRing (MvPolynomial σ k ⧸ K) :=
      @IsArtinianRing.of_finite k (MvPolynomial σ k ⧸ K) _ _ _ _ _ hRfin
    have hmax : {I : Ideal (MvPolynomial σ k ⧸ K) | I.IsMaximal}.Finite :=
      @IsArtinianRing.setOf_isMaximal_finite (MvPolynomial σ k ⧸ K) _ hArt
    have hrange : (Set.range Φ).Finite := hmax.subset (Set.range_subset_iff.mpr hΦmax)
    have hinj : Function.Injective Φ := by
      intro x y hxy
      have hval : ∀ i : σ, (x : σ → k) i = (y : σ → k) i := by
        intro i
        have hsub : Ideal.Quotient.mk K (MvPolynomial.X i - MvPolynomial.C ((x : σ → k) i)) ∈
            Φ x := by
          show Ideal.Quotient.mk K (MvPolynomial.X i - MvPolynomial.C ((x : σ → k) i)) ∈
            RingHom.ker (ff x)
          rw [RingHom.mem_ker, Ideal.Quotient.lift_mk]
          simp
        rw [hxy] at hsub
        rw [RingHom.mem_ker, Ideal.Quotient.lift_mk] at hsub
        have h0 : (y : σ → k) i - (x : σ → k) i = 0 := by simpa using hsub
        exact (sub_eq_zero.mp h0).symm
      exact Subtype.ext (funext hval)
    have hfin : Finite {x : σ → k // x ∈ Z ∧ ψ x = 1} :=
      @Finite.of_injective _ (Set.range Φ) hrange.to_subtype
        (fun x => (⟨Φ x, Set.mem_range_self x⟩ : Set.range Φ))
        (fun _ _ h => hinj (Subtype.ext_iff.mp h))
    exact Set.finite_coe_iff.mp hfin
  · rw [not_nonempty_iff] at hσ
    refine Set.Subsingleton.finite fun x _ y _ => ?_
    exact funext fun i => (hσ.false i).elim
end Finite

theorem finite_setOf_mem_and_eq_one [IsAlgClosed k] [FiniteDimensional k V] {C : Set V}
    (hC : IsZariskiClosed k C) (hcone : IsCone k C) (φ : Module.Dual k V)
    (hφ : ∀ v ∈ C, φ v = 0 → v = 0) : {v | v ∈ C ∧ φ v = 1}.Finite := by
  classical
  obtain ⟨I, hI⟩ := hC.exists_eq_preimage_zeroLocus (Module.finBasis k V)
  set e : V ≃ₗ[k] (Fin (Module.finrank k V) → k) := (Module.finBasis k V).equivFun with he
  have hCI : C = e ⁻¹' MvPolynomial.zeroLocus k I := by rw [hI]
  set Z : Set (Fin (Module.finrank k V) → k) := e '' C with hZdef
  have hZ : Z = MvPolynomial.zeroLocus k I := by
    ext x
    simp only [hZdef, Set.mem_image, Set.mem_preimage, hCI]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨e.symm x, by simpa using hx, e.apply_symm_apply x⟩
  have hconeZ : ∀ (t : k) (x : Fin (Module.finrank k V) → k), x ∈ Z → t • x ∈ Z := by
    intro t x hx
    simp only [hZdef, Set.mem_image] at hx ⊢
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨t • v, hcone t v hv, map_smul e t v⟩
  have hψZ : ∀ x ∈ Z, (φ.comp e.symm.toLinearMap) x = 0 → x = 0 := by
    intro x hx hx0
    simp only [hZdef, Set.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have h1 : φ v = 0 := by simpa [LinearMap.comp_apply] using hx0
    rw [hφ v hv h1, map_zero]
  have hA : {x | x ∈ Z ∧ (φ.comp e.symm.toLinearMap) x = 1}.Finite :=
    finite_setOf_mem_zeroLocus_and_apply_eq_one I hZ hconeZ _ hψZ
  have hpre : {v | v ∈ C ∧ φ v = 1} =
      e ⁻¹' {x | x ∈ Z ∧ (φ.comp e.symm.toLinearMap) x = 1} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hv, h1⟩
      exact ⟨⟨v, hv, rfl⟩, by simpa [LinearMap.comp_apply] using h1⟩
    · rintro ⟨hxZ, h1⟩
      have hv : v ∈ C := by
        simp only [hZdef, Set.mem_image] at hxZ
        obtain ⟨w, hw, hew⟩ := hxZ
        rwa [e.injective hew] at hw
      exact ⟨hv, by simpa [LinearMap.comp_apply] using h1⟩
  rw [hpre]
  exact hA.preimage fun _ _ _ _ h => e.injective h

end CFSG.LieType.AlgebraicGroups.ClosedCone
