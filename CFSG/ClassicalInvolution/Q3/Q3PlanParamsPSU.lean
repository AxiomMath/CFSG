module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsComp
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open CFSG.Open (IsSubnormal)
open CFSG.ClassicalInvolution.ModelFacts (negBlockK negBlockK_eq_diagonal neg_negBlockK_zero
  negBlockK_zero_eq_diagonal range_blockEmb_eq_longRootGroupSU_gen exists_su_conj_negBlock
  open_isQuasisimple_su subsingleton_su_of_le_one)
open CFSG.LieType.Universal (card_galoisField_two_mul)
open scoped MatrixGroups

section Diagonal

variable {F : Type} [Field F] {n : ℕ}

theorem eq_diagonal_of_commute_diag (h2 : (2 : F) ≠ 0) (e : Fin n → F)
    (he : ∀ p, e p = 1 ∨ e p = -1) {ν : Matrix (Fin n) (Fin n) F}
    (hD : ν * Matrix.diagonal e = Matrix.diagonal e * ν)
    (hs : ∀ i j, i ≠ j → e i = e j →
      ∃ d : Fin n → F, d i ≠ d j ∧ ν * Matrix.diagonal d = Matrix.diagonal d * ν) :
    ν = Matrix.diagonal (fun p => ν p p) := by
  have hoff : ∀ p q, p ≠ q → ν p q = 0 := by
    intro p q hpq
    by_cases hep : e p = e q
    · obtain ⟨d, hd, hνd⟩ := hs p q hpq hep
      have h := congrFun (congrFun hνd p) q
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      have h3 : ν p q * (d q - d p) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr (Ne.symm hd))
    · have h := congrFun (congrFun hD p) q
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      rcases he p with hp | hp <;> rcases he q with hq | hq
      · exact absurd (hp.trans hq.symm) hep
      · rw [hp, hq] at h
        have h3 : (2 : F) * ν p q = 0 := by linear_combination -h
        exact (mul_eq_zero.mp h3).resolve_left h2
      · rw [hp, hq] at h
        have h3 : (2 : F) * ν p q = 0 := by linear_combination h
        exact (mul_eq_zero.mp h3).resolve_left h2
      · exact absurd (hp.trans hq.symm) hep
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp
  · rw [Matrix.diagonal_apply_ne _ hpq, hoff p q hpq]

end Diagonal

section Elements

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

theorem exists_unitaryNorm_one_sq_ne_one (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    ∃ u : F, unitaryInvolution F p f u * u = 1 ∧ u * u ≠ 1 := by
  classical
  have hq1 : 1 ≤ p ^ f := by omega
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Nat.card Fˣ = (p ^ f) ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hfac : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
    zify [hq1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
    ring
  refine ⟨((g ^ (p ^ f - 1) : Fˣ) : F), ?_, ?_⟩
  · rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul, hfac, ← hord,
      pow_orderOf_eq_one, Units.val_one]
  · intro h
    have h1 : g ^ (2 * (p ^ f - 1)) = 1 := by
      rw [pow_mul', sq]
      exact Units.ext h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord, ← hfac] at h2
    have h3 : (p ^ f - 1) * (p ^ f + 1) ≤ 2 * (p ^ f - 1) :=
      Nat.le_of_dvd (by omega) h2
    have h4 : p ^ f + 1 ≤ 2 := Nat.le_of_mul_le_mul_left (by linarith) (by omega)
    omega

@[expose] def diagUV (i j : Fin n) (u : F) : Fin n → F :=
  fun k => if k = i then u else if k = j then u⁻¹ else 1

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem diagUV_left (i j : Fin n) (u : F) : diagUV i j u i = u := by simp [diagUV]

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem diagUV_right {i j : Fin n} (hij : i ≠ j) (u : F) : diagUV i j u j = u⁻¹ := by
  simp [diagUV, hij.symm]

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem diagUV_other {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (u : F) : diagUV i j u k = 1 := by
  simp [diagUV, hki, hkj]

theorem exists_su_diagUV {i j : Fin n} (hij : i ≠ j) {u : F}
    (hu : unitaryInvolution F p f u * u = 1) :
    ∃ t : Su F p f n, suMat t = Matrix.diagonal (diagUV i j u) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hdet : (Matrix.diagonal (diagUV i j u)).det = 1 := by
    rw [Matrix.det_diagonal, Fintype.prod_eq_mul i j hij (fun k hk => diagUV_other hk.1 hk.2 u),
      diagUV_left, diagUV_right hij, mul_inv_cancel₀ hu0]
  have hnorm : ∀ k, unitaryInvolution F p f (diagUV i j u k) * diagUV i j u k = 1 := by
    intro k
    by_cases hki : k = i
    · subst hki
      rw [diagUV_left]
      exact hu
    · by_cases hkj : k = j
      · subst hkj
        rw [diagUV_right hij, map_inv₀, ← mul_inv, hu, inv_one]
      · rw [diagUV_other hki hkj, map_one, one_mul]
  let A : SL(n, F) := ⟨Matrix.diagonal (diagUV i j u), hdet⟩
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL A, ⟨by simp, ?_⟩⟩, rfl⟩
  show conjTr (unitaryInvolution F p f) (Matrix.diagonal (diagUV i j u)) *
    Matrix.diagonal (diagUV i j u) = 1
  rw [CFSG.LieType.Steinberg.conjTr_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext k
  exact hnorm k

end Elements

section Std

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem mem_longRootGroupSU_of_diagUV {n : ℕ} {i j : Fin n} {u : F} {t : Su F p f n}
    (ht : suMat t = Matrix.diagonal (diagUV i j u)) (e' : Fin n → F)
    (hd : ∀ k, diagUV i j u k * (1 + e' k) = 1 + e' k) :
    t ∈ longRootGroupSU F p f (Matrix.diagonal e') := by
  refine mem_longRootGroupSU.mpr ⟨?_, ?_⟩
  · rw [ht, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  · have h1 : (1 : Matrix (Fin n) (Fin n) F) + Matrix.diagonal e' =
        Matrix.diagonal (fun k => 1 + e' k) := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]
    rw [ht, h1, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact hd k

theorem su_commute_of_isSubnormal_std (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (h2 : (2 : F) ≠ 0) {n a : ℕ} (ha : a ≤ n) {g : Su F p f n}
    (hg : suMat g = negBlockK F n 0 a) {N : Subgroup (Su F p f n)}
    (hNs : IsSubnormal N (Subgroup.centralizer ({g} : Set (Su F p f n))))
    (hsolv : Group.IsSolvable N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  set D : Matrix (Fin n) (Fin n) F := negBlockK F n 0 a with hD
  have hDc : negBlockK F n a (n - a) = -D := (neg_negBlockK_zero a).symm
  have hcomm : ∀ x : Su F p f n, x ∈ Subgroup.centralizer ({g} : Set (Su F p f n)) ↔
      suMat x * D = D * suMat x := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg suMat h
      simpa only [suMat_mul, hg] using h'
    · intro h
      apply suMat_injective
      simpa only [suMat_mul, hg] using h
  have hneg : ∀ x : Su F p f n, suMat x * (-D) = (-D) * suMat x ↔ suMat x * D = D * suMat x := by
    intro x
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  have hNC : N ≤ Subgroup.centralizer ({g} : Set (Su F p f n)) :=
    CFSG.ClassicalInvolution.isSubnormal_le hNs
  have key : ∀ (A : Subgroup (Su F p f n)) (k : ℕ) (e : Su F p f k ≃* A),
      A ≤ Subgroup.centralizer ({g} : Set (Su F p f n)) →
      (∀ c ∈ Subgroup.centralizer ({g} : Set (Su F p f n)), ∀ x ∈ A, c * x * c⁻¹ ∈ A) →
      ∀ x ∈ N, ∀ a ∈ A, x * a = a * x := by
    intro A k e hAC hAn x hx a ha
    by_cases hk : 2 ≤ k
    · have hq' : CFSG.Open.IsQuasisimple ↥A :=
        CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
          (open_isQuasisimple_su hF hq hk)
      exact commute_of_isSubnormal_of_isSolvable hq' hAC (le_normalizer_of_forall_conj_mem hAn)
        hNs hsolv x hx a ha
    · have : Subsingleton (Su F p f k) := subsingleton_su_of_le_one (by omega)
      obtain ⟨u, hu⟩ := e.surjective ⟨a, ha⟩
      have hu1 : u = 1 := Subsingleton.elim _ _
      rw [hu1, map_one] at hu
      have ha1 : a = 1 := (congrArg Subtype.val hu).symm
      rw [ha1, mul_one, one_mul]
  have h₁ : 0 + a ≤ n := by omega
  have h₂ : a + (n - a) ≤ n := by omega
  let e₁ : Su F p f a ≃* longRootGroupSU F p f (negBlockK F n 0 a) :=
    (MonoidHom.ofInjective (blockEmb_injective (K := F) (p := p) (f := f) (m := n) (k := a)
      (i := 0) h₁)).trans
      (MulEquiv.subgroupCongr (range_blockEmb_eq_longRootGroupSU_gen h2 h₁))
  let e₂ : Su F p f (n - a) ≃* longRootGroupSU F p f (negBlockK F n a (n - a)) :=
    (MonoidHom.ofInjective (blockEmb_injective (K := F) (p := p) (f := f) (m := n) (k := n - a)
      (i := a) h₂)).trans
      (MulEquiv.subgroupCongr (range_blockEmb_eq_longRootGroupSU_gen h2 h₂))
  have hL := key (longRootGroupSU F p f (negBlockK F n 0 a)) a e₁
    (fun x hx => (hcomm x).mpr hx.1)
    (fun c hc x hx => conj_mem_longRootGroupSU_of_commute ((hcomm c).mp hc) hx)
  have hC := key (longRootGroupSU F p f (negBlockK F n a (n - a))) (n - a) e₂
    (fun x hx => (hcomm x).mpr ((hneg x).mp (by rw [← hDc]; exact hx.1)))
    (fun c hc x hx => by
      rw [hDc] at hx ⊢
      exact conj_mem_longRootGroupSU_of_commute ((hneg c).mpr ((hcomm c).mp hc)) hx)
  obtain ⟨u, hu, hu2⟩ := exists_unitaryNorm_one_sq_ne_one hF hq
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hune : u ≠ u⁻¹ := by
    intro h
    apply hu2
    calc u * u = u * u⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ hu0
  have h1ne : (1 : F) ≠ -1 := fun h => h2 (by linear_combination h)
  set e : Fin n → F := fun p => if p.val < a then -1 else 1 with he_def
  have hDe : D = Matrix.diagonal e := negBlockK_zero_eq_diagonal a
  have hnegDe : -D = Matrix.diagonal (fun p => -e p) := by rw [hDe, Matrix.diagonal_neg]
  have he : ∀ p, e p = 1 ∨ e p = -1 := fun p => by
    by_cases h : p.val < a
    · exact Or.inr (by simp [e, h])
    · exact Or.inl (by simp [e, h])
  have hdiag : ∀ ν ∈ N, suMat ν = Matrix.diagonal (fun p => suMat ν p p) := by
    intro ν hν
    refine eq_diagonal_of_commute_diag h2 e he ?_ ?_
    · rw [← hDe]
      exact (hcomm ν).mp (hNC hν)
    · intro i j hij hee
      obtain ⟨t, ht⟩ := exists_su_diagUV hij hu
      refine ⟨diagUV i j u, ?_, ?_⟩
      · rw [diagUV_left, diagUV_right hij]
        exact hune
      · have hcomm' : ν * t = t * ν := by
          rcases he i with h1 | h1
          ·
            have hj1 : e j = 1 := hee ▸ h1
            have hmem : t ∈ longRootGroupSU F p f (negBlockK F n a (n - a)) := by
              rw [hDc, hnegDe]
              refine mem_longRootGroupSU_of_diagUV ht _ fun k => ?_
              rcases he k with hk | hk
              · simp [hk]
              · have hki : k ≠ i := fun h => h1ne (h1.symm.trans ((congrArg e h).symm.trans hk))
                have hkj : k ≠ j := fun h => h1ne (hj1.symm.trans ((congrArg e h).symm.trans hk))
                rw [diagUV_other hki hkj, one_mul]
            exact hC ν hν t hmem
          ·
            have hj1 : e j = -1 := hee ▸ h1
            have hmem : t ∈ longRootGroupSU F p f (negBlockK F n 0 a) := by
              rw [← hD, hDe]
              refine mem_longRootGroupSU_of_diagUV ht _ fun k => ?_
              rcases he k with hk | hk
              · have hki : k ≠ i := fun h => h1ne (hk.symm.trans ((congrArg e h).trans h1))
                have hkj : k ≠ j := fun h => h1ne (hk.symm.trans ((congrArg e h).trans hj1))
                rw [diagUV_other hki hkj, one_mul]
              · simp [hk]
            exact hL ν hν t hmem
        have := congrArg suMat hcomm'
        rwa [suMat_mul, suMat_mul, ht] at this
  intro x hx y hy
  apply suMat_injective
  rw [suMat_mul, suMat_mul, hdiag x hx, hdiag y hy, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  exact mul_comm _ _

end Std

section General

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem su_commute_of_isSubnormal (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 0 < n) {z : Su F p f n} (hz : z * z = 1)
    {N : Subgroup (Su F p f n)}
    (hNs : IsSubnormal N (Subgroup.centralizer ({z} : Set (Su F p f n))))
    (hsolv : Group.IsSolvable N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  obtain ⟨a, ha, g, hg⟩ := exists_su_conj_negBlock hF h2 hn hz
  refine commute_of_forall_map_mulEquiv (MulAut.conj g⁻¹) hNs hsolv ?_
  intro M hMs hMsolv
  refine su_commute_of_isSubnormal_std hF hq h2 ha
    (g := (MulAut.conj g⁻¹ : MulAut (Su F p f n)) z) ?_ hMs hMsolv
  rw [MulAut.conj_apply, suMat_mul, suMat_mul, inv_inv, Matrix.mul_assoc, hg, ← Matrix.mul_assoc,
    suMat_inv_mul_suMat, Matrix.one_mul]

theorem sU_commute_of_isSubnormal (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 0 < n) {w : SU (unitaryInvolution F p f) n}
    (hw : w * w = 1) {N : Subgroup (SU (unitaryInvolution F p f) n)}
    (hNs : IsSubnormal N (Subgroup.centralizer ({w} : Set (SU (unitaryInvolution F p f) n))))
    (hsolv : Group.IsSolvable N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  refine commute_of_forall_map_mulEquiv (conjEquiv P hP) hNs hsolv fun M hMs hMsolv => ?_
  refine su_commute_of_isSubnormal hF hq h2 hn ?_ hMs hMsolv
  rw [← map_mul, hw, map_one]

end General

theorem classicalMemberParameters3At_PSU : ClassicalMemberParameters3At .PSU := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  have he : 1 ≤ e := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have h5 : 5 ≤ r ^ e := five_le_pow_of_odd_prime_of_ne_three hr hr2 he hne
  have hfin : Finite (Generic.modelUniv .PSU n r e hr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have : NeZero (2 * e) := ⟨by omega⟩
  have hF : Nat.card (GaloisField r (2 * e)) = (r ^ e) ^ 2 := card_galoisField_two_mul r e he
  have h2 : (2 : GaloisField r (2 * e)) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField (2 * e) hr2
  have hM : Generic.modelUniv .PSU n r e hr =
      ⟨↥(SU (unitaryInvolution (GaloisField r (2 * e)) r e) n),
        CFSG.LieType.Universal.Unitary.rootDatum (card_galoisField_two_mul r e he) n⟩ :=
    (rfl : Generic.modelUniv .PSU n r e hr =
      CFSG.ClassicalInvolution.ModelFacts.modelUniv .PSU n r e hr).trans
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv_PSU (n := n) (p := r) (f := e) he)
  suffices hmain : ∀ M : CFSG.LieType.Universal.LieUniversal,
      M = ⟨↥(SU (unitaryInvolution (GaloisField r (2 * e)) r e) n),
        CFSG.LieType.Universal.Unitary.rootDatum (card_galoisField_two_mul r e he) n⟩ →
      ∀ ψ : M.K →* X, Function.Surjective ψ → ψ.ker ≤ Subgroup.center M.K → Finite M.K → False
    from hmain _ hM ψ hψ hker hfin
  intro M hM' ψ hψ hker hfin
  subst hM'
  refine false_of_isClassicalMember3_of_oddGenerated ψ hψ hker ?_ h
  intro w hw N _ hNs hsolv _
  exact derivedSeries_two_eq_bot_of_commute
    (sU_commute_of_isSubnormal hF h5 h2 (by omega) hw hNs hsolv)

end CFSG.ClassicalInvolution.Q3
