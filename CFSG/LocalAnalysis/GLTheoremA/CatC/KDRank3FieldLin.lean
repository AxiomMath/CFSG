module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace KDRank3FieldAux

section PSL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem dvd_exponent_of_dvd_outer_projectiveSL {K : Type} [Field K] [Finite K] {n p f : ℕ}
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (h : p ∣ Nat.card (Outer (projectiveSL n K))) : p ∣ f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hgen, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDnormR, -, -, -, -, hidx, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hDN : (linearAutGroup n K).Normal :=
    ⟨fun d hd x => by
      have := hDnormR.conj_mem ⟨d, hgen ▸ Subgroup.mem_top d⟩ (Subgroup.mem_subgroupOf.2 hd)
        ⟨x, hgen ▸ Subgroup.mem_top x⟩
      exact Subgroup.mem_subgroupOf.1 this⟩
  have hDE : linearAutGroup n K ≤ semilinearAutGroup n K := linearAutGroup_le_semilinearAutGroup
  have hE2 : ¬ p ∣ (semilinearAutGroup n K).index := by
    have h1 : (semilinearAutGroup n K).index ≤ 2 := by
      have : ((semilinearAutGroup n K).subgroupOf (standardAutGroup n K)).index ≤ 2 := hidx
      rw [hgen] at this
      change (semilinearAutGroup n K).relIndex ⊤ ≤ 2 at this
      rwa [Subgroup.relIndex_top_right] at this
    haveI : Finite (MulAut (projectiveSL n K)) :=
      Finite.of_injective (fun α : MulAut (projectiveSL n K) => (α : projectiveSL n K → _))
        fun _ _ h => MulEquiv.ext (congrFun h)
    have h0 : (semilinearAutGroup n K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    intro hd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
    have hp3 : 2 ≤ p := hp.two_le
    have : p = 2 := by omega
    exact hp2 this
  have hdiv : ¬ p ∣ Nat.gcd n (Nat.card K - 1) := fun hd =>
    not_dvd_pow_sub_one hp hf (hK ▸ hd.trans (Nat.gcd_dvd_right _ _))
  have hI : (inner (projectiveSL n K)).relIndex (linearAutGroup n K) = Nat.card
      (↥(linearAutGroup n K) ⧸ (inner (projectiveSL n K)).subgroupOf (linearAutGroup n K)) := rfl
  have hDI : ¬ p ∣ (inner (projectiveSL n K)).relIndex (linearAutGroup n K) := by
    intro hd
    rw [hI] at hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(linearAutGroup n K) ⧸
      (inner (projectiveSL n K)).subgroupOf (linearAutGroup n K)) p hd
    obtain ⟨⟨δ, hδ⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have hxp : (QuotientGroup.mk ⟨δ, hδ⟩ : ↥(linearAutGroup n K) ⧸
        (inner (projectiveSL n K)).subgroupOf (linearAutGroup n K)) ^ p = 1 := by
      rw [← hx]; exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hxp
    have hδI := CFSG.RankThree.PartOne.OutStructure.linear_D2 hp hn hdiv δ hδ 1
      (by simpa using hxp)
    have : (QuotientGroup.mk ⟨δ, hδ⟩ : ↥(linearAutGroup n K) ⧸
        (inner (projectiveSL n K)).subgroupOf (linearAutGroup n K)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hδI)
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hED : (linearAutGroup n K).relIndex (semilinearAutGroup n K) ∣ f := by
    set D := linearAutGroup n K
    set E := semilinearAutGroup n K
    haveI : (D.subgroupOf E).Normal := inferInstance
    let Φ : (K ≃+* K) →* ↥E ⧸ D.subgroupOf E :=
      (QuotientGroup.mk' (D.subgroupOf E)).comp
        ((fieldAut n K).codRestrict E fun σ => fieldAut_mem_semilinearAutGroup σ)
    have hΦ : Function.Surjective Φ := by
      intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hx
      refine ⟨σ, ?_⟩
      change QuotientGroup.mk _ = QuotientGroup.mk _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := hDN.conj_mem _ (conjAut_mem_linearAutGroup (n := n) (K := K) A) (fieldAut n K σ)⁻¹
      simpa [mul_assoc] using this
    have h1 : D.relIndex E = Nat.card (↥E ⧸ D.subgroupOf E) := rfl
    rw [h1, ← card_ringEquiv_eq hp hf hK]
    exact Subgroup.card_dvd_of_surjective hΦ
  exact dvd_of_dvd_index_chain hID hDE hp hDI hED hE2 h

end PSL

open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven Matrix

variable {K : Type} [Field K]

def twoSign (n : ℕ) (K : Type) [Field K] : Fin n → K := fun i => if i.val < 2 then -1 else 1

theorem det_diagonal_twoSign {n : ℕ} (hn : 2 ≤ n) : (diagonal (twoSign n K)).det = 1 := by
  rw [det_diagonal]
  simp only [twoSign]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Fin.card_filter_val_lt,
    min_eq_right hn]
  norm_num

theorem twoSign_mul_self {n : ℕ} (i : Fin n) : twoSign n K i * twoSign n K i = 1 := by
  simp only [twoSign]
  split_ifs <;> simp

def twoSignSL {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] : SpecialLinearGroup (Fin n) K :=
  ⟨diagonal (twoSign n K), det_diagonal_twoSign hn⟩

theorem twoSignSL_sq {n : ℕ} (hn : 2 ≤ n) : twoSignSL hn K ^ 2 = 1 := by
  rw [pow_two]
  refine Subtype.ext ?_
  change diagonal (twoSign n K) * diagonal (twoSign n K) = 1
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext twoSign_mul_self)

theorem twoSignSL_not_mem_center (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    twoSignSL (by omega) K ∉ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
  intro h
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center h (⟨0, by omega⟩ : Fin n)
  have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨2, by omega⟩ ⟨2, by omega⟩) hs
  change scalar (Fin n) (diagonal (twoSign n K) ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨2, by omega⟩
    ⟨2, by omega⟩ = diagonal (twoSign n K) ⟨2, by omega⟩ ⟨2, by omega⟩ at h4
  simp only [diagonal_apply_eq, twoSign, scalar_apply] at h4
  norm_num at h4
  apply h2
  linear_combination -h4


theorem le_localRank_PSL_of_unipotent [Finite K] {p k n : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) {W : Type} [AddCommGroup W] (hW : ∀ w : W, p • w = 0)
    (X : W →+ Matrix (Fin n) (Fin n) K) (hX : ∀ a b, X a * X b = 0)
    (hXi : Function.Injective X) (hdiag : ∀ a i, X a i i = 0)
    (hs : ∀ a (i j : Fin n), X a i j ≠ 0 → (i.val < 2 ↔ j.val < 2))
    (hcard : Nat.card W = p ^ k) :
    k ≤ localRank p (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set φ := unipotentSL X hX (fun a => det_one_add_of_mul_self_eq_zero p (hX a a))
  have hφ : Function.Injective φ :=
    unipotentSL_injective _ _ hXi
  have hcard' : Nat.card φ.range = p ^ k := by
    rw [card_range_of_injective hφ, hcard]
  refine le_localRank_quotient_of_commute _ hp (isElemAbelian_range_of_nsmul hW φ) hcard' ?_
    (twoSignSL_not_mem_center h2 hn) (by rw [twoSignSL_sq]; exact Subgroup.one_mem _) ?_
  · rw [eq_bot_iff]
    rintro x hx
    obtain ⟨⟨a, rfl⟩, hxc⟩ := Subgroup.mem_inf.mp hx
    have hs' := SpecialLinearGroup.scalar_eq_self_of_mem_center hxc (⟨0, by omega⟩ : Fin n)
    have h0 : X a.toAdd = 0 :=
      eq_zero_of_one_add_eq_scalar (fun i => hdiag _ i) (⟨0, by omega⟩ : Fin n) hs'.symm
    have ha : a = 1 := Multiplicative.toAdd.injective
      (hXi (h0.trans (map_zero _).symm))
    rw [ha, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨a, rfl⟩
    refine Subtype.ext ?_
    change (1 + X a.toAdd) * diagonal (twoSign n K) =
      diagonal (twoSign n K) * (1 + X a.toAdd)
    refine one_add_mul_diagonal_comm fun i j hij => ?_
    have := hs _ i j hij
    simp only [twoSign]
    split_ifs with h1 h2 <;> tauto


theorem le_localRank_PSL_three [Finite K] {p f n : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (hK : Nat.card K = p ^ f) :
    f ≤ localRank p (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  let i : Fin n := ⟨0, h0⟩
  let j : Fin n := ⟨1, h1⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  refine le_localRank_PSL_of_unipotent (K := K) hp2 hn (W := K) (fun w => ?_)
    (Matrix.singleAddMonoidHom i j) (fun a b => ?_) (fun a b hab => ?_) (fun a k => ?_)
    (fun a k l hkl => ?_) hK
  · rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]
  · rw [Matrix.singleAddMonoidHom_apply, Matrix.singleAddMonoidHom_apply]
    exact Matrix.single_mul_single_of_ne a i j i hij.symm b
  · have := congrFun (congrFun hab i) j
    simpa [Matrix.singleAddMonoidHom] using this
  · by_cases hk : i = k ∧ j = k
    · exact absurd (hk.1.trans hk.2.symm) hij
    · rw [Matrix.singleAddMonoidHom_apply]
      exact Matrix.single_apply_of_ne i j a k k hk
  · rw [Matrix.singleAddMonoidHom_apply] at hkl
    by_cases hk : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := hk
      simp [i, j]
    · exact absurd (Matrix.single_apply_of_ne i j a k l hk) hkl


theorem le_localRank_PSL_four [Finite K] {p f n : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hn : 4 ≤ n) (hK : Nat.card K = p ^ f) :
    2 * f ≤ localRank p (ProjectiveSpecialLinearGroup (Fin n) K) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let X : (K × K) →+ Matrix (Fin n) (Fin n) K :=
    (Matrix.singleAddMonoidHom i0 i1).comp (AddMonoidHom.fst K K) +
      (Matrix.singleAddMonoidHom i2 i3).comp (AddMonoidHom.snd K K)
  have hXapp : ∀ x : K × K, X x = Matrix.single i0 i1 x.1 + Matrix.single i2 i3 x.2 := fun x => rfl
  have e01 : (i0 ≠ i2) := by simp [i0, i2, Fin.ext_iff]
  have e03 : (i0 ≠ i3) := by simp [i0, i3, Fin.ext_iff]
  have e12 : (i1 ≠ i2) := by simp [i1, i2, Fin.ext_iff]
  have e13 : (i1 ≠ i3) := by simp [i1, i3, Fin.ext_iff]
  have e10 : (i1 ≠ i0) := by simp [i1, i0, Fin.ext_iff]
  have e32 : (i3 ≠ i2) := by simp [i3, i2, Fin.ext_iff]
  have e30 : (i3 ≠ i0) := by simp [i3, i0, Fin.ext_iff]
  have e21 : (i2 ≠ i1) := by simp [i2, i1, Fin.ext_iff]
  have e23 : (i2 ≠ i3) := by simp [i2, i3, Fin.ext_iff]
  have e01' : (i0 ≠ i1) := by simp [i0, i1, Fin.ext_iff]
  refine le_localRank_PSL_of_unipotent (K := K) hp2 (by omega) (W := K × K) (fun w => ?_) X
    (fun x y => ?_) (fun x y hxy => ?_) (fun x k => ?_) (fun x k l hkl => ?_) ?_
  · ext
    · rw [Prod.smul_fst, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]; rfl
    · rw [Prod.smul_snd, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]; rfl
  · rw [hXapp, hXapp, add_mul, mul_add, mul_add]
    rw [Matrix.single_mul_single_of_ne x.1 i0 i1 i0 e10 y.1,
      Matrix.single_mul_single_of_ne x.1 i0 i1 i2 e12 y.2,
      Matrix.single_mul_single_of_ne x.2 i2 i3 i0 e30 y.1,
      Matrix.single_mul_single_of_ne x.2 i2 i3 i2 e32 y.2]
    simp
  · have h1 := congrFun (congrFun hxy i0) i1
    have h2 := congrFun (congrFun hxy i2) i3
    rw [hXapp, hXapp] at h1 h2
    simp only [Matrix.add_apply, Matrix.single_apply_same] at h1 h2
    have n1 : ¬ (i2 = i0 ∧ i3 = i1) := fun h => e01 h.1.symm
    have n2 : ¬ (i0 = i2 ∧ i1 = i3) := fun h => e01 h.1
    rw [Matrix.single_apply_of_ne i2 i3 x.2 i0 i1 n1,
      Matrix.single_apply_of_ne i2 i3 y.2 i0 i1 n1] at h1
    rw [Matrix.single_apply_of_ne i0 i1 x.1 i2 i3 n2,
      Matrix.single_apply_of_ne i0 i1 y.1 i2 i3 n2] at h2
    exact Prod.ext (by simpa using h1) (by simpa using h2)
  · rw [hXapp, Matrix.add_apply]
    have : ¬ (i0 = k ∧ i1 = k) := fun h => e01' (h.1.trans h.2.symm)
    have : ¬ (i2 = k ∧ i3 = k) := fun h => e23 (h.1.trans h.2.symm)
    rw [Matrix.single_apply_of_ne i0 i1 x.1 k k (by assumption),
      Matrix.single_apply_of_ne i2 i3 x.2 k k (by assumption), add_zero]
  · rw [hXapp, Matrix.add_apply] at hkl
    by_cases hk1 : i0 = k ∧ i1 = l
    · obtain ⟨rfl, rfl⟩ := hk1
      simp [i0, i1]
    · by_cases hk2 : i2 = k ∧ i3 = l
      · obtain ⟨rfl, rfl⟩ := hk2
        simp [i2, i3]
      · rw [Matrix.single_apply_of_ne i0 i1 x.1 k l hk1,
          Matrix.single_apply_of_ne i2 i3 x.2 k l hk2, add_zero] at hkl
        exact absurd rfl hkl
  · rw [Nat.card_prod, hK, ← pow_add]
    ring_nf

end KDRank3FieldAux

open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven Matrix TauCeti
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open KDRank3FieldAux

theorem kdRank3Field_A (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    KDRank3FieldAt ⟨.A r q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  have hr : 1 ≤ r :=
    ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  rcases (show r = 1 ∨ 2 ≤ r by omega) with rfl | hr2
  · exact Or.inl ⟨q, rfl⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hqp : q.p = p := (LieTypeIndex.characteristic_A r q).symm.trans hchar
  subst hqp
  have hKc : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  let e1 : S ≃* ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)
  let e2 : S ≃* projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e1.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        (r + 1) _)
  have hout' : q.p ∣ Nat.card (Outer (projectiveSL (r + 1) (GaloisField q.p q.exponent))) := by
    rw [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e2).toEquiv]
    exact hout
  have hpf : q.p ∣ q.exponent :=
    dvd_exponent_of_dvd_outer_projectiveSL (by omega) q.prime_p hp2 q.exponent_pos hKc hout'
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hf3 : 3 ≤ q.exponent := hp3.trans (Nat.le_of_dvd q.exponent_pos hpf)
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · have h1 := le_gla_of_carrier e1 q.prime_p (le_localRank_PSL_three hp2 (by norm_num) hKc)
    have hf : q.exponent ≤ 3 := h1.trans hrank
    have hf' : q.exponent = 3 := le_antisymm hf hf3
    have hq3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 (hf' ▸ hpf)
    right; left
    show q.card = 27
    rw [PrimePower.card_def, hq3, hf']
    norm_num
  · exfalso
    have h1 := le_gla_of_carrier e1 q.prime_p (le_localRank_PSL_four hp2 (by omega) hKc)
    omega

end CFSG.LocalAnalysis.GLTheoremA
