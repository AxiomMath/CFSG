module

public import CFSG.RankThree.PartOne.KE.A1Fixed
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Steinberg.Adjoint Polynomial
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section PolyFrob

variable {L : Type} [Field L] {V : Type*} [AddCommGroup V] [Module L V]

theorem sum_smul_mul_sum_smul (F G : ℕ → Module.End L V) (s u : L) :
    (∑ i ∈ Finset.range 3, s ^ i • F i) * (∑ j ∈ Finset.range 3, u ^ j • G j) =
      ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, (s ^ i * u ^ j) • (F i * G j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm]

theorem eq_of_add_mul_eq {q i j i' j' : ℕ} (hi : i < q) (hi' : i' < q)
    (h : i + q * j = i' + q * j') : i = i' ∧ j = j' := by
  have hq : 0 < q := by omega
  have h1 : (i + q * j) % q = i := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have h2 : (i' + q * j') % q = i' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']
  have h3 : (i + q * j) / q = j := by
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hi, zero_add]
  have h4 : (i' + q * j') / q = j' := by
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hi', zero_add]
  exact ⟨by rw [← h1, ← h2, h], by rw [← h3, ← h4, h]⟩

theorem mul_sum_entry {ι : Type*} (M : Module.End L (ι →₀ L)) (F G : ℕ → Module.End L (ι →₀ L))
    (s u : L) (v : ι →₀ L) (a : ι) :
    (M * ((∑ i ∈ Finset.range 3, s ^ i • F i) * (∑ j ∈ Finset.range 3, u ^ j • G j))) v a =
      ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, (s ^ i * u ^ j) * (M * (F i * G j)) v a := by
  rw [sum_smul_mul_sum_smul, Finset.mul_sum, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]

theorem sum_mul_entry {ι : Type*} (M : Module.End L (ι →₀ L)) (F G : ℕ → Module.End L (ι →₀ L))
    (s u : L) (v : ι →₀ L) (a : ι) :
    (((∑ i ∈ Finset.range 3, s ^ i • F i) * (∑ j ∈ Finset.range 3, u ^ j • G j)) * M) v a =
      ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, (s ^ i * u ^ j) * ((F i * G j) * M) v a := by
  rw [sum_smul_mul_sum_smul, Finset.sum_mul, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]

theorem commute_of_frob_pair {ι : Type*} (F G : ℕ → Module.End L (ι →₀ L))
    {q : ℕ} (hq : 3 ≤ q) (z : Module.End L (ι →₀ L)) (T : Finset L)
    (hT : 2 + q * 2 < T.card)
    (hz : ∀ c ∈ T, z * ((∑ i ∈ Finset.range 3, c ^ i • F i) *
        (∑ j ∈ Finset.range 3, (c ^ q) ^ j • G j)) =
      ((∑ i ∈ Finset.range 3, c ^ i • F i) * (∑ j ∈ Finset.range 3, (c ^ q) ^ j • G j)) * z)
    {i₀ j₀ : ℕ} (hi₀ : i₀ < 3) (hj₀ : j₀ < 3) :
    z * (F i₀ * G j₀) = (F i₀ * G j₀) * z := by
  classical
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  set A : ℕ → ℕ → L := fun i j => (z * (F i * G j)) (Finsupp.single b 1) a with hA
  set B : ℕ → ℕ → L := fun i j => ((F i * G j) * z) (Finsupp.single b 1) a with hB
  set P : L[X] := ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
    C (A i j - B i j) * X ^ (i + q * j) with hP
  have hzero : ∀ c ∈ T, P.eval c = 0 := by
    intro c hc
    have h1 := congrArg (fun M : Module.End L (ι →₀ L) => M (Finsupp.single b 1) a) (hz c hc)
    rw [mul_sum_entry, sum_mul_entry] at h1
    rw [hP, eval_finsetSum]
    have h2 : ∀ i j, (C (A i j - B i j) * X ^ (i + q * j)).eval c =
        (c ^ i * (c ^ q) ^ j) * A i j - (c ^ i * (c ^ q) ^ j) * B i j := by
      intro i j
      rw [eval_mul, eval_C, eval_pow, eval_X, pow_add, pow_mul]
      ring
    simp only [eval_finsetSum, h2, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact h1
  have hdeg : P.natDegree ≤ 2 + q * 2 := by
    rw [hP]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have hi' : i ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hj' : j ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have := Nat.mul_le_mul_left q hj'
    omega
  have hP0 : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P T hzero
    (lt_of_le_of_lt hdeg hT)
  have hcoeff := congrArg (fun P : L[X] => P.coeff (i₀ + q * j₀)) hP0
  simp only [coeff_zero] at hcoeff
  rw [hP, finsetSum_coeff, Finset.sum_eq_single i₀] at hcoeff
  · rw [finsetSum_coeff, Finset.sum_eq_single j₀] at hcoeff
    · rw [coeff_C_mul_X_pow, ite_eq_left rfl, sub_eq_zero] at hcoeff
      exact hcoeff
    · intro j _ hj
      rw [coeff_C_mul_X_pow, ite_eq_right]
      intro h
      exact hj (eq_of_add_mul_eq (by omega) (by omega) h).2.symm
    · intro h
      exact absurd (Finset.mem_range.2 hj₀) h
  · intro i hi hi'
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul_X_pow, ite_eq_right]
    intro h
    exact hi' (eq_of_add_mul_eq (by omega) (by have := Finset.mem_range.1 hi; omega) h).1.symm
  · intro h
    exact absurd (Finset.mem_range.2 hi₀) h

theorem commute_of_frob_pair_units {ι : Type*} {q : ℕ} (hq : 3 ≤ q)
    (X Y : L → (Module.End L (ι →₀ L))ˣ) (Fc Gc : ℕ → Module.End L (ι →₀ L))
    (hX : ∀ t, (X t : Module.End L (ι →₀ L)) = ∑ k ∈ Finset.range 3, t ^ k • Fc k)
    (hY : ∀ t, (Y t : Module.End L (ι →₀ L)) = ∑ k ∈ Finset.range 3, t ^ k • Gc k)
    (hG0 : Gc 0 = 1) (z : (Module.End L (ι →₀ L))ˣ) (T : Finset L) (hT : 2 + q * 2 < T.card)
    (hz : ∀ c ∈ T, Commute z (X c * Y (c ^ q))) (t : L) : Commute z (X t) := by
  have hzT : ∀ c ∈ T, (z : Module.End L (ι →₀ L)) * ((∑ i ∈ Finset.range 3, c ^ i • Fc i) *
      (∑ j ∈ Finset.range 3, (c ^ q) ^ j • Gc j)) =
      ((∑ i ∈ Finset.range 3, c ^ i • Fc i) * (∑ j ∈ Finset.range 3, (c ^ q) ^ j • Gc j)) *
        (z : Module.End L (ι →₀ L)) := fun c hc => by
    have h := congrArg Units.val (hz c hc).eq
    simp only [Units.val_mul] at h
    rwa [hX, hY] at h
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hX, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h := commute_of_frob_pair Fc Gc hq (z : Module.End L (ι →₀ L)) T hT hzT
    (Finset.mem_range.1 hk) (by norm_num : 0 < 3)
  rw [hG0, mul_one] at h
  rw [mul_smul_comm, smul_mul_assoc, h]

end PolyFrob

section RigidSet

variable {τ : Tag} {L : Type} [Field L]


theorem eq_one_of_fix_of_centralizes {K : Type} [Field K] [Finite K] [Algebra K L]
    {p₀ F : ℕ} (hp₀ : p₀.Prime) (hF : 1 ≤ F) (hK : Nat.card K = p₀ ^ F) [ExpChar L p₀]
    {C : Subgroup (ModGL τ K)} {Γ : Subgroup (ModGL τ L)} (hΓC : Γ ≤ adjointGroup τ L)
    {g0 : ModGL τ L} (e : C ≃* Γ)
    (he : ∀ h : C,
      (e h : ModGL τ L) = g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * g0)
    (hnf : ∀ α : MulAut C, ∃ (y : ModGL τ K) (σ : K ≃+* K), ∀ h : C,
      (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (S : Set (ModGL τ L)) (hSΓ : S ⊆ Γ)
    (hfield : ∀ j < F, ∀ z : ModGL τ L,
      (∀ x ∈ S, x = z * Units.map (entrywiseHom (iterateFrobenius L p₀ j)) x * z⁻¹) →
      ∃ u : ModGL τ L, ∀ x ∈ Γ,
        Units.map (entrywiseHom (iterateFrobenius L p₀ j)) x = u * x * u⁻¹)
    (hcent : ∀ Z : ModGL τ L, (∀ x ∈ S, Commute Z x) → ∀ g ∈ adjointGroup τ L, Commute Z g)
    (δ : MulAut Γ) (hδ : ∀ x (hx : x ∈ S), δ ⟨x, hSΓ hx⟩ = ⟨x, hSΓ hx⟩) : δ = 1 := by
  classical
  obtain ⟨y, σ, hy⟩ := hnf ((e.trans δ).trans e.symm)
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hF hK σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : L →+* L, σ' = iterateFrobenius L p₀ j := ⟨_, rfl⟩
  have hσ'ι : ∀ c : K, σ' (algebraMap K L c) = algebraMap K L (σ.toRingHom c) := fun c => by
    rw [hσ', iterateFrobenius_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσj, map_pow]
  have hbase : ∀ g : ModGL τ K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom σ') (baseChangeGL (algebraMap K L) g) := fun g => by
    have h1 : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := RingHom.ext hσ'ι
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  obtain ⟨z, hz⟩ : ∃ z : ModGL τ L, z = g0⁻¹ * baseChangeGL (algebraMap K L) y *
      Units.map (entrywiseHom σ') g0 := ⟨_, rfl⟩
  have hδx : ∀ x : Γ, (δ x : ModGL τ L) = z * Units.map (entrywiseHom σ') x * z⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have h1 : δ (e h) = e (((e.trans δ).trans e.symm) h) := by simp
    have h2 : baseChangeGL (algebraMap K L) (h : ModGL τ K) = g0 * (e h : ModGL τ L) * g0⁻¹ := by
      rw [he]
      group
    rw [h1, he, hy, map_mul, map_mul, map_inv, hbase, h2, map_mul, map_mul, map_inv, hz]
    group
  obtain ⟨u, hu⟩ := hfield j hj z fun x hx => by
    have h1 := hδx ⟨x, hSΓ hx⟩
    rw [hδ x hx, hσ'] at h1
    exact h1
  have hu' : ∀ x ∈ Γ, Units.map (entrywiseHom σ') x = u * x * u⁻¹ := by
    rw [hσ']
    exact hu
  have hδx' : ∀ x : Γ, (δ x : ModGL τ L) = (z * u) * x * (z * u)⁻¹ := by
    intro x
    rw [hδx, hu' x x.2]
    group
  have hS : ∀ x ∈ S, Commute (z * u) x := by
    intro x hx
    have h1 := hδx' ⟨x, hSΓ hx⟩
    rw [hδ x hx] at h1
    show (z * u) * x = x * (z * u)
    calc (z * u) * x = ((z * u) * x * (z * u)⁻¹) * (z * u) := by group
      _ = x * (z * u) := by rw [← h1]
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx', MulAut.one_apply]
  have h1 : (z * u) * (x : ModGL τ L) = x * (z * u) := hcent _ hS _ (hΓC x.2)
  calc (z * u) * (x : ModGL τ L) * (z * u)⁻¹ = (x : ModGL τ L) * (z * u) * (z * u)⁻¹ := by
        rw [h1]
    _ = x := by group

end RigidSet

section CorootTest

theorem e6_pairing_bound : ∀ l ∈ Tag.E6.artifactRoots, ∀ k : Fin Tag.E6.rank,
    |∑ m : Fin Tag.E6.rank, Tag.E6.cartan k m * l.getD m 0| ≤ 2 := by
  decide +kernel

theorem abs_pairing_label_le_E6 (b : Label Tag.E6)
    (k : Fin Tag.E6.rank) : |∑ m, Tag.E6.cartan k m * b.latticeWeight m| ≤ 2 := by
  rcases b with l | ⟨β, hβ⟩
  · simp [Label.latticeWeight]
  · have hmem := isRoot_iff_mem_artifactRoots.1 hβ
    have h := e6_pairing_bound _ hmem k
    have hget : ∀ m : Fin Tag.E6.rank, (List.ofFn β).getD m 0 = β m := fun m => by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp only [hget] at h
    exact h

theorem eq_zero_of_coroot_test {ℓ f j N : ℕ} (hℓ : ℓ.Prime) (hj : j < f) (hq8 : 8 ≤ ℓ ^ f)
    (hN : ℓ ^ f ≤ N + 1) {c₁ c₂ : ℤ} (hc₁ : |c₁| ≤ 2) (hc₂ : |c₂| ≤ 2)
    (h₁ : (N : ℤ) ∣ c₁ - 2 * (ℓ ^ j : ℕ)) (h₂ : (N : ℤ) ∣ c₂ - (ℓ ^ j : ℕ)) : j = 0 := by
  by_contra hj0
  have hℓ2 := hℓ.two_le
  have hx : 2 ≤ ℓ ^ j := le_trans hℓ2 (Nat.le_self_pow hj0 ℓ)
  have hqx : 2 * ℓ ^ j ≤ ℓ ^ f := by
    have h1 : ℓ ^ f = ℓ ^ (f - j) * ℓ ^ j := by rw [← pow_add, Nat.sub_add_cancel hj.le]
    rw [h1]
    exact Nat.mul_le_mul_right _ (le_trans hℓ2 (Nat.le_self_pow (by omega) ℓ))
  set x : ℤ := ((ℓ ^ j : ℕ) : ℤ) with hxdef
  set Q : ℤ := ((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hx' : 2 ≤ x := by rw [hxdef]; exact_mod_cast hx
  have hqx' : 2 * x ≤ Q := by rw [hxdef, hQdef]; exact_mod_cast hqx
  have hN' : Q ≤ (N : ℤ) + 1 := by rw [hQdef]; exact_mod_cast hN
  have hq8' : 8 ≤ Q := by rw [hQdef]; exact_mod_cast hq8
  rw [abs_le] at hc₁ hc₂
  have e2 : c₂ - x = 0 := Int.eq_zero_of_abs_lt_dvd h₂ (by rw [abs_lt]; constructor <;> omega)
  have e1 : c₁ - 2 * x = 0 := Int.eq_zero_of_abs_lt_dvd h₁ (by rw [abs_lt]; constructor <;> omega)
  omega

end CorootTest


section Diagonal

variable {L : Type} [Field L]

theorem conjSL_diagUnitOne_HSL (s ζ : Lˣ) : conjSL (diagUnitOne s) (HSL ζ) = HSL ζ := by
  refine Subtype.ext ?_
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv, coe_HSL]
  have hs : (s : L) * (s : L)⁻¹ = 1 := mul_inv_cancel₀ s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (ζ : L) * hs

theorem sl2_map_HSL (Fr : L →+* L) (ζ : Lˣ) :
    Matrix.SpecialLinearGroup.map Fr (HSL ζ) = HSL (Units.map Fr.toMonoidHom ζ) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_HSL, coe_HSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

theorem HSL_mul_HSL (a b : Lˣ) : HSL a * HSL b = HSL (a * b) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_HSL, coe_HSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_one_eq : HSL (1 : Lˣ) = 1 := by
  refine Subtype.ext ?_
  rw [coe_HSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] noncomputable def hslHom : Lˣ →* SL2 L where
  toFun := HSL
  map_one' := HSL_one_eq
  map_mul' a b := (HSL_mul_HSL a b).symm

theorem hslHom_apply (ζ : Lˣ) : hslHom ζ = HSL ζ :=
  rfl

theorem units_map_eq_self_of_pow {Fr : L →+* L} {q : ℕ} (hq : 1 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    {ζ : Lˣ} (hζ : ζ ^ (q - 1) = 1) : Units.map Fr.toMonoidHom ζ = ζ := by
  refine Units.ext ?_
  have h1 : ((Units.map Fr.toMonoidHom ζ : Lˣ) : L) = Fr (ζ : L) := rfl
  rw [h1, hFr, ← Units.val_pow_eq_pow_val]
  have h : q = (q - 1) + 1 := by omega
  rw [h, pow_succ, hζ, one_mul]

end Diagonal

section PairGroup

variable {τ : Tag} {L : Type} [Field L]


theorem glMap_diagUnitOne' (Fr : L →+* L) (c : Lˣ) :
    (Matrix.GeneralLinearGroup.map Fr : GL (Fin 2) L →* GL (Fin 2) L) (diagUnitOne c) =
      diagUnitOne (Units.map Fr.toMonoidHom c) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, coe_diagUnitOne]


@[expose] noncomputable def pairElt (Fr : L →+* L) (β β' : Fin τ.rank → ℤ) (s : Lˣ)
    (A : SL2 L) : ModGL τ L :=
  rootSL2 τ L β A *
    rootSL2 τ L β' (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr A))

theorem pairElt_fixed (Fr : L →+* L) (m : ModGL τ L) {β β' : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) {s₁ s₂ : Lˣ}
    (h₁ : ∀ A, m * rootSL2 τ L β A * m⁻¹ = rootSL2 τ L β' (conjSL (diagUnitOne s₁) A))
    (h₂ : ∀ A, m * rootSL2 τ L β' A * m⁻¹ = rootSL2 τ L β (conjSL (diagUnitOne s₂) A))
    {A : SL2 L} (hA : conjSL (diagUnitOne (s₂ * Units.map Fr.toMonoidHom s₁))
      (Matrix.SpecialLinearGroup.map (Fr.comp Fr) A) = A) :
    m * Units.map (entrywiseHom Fr) (pairElt Fr β β' s₁ A) * m⁻¹ = pairElt Fr β β' s₁ A := by
  have hFr2 : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr A) =
      Matrix.SpecialLinearGroup.map (Fr.comp Fr) A :=
    Subtype.ext (by
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_map]
      rfl)
  rw [pairElt, map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field]
  have e : m * (rootSL2 τ L β (Matrix.SpecialLinearGroup.map Fr A) *
      rootSL2 τ L β' (Matrix.SpecialLinearGroup.map Fr (conjSL (diagUnitOne s₁)
        (Matrix.SpecialLinearGroup.map Fr A)))) * m⁻¹ =
      (m * rootSL2 τ L β (Matrix.SpecialLinearGroup.map Fr A) * m⁻¹) *
        (m * rootSL2 τ L β' (Matrix.SpecialLinearGroup.map Fr (conjSL (diagUnitOne s₁)
          (Matrix.SpecialLinearGroup.map Fr A))) * m⁻¹) := by group
  rw [e, h₁, h₂, CFSG.RankThree.QuadraticSL2.map_conjSL, glMap_diagUnitOne', hFr2,
    ← conjSL_mul, diagUnitOne_mul, hA]
  exact (hcomm _ _).symm.eq

theorem pairElt_mul (Fr : L →+* L) {β β' : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (A B : SL2 L) :
    pairElt Fr β β' s (A * B) = pairElt Fr β β' s A * pairElt Fr β β' s B := by
  simp only [pairElt, map_mul]
  have h := (hcomm B (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr A))).eq
  calc rootSL2 τ L β A * rootSL2 τ L β B *
        (rootSL2 τ L β' (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr A)) *
          rootSL2 τ L β' (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr B))) =
      rootSL2 τ L β A * (rootSL2 τ L β B *
        rootSL2 τ L β' (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr A))) *
          rootSL2 τ L β' (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr B)) := by
        group
    _ = _ := by rw [h]; group

@[expose] noncomputable def pairHom (Fr : L →+* L) (β β' : Fin τ.rank → ℤ)
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ) :
    SL2 L →* ModGL τ L where
  toFun := pairElt Fr β β' s
  map_one' := by simp [pairElt]
  map_mul' := pairElt_mul Fr hcomm s

theorem pairHom_apply (Fr : L →+* L) (β β' : Fin τ.rank → ℤ)
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (A : SL2 L) : pairHom Fr β β' hcomm s A = pairElt Fr β β' s A :=
  rfl

theorem exists_rootSL2_conjSL_eq [IsAlgClosed L] (β : Fin τ.rank → ℤ) (P : GL (Fin 2) L) :
    ∃ (j : Fin τ.rank) (g : ModGL τ L), ∀ B : SL2 L,
      rootSL2 τ L β (conjSL P B) = g * simpleRootSL2 τ L j B * g⁻¹ := by
  obtain ⟨P', hP'⟩ := exists_sl2_conjSL P
  refine ⟨(pinnedData τ β).1, pinnedWeyl τ L β * simpleRootSL2 τ L (pinnedData τ β).1 P',
    fun B => ?_⟩
  have hρ0 : ∀ B : SL2 L, rootSL2 τ L β B =
      pinnedWeyl τ L β * simpleRootSL2 τ L (pinnedData τ β).1 B * (pinnedWeyl τ L β)⁻¹ :=
    fun B => rfl
  rw [hP' B, hρ0, map_mul, map_mul, map_inv]
  group

theorem conj_xUnit_eq_sum (hdeg : entryDegreeBound τ = 2) (j : Fin τ.rank) (g : ModGL τ L)
    (s : L) :
    ((g * xUnit τ L j s * g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) =
      ∑ k ∈ Finset.range 3, s ^ k •
        ((g : Module.End L (RootModule τ L)) * xCoeff τ L j k *
          ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))) := by
  rw [Units.val_mul, Units.val_mul, coe_xUnit, xOp_eq_sum_xCoeff_entryDegreeBound, hdeg,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]

theorem conj_yUnit_eq_sum (hdeg : entryDegreeBound τ = 2) (j : Fin τ.rank) (g : ModGL τ L)
    (s : L) :
    ((g * yUnit τ L j s * g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) =
      ∑ k ∈ Finset.range 3, s ^ k •
        ((g : Module.End L (RootModule τ L)) * yCoeff τ L j k *
          ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))) := by
  rw [Units.val_mul, Units.val_mul, coe_yUnit, yOp_eq_sum_yCoeff_entryDegreeBound, hdeg,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]

theorem commute_rootRankOneGroup_of_pair [IsAlgClosed L] (hdeg : entryDegreeBound τ = 2)
    {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K₂ L] {q : ℕ} (hq : 3 ≤ q)
    (hcard : 2 + q * 2 < Nat.card K₂) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q)
    {β β' : Fin τ.rank → ℤ} (s₁ : Lˣ) (P : GL (Fin 2) L) {z : ModGL τ L}
    (hz : ∀ B : SL2 K₂, Commute z (pairElt Fr β β' s₁
      (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B)))) :
    ∀ x ∈ rootRankOneGroup τ L β, Commute z x := by
  classical
  have : Fintype K₂ := Fintype.ofFinite K₂
  obtain ⟨j, g, hρ⟩ := exists_rootSL2_conjSL_eq β P
  obtain ⟨j', g', hρ'⟩ := exists_rootSL2_conjSL_eq β'
    (diagUnitOne s₁ * Matrix.GeneralLinearGroup.map Fr P)
  set T : Finset L := Finset.univ.image (algebraMap K₂ L) with hT
  have hTcard : T.card = Nat.card K₂ := by
    rw [hT, Finset.card_image_of_injective _ (algebraMap K₂ L).injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hsecond : ∀ B : SL2 L, conjSL (diagUnitOne s₁) (Matrix.SpecialLinearGroup.map Fr
      (conjSL P B)) = conjSL (diagUnitOne s₁ * Matrix.GeneralLinearGroup.map Fr P)
        (Matrix.SpecialLinearGroup.map Fr B) := fun B => by
    rw [CFSG.RankThree.QuadraticSL2.map_conjSL, conjSL_mul]
  have hTc : 2 + q * 2 < T.card := by rw [hTcard]; exact hcard
  have hux : ∀ t : L, Commute z (g * xUnit τ L j t * g⁻¹) := by
    refine commute_of_frob_pair_units hq (fun t => g * xUnit τ L j t * g⁻¹)
      (fun t => g' * xUnit τ L j' t * g'⁻¹)
      (fun k => (g : Module.End L (RootModule τ L)) * xCoeff τ L j k *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)))
      (fun k => (g' : Module.End L (RootModule τ L)) * xCoeff τ L j' k *
        ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))) (conj_xUnit_eq_sum hdeg j g)
      (conj_xUnit_eq_sum hdeg j' g')
      (by beta_reduce; rw [xCoeff_zero, mul_one, Units.mul_inv]) z T hTc ?_
    intro c hc
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hc
    have h := hz (uSL c')
    rwa [pairElt, sl2_map_uSL, hρ, hsecond, hρ', sl2_map_uSL, simpleRootSL2_uSL,
      simpleRootSL2_uSL, hFr] at h
  have hvy : ∀ t : L, Commute z (g * yUnit τ L j t * g⁻¹) := by
    refine commute_of_frob_pair_units hq (fun t => g * yUnit τ L j t * g⁻¹)
      (fun t => g' * yUnit τ L j' t * g'⁻¹)
      (fun k => (g : Module.End L (RootModule τ L)) * yCoeff τ L j k *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)))
      (fun k => (g' : Module.End L (RootModule τ L)) * yCoeff τ L j' k *
        ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))) (conj_yUnit_eq_sum hdeg j g)
      (conj_yUnit_eq_sum hdeg j' g')
      (by beta_reduce; rw [yCoeff_zero, mul_one, Units.mul_inv]) z T hTc ?_
    intro c hc
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hc
    have h := hz (vSL c')
    rwa [pairElt, sl2_map_vSL, hρ, hsecond, hρ', sl2_map_vSL, simpleRootSL2_vSL,
      simpleRootSL2_vSL, hFr] at h
  have hall : ∀ B : SL2 L, Commute (g⁻¹ * z * g) (simpleRootSL2 τ L j B) := by
    intro B
    have hB : B ∈ Subgroup.closure (Set.range (sl2Upper L) ∪ Set.range (sl2Lower L)) := by
      rw [sl2_closure_upper_lower]
      exact Subgroup.mem_top B
    induction hB using Subgroup.closure_induction with
    | mem B hB =>
      rcases hB with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · change Commute (g⁻¹ * z * g) (simpleRootSL2 τ L j (uSL t))
        rw [simpleRootSL2_uSL]
        exact (commute_conj_iff z g _).1 (hux t)
      · change Commute (g⁻¹ * z * g) (simpleRootSL2 τ L j (vSL t))
        rw [simpleRootSL2_vSL]
        exact (commute_conj_iff z g _).1 (hvy t)
    | one => rw [map_one]; exact Commute.one_right _
    | mul B C _ _ hB hC => rw [map_mul]; exact hB.mul_right hC
    | inv B _ hB => rw [map_inv]; exact hB.inv_right
  rintro _ ⟨A, rfl⟩
  have hA : rootSL2 τ L β A = g * simpleRootSL2 τ L j (conjSL P⁻¹ A) * g⁻¹ := by
    rw [← hρ, ← conjSL_mul, mul_inv_cancel, conjSL_one]
  rw [hA]
  exact (commute_conj_iff z g _).2 (hall _)

theorem exists_pairSL2_fixed [IsAlgClosed L] {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K₂ L]
    {Fr : L →+* L} (hFr2 : ∀ c, Fr (Fr c) = c ^ Nat.card K₂) (m : ModGL τ L)
    {β β' : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s₁ s₂ : Lˣ)
    (h₁ : ∀ A, m * rootSL2 τ L β A * m⁻¹ = rootSL2 τ L β' (conjSL (diagUnitOne s₁) A))
    (h₂ : ∀ A, m * rootSL2 τ L β' A * m⁻¹ = rootSL2 τ L β (conjSL (diagUnitOne s₂) A)) :
    ∃ P : GL (Fin 2) L,
      (∀ B : SL2 K₂, m * Units.map (entrywiseHom Fr) (pairElt Fr β β' s₁
          (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B))) * m⁻¹ =
        pairElt Fr β β' s₁ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B))) ∧
      ∀ ζ : Lˣ, ζ ^ (Nat.card K₂ - 1) = 1 →
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₂ L)).range.map (conjSL P) := by
  have hFF : ∀ c, (Fr.comp Fr) c = c ^ Nat.card K₂ := fun c => hFr2 c
  obtain ⟨P, hP⟩ := exists_twist_diag (K := K₂) (Fr.comp Fr) hFF
    (s₂ * Units.map Fr.toMonoidHom s₁)
  have hfix := sl2_twistedFixed_iff (Fr.comp Fr) (frobenius_fixed_iff (Fr.comp Fr) hFF) P
  refine ⟨P, fun B => ?_, fun ζ hζ => ?_⟩
  · refine pairElt_fixed Fr m hcomm h₁ h₂ ?_
    rw [← hP]
    exact (hfix _).2 ⟨_, ⟨B, rfl⟩, rfl⟩
  · rw [← hfix, hP, sl2_map_HSL, conjSL_diagUnitOne_HSL,
      units_map_eq_self_of_pow Nat.card_pos hFF hζ]

theorem orderOf_pairElt_HSL {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (h0 : iform β' β = 0)
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (Fr : L →+* L)
    (s : Lˣ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Lˣ} (hζ : orderOf ζ = p) :
    orderOf (pairElt Fr β β' s (HSL ζ)) = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · have hζp : ζ ^ p = 1 := by
      rw [← hζ]
      exact pow_orderOf_eq_one ζ
    have h := map_pow ((pairHom Fr β β' hcomm s).comp hslHom) ζ p
    rw [hζp, map_one] at h
    exact h.symm
  · have hv := congrArg (fun g : ModGL τ L =>
      (g : Module.End L (RootModule τ L)) (rootVec τ L β)) h1
    simp only [Units.val_one, Module.End.one_apply] at hv
    rw [pairElt, Units.val_mul, Module.End.mul_apply, sl2_map_HSL, conjSL_diagUnitOne_HSL,
      rootSL2_HSL_rootVec hβ' hβ, h0, mul_zero, Int.zero_ediv, zpow_zero, Units.val_one,
      one_smul, rootSL2_HSL_rootVec hβ hβ,
      Int.mul_ediv_cancel _ (iform_self_pos hβ.ne_zero).ne'] at hv
    have h2 := eq_one_of_rootVec_eq_smul hβ hv.symm
    have h3 : ζ ^ 2 = 1 := Units.ext (by rw [Units.val_one]; exact_mod_cast h2)
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hζ] at h4
    have h5 := Nat.le_of_dvd (by norm_num) h4
    have h6 := hp.two_le
    exact hp2 (by omega)

@[expose] noncomputable def pairGroup (Fr : L →+* L) (β β' : Fin τ.rank → ℤ)
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (P : GL (Fin 2) L) (K₂ : Type) [Field K₂] [Algebra K₂ L] : Subgroup (ModGL τ L) :=
  ((Matrix.SpecialLinearGroup.map (algebraMap K₂ L)).range.map (conjSL P)).map
    (pairHom Fr β β' hcomm s)

theorem pairElt_mem_pairGroup (Fr : L →+* L) {β β' : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (P : GL (Fin 2) L) {K₂ : Type} [Field K₂] [Algebra K₂ L] {A : SL2 L}
    (hA : A ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₂ L)).range.map (conjSL P)) :
    pairElt Fr β β' s A ∈ pairGroup Fr β β' hcomm s P K₂ :=
  ⟨A, hA, rfl⟩

theorem mem_pairGroup_iff (Fr : L →+* L) {β β' : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (P : GL (Fin 2) L) {K₂ : Type} [Field K₂] [Algebra K₂ L] {x : ModGL τ L} :
    x ∈ pairGroup Fr β β' hcomm s P K₂ ↔ ∃ B : SL2 K₂,
      pairElt Fr β β' s (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B)) = x := by
  constructor
  · rintro ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩
    exact ⟨B, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩

theorem pairGroup_perfect [IsAlgClosed L] (Fr : L →+* L) {β β' : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (P : GL (Fin 2) L) {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K₂ L]
    (hK₂ : 4 ≤ Nat.card K₂) :
    ⁅pairGroup Fr β β' hcomm s P K₂, pairGroup Fr β β' hcomm s P K₂⁆ =
      pairGroup Fr β β' hcomm s P K₂ := by
  obtain ⟨-, hqs⟩ := sl2_conj_range_quasisimple (K := K₂) (L := L) hK₂ P
  rw [pairGroup, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]

theorem pairGroup_le_rootSpan (Fr : L →+* L) {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hβ' : IsRoot τ β')
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (P : GL (Fin 2) L) (K₂ : Type) [Field K₂] [Algebra K₂ L] :
    pairGroup Fr β β' hcomm s P K₂ ≤ rootSpan τ L {β, -β, β', -β'} := by
  rintro _ ⟨A, -, rfl⟩
  rw [pairHom_apply, pairElt]
  refine mul_mem ((biSup_mono ?_ : rootSpan τ L {β, -β} ≤ _) (rootSL2_mem_rootSpan_pair hβ A))
    ((biSup_mono ?_ : rootSpan τ L {β', -β'} ≤ _) (rootSL2_mem_rootSpan_pair hβ' _))
  · intro x hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro x hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem pairGroup_le_adjointGroup (Fr : L →+* L) {β β' : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s : Lˣ)
    (P : GL (Fin 2) L) (K₂ : Type) [Field K₂] [Algebra K₂ L] :
    pairGroup Fr β β' hcomm s P K₂ ≤ adjointGroup τ L := by
  rintro _ ⟨A, -, rfl⟩
  exact mul_mem (rootSL2_mem_adjointGroup _ A) (rootSL2_mem_adjointGroup _ _)

theorem commute_adjointGroup_of_simple {Z : ModGL τ L}
    (h : ∀ i : Fin τ.rank, ∀ x ∈ rootRankOneGroup τ L (Pi.single i 1), Commute Z x) :
    ∀ g ∈ adjointGroup τ L, Commute Z g := by
  have hxy : ∀ (i : Fin τ.rank) (c : L),
      Commute Z (xUnit τ L i c) ∧ Commute Z (yUnit τ L i c) := fun i c =>
    ⟨h i _ ⟨uSL c, by rw [rootSL2_single, simpleRootSL2_uSL]⟩,
      h i _ ⟨vSL c, by rw [rootSL2_single, simpleRootSL2_vSL]⟩⟩
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {Z} := by
    rw [adjointGroup, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have hgx : g = xUnit τ L i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hgx]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hxy i c).1.symm.eq
    · have hgy : g = yUnit τ L i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hgy]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hxy i c).2.symm.eq
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem exists_label_of_conj_torusElt_on (z : ModGL τ L) (ζ ζ' : Lˣ) (I : Set (Fin τ.rank))
    (hz : ∀ i ∈ I, z * torusElt τ L i ζ' * z⁻¹ = torusElt τ L i ζ) (α : Label τ) :
    ∃ b : Label τ, ∀ i ∈ I, ζ ^ (∑ j, τ.cartan i j * b.latticeWeight j) =
      ζ' ^ (∑ j, τ.cartan i j * α.latticeWeight j) := by
  obtain ⟨b, hb⟩ := exists_label_of_conj_diag z
    (fun i : I => (torusElt τ L i ζ : Module.End L _))
    (fun i : I => (torusElt τ L i ζ' : Module.End L _))
    (fun i b => ((ζ ^ (∑ j, τ.cartan i j * b.latticeWeight j) : Lˣ) : L))
    (fun i b => ((ζ' ^ (∑ j, τ.cartan i j * b.latticeWeight j) : Lˣ) : L))
    (fun i b => torusElt_single_eq (i : Fin τ.rank) ζ b)
    (fun i b => torusElt_single_eq (i : Fin τ.rank) ζ' b) (fun i => by
      have h : z * torusElt τ L i ζ' = torusElt τ L i ζ * z := by
        rw [← hz i i.2]
        group
      exact congrArg Units.val h) α
  exact ⟨b, fun i hi => Units.ext (hb ⟨i, hi⟩)⟩

end PairGroup

section BigComponent


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem subset_bigComponentSet_of_perfect (S : LangSetup τ L p) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {Y : Subgroup (ModGL τ L)} (hYΓ : Y ≤ S.Γ) (hYp : ⁅Y, Y⁆ = Y)
    (hYspan : Y ≤ rootSpan τ L {γ | ∃ j : ℕ, γ = (S.ρ : (Fin τ.rank → ℤ) → _)^[j] β ∨
      γ = (S.ρ : (Fin τ.rank → ℤ) → _)^[j] (-β)})
    {x : ModGL τ L} (hxY : x ∈ Y) (hxp : orderOf x = p) :
    (Y : Set (ModGL τ L)) ⊆ bigComponentSet S D₁ := by
  classical
  have hp := S.hp
  have := S.finite_Γ
  have hD₁Γ : D₁ ≤ S.Γ := fun x hx => (S.E_le (hD₁E hx)).2
  have : Finite D₁ := Finite.of_injective (Subgroup.inclusion hD₁Γ)
    (Subgroup.inclusion_injective hD₁Γ)
  have hD₁T : D₁ ≤ torusGroup τ L := fun x hx => (mem_twistedTorusOf.1 (S.E_le (hD₁E hx)).1).1
  have hD₁p : ∀ x ∈ D₁, x ^ p = 1 := fun x hx => S.E_exp x (hD₁E hx)
  have hcard : p < Nat.card D₁ := by
    rw [hD₁c]
    have := hp.one_lt
    nlinarith
  obtain ⟨a, haD, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite hp hD₁T hD₁p hcard β
  have hαk : β ∈ kernelRoots (rootCharHom a) := ⟨hβ, hχ⟩
  set i₀ : KernelComponent (rootCharHom a) := ⟦⟨_, hαk⟩⟧ with hi₀
  have hαi : β ∈ componentRoots (rootCharHom a) i₀ := ⟨hαk, rfl⟩
  have hnegi := (isRootComponent_componentRoots (χ := rootCharHom a) i₀).neg_mem _ hαi
  have hXspan : Y ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i₀) := by
    refine hYspan.trans (biSup_mono ?_)
    rintro γ ⟨j, rfl | rfl⟩
    · exact ⟨j, _, hαi, rfl⟩
    · exact ⟨j, _, hnegi, rfl⟩
  have hXR : Y ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i₀ := by
    rw [← hYp]
    exact Subgroup.commutator_mono (le_inf hXspan hYΓ) (le_inf hXspan hYΓ)
  have hRΓ : rationalComponent S.ρ S.Γ (rootCharHom a) i₀ ≤ S.Γ :=
    (commutator_self_le_self _).trans inf_le_right
  have : Finite (rationalComponent S.ρ S.Γ (rootCharHom a) i₀) :=
    Finite.of_injective (Subgroup.inclusion hRΓ) (Subgroup.inclusion_injective hRΓ)
  have hbig : ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i₀)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
    have h1 := orderOf_dvd_natCard (⟨_, hXR hxY⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i₀))
    rwa [Subgroup.orderOf_mk, hxp] at h1
  intro y hy
  exact ⟨a, haD, ha1, i₀, hbig, hXR hy⟩

end BigComponent

section RootMap


variable {L : Type} [Field L] [IsAlgClosed L]

theorem frobRootMap_ofFrobenius_apply {τ : Tag} {Fr : L →+* L} {q : ℕ} (hq : 0 < q)
    (hFr : ∀ c, Fr c = c ^ q) {w : WeylGroup τ} {g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap (LangDatum.ofFrobenius Fr q hFr w hg0C hg0) ρ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : ρ γ = w • γ := by
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩
  have h1 := hρ.map_rootSubgroup γ hγ
  rw [LangDatum.map_step_rootSubgroup _ hsurj rfl rfl hγ] at h1
  exact (eq_of_rootSubgroup_eq ((isRoot_smul_iff w).2 hγ) ((hρ.isRoot_iff γ).2 hγ) h1).symm

theorem frobRootMap_ofTwist_apply {t : TwistTag} {Fr : L →+* L} {q : ℕ} (hq : 0 < q)
    (hFr : ∀ c, Fr c = c ^ q) {w : WeylGroup t.tag} {g0 : ModGL t.tag L}
    (hg0C : g0 ∈ adjointGroup t.tag L)
    (hg0 : twistHom t L Fr g0 = g0 * canonicalRep (coxeterSystem t.tag) L w)
    {ρ : Equiv.Perm (Fin t.tag.rank → ℤ)}
    (hρ : FrobRootMap (LangDatum.ofTwist t Fr q hFr w hg0C hg0) ρ) {γ : Fin t.tag.rank → ℤ}
    (hγ : IsRoot t.tag γ) : ρ γ = w • permLattice t.perm γ := by
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩
  have hπγ : IsRoot t.tag (permLattice t.perm γ) := hγ.permLattice t.cartan_perm
  have h1 : (rootSubgroup t.tag L γ).map (Units.map (entrywiseHom Fr)) =
      rootSubgroup t.tag L γ := by
    rw [rootSubgroup, MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Fr c, (units_map_entrywiseHom_pinnedX Fr γ c).symm⟩
    · rintro ⟨d, rfl⟩
      obtain ⟨c, rfl⟩ := hsurj d
      exact ⟨c, units_map_entrywiseHom_pinnedX Fr γ c⟩
  obtain ⟨ε, hε, hP⟩ := diagramMap_conj_pinnedX (K := L) t hγ
  have h2 : (rootSubgroup t.tag L γ).map (MulAut.conj (diagramMap t L)).toMonoidHom =
      rootSubgroup t.tag L (permLattice t.perm γ) := by
    rw [rootSubgroup, MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨ε * c, (hP c).symm⟩
    · rintro ⟨d, rfl⟩
      refine ⟨ε * d, ?_⟩
      simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hP, ← mul_assoc, hε, one_mul]
  have hstep : (LangDatum.ofTwist t Fr q hFr w hg0C hg0).step =
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) L w)).toMonoidHom.comp
        ((MulAut.conj (diagramMap t L)).toMonoidHom.comp (Units.map (entrywiseHom Fr))) := rfl
  have h3 := hρ.map_rootSubgroup γ hγ
  rw [hstep, ← Subgroup.map_map, ← Subgroup.map_map, h1, h2,
    (canonical_weyl_root_transport t.tag L).2.1 w _ hπγ] at h3
  exact (eq_of_rootSubgroup_eq ((isRoot_smul_iff w).2 hπγ) ((hρ.isRoot_iff γ).2 hγ) h3).symm

end RootMap

end CFSG.HardMathSupport.Timmesfeld.CrossChar
