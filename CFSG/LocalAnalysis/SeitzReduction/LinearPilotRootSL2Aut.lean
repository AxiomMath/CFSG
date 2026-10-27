module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le_derivedSeriesOf derivedSeriesOf_succ
  le_perfectCore_of_perfect)
open scoped commutatorElement

variable {n : ℕ} {K : Type*} [Field K]

private theorem map_mulAut_eq_of_le {G : Type*} [Group G] [Finite G] (φ : MulAut G)
    {H : Subgroup G} (h : H.map φ.toMonoidHom ≤ H) : H.map φ.toMonoidHom = H :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective φ.injective])

private theorem map_mul_mulAut {G : Type*} [Group G] (φ ψ : MulAut G) (H : Subgroup G) :
    H.map (φ * ψ).toMonoidHom = (H.map ψ.toMonoidHom).map φ.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_centralizer_mulAut {G : Type*} [Group G] (φ : MulAut G) (H : Subgroup G) :
    (centralizer (H : Set G)).map φ.toMonoidHom =
      centralizer ((H.map φ.toMonoidHom : Subgroup G) : Set G) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨h, hh, rfl⟩
    change φ h * φ y = φ y * φ h
    rw [← map_mul, ← map_mul, hy h hh]
  · refine ⟨φ.symm x, fun h hh => φ.injective ?_, φ.apply_symm_apply x⟩
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact hx (φ h) ⟨h, hh, rfl⟩

private theorem commutatorElement_mul_central {G : Type*} [Group G] {p q z z' : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) : ⁅p * z, q * z'⁆ = ⁅p, q⁆ := by
  rw [Subgroup.mem_center_iff] at hz hz'
  have c1 : ∀ a b : G, z * (a * b) = a * (z * b) := fun a b => by
    rw [← mul_assoc, ← hz a, mul_assoc]
  have c2 : ∀ a b : G, z' * (a * b) = a * (z' * b) := fun a b => by
    rw [← mul_assoc, ← hz' a, mul_assoc]
  simp only [commutatorElement_def, _root_.mul_inv_rev, mul_assoc]
  rw [c1 q, c1 z', mul_inv_cancel_left, c2 p⁻¹, mul_inv_cancel_left]

theorem transpose_inv_mem_blockSpecialLinear {I : Finset (Fin n)}
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I) :
    (A⁻¹).transpose ∈ blockSpecialLinear I := by
  have hA' := (blockSpecialLinear I).inv_mem hA
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply, hA' j i hij.symm,
    Matrix.one_apply, Matrix.one_apply]
  simp only [eq_comm]

theorem map_mem_blockSpecialLinear {I : Finset (Fin n)} (σ : K →+* K)
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I) :
    Matrix.SpecialLinearGroup.map σ A ∈ blockSpecialLinear I := by
  intro i j hij
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    hA i j hij, Matrix.one_apply]
  split_ifs <;> simp

theorem slConjugation_mem_blockSpecialLinear {I : Finset (Fin n)} (D : GL (Fin n) K)
    (d : Fin n → K) (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal d)
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K D A ∈
      blockSpecialLinear I := by
  have hd : ∀ j, d j ≠ 0 := by
    intro j hj
    have h0 := Matrix.GeneralLinearGroup.det_ne_zero D
    rw [hD, det_diagonal] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hB : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K D A :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K) =
      (D : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) := by
    rw [coe_slConjugation, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  intro i j hij
  have h := congrFun (congrFun hB i) j
  rw [hD, mul_diagonal, diagonal_mul, hA i j hij] at h
  by_cases hij' : i = j
  · subst hij'
    rw [Matrix.one_apply_eq, mul_one] at h
    rw [Matrix.one_apply_eq]
    exact mul_right_cancel₀ (hd i) (h.trans (one_mul _).symm)
  · rw [Matrix.one_apply_ne hij', mul_zero] at h
    rw [Matrix.one_apply_ne hij']
    exact (mul_eq_zero.mp h).resolve_right (hd j)

@[expose] def diagAt (a : Fin n) (u : Kˣ) : GL (Fin n) K :=
  ⟨diagonal fun j => if j = a then (u : K) else 1,
    diagonal fun j => if j = a then ((u⁻¹ : Kˣ) : K) else 1, by
      simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.mul_inv, one_mul, mul_one,
        diagonal_eq_one]
      funext j; split_ifs <;> simp, by
      simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.inv_mul, one_mul, mul_one,
        diagonal_eq_one]
      funext j; split_ifs <;> simp⟩

theorem coe_diagAt (a : Fin n) (u : Kˣ) :
    (diagAt a u : Matrix (Fin n) (Fin n) K) = diagonal fun j => if j = a then (u : K) else 1 :=
  rfl

theorem det_diagAt (a : Fin n) (u : Kˣ) : Matrix.GeneralLinearGroup.det (diagAt a u) = u := by
  ext
  simp [diagAt, Matrix.GeneralLinearGroup.det]

theorem exists_toGL_mul_diagAt (a : Fin n) (A : GL (Fin n) K) :
    ∃ s : SpecialLinearGroup (Fin n) K,
      A = SpecialLinearGroup.toGL s * diagAt a (Matrix.GeneralLinearGroup.det A) := by
  have hker : A * (diagAt a (Matrix.GeneralLinearGroup.det A))⁻¹ ∈
      (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, det_diagAt, mul_inv_cancel]
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det] at hker
  obtain ⟨s, hs⟩ := hker
  exact ⟨s, by rw [hs, inv_mul_cancel_right]⟩

section Automorphisms

variable [Finite K]

theorem map_blockSL_dualAut (I : Finset (Fin n)) :
    (blockSL (K := K) I).map (dualAut n K).toMonoidHom = blockSL I := by
  refine map_mulAut_eq_of_le _ ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.mp hx
  change dualAut n K (proj n K A) ∈ blockSL I
  rw [dualAut_proj]
  exact proj_mem_blockSL (transpose_inv_mem_blockSpecialLinear hA)

theorem map_blockSL_fieldAut (I : Finset (Fin n)) (σ : K ≃+* K) :
    (blockSL (K := K) I).map (fieldAut n K σ).toMonoidHom = blockSL I := by
  refine map_mulAut_eq_of_le _ ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.mp hx
  change fieldAut n K σ (proj n K A) ∈ blockSL I
  rw [fieldAut_proj]
  exact proj_mem_blockSL (map_mem_blockSpecialLinear _ hA)

theorem map_blockSL_conjAut_diagonal (I : Finset (Fin n)) (D : GL (Fin n) K)
    (d : Fin n → K) (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal d) :
    (blockSL (K := K) I).map (conjAut n K D).toMonoidHom = blockSL I := by
  refine map_mulAut_eq_of_le _ ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.mp hx
  change conjAut n K D (proj n K A) ∈ blockSL I
  rw [conjAut_proj]
  exact proj_mem_blockSL (slConjugation_mem_blockSpecialLinear D d hD hA)

theorem exists_map_blockSL_conjAut (a : Fin n) (I : Finset (Fin n)) (A : GL (Fin n) K) :
    ∃ g : projectiveSL n K, (blockSL (K := K) I).map (conjAut n K A).toMonoidHom =
      (blockSL I).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨s, hs⟩ := exists_toGL_mul_diagAt a A
  refine ⟨proj n K s, ?_⟩
  rw [hs, map_mul, conjAut_toGL, map_mul_mulAut,
    map_blockSL_conjAut_diagonal I _ _ (coe_diagAt a _)]

theorem exists_map_blockSL_of_mulAut (hn : 3 ≤ n) (β : MulAut (projectiveSL n K))
    (I : Finset (Fin n)) :
    ∃ g : projectiveSL n K, (blockSL (K := K) I).map β.toMonoidHom =
      (blockSL I).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform β
  have hδ : (blockSL (K := K) I).map (dualAut n K ^ ε).toMonoidHom = blockSL I := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [pow_zero]
      exact Subgroup.map_id _
    · rw [pow_one]
      exact map_blockSL_dualAut I
  obtain ⟨g, hg⟩ := exists_map_blockSL_conjAut ⟨0, by omega⟩ I A
  exact ⟨g, by rw [map_mul_mulAut, map_mul_mulAut, hδ, map_blockSL_fieldAut, hg]⟩

theorem map_rootSL2_of_mulAut {m : ℕ} (hm : 3 ≤ m) (β : MulAut (projectiveSL m K))
    (a b : Fin m) :
    ∃ g : projectiveSL m K, (rootSL2 (K := K) a b).map β.toMonoidHom =
      (rootSL2 a b).map (MulAut.conj g).toMonoidHom :=
  exists_map_blockSL_of_mulAut hm β {a, b}

theorem exists_map_rootSL2_eq_conj_rootSL2 {m : ℕ} (hm : 3 ≤ m) (β : MulAut (projectiveSL m K))
    {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : projectiveSL m K, (rootSL2 (K := K) a b).map β.toMonoidHom =
      (rootSL2 c d).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := map_rootSL2_of_mulAut (K := K) hm β a b
  obtain ⟨h, hh⟩ := exists_conj_rootSL2 (K := K) c d a b hcd hab
  refine ⟨g * h, ?_⟩
  rw [hg, map_mul, map_mul_mulAut, hh]

end Automorphisms

theorem scalar_eq_one_of_conj_transvection {a b j : Fin n} (hab : a ≠ b) (hja : j ≠ a)
    (g : SpecialLinearGroup (Fin n) K) (c s : K)
    (h : (g : Matrix (Fin n) (Fin n) K) * (SpecialLinearGroup.transvection hab c :
        Matrix (Fin n) (Fin n) K) * ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) s * (SpecialLinearGroup.transvection hab c : Matrix (Fin n) (Fin n) K)) :
    s = 1 := by
  have hGGi : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hGiG := LinearFlag.coe_inv_mul_coe g
  set G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hG
  set Gi : Matrix (Fin n) (Fin n) K := ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hGi
  set E : Matrix (Fin n) (Fin n) K := single a b c with hE
  have hT : (SpecialLinearGroup.transvection hab c : Matrix (Fin n) (Fin n) K) = 1 + E :=
    SpecialLinearGroup.transvection_coe hab c
  rw [hT] at h
  have hN : scalar (Fin n) s * (1 + E) - 1 = G * E * Gi := by
    rw [← h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hGGi, add_sub_cancel_left]
  have hEE : E * E = 0 := single_mul_single_of_ne c a b a hab.symm c
  have hNN : (scalar (Fin n) s * (1 + E) - 1) * (scalar (Fin n) s * (1 + E) - 1) = 0 := by
    rw [hN]
    calc G * E * Gi * (G * E * Gi) = G * E * (Gi * G) * E * Gi := by
          simp only [Matrix.mul_assoc]
      _ = G * (E * E) * Gi := by rw [hGiG]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hEE, Matrix.mul_zero, Matrix.zero_mul]
  have hrow : ∀ k, (scalar (Fin n) s * (1 + E) - 1) j k = if j = k then s - 1 else 0 := by
    intro k
    by_cases hjk : j = k
    · subst hjk
      simp [hE, Matrix.sub_apply, Matrix.mul_add, hja.symm]
    · simp [hE, Matrix.sub_apply, Matrix.mul_add, hja.symm, hjk]
  have entry := congrFun (congrFun hNN j) j
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [hrow k]; simp [Ne.symm hk])
    (by simp), hrow j] at entry
  simp only [ite_true, Matrix.zero_apply] at entry
  exact sub_eq_zero.mp (mul_self_eq_zero.mp entry)

theorem commute_transvection_of_commute_proj {a b j : Fin n} (hab : a ≠ b) (hja : j ≠ a)
    {g : SpecialLinearGroup (Fin n) K} (c : K)
    (h : Commute (proj n K g) (proj n K (SpecialLinearGroup.transvection hab c))) :
    Commute g (SpecialLinearGroup.transvection hab c) := by
  set t := SpecialLinearGroup.transvection hab c with ht
  have hmem : g * t * g⁻¹ * t⁻¹ ∈ scalars n K := by
    rw [← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, h.eq]
    group
  obtain ⟨s, -, hs⟩ := mem_scalars.mp hmem
  have hmat : (g : Matrix (Fin n) (Fin n) K) * (t : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) (s : K) * (t : Matrix (Fin n) (Fin n) K) := by
    rw [← hs]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    rw [LinearFlag.coe_inv_mul_coe t, Matrix.mul_one]
  have hs1 : (s : K) = 1 := scalar_eq_one_of_conj_transvection hab hja g c s hmat
  have h1 : g * t * g⁻¹ * t⁻¹ = 1 := by
    apply Subtype.ext
    rw [hs, hs1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have h2 : g * t = t * g := by
    have := congrArg (· * (t * g)) h1
    simpa [mul_assoc] using this
  exact h2

private def ScalarBlock (a b : Fin n) (s : K) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j, (i = a ∨ i = b ∨ j = a ∨ j = b) → A i j = if i = j then s else 0

private theorem entries_of_commute_single {a b : Fin n} {A : Matrix (Fin n) (Fin n) K}
    (h : A * single a b 1 = single a b 1 * A) :
    (∀ i, i ≠ a → A i a = 0) ∧ A a a = A b b ∧ ∀ j, j ≠ b → A b j = 0 := by
  refine ⟨fun i hi => ?_, ?_, fun j hj => ?_⟩
  · have := congrFun (congrFun h i) b
    rwa [mul_single_apply_same, mul_one, single_mul_apply_of_ne _ _ _ _ _ hi] at this
  · have := congrFun (congrFun h a) b
    rwa [mul_single_apply_same, mul_one, single_mul_apply_same, one_mul] at this
  · have := congrFun (congrFun h a) j
    rw [mul_single_apply_of_ne _ _ _ _ _ hj, single_mul_apply_same, one_mul] at this
    exact this.symm

private theorem scalarBlock_of_commute {a b : Fin n} {A : Matrix (Fin n) (Fin n) K}
    (h₁ : A * single a b 1 = single a b 1 * A) (h₂ : A * single b a 1 = single b a 1 * A) :
    ScalarBlock a b (A a a) A := by
  obtain ⟨h1a, h1ab, h1b⟩ := entries_of_commute_single h₁
  obtain ⟨h2b, -, h2a⟩ := entries_of_commute_single h₂
  intro i j hij
  rcases hij with rfl | rfl | rfl | rfl
  · by_cases hj : i = j
    · subst hj; simp
    · rw [ite_eq_right hj, h2a j (Ne.symm hj)]
  · by_cases hj : i = j
    · subst hj; simp [h1ab]
    · rw [ite_eq_right hj, h1b j (Ne.symm hj)]
  · by_cases hi : i = j
    · subst hi; simp
    · rw [ite_eq_right hi, h1a i hi]
  · by_cases hi : i = j
    · subst hi; simp [h1ab]
    · rw [ite_eq_right hi, h2b i hi]

private theorem ScalarBlock.mul {a b : Fin n} {s t : K} {A B : Matrix (Fin n) (Fin n) K}
    (hA : ScalarBlock a b s A) (hB : ScalarBlock a b t B) :
    ScalarBlock a b (s * t) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  rcases hij with hi | hi | hj | hj
  all_goals first
    | (rw [Finset.sum_eq_single i (fun k _ hk => by
          rw [hA i k (by tauto), ite_eq_right (Ne.symm hk), zero_mul]) (by simp),
        hA i i (by tauto), ite_eq_left rfl, hB i j (by tauto)]
       split_ifs <;> simp)
    | (rw [Finset.sum_eq_single j (fun k _ hk => by
          rw [hB k j (by tauto), ite_eq_right hk, mul_zero]) (by simp),
        hB j j (by tauto), ite_eq_left rfl, hA i j (by tauto)]
       split_ifs <;> simp)

private theorem scalarBlock_of_proj_mem_centralizer (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {g : SpecialLinearGroup (Fin n) K}
    (hg : proj n K g ∈ centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K))) :
    ScalarBlock a b ((g : Matrix (Fin n) (Fin n) K) a a) (g : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨j, hja, hjb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have key : ∀ {i k : Fin n} (hik : i ≠ k), j ≠ i →
      proj n K (SpecialLinearGroup.transvection hik 1) ∈ rootSL2 (K := K) a b →
      (g : Matrix (Fin n) (Fin n) K) * single i k 1 =
        single i k 1 * (g : Matrix (Fin n) (Fin n) K) := by
    intro i k hik hji hmem
    have hc : Commute (proj n K g) (proj n K (SpecialLinearGroup.transvection hik 1)) :=
      (hg _ hmem).symm
    have h := (commute_transvection_of_commute_proj hik hji (1 : K) hc).eq
    have h' := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h'
    exact add_left_cancel h'
  exact scalarBlock_of_commute (key hab hja (proj_transvection_mem_rootSL2 hab 1))
    (key hab.symm hjb (proj_transvection_mem_rootSL2' hab 1))

theorem commutatorElement_mem_blockSpecialLinear_compl (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {g h : SpecialLinearGroup (Fin n) K}
    (hg : proj n K g ∈ centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K)))
    (hh : proj n K h ∈ centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K))) :
    ⁅g, h⁆ ∈ blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)) := by
  have hinv : ∀ {x : SpecialLinearGroup (Fin n) K},
      proj n K x ∈ centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K)) →
      proj n K x⁻¹ ∈ centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K)) := by
    intro x hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have Bg := scalarBlock_of_proj_mem_centralizer hn hab hg
  have Bh := scalarBlock_of_proj_mem_centralizer hn hab hh
  have Bgi := scalarBlock_of_proj_mem_centralizer hn hab (hinv hg)
  have Bhi := scalarBlock_of_proj_mem_centralizer hn hab (hinv hh)
  have hunit : ∀ {x : SpecialLinearGroup (Fin n) K} {s s' : K},
      ScalarBlock a b s (x : Matrix (Fin n) (Fin n) K) →
      ScalarBlock a b s' ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      s * s' = 1 := by
    intro x s s' hx hx'
    have h1 := (hx.mul hx') a a (Or.inl rfl)
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, ite_eq_left rfl] at h1
    exact h1.symm
  have hB := ((Bg.mul Bh).mul Bgi).mul Bhi
  have hsc : (g : Matrix (Fin n) (Fin n) K) a a * (h : Matrix (Fin n) (Fin n) K) a a *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a a *
      ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a a = 1 := by
    have e1 := hunit Bg Bgi
    have e2 := hunit Bh Bhi
    calc _ = ((g : Matrix (Fin n) (Fin n) K) a a *
            ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a a) *
          ((h : Matrix (Fin n) (Fin n) K) a a *
            ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a a) := by ring
      _ = 1 := by rw [e1, e2, one_mul]
  rw [hsc] at hB
  intro i j hij
  have hi : i = a ∨ i = b ∨ j = a ∨ j = b := by
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_not] at hij
    tauto
  rw [commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [hB i j hi, Matrix.one_apply]

theorem commutator_centralizer_rootSL2_le (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    ⁅centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K)),
      centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K))⁆ ≤
      blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  obtain ⟨h, rfl⟩ := proj_surjective n K y
  rw [← map_commutatorElement]
  exact proj_mem_blockSL (commutatorElement_mem_blockSpecialLinear_compl hn hab hx hy)

theorem blockSL_le_centralizer_blockSL_of_disjoint {I J : Finset (Fin n)} (hIJ : Disjoint I J) :
    blockSL (K := K) I ≤ centralizer (blockSL (K := K) J : Set (projectiveSL n K)) :=
  fun x hx y hy => (commute_blockSL_of_disjoint hIJ x hx y hy).eq.symm

private theorem commutator_specialLinearGroup_eq_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 3 ≤ Fintype.card ι) : commutator (SpecialLinearGroup ι K) = ⊤ := by
  apply le_antisymm le_top
  rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := ι)
    (K := K), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset ι) ⊆ {i, j} := fun k _ => by
      by_cases hki : k = i
      · simp [hki]
      · simp [hcon k hki]
    have h1 := Finset.card_le_card hsub
    have h2 : ({i, j} : Finset ι).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at h1
    omega
  have hword := Matrix.SpecialLinearGroup.commutatorElement_transvection hki.symm hkj hij c (1 : K)
  rw [mul_one] at hword
  rw [← hword]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem commutator_specialLinearGroup_eq_top_of_card_two [Finite K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2) (hK : 4 ≤ Nat.card K) :
    commutator (SpecialLinearGroup ι K) = ⊤ := by
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hP : Group.IsPerfect (SpecialLinearGroup ι K) :=
    Group.IsPerfect.ofSurjective
      (f := (reindexSpecialLinear (K := K) (Fintype.equivFinOfCardEq hι).symm).toMonoidHom)
      (MulEquiv.surjective _)
  exact hP.commutator_eq_top

theorem commutator_blockSpecialLinear_eq_of_three_le {I : Finset (Fin n)} (hI : 3 ≤ I.card) :
    ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear (K := K) I := by
  rw [← range_blockEmbed, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    commutator_specialLinearGroup_eq_top (by rw [Fintype.card_coe]; exact hI)]

theorem commutator_blockSpecialLinear_eq_of_card_two [Finite K] {I : Finset (Fin n)}
    (hI : I.card = 2) (hK : 4 ≤ Nat.card K) :
    ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear (K := K) I := by
  rw [← range_blockEmbed, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    commutator_specialLinearGroup_eq_top_of_card_two (by rw [Fintype.card_coe]; exact hI) hK]

theorem commutator_blockSL_eq_of_three_le {I : Finset (Fin n)} (hI : 3 ≤ I.card) :
    ⁅blockSL (K := K) I, blockSL (K := K) I⁆ = blockSL (K := K) I := by
  rw [blockSL, ← Subgroup.map_commutator, commutator_blockSpecialLinear_eq_of_three_le hI]

theorem commutator_blockSL_eq_of_card_two [Finite K] {I : Finset (Fin n)} (hI : I.card = 2)
    (hK : 4 ≤ Nat.card K) :
    ⁅blockSL (K := K) I, blockSL (K := K) I⁆ = blockSL (K := K) I := by
  rw [blockSL, ← Subgroup.map_commutator, commutator_blockSpecialLinear_eq_of_card_two hI hK]

theorem perfectCore_centralizer_rootSL2_of_perfect (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (hperf : ⁅blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)),
      blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))⁆ = blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) :
    perfectCore (centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K))) =
      blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) := by
  apply le_antisymm
  · calc perfectCore (centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K)))
        _ ≤ CFSG.Quasithin.derivedSeriesOf
            (centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K))) 1 :=
          perfectCore_le_derivedSeriesOf _ 1
        _ = ⁅centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K)),
            centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K))⁆ :=
          derivedSeriesOf_succ _ 0
        _ ≤ _ := commutator_centralizer_rootSL2_le hn hab
  · exact le_perfectCore_of_perfect
      (blockSL_le_centralizer_blockSL_of_disjoint disjoint_compl_left) hperf

theorem perfectCore_centralizer_rootSL2 (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    perfectCore (centralizer (rootSL2 (K := K) a b : Set (projectiveSL n K))) =
      blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) :=
  perfectCore_centralizer_rootSL2_of_perfect (by omega) hab (commutator_blockSL_eq_of_three_le (by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega))

theorem perfectCore_centralizer_rootSL2_four [Finite K] (hK : 4 ≤ Nat.card K) {a b : Fin 4}
    (hab : a ≠ b) :
    perfectCore (centralizer (rootSL2 (K := K) a b : Set (projectiveSL 4 K))) =
      blockSL (K := K) ({a, b}ᶜ : Finset (Fin 4)) :=
  perfectCore_centralizer_rootSL2_of_perfect (by norm_num) hab
    (commutator_blockSL_eq_of_card_two (by
      rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]) hK)

theorem perfectCore_centralizer_map_rootSL2 [Finite K] (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (φ : MulAut (projectiveSL n K)) :
    perfectCore (centralizer ((rootSL2 (K := K) a b).map φ.toMonoidHom :
        Set (projectiveSL n K))) =
      (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map φ.toMonoidHom := by
  rw [← map_centralizer_mulAut, ← CFSG.Quasithin.map_perfectCore,
    perfectCore_centralizer_rootSL2 hn hab]

theorem exists_map_blockSpecialLinear_pair_of_mulAut [Finite K] {m : ℕ} (hm : 3 ≤ m)
    (hK : 4 ≤ Nat.card K) (β : MulAut (SpecialLinearGroup (Fin m) K)) {a b : Fin m}
    (hab : a ≠ b) :
    ∃ s : SpecialLinearGroup (Fin m) K,
      (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map β.toMonoidHom =
        (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map
          (MulAut.conj s).toMonoidHom := by
  obtain ⟨g, hg⟩ := map_rootSL2_of_mulAut hm (descendAut m K β) a b
  obtain ⟨s, rfl⟩ := proj_surjective m K g
  refine ⟨s, ?_⟩
  set H := blockSpecialLinear (K := K) ({a, b} : Finset (Fin m)) with hH
  have hperf : ⁅H, H⁆ = H :=
    commutator_blockSpecialLinear_eq_of_card_two (Finset.card_pair hab) hK
  have hdecomp : ∀ x ∈ H.map β.toMonoidHom, ∃ y ∈ H.map (MulAut.conj s).toMonoidHom,
      ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin m) K), x = y * z := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : proj m K (β x) ∈ (rootSL2 (K := K) a b).map (descendAut m K β).toMonoidHom :=
      ⟨proj m K x, proj_mem_blockSL hx, descendAut_proj m K β x⟩
    rw [hg] at h1
    obtain ⟨w, hw, hweq⟩ := h1
    obtain ⟨y, hy, rfl⟩ := mem_blockSL.mp hw
    refine ⟨s * y * s⁻¹, ⟨y, hy, rfl⟩, (s * y * s⁻¹)⁻¹ * β x, ?_,
      by rw [mul_inv_cancel_left]; rfl⟩
    rw [← scalars_eq_center, ← proj_eq_one_iff, map_mul, map_inv, ← hweq]
    change (proj m K (s * y * s⁻¹))⁻¹ * (proj m K s * proj m K y * (proj m K s)⁻¹) = 1
    rw [map_mul, map_mul, map_inv, inv_mul_cancel]
  have hle : H.map β.toMonoidHom ≤ H.map (MulAut.conj s).toMonoidHom := by
    conv_lhs => rw [← hperf, Subgroup.map_commutator]
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := hdecomp u hu
    obtain ⟨y', hy', z', hz', rfl⟩ := hdecomp v hv
    rw [commutatorElement_mul_central hz hz', commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hy')
      (Subgroup.inv_mem _ hy)) (Subgroup.inv_mem _ hy')
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj s).injective,
    Subgroup.card_map_of_injective β.injective]

theorem exists_map_blockSpecialLinear_pair_eq_conj_of_mulEquiv [Finite K] {m : ℕ} (hm : 3 ≤ m)
    (hK : 4 ≤ Nat.card K) {F : Type*} [Group F] (θ₁ θ₂ : SpecialLinearGroup (Fin m) K ≃* F)
    {a b : Fin m} (hab : a ≠ b) :
    ∃ f : F, (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map θ₁.toMonoidHom =
      ((blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map θ₂.toMonoidHom).map
        (MulAut.conj f).toMonoidHom := by
  obtain ⟨s, hs⟩ := exists_map_blockSpecialLinear_pair_of_mulAut hm hK (θ₁.trans θ₂.symm) hab
  refine ⟨θ₂ s, ?_⟩
  have h1 : (blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map θ₁.toMonoidHom =
      ((blockSpecialLinear (K := K) ({a, b} : Finset (Fin m))).map
        (θ₁.trans θ₂.symm).toMonoidHom).map θ₂.toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [h1, hs, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

@[expose] noncomputable def blockSLEquivOfEquiv {I : Finset (Fin n)} (hI : I.card < n) {m : ℕ}
    (e : I ≃ Fin m) : SpecialLinearGroup (Fin m) K ≃* blockSL (K := K) I :=
  (reindexSpecialLinear e.symm).trans
    ((MonoidHom.ofInjective (proj_comp_blockEmbed_injective (K := K) hI)).trans
      (MulEquiv.subgroupCongr (blockSL_eq_range I).symm))

theorem coe_blockSLEquivOfEquiv {I : Finset (Fin n)} (hI : I.card < n) {m : ℕ}
    (e : I ≃ Fin m) (A : SpecialLinearGroup (Fin m) K) :
    ((blockSLEquivOfEquiv hI e A : blockSL (K := K) I) : projectiveSL n K) =
      proj n K (blockEmbed I (reindexSpecialLinear e.symm A)) :=
  rfl

theorem map_blockSLEquivOfEquiv_pair {I : Finset (Fin n)} (hI : I.card < n) {m : ℕ}
    (e : I ≃ Fin m) {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I) :
    ((blockSpecialLinear (K := K) ({e ⟨a, ha⟩, e ⟨b, hb⟩} : Finset (Fin m))).map
      (blockSLEquivOfEquiv hI e).toMonoidHom).map (blockSL (K := K) I).subtype =
      rootSL2 (K := K) a b := by
  have hmem : ∀ {i : Fin n} (hi : i ∈ I), i ∉ ({a, b} : Finset (Fin n)) →
      e ⟨i, hi⟩ ∉ ({e ⟨a, ha⟩, e ⟨b, hb⟩} : Finset (Fin m)) := by
    intro i hi hiab h
    apply hiab
    simp only [Finset.mem_insert, Finset.mem_singleton, e.injective.eq_iff, Subtype.mk.injEq]
      at h ⊢
    exact h
  rw [Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    change proj n K (blockEmbed I (reindexSpecialLinear e.symm A)) ∈ rootSL2 a b
    refine proj_mem_blockSL ?_
    intro i j hij
    rw [coe_blockEmbed, blockMatrix_apply]
    split_ifs with h
    · have hA' := hA (e ⟨i, h.1⟩) (e ⟨j, h.2⟩)
        (hij.imp (hmem h.1) (hmem h.2))
      change (A : Matrix (Fin m) (Fin m) K) (e ⟨i, h.1⟩) (e ⟨j, h.2⟩) = _
      rw [hA', Matrix.one_apply, Matrix.one_apply]
      simp [e.injective.eq_iff]
    · rfl
  · intro hx
    obtain ⟨B, hB, rfl⟩ := mem_blockSL.mp hx
    have hsub : ({a, b} : Finset (Fin n)) ⊆ I := by
      simp [Finset.insert_subset_iff, ha, hb]
    have hBI : B ∈ (blockEmbed (K := K) I).range := by
      rw [range_blockEmbed]
      exact blockSpecialLinear_mono hsub hB
    obtain ⟨C, rfl⟩ := hBI
    refine ⟨reindexSpecialLinear e C, ?_, ?_⟩
    · intro p q hpq
      have hback : ∀ r : Fin m, ((e.symm r : I) : Fin n) ∈ ({a, b} : Finset (Fin n)) →
          r ∈ ({e ⟨a, ha⟩, e ⟨b, hb⟩} : Finset (Fin m)) := by
        intro r h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
        rcases h with h | h
        · left
          rw [← e.apply_symm_apply r]
          exact congrArg e (Subtype.ext h)
        · right
          rw [← e.apply_symm_apply r]
          exact congrArg e (Subtype.ext h)
      have hpq' : (e.symm p : Fin n) ∉ ({a, b} : Finset (Fin n)) ∨
          (e.symm q : Fin n) ∉ ({a, b} : Finset (Fin n)) :=
        hpq.imp (fun hp h => hp (hback p h)) (fun hq h => hq (hback q h))
      have h1 := hB (e.symm p) (e.symm q) hpq'
      rw [coe_blockEmbed, blockMatrix_apply, dite_eq_left ⟨(e.symm p).2, (e.symm q).2⟩] at h1
      change (C : Matrix I I K) (e.symm p) (e.symm q) = _
      simp only [Subtype.coe_eta] at h1
      rw [h1, Matrix.one_apply, Matrix.one_apply]
      simp [Subtype.ext_iff.symm, e.symm.injective.eq_iff]
    · change proj n K (blockEmbed I (reindexSpecialLinear e.symm (reindexSpecialLinear e C))) =
        proj n K (blockEmbed I C)
      have hC : reindexSpecialLinear e.symm (reindexSpecialLinear e C) = C :=
        (reindexSpecialLinear e).symm_apply_apply C
      rw [hC]


private theorem exists_map_rootSL2_of_mulEquiv_blockSL_of_three_le [Finite K]
    (hK : 4 ≤ Nat.card K) {I I' : Finset (Fin n)} (hI : 3 ≤ I.card) (hII' : I.card = I'.card)
    (hI'n : I'.card < n)
    (ψ : blockSL (K := K) I ≃* blockSL (K := K) I') {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) :
    ∃ c ∈ I', ∃ d ∈ I', c ≠ d ∧ ∃ g ∈ blockSL (K := K) I',
      ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I)).map
          ((blockSL (K := K) I').subtype.comp ψ.toMonoidHom) =
        (rootSL2 (K := K) c d).map (MulAut.conj g).toMonoidHom := by
  have hIn : I.card < n := hII' ▸ hI'n
  set eI : I ≃ Fin I.card := I.equivFin with heI
  set eI' : I' ≃ Fin I.card := I'.equivFin.trans (finCongr hII'.symm) with heI'
  set θ := blockSLEquivOfEquiv (K := K) hIn eI with hθ
  set θ' := blockSLEquivOfEquiv (K := K) hI'n eI' with hθ'
  set a' := eI ⟨a, ha⟩ with ha'
  set b' := eI ⟨b, hb⟩ with hb'
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val (eI.injective h))
  obtain ⟨f, hf⟩ :=
    exists_map_blockSpecialLinear_pair_eq_conj_of_mulEquiv hI hK (θ.trans ψ) θ' hab'
  set c : Fin n := (eI'.symm a' : Fin n) with hcdef
  set d : Fin n := (eI'.symm b' : Fin n) with hddef
  have hc : c ∈ I' := (eI'.symm a').2
  have hd : d ∈ I' := (eI'.symm b').2
  have hcd : c ≠ d := fun h => hab' (eI'.symm.injective (Subtype.ext h))
  refine ⟨c, hc, d, hd, hcd, f, f.2, ?_⟩
  have hJ : (rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I) =
      (blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map θ.toMonoidHom := by
    apply Subgroup.map_injective (blockSL (K := K) I).subtype_injective
    rw [map_blockSLEquivOfEquiv_pair hIn eI ha hb]
    exact Subgroup.map_subgroupOf_eq_of_le (H := rootSL2 (K := K) a b) (K := blockSL (K := K) I)
      (blockSL_mono (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩))
  have hJ' : ((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
      θ'.toMonoidHom).map (blockSL (K := K) I').subtype = rootSL2 (K := K) c d := by
    have h := map_blockSLEquivOfEquiv_pair (K := K) hI'n eI' hc hd
    have h1 : eI' ⟨c, hc⟩ = a' := by
      have : (⟨c, hc⟩ : I') = eI'.symm a' := Subtype.ext rfl
      rw [this, Equiv.apply_symm_apply]
    have h2 : eI' ⟨d, hd⟩ = b' := by
      have : (⟨d, hd⟩ : I') = eI'.symm b' := Subtype.ext rfl
      rw [this, Equiv.apply_symm_apply]
    rw [h1, h2] at h
    exact h
  calc ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I)).map
          ((blockSL (K := K) I').subtype.comp ψ.toMonoidHom)
      _ = ((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
            (θ.trans ψ).toMonoidHom).map (blockSL (K := K) I').subtype := by
        rw [hJ, Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = (((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
            θ'.toMonoidHom).map (MulAut.conj f).toMonoidHom).map (blockSL (K := K) I').subtype := by
        rw [hf]
      _ = (((blockSpecialLinear (K := K) ({a', b'} : Finset (Fin I.card))).map
            θ'.toMonoidHom).map (blockSL (K := K) I').subtype).map
            (MulAut.conj (f : projectiveSL n K)).toMonoidHom := by
        simp only [Subgroup.map_map]
        congr 1
      _ = (rootSL2 (K := K) c d).map (MulAut.conj (f : projectiveSL n K)).toMonoidHom := by
        rw [hJ']


private theorem exists_map_rootSL2_of_mulEquiv_blockSL_of_card_two {I I' : Finset (Fin n)}
    (hI : I.card = 2) (hII' : I.card = I'.card)
    (ψ : blockSL (K := K) I ≃* blockSL (K := K) I') {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) :
    ∃ c ∈ I', ∃ d ∈ I', c ≠ d ∧ ∃ g ∈ blockSL (K := K) I',
      ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I)).map
          ((blockSL (K := K) I').subtype.comp ψ.toMonoidHom) =
        (rootSL2 (K := K) c d).map (MulAut.conj g).toMonoidHom := by
  have hIab : I = {a, b} := (Finset.eq_of_subset_of_card_le
    (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)
    (by rw [hI, Finset.card_pair hab])).symm
  obtain ⟨c, d, hcd, hI'cd⟩ := Finset.card_eq_two.mp (hII'.symm.trans hI)
  refine ⟨c, by simp [hI'cd], d, by simp [hI'cd], hcd, 1, Subgroup.one_mem _, ?_⟩
  have h1 : (rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I) = ⊤ := by
    rw [hIab]
    exact Subgroup.subgroupOf_self _
  rw [h1, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective ψ), ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, map_one, hI'cd]
  exact (Subgroup.map_id _).symm

theorem exists_map_rootSL2_of_mulEquiv_blockSL [Finite K] (hK : 4 ≤ Nat.card K)
    {I I' : Finset (Fin n)} (hI : 2 ≤ I.card) (hII' : I.card = I'.card) (hI'n : I'.card < n)
    (ψ : blockSL (K := K) I ≃* blockSL (K := K) I') {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) :
    ∃ c ∈ I', ∃ d ∈ I', c ≠ d ∧ ∃ g ∈ blockSL (K := K) I',
      ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I)).map
          ((blockSL (K := K) I').subtype.comp ψ.toMonoidHom) =
        (rootSL2 (K := K) c d).map (MulAut.conj g).toMonoidHom := by
  rcases hI.lt_or_eq with h3 | h2
  · exact exists_map_rootSL2_of_mulEquiv_blockSL_of_three_le hK h3 hII' hI'n ψ ha hb hab
  · exact exists_map_rootSL2_of_mulEquiv_blockSL_of_card_two h2.symm hII' ψ ha hb hab

end CFSG.SeitzReduction.LinearPilot
