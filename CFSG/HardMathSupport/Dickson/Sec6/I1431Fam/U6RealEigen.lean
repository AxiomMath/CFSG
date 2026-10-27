module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealArith
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityBlock
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6ElemAux
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBBasic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

section Eigen

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem u6r_mem_primaryComponent_iff (B : primeFormUnitary h (idGram K n)) (d : K)
    (v : Fin n → K) :
    v ∈ primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (X - C d) ↔
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v = d • v := by
  rw [mem_primaryComponent, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
    Module.algebraMap_end_apply, sub_eq_zero]

theorem u6r_squarefree (B : primeFormUnitary h (idGram K n))
    (hB3 : (B : GL (Fin n) K) ^ 3 = 1) :
    Squarefree (minpoly K ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) := by
  have : CharP K 2 := h.charP
  have h3 : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  exact t6psuh_squarefree_minpoly_toLin_of_pow_scalar (c := 1) h3 (by rw [hB3, map_one])

theorem u6r_primaryFactor_eq (B : primeFormUnitary h (idGram K n))
    (hB3 : (B : GL (Fin n) K) ^ 3 = 1) {b : K[X]}
    (hb : b ∈ primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) :
    ∃ c : K, c ^ 3 = 1 ∧ b = X - C c := by
  obtain ⟨κ, hκ3, hκ1⟩ := u6r_exists_primitive_cube_root h
  have hx3 : ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, t6psub_toLin, ← map_pow, hB3, map_one, Units.val_one]
  have hdvd : b ∣ X ^ 3 - 1 := by
    refine (mem_primaryFactors.mp hb).2.2.trans (minpoly.dvd K _ ?_)
    rw [map_sub, map_pow, aeval_X, map_one, hx3, sub_self]
  rw [u6r_X_pow_three_sub_one hκ3 hκ1] at hdvd
  have hbi := irreducible_of_mem_primaryFactors hb
  have key : ∀ c : K, b ∣ X - C c → b = X - C c := fun c hc =>
    eq_of_monic_of_associated (monic_of_mem_primaryFactors hb) (monic_X_sub_C c)
      (hbi.associated_of_dvd (irreducible_X_sub_C c) hc)
  rcases hbi.prime.dvd_or_dvd hdvd with h12 | h3
  · rcases hbi.prime.dvd_or_dvd h12 with h1 | h2
    · exact ⟨1, one_pow 3, key 1 h1⟩
    · exact ⟨κ, hκ3, key κ h2⟩
  · exact ⟨κ ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hκ3, one_pow], key _ h3⟩

theorem u6r_mem_primaryFactors (B : primeFormUnitary h (idGram K n)) {d : K} {v : Fin n → K}
    (hv : v ∈ primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (X - C d)) (hv0 : v ≠ 0) :
    X - C d ∈ primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) := by
  rw [u6r_mem_primaryComponent_iff] at hv
  refine mem_primaryFactors.mpr ⟨irreducible_X_sub_C d, monic_X_sub_C d, ?_⟩
  rw [dvd_iff_isRoot]
  have h1 := Module.End.aeval_apply_of_mem_apply_eq_smul (p := minpoly K
    ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    hv
  rw [minpoly.aeval, LinearMap.zero_apply] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_right hv0

theorem u6r_dualPoly (h : UnitaryFieldData 2 f K) (hf : Odd f) {d : K} (hd : d ^ 3 = 1) :
    dualPoly h.bar (X - C d) = X - C d := by
  have h1 := u6r_bar_mul_self h hf hd
  rw [KCUnitaryBlock.dualPoly_X_sub_C (left_ne_zero_of_mul_eq_one h1),
    inv_eq_of_mul_eq_one_right h1]

theorem u6r_apply_mem_primaryComponent (B D : primeFormUnitary h (idGram K n)) {κ : Kˣ}
    (hDB : (D : GL (Fin n) K) * B * (D : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) κ * B) {d : K} {v : Fin n → K}
    (hv : v ∈ primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (X - C d)) :
    ((t6psub_toLin D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v ∈
      primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (X - C (((κ⁻¹ : Kˣ) : K) * d)) := by
  rw [u6r_mem_primaryComponent_iff] at hv ⊢
  have hDB' : (D : GL (Fin n) K) * B = Matrix.GeneralLinearGroup.scalar (Fin n) κ * B * D :=
    mul_inv_eq_iff_eq_mul.mp hDB
  have hBD : (B : GL (Fin n) K) * D =
      Matrix.GeneralLinearGroup.scalar (Fin n) κ⁻¹ * ((D : GL (Fin n) K) * B) := by
    rw [hDB', map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 : ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K))
        (((t6psub_toLin D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) v) =
      ((κ⁻¹ : Kˣ) : K) • ((t6psub_toLin D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K))
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) v) := by
    have := congrArg (fun g : GL (Fin n) K =>
      ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v) hBD
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, t6psub_glA_scalar_apply] at this
    exact this
  rw [h1, hv, map_smul, smul_smul]

theorem u6r_finrank_le (B D : primeFormUnitary h (idGram K n)) {κ : Kˣ}
    (hDB : (D : GL (Fin n) K) * B * (D : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) κ * B) (c : K) :
    Module.finrank K (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) (X - C c)) ≤
    Module.finrank K (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) (X - C (((κ⁻¹ : Kˣ) : K) * c))) := by
  have hinj := t6psub_injective_of_glUnit (t6psub_toLin D)
  have hle : (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) (X - C c)).map
        ((t6psub_toLin D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) ≤
      primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K
        (Fin n → K)) : Module.End K (Fin n → K)) (X - C (((κ⁻¹ : Kˣ) : K) * c)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact u6r_apply_mem_primaryComponent B D hDB hv
  exact ((Submodule.equivMapOfInjective _ hinj _).finrank_eq).trans_le
    (Submodule.finrank_mono hle)

theorem u6r_pow_three_eq_one_of_twist [NeZero n] (B D : primeFormUnitary h (idGram K n))
    (hB3 : (B : GL (Fin n) K) ^ 3 = 1) {κ : Kˣ}
    (hDB : (D : GL (Fin n) K) * B * (D : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) κ * B) : κ ^ 3 = 1 := by
  have h1 : (Matrix.GeneralLinearGroup.scalar (Fin n) κ * B) ^ 3 = 1 := by
    rw [← hDB, conj_pow, hB3, mul_one, mul_inv_cancel]
  rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar κ (B : GL (Fin n) K)).symm.mul_pow, hB3,
    mul_one, ← map_pow] at h1
  have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) 0 0) h1
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_one,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
  exact Units.ext h2

theorem u6r_finrank_eq_two (B D : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1) {κ : Kˣ} (hκ1 : κ ≠ 1)
    (hDB : (D : GL (Fin 6) K) * B * (D : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B) {d : K} (hd : d ^ 3 = 1) :
    Module.finrank K (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K
      (Fin 6 → K)) : Module.End K (Fin 6 → K)) (X - C d)) = 2 := by
  classical
  have hκ3 := u6r_pow_three_eq_one_of_twist B D hB3 hDB
  have hkinv : ((κ⁻¹ : Kˣ) : K) = (κ : K) ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right ((pow_succ' κ 2).symm.trans hκ3), Units.val_pow_eq_pow_val]
  have hk3 : (κ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hκ3, Units.val_one]
  have hk1 : (κ : K) ≠ 1 := fun h1 => hκ1 (Units.ext h1)
  obtain ⟨m, hm⟩ : ∃ m : K → ℕ, ∀ c, Module.finrank K (primaryComponent
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C c)) = m c := ⟨_, fun _ => rfl⟩
  have hmono : ∀ c, m c ≤ m ((κ : K) ^ 2 * c) := fun c => by
    have := u6r_finrank_le B D hDB c
    rwa [hm, hm, hkinv] at this
  rw [hm]
  generalize (κ : K) = k at hk3 hk1 hmono
  have hcyc : ∀ c, m c = m (k ^ 2 * c) := fun c => by
    refine le_antisymm (hmono c) ?_
    have h6 : k ^ 2 * (k ^ 2 * (k ^ 2 * c)) = c := by linear_combination (k ^ 3 + 1) * c * hk3
    calc m (k ^ 2 * c) ≤ m (k ^ 2 * (k ^ 2 * c)) := hmono _
      _ ≤ m (k ^ 2 * (k ^ 2 * (k ^ 2 * c))) := hmono _
      _ = m c := by rw [h6]
  have hm2 : m (k ^ 2) = m 1 := by
    have := hcyc 1
    rw [mul_one] at this
    exact this.symm
  have hmk : m k = m 1 := by
    have := hcyc (k ^ 2)
    have h4 : k ^ 2 * k ^ 2 = k := by linear_combination k * hk3
    rw [h4] at this
    rw [← hm2, this]
  have hk2 : k ^ 2 ≠ 1 := fun h2 => hk1 (by linear_combination hk3 - k * h2)
  have hkk : k ^ 2 ≠ k := fun h2 => hk1 (by linear_combination hk3 - (k + 1) * h2)
  have hXC : ∀ a a' : K, a ≠ a' → (X - C a : K[X]) ≠ X - C a' := fun a a' haa' h =>
    haa' (C_injective (sub_right_injective h))
  have hsq := u6r_squarefree B hB3
  have hsub : primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) ⊆ {X - C 1, X - C k, X - C (k ^ 2)} := by
    intro b hb
    obtain ⟨c, hc3, rfl⟩ := u6r_primaryFactor_eq B hB3 hb
    rcases u6r_cube_root_cases hk3 hk1 hc3 with rfl | rfl | rfl <;> simp
  have hzero : ∀ a ∈ ({X - C 1, X - C k, X - C (k ^ 2)} : Finset K[X]),
      a ∉ primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) →
      Module.finrank K (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K
        (Fin 6 → K)) : Module.End K (Fin 6 → K)) a) = 0 := by
    intro a ha hna
    obtain ⟨c, rfl⟩ : ∃ c, a = X - C c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    exact hna (u6r_mem_primaryFactors B hv hv0)
  have h6 := (finrank_eq_sum_primaryComponent hsq).trans (Finset.sum_coe_sort _
    (fun a => Module.finrank K (primaryComponent ((t6psub_toLin B :
      LinearMap.GeneralLinearGroup K (Fin 6 → K)) : Module.End K (Fin 6 → K)) a)))
  rw [Finset.sum_subset hsub hzero, Finset.sum_insert, Finset.sum_pair (hXC _ _ (Ne.symm hkk)),
    Module.finrank_fin_fun, hm, hm, hm, hm2, hmk] at h6
  · rcases u6r_cube_root_cases hk3 hk1 hd with rfl | rfl | rfl <;> omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hXC _ _ (Ne.symm hk1), hXC _ _ (Ne.symm hk2)⟩

theorem u6r_mem_primaryFactors_of_cycle (B D : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1) {κ : Kˣ} (hκ1 : κ ≠ 1)
    (hDB : (D : GL (Fin 6) K) * B * (D : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B) {d : K} (hd : d ^ 3 = 1) :
    X - C d ∈ primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) := by
  have h2 := u6r_finrank_eq_two B D hB3 hκ1 hDB hd
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp (by rw [h2]; norm_num))
  exact u6r_mem_primaryFactors B hv hv0

theorem u6r_multiplicity_eq_two (B D : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1) {κ : Kˣ} (hκ1 : κ ≠ 1)
    (hDB : (D : GL (Fin 6) K) * B * (D : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B) {d : K} (hd : d ^ 3 = 1) :
    primaryMultiplicity ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) (X - C d) = 2 := by
  have h2 := u6r_finrank_eq_two B D hB3 hκ1 hDB hd
  have : Fact (Irreducible (X - C d)) := ⟨irreducible_X_sub_C d⟩
  rw [finrank_primaryComponent, natDegree_X_sub_C, one_mul] at h2
  exact h2

theorem u6r_isGoodBlock (hf4 : 4 ≤ 2 ^ f) (B D : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1) {κ : Kˣ} (hκ1 : κ ≠ 1)
    (hDB : (D : GL (Fin 6) K) * B * (D : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B) {d : K} (hd : d ^ 3 = 1) :
    IsGoodBlock h (t6psub_toLin B)
      ⟨X - C d, u6r_mem_primaryFactors_of_cycle B D hB3 hκ1 hDB hd⟩ := by
  have hm := u6r_multiplicity_eq_two B D hB3 hκ1 hDB hd
  refine ⟨hm.ge, fun _ => ?_⟩
  change (primaryMultiplicity ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) (X - C d), 2 ^ (f * (X - C d : K[X]).natDegree)) ∉ _
  rw [hm, natDegree_X_sub_C, mul_one]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
  omega

theorem u6r_conj_apply (D : primeFormUnitary h (idGram K n)) (g : gramSU h (idGram K n))
    (v : Fin n → K) :
    ((t6psuh_toLinSU h n (t6psub_actSU h n D g) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K))
      (((t6psub_toLin D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v) =
    ((t6psub_toLin D : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
      (((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v) := by
  have hc : (D : GL (Fin n) K) * g * (D : GL (Fin n) K)⁻¹ * D = D * g := by group
  have h2 := congrArg (fun y : GL (Fin n) K =>
    ((Matrix.GeneralLinearGroup.toLin y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v) hc
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h2
  rw [t6psuh_toLinSU_apply, t6psub_actSU_coe, t6psuh_toLinSU_apply, t6psub_toLin]
  simp only [map_mul, Units.val_mul, Module.End.mul_apply]
  exact h2

theorem u6r_supp (hf : Odd f) (B D : primeFormUnitary h (idGram K n))
    (hB3 : (B : GL (Fin n) K) ^ 3 = 1) {κ : Kˣ}
    (hDB : (D : GL (Fin n) K) * B * (D : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) κ * B) {d e : K} (hd : d ^ 3 = 1) (he : e ^ 3 = 1)
    (hne : e ≠ ((κ⁻¹ : Kˣ) : K) * d) {g : gramSU h (idGram K n)}
    (hg : g ∈ (specialBlock (idForm h n) (t6psub_toLin B) (X - C d)).comap (t6psuh_toLinSU h n))
    (hDg : t6psub_actSU h n D g ∈
      (specialBlock (idForm h n) (t6psub_toLin B) (X - C e)).comap (t6psuh_toLinSU h n)) :
    g = 1 := by
  have hg' := (specialBlock_le_orbitFactor (Subgroup.mem_comap.mp hg)).2
  have hDg' := (specialBlock_le_orbitFactor (Subgroup.mem_comap.mp hDg)).2
  rw [u6r_dualPoly h hf hd] at hg'
  rw [u6r_dualPoly h hf he] at hDg'
  have hinjD := t6psub_injective_of_glUnit (t6psub_toLin D)
  have hXC : ∀ a a' : K, a ≠ a' → (X - C a : K[X]) ∉ ({X - C a', X - C a'} : Set K[X]) := by
    intro a a' haa' hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at hmem
    exact haa' (C_injective (sub_right_injective hmem))
  apply t6psuh_toLinSU_injective (h := h) (n := n)
  rw [map_one]
  refine eq_one_of_forall_apply_eq (u6r_squarefree B hB3) fun b hb v hv => ?_
  obtain ⟨c, -, rfl⟩ := u6r_primaryFactor_eq B hB3 hb
  by_cases hcd : c = d
  · subst hcd
    have hw := u6r_apply_mem_primaryComponent B D hDB hv
    by_cases hw0 : ((t6psub_toLin D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v = 0
    · have hv0 : v = 0 := hinjD (hw0.trans (map_zero _).symm)
      rw [hv0, map_zero]
    · have h1 := hDg' _ (u6r_mem_primaryFactors B hw hw0) (hXC _ _ (Ne.symm hne)) _ hw
      exact hinjD ((u6r_conj_apply D g v).symm.trans h1)
  · exact hg' _ hb (hXC _ _ hcd) v hv


noncomputable local instance decEqU6rK : DecidableEq K := Classical.decEq K

theorem u6r_complement_of_cubic_scalar_commutator
    (hf : Odd f)
    (B g₁ g₂ : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1)
    (κ : Kˣ) (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1)
    (h12 : (g₁ : GL (Fin 6) K) * (g₂ : GL (Fin 6) K) *
        (g₁ : GL (Fin 6) K)⁻¹ * (g₂ : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (h13 : (g₁ : GL (Fin 6) K) * (B : GL (Fin 6) K) =
      (B : GL (Fin 6) K) * (g₁ : GL (Fin 6) K))
    (h23 : (g₂ : GL (Fin 6) K) * (B : GL (Fin 6) K) =
      (B : GL (Fin 6) K) * (g₂ : GL (Fin 6) K))
    (c : K) (hc3 : c ^ 3 = 1)
    (hWc : Module.finrank K (primaryComponent
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C c)) = 3) :
    ∃ d : K, d ^ 3 = 1 ∧ d ≠ c ∧
      primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) = {X - C c, X - C d} ∧
      Module.finrank K (primaryComponent
        ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C d)) = 3 ∧
      IsCompl
        (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C c))
        (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C d)) ∧
      (∀ v ∈ primaryComponent
          ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K)) (X - C c),
        ∀ w ∈ primaryComponent
          ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K)) (X - C d),
        idForm h 6 v w = 0) ∧
      ((idForm h 6).domRestrict₁₂
        (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C c))
        (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C c))).SeparatingLeft ∧
      ((idForm h 6).domRestrict₁₂
        (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C d))
        (primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C d))).SeparatingLeft ∧
      primaryProjection ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C c) +
      primaryProjection ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C d) = 1 ∧
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) =
      c • primaryProjection ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C c) +
      d • primaryProjection ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C d) := by
  classical
  let x : Module.End K (Fin 6 → K) :=
    ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K))
  have hsq : Squarefree (minpoly K x) := by
    change Squarefree (minpoly K ((t6psub_toLin B :
      LinearMap.GeneralLinearGroup K (Fin 6 → K)) : Module.End K (Fin 6 → K)))
    exact u6r_squarefree B hB3
  have hfin (a : K) : Module.finrank K (primaryComponent x (X - C a)) =
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.eigenDim
        ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a := by
    have hker : primaryComponent x (X - C a) =
        LinearMap.ker (Matrix.toLin'
          ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) -
          a • (LinearMap.id : (Fin 6 → K) →ₗ[K] (Fin 6 → K))) := by
      ext v
      change v ∈ primaryComponent
        ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C a) ↔ _
      rw [u6r_mem_primaryComponent_iff, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      rfl
    rw [hker]
    rfl
  have hWc' : Module.finrank K (primaryComponent x (X - C c)) = 3 := by
    change Module.finrank K (primaryComponent
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C c)) = 3
    exact hWc
  have hdiv : ∀ a ∈ primaryFactors x, 3 ∣ Module.finrank K (primaryComponent x a) := by
    intro a ha
    obtain ⟨e, -, rfl⟩ := u6r_primaryFactor_eq B hB3 ha
    rw [hfin e]
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.three_dvd_eigenDim
      (g₁ : GL (Fin 6) K) (g₂ : GL (Fin 6) K) (B : GL (Fin 6) K)
      κ hκ3 hκ1 h12 h13 h23 e
  have hpos : ∀ a ∈ primaryFactors x, 0 < Module.finrank K (primaryComponent x a) := by
    intro a ha
    refine Nat.pos_of_ne_zero fun h0 => ?_
    exact primaryComponent_ne_bot hsq ha (Submodule.finrank_eq_zero.mp h0)
  have hcF : X - C c ∈ primaryFactors x := by
    have hne : primaryComponent x (X - C c) ≠ ⊥ := by
      intro hbot
      have h0 : Module.finrank K (primaryComponent x (X - C c)) = 0 := by
        rw [hbot, finrank_bot]
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact u6r_mem_primaryFactors B hv hv0
  have hsum : ∑ a ∈ primaryFactors x, Module.finrank K (primaryComponent x a) = 6 := by
    rw [← Finset.sum_coe_sort (primaryFactors x)
      (fun a => Module.finrank K (primaryComponent x a))]
    rw [← finrank_eq_sum_primaryComponent hsq]
    exact Module.finrank_fin_fun K
  have hsum_erase : ∑ a ∈ (primaryFactors x).erase (X - C c),
      Module.finrank K (primaryComponent x a) = 3 := by
    have h := hsum
    rw [← Finset.insert_erase hcF,
      Finset.sum_insert (Finset.notMem_erase _ _), hWc'] at h
    omega
  have hge3 : ∀ a ∈ (primaryFactors x).erase (X - C c),
      3 ≤ Module.finrank K (primaryComponent x a) := by
    intro a ha
    obtain ⟨k, hk⟩ := hdiv a (Finset.mem_of_mem_erase ha)
    have hp := hpos a (Finset.mem_of_mem_erase ha)
    omega
  have hcard1 : ((primaryFactors x).erase (X - C c)).card = 1 := by
    have hle : ((primaryFactors x).erase (X - C c)).card * 3 ≤
        ∑ a ∈ (primaryFactors x).erase (X - C c),
          Module.finrank K (primaryComponent x a) := by
      calc ((primaryFactors x).erase (X - C c)).card * 3 =
          ∑ _a ∈ (primaryFactors x).erase (X - C c), (3 : ℕ) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hge3
    have hne0 : ((primaryFactors x).erase (X - C c)).card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hsum_erase
      omega
    omega
  obtain ⟨p, hT⟩ := Finset.card_eq_one.mp hcard1
  have hpT : p ∈ (primaryFactors x).erase (X - C c) := by
    rw [hT]
    exact Finset.mem_singleton_self _
  have hpF : p ∈ primaryFactors x := Finset.mem_of_mem_erase hpT
  obtain ⟨d, hd3, hpd⟩ := u6r_primaryFactor_eq B hB3 hpF
  have hdF : X - C d ∈ primaryFactors x := by
    rwa [← hpd]
  have hXC : ∀ a a' : K, a ≠ a' → (X - C a : K[X]) ≠ X - C a' := fun a a' haa' h =>
    haa' (C_injective (sub_right_injective h))
  have hT' : (primaryFactors x).erase (X - C c) = {X - C d} := by
    rw [hT, hpd]
  have hdne : d ≠ c := by
    intro hdc
    have hmem : X - C c ∈ ({X - C d} : Finset K[X]) := by
      rw [← hdc]
      exact Finset.mem_singleton_self _
    rw [← hT'] at hmem
    exact Finset.notMem_erase _ _ hmem
  have hF_eq : primaryFactors x = {X - C c, X - C d} := by
    rw [← Finset.insert_erase hcF, hT']
  have hWd : Module.finrank K (primaryComponent x (X - C d)) = 3 := by
    have h := hsum_erase
    rw [hT'] at h
    simpa using h
  have hne_poly : (X - C c : K[X]) ≠ X - C d := hXC c d (fun h => hdne h.symm)
  have hproj : primaryProjection x (X - C c) + primaryProjection x (X - C d) = 1 := by
    have h := sum_primaryProjection hsq
    rw [hF_eq, Finset.sum_pair hne_poly] at h
    exact h
  let Wc : Submodule K (Fin 6 → K) := primaryComponent x (X - C c)
  let Wd : Submodule K (Fin 6 → K) := primaryComponent x (X - C d)
  have hdisj : Disjoint Wc Wd := by
    rw [Submodule.disjoint_def]
    intro v hvc hvd
    have hvc' : x v = c • v := (u6r_mem_primaryComponent_iff B c v).mp hvc
    have hvd' : x v = d • v := (u6r_mem_primaryComponent_iff B d v).mp hvd
    have hcdv : c • v = d • v := hvc'.symm.trans hvd'
    have h0 : (c - d) • v = 0 := by
      rw [sub_smul, hcdv, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (fun h => hdne h.symm))
  have hsup : Wc ⊔ Wd = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = primaryProjection x (X - C c) v + primaryProjection x (X - C d) v := by
      have h := congrArg (fun f : Module.End K (Fin 6 → K) => f v) hproj
      simpa [LinearMap.add_apply] using h.symm
    rw [hv]
    exact Submodule.add_mem_sup (primaryProjection_mem hsq hcF v)
      (primaryProjection_mem hsq hdF v)
  have hcompl : IsCompl Wc Wd := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  have hap : (B : GL (Fin 6) K) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (1 : Kˣ) := by
    simpa only [map_one] using hB3
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin B) :=
    t6psuh_primaryData_toLin' h B.2 Nat.prime_three (by norm_num) hap
  have horth : ∀ v ∈ Wc, ∀ w ∈ Wd, idForm h 6 v w = 0 := by
    intro v hv w hw
    refine KCUnitary.orthogonal_of_ne_dualPoly (H := H) (x := t6psub_toLin B)
      (B := idForm h 6) hcF hdF ?_ hv hw
    rw [u6r_dualPoly h hf hc3]
    exact hXC d c hdne
  have hsepC : ((idForm h 6).domRestrict₁₂ Wc Wc).SeparatingLeft :=
    KCUnitary.separatingLeft_primaryComponent_selfDual (H := H) (x := t6psub_toLin B)
      (B := idForm h 6) hcF (u6r_dualPoly h hf hc3)
  have hsepD : ((idForm h 6).domRestrict₁₂ Wd Wd).SeparatingLeft :=
    KCUnitary.separatingLeft_primaryComponent_selfDual (H := H) (x := t6psub_toLin B)
      (B := idForm h 6) hdF (u6r_dualPoly h hf hd3)
  have hsum_proj : primaryProjection x (X - C c) +
      primaryProjection x (X - C d) = 1 := hproj
  have hop : x = c • primaryProjection x (X - C c) +
      d • primaryProjection x (X - C d) := by
    refine LinearMap.ext fun v => ?_
    have hv : v = primaryProjection x (X - C c) v +
        primaryProjection x (X - C d) v := by
      have h := congrArg (fun f : Module.End K (Fin 6 → K) => f v) hproj
      simpa [LinearMap.add_apply] using h.symm
    have hxc : x (primaryProjection x (X - C c) v) =
        c • primaryProjection x (X - C c) v :=
      (u6r_mem_primaryComponent_iff B c _).mp (primaryProjection_mem hsq hcF v)
    have hxd : x (primaryProjection x (X - C d) v) =
        d • primaryProjection x (X - C d) v :=
      (u6r_mem_primaryComponent_iff B d _).mp (primaryProjection_mem hsq hdF v)
    calc x v = x (primaryProjection x (X - C c) v +
          primaryProjection x (X - C d) v) := by
          conv_lhs => rw [hv]
      _ = x (primaryProjection x (X - C c) v) +
          x (primaryProjection x (X - C d) v) := map_add _ _ _
      _ = c • primaryProjection x (X - C c) v +
          d • primaryProjection x (X - C d) v := by rw [hxc, hxd]
      _ = (c • primaryProjection x (X - C c) +
          d • primaryProjection x (X - C d)) v := by
          simp [LinearMap.add_apply]
  refine ⟨d, hd3, hdne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hF_eq
  · exact hWd
  · exact hcompl
  · exact horth
  · exact hsepC
  · exact hsepD
  · exact hsum_proj
  · exact hop


end Eigen

end CFSG.HardMathSupport.Dickson.Sec6.I1431
