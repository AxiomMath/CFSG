module

public import CFSG.RankThree.PartOne.SEITZ8.D4Form

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ8

variable {K : Type} [Field K]

@[expose] def wtRoot (γ : Fin d4.rank → ℤ) : ℤ := (-1) ^ ((∑ j, γ j).natAbs + 1)

@[expose] def cartO (i j : Fin d4.rank) : ℤ :=
  if i = j then -2 else if i.val = 2 ∨ j.val = 2 then -1 else 0

@[expose] noncomputable def jLabO : Label d4 → Label d4 → ℤ
  | .inl i, .inl j => cartO i j
  | .inr α, .inr β => open Classical in if β.1 = -α.1 then wtRoot α.1 else 0
  | _, _ => 0

@[expose] noncomputable def jFormO (K : Type) [Field K] : LinearMap.BilinForm K (RootModule d4 K) :=
  Finsupp.linearCombination K fun a => Finsupp.linearCombination K fun b => (jLabO a b : K)

theorem jFormO_single (a b : Label d4) :
    jFormO K (Finsupp.single a 1) (Finsupp.single b 1) = (jLabO a b : K) := by
  simp [jFormO, Finsupp.linearCombination_single]

@[expose] def jIdxO : DIdx → DIdx → ℤ
  | .inl i, .inl j => cartO i j
  | .inr m, .inr n =>
    if vecBEq ((Tag.rootCertificate d4).root n) (-((Tag.rootCertificate d4).root m)) then
      wtRoot ((Tag.rootCertificate d4).root m) else 0
  | _, _ => 0

@[expose] def jColLO : Col (Tag.rootCertificate d4) → DIdx → ℤ
  | none, _ => 0
  | some (a, z), b => z * jIdxO a b

@[expose] def jColRO : DIdx → Col (Tag.rootCertificate d4) → ℤ
  | _, none => 0
  | a, some (b, z) => z * jIdxO a b

@[expose] def selfAdjOB (s : ℤ) (f : DIdx → Col (Tag.rootCertificate d4)) : Bool :=
  dIdxList.all fun a => dIdxList.all fun b => jColLO (f a) b == s * jColRO a (f b)

@[expose] def formCheckO : Bool :=
  (List.finRange (Tag.rank d4)).all fun i => [1, 2, 3].all fun k =>
    selfAdjOB ((-1) ^ k) (xCol (Tag.rootCertificate d4) (Tag.stringData d4) i k) &&
      selfAdjOB ((-1) ^ k) (yCol (Tag.rootCertificate d4) (Tag.stringData d4) i k)

theorem formCheckO_eq : formCheckO = true := by decide +kernel

theorem selfAdjOB_spec {s : ℤ} {f : DIdx → Col (Tag.rootCertificate d4)}
    (h : selfAdjOB s f = true) (a b : DIdx) : jColLO (f a) b = s * jColRO a (f b) := by
  simp only [selfAdjOB, List.all_eq_true, beq_iff_eq] at h
  exact h a (mem_dIdxList a) b (mem_dIdxList b)

section Certs


theorem jLabO_toLabel (a b : DIdx) :
    jLabO (toLabel (Tag.rootCertificate_check d4) a) (toLabel (Tag.rootCertificate_check d4) b) =
      jIdxO a b := by
  rcases a with i | m <;> rcases b with j | n
  · rfl
  · rfl
  · rfl
  · simp only [jLabO, jIdxO, toLabel]
    by_cases h : (Tag.rootCertificate d4).root n = -(Tag.rootCertificate d4).root m
    · rw [ite_eq_left h, ite_eq_left (vecBEq_iff.2 h)]
    · rw [ite_eq_right h, ite_eq_right fun e => h (vecBEq_iff.1 e)]

theorem jFormO_toVec_single (u : Col (Tag.rootCertificate d4)) (b : DIdx) :
    jFormO K (toVec (Tag.rootCertificate_check d4) K u)
      (Finsupp.single (toLabel (Tag.rootCertificate_check d4) b) 1) = (jColLO u b : K) := by
  rcases u with _ | ⟨a, z⟩
  · simp [jColLO]
  · rw [toVec_some, map_smul, LinearMap.smul_apply, jFormO_single, jLabO_toLabel]
    simp [jColLO]

theorem jFormO_single_toVec (a : DIdx) (u : Col (Tag.rootCertificate d4)) :
    jFormO K (Finsupp.single (toLabel (Tag.rootCertificate_check d4) a) 1)
      (toVec (Tag.rootCertificate_check d4) K u) = (jColRO a u : K) := by
  rcases u with _ | ⟨b, z⟩
  · simp [jColRO]
  · rw [toVec_some, map_smul, jFormO_single, jLabO_toLabel]
    simp [jColRO]

theorem selfAdjO_of_check {s : ℤ} {T : Module.End K (RootModule d4 K)}
    {f : DIdx → Col (Tag.rootCertificate d4)}
    (hT : ∀ a, T (Finsupp.single (toLabel (Tag.rootCertificate_check d4) a) 1) =
      toVec (Tag.rootCertificate_check d4) K (f a)) (hf : selfAdjOB s f = true)
    (x y : RootModule d4 K) : jFormO K (T x) y = (s : K) * jFormO K x (T y) := by
  have key : (jFormO K).compl₁₂ T LinearMap.id =
      (s : K) • (jFormO K).compl₁₂ LinearMap.id T := by
    refine LinearMap.ext_basis Finsupp.basisSingleOne Finsupp.basisSingleOne fun a b => ?_
    obtain ⟨a', rfl⟩ := surjective_toLabel (Tag.rootCertificate_check d4) a
    obtain ⟨b', rfl⟩ := surjective_toLabel (Tag.rootCertificate_check d4) b
    simp only [Finsupp.coe_basisSingleOne, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hT a', hT b', jFormO_toVec_single, jFormO_single_toVec]
    have h2 := selfAdjOB_spec hf a' b'
    rw [h2]
    push_cast
    rfl
  exact LinearMap.congr_fun₂ key x y

end Certs

section Invariance


theorem jFormO_xCoeff_comm (i : Fin d4.rank) {k : ℕ} (hk : k ∈ [1, 2, 3])
    (x y : RootModule d4 K) :
    jFormO K (xCoeff d4 K i k x) y = ((-1 : K) ^ k) * jFormO K x (xCoeff d4 K i k y) := by
  have := selfAdjO_of_check (K := K) (s := (-1) ^ k) (T := xCoeff d4 K i k)
    (f := xCol (Tag.rootCertificate d4) (Tag.stringData d4) i k)
    (fun a => xCoeff_toLabel (Tag.rootCertificate_check d4) K (Tag.stringData_check d4) i k a)
    (by
      have h := formCheckO_eq
      simp only [formCheckO, List.all_eq_true, List.mem_finRange, true_implies,
        Bool.and_eq_true] at h
      exact (h i k hk).1) x y
  simpa using this

theorem jFormO_yCoeff_comm (i : Fin d4.rank) {k : ℕ} (hk : k ∈ [1, 2, 3])
    (x y : RootModule d4 K) :
    jFormO K (yCoeff d4 K i k x) y = ((-1 : K) ^ k) * jFormO K x (yCoeff d4 K i k y) := by
  have := selfAdjO_of_check (K := K) (s := (-1) ^ k) (T := yCoeff d4 K i k)
    (f := yCol (Tag.rootCertificate d4) (Tag.stringData d4) i k)
    (fun a => yCoeff_toLabel (Tag.rootCertificate_check d4) K (Tag.stringData_check d4) i k a)
    (by
      have h := formCheckO_eq
      simp only [formCheckO, List.all_eq_true, List.mem_finRange, true_implies,
        Bool.and_eq_true] at h
      exact (h i k hk).2) x y
  simpa using this

theorem jFormO_xOp_comm (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jFormO K (xOp d4 K i c x) y = jFormO K x (xOp d4 K i (-c) y) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk4 : k < 4 := Finset.mem_range.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [xCoeff_zero]
  · rw [jFormO_xCoeff_comm i (by interval_cases k <;> simp) x y, neg_pow]
    ring

theorem jFormO_yOp_comm (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jFormO K (yOp d4 K i c x) y = jFormO K x (yOp d4 K i (-c) y) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk4 : k < 4 := Finset.mem_range.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [yCoeff_zero]
  · rw [jFormO_yCoeff_comm i (by interval_cases k <;> simp) x y, neg_pow]
    ring

theorem jFormO_xOp (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jFormO K (xOp d4 K i c x) (xOp d4 K i c y) = jFormO K x y := by
  rw [jFormO_xOp_comm, ← Module.End.mul_apply (xOp d4 K i (-c)) (xOp d4 K i c) y,
    xOp_neg_mul_xOp (upTransport d4)]
  rfl

theorem jFormO_yOp (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jFormO K (yOp d4 K i c x) (yOp d4 K i c y) = jFormO K x y := by
  rw [jFormO_yOp_comm, ← Module.End.mul_apply (yOp d4 K i (-c)) (yOp d4 K i c) y,
    yOp_neg_mul_yOp (downTransport d4)]
  rfl

@[expose] def jInvO (K : Type) [Field K] : Subgroup (ModGL d4 K) where
  carrier := {g | ∀ x y : RootModule d4 K,
    jFormO K ((g : Module.End K (RootModule d4 K)) x) ((g : Module.End K (RootModule d4 K)) y) =
      jFormO K x y}
  mul_mem' := by
    intro a b ha hb x y
    rw [Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  one_mem' := by
    intro x y
    simp
  inv_mem' := by
    intro a ha x y
    have h1 : ∀ z : RootModule d4 K, (a : Module.End K (RootModule d4 K))
        (((a⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) z) = z := fun z => by
      rw [← Module.End.mul_apply, Units.mul_inv]
      rfl
    have := ha (((a⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) x)
      (((a⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) y)
    rw [h1, h1] at this
    exact this.symm

theorem adjointGroup_le_jInvO : adjointGroup d4 K ≤ jInvO K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, h | h⟩
  · intro x y
    rw [h]
    exact jFormO_xOp i c x y
  · intro x y
    rw [h]
    exact jFormO_yOp i c x y

theorem jFormO_invariant (g : adjointGroup d4 K) (x y : RootModule d4 K) :
    jFormO K (g • x) (g • y) = jFormO K x y :=
  adjointGroup_le_jInvO g.2 x y

theorem jFormO_smul_left (r : adjointGroup d4 K) (x y : RootModule d4 K) :
    jFormO K (r • x) y = jFormO K x (r⁻¹ • y) := by
  have := jFormO_invariant r x (r⁻¹ • y)
  rwa [smul_inv_smul] at this

end Invariance

theorem wtRoot_neg (γ : Fin d4.rank → ℤ) : wtRoot (-γ) = wtRoot γ := by
  simp [wtRoot]

section Extraction


theorem jFormO_rootVec_left (γ : Fin d4.rank → ℤ) (x : RootModule d4 K) :
    jFormO K (rootVec d4 K (-γ)) x = (wtRoot γ : K) * coordAt γ x := by
  by_cases hγ : IsRoot d4 γ
  · have hγ' := isRoot_neg_d4 hγ
    rw [rootVec_eq_single K hγ']
    induction x using Finsupp.induction_linear with
    | zero => simp [coordAt]
    | add x y hx hy => rw [map_add, hx, hy, coordAt_add, mul_add]
    | single b r =>
      rw [← Finsupp.smul_single_one b r, map_smul, coordAt_smul]
      rw [smul_eq_mul, mul_left_comm]
      congr 1
      rcases b with j | ⟨δ, hδ⟩
      · rw [jFormO_single]
        have : Finsupp.single (Sum.inl j : Label d4) (1 : K) = hVec d4 K j := rfl
        rw [this, coordAt_hVec]
        simp [jLabO]
      · rw [jFormO_single, ← rootVec_eq_single K hδ]
        by_cases h : γ = δ
        · subst h
          rw [coordAt_rootVec_self hγ]
          simp [jLabO, wtRoot_neg]
        · rw [coordAt_rootVec_ne h]
          have : ¬ δ = γ := fun e => h e.symm
          simp [jLabO, this]
  · have h' : ¬ IsRoot d4 (-γ) := fun h => hγ (by simpa using isRoot_neg_d4 h)
    rw [rootVec, dite_eq_right h']
    simp [coordAt, hγ]

theorem jFormO_rootVec_left' {γ δ : Fin d4.rank → ℤ} (h : δ = -γ)
    (x : RootModule d4 K) : jFormO K (rootVec d4 K δ) x = (wtRoot γ : K) * coordAt γ x := by
  subst h
  exact jFormO_rootVec_left γ x

theorem jFormO_hVec_left (i : Fin d4.rank) (x : RootModule d4 K) :
    jFormO K (hVec d4 K i) x = ∑ j : Fin d4.rank, (cartO i j : K) * x (Sum.inl j) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, hx, hy]
    simp only [Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  | single b r =>
    rw [← Finsupp.smul_single_one b r, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    have : hVec d4 K i = Finsupp.single (Sum.inl i : Label d4) 1 := rfl
    rw [this, jFormO_single]
    rcases b with j' | δ
    · rw [Finset.sum_eq_single j']
      · simp [jLabO]
        ring
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    · simp [jLabO]

end Extraction

end CFSG.HardMathSupport.Seitz.TrialityOdd
