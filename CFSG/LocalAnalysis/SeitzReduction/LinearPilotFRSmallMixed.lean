module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

theorem eq_bot_of_commutator_eq_self_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (Q : Subgroup G) (hQ : IsPGroup p Q) (hperf : ⁅Q, Q⁆ = Q) : Q = ⊥ := by
  by_contra hne
  have hnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  have hp : Group.IsPerfect Q := Subgroup.isPerfect_iff.mpr hperf
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne (Group.isPerfect_def.mp hp)

section Simple

variable {n k : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem InvPlacement.inf_radicalP_spec (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (P : InvPlacement n k) (hP : P.elt K ≠ 1) :
    IsPGroup 2 (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ⊓ P.radicalP K :
      Subgroup (projectiveSL n K)) ∧
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
        normalizer ((perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ⊓
          P.radicalP K : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) ∧
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ⊓ P.radicalP K ≠ ⊥ ∧
      ¬ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
        perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ⊓ P.radicalP K := by
  set Λ := perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) with hΛdef
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)
  have h2 : IsPGroup 2 (Λ ⊓ P.radicalP K : Subgroup (projectiveSL n K)) :=
    P.isPGroup_radicalP.to_le inf_le_right
  have hN : Λ ≤ normalizer ((Λ ⊓ P.radicalP K : Subgroup (projectiveSL n K)) :
      Set (projectiveSL n K)) :=
    (le_inf le_normalizer ((perfectCore_centralizer_elt_le_map_core (K := K) P).trans
      P.map_core_le_normalizer_radicalP)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hne : Λ ⊓ P.radicalP K ≠ ⊥ := by
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
    ·
      have hJ : 2 ≤ P.free.card := by have := P.card_free; omega
      obtain ⟨-, hΛeq, -, -, -⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ)
      intro hbot
      apply hP
      have hy : P.elt K ∈ Λ ⊓ P.radicalP K := by
        refine ⟨?_, P.elt_mem_radicalP⟩
        rw [hΛdef, hΛeq]
        exact Subgroup.mem_sup_left P.elt_mem_radicalP
      rw [hbot] at hy
      exact hy
    ·
      have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      intro hbot
      have hmem := P.proj_transvection_u_w_mem_coreRadicalP hq h01 (1 : K)
      change _ ∈ Λ ⊓ P.radicalP K at hmem
      rw [hbot, Subgroup.mem_bot] at hmem
      exact proj_transvection_ne_one (P.u_ne_w _ _) one_ne_zero hmem
  refine ⟨h2, hN, hne, fun hle => hne ?_⟩
  have hΛ2 : IsPGroup 2 Λ := h2.to_le hle
  have hΛbot := eq_bot_of_commutator_eq_self_of_isPGroup (p := 2) Λ hΛ2
    (perfectCore_perfect _)
  exact le_bot_iff.1 (hΛbot ▸ inf_le_left)

theorem fieldRigidIn_inner_of_isSimpleGroup (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (P : InvPlacement n k) (hP : P.elt K ≠ 1) (X : Subgroup (projectiveSL n K))
    (hX : IsSimpleGroup X) :
    FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))) X := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hΛX γ β₁ β₂ hβX h₁ h₂
  exfalso
  set Λ := perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) with hΛdef
  obtain ⟨-, hΛN, hne, hnle⟩ := P.inf_radicalP_spec hq hn hP
  set N := Λ ⊓ P.radicalP K with hNdef
  set T := (N.map φ₁).comap φ₂ with hT
  have hTX : T ≤ X := comap_map_le hφ₂ hΛX inf_le_left
  have hXT : X ≤ normalizer (T : Set (projectiveSL n K)) := le_normalizer_comap_map hΛX hΛN
  have hTn : (T.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTX).2 hXT
  rcases hX.eq_bot_or_eq_top_of_normal (T.subgroupOf X) with h | h
  · have hT0 : T = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact le_bot_iff.1 fun x hx => h.le_bot ⟨hx, hTX hx⟩
    have hmap := map_comap_map_eq (φ := φ₁) (φ' := φ₂) hΛX (H := N) inf_le_left
    rw [← hT, hT0, Subgroup.map_bot] at hmap
    exact hne ((map_eq_bot_iff_of_injective _ hφ₁).1 hmap.symm)
  · rw [Subgroup.subgroupOf_eq_top] at h
    apply hnle
    rw [← map_le_map_iff_of_injective hφ₁, hΛX]
    calc X.map φ₂ ≤ T.map φ₂ := map_mono h
      _ = N.map φ₁ := map_comap_map_eq hΛX inf_le_left

end Simple

section GraphCores

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem autFixSubgroup_eq_fixedSubgroup {G : Type*} [Group G] (α : MulAut G) :
    autFixSubgroup α = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α := by
  ext x
  rfl

theorem isSimpleGroup_perfectCore_autFixSubgroup_graph {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) {r : ℕ} (hr : 2 ≤ r) (C : GL (Fin n) K)
    (hC : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) ∨
      (n = 2 * r + 1 ∧ (C : Matrix (Fin n) (Fin n) K) = 1)) :
    IsSimpleGroup (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K))) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : NeZero r := ⟨by omega⟩
  have hC' : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r := by
    rcases hC with ⟨hn2, hJ⟩ | ⟨-, h1⟩
    · exact Or.inr ⟨r, hn2, hJ⟩
    · exact Or.inl h1
  obtain ⟨e₁⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv hf hK
    hn C hC'
  obtain ⟨e₂⟩ : Nonempty (FourGroupEvenCanonical.matrixIsometryGroup
      (C : Matrix (Fin n) (Fin n) K) ≃* CFSG.Assembly.LowTwoRank.StatedSp r K) := by
    rcases hC with ⟨hn2, hJ⟩ | ⟨hn2, h1⟩
    · exact ⟨(MulEquiv.subgroupCongr
        (congrArg FourGroupEvenCanonical.matrixIsometryGroup hJ)).trans
        (CFSG.ComponentClassification.OutcomeLocal.blockSwapIsometryEquivStatedSp
          (by omega))⟩
    · have hC1 : (C : Matrix (Fin n) (Fin n) K) =
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, Units.val_one]
      obtain ⟨e⟩ :=
        CFSG.ComponentClassification.OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
        (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_isAlt (k := K) (n := n))
        (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_nondegenerate hn2)
        (CFSG.ComponentClassification.OutcomeLocal.finrank_dotForm_ker hn2)
      exact ⟨((MulEquiv.subgroupCongr
        (congrArg FourGroupEvenCanonical.matrixIsometryGroup hC1)).trans
        (CFSG.ComponentClassification.OutcomeLocal.oneRestrictEquiv hn2)).trans e⟩
  set e₃ : CFSG.Assembly.LowTwoRank.StatedSp r K ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r K) :=
    MulEquiv.ofBijective _ UnitaryHigher.proj_bijective_of_charTwo
  set X := autFixSubgroup (conjAut n K C * dualAut n K) with hX
  set e : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r K) :=
    ((MulEquiv.subgroupCongr (autFixSubgroup_eq_fixedSubgroup _)).trans e₁).trans
      (e₂.trans e₃) with he
  have hne : ¬(r = 2 ∧ Nat.card K = 2) := fun h => by omega
  obtain ⟨hsimple, hperf⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr hne
  have hXs : IsSimpleGroup X := e.isSimpleGroup_congr.2 hsimple
  have hXp : Group.IsPerfect X := by
    rw [Group.isPerfect_def, commutator_def] at hperf ⊢
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  have hcomm : ⁅X, X⁆ = X := Subgroup.commutator_eq_self
  have hcore : perfectCore X = X :=
    le_antisymm (perfectCore_le X) (le_perfectCore_of_perfect le_rfl hcomm)
  rw [hcore]
  exact hXs

variable {k : ℕ}

theorem fieldRigidIn_inner_graph_of_symplectic {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (P : InvPlacement n k) (hP : P.elt K ≠ 1)
    (C : GL (Fin n) K) (hC : (∃ r, n = 2 * r ∧
        (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ Odd n)) :
    FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K))) := by
  refine fieldRigidIn_inner_of_isSimpleGroup hq hn P hP _ ?_
  rcases hC with ⟨r, hr, hJ⟩ | ⟨h1, r, hr⟩
  · exact isSimpleGroup_perfectCore_autFixSubgroup_graph hK hq (Nat.le_of_succ_le hn)
      (r := r) (by omega) C (Or.inl ⟨hr, hJ⟩)
  · exact isSimpleGroup_perfectCore_autFixSubgroup_graph hK hq (Nat.le_of_succ_le hn)
      (r := r) (by omega) C (Or.inr ⟨by omega, h1⟩)

omit [CharP K 2] in
theorem not_isSimpleGroup_perfectCore_autFixSubgroup_dualAut {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (hev : Even n) :
    ¬ IsSimpleGroup (perfectCore (autFixSubgroup (dualAut n K))) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      omega
    · exact h
  intro hY
  set X := autFixSubgroup (dualAut n K) with hXdef
  set Y := perfectCore X with hYdef
  have hchar : IsCharacteristicP 2 X := by
    rw [hXdef, autFixSubgroup_eq_fixedSubgroup]
    exact CFSG.ComponentClassification.CatLeafProof.isCharacteristicP_fixed_dualAut hf hK hn hev
  set O : Subgroup (projectiveSL n K) := (pCore 2 X).map X.subtype with hO
  have hO2 : IsPGroup 2 O := pCore_isPGroup.map _
  have hOX : O ≤ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hXO : X ≤ normalizer (O : Set (projectiveSL n K)) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨x, hx⟩ * o * ⟨x, hx⟩⁻¹, (pCore_normal (p := 2) (G := X)).conj_mem o ho _, rfl⟩
    · rintro ⟨o, ho, hoe⟩
      refine ⟨⟨x, hx⟩⁻¹ * o * ⟨x, hx⟩, ?_, ?_⟩
      · have := (pCore_normal (p := 2) (G := X)).conj_mem o ho ⟨x, hx⟩⁻¹
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hoe ⊢
        rw [hoe]
        group
  have hYX : Y ≤ X := perfectCore_le X
  have hXY : X ≤ normalizer (Y : Set (projectiveSL n K)) :=
    (le_normalizer).trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore X)
  have hYne : Y ≠ ⊥ := by
    intro h
    have : Nontrivial Y := hY.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne Y
    apply hab
    have ha : (a : projectiveSL n K) = 1 := (Subgroup.eq_bot_iff_forall Y).1 h _ a.2
    have hb : (b : projectiveSL n K) = 1 := (Subgroup.eq_bot_iff_forall Y).1 h _ b.2
    exact Subtype.ext (ha.trans hb.symm)
  have hN : ((O ⊓ Y).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2
      ((le_inf (hYX.trans hXO) le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
  rcases hY.eq_bot_or_eq_top_of_normal ((O ⊓ Y).subgroupOf Y) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    have hOY : O ⊓ Y = ⊥ := le_bot_iff.1 fun x hx =>
      h.le_bot ⟨hx, (inf_le_right : O ⊓ Y ≤ Y) hx⟩
    have hcent : ∀ y ∈ Y, ∀ o ∈ O, y * o = o * y := by
      intro y hy o ho
      have hc : y * o * y⁻¹ * o⁻¹ ∈ O ⊓ Y := by
        refine ⟨?_, ?_⟩
        · exact O.mul_mem ((mem_normalizer_iff.1 (hXO (hYX hy)) o).1 ho) (O.inv_mem ho)
        · have h1 : o * y⁻¹ * o⁻¹ ∈ Y := (mem_normalizer_iff.1 (hXY (hOX ho)) _).1 (Y.inv_mem hy)
          have e : y * o * y⁻¹ * o⁻¹ = y * (o * y⁻¹ * o⁻¹) := by group
          rw [e]
          exact Y.mul_mem hy h1
      rw [hOY, Subgroup.mem_bot] at hc
      calc y * o = (y * o * y⁻¹ * o⁻¹) * o * y := by group
        _ = o * y := by rw [hc, one_mul]
    have hYO : Y ≤ O := by
      intro y hy
      have hyc : (⟨y, hYX hy⟩ : X) ∈ centralizer (pCore 2 X : Set X) := by
        rw [mem_centralizer_iff]
        intro o ho
        apply Subtype.ext
        exact (hcent y hy o ⟨o, ho, rfl⟩).symm
      exact ⟨_, hchar hyc, rfl⟩
    exact hYne (le_bot_iff.1 (hOY ▸ le_inf hYO le_rfl))
  · rw [Subgroup.subgroupOf_eq_top] at h
    have hY2 : IsPGroup 2 Y := hO2.to_le (h.trans inf_le_left)
    exact hYne (eq_bot_of_commutator_eq_self_of_isPGroup (p := 2) Y hY2 (perfectCore_perfect X))

theorem fieldRigidIn_graph_alt_nonalt {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) {r : ℕ} (hr : n = 2 * r) (C : GL (Fin n) K)
    (hC : (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) :
    FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)))
      (perfectCore (autFixSubgroup (dualAut n K))) := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  exfalso
  have hs := isSimpleGroup_perfectCore_autFixSubgroup_graph hK hq (Nat.le_of_succ_le hn)
    (r := r) (by omega) C (Or.inl ⟨hr, hC⟩)
  apply not_isSimpleGroup_perfectCore_autFixSubgroup_dualAut hK hn ⟨r, by omega⟩
  set A := perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)) with hA
  set B := perfectCore (autFixSubgroup (dualAut n K)) with hB
  set e : A ≃* B := (A.equivMapOfInjective φ₁ hφ₁).trans
    ((MulEquiv.subgroupCongr hX).trans (B.equivMapOfInjective φ₂ hφ₂).symm)
  exact e.symm.isSimpleGroup_congr.2 hs

end GraphCores

section Residual

variable {n : ℕ} (K : Type) [Field K] [Finite K]

@[expose] def InnerNonaltFieldRigid (hn : 3 ≤ n) : Prop :=
  Even n → ∀ (k : ℕ) (P : InvPlacement n k), P.elt K ≠ 1 →
    FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (autFixSubgroup (dualAut n K)))

@[expose] def GraphSameFieldRigid (hn : 3 ≤ n) : Prop :=
  FieldRigidIn hn (perfectCore (autFixSubgroup (dualAut n K)))
      (perfectCore (autFixSubgroup (dualAut n K))) ∧
    ∀ (r : ℕ) (C : GL (Fin n) K), n = 2 * r →
      (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r →
      FieldRigidIn hn (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)))
        (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)))

variable {K}

omit [Finite K] in
theorem conjAut_mul_dualAut_eq_of_eq_one {C : GL (Fin n) K}
    (h1 : (C : Matrix (Fin n) (Fin n) K) = 1) : conjAut n K C * dualAut n K = dualAut n K := by
  rw [show C = 1 from Units.ext h1, map_one, one_mul]

theorem innerGraphFieldRigid_of_residual {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (hAD : InnerNonaltFieldRigid K (Nat.le_of_succ_le hn))
    (hDD : GraphSameFieldRigid K (Nat.le_of_succ_le hn)) :
    InnerGraphFieldRigid K (Nat.le_of_succ_le hn) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  refine innerGraphFieldRigid_of_graph_cases hK hq hn ?_ ?_
  · intro k P C hP hC
    rcases hC with h1 | ⟨r, hr, hJ⟩
    · rcases Nat.even_or_odd n with hev | hodd
      · rw [conjAut_mul_dualAut_eq_of_eq_one h1]
        exact hAD hev k P hP
      · exact fieldRigidIn_inner_graph_of_symplectic hK hq hn P hP C (Or.inr ⟨h1, hodd⟩)
    · exact fieldRigidIn_inner_graph_of_symplectic hK hq hn P hP C (Or.inl ⟨r, hr, hJ⟩)
  · intro C C' hC hC'
    rcases hC with h1 | ⟨r, hr, hJ⟩ <;> rcases hC' with h1' | ⟨r', hr', hJ'⟩
    · rw [conjAut_mul_dualAut_eq_of_eq_one h1, conjAut_mul_dualAut_eq_of_eq_one h1']
      exact hDD.1
    · rw [conjAut_mul_dualAut_eq_of_eq_one h1]
      exact (fieldRigidIn_graph_alt_nonalt hK hq hn hr' C' hJ').symm
    · rw [conjAut_mul_dualAut_eq_of_eq_one h1']
      exact fieldRigidIn_graph_alt_nonalt hK hq hn hr C hJ
    · have hrr : r = r' := by omega
      subst hrr
      have hCC : C = C' := Units.ext (hJ.trans hJ'.symm)
      subst hCC
      exact hDD.2 r C hr hJ

end Residual

end CFSG.SeitzReduction.LinearPilot
