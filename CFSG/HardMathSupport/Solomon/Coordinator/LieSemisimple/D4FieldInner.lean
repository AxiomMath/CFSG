module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
import CFSG.HardMathSupport.Lang.D4Three.DiagSquare
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
import CFSG.LieType.Chevalley.NoncentralNormalSolvable
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RecipeExcLang
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


variable {K : Type} [Field K] [Finite K]

private theorem coe_conj_mul_exactNormalAut_one (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (h : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) h : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * (h : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)⁻¹ := by
  have h1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL Tag.D4 K) = h := by
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_exactNormalAut, exactQ_zero, h1]
  group

theorem d4_inner_of_diag (hK3 : ringChar K ≠ 3) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (hα : (MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) ^ 3 = 1) :
    ∃ h : adjointGroup Tag.D4 K, MulAut.conj g * exactNormalAut Tag.D4 K a 1 0 = MulAut.conj h := by
  set α := MulAut.conj g * exactNormalAut Tag.D4 K a 1 0 with hαdef
  have hγ : (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a ∈ inndiagGroup Tag.D4 K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  have hsq := sq_mem_adjointGroup_of_mem_inndiagGroup hγ
  have hα2 : α ^ 2 = MulAut.conj ⟨_, hsq⟩ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [pow_two, MulAut.mul_apply, hαdef, coe_conj_mul_exactNormalAut_one,
      coe_conj_mul_exactNormalAut_one, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, pow_two]
    group
  have hinv : α = (α ^ 2)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ' α 2]
    exact hα
  exact ⟨_, by rw [hinv, hα2, ← map_inv]⟩

private theorem perfectInLayer_of_fix_eq {S : Type*} [Group S] {β β' : MulAut S}
    (h : fixSubgroup β = fixSubgroup β') (hβ : PerfectInLayer β) : PerfectInLayer β' := by
  intro P hP hPP
  rw [← h] at hP ⊢
  exact hβ P hP hPP

private theorem perfectInLayer_of_inv {S : Type*} [Group S] {β : MulAut S}
    (h : PerfectInLayer β⁻¹) : PerfectInLayer β := by
  refine perfectInLayer_of_fix_eq (β := β⁻¹) ?_ h
  ext x
  rw [mem_fixSubgroup, mem_fixSubgroup]
  constructor
  · intro hx
    have h1 : β (β⁻¹ x) = β x := congrArg (fun y => β y) hx
    rw [MulAut.apply_inv_self] at h1
    exact h1.symm
  · intro hx
    have h1 : β⁻¹ (β x) = β⁻¹ x := congrArg (fun y => β⁻¹ y) hx
    rw [MulAut.inv_apply_self] at h1
    exact h1.symm

private theorem perfectInLayer_of_conj_eq {S : Type*} [Group S] {α δ ψ : MulAut S}
    (h : ψ * α * ψ⁻¹ = δ) (hδ : PerfectInLayer δ) : PerfectInLayer α := by
  have h1 := perfectInLayer_conj ψ⁻¹ δ hδ
  rw [← h] at h1
  have e : ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α := by group
  rwa [e] at h1

private theorem isSimpleGroup_adjointGroup_D4 (k : Type) [Field k] [Finite k] :
    IsSimpleGroup (adjointGroup Tag.D4 k) ∧ ∃ x y : adjointGroup Tag.D4 k, x * y ≠ y * x := by
  have hnc := (opposite_simple_root_noncommutativity Tag.D4 k).2.2.1
  have : Group.IsPerfect (adjointGroup Tag.D4 k) :=
    ⟨single_edge_perfect Tag.D4 k (Or.inr (Or.inl rfl))⟩
  have : Nontrivial (adjointGroup Tag.D4 k) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup Tag.D4 k) = ⊥ := center_adjointGroup_eq_bot
  refine ⟨IsSimpleGroup.mk fun M hM => ?_, hnc⟩
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center (adjointGroup Tag.D4 k) := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := (noncentral_normal_solvable_quotient Tag.D4 k M hnot).2.1
    by_contra htop
    have : Nontrivial (adjointGroup Tag.D4 k ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

private theorem perfectInLayer_entrywiseAdjointAut_D4 (σ : K ≃+* K) :
    PerfectInLayer (entrywiseAdjointAut Tag.D4 σ) := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, -, hJnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup Tag.D4 K σ
  have : Finite (fixSubfield σ) := inferInstance
  obtain ⟨hs, hnc⟩ := isSimpleGroup_adjointGroup_D4 (fixSubfield σ)
  have hJC : fixedFieldImage Tag.D4 σ ≤ adjointGroup Tag.D4 K := fun g hg => (hJΓ hg).1
  have hΓnorm : entrywiseFixedGroup Tag.D4 σ ≤
      Subgroup.normalizer (fixedFieldImage Tag.D4 σ : Set (ModGL Tag.D4 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJnormal
  have hfix : ∀ x : adjointGroup Tag.D4 K,
      x ∈ fixSubgroup (entrywiseAdjointAut Tag.D4 σ) ↔
        (x : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ := fun x => by
    rw [mem_fixSubgroup, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨x.2, (coe_entrywiseAdjointAut Tag.D4 σ x).symm.trans (congrArg Subtype.val h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut Tag.D4 σ x).trans h)
  let J : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (fixedFieldImage Tag.D4 σ).subgroupOf (adjointGroup Tag.D4 K)
  have hJmem : ∀ x : adjointGroup Tag.D4 K,
      x ∈ J ↔ (x : ModGL Tag.D4 K) ∈ fixedFieldImage Tag.D4 σ := fun x => Iff.rfl
  have hJle : J ≤ fixSubgroup (entrywiseAdjointAut Tag.D4 σ) := fun x hx =>
    (hfix x).2 (hJΓ ((hJmem x).1 hx))
  have hJn : (J.subgroupOf (fixSubgroup (entrywiseAdjointAut Tag.D4 σ))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hJmem, hJmem]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm ((hfix g).1 hg)) (h : ModGL Tag.D4 K)
  let eJ : J ≃* adjointGroup Tag.D4 (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans
      ((adjointGroup Tag.D4 (fixSubfield σ)).equivMapOfInjective _ hinj).symm
  have hJs : IsSimpleGroup J := eJ.isSimpleGroup
  have hJnc : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  have hsol : Group.IsSolvable
      (↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) ⧸
        J.subgroupOf (fixSubgroup (entrywiseAdjointAut Tag.D4 σ))) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have hx : ((x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ :=
      (hfix x.1).1 x.2
    have hy : ((y : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ :=
      (hfix y.1).1 y.2
    have hq := hcomm (QuotientGroup.mk ⟨_, hx⟩) (QuotientGroup.mk ⟨_, hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hJmem]
    exact hq
  exact perfectInLayer_of_normal_quasisimple hJle (isQuasisimple_of_isSimpleGroup hJs hJnc) hsol

private theorem d4Graph_zero' : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

private theorem exists_frobenius_data (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ3 : σ ^ 3 = 1) :
    ∃ (ℓ e : ℕ) (T : K ≃+* K), ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ e ∧ Nat.card K = ℓ ^ (e * 3) ∧
      (∀ c, T c = c ^ (ℓ ^ e)) ∧ (σ = T ∨ σ = T⁻¹) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three hpr n.pos K hK σ hord
  exact ⟨ringChar K, e, T, hpr, ringChar.charP K, he, by rw [hef, hK], hT, hσT⟩

private theorem perfectInLayer_of_lang {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hσT : σ = T ∨ σ = T⁻¹) (ε : ℕ)
    (hP : ∀ j : ℤ, (j = (ε : ℤ) ∨ j = -(ε : ℤ)) →
      PerfectInLayer (twistedEntrywiseAut TwistTag.D4 j T))
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    PerfectInLayer (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le 2
      _ ≤ ℓ ^ (e * 3) := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)
  set α := MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) with hαdef
  rcases hσT with hσT | hσT
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl σ hT α hα
      g a ε hαdef
    exact perfectInLayer_of_conj_eq hψ (hP _ (Or.inl rfl))
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl T T⁻¹
      hT (mul_inv_cancel T) α hα g a ε hαdef
    exact perfectInLayer_of_inv (perfectInLayer_of_conj_eq hψ (hP _ (Or.inr rfl)))

private theorem perfectInLayer_twistedEntrywiseAut_one {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (σ : K ≃+* K) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) :
    PerfectInLayer (twistedEntrywiseAut TwistTag.D4 1 σ) := by
  classical
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, hfixeq, hsimple, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ e Fact.out he K
      (by rw [hK, pow_mul]) (AlgebraicClosure K) r hr σ.toRingHom hσ
      (iterateFrobenius (AlgebraicClosure K) ℓ e) (fun c => by simp [iterateFrobenius_def])
  let eΓ : fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 σ).trans
      (MulEquiv.subgroupCongr hfixeq)
  have hs : IsSimpleGroup (fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) :=
    eΓ.isSimpleGroup
  have hnc' : ∃ x y : fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨eΓ.symm x, eΓ.symm y, fun h => hxy ?_⟩
    have h1 := congrArg eΓ h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
    exact h1
  exact perfectInLayer_of_isSimpleGroup _ hs hnc'

private theorem perfectInLayer_twistedEntrywiseAut_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    PerfectInLayer (twistedEntrywiseAut TwistTag.D4 j T) := by
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← pow_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul, show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
    have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
    intro c
    rw [h1, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, sq]
  have hper : twistedEntrywiseAut TwistTag.D4 j T = twistedEntrywiseAut TwistTag.D4 (j % 3) T := by
    have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
    rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
      change j % 3 + j / 3 * 3 = j
      omega] at h
    exact h
  rw [hper]
  rcases hj with h | h
  · rw [h]
    exact perfectInLayer_twistedEntrywiseAut_one he hK T 1 (Or.inl rfl) (fun c => by
      rw [hT, pow_one])
  · rw [h]
    exact perfectInLayer_of_fix_eq (fixedSubgroup_twistedEntrywiseAut_D4_two T).symm
      (perfectInLayer_twistedEntrywiseAut_one he hK T⁻¹ 2 (Or.inr rfl) hinv)

theorem perfectInLayer_d4_field (hK3 : ringChar K ≠ 3) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ3 : σ ^ 3 = 1)
    (hα : (MulAut.conj g * exactNormalAut Tag.D4 K a σ 0) ^ 3 = 1) :
    PerfectInLayer (MulAut.conj g * exactNormalAut Tag.D4 K a σ 0) := by
  obtain ⟨ℓ, e, T, hℓ, hchar, he, hK, hT, hσT⟩ := exists_frobenius_data σ hσ hσ3
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hα' : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) ^ 3 = 1 := by
    rwa [d4Graph_zero', mul_one]
  have h := perfectInLayer_of_lang he hK T hT g a σ hσT 0 (fun j hj => ?_) hα'
  · rwa [d4Graph_zero', mul_one] at h
  · have hj0 : j = 0 := by rcases hj with h | h <;> simpa using h
    subst hj0
    have e0 : twistedEntrywiseAut TwistTag.D4 0 T = entrywiseAdjointAut Tag.D4 T := by
      unfold twistedEntrywiseAut
      rw [zpow_zero, one_mul]
      rfl
    rw [e0]
    exact perfectInLayer_entrywiseAdjointAut_D4 T

theorem perfectInLayer_d4_graphField (hK3 : ringChar K ≠ 3) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ3 : σ ^ 3 = 1) {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    PerfectInLayer (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) := by
  obtain ⟨ℓ, e, T, hℓ, hchar, he, hK, hT, hσT⟩ := exists_frobenius_data σ hσ hσ3
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine perfectInLayer_of_lang he hK T hT g a σ hσT ε (fun j hj => ?_) hα
  refine perfectInLayer_twistedEntrywiseAut_D4 he hK T hT j ?_
  rcases hε with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
