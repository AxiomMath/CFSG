module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceFromYS
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearModel
public import CFSG.RankThree.PartOne.SRC.CoverSL3
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1918

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

section General

theorem pCore_two_eq_bot_of_simple {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    [Group.IsPerfect T] : CFSG.pCore 2 T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := CFSG.LieType.BorelTits.pCore_characteristic 2 (G := T)
  have hN : (CFSG.pCore 2 T).Normal := inferInstance
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 T := by
      have h1 := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := T)
      rw [h] at h1
      exact h1.of_equiv Subgroup.topEquiv
    haveI : Nontrivial T := IsSimpleGroup.toNontrivial
    exact Group.IsPerfect.not_isNilpotent T hp.isNilpotent

theorem pCoreOf_eq_bot_of_mulEquiv {M T : Type*} [Group M] [Group T] {H : Subgroup M}
    (e : ↥H ≃* T) (hT : CFSG.pCore 2 T = ⊥) : pCoreOf 2 H = ⊥ := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e.symm, hT, Subgroup.map_bot,
    Subgroup.map_bot]

theorem mulAut_mul_conj_mul_inv' {P : Type*} [Group P] (φ : MulAut P) (g : P) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup) in
theorem innerAut_inf_centralizer_eq_map {P : Type*} [Group P]
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) (x : MulAut P) :
    innerAut P ⊓ Subgroup.centralizer ({x} : Set (MulAut P)) =
      (fixSubgroup x).map (MulAut.conj : P →* MulAut P) := by
  ext a
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨g, rfl⟩, hc⟩
    refine ⟨g, ?_, rfl⟩
    rw [mem_fixSubgroup]
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have h1 := mulAut_mul_conj_mul_inv' x g
    have h2 : x * MulAut.conj g * x⁻¹ = MulAut.conj g := by
      rw [← hc, mul_inv_cancel_right]
    exact hinj (h1.symm.trans h2)
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := mulAut_mul_conj_mul_inv' x g
    rw [mem_fixSubgroup.1 hg] at h1
    calc MulAut.conj g * x = (x * MulAut.conj g * x⁻¹) * x := by rw [h1]
      _ = x * MulAut.conj g := by group

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup) in
theorem fixSubgroup_conj {P : Type*} [Group P] (h f : MulAut P) :
    fixSubgroup (h * f * h⁻¹) = (fixSubgroup f).map h.toMonoidHom := by
  ext g
  rw [mem_fixSubgroup, Subgroup.mem_map]
  constructor
  · intro hg
    refine ⟨h⁻¹ g, ?_, by simp⟩
    rw [mem_fixSubgroup]
    apply h.injective
    have e1 : h (h⁻¹ g) = g := by simp
    rw [e1]
    simpa [MulAut.mul_apply] using hg
  · rintro ⟨g', hg', rfl⟩
    rw [mem_fixSubgroup] at hg'
    simp [MulAut.mul_apply, hg']

theorem exists_mul_ne_of_perfect {G : Type*} [Group G] [Nontrivial G] [Group.IsPerfect G] :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have h : commutator G = ⊥ := by
    rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact hc h g
  rw [Group.IsPerfect.commutator_eq_top] at h
  exact top_ne_bot h

theorem isWeaklyLocallyOTwoBalancedWrtP_of_outTwo {M : Type} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime)
    (hOut : ∀ N : Subgroup (MulAut M), IsPGroup 2 N → N ⊓ innerAut M = ⊥ → Nat.card N ≤ 2)
    (hcore : ∀ x : MulAut M, orderOf x = p →
      pCoreOf 2 (innerAut M ⊓ Subgroup.centralizer ({x} : Set (MulAut M))) = ⊥) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine BalanceFromYS.isWeaklyLocallyOTwoBalancedWrtP_of_card_le_two hp fun x hx H hH _ => ?_
  refine hOut _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
  rw [eq_bot_iff, ← hcore x hx]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · exact le_inf inf_le_right
      ((inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans inf_le_right)
  · intro g hg
    have hgH : g ∈ H ⊓ Subgroup.centralizer ({x} : Set (MulAut M)) :=
      Subgroup.mem_inf.2 ⟨hH (Subgroup.mem_inf.1 hg).1, (Subgroup.mem_inf.1 hg).2⟩
    exact Lemma123.mem_normalizer_inf'
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer hgH))
      (Subgroup.le_normalizer (Subgroup.mem_inf.1 hg).1)
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left

end General

section LThree

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

theorem conjAut_mem_innerAut_three [CharP K 3] (A : GL (Fin 3) K) :
    conjAut 3 K A ∈ innerAut (projectiveSL 3 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.coprime_card_units (K := K) 3
  set d : Kˣ := Matrix.GeneralLinearGroup.det A with hd
  set μ : Kˣ := (powCoprime hcop).symm d with hμ
  have hμ3 : μ ^ 3 = d := by
    have h := (powCoprime hcop).apply_symm_apply d
    rwa [powCoprime_apply] at h
  set A' : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A with hA'
  have hdet : (A' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((μ⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hA', Units.val_mul, h1, Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul,
      Fintype.card_fin]
    have h2 : (A : Matrix (Fin 3) (Fin 3) K).det = (d : K) := rfl
    rw [h2, ← hμ3]
    simp
  let g : Matrix.SpecialLinearGroup (Fin 3) K := ⟨(A' : Matrix (Fin 3) (Fin 3) K), hdet⟩
  have htoGL : Matrix.SpecialLinearGroup.toGL g = A' := Units.ext rfl
  have hAeq : A = Matrix.GeneralLinearGroup.scalar (Fin 3) μ * A' := by
    rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have key : conjAut 3 K A = conjAut 3 K A' := by
    calc conjAut 3 K A = conjAut 3 K (Matrix.GeneralLinearGroup.scalar (Fin 3) μ * A') :=
          congrArg _ hAeq
      _ = conjAut 3 K A' := by
          rw [map_mul, CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.conjAut_scalar', one_mul]
  refine ⟨proj 3 K g, ?_⟩
  rw [← conjAut_toGL, htoGL, key]

theorem mem_innerAut_of_semilinear_of_pow_two [CharP K 3] (hodd : Odd (Nat.card (K ≃+* K)))
    {α : MulAut (projectiveSL 3 K)} (hα : α ∈ semilinearAutGroup 3 K) {k : ℕ}
    (hk : α ^ (2 ^ k) = 1) : α ∈ innerAut (projectiveSL 3 K) := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hα
  haveI : (innerAut (projectiveSL 3 K)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  let π := QuotientGroup.mk' (innerAut (projectiveSL 3 K))
  have h1 : π (conjAut 3 K A) = 1 := (QuotientGroup.eq_one_iff _).2 (conjAut_mem_innerAut_three A)
  have h2 : π (fieldAut 3 K σ) ^ Nat.card (K ≃+* K) = 1 := by
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have h3 : π (fieldAut 3 K σ) ^ (2 ^ k) = 1 := by
    have h := congrArg π hk
    rwa [map_pow, map_mul, h1, one_mul, map_one] at h
  have hcop : Nat.Coprime (Nat.card (K ≃+* K)) (2 ^ k) :=
    Nat.Coprime.pow_right _ hodd.coprime_two_right
  have h4 : orderOf (π (fieldAut 3 K σ)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact mul_mem (conjAut_mem_innerAut_three A) h4

theorem card_le_two_of_inf_innerAut_eq_bot [CharP K 3] (hodd : Odd (Nat.card (K ≃+* K)))
    (N : Subgroup (MulAut (projectiveSL 3 K))) (hN : IsPGroup 2 N)
    (hNI : N ⊓ innerAut (projectiveSL 3 K) = ⊥) : Nat.card N ≤ 2 := by
  have hE : ∀ a ∈ N, a ∈ semilinearAutGroup 3 K → a = 1 := by
    intro a ha haE
    obtain ⟨k, hk⟩ := hN ⟨a, ha⟩
    have hk' : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hmem : a ∈ N ⊓ innerAut (projectiveSL 3 K) :=
      ⟨ha, mem_innerAut_of_semilinear_of_pow_two hodd haE hk'⟩
    rw [hNI] at hmem
    exact hmem
  have hR : ∀ a : MulAut (projectiveSL 3 K), a ∈ semilinearAutGroup 3 K ∨
      a * dualAut 3 K ∈ semilinearAutGroup 3 K := fun a =>
    mem_or_mul_dualAut_mem (by rw [(automorphism_generation (n := 3) (K := K) le_rfl).1]; trivial)
  have key : ∀ a ∈ N, ∀ b ∈ N, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    rcases hR a with haE | haE
    · exact absurd (hE a ha haE) ha1
    rcases hR b with hbE | hbE
    · exact absurd (hE b hb hbE) hb1
    have hab : a * b⁻¹ ∈ semilinearAutGroup 3 K := by
      have e : a * b⁻¹ = (a * dualAut 3 K) * (b * dualAut 3 K)⁻¹ := by group
      rw [e]
      exact mul_mem haE (inv_mem hbE)
    exact mul_inv_eq_one.1 (hE _ (mul_mem ha (inv_mem hb)) hab)
  by_cases h : ∃ a ∈ N, a ≠ 1
  · obtain ⟨a, haN, ha1⟩ := h
    have hsub : (N : Set (MulAut (projectiveSL 3 K))) ⊆ {1, a} := fun b hb => by
      by_cases hb1 : b = 1
      · simp [hb1]
      · simp [key b hb a haN hb1 ha1]
    calc Nat.card N = Nat.card (N : Set (MulAut (projectiveSL 3 K))) := rfl
      _ ≤ Nat.card ({1, a} : Set (MulAut (projectiveSL 3 K))) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
  · push Not at h
    have hN1 : N = ⊥ := eq_bot_iff.2 fun b hb => h b hb
    rw [hN1, Subgroup.card_bot]
    norm_num

theorem psl_three_simple_perfect (k : Type*) [Field k] :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) k) ∧
      Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) k) :=
  ⟨(CFSG.LinearGroups.linear_projective_simple (K := k) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1,
    CFSG.LinearGroups.linear_projective_perfect (K := k) (n := 3) (by norm_num) (Or.inl le_rfl)⟩

theorem center_projectiveSL_three_eq_bot (k : Type*) [Field k] :
    Subgroup.center (projectiveSL 3 k) = ⊥ := by
  obtain ⟨hs, hp⟩ := psl_three_simple_perfect k
  let e := LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k
  haveI : IsSimpleGroup (projectiveSL 3 k) := e.symm.isSimpleGroup
  haveI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 3) k) := IsSimpleGroup.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_perfect (G := Matrix.ProjectiveSpecialLinearGroup (Fin 3) k)
  refine CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup
    ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup) in
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield) in
theorem pCoreOf_innerAut_centralizer_eq_bot_of_outer [CharP K 3] (hK : Nat.card K = 3 ^ 13)
    {x : MulAut (projectiveSL 3 K)} (hx : orderOf x = 13)
    (hout : x ∉ innerAut (projectiveSL 3 K)) :
    pCoreOf 2 (innerAut (projectiveSL 3 K) ⊓ Subgroup.centralizer ({x} : Set _)) = ⊥ := by
  have hx13 : x ^ 13 = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨A, σ, hxe⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd
    (by norm_num : 3 ≤ 3) (by decide : Odd 13) hx13
  have hmem : x ∈ semilinearAutGroup 3 K := hxe ▸ mul_mem
    (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
    (fieldAut_mem_semilinearAutGroup σ)
  have hlin : x ∉ linearAutGroup 3 K := fun h => hout (by
    obtain ⟨A', rfl⟩ := mem_linearAutGroup_iff.1 h
    exact conjAut_mem_innerAut_three A')
  obtain ⟨-, τ, hτ, ⟨h, -, hxh⟩, -⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      Nat.prime_three (by norm_num : 1 ≤ 13) (by norm_num : 3 ≤ 3) hK (by norm_num : Nat.Prime 13)
      x hmem hlin hx
  have hτ13 : τ ^ 13 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hpK : ¬ 13 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    decide
  have hC : fixSubgroup (fieldAut 3 K τ) =
      (CFSG.RankThree.PartOne.linearSubfieldInclusion 3 (semilinearFixedSubfield τ)).range :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.fixSubgroup_fieldAut_eq_range (by norm_num)
      (by norm_num : Nat.Prime 13) hτ13 hpK
  have hinj := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot
    (center_projectiveSL_three_eq_bot K)
  set k := semilinearFixedSubfield τ
  set j := CFSG.RankThree.PartOne.linearSubfieldInclusion 3 k
  let φ : projectiveSL 3 k →* MulAut (projectiveSL 3 K) :=
    (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).comp (h.toMonoidHom.comp j)
  have hφ : Function.Injective φ :=
    hinj.comp (h.injective.comp (CFSG.RankThree.PartOne.linearSubfieldInclusion_injective
      (by norm_num) k))
  have heq : innerAut (projectiveSL 3 K) ⊓ Subgroup.centralizer ({x} : Set _) = φ.range := by
    rw [innerAut_inf_centralizer_eq_map hinj, hxh, fixSubgroup_conj, hC, MonoidHom.range_eq_map,
      MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map]
    rfl
  obtain ⟨hs, hp⟩ := psl_three_simple_perfect k
  haveI : Finite k := inferInstance
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 3) k) := inferInstance
  let e : ↥(innerAut (projectiveSL 3 K) ⊓ Subgroup.centralizer ({x} : Set _)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) k :=
    ((MulEquiv.subgroupCongr heq).trans (MonoidHom.ofInjective hφ).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).symm
  exact pCoreOf_eq_bot_of_mulEquiv e pCore_two_eq_bot_of_simple

theorem proj_three_injective [CharP K 3] : Function.Injective (proj 3 K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [proj_eq_one_iff, scalars_eq_center, CFSG.RankThree.PartOne.SRC.center_SL3_eq_bot] at hA
  exact hA

theorem false_of_commute_of_orderOf [CharP K 3] (hK : Nat.card K = 3 ^ 13) {s g : projectiveSL 3 K}
    (hs : orderOf s = 2) (hg : orderOf g = 13) (hsg : s * g = g * s) : False := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨S', rfl⟩ := proj_surjective 3 K s
  obtain ⟨G', rfl⟩ := proj_surjective 3 K g
  have hinj := proj_three_injective (K := K)
  have hS' : orderOf S' = 2 := by rw [← orderOf_injective _ hinj S']; exact hs
  have hG' : orderOf G' = 13 := by rw [← orderOf_injective _ hinj G']; exact hg
  have hSG : S' * G' = G' * S' := hinj (by rw [map_mul, map_mul, hsg])
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K 3] at h'
    norm_num at h'
  let ι : Matrix.SpecialLinearGroup (Fin 3) K →* CFSG.Open.StatedSL 3 K :=
    (Matrix.SpecialLinearGroup.toGL).codRestrict (CFSG.Open.StatedSL 3 K) fun A =>
      CFSG.Open.StatedAPI.mem_statedSL_iff.2 A.2
  have hι : Function.Injective ι := fun A B h => by
    have h1 := congrArg (fun x : CFSG.Open.StatedSL 3 K =>
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    exact Subtype.ext h1
  have ha : ι S' * ι S' = 1 := by
    rw [← map_mul, ← sq, ← hS', pow_orderOf_eq_one, map_one]
  have ha1 : ι S' ≠ 1 := by
    intro h
    have : S' = 1 := hι (by rw [h, map_one])
    rw [this, orderOf_one] at hS'
    norm_num at hS'
  obtain ⟨φ, hφ, hrange⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.exists_phi h2
    (CFSG.Open.StatedSL 3 K) (fun A => CFSG.Open.StatedAPI.mem_statedSL_iff) ha ha1
  have hb : ι G' ∈ φ.range := by
    rw [hrange, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hSG]
  obtain ⟨c, hc⟩ := hb
  have hco : orderOf c = 13 := by
    rw [← orderOf_injective φ hφ c, hc, orderOf_injective ι hι, hG']
  have hdvd : 13 ∣ Nat.card (GL (Fin 2) K) := hco ▸ orderOf_dvd_natCard c
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK] at hdvd
  revert hdvd
  decide

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup) in
theorem pCoreOf_innerAut_centralizer_eq_bot_of_inner [CharP K 3] (hK : Nat.card K = 3 ^ 13)
    {x : MulAut (projectiveSL 3 K)} (hx : orderOf x = 13) (hin : x ∈ innerAut (projectiveSL 3 K)) :
    pCoreOf 2 (innerAut (projectiveSL 3 K) ⊓ Subgroup.centralizer ({x} : Set _)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot
    (center_projectiveSL_three_eq_bot K)
  obtain ⟨g, rfl⟩ := hin
  have hg : orderOf g = 13 := by rw [← orderOf_injective _ hinj g]; exact hx
  set Q := pCoreOf 2 (innerAut (projectiveSL 3 K) ⊓ Subgroup.centralizer
    ({MulAut.conj g} : Set (MulAut (projectiveSL 3 K)))) with hQ
  by_contra hne
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  haveI : Finite (MulAut (projectiveSL 3 K)) := inferInstance
  obtain ⟨t, ht⟩ : ∃ t : Q, orderOf t = 2 := by
    haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have := Finite.one_lt_card (α := Q)
      omega
    exact exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  have htQ : (t : MulAut (projectiveSL 3 K)) ∈ innerAut (projectiveSL 3 K) ⊓
      Subgroup.centralizer ({MulAut.conj g} : Set _) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ t.2
  rw [innerAut_inf_centralizer_eq_map hinj] at htQ
  obtain ⟨s, hs, hst⟩ := htQ
  have hs' : g * s * g⁻¹ = s := by
    have h := mem_fixSubgroup.1 hs
    rwa [MulAut.conj_apply] at h
  have hso : orderOf s = 2 := by
    rw [← orderOf_injective _ hinj s, hst, Subgroup.orderOf_coe, ht]
  refine false_of_commute_of_orderOf hK hso hg ?_
  calc s * g = (g * s * g⁻¹) * g := by rw [hs']
    _ = g * s := by group

theorem isWeaklyLocallyOTwoBalancedWrtP_projectiveSL_three [CharP K 3] (hK : Nat.card K = 3 ^ 13) :
    IsWeaklyLocallyOTwoBalancedWrtP 13 1 (projectiveSL 3 K) := by
  have hodd : Odd (Nat.card (K ≃+* K)) := by
    rw [(card_ringAut_and_isCyclic Nat.prime_three K hK).1]
    decide
  refine isWeaklyLocallyOTwoBalancedWrtP_of_outTwo (by norm_num)
    (fun N hN hNI => card_le_two_of_inf_innerAut_eq_bot hodd N hN hNI) fun x hx => ?_
  by_cases hin : x ∈ innerAut (projectiveSL 3 K)
  · exact pCoreOf_innerAut_centralizer_eq_bot_of_inner hK hx hin
  · exact pCoreOf_innerAut_centralizer_eq_bot_of_outer hK hx hin

theorem input19_18b_holds : BalanceFromYS.Input19_18b := by
  intro S _ _ hL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  haveI : CharP F 3 := finite_field_prime_power_characteristic Nat.prime_three (by norm_num) hF
  let e' : S ≃* projectiveSL 3 F :=
    e.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)).symm
  exact (BalanceFromYS.isWeaklyLocallyOTwoBalancedWrtP_congr e').2
    (isWeaklyLocallyOTwoBalancedWrtP_projectiveSL_three hF)

end LThree

section ChevThree

open TauCeti

theorem char_exp_of_fieldOrder_three {d : LieTypeIndex} (hd : d.fieldOrder = 3) :
    d.characteristic = 3 ∧ d.fieldExponent = 1 := by
  rw [LieTypeIndex.fieldOrder_eq_characteristic_pow] at hd
  exact (Nat.Prime.pow_eq_iff Nat.prime_three).1 hd

theorem exists_lieModel_of_fieldOrder_three
    {G : Type} [Group G] (d : ValidLieTypeIndex) (hd : d.1.fieldOrder = 3) (e : G ≃* d.Group) :
    ∃ (t : StatedLieTag) (n : ℕ), CFSG.Blueprint.LieModel G t n 3 1 := by
  obtain ⟨d, hv⟩ := d
  change d.fieldOrder = 3 at hd
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have h2 : ∀ q : PrimePower, q.p = 3 → q.p ≠ 2 := fun q h => by rw [h]; norm_num
  obtain ⟨hc, hx⟩ := char_exp_of_fieldOrder_three hd
  cases d with
  | A r q =>
    simp only [LieTypeIndex.characteristic_A, LieTypeIndex.fieldExponent_A] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have h := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
      (CFSG.Models.lieModel_A r q hv e)
    rw [hp, hf] at h
    exact ⟨_, _, h⟩
  | twistedA r q =>
    simp only [LieTypeIndex.characteristic_twistedA, LieTypeIndex.fieldExponent_twistedA] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have h := CFSG.Models.lieModel_twistedA r q hv e
    simp only [ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent,
      LieTypeIndex.characteristic_twistedA, LieTypeIndex.fieldExponent_twistedA] at h
    have h' := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) h
    rw [hp, hf] at h'
    exact ⟨_, _, h'⟩
  | B r q =>
    simp only [LieTypeIndex.characteristic_B, LieTypeIndex.fieldExponent_B] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · have h' := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) h
      rw [hp, hf] at h'
      exact ⟨_, _, h'⟩
    · have h' := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) h
      rw [hp, hf] at h'
      exact ⟨_, _, h'⟩
  | C r q =>
    simp only [LieTypeIndex.characteristic_C, LieTypeIndex.fieldExponent_C] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have h := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
      (CFSG.Models.lieModel_C r q hv e)
    rw [hp, hf] at h
    exact ⟨_, _, h⟩
  | D r q =>
    simp only [LieTypeIndex.characteristic_D, LieTypeIndex.fieldExponent_D] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have h := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
      (CFSG.Models.lieModel_D r q hv e)
    rw [hp, hf] at h
    exact ⟨_, _, h⟩
  | twistedD r q =>
    simp only [LieTypeIndex.characteristic_twistedD, LieTypeIndex.fieldExponent_twistedD] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have h := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
      (CFSG.Models.lieModel_twistedD r q hv e)
    rw [hp, hf] at h
    exact ⟨_, _, h⟩
  | E6 q =>
    simp only [LieTypeIndex.characteristic_E6, LieTypeIndex.fieldExponent_E6] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e6 q hv (h2 q hp) e⟩
    rw [hp, hf] at hm
    exact ⟨.E6, 0, Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | E7 q =>
    simp only [LieTypeIndex.characteristic_E7, LieTypeIndex.fieldExponent_E7] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E7 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e7 q hv (h2 q hp) e⟩
    rw [hp, hf] at hm
    exact ⟨.E7, 0, Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | E8 q =>
    simp only [LieTypeIndex.characteristic_E8, LieTypeIndex.fieldExponent_E8] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E8 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e8 q hv (h2 q hp) e⟩
    rw [hp, hf] at hm
    exact ⟨.E8, 0, Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | F4 q =>
    simp only [LieTypeIndex.characteristic_F4, LieTypeIndex.fieldExponent_F4] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .F4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.f4 q hv (h2 q hp) e⟩
    rw [hp, hf] at hm
    exact ⟨.F4, 0, Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | G2 q =>
    simp only [LieTypeIndex.characteristic_G2, LieTypeIndex.fieldExponent_G2] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have h3 : 3 ≤ q.p ^ q.exponent := by
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using hr
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.g2 q hv (h2 q hp) e⟩
    rw [hp, hf] at hm
    exact ⟨.G2, 0, Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | twistedE6 q =>
    simp only [LieTypeIndex.characteristic_twistedE6, LieTypeIndex.fieldExponent_twistedE6] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .twistedE6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv (h2 q hp) (by decide) e⟩
    rw [hp, hf] at hm
    exact ⟨.twistedE6, 0, Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
      hm⟩)⟩
  | trialityD4 q =>
    simp only [LieTypeIndex.characteristic_trialityD4, LieTypeIndex.fieldExponent_trialityD4] at hc hx
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := ⟨hc, hx⟩
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv (h2 q hp) (by decide) e⟩
    rw [hp, hf] at hm
    exact ⟨.trialityD4, 0, Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
      hm⟩)⟩
  | suzuki m =>
    simp only [LieTypeIndex.characteristic_suzuki] at hc
    omega
  | reeG2 m =>
    have hm : 1 ≤ m := by simpa [LieTypeIndex.inStandardRange_iff] using hr
    simp only [LieTypeIndex.fieldExponent_reeG2] at hx
    omega
  | reeF4 m =>
    simp only [LieTypeIndex.characteristic_reeF4] at hc
    omega
  | tits =>
    simp only [LieTypeIndex.characteristic_tits] at hc
    omega

section DFour

open CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)

theorem inner_of_gates_three {K : Type} [Field K] [Finite K] {d : ℕ} (hK : Nat.card K = 3)
    (Q : QuadraticForm K (Fin d → K)) (hG : OrthogonalGates Q 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (α : MulAut (matrixProjectiveDerived Q)) (hα : α ^ p = 1) :
    α ∈ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, k₂, hk₂⟩, -, -, hEA, hpK, -, -⟩ := hG
  have hE : α ∈ matrixProjectiveImage Q := by
    have hA : IsPGroup p (Subgroup.zpowers α) := by
      intro x
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
    have := hpK p hp hp3 _ hA (Subgroup.mem_zpowers α)
    rw [← hEA]
    exact familyOrbitKernel_le Q this
  have hsub : Subsingleton (K ≃+* K) := ⟨fun σ τ =>
    (CFSG.ClassicalInvolution.Q3.Q3T.ringEquiv_eq_refl_of_card_three hK σ).trans
      (CFSG.ClassicalInvolution.Q3.Q3T.ringEquiv_eq_refl_of_card_three hK τ).symm⟩
  have hD : α ∈ (linearConjugationHom Q).range := by
    have h1 : (⟨α, hE⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]; exact Subsingleton.elim _ _
    rw [hψker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hp2 : p ≠ 2 := by omega
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  set H := OuterAutomorphisms.inner (matrixProjectiveDerived Q) with hH
  set D := (linearConjugationHom Q).range with hDdef
  have : H.Normal := OuterAutomorphisms.inner_normal _
  set y : D := ⟨α, hD⟩ with hydef
  have hy : y ^ p = 1 := Subtype.ext (by simpa [hydef] using hα)
  have h1 : orderOf (y : D ⧸ H.subgroupOf D) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : D ⧸ H.subgroupOf D) ∣ 2 ^ k₂ := by
    rw [← hk₂, Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (y : D ⧸ H.subgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_right k₂ hcop2).coprime_dvd_left h1) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem mem_inner_of_pOmegaPlus_four {S : Type} [Group S]
    (hM : StatedClassicalModel S .POmegaPlus 4 3 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (x : MulAut S) (hx : x ^ p = 1) : x ∈ OuterAutomorphisms.inner S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 3 1 hM K hK e
  have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
  obtain ⟨y, hy⟩ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_conj_of_mulEquiv
    (coordinatePlusWitnessEquiv K e) p
    (fun α hα => inner_of_gates_three hK3 _ hgates hp hp3 α hα) x hx
  exact ⟨y, hy.symm⟩

end DFour

section TrialityD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
open CFSG.ClassicalInvolution.Q3.Q3T (F27 σe27 σ27)
open CFSG.ComponentClassification

theorem td4_mem_inner_of_pow_eq_one
    (β : MulAut (twistedGroup σ27)) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hβ : β ^ p = 1) :
    β ∈ OuterAutomorphisms.inner (twistedGroup σ27) := by
  have hσ' : ∀ c, σe27 c = c ^ (3 ^ 1) := fun c => iterateFrobeniusEquiv_def F27 3 1 c
  have hK : Nat.card F27 = (3 ^ 1) ^ 3 := by
    rw [GaloisField.card 3 (3 * 1) (by norm_num)]
    norm_num
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcard, -⟩ := odd_triality_exact_automorphism_normal_form
    Nat.prime_three (by norm_num) le_rfl F27 hK σe27 hσ'
  have hrange : (twistedIncl σ27).range = graphFixedRootGroup TwistTag.D4 F27 σ27 :=
    range_twistedIncl_eq (p := 3) (by norm_num) 1 le_rfl
  have hC : graphFixedRootGroup TwistTag.D4 F27 σ27 =
      graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom := rfl
  let ι : twistedGroup σ27 ≃* ↥(graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom) :=
    (MonoidHom.ofInjective (twistedIncl_injective σ27)).trans
      (MulEquiv.subgroupCongr (hrange.trans hC))
  have hγp : MulAut.congr ι β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hΘ : Θ (MulAut.congr ι β) = 1 := by
    have h3 : Θ (MulAut.congr ι β) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := F27 ≃+* F27) (x := Θ (MulAut.congr ι β))
      rwa [hcard] at h
    have hp' : Θ (MulAut.congr ι β) ^ p = 1 := by rw [← map_pow, hγp, map_one]
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hp')
      (orderOf_dvd_of_pow_eq_one h3))
  obtain ⟨c, hc⟩ : MulAut.congr ι β ∈
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom →* _).range := by
    rw [← hker]
    exact hΘ
  refine ⟨ι.symm c, (MulAut.congr ι).injective ?_⟩
  rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hc]

end TrialityD4

theorem input7_1Chev3_holds :
    BalanceFromYS.Input7_1Chev3 := by
  intro p hp hp3 S _ _ hS hlie x hx
  haveI := hS
  obtain ⟨idx, ⟨e⟩, hfo⟩ := hlie
  obtain ⟨t, n, hMq⟩ := exists_lieModel_of_fieldOrder_three idx hfo e
  obtain ⟨-, hnt, -⟩ := CFSG.LieType.Catalog.lieModel_finite_simple _ t n 3 1 hMq
  have hZ : Subgroup.center S = ⊥ := by
    rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne (S ⧸ Subgroup.center S)
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [QuotientGroup.eq]
      rw [h]
      exact Subgroup.mem_top _
  let eS : S ≃* S ⧸ Subgroup.center S := Prop1116Design.mulEquivQuotCenterOfEqBot hZ
  have hM : CFSG.Blueprint.LieModel S t n 3 1 := CFSG.Blueprint.LieModel.of_mulEquiv eS.symm hMq
  have hadm := hM.admissible
  have hG2 : t ≠ .twistedG2 := by
    rintro rfl
    obtain ⟨-, -, -, -, -, h3⟩ := hadm
    omega
  have hFT := CFSG.ComponentClassification.RankTwoOddLie.isFundTag_of_admissible hadm
    (by norm_num) hG2
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t n 3 1
    Nat.prime_three (by norm_num) hFT hadm S hM
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two (by omega)) (orderOf_dvd_of_pow_eq_one hx)
  by_cases hD4 : t = .POmegaPlus ∧ n = 4
  · obtain ⟨rfl, rfl⟩ := hD4
    exact mem_inner_of_pOmegaPlus_four (hM.statedClassicalModel (by decide)) hp hp3 x hx
  by_cases hT : t = .trialityD4
  · subst hT
    obtain rfl : n = 0 := hadm.2.2
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [CFSG.ClassicalInvolution.Q3.exc3_center_trialityD4 0 Nat.prime_three] at hker
      exact le_bot_iff.mp hker
    obtain ⟨y, hy⟩ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_conj_of_mulEquiv
      (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩).symm p
      (fun β hβ => td4_mem_inner_of_pow_eq_one β hp (by omega) hβ) x hx
    exact ⟨y, hy.symm⟩
  exact CFSG.ClassicalInvolution.Q3.TL4.oddAut_inner_of_cover hD4 hT hFT hadm ψ hψ hker hZ x hodd

end ChevThree

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1918
