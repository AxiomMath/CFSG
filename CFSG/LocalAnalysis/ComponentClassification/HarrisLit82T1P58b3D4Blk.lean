module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDBlk
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat isoOrthGL
  trans_commutator isQuasisimple_trans)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.LocalAnalysis.ComponentInitial
  (orthogonal_low_dimensional_fixed_derived_component_coverage)
open P58b3 (rhoL rhoR)
open scoped MatrixGroups

namespace P58b3D4

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem mem_matrixDerived_of_odd {Q : QuadraticForm K (Fin d → K)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) (hodd : Odd (orderOf g)) :
    g ∈ matrixDerived Q := by
  obtain ⟨-, -, -, -, -, -, hodd', -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  have h1 := hodd' (matrixLinearIso g) hg (by rwa [MulEquiv.orderOf_eq])
  rw [← CFSG.RankThree.PartOne.KCOrthogonalAut.map_matrixDerived Q] at h1
  obtain ⟨z, hz, hzx⟩ := h1
  rwa [matrixLinearIso.injective hzx] at hz

omit [Finite K] in
theorem exists_totallySingular_three {Q : QuadraticForm K (Fin d → K)} (hd : d = 8)
    (hQ : GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  classical
  obtain ⟨W, hW, hWs⟩ := hQ
  rw [Module.finrank_fin_fun] at hW
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank (R := K) (M := W)
    (n := 3) (by omega)
  refine ⟨(Submodule.span K (s : Set W)).map W.subtype, ?_, ?_⟩
  · rw [Submodule.finrank_map_subtype_eq, finrank_span_finset_eq_card hli, hs]
  · rintro _ ⟨x, -, rfl⟩
    exact hWs _ x.2

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

omit [Finite K] in
theorem commute_sign_of_odd {J : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) {B : matrixDerived (oQ (diagGL hw))}
    (hB : projH _ B ∈ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hodd : Odd (orderOf B)) : (B : GL (Fin d) K) * signGL K J = signGL K J * B := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, projH_eq_projH_iff] at hB
  obtain ⟨c, hc⟩ := mem_subgroupOf.mp hB
  set s := signGL K J with hs
  set b := (B : GL (Fin d) K) with hb
  set C := GeneralLinearGroup.scalar (Fin d) c with hCdef
  have hC : ∀ g : GL (Fin d) K, g * C = C * g := fun g => (commute_scalar c g).eq
  have hss : s * s = 1 := mul_eq_one_iff_eq_inv.mpr (signGL_inv (K := K) J).symm
  have h1 : s * b = b * s * C := by
    have e : C = (b * s)⁻¹ * (s * b) := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul]
    rw [e]
    group
  have hconj : s * b * s⁻¹ = b * C := by
    calc s * b * s⁻¹ = b * (s * C) * s⁻¹ := by rw [h1]; group
      _ = b * (C * s) * s⁻¹ := by rw [hC s]
      _ = b * C := by group
  have hpow : ∀ n : ℕ, s * b ^ n * s⁻¹ = b ^ n * C ^ n := fun n => by
    rw [← conj_pow, hconj, (Commute.mul_pow (hC b) n)]
  have hbm : b ^ orderOf B = 1 := by
    rw [hb, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  have hCm : C ^ orderOf B = 1 := by
    have h := hpow (orderOf B)
    rw [hbm, mul_one, mul_inv_cancel, one_mul] at h
    exact h.symm
  have hC2 : C * C = 1 := by
    have e : b = b * C * C := by
      calc b = s * s * b * (s * s)⁻¹ := by rw [hss]; group
        _ = s * (s * b * s⁻¹) * s⁻¹ := by group
        _ = s * b * (C * s⁻¹) := by rw [hconj]; group
        _ = s * b * (s⁻¹ * C) := by rw [hC s⁻¹]
        _ = b * C * C := by rw [← mul_assoc, hconj]
    have e' : b * 1 = b * (C * C) := by rw [mul_one, ← mul_assoc]; exact e
    exact (mul_left_cancel e').symm
  have hC1 : C = 1 := by
    obtain ⟨j, hj⟩ := hodd
    rw [hj, pow_succ, pow_mul, sq, hC2, one_pow, one_mul] at hCm
    exact hCm
  rw [h1, hC1, mul_one]

omit [Finite K] in
theorem eq_one_of_mem_oIsoBlock_compl {J : Finset (Fin d)} {g : GL (Fin d) K}
    (hg : g ∈ oIsoBlock K hw J) (hg' : g ∈ oIsoBlock K hw Jᶜ) : g = 1 := by
  rw [mem_oIsoBlock_iff] at hg hg'
  apply Units.ext
  ext i j
  rw [Units.val_one, Matrix.one_apply]
  by_cases hi : i ∈ J
  · exact hg'.2 i j (Or.inl (by simpa using hi))
  · exact hg.2 i j (Or.inl hi)

omit [Finite K] in
theorem exists_block_of_pow_eq_one (hK : ringChar K ≠ 2) {J I : Finset (Fin d)}
    (hI : I = J ∨ I = Jᶜ) {B : GL (Fin d) K}
    (hBI : B ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hB : B * signGL K J = signGL K J * B) {m : ℕ} (hm : B ^ m = 1) :
    ∃ B₁ ∈ oIsoBlock K hw I, ∃ B₂ ∈ oIsoBlock K hw Iᶜ, B = B₁ * B₂ ∧ B₁ * B₂ = B₂ * B₁ ∧
      B₁ ^ m = 1 ∧ B₂ ^ m = 1 := by
  obtain ⟨B₁, hB₁, B₂, hB₂, rfl⟩ := exists_block_mul_of_commute hK hw J hBI hB
  have hc : B₁ * B₂ = B₂ * B₁ := commute_of_mem_oIsoBlock hw hB₁ hB₂
  have hpow : B₁ ^ m * B₂ ^ m = 1 := by rw [← (Commute.mul_pow hc m), hm]
  have h1 : B₁ ^ m = 1 := by
    refine eq_one_of_mem_oIsoBlock_compl hw (pow_mem hB₁ m) ?_
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact inv_mem (pow_mem hB₂ m)
  have h2 : B₂ ^ m = 1 := by rw [h1, one_mul] at hpow; exact hpow
  rcases hI with rfl | rfl
  · exact ⟨B₁, hB₁, B₂, hB₂, rfl, hc, h1, h2⟩
  · exact ⟨B₂, hB₂, B₁, by rwa [compl_compl], hc, hc.symm, h2, h1⟩

theorem nonempty_oIsoBlock_equiv_det (hK : ringChar K ≠ 2) {I : Finset (Fin d)}
    (hI4 : I.card = 4) (hIc : Iᶜ.Nonempty) (hq : ¬ IsQuasisimple (blockP K hw I)) :
    Nonempty (oIsoBlock K hw I ≃* DeterminantIsometries K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd' : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  obtain ⟨eP⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at eP
  have hq' : ¬ IsQuasisimple (Burgoyne.C.omegaR (diagGL (wRes_ne_zero hw I))) := fun h =>
    hq (LocalCores.isQuasisimple_of_mulEquiv eP.symm h)
  set R := diagGL (wRes_ne_zero hw I) with hRdef
  have hR : (R : Matrix (Fin I.card) (Fin I.card) K)ᵀ = R := diagGL_transpose _
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin I.card → K) = 4 := by rw [Module.finrank_fin_fun, hI4]
  set e₁ := isoOrthGL hK R hR with he₁
  obtain ⟨S, hS2, hSQ⟩ : ∃ S : Submodule K (Fin I.card → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, Q x = 0 := by
    by_contra hS
    obtain ⟨-, -, -, -, h4n, -, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
      Q hQnd (Or.inl ⟨hodd', Or.inr (Or.inl hdim)⟩)
    obtain ⟨-, -, -, -, -, -, -, -, hq''⟩ := h4n hodd' hdim hS
    apply hq'
    have h := isQuasisimple_trans e₁ hq''
    rwa [trans_commutator] at h
  obtain ⟨-, e₂, -, -, -⟩ := split_four_determinant_form_isometry Q hQnd hdim S hS2 hSQ
  exact ⟨(oIsoBlockEquiv hw I).symm.trans (e₁.symm.trans e₂)⟩

abbrev blockFactor {I : Finset (Fin d)} (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K)
    (ρ₀ : SL(2, K) →* DeterminantIsometries K) : SL(2, K) →* GL (Fin d) K :=
  (oIsoBlock K hw I).subtype.comp (Φ.symm.toMonoidHom.comp ρ₀)

omit [Finite K] in
theorem blockFactor_mem {I : Finset (Fin d)} (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K)
    (ρ₀ : SL(2, K) →* DeterminantIsometries K) (A : SL(2, K)) :
    blockFactor hw Φ ρ₀ A ∈ oIsoBlock K hw I :=
  (Φ.symm (ρ₀ A)).2

omit [Finite K] in
theorem blockFactor_injective {I : Finset (Fin d)}
    (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K) {ρ₀ : SL(2, K) →* DeterminantIsometries K}
    (hρ₀ : Function.Injective ρ₀) : Function.Injective (blockFactor hw Φ ρ₀) :=
  (oIsoBlock K hw I).subtype_injective.comp (Φ.symm.injective.comp hρ₀)

omit [Finite K] in
theorem exists_conj_eq_of_mem_leftRightImage {ρ₀ : SL(2, K) →* DeterminantIsometries K}
    (hρ₀ : ρ₀ = rhoL ∨ ρ₀ = rhoR) {g : DeterminantIsometries K} (hg : g ∈ leftRightImage K)
    (A : SL(2, K)) : ∃ A' : SL(2, K), g * ρ₀ A * g⁻¹ = ρ₀ A' := by
  rcases hρ₀ with rfl | rfl
  · obtain ⟨A', hA'⟩ := (normal_subgroupOf_iff P58b3.range_rhoL_le).mp P58b3.normal_range_rhoL
      _ g ⟨A, rfl⟩ hg
    exact ⟨A', hA'.symm⟩
  · obtain ⟨A', hA'⟩ := (normal_subgroupOf_iff P58b3.range_rhoR_le).mp P58b3.normal_range_rhoR
      _ g ⟨A, rfl⟩ hg
    exact ⟨A', hA'.symm⟩

omit [Finite K] in
theorem conj_blockFactor_of_odd (hK : ringChar K ≠ 2) {J I : Finset (Fin d)}
    (hI : I = J ∨ I = Jᶜ) (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K)
    {ρ₀ : SL(2, K) →* DeterminantIsometries K} (hρ₀ : ρ₀ = rhoL ∨ ρ₀ = rhoR) {B : GL (Fin d) K}
    (hBI : B ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hB : B * signGL K J = signGL K J * B) (hodd : Odd (orderOf B)) (A : SL(2, K)) :
    ∃ A' : SL(2, K), B * blockFactor hw Φ ρ₀ A * B⁻¹ = blockFactor hw Φ ρ₀ A' := by
  obtain ⟨B₁, hB₁, B₂, hB₂, rfl, -, hB₁m, -⟩ :=
    exists_block_of_pow_eq_one hw hK hI hBI hB (pow_orderOf_eq_one B)
  set b₁ : oIsoBlock K hw I := ⟨B₁, hB₁⟩ with hb₁
  have hb₁o : Odd (orderOf (Φ b₁)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hB₁m)
  obtain ⟨A', hA'⟩ := exists_conj_eq_of_mem_leftRightImage hρ₀
    (P58b3.mem_leftRightImage_of_odd hb₁o) A
  refine ⟨A', ?_⟩
  have hcomm : blockFactor hw Φ ρ₀ A * B₂ = B₂ * blockFactor hw Φ ρ₀ A :=
    commute_of_mem_oIsoBlock hw (blockFactor_mem hw Φ ρ₀ A) hB₂
  have e : B₁ * B₂ * blockFactor hw Φ ρ₀ A * (B₁ * B₂)⁻¹ =
      B₁ * blockFactor hw Φ ρ₀ A * B₁⁻¹ := by
    calc B₁ * B₂ * blockFactor hw Φ ρ₀ A * (B₁ * B₂)⁻¹ =
        B₁ * (B₂ * blockFactor hw Φ ρ₀ A) * B₂⁻¹ * B₁⁻¹ := by group
      _ = B₁ * (blockFactor hw Φ ρ₀ A * B₂) * B₂⁻¹ * B₁⁻¹ := by rw [hcomm]
      _ = B₁ * blockFactor hw Φ ρ₀ A * B₁⁻¹ := by group
  rw [e]
  have e2 : Φ.symm (ρ₀ A') = b₁ * Φ.symm (ρ₀ A) * b₁⁻¹ := by
    rw [← hA', map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  change B₁ * ((Φ.symm (ρ₀ A) : oIsoBlock K hw I) : GL (Fin d) K) * B₁⁻¹ =
    ((Φ.symm (ρ₀ A') : oIsoBlock K hw I) : GL (Fin d) K)
  rw [e2]
  rfl

theorem blockFactor_mem_matrixDerived (hK3 : Nat.card K = 3) {I : Finset (Fin d)}
    (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K) (ρ₀ : SL(2, K) →* DeterminantIsometries K)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, oQ (diagGL hw) x = 0) (A : SL(2, K)) :
    blockFactor hw Φ ρ₀ A ∈ matrixDerived (oQ (diagGL hw)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hA : A ∈ closure {x : SL(2, K) | orderOf x = 3} := by
    rw [CFSG.LieType.HighestRoot.closure_orderOf_three_eq_top_of_mulEquiv hK3
      (MulEquiv.refl _)]
    exact mem_top A
  have hle : (closure {x : SL(2, K) | orderOf x = 3}).map (blockFactor hw Φ ρ₀) ≤
      matrixDerived (oQ (diagGL hw)) := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu3 : orderOf u = 3 := hu
    refine mem_matrixDerived_of_odd
      (CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _
        (diagGL_transpose hw)) hT ?_ ?_
    · rw [mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw)]
      exact oIsoBlock_le hw I (blockFactor_mem hw Φ ρ₀ u)
    · have hd : orderOf (blockFactor hw Φ ρ₀ u) ∣ 3 := hu3 ▸ orderOf_map_dvd _ u
      exact Odd.of_dvd_nat (by decide) hd
  exact hle ⟨A, hA, rfl⟩

abbrev blockFactorP (hK3 : Nat.card K = 3) {I : Finset (Fin d)}
    (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K) (ρ₀ : SL(2, K) →* DeterminantIsometries K)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, oQ (diagGL hw) x = 0) :
    SL(2, K) →* StatedProj (matrixDerived (oQ (diagGL hw))) :=
  (projH _).comp ((blockFactor hw Φ ρ₀).codRestrict _
    (blockFactor_mem_matrixDerived hw hK3 Φ ρ₀ hT))

theorem blockFactorP_apply (hK3 : Nat.card K = 3) {I : Finset (Fin d)}
    (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K) (ρ₀ : SL(2, K) →* DeterminantIsometries K)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, oQ (diagGL hw) x = 0) (A : SL(2, K)) :
    blockFactorP hw hK3 Φ ρ₀ hT A =
      projH _ ⟨blockFactor hw Φ ρ₀ A, blockFactor_mem_matrixDerived hw hK3 Φ ρ₀ hT A⟩ :=
  rfl

theorem blockFactorP_injective (hK3 : Nat.card K = 3) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K) {ρ₀ : SL(2, K) →* DeterminantIsometries K}
    (hρ₀ : Function.Injective ρ₀)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, oQ (diagGL hw) x = 0) :
    Function.Injective (blockFactorP hw hK3 Φ ρ₀ hT) := by
  intro A A' h
  have h' := P58b3L.projH_inj_of_mem_oIsoBlock hw hIc
    (B := ⟨_, blockFactor_mem_matrixDerived hw hK3 Φ ρ₀ hT A⟩)
    (B' := ⟨_, blockFactor_mem_matrixDerived hw hK3 Φ ρ₀ hT A'⟩) (blockFactor_mem hw Φ ρ₀ A)
    (blockFactor_mem hw Φ ρ₀ A') h
  have h'' : blockFactor hw Φ ρ₀ A = blockFactor hw Φ ρ₀ A' :=
    congrArg (fun u : matrixDerived (oQ (diagGL hw)) => (u : GL (Fin d) K)) h'
  exact blockFactor_injective hw Φ hρ₀ h''

end P58b3D4

end CFSG.ComponentClassification.HarrisLit.T1
