module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE6Embed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryNuGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycleGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Levi
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Stab

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Word

@[expose] def l0E6 : List (Fin (Tag.rank .E6)) :=
  [idxE6 3, idxE6 4, idxE6 5, idxE6 2, idxE6 3, idxE6 4, idxE6 0, idxE6 2, idxE6 3]

theorem l0E6_mem_J : ∀ j ∈ l0E6, j ∈ JE6 := by
  unfold l0E6 JE6 idxE6
  decide +kernel

theorem l0E6_comm :
    ((coxeterSystem .E6).wordProd l0E6 * rootReflection thetaE6) • deltaE6 = -deltaE6 := by
  rw [mul_smul,
    ((exceptional_Lang_root_rank_one_torus_transport .E6 ℚ isRoot_thetaE6).2.2.2.1 deltaE6).1,
    wordProd_smul_eq_simpleWordAct, thetaE6_eq]
  unfold l0E6 simpleWordAct idxE6
  decide +kernel

end Word

section Orth

theorem kernel_orth_aux_E6 : ∀ σ ∈ rootFinset .E6, iform thetaE6' σ = 0 →
    iform deltaE6 σ % 2 = 0 → iform deltaE6 σ = 0 := by
  decide +kernel

theorem kernel_strong_orth_aux_E6 : ∀ σ ∈ rootFinset .E6, iform thetaE6' σ = 0 →
    iform deltaE6 σ = 0 →
      σ + thetaE6' ∉ rootFinset .E6 ∧ σ + -thetaE6' ∉ rootFinset .E6 ∧
        σ + deltaE6 ∉ rootFinset .E6 ∧ σ + -deltaE6 ∉ rootFinset .E6 := by
  decide +kernel

end Orth

section DiagAct

variable {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem pinnedX_commute_hex_E6 {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ)
    (h1 : iform thetaE6 σ = 0) (h2 : iform deltaE6 σ = 0) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ ∈ ({thetaE6, -thetaE6, deltaE6, -deltaE6} : Set (Fin (Tag.rank .E6) → ℤ)))
    (x y : k) :
    pinnedX .E6 k σ x * pinnedX .E6 k γ y = pinnedX .E6 k γ y * pinnedX .E6 k σ x := by
  have h1' : iform thetaE6' σ = 0 := by rwa [← thetaE6_eq]
  obtain ⟨n1, n2, n3, n4⟩ := kernel_strong_orth_aux_E6 σ (mem_rootFinset.2 hσ) h1' h2
  rw [← thetaE6_eq] at n1 n2
  have hθ := isRoot_thetaE6
  have hδ := isPartnerE6_deltaE6.1
  rcases hγ with rfl | rfl | rfl | rfl
  · exact pinnedX_commute_of_kernel hσ hθ h1 n1 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hθ) (by rw [iform_neg_left, h1, neg_zero])
      n2 x y
  · exact pinnedX_commute_of_kernel hσ hδ h2 n3 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hδ) (by rw [iform_neg_left, h2, neg_zero])
      n4 x y

theorem mem_diagAct_of_levi_comm_E6 (hk : ringChar k ≠ 2) {s : ModGL .E6 k}
    (hs : s ∈ parabolicLevi .E6 k JE6)
    (hsd : signDiagE6 k deltaE6 * s = s * signDiagE6 k deltaE6) :
    s ∈ diagActSubgroup .E6 k {thetaE6, -thetaE6, deltaE6, -deltaE6} := by
  classical
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hk (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiagE6 deltaE6 c with ha'
  set d := rootDiagUnit .E6 (thetaDiag deltaE6 (-1 : kˣ)) with hd
  set db := rootDiagUnit .E6 (thetaDiag thetaE6 c) with hdb
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E6 σ ∧ iform thetaE6 σ = 0 ∧
      iform deltaE6 σ = 0 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagE6_eq_one hc hσr hσ1
    refine ⟨hσr, h1, kernel_orth_aux_E6 σ (mem_rootFinset.2 hσr) (by rwa [← thetaE6_eq]) ?_⟩
    have h4 : Even (iform deltaE6 σ) := by
      by_contra he
      have h7 : (-1 : kˣ) ^ iform deltaE6 σ = -1 := by
        rw [neg_one_zpow_eq_ite]
        simp [he]
      exact hk2 (h7.symm.trans h2)
    rcases h4 with ⟨m, hm⟩
    omega
  set M := torusGroup .E6 k ⊔ rootSpan .E6 k (kernelRoots (rootCharHom a')) with hM
  have hsd' : d * s = s * d := hsd
  have hsM : s ∈ M := by
    have hmem : s ∈ toralCentralizer .E6 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JE6 hs), ?_⟩
      have hmul : rootDiagUnit .E6 a' = d * db := rootDiagUnit_mul _ _
      have hsb : db * s = s * db := rootDiagUnit_thetaDiag_comm_levi_E6 c hs
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * s = d * (db * s) := by group
        _ = d * (s * db) := by rw [hsb]
        _ = (d * s) * db := by group
        _ = (s * d) * db := by rw [hsd']
        _ = s * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiag_le_partnerE6 hk2 isPartnerE6_deltaE6 hc hw) hmem
  have hle : M ≤ diagActSubgroup .E6 k {thetaE6, -thetaE6, deltaE6, -deltaE6} := by
    refine sup_le (fun t ht => ?_) (iSup₂_le fun σ hσ => ?_)
    · obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      exact ⟨b, fun γ _ hr c' => rootDiagUnit_conj_pinnedX b hr c'⟩
    · obtain ⟨hσr, h1, h2⟩ := hker σ hσ
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨1, fun γ hγ hr y => ?_⟩
      rw [pinnedX_commute_hex_E6 hσr h1 h2 hγ x y]
      simp [rootChar_one']
  exact hle hsM

end DiagAct

section Cocycle

variable {k : Type} [Field k] [IsAlgClosed k]

theorem cocycle_conj_pinnedX_E6 (p : ℕ) [Fact p.Prime] [CharP k p] (hk : ringChar k ≠ 2)
    (e : ℕ) {c v m : ModGL .E6 k} (hFc : entrywiseFrobGL .E6 k p e c = c)
    (hd : v * c * v⁻¹ = signDiagE6 k deltaE6) (hm : m ∈ parabolicLevi .E6 k JE6)
    (hcoc : entrywiseFrobGL .E6 k p e v * v⁻¹ = m * rootSL2 .E6 k thetaE6 WSL) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, (entrywiseFrobGL .E6 k p e v * v⁻¹) * pinnedX .E6 k thetaE6 x *
        (entrywiseFrobGL .E6 k p e v * v⁻¹)⁻¹ = pinnedX .E6 k (-thetaE6) (Λ₀ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E6 k p e v * v⁻¹) * pinnedX .E6 k (-thetaE6) x *
        (entrywiseFrobGL .E6 k p e v * v⁻¹)⁻¹ = pinnedX .E6 k thetaE6 (Λ₁ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E6 k p e v * v⁻¹) * pinnedX .E6 k deltaE6 x *
        (entrywiseFrobGL .E6 k p e v * v⁻¹)⁻¹ = pinnedX .E6 k (-deltaE6) (Λ₂ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E6 k p e v * v⁻¹) * pinnedX .E6 k (-deltaE6) x *
        (entrywiseFrobGL .E6 k p e v * v⁻¹)⁻¹ = pinnedX .E6 k deltaE6 (Λ₃ * x)) := by
  have hθ := isRoot_thetaE6
  have hδ := isPartnerE6_deltaE6.1
  refine cocycle_conj_pinnedX_gen (J := JE6) p hk e hθ hδ hFc hd
    (entrywiseFrobGL_rootDiagUnit_of_sign p e (thetaDiag_neg_one_eq_one_or_neg_one deltaE6)) hm
    (nWordE6_mem_levi l0E6_mem_J) hcoc (nuElt_comm_rootDiagUnit_thetaDiag hθ l0E6 l0E6_comm)
    ?_ ?_ ?_ ?_ (fun s hs hsd => mem_diagAct_of_levi_comm_E6 hk hs hsd)
  · exact nuElt_conj_pinnedX hθ l0E6 hθ (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E6 (IsRoot.neg hθ) (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E6 hδ (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E6 (IsRoot.neg hδ) (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)

end Cocycle

end CFSG.ClassicalInvolution.ModelFacts.Levi
