module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryNuGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycleGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Levi
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Stab

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Word

@[expose] def l0E8 : List (Fin (Tag.rank .E8)) :=
  [idxE8 6, idxE8 5, idxE8 4, idxE8 3, idxE8 2, idxE8 1, idxE8 3, idxE8 4, idxE8 5,
   idxE8 6, idxE8 0, idxE8 2, idxE8 3, idxE8 4, idxE8 5, idxE8 1, idxE8 3, idxE8 4,
   idxE8 2, idxE8 3, idxE8 0, idxE8 2, idxE8 1, idxE8 3, idxE8 4, idxE8 5, idxE8 6]

theorem l0E8_mem_J : ∀ j ∈ l0E8, j ∈ JE8 := by
  unfold l0E8 JE8 idxE8
  decide +kernel

theorem l0E8_comm :
    ((coxeterSystem .E8).wordProd l0E8 * rootReflection thetaE8) • deltaE8 = -deltaE8 := by
  rw [mul_smul,
    ((exceptional_Lang_root_rank_one_torus_transport .E8 ℚ isRoot_thetaE8).2.2.2.1 deltaE8).1,
    wordProd_smul_eq_simpleWordAct, thetaE8_eq]
  unfold l0E8 simpleWordAct idxE8
  decide +kernel

end Word

section Orth

theorem kernel_orth_aux_E8 : ∀ σ ∈ rootFinset .E8, iform thetaE8' σ = 0 →
    iform deltaE8 σ % 2 = 0 → iform deltaE8 σ = 0 := by
  decide +kernel

theorem kernel_strong_orth_aux_E8 : ∀ σ ∈ rootFinset .E8, iform thetaE8' σ = 0 →
    iform deltaE8 σ = 0 →
      σ + thetaE8' ∉ rootFinset .E8 ∧ σ + -thetaE8' ∉ rootFinset .E8 ∧
        σ + deltaE8 ∉ rootFinset .E8 ∧ σ + -deltaE8 ∉ rootFinset .E8 := by
  decide +kernel

end Orth

section DiagAct

variable {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem pinnedX_commute_hex_E8 {σ : Fin (Tag.rank .E8) → ℤ} (hσ : IsRoot .E8 σ)
    (h1 : iform thetaE8 σ = 0) (h2 : iform deltaE8 σ = 0) {γ : Fin (Tag.rank .E8) → ℤ}
    (hγ : γ ∈ ({thetaE8, -thetaE8, deltaE8, -deltaE8} : Set (Fin (Tag.rank .E8) → ℤ)))
    (x y : k) :
    pinnedX .E8 k σ x * pinnedX .E8 k γ y = pinnedX .E8 k γ y * pinnedX .E8 k σ x := by
  have h1' : iform thetaE8' σ = 0 := by rwa [← thetaE8_eq]
  obtain ⟨n1, n2, n3, n4⟩ := kernel_strong_orth_aux_E8 σ (mem_rootFinset.2 hσ) h1' h2
  rw [← thetaE8_eq] at n1 n2
  have hθ := isRoot_thetaE8
  have hδ := isPartnerE8_deltaE8.1
  rcases hγ with rfl | rfl | rfl | rfl
  · exact pinnedX_commute_of_kernel hσ hθ h1 n1 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hθ) (by rw [iform_neg_left, h1, neg_zero])
      n2 x y
  · exact pinnedX_commute_of_kernel hσ hδ h2 n3 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hδ) (by rw [iform_neg_left, h2, neg_zero])
      n4 x y

theorem mem_diagAct_of_levi_comm_E8 (hk : ringChar k ≠ 2) {s : ModGL .E8 k}
    (hs : s ∈ parabolicLevi .E8 k JE8)
    (hsd : signDiagE8 k deltaE8 * s = s * signDiagE8 k deltaE8) :
    s ∈ diagActSubgroup .E8 k {thetaE8, -thetaE8, deltaE8, -deltaE8} := by
  classical
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hk (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiag deltaE8 c with ha'
  set d := rootDiagUnit .E8 (thetaDiag deltaE8 (-1 : kˣ)) with hd
  set db := rootDiagUnit .E8 (thetaDiag thetaE8 c) with hdb
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E8 σ ∧ iform thetaE8 σ = 0 ∧
      iform deltaE8 σ = 0 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiag_eq_one hc hσr hσ1
    refine ⟨hσr, h1, kernel_orth_aux_E8 σ (mem_rootFinset.2 hσr) (by rwa [← thetaE8_eq]) ?_⟩
    have h4 : Even (iform deltaE8 σ) := by
      by_contra he
      have h7 : (-1 : kˣ) ^ iform deltaE8 σ = -1 := by
        rw [neg_one_zpow_eq_ite]
        simp [he]
      exact hk2 (h7.symm.trans h2)
    rcases h4 with ⟨m, hm⟩
    omega
  set M := torusGroup .E8 k ⊔ rootSpan .E8 k (kernelRoots (rootCharHom a')) with hM
  have hsd' : d * s = s * d := hsd
  have hsM : s ∈ M := by
    have hmem : s ∈ toralCentralizer .E8 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JE8 hs), ?_⟩
      have hmul : rootDiagUnit .E8 a' = d * db := rootDiagUnit_mul _ _
      have hsb : db * s = s * db := rootDiagUnit_thetaDiag_comm_levi c hs
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * s = d * (db * s) := by group
        _ = d * (s * db) := by rw [hsb]
        _ = (d * s) * db := by group
        _ = (s * d) * db := by rw [hsd']
        _ = s * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiag_le_partnerE8 hk2 isPartnerE8_deltaE8 hc hw) hmem
  have hle : M ≤ diagActSubgroup .E8 k {thetaE8, -thetaE8, deltaE8, -deltaE8} := by
    refine sup_le (fun t ht => ?_) (iSup₂_le fun σ hσ => ?_)
    · obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      exact ⟨b, fun γ _ hr c' => rootDiagUnit_conj_pinnedX b hr c'⟩
    · obtain ⟨hσr, h1, h2⟩ := hker σ hσ
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨1, fun γ hγ hr y => ?_⟩
      rw [pinnedX_commute_hex_E8 hσr h1 h2 hγ x y]
      simp [rootChar_one']
  exact hle hsM

end DiagAct

section Cocycle

variable {k : Type} [Field k] [IsAlgClosed k]

theorem cocycle_conj_pinnedX_E8 (p : ℕ) [Fact p.Prime] [CharP k p] (hk : ringChar k ≠ 2)
    (e : ℕ) {c v m : ModGL .E8 k} (hFc : entrywiseFrobGL .E8 k p e c = c)
    (hd : v * c * v⁻¹ = signDiagE8 k deltaE8) (hm : m ∈ parabolicLevi .E8 k JE8)
    (hcoc : entrywiseFrobGL .E8 k p e v * v⁻¹ = m * rootSL2 .E8 k thetaE8 WSL) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, (entrywiseFrobGL .E8 k p e v * v⁻¹) * pinnedX .E8 k thetaE8 x *
        (entrywiseFrobGL .E8 k p e v * v⁻¹)⁻¹ = pinnedX .E8 k (-thetaE8) (Λ₀ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E8 k p e v * v⁻¹) * pinnedX .E8 k (-thetaE8) x *
        (entrywiseFrobGL .E8 k p e v * v⁻¹)⁻¹ = pinnedX .E8 k thetaE8 (Λ₁ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E8 k p e v * v⁻¹) * pinnedX .E8 k deltaE8 x *
        (entrywiseFrobGL .E8 k p e v * v⁻¹)⁻¹ = pinnedX .E8 k (-deltaE8) (Λ₂ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E8 k p e v * v⁻¹) * pinnedX .E8 k (-deltaE8) x *
        (entrywiseFrobGL .E8 k p e v * v⁻¹)⁻¹ = pinnedX .E8 k deltaE8 (Λ₃ * x)) := by
  have hθ := isRoot_thetaE8
  have hδ := isPartnerE8_deltaE8.1
  refine cocycle_conj_pinnedX_gen (J := JE8) p hk e hθ hδ hFc hd
    (entrywiseFrobGL_rootDiagUnit_of_sign p e (thetaDiag_neg_one_eq_one_or_neg_one deltaE8)) hm
    (nWordE8_mem_levi l0E8_mem_J) hcoc (nuElt_comm_rootDiagUnit_thetaDiag hθ l0E8 l0E8_comm)
    ?_ ?_ ?_ ?_ (fun s hs hsd => mem_diagAct_of_levi_comm_E8 hk hs hsd)
  · exact nuElt_conj_pinnedX hθ l0E8 hθ (by
      rw [thetaE8_eq]
      unfold l0E8 simpleWordAct idxE8
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E8 (IsRoot.neg hθ) (by
      rw [thetaE8_eq]
      unfold l0E8 simpleWordAct idxE8
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E8 hδ (by
      rw [thetaE8_eq]
      unfold l0E8 simpleWordAct idxE8
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E8 (IsRoot.neg hδ) (by
      rw [thetaE8_eq]
      unfold l0E8 simpleWordAct idxE8
      decide +kernel)

end Cocycle

end CFSG.ClassicalInvolution.ModelFacts.Levi
