module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE7Embed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryNuGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycleGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Levi
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Stab

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Word

@[expose] def l0E7 : List (Fin (Tag.rank .E7)) :=
  [idxE7 2, idxE7 3, idxE7 4, idxE7 5, idxE7 6, idxE7 1, idxE7 3, idxE7 4, idxE7 5,
   idxE7 2, idxE7 3, idxE7 4, idxE7 1, idxE7 3, idxE7 2]

theorem l0E7_mem_J : ∀ j ∈ l0E7, j ∈ JE7 := by
  unfold l0E7 JE7 idxE7
  decide +kernel

theorem l0E7_comm :
    ((coxeterSystem .E7).wordProd l0E7 * rootReflection thetaE7) • deltaE7 = -deltaE7 := by
  rw [mul_smul,
    ((exceptional_Lang_root_rank_one_torus_transport .E7 ℚ isRoot_thetaE7).2.2.2.1 deltaE7).1,
    wordProd_smul_eq_simpleWordAct, thetaE7_eq_vec]
  unfold l0E7 simpleWordAct idxE7
  decide +kernel

end Word

section Orth

theorem kernel_orth_aux_E7 : ∀ σ ∈ rootFinset .E7, iform thetaE7' σ = 0 →
    iform deltaE7 σ % 2 = 0 → iform deltaE7 σ = 0 := by
  decide +kernel

theorem kernel_strong_orth_aux_E7 : ∀ σ ∈ rootFinset .E7, iform thetaE7' σ = 0 →
    iform deltaE7 σ = 0 →
      σ + thetaE7' ∉ rootFinset .E7 ∧ σ + -thetaE7' ∉ rootFinset .E7 ∧
        σ + deltaE7 ∉ rootFinset .E7 ∧ σ + -deltaE7 ∉ rootFinset .E7 := by
  decide +kernel

end Orth

section DiagAct

variable {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem pinnedX_commute_hex_E7 {σ : Fin (Tag.rank .E7) → ℤ} (hσ : IsRoot .E7 σ)
    (h1 : iform thetaE7 σ = 0) (h2 : iform deltaE7 σ = 0) {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ ({thetaE7, -thetaE7, deltaE7, -deltaE7} : Set (Fin (Tag.rank .E7) → ℤ)))
    (x y : k) :
    pinnedX .E7 k σ x * pinnedX .E7 k γ y = pinnedX .E7 k γ y * pinnedX .E7 k σ x := by
  have h1' : iform thetaE7' σ = 0 := by rwa [← thetaE7_eq_vec]
  obtain ⟨n1, n2, n3, n4⟩ := kernel_strong_orth_aux_E7 σ (mem_rootFinset.2 hσ) h1' h2
  rw [← thetaE7_eq_vec] at n1 n2
  have hθ := isRoot_thetaE7
  have hδ := isPartnerE7_deltaE7.1
  rcases hγ with rfl | rfl | rfl | rfl
  · exact pinnedX_commute_of_kernel hσ hθ h1 n1 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hθ) (by rw [iform_neg_left, h1, neg_zero])
      n2 x y
  · exact pinnedX_commute_of_kernel hσ hδ h2 n3 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hδ) (by rw [iform_neg_left, h2, neg_zero])
      n4 x y

theorem mem_diagAct_of_levi_comm_E7 (hk : ringChar k ≠ 2) {s : ModGL .E7 k}
    (hs : s ∈ parabolicLevi .E7 k JE7)
    (hsd : signDiagE7 k deltaE7 * s = s * signDiagE7 k deltaE7) :
    s ∈ diagActSubgroup .E7 k {thetaE7, -thetaE7, deltaE7, -deltaE7} := by
  classical
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hk (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiagE7 deltaE7 c with ha'
  set d := rootDiagUnit .E7 (thetaDiag deltaE7 (-1 : kˣ)) with hd
  set db := rootDiagUnit .E7 (thetaDiag thetaE7 c) with hdb
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E7 σ ∧ iform thetaE7 σ = 0 ∧
      iform deltaE7 σ = 0 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagE7_eq_one hc hσr hσ1
    refine ⟨hσr, h1, kernel_orth_aux_E7 σ (mem_rootFinset.2 hσr) (by rwa [← thetaE7_eq_vec]) ?_⟩
    have h4 : Even (iform deltaE7 σ) := by
      by_contra he
      have h7 : (-1 : kˣ) ^ iform deltaE7 σ = -1 := by
        rw [neg_one_zpow_eq_ite]
        simp [he]
      exact hk2 (h7.symm.trans h2)
    rcases h4 with ⟨m, hm⟩
    omega
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (rootCharHom a')) with hM
  have hsd' : d * s = s * d := hsd
  have hsM : s ∈ M := by
    have hmem : s ∈ toralCentralizer .E7 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JE7 hs), ?_⟩
      have hmul : rootDiagUnit .E7 a' = d * db := rootDiagUnit_mul _ _
      have hsb : db * s = s * db := rootDiagUnit_thetaDiag_comm_levi_E7 c hs
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * s = d * (db * s) := by group
        _ = d * (s * db) := by rw [hsb]
        _ = (d * s) * db := by group
        _ = (s * d) * db := by rw [hsd']
        _ = s * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiag_le_partnerE7 hk2 isPartnerE7_deltaE7 hc hw) hmem
  have hle : M ≤ diagActSubgroup .E7 k {thetaE7, -thetaE7, deltaE7, -deltaE7} := by
    refine sup_le (fun t ht => ?_) (iSup₂_le fun σ hσ => ?_)
    · obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      exact ⟨b, fun γ _ hr c' => rootDiagUnit_conj_pinnedX b hr c'⟩
    · obtain ⟨hσr, h1, h2⟩ := hker σ hσ
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨1, fun γ hγ hr y => ?_⟩
      rw [pinnedX_commute_hex_E7 hσr h1 h2 hγ x y]
      simp [rootChar_one']
  exact hle hsM

end DiagAct

section Cocycle

variable {k : Type} [Field k] [IsAlgClosed k]

theorem cocycle_conj_pinnedX_E7 (p : ℕ) [Fact p.Prime] [CharP k p] (hk : ringChar k ≠ 2)
    (e : ℕ) {c v m : ModGL .E7 k} (hFc : entrywiseFrobGL .E7 k p e c = c)
    (hd : v * c * v⁻¹ = signDiagE7 k deltaE7) (hm : m ∈ parabolicLevi .E7 k JE7)
    (hcoc : entrywiseFrobGL .E7 k p e v * v⁻¹ = m * rootSL2 .E7 k thetaE7 WSL) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, (entrywiseFrobGL .E7 k p e v * v⁻¹) * pinnedX .E7 k thetaE7 x *
        (entrywiseFrobGL .E7 k p e v * v⁻¹)⁻¹ = pinnedX .E7 k (-thetaE7) (Λ₀ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E7 k p e v * v⁻¹) * pinnedX .E7 k (-thetaE7) x *
        (entrywiseFrobGL .E7 k p e v * v⁻¹)⁻¹ = pinnedX .E7 k thetaE7 (Λ₁ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E7 k p e v * v⁻¹) * pinnedX .E7 k deltaE7 x *
        (entrywiseFrobGL .E7 k p e v * v⁻¹)⁻¹ = pinnedX .E7 k (-deltaE7) (Λ₂ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .E7 k p e v * v⁻¹) * pinnedX .E7 k (-deltaE7) x *
        (entrywiseFrobGL .E7 k p e v * v⁻¹)⁻¹ = pinnedX .E7 k deltaE7 (Λ₃ * x)) := by
  have hθ := isRoot_thetaE7
  have hδ := isPartnerE7_deltaE7.1
  refine cocycle_conj_pinnedX_gen (J := JE7) p hk e hθ hδ hFc hd
    (entrywiseFrobGL_rootDiagUnit_of_sign p e (thetaDiag_neg_one_eq_one_or_neg_one deltaE7)) hm
    (nWordE7_mem_levi l0E7_mem_J) hcoc (nuElt_comm_rootDiagUnit_thetaDiag hθ l0E7 l0E7_comm)
    ?_ ?_ ?_ ?_ (fun s hs hsd => mem_diagAct_of_levi_comm_E7 hk hs hsd)
  · exact nuElt_conj_pinnedX hθ l0E7 hθ (by
      rw [thetaE7_eq_vec]
      unfold l0E7 simpleWordAct idxE7
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E7 (IsRoot.neg hθ) (by
      rw [thetaE7_eq_vec]
      unfold l0E7 simpleWordAct idxE7
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E7 hδ (by
      rw [thetaE7_eq_vec]
      unfold l0E7 simpleWordAct idxE7
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E7 (IsRoot.neg hδ) (by
      rw [thetaE7_eq_vec]
      unfold l0E7 simpleWordAct idxE7
      decide +kernel)

end Cocycle

end CFSG.ClassicalInvolution.ModelFacts.Levi
