module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycleGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryNu
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Stab

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Orth

theorem kernel_orth_aux : ∀ σ ∈ rootFinset .F4, iform thetaF4' σ = 0 →
    (iform deltaF4 σ / 2) % 2 = 0 → iform deltaF4 σ = 0 := by
  decide +kernel

theorem kernel_strong_orth_aux : ∀ σ ∈ rootFinset .F4, iform thetaF4' σ = 0 →
    iform deltaF4 σ = 0 →
      σ + thetaF4' ∉ rootFinset .F4 ∧ σ + -thetaF4' ∉ rootFinset .F4 ∧
        σ + deltaF4 ∉ rootFinset .F4 ∧ σ + -deltaF4 ∉ rootFinset .F4 := by
  decide +kernel

end Orth

section DiagAct

variable {k : Type} [Field k] [IsAlgClosed k]

@[expose] def hexRootsF4 : Set (Fin (Tag.rank .F4) → ℤ) := {thetaF4, -thetaF4, deltaF4, -deltaF4}

omit [IsAlgClosed k] in
theorem pinnedX_commute_hex {σ : Fin (Tag.rank .F4) → ℤ} (hσ : IsRoot .F4 σ)
    (h1 : iform thetaF4 σ = 0) (h2 : iform deltaF4 σ = 0) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ hexRootsF4) (x y : k) :
    pinnedX .F4 k σ x * pinnedX .F4 k γ y = pinnedX .F4 k γ y * pinnedX .F4 k σ x := by
  have h1' : iform thetaF4' σ = 0 := by rwa [← thetaF4_eq]
  obtain ⟨n1, n2, n3, n4⟩ := kernel_strong_orth_aux σ (mem_rootFinset.2 hσ) h1' h2
  rw [← thetaF4_eq] at n1 n2
  have hθ := isRoot_thetaF4
  have hδ := isPartnerF4_deltaF4.1
  rcases hγ with rfl | rfl | rfl | rfl
  · exact pinnedX_commute_of_kernel hσ hθ h1 n1 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hθ) (by rw [iform_neg_left, h1, neg_zero])
      n2 x y
  · exact pinnedX_commute_of_kernel hσ hδ h2 n3 x y
  · exact pinnedX_commute_of_kernel hσ (IsRoot.neg hδ) (by rw [iform_neg_left, h2, neg_zero])
      n4 x y

theorem mem_diagAct_of_levi_comm (hk : ringChar k ≠ 2) {s : ModGL .F4 k}
    (hs : s ∈ parabolicLevi .F4 k JF4)
    (hsd : signDiagF4 k deltaF4 * s = s * signDiagF4 k deltaF4) :
    s ∈ diagActSubgroup .F4 k hexRootsF4 := by
  classical
  obtain ⟨hδr, hl, hδθ⟩ := isPartnerF4_deltaF4
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hk (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiagF4 deltaF4 c with ha'
  set d := rootDiagUnit .F4 (corootDiagF4 deltaF4 (-1 : kˣ)) with hd
  set db := rootDiagUnit .F4 (corootDiagF4 thetaF4 c) with hdb
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .F4 σ ∧ iform thetaF4 σ = 0 ∧
      iform deltaF4 σ = 0 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagF4_eq_one hδr hl hc hσr hσ1
    refine ⟨hσr, h1, kernel_orth_aux σ (mem_rootFinset.2 hσr) (by rwa [← thetaF4_eq]) ?_⟩
    have h3 : (-1 : kˣ) ^ (iform deltaF4 σ / 2) = 1 := h2
    have h4 : Even (iform deltaF4 σ / 2) := by
      by_contra he
      have h7 : (-1 : kˣ) ^ (iform deltaF4 σ / 2) = -1 := by
        rw [neg_one_zpow_eq_ite]
        simp [he]
      exact hk2 (h7.symm.trans h3)
    rcases h4 with ⟨m, hm⟩
    omega
  set M := torusGroup .F4 k ⊔ rootSpan .F4 k (kernelRoots (rootCharHom a')) with hM
  have hsd' : d * s = s * d := hsd
  have hsM : s ∈ M := by
    have hmem : s ∈ toralCentralizer .F4 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JF4 hs), ?_⟩
      have hmul : rootDiagUnit .F4 a' = d * db := rootDiagUnit_mul _ _
      have hsb : db * s = s * db := rootDiagUnit_corootDiagF4_comm_levi c hs
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * s = d * (db * s) := by group
        _ = d * (s * db) := by rw [hsb]
        _ = (d * s) * db := by group
        _ = (s * d) * db := by rw [hsd']
        _ = s * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiagF4_le_partner hk2 ⟨hδr, hl, hδθ⟩ hc hw) hmem
  have hle : M ≤ diagActSubgroup .F4 k hexRootsF4 := by
    refine sup_le (fun t ht => ?_) (iSup₂_le fun σ hσ => ?_)
    · obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      exact ⟨b, fun γ _ hr c' => rootDiagUnit_conj_pinnedX b hr c'⟩
    · obtain ⟨hσr, h1, h2⟩ := hker σ hσ
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨1, fun γ hγ hr y => ?_⟩
      rw [pinnedX_commute_hex hσr h1 h2 hγ x y]
      simp [rootChar_one']
  exact hle hsM

end DiagAct

section Cocycle

variable {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem signDiagF4_deltaF4_sign :
    ∀ i, corootDiagF4 deltaF4 (-1 : kˣ) i = 1 ∨ corootDiagF4 deltaF4 (-1 : kˣ) i = -1 := fun i => by
  rcases Int.even_or_odd (iform deltaF4 (Pi.single i 1) / 2) with h | h
  · left
    exact h.neg_one_zpow
  · right
    exact h.neg_one_zpow

theorem cocycle_conj_pinnedX (p : ℕ) [Fact p.Prime] [CharP k p] (hk : ringChar k ≠ 2) (e : ℕ)
    {c v m : ModGL .F4 k} (hFc : entrywiseFrobGL .F4 k p e c = c)
    (hd : v * c * v⁻¹ = signDiagF4 k deltaF4) (hm : m ∈ parabolicLevi .F4 k JF4)
    (hcoc : entrywiseFrobGL .F4 k p e v * v⁻¹ = m * rootSL2 .F4 k thetaF4 WSL) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, (entrywiseFrobGL .F4 k p e v * v⁻¹) * pinnedX .F4 k thetaF4 x *
        (entrywiseFrobGL .F4 k p e v * v⁻¹)⁻¹ = pinnedX .F4 k (-thetaF4) (Λ₀ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .F4 k p e v * v⁻¹) * pinnedX .F4 k (-thetaF4) x *
        (entrywiseFrobGL .F4 k p e v * v⁻¹)⁻¹ = pinnedX .F4 k thetaF4 (Λ₁ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .F4 k p e v * v⁻¹) * pinnedX .F4 k deltaF4 x *
        (entrywiseFrobGL .F4 k p e v * v⁻¹)⁻¹ = pinnedX .F4 k (-deltaF4) (Λ₂ * x)) ∧
      (∀ x : k, (entrywiseFrobGL .F4 k p e v * v⁻¹) * pinnedX .F4 k (-deltaF4) x *
        (entrywiseFrobGL .F4 k p e v * v⁻¹)⁻¹ = pinnedX .F4 k deltaF4 (Λ₃ * x)) := by
  exact cocycle_conj_pinnedX_gen (J := JF4) p hk e isRoot_thetaF4 isPartnerF4_deltaF4.1 hFc hd
    (entrywiseFrobGL_rootDiagUnit_of_sign p e signDiagF4_deltaF4_sign) hm
    (nWordF4_mem_levi l0F4_mem_J) hcoc nu0F4_comm_signDiagF4 nu0F4_conj_theta nu0F4_conj_neg_theta
    nu0F4_conj_delta nu0F4_conj_neg_delta (fun s hs hsd => mem_diagAct_of_levi_comm hk hs hsd)

end Cocycle

end CFSG.ClassicalInvolution.ModelFacts.Levi
