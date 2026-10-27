module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Factor
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Stab

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Descent

variable {k : Type} [Field k]

theorem exists_h1_fixed_conj_E7 (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsPartnerE7 δ)
    {y v : ModGL .E7 k} (hv : v ∈ h1E7 k) (hFy : entrywiseFrobGL .E7 k p e y = y)
    (hvy : v * y * v⁻¹ = signDiagE7 k δ)
    (hu : entrywiseFrobGL .E7 k p e v * v⁻¹ ∈ parabolicLevi .E7 k JE7) :
    ∃ h ∈ h1E7 k, entrywiseFrobGL .E7 k p e h = h ∧ h * y * h⁻¹ = signDiagE7 k δ := by
  classical
  have hchar : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiagE7 δ c with ha'
  set d := rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) with hd
  set db := rootDiagUnit .E7 (thetaDiag thetaE7 c) with hdb
  have hvy' : v * y * v⁻¹ = d := hvy
  have hFd : entrywiseFrobGL .E7 k p e d = d :=
    entrywiseFrobGL_rootDiagUnit_of_sign p e (thetaDiag_neg_one_sign_E7 δ)
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E7 σ ∧ iform thetaE7 σ = 0 ∧
      rootChar (thetaDiag δ (-1 : kˣ)) σ = 1 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagE7_eq_one hc hσr hσ1
    exact ⟨hσr, h1, by rw [rootChar_thetaDiag]; exact h2⟩
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (rootCharHom a')) with hM
  have hMd : ∀ m ∈ M, m * d * m⁻¹ = d := by
    have hle : M ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun t ht => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
      · exact rootSpan_le_centralizer (thetaDiag δ (-1 : kˣ))
          (fun σ hσ => ⟨(hker σ hσ).1, (hker σ hσ).2.2⟩)
    intro m hm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hMJ : M ≤ parabolicLevi .E7 k JE7 := by
    refine sup_le (torusGroup_le_parabolicLevi JE7) ?_
    refine iSup₂_le fun σ hσ => rootSubgroup_le_parabolicLevi' ?_
    exact mem_parabolicRoots_E7 (hker σ hσ).1 (hker σ hσ).2.1
  have hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * entrywiseFrobGL .E7 k p e m :=
    fun u hu => exists_eq_inv_mul_frob_torus_sup_rootSpan p he (rootCharHom a') hu
  have hFvM : entrywiseFrobGL .E7 k p e v * v⁻¹ ∈ M := by
    set u := entrywiseFrobGL .E7 k p e v * v⁻¹ with hudef
    have hF : entrywiseFrobGL .E7 k p e v * y * (entrywiseFrobGL .E7 k p e v)⁻¹ = d := by
      have := congrArg (entrywiseFrobGL .E7 k p e) hvy'
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hud : d * u = u * d := by
      have hy' : v⁻¹ * d * v = y := by rw [← hvy']; group
      have h1 : u * d * u⁻¹ = d := by
        calc u * d * u⁻¹ = entrywiseFrobGL .E7 k p e v * (v⁻¹ * d * v) *
              (entrywiseFrobGL .E7 k p e v)⁻¹ := by rw [hudef]; group
          _ = d := by rw [hy', hF]
      calc d * u = (u * d * u⁻¹) * u := by rw [h1]
        _ = u * d := by group
    have hub : db * u = u * db := rootDiagUnit_thetaDiag_comm_levi_E7 c hu
    have hmem : u ∈ toralCentralizer .E7 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JE7 hu), ?_⟩
      have hmul : rootDiagUnit .E7 a' = d * db := rootDiagUnit_mul _ _
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * u = d * (db * u) := by group
        _ = d * (u * db) := by rw [hub]
        _ = (d * u) * db := by group
        _ = (u * d) * db := by rw [hud]
        _ = u * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiag_le_partnerE7 hk2 hδ hc hw) hmem
  obtain ⟨m, hm, hFix, hconj⟩ := exists_fixed_conj (entrywiseFrobGL .E7 k p e) hvy' hMd hlang hFvM
  exact ⟨m * v, mul_mem (levi_le_h1E7 (hMJ hm)) hv, hFix, hconj⟩

end Descent

end CFSG.ClassicalInvolution.ModelFacts.Levi
