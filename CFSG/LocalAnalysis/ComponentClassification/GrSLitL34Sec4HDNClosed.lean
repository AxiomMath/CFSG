module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDNConn

public section

namespace CFSG.ComponentClassification.GrSLit.HeNormal

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.HeDiag

variable {X : Type} [Group X] [Finite X]

theorem false_of_normal
    [IsSimpleGroup X] (hnab : ∃ x y : X, x * y ≠ y * x)
    (hGWB : GWTwoBalanced X) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) (hGold : GoldschmidtStronglyClosedInput)
    {M K T A : Subgroup X} {a : X} (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (hKM : K ≤ M) (hKn : M ≤ normalizer (K : Set X)) (hTsyl : IsSylowTwoIn T M) (haT : a ∈ T)
    (ha1 : a ≠ 1) (hak : a ∈ coreActionKernel K) (hAe : IsElemTwo A) (hA16 : 16 ≤ Nat.card A)
    (hMW : M = normalizer (wGroup A : Set X)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 := hTsyl.isPGroup
  have hTN : T ≤ normalizer (K : Set X) := hTsyl.1.trans hKn
  have h1024 := card_inf_eq_of_normal e₁ hKM hKn hTsyl
  have h3 := isThreeConnected_of_normal e₁ h64 hOut hT2 hTN h1024
  obtain ⟨⟨P₀, hP₀⟩, hfus⟩ := sylow_and_fusion_of_threeConnected hGWB hAe hA16 (hMW ▸ hTsyl) h3
  set P : Subgroup X := T ⊓ coreActionKernel K with hPdef
  have hsc : ∀ n : ℕ, ∀ p ∈ P, p ^ (2 ^ n) = 1 → ∀ g : X, g⁻¹ * p * g ∈ T →
      g⁻¹ * p * g ∈ P := by
    intro n
    induction n with
    | zero =>
      intro p _ hpn g _
      rw [pow_zero, pow_one] at hpn
      rw [hpn, mul_one, inv_mul_cancel]
      exact one_mem _
    | succ n ih =>
      intro p hp hpn g hg
      have hpT : p ∈ T := (mem_inf.mp hp).1
      have hp2 : p * p ∈ P := mul_mem hp hp
      have hp2n : (p * p) ^ (2 ^ n) = 1 := by
        rw [← pow_two, ← pow_mul, ← pow_succ']
        exact hpn
      have hsq : g⁻¹ * (p * p) * g = (g⁻¹ * p * g) * (g⁻¹ * p * g) := by group
      have hbb := ih (p * p) hp2 hp2n g (by rw [hsq]; exact mul_mem hg hg)
      rw [hsq] at hbb
      obtain ⟨h, hext⟩ := exists_extremal_conj ⟨P₀, hP₀⟩ hpT
      obtain ⟨m, hmN, hm⟩ := hfus _ p hpT hext ⟨h, rfl⟩
        (three_le_pRank_centralizer_of_sq e₁ h64 hOut hT2 hTN h1024 hpT hp2)
      obtain ⟨m', hm'N, hm'⟩ := hfus _ (g⁻¹ * p * g) hg hext ⟨g⁻¹ * h, by group⟩
        (three_le_pRank_centralizer_of_sq e₁ h64 hOut hT2 hTN h1024 hg hbb)
      have ha₀ : h⁻¹ * p * h = m * p * m⁻¹ := by
        calc h⁻¹ * p * h = m * (m⁻¹ * (h⁻¹ * p * h) * m) * m⁻¹ := by group
          _ = m * p * m⁻¹ := by rw [← hm]
      have hν : g⁻¹ * p * g = (m⁻¹ * m')⁻¹ * p * (m⁻¹ * m') := by
        rw [hm', ha₀]
        group
      refine mem_inf.mpr ⟨hg, ?_⟩
      rw [hν]
      have hνM : (m⁻¹ * m')⁻¹ ∈ M := by
        rw [hMW]
        exact inv_mem (mul_mem (inv_mem hmN) hm'N)
      have := conj_mem_coreActionKernel_of_mem (hKn hνM) (mem_inf.mp hp).2
      rwa [inv_inv] at this
  have htop : GeneralizedFitting.subgroup X = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup X, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hPne : P ≠ ⊥ := fun h => by
    have haP : a ∈ P := mem_inf.mpr ⟨haT, hak⟩
    rw [h, mem_bot] at haP
    exact ha1 haP
  have hP2 : IsPGroup 2 P := hT2.to_le inf_le_left
  have hsolv := hGold X hsF hnF P₀ P (hP₀ ▸ inf_le_left) hPne fun p hp g hg => by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨p, hp⟩
    refine hsc n p hp ?_ g (hP₀ ▸ hg)
    rw [← orderOf_dvd_iff_pow_eq_one, ← Subgroup.orderOf_mk p hp, hn]
  set C : Subgroup X := centralizer (P : Set X) with hCdef
  have hsurj : Function.Surjective ((heModelL e₁).comp
      (inclusion (inf_le_left : K ⊓ C ≤ K))) := by
    intro y
    obtain ⟨x, hxK, hxy⟩ := exists_heL_eq (e := e₁) y.2
    obtain ⟨w, hw, hwx⟩ :=
      FooteLit.exists_mem_centralizer_of_le_coreActionKernel hP2 inf_le_right hxK
    have hwK : w ∈ K := (mem_inf.mp hw).1
    have h1 : heL e₁ (w⁻¹ * x) = 1 := (heL_eq_one_iff (mul_mem (inv_mem hwK) hxK)).mpr hwx
    rw [heL_mul (inv_mem hwK) hxK, heL_inv hwK, inv_mul_eq_one] at h1
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    show ((heModelL e₁ ⟨w, hwK⟩ : heP) : Equiv.Perm (Fin 8330)) = (y : Equiv.Perm (Fin 8330))
    rw [← heL_of_mem hwK, h1, hxy]
  have : Group.IsSolvable ↥(K ⊓ C) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective (inf_le_right : K ⊓ C ≤ C))
  have hheP : Group.IsSolvable heP := Group.isSolvable_of_surjective hsurj
  have : IsSimpleGroup heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He heEquivP.symm
  obtain ⟨u, v, huv⟩ := exists_mul_ne_held
  apply huv
  apply heEquivP.injective
  rw [map_mul, map_mul]
  exact IsSimpleGroup.comm_iff_isSolvable.mpr hheP _ _

end CFSG.ComponentClassification.GrSLit.HeNormal
