module

public import CFSG.ClassicalInvolution.Q3.Q3T6DCaseIB

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding

section Sq

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_sq_eq_involution3 (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) : ∃ k ∈ K, k * k = z ∧ k ^ 4 = 1 := by
  obtain ⟨-, R, hR, hRnc⟩ := hΩ.omega1 K hK
  have hRK : R ≤ K := hR.1
  have hR2 : IsPGroup 2 R := hR.2.1
  obtain ⟨y, hyR, hy⟩ : ∃ y ∈ R, y * y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hRnc ⟨⟨fun a b => ?_⟩⟩
    have ha := hcon a a.2
    have hb := hcon b b.2
    have hab : (a : G) * b * ((a : G) * b) = 1 := hcon _ (R.mul_mem a.2 b.2)
    have hai : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbi : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    apply Subtype.ext
    have := inv_eq_of_mul_eq_one_right hab
    rw [mul_inv_rev, hai, hbi] at this
    exact this.symm
  obtain ⟨m, hm⟩ := hR2 ⟨y, hyR⟩
  have hym : y ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨j, hjm, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hym)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hdvd : orderOf y ∣ 2 := by
      rw [hj]
      exact (Nat.pow_dvd_pow 2 (by omega : j ≤ 1))
    exact hy (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj2
  set k := y ^ (2 ^ d) with hk
  have hkord : orderOf k = 4 := by
    rw [hk, orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact Nat.pow_dvd_pow 2 (by omega)),
      hj, pow_add, Nat.mul_div_cancel _ (by positivity)]
    norm_num
  have hk4 : k ^ 4 = 1 := by rw [← hkord]; exact pow_orderOf_eq_one k
  have hkK : k ∈ K := K.pow_mem (hRK hyR) _
  have hkk1 : k * k ≠ 1 := fun h => by
    have : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h)
    rw [hkord] at this
    omega
  have hsq : k * k * (k * k) = 1 := by
    calc k * k * (k * k) = k ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hk4
  exact ⟨k, hkK, (hz.unique _ (K.mul_mem hkK hkK) hsq).resolve_left hkk1, hk4⟩

end Sq

section Main


theorem caseI3_of (h4 : Asc75Theorem4) : CaseI3 := by
  intro G _ _ _ K z hb hΩ J t hv hne
  obtain ⟨H, hHdef⟩ : ∃ H, omegaGen (aStar (CoreAssembly.conjClass K) K) = H := ⟨_, rfl⟩
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := hypGen_of_modU hΩ
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have htrans : ∀ M ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = M := by
    intro M hM
    obtain ⟨g, rfl⟩ := hM
    exact ⟨g, rfl⟩
  have hKS : K ∈ aStar (CoreAssembly.conjClass K) K := Relation.ReflTransGen.refl
  have hJS : J ∈ aStar (CoreAssembly.conjClass K) K :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨z, t, hv⟩⟩
  have hKH : K ≤ H := hHdef ▸ le_omegaGen hKS
  have hJH : J ≤ H := hHdef ▸ le_omegaGen hJS
  have hz : IsUniqueInvolution K z := hv.hzK
  have ht : IsUniqueInvolution J t := hv.hzJ
  have hzH : z ∈ H := hKH hz.mem
  have htH : t ∈ H := hJH ht.mem
  have hHtop : H ≠ ⊤ := fun h =>
    hne (aStar_eq_of_omegaGen_eq_top hΩ.conjInvariant hK htrans (hHdef.trans h))
  have hlt : Nat.card ↥H < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group H)
      (fun h => hHtop ((Subgroup.card_eq_iff_eq_top H).mp h))
  have hsec : G2Section H z := g2Section3_of_violation hΩ hb.below hK hHdef hv hlt
  have hT : TightlyEmbedded H :=
    tightlyEmbedded_of_g2Section hΩ.conjInvariant hK hz hHdef hsec
  have hlay : twoPrimeLayerIn H = H := twoPrimeLayerIn_eq_self hsec.quasisimple
  have hne' : twoPrimeLayerIn H ≠ oddCoreIn H := by
    rw [hlay]
    intro h
    exact not_mem_oddCoreIn hz (h ▸ hzH)
  have hHn : ¬ H.Normal := by
    intro hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · exact hz.ne_one (by simpa [h] using hzH)
    · exact hHtop h
  have hF : IsSimpleGroup (CFSG.generalizedFitting G) :=
    isSimpleGroup_generalizedFitting hb.nonabelian
  rcases h4 G H hT hne' with hB | ⟨hr, -⟩ | ⟨g, hg, T, hTs, hTN, n, hn, φ, hφ, hker⟩
  · exact false_of_normalIn_twoPrimeLayerIn_top hT hHn hF hne' hB
  · rw [hlay] at hr
    have h2 := two_le_pRank_of_commuting hz.sq ht.sq hz.ne_one ht.ne_one
      (AViol.ne_involution_gen hΩg hK hv).symm (AViol.comm_gen hΩg hv) hzH htH
    omega
  · obtain ⟨k, hkK, hkk, hk4⟩ := exists_sq_eq_involution3 hΩg hK hz
    have hkH : k ∈ H := hKH hkK
    have hkC : k ∈ oUpperTwoPrime (H ⊔ T) :=
      Subgroup.subset_closure ⟨(le_sup_left : H ≤ H ⊔ T) hkH, 2, by simpa using hk4⟩
    have hzC : z ∈ oUpperTwoPrime (H ⊔ T) :=
      Subgroup.subset_closure ⟨(le_sup_left : H ≤ H ⊔ T) hzH, 1, by simpa [pow_two] using hz.sq⟩
    set k' : ↥(oUpperTwoPrime (H ⊔ T)) := ⟨k, hkC⟩ with hk'
    set z' : ↥(oUpperTwoPrime (H ⊔ T)) := ⟨z, hzC⟩ with hz'
    have hkz : k' ^ 2 = z' := Subtype.ext (by rw [pow_two, Subgroup.coe_mul]; exact hkk)
    have hk'4 : k' ^ 4 = 1 := Subtype.ext (by simpa using hk4)
    have hz1 : φ z' ≠ 1 := by
      intro h
      have hzk : z' ∈ φ.ker := h
      rw [hker, Subgroup.mem_subgroupOf] at hzk
      exact not_mem_oddCoreIn hz hzk
    have h44 : (φ k') ^ 4 = 1 := by rw [← map_pow, hk'4, map_one]
    exact hz1 (by rw [← hkz, map_pow]; exact prod_sq_eq_one_of_pow_four _ h44)

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6D
