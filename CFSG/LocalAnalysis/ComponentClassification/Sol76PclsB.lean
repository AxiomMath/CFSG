module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MonsterLocalProof
public import CFSG.RankThree.GroupTheory.SteinbergBMClassTwoExtraspecialAction

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.TwoB
  CFSG.RankThree.PartTwo.Sec4.Census

theorem sporadicCoverRankInput_B :
    SporadicCoverRankInput .B := by
  intro Q _ _ hQ hZ2 hS
  obtain ⟨t, htZ, ht2, -⟩ := exists_center_eq_zpowers hZ2
  have hcov : IsTwoBCover Q := ⟨hQ.1, hZ2, hS⟩
  obtain ⟨z, hloc, hR⟩ := twoBLocal_of_monster monsterLocal Q hcov t htZ ht2
  obtain ⟨R₀, -, hRe, hR23, hRz, -, hdisj, -⟩ := hR.r0
  have hz2 : orderOf z = 2 := hloc.order_z
  have hzR : z ∈ R₀ := by
    have hz : z ∈ (center R₀).map R₀.subtype := hRz ▸ mem_zpowers z
    obtain ⟨w, -, rfl⟩ := hz
    exact w.2
  have hcenR : center ↥R₀ = zpowers (⟨z, hzR⟩ : R₀) := by
    apply Subgroup.map_injective R₀.subtype_injective
    rw [hRz, MonoidHom.map_zpowers]
    rfl
  obtain ⟨s, hsZ, hs2⟩ := RankThree.GroupTheory.SteinbergBM.exists_noncentral_involution hRe
    (n := 11) (by rw [hR23]) (by norm_num) hcenR
  have hsq : ∀ {w : Q}, orderOf w = 2 → w * w = 1 := fun hw => by
    rw [← pow_two, ← hw, pow_orderOf_eq_one]
  have hx2 : (s : Q) * s = 1 := by
    rw [← Subgroup.coe_mul, ← pow_two, ← hs2, pow_orderOf_eq_one, Subgroup.coe_one]
  have hzc : (⟨z, hzR⟩ : R₀) ∈ center ↥R₀ := hcenR ▸ mem_zpowers _
  have hxz : (s : Q) * z = z * s := by
    have h := (mem_center_iff.mp hzc s)
    exact congrArg Subtype.val h
  have hxt : (s : Q) * t = t * s := mem_center_iff.mp htZ s
  have hzt : z * t = t * z := mem_center_iff.mp htZ z
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at ht2; omega
  refine three_le_pRank_of_involutions hx2 (hsq hz2) (hsq ht2) hxz hxt hzt ?_
  intro a b d h
  have hval : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hval d with rfl | rfl
  · rcases hval a with rfl | rfl
    · rcases hval b with rfl | rfl
      · exact ⟨rfl, rfl, rfl⟩
      · simp at h
        exact absurd h hz1
    · exfalso
      apply hsZ
      rw [hcenR]
      have h' : (s : Q) = (z ^ b.val)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        simpa using h
      have hs' : s = ((⟨z, hzR⟩ : R₀) ^ b.val)⁻¹ := Subtype.ext (by
        rw [h', Subgroup.coe_inv, Subgroup.coe_pow])
      rw [hs']
      exact inv_mem (pow_mem (mem_zpowers _) _)
  · exfalso
    have htR : t ∈ R₀ := by
      have h' : t = ((s : Q) ^ a.val * z ^ b.val)⁻¹ :=
        eq_inv_of_mul_eq_one_right (by simpa using h)
      rw [h']
      exact inv_mem (mul_mem (pow_mem s.2 _) (pow_mem hzR _))
    exact ht1 ((Subgroup.disjoint_def.mp hdisj) htR (mem_zpowers t))

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
