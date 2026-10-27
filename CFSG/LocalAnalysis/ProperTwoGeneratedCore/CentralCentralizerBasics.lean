module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientRoot

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G}

omit [Finite G] in
theorem mem_rightConjugate_iff_conj_mem (X : Subgroup G) (g x : G) :
    x ∈ rightConjugate X g ↔ g * x * g⁻¹ ∈ X := by
  change x ∈ X.map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]

theorem pRank_rightConjugate {p : ℕ} (hp : 1 < p) (X : Subgroup G) (g : G) :
    Open.pRank p (rightConjugate X g) = Open.pRank p X := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map hp (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective (rightConjugate X g)
    have hmap : (rightConjugate X g).map (MulAut.conj g).toMonoidHom = X := by
      ext x
      rw [Subgroup.mem_map_equiv, mem_rightConjugate_iff_conj_mem, MulAut.conj_symm_apply]
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    rwa [hmap] at h
  · exact CFSG.SectionRank.pRank_le_map hp (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective X

omit [Finite G] in
theorem mem_rightCosetStabilizer_mk_iff (b x : G) :
    x ∈ rightCosetStabilizer H (Quotient.mk (QuotientGroup.rightRel H) b) ↔ b * x * b⁻¹ ∈ H := by
  change x ∈ rightCosetStabilizer H (rightCosetMk H b) ↔ _
  rw [rightCosetStabilizer_mk, mem_rightConjugate_iff_conj_mem]

omit [Finite G] in
theorem mk_mem_elementFixedSet_iff (b x : G) :
    Quotient.mk (QuotientGroup.rightRel H) b ∈ elementFixedSet H x ↔ b * x * b⁻¹ ∈ H := by
  rw [← mem_rightCosetStabilizer_mk_iff, mem_point_right_stabilizer_iff]
  rfl

omit [Finite G] in
theorem mem_elementFixedSet_iff_mem_stabilizer (x : G) (β : pointRightCosetSpace H) :
    β ∈ elementFixedSet H x ↔ x ∈ rightCosetStabilizer H β :=
  (mem_point_right_stabilizer_iff H β x).symm

omit [Finite G] in
theorem base_mem_elementFixedSet_iff (x : G) :
    Quotient.mk (QuotientGroup.rightRel H) 1 ∈ elementFixedSet H x ↔ x ∈ H := by
  rw [mk_mem_elementFixedSet_iff, one_mul, inv_one, mul_one]

omit [Finite G] in
theorem quotient_mk_eq_iff (b c : G) :
    Quotient.mk (QuotientGroup.rightRel H) b = Quotient.mk (QuotientGroup.rightRel H) c ↔
      c * b⁻¹ ∈ H :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

omit [Finite G] in
theorem IsCentralInvolution.le_centralizer {T : Subgroup G} {z : G}
    (hz : IsCentralInvolution T z) : T ≤ Subgroup.centralizer ({z} : Set G) := fun s hs =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hz.2.2 s hs)

theorem coreSetting_conj_inter_twoRank_le_one (hset : CoreSetting G S H) {g : G} (hg : g ∉ H) :
    Open.pRank 2 (H ⊓ rightConjugate H g) ≤ 1 := by
  have := conjugate_intersection_rank_lt S H (k := 2) (by decide) hset.sylow_le hset.core_le g hg
  change Open.pRank 2 (H ⊓ H.conjBy g⁻¹) ≤ 1
  omega

theorem coreSetting_stabilizer_inter_twoRank_le_one (hset : CoreSetting G S H)
    {β γ : pointRightCosetSpace H} (hne : β ≠ γ) :
    Open.pRank 2 (rightCosetStabilizer H β ⊓ rightCosetStabilizer H γ) ≤ 1 := by
  obtain ⟨b, rfl⟩ := Quotient.exists_rep β
  obtain ⟨c, rfl⟩ := Quotient.exists_rep γ
  have hcb : c * b⁻¹ ∉ H := fun h => hne ((quotient_mk_eq_iff b c).mpr h)
  have heq : rightCosetStabilizer H (Quotient.mk _ b) ⊓ rightCosetStabilizer H (Quotient.mk _ c) =
      rightConjugate (H ⊓ rightConjugate H (c * b⁻¹)) b := by
    ext x
    have hx : c * b⁻¹ * (b * x * b⁻¹) * (c * b⁻¹)⁻¹ = c * x * c⁻¹ := by group
    rw [Subgroup.mem_inf, mem_rightCosetStabilizer_mk_iff, mem_rightCosetStabilizer_mk_iff,
      mem_rightConjugate_iff_conj_mem, Subgroup.mem_inf, mem_rightConjugate_iff_conj_mem, hx]
  rw [heq, pRank_rightConjugate (by decide)]
  exact coreSetting_conj_inter_twoRank_le_one hset hcb

theorem coreSetting_normalizer_le (hset : CoreSetting G S H) {D : Subgroup G} (hDH : D ≤ H)
    (hD : 2 ≤ Open.pRank 2 D) : Subgroup.normalizer (D : Set G) ≤ H :=
  two_generated_core_subgroup_normalizer_le S H hset.sylow_le hset.core_le D hDH hD

theorem coreSetting_sylow_normalizer_le (hset : CoreSetting G S H) :
    Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ H :=
  coreSetting_normalizer_le hset hset.sylow_le (by have := hset.rank; omega)

theorem coreSetting_involution_fusion (hset : CoreSetting G S H) {x : G} (hxH : x ∈ H)
    (hx : orderOf x = 2) {g : G} (hg : g⁻¹ * x * g ∈ H) :
    ∃ h ∈ H, h⁻¹ * x * h = g⁻¹ * x * g :=
  two_generated_core_controls_involution_fusion S H hset.sylow_le hset.core_le x hxH hx g hg

theorem twoGroup_fixes_point_of_sylow_le (hSH : (S : Subgroup G) ≤ H) {P : Subgroup G}
    (hP : IsPGroup 2 P) : ∃ β : pointRightCosetSpace H, P ≤ rightCosetStabilizer H β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow S hP
  refine ⟨Quotient.mk _ g⁻¹, fun x hx => ?_⟩
  rw [mem_rightCosetStabilizer_mk_iff, inv_inv]
  exact hSH (hg x hx)

theorem coreSetting_twoGroup_fixes_point (hset : CoreSetting G S H) {P : Subgroup G}
    (hP : IsPGroup 2 P) : ∃ β : pointRightCosetSpace H, P ≤ rightCosetStabilizer H β :=
  twoGroup_fixes_point_of_sylow_le hset.sylow_le hP

theorem coreSetting_eq_of_le_stabilizer (hset : CoreSetting G S H) {D : Subgroup G}
    (hD : 2 ≤ Open.pRank 2 D) {β γ : pointRightCosetSpace H} (hβ : D ≤ rightCosetStabilizer H β)
    (hγ : D ≤ rightCosetStabilizer H γ) : β = γ := by
  by_contra hne
  have h1 := coreSetting_stabilizer_inter_twoRank_le_one hset hne
  have h2 := CFSG.SectionRank.pRank_mono (by decide : 1 < 2) (le_inf hβ hγ)
  omega

theorem coreSetting_exists_centralizer_mul_eq (hset : CoreSetting G S H) {x : G}
    (hx : orderOf x = 2) {β γ : pointRightCosetSpace H} (hβ : β ∈ elementFixedSet H x)
    (hγ : γ ∈ elementFixedSet H x) :
    ∃ m ∈ Subgroup.centralizer ({x} : Set G), pointRightCosetMul H β m = γ := by
  obtain ⟨b, rfl⟩ := Quotient.exists_rep β
  obtain ⟨c, rfl⟩ := Quotient.exists_rep γ
  rw [mk_mem_elementFixedSet_iff] at hβ hγ
  have hbx : orderOf (b * x * b⁻¹) = 2 := by
    rw [← hx]
    simpa only [MulAut.conj_apply] using (MulAut.conj b).orderOf_eq x
  have hcb : (b * c⁻¹)⁻¹ * (b * x * b⁻¹) * (b * c⁻¹) = c * x * c⁻¹ := by group
  obtain ⟨h, hhH, hh⟩ := coreSetting_involution_fusion hset hβ hbx (g := b * c⁻¹) (hcb ▸ hγ)
  rw [hcb] at hh
  refine ⟨b⁻¹ * h * c, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * h * c * x = b⁻¹ * h * (c * x * c⁻¹) * c := by group
      _ = b⁻¹ * h * (h⁻¹ * (b * x * b⁻¹) * h) * c := by rw [hh]
      _ = x * (b⁻¹ * h * c) := by group
  · rw [pointRightCosetMul_mk, quotient_mk_eq_iff]
    have hinv : c * (b * (b⁻¹ * h * c))⁻¹ = h⁻¹ := by group
    rw [hinv]
    exact H.inv_mem hhH

end CFSG.ProperTwoGeneratedCore.Assembly
