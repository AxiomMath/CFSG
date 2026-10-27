module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.CGT.PushingUpLit.BHS CFSG.RankThree.PartOne
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem oResidualTwo_eq_top_of_isShort2 {E : Subgroup Γ} (h : IsShort2 E) :
    oResidualTwo ↥E = ⊤ := by
  refine eq_top_iff.2 (le_sInf ?_)
  rintro N ⟨hN, hq⟩
  have := hN
  exact (h.1 N hq).ge

theorem commutator_eq_of_isShort2 [Finite Γ] {P' S E : Subgroup Γ} (hmin : IsMinParabolic2 S P')
    (hE : E = twoResidual P') (hshort : IsShort2 E) {A : Type} [Group A] [IsSimpleGroup A]
    (α : ↥E →* A) (hα : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥E) :
    ⁅E, S⁆ = E := by
  classical
  have hSyl : IsSylowTwoOf S P' := isSylowTwoOf_of_isSylowOf hmin.1
  have hSP : S ≤ P' := hSyl.1
  have hEP : E ≤ P' := hE ▸ twoResidual_le P'
  have hEn : P' ≤ Subgroup.normalizer (E : Set Γ) := hE ▸ le_normalizer_twoResidual P'
  have hSE : S ≤ Subgroup.normalizer (E : Set Γ) := hSP.trans hEn
  have hPSE : S ⊔ E = P' := hE ▸ sup_twoResidual_eq hSyl
  have hQS : pCoreOf 2 E ≤ S := by
    have h1 : pCoreOf 2 E ≤ pCoreOf 2 P' := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E |>.trans hEP)
        (hEn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E)
    exact h1.trans hSyl.pCoreOf_le
  have hKE : ⁅E, S⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he s hs
    have h1 : s * e⁻¹ * s⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hSE hs) e⁻¹).1 (E.inv_mem he)
    have h2 : ⁅e, s⁆ = e * (s * e⁻¹ * s⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact E.mul_mem he h1
  have hnotle : ¬ ⁅E, S⁆ ≤ pCoreOf 2 E := by
    intro hKQ
    apply hmin.2.1
    rw [← hPSE]
    refine sup_le Subgroup.le_normalizer ?_
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ e' ∈ E, ∀ s ∈ S, e' * s * e'⁻¹ ∈ S := by
      intro e' he' s hs
      have h1 : ⁅e', s⁆ ∈ ⁅E, S⁆ := Subgroup.commutator_mem_commutator he' hs
      have h2 : ⁅e', s⁆ * s = e' * s * e'⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [← h2]
      exact S.mul_mem (hQS (hKQ h1)) hs
    intro s
    refine ⟨fun hs => key e he s hs, fun hs => ?_⟩
    have := key e⁻¹ (E.inv_mem he) _ hs
    simpa [mul_assoc] using this
  set K' : Subgroup ↥E := (⁅E, S⁆).subgroupOf E with hK'
  have hKnorm : E ≤ Subgroup.normalizer ((⁅E, S⁆ : Subgroup Γ) : Set Γ) :=
    Subgroup.normalizer_commutator_ge_left E S
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mpr hKnorm
  have hαK : (K'.map α) = ⊤ := by
    have : (K'.map α).Normal := hK'n.map α hα
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K'.map α) with h | h
    · exfalso
      apply hnotle
      intro k hk
      have hkE : k ∈ E := hKE hk
      have hk' : (⟨k, hkE⟩ : ↥E) ∈ K' := Subgroup.mem_subgroupOf.2 hk
      have h1 : α ⟨k, hkE⟩ ∈ K'.map α := Subgroup.mem_map_of_mem α hk'
      rw [h, Subgroup.mem_bot] at h1
      have h2 : (⟨k, hkE⟩ : ↥E) ∈ α.ker := h1
      rw [hαk] at h2
      exact (mem_pCore_iff_mem_pCoreOf (E := E) ⟨k, hkE⟩).1 h2
    · exact h
  have hq : IsPGroup 2 (↥E ⧸ K') := by
    intro x
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : α e ∈ K'.map α := hαK ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hke⟩ := h1
    have h2 : e * k⁻¹ ∈ CFSG.pCore 2 ↥E := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hke, mul_inv_cancel]
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥E)) ⟨e * k⁻¹, h2⟩
    refine ⟨j, ?_⟩
    have hj' : (e * k⁻¹) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hmk : (QuotientGroup.mk e : ↥E ⧸ K') = QuotientGroup.mk (e * k⁻¹) := by
      rw [QuotientGroup.eq]
      simpa using K'.inv_mem hk
    rw [hmk, ← QuotientGroup.mk_pow, hj']
    rfl
  have htop : K' = ⊤ := hshort.1 K' hq
  have hEle : E ≤ ⁅E, S⁆ := (Subgroup.subgroupOf_eq_top).1 htop
  exact le_antisymm hKE hEle

end CFSG.CGT.PushingUpLit.BHS6
