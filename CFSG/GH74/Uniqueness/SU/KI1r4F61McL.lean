module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Sp

public noncomputable section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.GH74.Uniqueness.SU.K.R3

theorem exists_E4_of_simple {C : Type} [Group C] [Finite C] [IsSimpleGroup C]
    (hnab : ∃ a b : C, a * b ≠ b * a) :
    ∃ E : Subgroup C, Open.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  have heven : Even (Nat.card C) := CFSG.GH74.even_card_of_nonabelian_simple hnab
  have h2 : 2 ≤ Open.twoRank C := CFSG.Walter.two_le_twoRank C hnab heven
  obtain ⟨E, -, hEel, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
    (H := (⊤ : Subgroup C)) (k := 2) h2
  exact ⟨E, hEel, by rw [hEcard]; norm_num⟩

theorem fixed_four_of_fixSub_equiv {K C : Type} [Group K] [Group C] (α : MulAut K)
    (eC : ↥(fixSub α) ≃* C) {E : Subgroup C} (hE : Open.IsElemAbelian 2 E)
    (hcard : Nat.card E = 4) :
    ∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  refine ⟨(E.map eC.symm.toMonoidHom).map (fixSub α).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact mem_fixSub.1 x.2
  · exact SU4.isElemAbelian_map _ (SU4.isElemAbelian_map eC.symm.toMonoidHom hE)
  · rw [Subgroup.card_map_of_injective (fixSub α).subtype_injective,
      Subgroup.card_map_of_injective eC.symm.injective]
    exact hcard

theorem mcl_fixSub_equiv
    {G : Type} [Group G] (e : G ≃* NativeSporadic.McL) (α : MulAut G)
    (hα2 : α * α = 1) (hα : α ∉ inner G) : Nonempty (↥(fixSub α) ≃* ↥mclC1) := by
  set θ : G ≃* mclP := e.trans mclPermEquiv
  set β : MulAut mclP := transportAut θ α
  have hβ2 : β * β = 1 := transportAut_mul_self θ hα2
  have hβ : β ∉ inner mclP := transportAut_not_mem_inner θ hα
  obtain ⟨x, hxR, hx⟩ := mcl_autModel.surj β
  have hxP : x ∉ mclP := by
    intro hxP
    apply hβ
    refine ⟨⟨x, hxP⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    rw [hx p]
    rfl
  have hx2 : x * x = 1 := by
    apply mcl_autModel.inj (x * x) (mclR.mul_mem hxR hxR)
    intro p hp
    have h := congrArg (fun φ : MulAut mclP => ((φ ⟨p, hp⟩ : mclP) : Equiv.Perm (Fin 275))) hβ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hx, hx] at h
    calc x * x * p = x * (x * p * x⁻¹) * x⁻¹ * (x * x) := by group
      _ = p * (x * x) := by rw [h]
  have hx1 : x ≠ 1 := fun h1 => hxP (h1 ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x hxR hxo
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hxu : x = g * mclU1 * g⁻¹ := by
    rcases hr with rfl | rfl
    · exfalso
      dsimp only at hxg
      apply hxP
      rw [hxg]
      exact mclP.mul_mem (mclP.mul_mem hg mclT0_facts.1) (mclP.inv_mem hg)
    · dsimp only at hxg
      exact hxg
  have hfix := map_fixSub_conjOn mclP β x hx
  rw [hxu, centralizerIn_conj mclP hg] at hfix
  exact ⟨((fixSubTransportEquiv θ α).trans ((((fixSub β).equivMapOfInjective mclP.subtype
    mclP.subtype_injective).trans (MulEquiv.subgroupCongr hfix)))).trans
      (conjEquiv mclC1 g).symm⟩

theorem strictSp_McL :
    StrictFamSp .McL := by
  intro K _ _ ⟨e⟩
  have : IsSimpleGroup (NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.fam_mcl_simplicity.2.2
  have hsK : IsSimpleGroup K := e.isSimpleGroup
  have hnab : ∃ a b : K, a * b ≠ b * a :=
    FamSp1.exists_noncomm_of_simple (by
      rw [Nat.card_congr e.toEquiv]
      show ¬ (Nat.card NativeSporadic.McL).Prime
      rw [CFSG.Sporadic.McL.card_McL]
      norm_num)
  refine StrictFix.of_outer hnab fun α hα2 hα => ?_
  have hα2' : α * α = 1 := by rw [← pow_two]; exact hα2
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K :=
    fun ⟨g, hg⟩ => hα ⟨g, hg.symm⟩
  obtain ⟨eC⟩ := mcl_fixSub_equiv e α hα2' hαin
  obtain ⟨hs, hnabC, -⟩ := mclC1_simple
  have : Finite ↥mclC1 := inferInstance
  obtain ⟨E, hEel, hEcard⟩ := exists_E4_of_simple hnabC
  exact fixed_four_of_fixSub_equiv α eC hEel hEcard

end CFSG.GH74.Uniqueness.SU.K.R4
