module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWSyl
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWNonW

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer


theorem l34Lemma43SylowStepKS_of_certs : L34Lemma43SylowStepKS := by
  intro G _ _ a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ _ _ _ _ _ hSM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hS, -, -⟩ := id hset
  set M : Subgroup G := normalizer (W : Set G) with hM
  obtain ⟨F, hFP, hF, s, hsS, hss, hsF, hsn⟩ := exists_eight_not_isolated hset h3
  have hFS : F ≤ S := hFP.trans inf_le_left
  have hFW : wGroup F = W := hWB F (hFP.trans (inf_le_inf_left _ le_sup_left))
    (hF.1.isAbelianTwoOfRank hF.2.ge)
  obtain ⟨Q, hSQ⟩ := (GrS4.isPGroup_of_isSylowTwoIn hS).exists_le_sylow
  refine ⟨Q, le_antisymm ?_ hSQ⟩
  by_contra hQS
  have hlt : S.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hQS fun q hq => ?_
    have : (⟨q, hq⟩ : Q) ∈ S.subgroupOf Q := by rw [htop]; exact mem_top _
    exact mem_subgroupOf.mp this
  have hnil : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hconj : ∀ z ∈ S, (y : G) * z * (y : G)⁻¹ ∈ S := by
    intro z hz
    have hzQ : z ∈ Q := hSQ hz
    have hz' : (⟨z, hzQ⟩ : Q) ∈ S.subgroupOf Q := mem_subgroupOf.mpr hz
    have := (mem_normalizer_iff.mp hyN _).mp hz'
    exact mem_subgroupOf.mp this
  have hFy : F.map (MulAut.conj (y : G)).toMonoidHom ≤ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hconj z (hFS hz)
  have hyM : (y : G) ∈ M := by
    have hns : ∃ t ∈ S, t * t = 1 ∧
        (∀ e ∈ F.map (MulAut.conj (y : G)).toMonoidHom, t * e = e * t) ∧
        t ∉ F.map (MulAut.conj (y : G)).toMonoidHom := by
      refine ⟨(y : G) * s * (y : G)⁻¹, hconj s (mem_inf.mp hsS).1, ?_, ?_, ?_⟩
      · rw [show (y : G) * s * (y : G)⁻¹ * ((y : G) * s * (y : G)⁻¹) =
          (y : G) * (s * s) * (y : G)⁻¹ by group, hss]
        group
      · rintro _ ⟨e, he, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show (y : G) * s * (y : G)⁻¹ * ((y : G) * e * (y : G)⁻¹) =
          (y : G) * (s * e) * (y : G)⁻¹ by group, hsF e he]
        group
      · rintro ⟨e, he, hee⟩
        apply hsn
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hee
        have : e = s := mul_left_cancel (mul_right_cancel hee)
        rw [← this]
        exact he
    have hFy8 : IsEightGroup (F.map (MulAut.conj (y : G)).toMonoidHom) :=
      ⟨hF.1.map_conj _, by rw [card_map_of_injective (MulAut.conj (y : G)).injective, hF.2]⟩
    have h1 := wGroup_eq_of_not_stronglyIsolated hset hcent hWB hFy hFy8 hns
    rw [wGroup_map_conj, hFW] at h1
    exact mem_normalizer_iff_map_conj_eq.mpr h1
  have hQ' : IsPGroup 2 ↥(S ⊔ zpowers (y : G)) :=
    Q.isPGroup'.to_le (sup_le hSQ (zpowers_le.mpr y.2))
  have heq := hSM.eq_of_le le_sup_left (sup_le hSM.1 (zpowers_le.mpr hyM)) hQ'
  have hyS' : (y : G) ∈ S ⊔ zpowers (y : G) :=
    (le_sup_right : zpowers (y : G) ≤ S ⊔ zpowers (y : G)) (mem_zpowers (y : G))
  rw [heq] at hyS'
  exact hyS (mem_subgroupOf.mpr hyS')

end CFSG.ComponentClassification.GrSLit.GrS5S
