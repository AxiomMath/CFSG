module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoE
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIso
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoCount

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34


theorem l34WCriterionD1Fact_of_certs : L34WCriterionD1Fact := by
  intro G _ _ J S hJ hL hT hS2 hSN hZ E hES hE h2 hEC
  obtain ⟨D⟩ := exists_wStd hJ hL hT hSN
  have hE₁E : E ⊓ withKernel J ≤ E := inf_le_left
  have hE₁C : E ⊓ withKernel J ≤ coreActionKernel J := by
    have hle : E ⊓ coreActionKernel J ≤ E ⊓ withKernel J := inf_le_inf_left _ le_sup_right
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h2]; exact hEC)
    rw [← heq]
    exact inf_le_right
  obtain ⟨e₁, he₁E, he₁K⟩ : ∃ e₁ ∈ E, e₁ ∉ withKernel J := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (fun g hg => mem_inf.mpr ⟨hg, hne g hg⟩ :
      E ≤ E ⊓ withKernel J)
    rw [hE.2, h2] at h1
    norm_num at h1
  obtain ⟨-, hF₁e, hF₁c⟩ := sup_zpowers_inf_withKernel (hE.1.mono hE₁E) inf_le_right
    (hE.1.2 e₁ he₁E) he₁K (fun w hw => hE.1.1 w (hE₁E hw) e₁ he₁E)
  have hF₁E : E ⊓ withKernel J ⊔ zpowers e₁ ≤ E := sup_le hE₁E (zpowers_le.mpr he₁E)
  obtain ⟨e₂, he₂E, he₂F⟩ : ∃ e₂ ∈ E, e₂ ∉ E ⊓ withKernel J ⊔ zpowers e₁ := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (fun g hg => hne g hg :
      E ≤ E ⊓ withKernel J ⊔ zpowers e₁)
    rw [hE.2, hF₁c, h2] at h1
    norm_num at h1
  have he₂K : e₂ ∉ withKernel J := fun h => he₂F (mem_sup_left (mem_inf.mpr ⟨he₂E, h⟩))
  obtain ⟨-, hFc⟩ := GrS4.isElemTwo_sup_zpowers hF₁e (hE.1.2 e₂ he₂E) he₂F
    (fun w hw => hE.1.1 w (hF₁E hw) e₂ he₂E)
  have hEeq : E ⊓ withKernel J ⊔ zpowers e₁ ⊔ zpowers e₂ = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le hF₁E (zpowers_le.mpr he₂E)) (by rw [hFc, hF₁c, h2, hE.2])
  obtain ⟨t₁, ht₁, i₁, hi₁, hy₁, -, hβ₁⟩ := D.model (hES he₁E)
  obtain ⟨t₂, ht₂, i₂, hi₂, hy₂, -, hβ₂⟩ := D.model (hES he₂E)
  obtain ⟨hS₁, hy₁2⟩ := D.outer_spec hJ (hES he₁E) (hE.1.2 e₁ he₁E) he₁K hi₁ hy₁
  obtain ⟨hS₂, hy₂2⟩ := D.outer_spec hJ (hES he₂E) (hE.1.2 e₂ he₂E) he₂K hi₂ hy₂
  have hcomm : D.ψ ⟨e₂, hES he₂E⟩ * D.ψ ⟨e₁, hES he₁E⟩ =
      D.ψ ⟨e₁, hES he₁E⟩ * D.ψ ⟨e₂, hES he₂E⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE.1.1 e₂ he₂E e₁ he₁E)
  have hc : yPerm t₁ i₁ * yPerm t₂ i₂ = yPerm t₂ i₂ * yPerm t₁ i₁ := by
    rw [← hy₁, ← hy₂, ← mul_inv_rev, ← mul_inv_rev, hcomm]
  have hfull : kbFull D.kb = false := by
    cases hf : kbFull D.kb
    · rfl
    · exact absurd (D.Z_eq_bot_of_kbFull hS2 hf) hZ
  obtain ⟨a, ha0, b, hb0, hba, ha1, ha2, ha3, hb1, hb2, hb3⟩ :=
    wIsoD1Parts.d1 D.kb D.hkbL hfull t₁ ht₁ i₁ hi₁ t₂ ht₂ i₂ hi₂ hS₁ hS₂ hy₁2 hy₂2 hc
  have ha : a ∈ (fixInvs D.kb t₁ i₁).filter fun x => fixKB D.kb t₂ i₂ x :=
    List.mem_filter.2 ⟨mem_fixInvs.2 ⟨ha0, ha1, ha3⟩, ha2⟩
  have hb : b ∈ (fixInvs D.kb t₁ i₁).filter fun x => fixKB D.kb t₂ i₂ x :=
    List.mem_filter.2 ⟨mem_fixInvs.2 ⟨hb0, hb1, hb3⟩, hb2⟩
  have hψ1 : ∀ w (hw : w ∈ E ⊓ withKernel J), D.ψ ⟨w, hES (hE₁E hw)⟩ = 1 ∨
      D.ψ ⟨w, hES (hE₁E hw)⟩ = wordPerm (tg 0) := fun w hw =>
    Or.inl ((D.ψ_eq_one_iff hJ (hES (hE₁E hw))).2 (hE₁C hw))
  have hinv : ∀ x ∈ (fixInvs D.kb t₁ i₁).filter fun x => fixKB D.kb t₂ i₂ x,
      ∃ p, ∃ hpS : p ∈ S, ∃ hpJ : p ∈ J, p * p = 1 ∧ p ≠ 1 ∧ (∀ g ∈ E, p * g = g * p) ∧
        jq J ⟨p, hpJ⟩ = nfM D.l x := by
    intro x hx
    obtain ⟨hxF, hx2⟩ := List.mem_filter.mp hx
    have hx64 : x.1 < 64 := lt_of_mem_allM (mem_fixInvs.mp hxF).1
    have hx0 : eqKB D.kb (mulM x (0, 0, 0)) (mulM (0, 0, 0) x) = true := by
      rw [commKB_iff D.hQ D.hkb hx64 (by norm_num)]
      show nfM D.l x * nfM D.l oneM = nfM D.l oneM * nfM D.l x
      rw [nfM_one, mul_one, one_mul]
    obtain ⟨p, hpS, hpJ, hp2, hp1, hpc, -, hpe⟩ := D.exists_of_model hJ hS2
      (fun w hw => hES (hE₁E hw)) (by norm_num) hψ1 (hES he₁E) ht₁ hi₁ hβ₁ hxF hx0
    have hpe₂ := D.comm_of_fix hS2 (hES he₂E) ht₂ hi₂ hβ₂ hx64 hx2 (mem_inf.mpr ⟨hpS, hpJ⟩) hpe
    refine ⟨p, hpS, hpJ, hp2, hp1, fun g hg => ?_, hpe⟩
    have hle : E ⊓ withKernel J ⊔ zpowers e₁ ⊔ zpowers e₂ ≤ centralizer ({p} : Set G) := by
      refine sup_le (fun g hg => mem_centralizer_singleton_iff.mpr (hpc g hg).symm)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hpe₂.symm))
    rw [← hEeq] at hg
    exact (mem_centralizer_singleton_iff.mp (hle hg)).symm
  obtain ⟨pa, hpaS, hpaJ, hpa2, hpa1, hpac, hpae⟩ := hinv a ha
  obtain ⟨pb, hpbS, hpbJ, hpb2, hpb1, hpbc, hpbe⟩ := hinv b hb
  have hab : pa ≠ pb := by
    rintro rfl
    have ha64 : a.1 < 64 := lt_of_mem_allM (mem_fixInvs.mp (List.mem_filter.mp ha).1).1
    have hb64 : b.1 < 64 := lt_of_mem_allM (mem_fixInvs.mp (List.mem_filter.mp hb).1).1
    have h3 : nfM D.l b = nfM D.l a := by rw [← hpae, ← hpbe]
    rw [← eqKB_iff D.hQ D.hkb hb64 ha64] at h3
    rw [h3] at hba
    exact Bool.noConfusion hba
  by_cases hpaE : pa ∈ E
  · by_cases hpbE : pb ∈ E
    · exfalso
      have h3 := length_le_card (H := E ⊓ withKernel J) (l := [1, pa, pb])
        (by simp [hpa1.symm, hpb1.symm, hab])
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact one_mem _
          · exact mem_inf.mpr ⟨hpaE, mem_sup_left hpaJ⟩
          · exact mem_inf.mpr ⟨hpbE, mem_sup_left hpbJ⟩)
      rw [h2] at h3
      simp at h3
    · exact ⟨pb, mem_inf.mpr ⟨hpbS, mem_sup_left hpbJ⟩, hpb2, hpbc, hpbE⟩
  · exact ⟨pa, mem_inf.mpr ⟨hpaS, mem_sup_left hpaJ⟩, hpa2, hpac, hpaE⟩

end CFSG.ComponentClassification.GrSLit.GrS5S
