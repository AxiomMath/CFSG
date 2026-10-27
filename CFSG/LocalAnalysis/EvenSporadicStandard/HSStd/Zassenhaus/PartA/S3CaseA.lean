module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseAF
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv Subgroup

theorem caseA_data {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D} (h : DShape D t K)
    (e : ↥(GorensteinWalter.componentLayerOf (⊤ : Subgroup D)) ≃*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    Nonempty (CaseAData D t) := by
  obtain ⟨ψ⟩ := h.K_S5
  set E : Subgroup D := GorensteinWalter.componentLayerOf (⊤ : Subgroup D) with hE
  have hn : E.Normal :=
    ⟨fun x hx g => (GorensteinWalter.componentLayerOf_isNormalIn (⊤ : Subgroup D)).2 g
      (Subgroup.mem_top g) x hx⟩
  have hpc : ((∀ a, ∃ c, t * s3a_j₁ E e a * t⁻¹ = s3a_j₁ E e c) ∧
      ∀ b, ∃ c, t * s3a_j₂ E e b * t⁻¹ = s3a_j₂ E e c) → False :=
    fun hp => s3a_not_preserved h ψ E e hp
  refine ⟨{ Y₁ := (s3a_j₁ E e).range
            Y₂ := (s3a_j₂ E e).range
            e₁ := (MonoidHom.ofInjective (s3a_j₁_injective E e)).symm
            comm := ?_
            perm := ?_
            swap₁ := ?_
            swap₂ := ?_
            faithful := ?_ }⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact s3a_j_comm E e a b
  · intro d
    rcases s3a_perm_cases E e d with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, rfl⟩
        obtain ⟨c, hc⟩ := h1 a
        exact ⟨c, hc.symm⟩
      · rintro _ ⟨b, rfl⟩
        obtain ⟨c, hc⟩ := h2 b
        exact ⟨c, hc.symm⟩
    · right
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, rfl⟩
        obtain ⟨c, hc⟩ := h1 a
        exact ⟨c, hc.symm⟩
      · rintro _ ⟨b, rfl⟩
        obtain ⟨c, hc⟩ := h2 b
        exact ⟨c, hc.symm⟩
  · rintro _ ⟨a, rfl⟩
    rcases s3a_perm_cases E e t with hp | ⟨h1, h2⟩
    · exact (hpc hp).elim
    · obtain ⟨c, hc⟩ := h1 a
      exact ⟨c, hc.symm⟩
  · rintro _ ⟨b, rfl⟩
    rcases s3a_perm_cases E e t with hp | ⟨h1, h2⟩
    · exact (hpc hp).elim
    · obtain ⟨c, hc⟩ := h2 b
      exact ⟨c, hc.symm⟩
  · intro d h1 h2
    refine s3a_faithful h ψ h.zstar E e (fun x hx => ?_)
    obtain ⟨⟨a, b⟩, rfl⟩ := s3a_fE_surj E e hx
    rw [s3a_fE_mul]
    have ha : d * s3a_j₁ E e a = s3a_j₁ E e a * d := h1 _ ⟨a, rfl⟩
    have hb : d * s3a_j₂ E e b = s3a_j₂ E e b * d := h2 _ ⟨b, rfl⟩
    calc d * (s3a_j₁ E e a * s3a_j₂ E e b) = (d * s3a_j₁ E e a) * s3a_j₂ E e b := by
          rw [mul_assoc]
      _ = s3a_j₁ E e a * (d * s3a_j₂ E e b) := by rw [ha, mul_assoc]
      _ = s3a_j₁ E e a * (s3a_j₂ E e b * d) := by rw [hb]
      _ = (s3a_j₁ E e a * s3a_j₂ E e b) * d := by rw [mul_assoc]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
