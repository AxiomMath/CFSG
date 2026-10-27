module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrSound

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8Wr

open Subgroup CFSG.EvenSporadicStandard.Fin76b

theorem TabR_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    {ζ α t g₁ g₂ h₁ h₂ : G} (h : TabR ζ α t g₁ g₂ h₁ h₂) :
    TabR (f ζ) (f α) (f t) (f g₁) (f g₂) (f h₁) (f h₂) := by
  obtain ⟨hζζ, hαα, htt, hα1, ht1, hαt, hαtc, hζt, hζα, hh1ζ, hh2ζ, ⟨hg1α, hg1t⟩,
    ⟨hg2α, hg2t⟩, ⟨hh1α, hh1t⟩, ⟨hh2α, hh2t⟩, hsq1, hsq2, hgg, hhh, hgh, hhg, hg1h1,
    hg2h2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [← map_mul, hζζ, map_one]
  · simp only [← map_mul, hαα, map_one]
  · simp only [← map_mul, htt, map_one]
  · exact fun he => hα1 (hf (he.trans (map_one f).symm))
  · exact fun he => ht1 (hf (he.trans (map_one f).symm))
  · exact fun he => hαt (hf he)
  · simp only [← map_mul, hαtc]
  · simp only [← map_mul, hζt]
  · simp only [← map_mul, hζα]
  · simp only [← map_mul, hh1ζ]
  · simp only [← map_mul, hh2ζ]
  · simp only [← map_mul, hg1α]
  · simp only [← map_mul, hg1t]
  · simp only [← map_mul, hg2α]
  · simp only [← map_mul, hg2t]
  · simp only [← map_mul, hh1α]
  · simp only [← map_mul, hh1t]
  · simp only [← map_mul, hh2α]
  · simp only [← map_mul, hh2t]
  · rcases hsq1 with h1 | h1
    · left
      simp only [← map_mul, h1, map_one]
    · right
      simp only [← map_mul, h1]
  · rcases hsq2 with h1 | h1
    · left
      simp only [← map_mul, h1, map_one]
    · right
      simp only [← map_mul, h1]
  · simp only [← map_mul, hgg]
  · simp only [← map_mul, hhh]
  · simp only [← map_mul, hgh]
  · simp only [← map_mul, hhg]
  · simp only [← map_mul, hg1h1]
  · simp only [← map_mul, hg2h2]

theorem no_table_Wfull (hsig : NoTabSig) {ζ α t g₁ g₂ h₁ h₂ : Wfull}
    (h : OuterTable ζ α t g₁ g₂ h₁ h₂) : False := by
  have hT := tabR_of_outerTable h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hP, -⟩ := h
  obtain ⟨hζζ, hαα, htt, hα1, ht1, hαt, hαtc, hζt, hζα, hh1ζ, hh2ζ, -, -, -, -, -, -,
    hgg, hhh, hgh, hhg, hg1h1, hg2h2⟩ := id hT
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup Wfull,
      P' = Subgroup.closure ({α, t, g₁, g₂, h₁, h₂} : Set Wfull) := ⟨_, rfl⟩
  rw [← hP'] at hP
  have gen : ∀ x ∈ ({α, t, g₁, g₂, h₁, h₂} : Set Wfull), x ∈ P' := by
    intro x hx
    rw [hP']
    exact Subgroup.subset_closure hx
  have hζinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζζ
  have hζ2 : ζ⁻¹ * ζ⁻¹ = 1 := by rw [hζinv, hζζ]
  have hh1 : h₁ = ζ * g₁ * ζ⁻¹ := by
    rw [← hh1ζ]
    group
  have hh2 : h₂ = ζ * g₂ * ζ⁻¹ := by
    rw [← hh2ζ]
    group
  have hle : P' ≤ P'.comap (MulAut.conj ζ).toMonoidHom := by
    rw [hP', Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, ← hP']
    rcases hx with h | h | h | h | h | h <;> rw [h]
    · have e : ζ * α * ζ⁻¹ = α * t := by
        calc ζ * α * ζ⁻¹ = α * t * ζ * ζ⁻¹ := by rw [hζα]
          _ = α * t := by group
      show ζ * α * ζ⁻¹ ∈ P'
      rw [e]
      exact P'.mul_mem (gen α (by simp)) (gen t (by simp))
    · have e : ζ * t * ζ⁻¹ = t := by
        calc ζ * t * ζ⁻¹ = t * ζ * ζ⁻¹ := by rw [hζt]
          _ = t := by group
      show ζ * t * ζ⁻¹ ∈ P'
      rw [e]
      exact gen t (by simp)
    · have e : ζ * g₁ * ζ⁻¹ = h₁ := by
        calc ζ * g₁ * ζ⁻¹ = h₁ * ζ * ζ⁻¹ := by rw [hh1ζ]
          _ = h₁ := by group
      show ζ * g₁ * ζ⁻¹ ∈ P'
      rw [e]
      exact gen h₁ (by simp)
    · have e : ζ * g₂ * ζ⁻¹ = h₂ := by
        calc ζ * g₂ * ζ⁻¹ = h₂ * ζ * ζ⁻¹ := by rw [hh2ζ]
          _ = h₂ := by group
      show ζ * g₂ * ζ⁻¹ ∈ P'
      rw [e]
      exact gen h₂ (by simp)
    · have e : ζ * h₁ * ζ⁻¹ = g₁ := by
        rw [hh1]
        calc ζ * (ζ * g₁ * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * g₁ * (ζ⁻¹ * ζ⁻¹) := by group
          _ = g₁ := by rw [hζζ, hζ2, one_mul, mul_one]
      show ζ * h₁ * ζ⁻¹ ∈ P'
      rw [e]
      exact gen g₁ (by simp)
    · have e : ζ * h₂ * ζ⁻¹ = g₂ := by
        rw [hh2]
        calc ζ * (ζ * g₂ * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * g₂ * (ζ⁻¹ * ζ⁻¹) := by group
          _ = g₂ := by rw [hζζ, hζ2, one_mul, mul_one]
      show ζ * h₂ * ζ⁻¹ ∈ P'
      rw [e]
      exact gen g₂ (by simp)
  have hζN : ζ ∈ Subgroup.normalizer P' := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact Subgroup.mem_comap.1 (hle hn)
    · intro hn
      have h2 : ζ * (ζ * n * ζ⁻¹) * ζ⁻¹ ∈ P' := Subgroup.mem_comap.1 (hle hn)
      have e : ζ * (ζ * n * ζ⁻¹) * ζ⁻¹ = n := by
        calc ζ * (ζ * n * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * n * (ζ⁻¹ * ζ⁻¹) := by group
          _ = n := by rw [hζζ, hζ2, one_mul, mul_one]
      rwa [e] at h2
  have hZN : Subgroup.zpowers ζ ≤ Subgroup.normalizer P' := Subgroup.zpowers_le.2 hζN
  have hZ : IsPGroup 2 (Subgroup.zpowers ζ) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hζζ)
  have hS' : IsPGroup 2 (↥(Subgroup.closure ({ζ, α, t, g₁, g₂, h₁, h₂} : Set Wfull))) := by
    have hsup : IsPGroup 2 (↥(Subgroup.zpowers ζ ⊔ P')) :=
      IsPGroup.to_sup_of_normal_right' hZ hP hZN
    refine IsPGroup.to_le hsup ?_
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h | h | h <;> rw [h]
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers ζ)
    · exact Subgroup.mem_sup_right (gen α (by simp))
    · exact Subgroup.mem_sup_right (gen t (by simp))
    · exact Subgroup.mem_sup_right (gen g₁ (by simp))
    · exact Subgroup.mem_sup_right (gen g₂ (by simp))
    · exact Subgroup.mem_sup_right (gen h₁ (by simp))
    · exact Subgroup.mem_sup_right (gen h₂ (by simp))
  obtain ⟨m, hm⟩ := exists_conj_mem_sigSub hS'
  have hT' : TabR (m⁻¹ * ζ * m) (m⁻¹ * α * m) (m⁻¹ * t * m) (m⁻¹ * g₁ * m)
      (m⁻¹ * g₂ * m) (m⁻¹ * h₁ * m) (m⁻¹ * h₂ * m) := by
    have := TabR_map (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective hT
    simpa [MulAut.conj_apply] using this
  have hT'' := TabR_map Wfull.subtype Subtype.val_injective hT'
  exact hsig _ _ _ _ _ _ _
    (Subgroup.mem_subgroupOf.1 (hm ζ (Subgroup.subset_closure (by simp))))
    (Subgroup.mem_subgroupOf.1 (hm α (Subgroup.subset_closure (by simp))))
    (Subgroup.mem_subgroupOf.1 (hm t (Subgroup.subset_closure (by simp))))
    (Subgroup.mem_subgroupOf.1 (hm g₁ (Subgroup.subset_closure (by simp))))
    (Subgroup.mem_subgroupOf.1 (hm g₂ (Subgroup.subset_closure (by simp))))
    (Subgroup.mem_subgroupOf.1 (hm h₁ (Subgroup.subset_closure (by simp))))
    (Subgroup.mem_subgroupOf.1 (hm h₂ (Subgroup.subset_closure (by simp))))
    hT''

end CFSG.EvenSporadicStandard.Fin76b.TS8Wr
