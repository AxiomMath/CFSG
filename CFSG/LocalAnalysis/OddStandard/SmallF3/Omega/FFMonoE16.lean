module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoE16Aux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

@[expose] def IsLiftE16 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) : Prop :=
  U ≤ ffP0 hQ fr ∧ piOrth Q ∈ U ∧ Nat.card U = 32 ∧
    (∀ u ∈ U, u * u = 1 ∨ u * u = piOrth Q) ∧
    ∀ u ∈ U, ∀ v ∈ U, u * v = v * u ∨ u * v = piOrth Q * (v * u)

theorem ffB0_isLiftE16 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    IsLiftE16 hQ fr (ffB0 fr) := by
  refine ⟨ffB0_le_ffP0 hQ fr, piOrth_mem_ffB0 fr, ffB0_card fr, ?_, ?_⟩
  · intro u hu
    exact Or.inl (ffB0_mul_self fr hu)
  · intro u hu v hv
    exact Or.inl (ffB0_comm fr hu hv)

theorem ff_liftE16_subset (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    {U : Subgroup (OGroup Q)} (hU : IsLiftE16 hQ fr U) (hne : U ≠ ffB0 fr) {u : OGroup Q}
    (hu : u ∈ U) :
    ∃ σ ∈ ffK0, ∃ J ∈ ffF0, u = fr.permOrth σ * fr.signChange J := by
  classical
  obtain ⟨hUle, -, hUcard, hsq, hcomm⟩ := hU
  let ρ : ↥U →* Equiv.Perm (Fin 6) := ffRhoU hQ fr U hUle
  let R : Subgroup (Equiv.Perm (Fin 6)) := ρ.range
  have hRmono : ∀ r ∈ R, r ∈ monoD := by
    intro r hr
    change r ∈ ρ.range at hr
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hr
    exact ffRhoU_mem_monoD hQ fr U hUle v
  have hR2 : ∀ r ∈ R, r * r = 1 := by
    intro r hr
    change r ∈ ρ.range at hr
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hr
    exact ffRhoU_mul_self hQ fr U hUle hsq v
  have hRcard_le : Nat.card R ≤ 4 := ffExp2_card_le R hRmono hR2
  have hkerF : Nat.card ρ.ker = (ffFU fr U).card := ffRhoU_ker_card hQ fr U hUle
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hUB0 : U ≤ ffB0 fr := by
      intro w hw
      have h1 : ρ ⟨w, hw⟩ ∈ R := MonoidHom.mem_range.mpr ⟨⟨w, hw⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      obtain ⟨J, hJ, heq⟩ := ffRhoU_spec hQ fr U hUle ⟨w, hw⟩
      rw [show ffRhoU hQ fr U hUle ⟨w, hw⟩ = 1 from h1, fr.permOrth_one, one_mul] at heq
      exact (mem_ffB0_iff fr).mpr ⟨J, hJ, heq⟩
    haveI : Finite (ffB0 fr) :=
      Nat.finite_of_card_ne_zero (by rw [ffB0_card fr]; norm_num)
    have hcardB0 : Nat.card (ffB0 fr) ≤ Nat.card U := by rw [ffB0_card fr, hUcard]
    exact hne (Subgroup.eq_of_le_of_card_ge hUB0 hcardB0)
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  have ha1' : a.1 ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haR : a.1 ∈ (ffRhoU hQ fr U hUle).range := a.2
  have hFsub : ffFU fr U ⊆ ffF a.1 := ffFU_subset_ffF hQ fr U hUle hcomm haR
  have hFcard_le : (ffFU fr U).card ≤ 8 := by
    have h := Finset.card_le_card hFsub
    rwa [ffF_card (hRmono a.1 a.2) (hR2 a.1 a.2) ha1'] at h
  have hcardmul : (ffFU fr U).card * Nat.card R = 32 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hkerF, hUcard] at h
    exact h
  have hR4 : Nat.card R = 4 := by
    have h8R : 8 * Nat.card R = 32 := by
      refine le_antisymm ?_ ?_
      · have h := Nat.mul_le_mul_left 8 hRcard_le
        omega
      · have hle : (ffFU fr U).card * Nat.card R ≤ 8 * Nat.card R :=
          Nat.mul_le_mul hFcard_le le_rfl
        rwa [hcardmul] at hle
    omega
  have hF8 : (ffFU fr U).card = 8 := by
    rw [hR4] at hcardmul
    omega
  have hF_eq : ∀ σ ∈ R, σ ≠ 1 → ffFU fr U = ffF σ := by
    intro σ hσR hσ1
    have hσrange : σ ∈ (ffRhoU hQ fr U hUle).range := hσR
    have hsub := ffFU_subset_ffF hQ fr U hUle hcomm hσrange
    have hcard : (ffF σ).card ≤ (ffFU fr U).card := by
      rw [ffF_card (hRmono σ hσR) (hR2 σ hσR) hσ1, hF8]
    exact Finset.eq_of_subset_of_card_le hsub hcard
  have hcard_univ : (Finset.univ : Finset ↥R).card = 4 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hR4]
  let s : Finset ↥R := (Finset.univ : Finset ↥R).erase (1 : ↥R)
  have ha_mem : a ∈ s := by
    show a ∈ (Finset.univ : Finset ↥R).erase (1 : ↥R)
    exact Finset.mem_erase.mpr ⟨ha1, Finset.mem_univ a⟩
  have hs_card : s.card = 3 := by
    show ((Finset.univ : Finset ↥R).erase (1 : ↥R)).card = 3
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), hcard_univ]
  let s2 : Finset ↥R := s.erase a
  have hs2_card : s2.card = 2 := by
    show (s.erase a).card = 2
    rw [Finset.card_erase_of_mem ha_mem, hs_card]
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by rw [hs2_card]; norm_num : 0 < s2.card)
  have hb_ne_a : b ≠ a := (Finset.mem_erase.mp (show b ∈ s.erase a from hb)).1
  have hb_s : b ∈ s := (Finset.mem_erase.mp (show b ∈ s.erase a from hb)).2
  have hb1 : b ≠ 1 :=
    (Finset.mem_erase.mp (show b ∈ (Finset.univ : Finset ↥R).erase (1 : ↥R) from hb_s)).1
  have hb1' : b.1 ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hba : a.1 ≠ b.1 := fun h => hb_ne_a (Subtype.ext h.symm)
  have hFa : ffFU fr U = ffF a.1 := hF_eq a.1 a.2 ha1'
  have hFb : ffFU fr U = ffF b.1 := hF_eq b.1 b.2 hb1'
  have hK0 : a.1 ∈ ffK0 ∧ b.1 ∈ ffK0 :=
    ffF_ne_of_ne (hRmono a.1 a.2) (hR2 a.1 a.2) ha1'
      (hRmono b.1 b.2) (hR2 b.1 b.2) hb1' hba (hFa.symm.trans hFb)
  have hRK0 : ∀ σ ∈ R, σ ∈ ffK0 := by
    intro σ hσR
    by_cases hσ1 : σ = 1
    · rw [hσ1]; decide
    · by_cases hσa : σ = a.1
      · rw [hσa]; exact hK0.1
      · have hFσ : ffFU fr U = ffF σ := hF_eq σ hσR hσ1
        exact (ffF_ne_of_ne (hRmono σ hσR) (hR2 σ hσR) hσ1
          (hRmono a.1 a.2) (hR2 a.1 a.2) ha1' hσa (hFσ.symm.trans hFa)).1
  have hF0 : ffFU fr U = ffF0 := by
    rw [hFa, ffF_eq_iff (hRmono a.1 a.2) (hR2 a.1 a.2) ha1']
    exact hK0.1
  obtain ⟨σ, -, J, hJ, rfl⟩ := (mem_ffP0_iff hQ fr).mp (hUle hu)
  let w : ↥U := ⟨fr.permOrth σ * fr.signChange J, hu⟩
  have hρ : ffRhoU hQ fr U hUle w = σ := ffRhoU_eq_of hQ fr U hUle w rfl
  have hσR : σ ∈ R := by
    change σ ∈ (ffRhoU hQ fr U hUle).range
    rw [← hρ]
    exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hσK0 : σ ∈ ffK0 := hRK0 σ hσR
  have hJ0 : J ∈ ffF0 := by
    by_cases hσ1 : σ = 1
    · have hJF : J ∈ ffFU fr U :=
        (mem_ffFU_iff).mpr ⟨hJ, by simpa [hσ1, fr.permOrth_one] using hu⟩
      rwa [hF0] at hJF
    · have hmap : J ∈ ffF σ := by
        have hsqw := hsq (fr.permOrth σ * fr.signChange J) hu
        have hcomp : (fr.permOrth σ * fr.signChange J) * (fr.permOrth σ * fr.signChange J) =
            fr.permOrth (σ * σ) *
              fr.signChange (symmDiff (J.map σ⁻¹.toEmbedding) J) := by
          rw [ffMono_mul]
        have hcase : σ * σ = 1 ∧ (symmDiff (J.map σ⁻¹.toEmbedding) J = ∅ ∨
            symmDiff (J.map σ⁻¹.toEmbedding) J = Finset.univ) := by
          rcases hsqw with h | h
          · have h1 : (1 : OGroup Q) = fr.permOrth 1 * fr.signChange (∅ : Finset (Fin 6)) := by
              rw [fr.permOrth_one, fr.signChange_empty, one_mul]
            obtain ⟨hσ2, hsymm⟩ := ffMono_unique fr (hcomp.symm.trans (h.trans h1))
            exact ⟨hσ2, Or.inl hsymm⟩
          · have hpi : piOrth Q =
                fr.permOrth 1 * fr.signChange (Finset.univ : Finset (Fin 6)) := by
              rw [fr.permOrth_one, one_mul, fr.piOrth_eq_signChange_univ]
            obtain ⟨hσ2, hsymm⟩ := ffMono_unique fr (hcomp.symm.trans (h.trans hpi))
            exact ⟨hσ2, Or.inr hsymm⟩
        obtain ⟨hσ2, hsymm⟩ := hcase
        have hinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
        have hmap' : J.map σ.toEmbedding = J ∨ J.map σ.toEmbedding = Jᶜ := by
          rcases hsymm with h | h
          · left
            have h' := Finset.symmDiff_eq_empty.mp h
            rwa [hinv] at h'
          · right
            have h' := eq_compl_of_symmDiff_eq_univ h
            rwa [hinv] at h'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ J, hJ, hmap'⟩
      rw [← hF_eq σ hσR hσ1] at hmap
      rwa [hF0] at hmap
  exact ⟨σ, hσK0, J, hJ0, rfl⟩

theorem ff_liftE16_unique (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    {U₁ U₂ : Subgroup (OGroup Q)} (h₁ : IsLiftE16 hQ fr U₁) (h₂ : IsLiftE16 hQ fr U₂)
    (n₁ : U₁ ≠ ffB0 fr) (n₂ : U₂ ≠ ffB0 fr) : U₁ = U₂ := by
  classical
  set S : Set (OGroup Q) := (fun x : Equiv.Perm (Fin 6) × Finset (Fin 6) =>
    fr.permOrth x.1 * fr.signChange x.2) '' (↑(ffK0 ×ˢ ffF0) : Set _) with hSdef
  have hScard : S.ncard ≤ 32 := by
    rw [hSdef]
    calc ((fun x : Equiv.Perm (Fin 6) × Finset (Fin 6) =>
          fr.permOrth x.1 * fr.signChange x.2) ''
            (↑(ffK0 ×ˢ ffF0) : Set (Equiv.Perm (Fin 6) × Finset (Fin 6)))).ncard
        ≤ (↑(ffK0 ×ˢ ffF0) : Set (Equiv.Perm (Fin 6) × Finset (Fin 6))).ncard :=
          Set.ncard_image_le
            (s := (↑(ffK0 ×ˢ ffF0) : Set (Equiv.Perm (Fin 6) × Finset (Fin 6))))
            (f := fun x : Equiv.Perm (Fin 6) × Finset (Fin 6) =>
              fr.permOrth x.1 * fr.signChange x.2)
            (hs := Finset.finite_toSet (ffK0 ×ˢ ffF0))
      _ = (ffK0 ×ˢ ffF0).card := Set.ncard_coe_finset (ffK0 ×ˢ ffF0)
      _ = 32 := by
            rw [Finset.card_product]
            have h4 : ffK0.card = 4 := by decide
            have h5 : ffF0.card = 8 := by decide
            rw [h4, h5]
  have hU₁sub : (U₁ : Set (OGroup Q)) ⊆ S := by
    rw [hSdef]
    intro x hx
    obtain ⟨σ, hσ, J, hJ, rfl⟩ := ff_liftE16_subset hQ fr h₁ n₁ hx
    exact ⟨(σ, J), by simpa [Finset.mem_product] using ⟨hσ, hJ⟩, rfl⟩
  have hU₂sub : (U₂ : Set (OGroup Q)) ⊆ S := by
    rw [hSdef]
    intro x hx
    obtain ⟨σ, hσ, J, hJ, rfl⟩ := ff_liftE16_subset hQ fr h₂ n₂ hx
    exact ⟨(σ, J), by simpa [Finset.mem_product] using ⟨hσ, hJ⟩, rfl⟩
  have hU₁card : (U₁ : Set (OGroup Q)).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]
    exact h₁.2.2.1
  have hU₂card : (U₂ : Set (OGroup Q)).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]
    exact h₂.2.2.1
  have hU₁eq : (U₁ : Set (OGroup Q)) = S :=
    Set.eq_of_subset_of_ncard_le hU₁sub (by rw [hU₁card]; exact hScard)
  have hU₂eq : (U₂ : Set (OGroup Q)) = S :=
    Set.eq_of_subset_of_ncard_le hU₂sub (by rw [hU₂card]; exact hScard)
  exact SetLike.ext'_iff.mpr (hU₁eq.trans hU₂eq.symm)

end CFSG.OddStandard.SmallF3.Omega
