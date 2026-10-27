module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GRow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205AzBlock
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205MNorm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4 CFSG.Open
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
open scoped commutatorElement

@[expose] def G2ModelInnerOddFree : Prop :=
  ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L],
    CFSG.Blueprint.LieModel L .G2 0 3 1 → Q3NM.AutOddFreeInner L

section Subnormal

variable {X : Type} [Group X] [Finite X]

theorem isSubnormal_map_omegaGen_aStarG {Φ : Set (Subgroup X)} {KA : Subgroup X} (hKA : KA ∈ Φ)
    (hΘ : Thm3A.Thm3RConclG Φ KA) (hinv : ConjInvariant Φ) {Y : Type} [Group Y]
    (q : X →* Y) (hq : Function.Surjective q) :
    ((omegaGen (aStar Φ KA)).map q).IsSubnormal := by
  obtain ⟨⟨h1, h2⟩, -⟩ := hΘ
  have hsub : aStar Φ KA ⊆ Φ := fun J hJ => T3Core.mem_of_mem_aStar hKA hJ
  have hMN : omegaGen (aStar Φ KA) ≤ omegaGen Φ := iSup₂_le fun J hJ => le_omegaGen (hsub hJ)
  have hNM : omegaGen Φ ≤ Subgroup.normalizer (omegaGen (aStar Φ KA) : Set X) := by
    refine iSup₂_le fun P hP => ?_
    by_cases hPv : P ∈ vStar Φ KA
    · have hPa : P ∈ aStar Φ KA := by
        rw [h1]
        exact hPv
      exact (le_omegaGen hPa).trans Subgroup.le_normalizer
    · refine le_normalizer_iSup_of_forall (S := aStar Φ KA) fun p hp Q hQ x hx => ?_
      have hQv : Q ∈ vStar Φ KA := by
        rw [← h1]
        exact hQ
      exact conj_mem_of_commutator_le
        ((h2 P hP hPv Q hQv).trans (inf_le_right.trans (oddCoreOf_le_self Q))) hp hx
  have hNbar : (omegaGen Φ).map q ≤
      Subgroup.normalizer (((omegaGen (aStar Φ KA)).map q : Subgroup Y) : Set Y) :=
    (Subgroup.map_mono hNM).trans (Subgroup.le_normalizer_map q)
  have hMbar : (omegaGen (aStar Φ KA)).map q ≤ (omegaGen Φ).map q := Subgroup.map_mono hMN
  exact Subgroup.IsSubnormal.step _ _ hMbar ((omegaGen_normal hinv).map q hq).isSubnormal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hMbar).mpr hNbar)

end Subnormal

theorem hyp51_of_rows_blockG (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12 : TwinCentRes.ModelFactM12)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    {Z Y : Type} [Group Z] [Finite Z] [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}
    {P : Subgroup Y} (hrows : Thm3A.Thm3RowsG Ω P) {T : Subgroup Z}
    (F : ↥T →* (↥P ⧸ classicalInvolutionOddCore ↥P)) (hFs : Function.Surjective F)
    (hK : Odd (Nat.card F.ker)) {ζ : Z} (hζT : ζ ∈ T) {ζP : Y} (hζP : ζP ∈ P)
    (hFz : F ⟨ζ, hζT⟩ = QuotientGroup.mk' (classicalInvolutionOddCore ↥P) ⟨ζP, hζP⟩)
    (hq : ∃ ι : QuaternionGroup 2 →* Y, (∀ q, ι q ∈ P) ∧ ι (QuaternionGroup.a 2) = ζP)
    (hmoved : ∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) → L ≤ T) :
    (∀ L₁ L₂ : Subgroup Z, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, ζ * y ≠ y * ζ) → (∃ y ∈ L₂, ζ * y ≠ y * ζ) → L₁ = L₂) ∧
    (∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) →
      Q3NM.AutOddFree ↥L ∨ (Q3NM.AutOddFreeInner ↥L ∧
        ∀ y ∈ T, ∃ l ∈ L, ∀ w ∈ L, y * w * y⁻¹ = l * w * l⁻¹)) := by
  rcases hrows with hG | hA
  · have hm : CFSG.Blueprint.LieModel (SecQuot P) .G2 0 3 1 := hG
    haveI : IsSimpleGroup (SecQuot P) := isSimpleGroup_of_lieModel_g2 (by norm_num) hm
    have hnab := exists_noncomm_of_center_eq_bot (center_eq_bot_of_lieModel_g2 hm)
    obtain ⟨U, I⟩ := g23_block F hFs hK hnab (hG2 (SecQuot P) hm) hmoved
    exact ⟨U, fun L hL hmv => Or.inr (I L hL hmv)⟩
  · obtain ⟨U, O⟩ := hyp51_of_rows_block hU hM12 hM12fin hM12nab hA F hFs hK hζT hζP hFz hq hmoved
    exact ⟨U, fun L hL hmv => Or.inl (O L hL hmv)⟩

theorem hyp51_of_thm3BarG (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12 : TwinCentRes.ModelFactM12)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hTR : TypeRHyp Φ)
    {M₀ : Subgroup X} (hM₀ : M₀ ∈ Φ)
    (hconcl : Thm3A.Thm3RConclG (oddQuotientFamily Φ)
      (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore X))))
    {ζ : X} (hζ : ζ ∈ M₀) (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1) :
    (∀ L₁ L₂ : Subgroup (X ⧸ classicalInvolutionOddCore X), CFSG.IsComponent L₁ →
        CFSG.IsComponent L₂ →
        (∃ y ∈ L₁, QuotientGroup.mk' (classicalInvolutionOddCore X) ζ * y ≠
          y * QuotientGroup.mk' (classicalInvolutionOddCore X) ζ) →
        (∃ y ∈ L₂, QuotientGroup.mk' (classicalInvolutionOddCore X) ζ * y ≠
          y * QuotientGroup.mk' (classicalInvolutionOddCore X) ζ) → L₁ = L₂) ∧
      (∀ L : Subgroup (X ⧸ classicalInvolutionOddCore X), CFSG.IsComponent L →
        (∃ y ∈ L, QuotientGroup.mk' (classicalInvolutionOddCore X) ζ * y ≠
          y * QuotientGroup.mk' (classicalInvolutionOddCore X) ζ) →
        Q3NM.AutOddFree ↥L ∨ (Q3NM.AutOddFreeInner ↥L ∧
          ∀ y ∈ omegaGen (aStar (oddQuotientFamily Φ)
              (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore X)))),
            ∃ l ∈ L, ∀ w ∈ L, y * w * y⁻¹ = l * w * l⁻¹)) := by
  set q := QuotientGroup.mk' (classicalInvolutionOddCore X) with hq
  have hΦb : ConjInvariant (oddQuotientFamily Φ) :=
    AscQuot.conjInvariant_quot hTR.hyp.conjInvariant (classicalInvolutionOddCore X)
  have hMb : M₀.map q ∈ oddQuotientFamily Φ := ⟨M₀, hM₀, rfl⟩
  have hsub : (omegaGen (aStar (oddQuotientFamily Φ) (M₀.map q))).IsSubnormal := by
    have := isSubnormal_map_omegaGen_aStarG hMb hconcl hΦb (MonoidHom.id _)
      Function.surjective_id
    rwa [Subgroup.map_id] at this
  have hMbT : M₀.map q ≤ omegaGen (aStar (oddQuotientFamily Φ) (M₀.map q)) :=
    le_omegaGen (self_mem_aStar _)
  have hζT : q ζ ∈ omegaGen (aStar (oddQuotientFamily Φ) (M₀.map q)) :=
    hMbT (Subgroup.mem_map_of_mem q hζ)
  have hζp : IsPGroup 2 (Subgroup.zpowers ζ) := isPGroup_zpowers_of_mul_self_eq_one hζ2 hζ1
  obtain ⟨R₀, -, hR₀, hζR₀⟩ := exists_mem_RSet_ge (Ω := Φ) hM₀ hζp (Subgroup.zpowers_le.mpr hζ)
  obtain ⟨ψ⟩ := hTR.sylow M₀ hM₀ R₀ hR₀
  obtain ⟨ι, hιR, hιa⟩ := exists_q8_hom_of_involution ψ (hζR₀ (Subgroup.mem_zpowers ζ)) hζ2 hζ1
  exact hyp51_of_rows_blockG hU hM12 hM12fin hM12nab hG2 hconcl.2
    (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(omegaGen (aStar (oddQuotientFamily Φ) (M₀.map q)))))
    (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact CFSG.ComponentClassification.OddCore.odd_card _)
    hζT hζT rfl
    ⟨q.comp ι, fun x => hMbT (Subgroup.mem_map_of_mem q (hR₀.1 (hιR x))), by simp [hιa]⟩
    fun L hL hm => component_le_of_moved hsub hζT hL hm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
