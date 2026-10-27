module

public import CFSG.ClassicalInvolution.Q3.TL3TopRestrict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3

section Trans

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem oddCore_le_comap {A B : Subgroup Γ} (hAB : A ≤ B) (hAs : IsSubnormal A B) :
    classicalInvolutionOddCore ↥A ≤
      (classicalInvolutionOddCore ↥B).comap (Subgroup.inclusion hAB) := by
  intro h hh
  have h1 : (h : Γ) ∈ oddCoreIn A := ⟨h, hh, rfl⟩
  obtain ⟨b, hb, hbh⟩ := oddCoreIn_le_of_isSubnormal hAs h1
  have : b = Subgroup.inclusion hAB h := Subtype.ext hbh
  rw [Subgroup.mem_comap]
  exact this ▸ hb

@[expose] noncomputable def secEmb {A B : Subgroup Γ} (hAB : A ≤ B) (hAs : IsSubnormal A B) :
    (↥A ⧸ classicalInvolutionOddCore ↥A) →* (↥B ⧸ classicalInvolutionOddCore ↥B) :=
  QuotientGroup.map _ _ (Subgroup.inclusion hAB) (oddCore_le_comap hAB hAs)

theorem secEmb_injective {A B : Subgroup Γ} (hAB : A ≤ B) (hAs : IsSubnormal A B) :
    Function.Injective (secEmb hAB hAs) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set O := classicalInvolutionOddCore ↥A with hO
  set T : Subgroup ↥A := (classicalInvolutionOddCore ↥B).comap (Subgroup.inclusion hAB) with hT
  have hker : (secEmb hAB hAs).ker ≤ T.map (QuotientGroup.mk' O) := by
    intro y hy
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O y
    refine ⟨h, ?_, rfl⟩
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥B) (Subgroup.inclusion hAB h) = 1 := hy
    exact (QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥B) _).mp h1
  have hTodd : Odd (Nat.card T) := by
    have h1 : Nat.card T = Nat.card (T.map (Subgroup.inclusion hAB)) :=
      (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hAB)).symm
    have h2 : T.map (Subgroup.inclusion hAB) ≤ classicalInvolutionOddCore ↥B := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    rw [h1]
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥B).of_dvd_nat
      (Subgroup.card_dvd_of_le h2)
  have hKodd : Odd (Nat.card (secEmb hAB hAs).ker) :=
    hTodd.of_dvd_nat ((Subgroup.card_dvd_of_le hker).trans
      (Subgroup.card_map_dvd T (QuotientGroup.mk' O)))
  have hle : (secEmb hAB hAs).ker ≤ classicalInvolutionOddCore (↥A ⧸ O) := by
    show _ ≤ sSup _
    exact le_sSup ⟨inferInstance, hKodd⟩
  have hbot : classicalInvolutionOddCore (↥A ⧸ O) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥A
  have := hle (MonoidHom.mem_ker.mpr hx)
  rwa [hbot, Subgroup.mem_bot] at this

theorem transfer_classicalMember {A B : Subgroup Γ} (hAB : A ≤ B) (hAs : IsSubnormal A B)
    {u : ↥A ⧸ classicalInvolutionOddCore ↥A} {L : Subgroup (↥A ⧸ classicalInvolutionOddCore ↥A)}
    (hL : IsClassicalMember3 L u) :
    IsClassicalMember3 (L.map (secEmb hAB hAs)) (secEmb hAB hAs u) := by
  set φ := secEmb hAB hAs with hφ
  have hinj : Function.Injective φ := secEmb_injective hAB hAs
  set e : (↥A ⧸ classicalInvolutionOddCore ↥A) ≃* φ.range := MonoidHom.ofInjective hinj with he
  have hrange : φ.range = ((A.subgroupOf B).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥B))) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥A) y
      exact ⟨Subgroup.inclusion hAB h, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥A) ⟨b, Subgroup.mem_subgroupOf.mp hb⟩, rfl⟩
  have hsub : IsSubnormal φ.range ⊤ := by
    rw [hrange]
    have h1 := isSubnormal_subgroupOf hAs B
    rw [Subgroup.subgroupOf_self] at h1
    have h2 := CFSG.ComponentClassification.Components.chain_map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥B)) h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  have h3 := IsClassicalMember3.map_mulEquiv e hL
  have h4 := isClassicalMember3_map_subnormal hsub h3
  have hcomp : φ.range.subtype.comp e.toMonoidHom = φ := by
    ext x
    rfl
  have h5 : (L.map e.toMonoidHom).map φ.range.subtype = L.map φ := by
    rw [Subgroup.map_map, hcomp]
  rw [h5] at h4
  exact h4

end Trans

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
