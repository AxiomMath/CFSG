module

public import CFSG.Adapters.LinearCatalog
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift
public import CFSG.LieType.Steinberg.CentralExt.SLMilnor

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix
open CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LieType.Steinberg.CentralExt.SLClosed

theorem exists_central_cover_specialLinear_of_centrallyClosed
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 1 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hsec : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      Nat.card F = Q.card →
      ∀ (E : Type) [Group E] [Finite E]
        (π : E →* SpecialLinearGroup (Fin (m + 1)) F),
        Function.Surjective π → π.ker ≤ Subgroup.center E →
          ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (π : SpecialLinearGroup (Fin (m + 1)) F →* L),
      Nat.card F = Q.card ∧ Function.Surjective π ∧
      π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Group.IsPerfect L := Group.isPerfect_def.2 hL.1
  let F := GaloisField Q.p Q.exponent
  have hcardF : Nat.card F = Q.card := by
    rw [GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  haveI : CharP F 2 := CharP.congr Q.p hQ
  let Cov := SpecialLinearGroup (Fin (m + 1)) F
  let X := (TauCeti.CFSGIndex.lie
    (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group
  let eP : Cov ⧸ Subgroup.center Cov ≃* X :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv).symm
  let ρC : Cov →* X := eP.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Cov))
  let ρK : L →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hC : Function.Surjective ρC :=
    eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hK : Function.Surjective ρK :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcK : ρK.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hmk : (QuotientGroup.mk' (Subgroup.center L)) x = 1 := by
      apply e.injective
      rw [map_one]
      simpa [ρK] using hx
    exact (QuotientGroup.eq_one_iff x).1 hmk
  have hcC : ρC.ker ≤ Subgroup.center Cov := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hmk : (QuotientGroup.mk' (Subgroup.center Cov)) x = 1 := by
      apply eP.injective
      rw [map_one]
      simpa [ρC] using hx
    exact (QuotientGroup.eq_one_iff x).1 hmk
  obtain ⟨π, hπ, hπsurj⟩ := exists_surjective_lift ρC ρK hC hK hcK
    (inferInstance : Group.IsPerfect L) (hsec F hcardF)
  refine ⟨F, inferInstance, inferInstance, (inferInstance : CharP F 2), π, hcardF, hπsurj, ?_⟩
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  apply hcC
  rw [MonoidHom.mem_ker]
  have h1 : ρK (π x) = 1 := by rw [hx, map_one]
  rwa [hπ x] at h1

theorem exists_central_cover_specialLinear_of_two_le
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 2 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : ¬ (m = 2 ∧ Q.card = 4)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (π : SpecialLinearGroup (Fin (m + 1)) F →* L),
      Nat.card F = Q.card ∧ Function.Surjective π ∧
      π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
  have h2le : 2 ≤ Q.card := by
    rw [TauCeti.PrimePower.card_def, hQ]
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num : 1 ≤ 2) Q.exponent_pos
  have hne3 : Q.card ≠ 3 := by
    rw [TauCeti.PrimePower.card_def, hQ]
    intro h
    have hdvd : 2 ∣ 2 ^ Q.exponent := dvd_pow_self 2 Q.exponent_pos.ne'
    rw [h] at hdvd
    norm_num at hdvd
  refine exists_central_cover_specialLinear_of_centrallyClosed hL m (by omega) Q hQ hv e ?_
  intro F _ _ _ hcard E _ _ π hπ hcen
  rcases (show Q.card = 2 ∨ Q.card = 4 ∨ 5 ≤ Q.card by omega) with h2 | h4 | h5
  ·
    have hm4 : 4 ≤ m := by
      by_contra h
      have hm23 : m = 2 ∨ m = 3 := by omega
      have h2' : Q.p ^ Q.exponent = 2 := by
        rw [← TauCeti.PrimePower.card_def]
        exact h2
      rcases hm23 with rfl | rfl
      · exact ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2 (by
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
          simp [h2'])
      · exact ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2 (by
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
          simp [h2'])
    exact sl_exists_section_of_four_le hm4 hπ hcen
  ·
    have hm3 : 3 ≤ m := by omega
    refine sl_exists_section_of_separating (by omega)
      (separating_of_card (m := m) (by omega)
        (by rw [hcard]; omega)
        (by rintro ⟨rfl, h⟩; rw [hcard] at h; omega)
        (by rintro ⟨rfl, h⟩; rw [hcard] at h; omega)) hπ hcen
  · exact sl_exists_section_of_separating (by omega)
      (separating_of_five_le (by rw [hcard]; exact h5))
      hπ hcen

end CFSG.ClassicalGroups.SpecialLinear

end
