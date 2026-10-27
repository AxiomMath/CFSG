module

public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCover
public import CFSG.LieType.Steinberg.CentralExt.PrimeCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
public import CFSG.Quasithin.Background.FFC11A
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot

public section

open Matrix

namespace CFSG.LieType.Steinberg.CentralExt.SL2Closed

theorem sl2_exists_section_of_central_of_card_eq_two_pow
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 3 ≤ f) (hcard : Nat.card F = 2 ^ f)
    {E : Type} [Group E] [Finite E]
    {π : E →* SpecialLinearGroup (Fin 2) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin 2) F →* E, ∀ g, π (σ g) = g := by
  let H := SpecialLinearGroup (Fin 2) F
  haveI : Fintype F := Fintype.ofFinite F
  have h4card : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by simpa using h4card)
  have hHsimple : IsSimpleGroup H :=
    CFSG.ComponentClassification.GMS78.u3_isSimpleGroup_SL2 F ⟨s, hs⟩
  have hHnonab : ∃ a b : H, a * b ≠ b * a := by
    refine ⟨⟨!![1,1;0,1], by simp [Matrix.det_fin_two]⟩,
      ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩, ?_⟩
    intro h
    have h' := congrArg (fun z : H => (z : Matrix (Fin 2) (Fin 2) F) 0 0) h
    change (!![1,1;0,1] * !![0,1;1,0] : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (!![0,1;1,0] * !![1,1;0,1] : Matrix (Fin 2) (Fin 2) F) 0 0 at h'
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h'
  have hHq : CFSG.IsQuasisimple H := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hHnonab).1
  haveI : Group.IsPerfect H := hHq.1
  refine CFSG.LieType.Steinberg.CentralExt.PrimeCover.exists_section_of_forall_prime ?_ E π hπ hcen
  intro ℓ hℓ P _ _ hPperf η hη hker hkp
  by_cases h2 : ℓ = 2
  · subst h2
    exact CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot
      f hf hcard η hη hker hkp
  · have hℓodd : Odd ℓ := hℓ.odd_of_ne_two h2
    have hodd : ∀ x ∈ η.ker, Odd (orderOf x) := by
      intro x hx
      obtain ⟨n, hn⟩ := hkp ⟨x, hx⟩
      have hxpow : x ^ ℓ ^ n = 1 := congrArg Subtype.val hn
      exact Odd.of_dvd_nat hℓodd.pow ((orderOf_dvd_iff_pow_eq_one).2 hxpow)
    have hPq : CFSG.IsQuasisimple P :=
      (CFSG.LocalCores.isQuasisimple_iff_of_surjective hPperf η hη hker).mpr hHq
    have hPopen : CFSG.Open.IsQuasisimple P := ⟨Group.isPerfect_def.1 hPq.1, hPq.2.1⟩
    have hH : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (H ≃* ↥(CFSG.Open.StatedSL 2 K)) :=
      ⟨f, F, inferInstance, inferInstance, hcard,
        ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F⟩⟩
    have hinj := CFSG.Quasithin.B69.noOddCoverSL2 P H hPopen η hη hodd hH
    exact (MonoidHom.ker_eq_bot_iff η).2 hinj

end CFSG.LieType.Steinberg.CentralExt.SL2Closed

namespace CFSG.ClassicalGroups.SpecialLinear

private theorem sl2_section_of_A_one_valid
    (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A 1 Q).Valid)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hcard : Nat.card F = Q.card)
    {E : Type} [Group E] [Finite E]
    {π : E →* SpecialLinearGroup (Fin 2) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin 2) F →* E, ∀ g, π (σ g) = g := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have h4 : 4 ≤ Q.card := by
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hv'.1
  have hne4 : Q.card ≠ 4 := by
    intro h
    exact hv'.2 (by
      rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact Or.inl ⟨rfl, Or.inl h⟩)
  have hcardQ : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hexp3 : 3 ≤ Q.exponent := by
    have h2 : 2 ≤ Q.exponent := by
      by_contra h
      have h1 : Q.exponent ≤ 1 := by omega
      have hle : Q.card ≤ 2 := by
        rw [hcardQ]
        calc 2 ^ Q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
          _ = 2 := by norm_num
      omega
    rcases (show Q.exponent = 2 ∨ 3 ≤ Q.exponent by omega) with h | h
    · exact absurd (by rw [hcardQ, h]; norm_num) hne4
    · exact h
  exact CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central_of_card_eq_two_pow
    hexp3 (hcard.trans hcardQ) hπ hcen

theorem exists_central_cover_specialLinear_of_ne_two_four
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 1 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : ¬ (m = 2 ∧ Q.card = 4)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (π : Matrix.SpecialLinearGroup (Fin (m+1)) F →* L),
      Nat.card F = Q.card ∧ Function.Surjective π ∧
      π.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m+1)) F) := by
  by_cases hm2 : 2 ≤ m
  · exact exists_central_cover_specialLinear_of_two_le hL m hm2 Q hQ hv e hne
  · have hm1 : m = 1 := by omega
    subst hm1
    refine exists_central_cover_specialLinear_of_centrallyClosed hL 1 (by norm_num) Q hQ hv e ?_
    intro F _ _ _ hcard E _ _ π hπ hcen
    exact sl2_section_of_A_one_valid Q hQ hv hcard hπ hcen

end CFSG.ClassicalGroups.SpecialLinear

end
