module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InnerIsoTw
public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjOneProof

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


@[expose] def ScBaseChange : Prop :=
  ∀ {k k₁ : Type} [Field k] [Finite k] [Field k₁] [Finite k₁] (ι : k →+* k₁),
    ∃ φ : ↥(e6Data_valid.minGroup k) →* ↥(e6Data_valid.minGroup k₁),
      Function.Injective φ ∧ ∀ g : ↥(e6Data_valid.minGroup k),
        ((e6Isogeny k₁ (φ g) : ↥(adjointGroup Tag.E6 k₁)) : ModGL Tag.E6 k₁) =
          baseChangeGL ι ((e6Isogeny k g : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k)

theorem e6InnerIsotropic_of_frame_of_scBase (hsc : ScBaseChange) (h : E6HeisFrameNormalizesR) :
    E6InnerIsotropic := by
  intro K _ _ hq E₀ hexp hcard hnorm x hx y hy
  classical
  by_contra hxy
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK4 : 4 ≤ Nat.card K := by omega
  have h3 : ¬ 3 ∣ Nat.card K := by omega
  have hK3 : ringChar K ≠ 3 := by
    intro h3'
    apply h3
    obtain ⟨e, he, hcardK⟩ := card_eq_pow_ringChar K
    rw [hcardK, h3']
    exact dvd_pow_self 3 (by omega)
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  haveI := hK₁
  have hinjc : Function.Injective (MulAut.conj : ↥(adjointGroup Tag.E6 K) →*
      MulAut ↥(adjointGroup Tag.E6 K)) :=
    mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  set E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K)) :=
    E₀.map (MulAut.conj : ↥(adjointGroup Tag.E6 K) →* MulAut ↥(adjointGroup Tag.E6 K)) with hE
  have hcardE : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective hinjc]
    exact hcard
  have hd : E ≤ e6Inndiag K := by
    rintro _ ⟨x, -, rfl⟩
    exact innerAut_le_e6Inndiag K ⟨x, rfl⟩
  have hEab : CFSG.IsElementaryAbelian 3 E := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcomm : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardE
    have hexpE : Monoid.exponent E ∣ 3 := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow, hexp x hx, map_one]
    exact { toIsMulCommutative := hcomm, exponent_dvd_p := hexpE }
  have hcE : ∀ g : adjointGroup Tag.E6 K,
      e6InndiagConj K ⟨(g : ModGL Tag.E6 K), adjointGroup_le_e6InndiagGL K g.2⟩ =
        MulAut.conj g := fun g => MulEquiv.ext fun z => Subtype.ext rfl
  have hniso : ¬ E6DiagIsotropic K K₁ E := by
    intro hiso
    obtain ⟨φ, hφinj, hφ⟩ := hsc (algebraMap K K₁)
    apply hxy
    apply hφinj
    rw [map_mul, map_mul]
    have hmem : ∀ z : ↥(e6Data_valid.minGroup K), z ∈ E₀.comap (e6Isogeny K) →
        ((e6Isogeny K₁ (φ z) : ↥(adjointGroup Tag.E6 K₁)) : ModGL Tag.E6 K₁) ∈
          ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
            (baseChangeGL (algebraMap K K₁)) := by
      intro z hz
      rw [hφ z]
      refine Subgroup.mem_map_of_mem _ ⟨⟨((e6Isogeny K z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K),
        adjointGroup_le_e6InndiagGL K (e6Isogeny K z).2⟩, ?_, rfl⟩
      show e6InndiagConj K ⟨((e6Isogeny K z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K), _⟩ ∈ E
      rw [hcE (e6Isogeny K z)]
      exact Subgroup.mem_map_of_mem _ hz
    exact hiso _ _ (hmem x hx) (hmem y hy)
  obtain ⟨F⟩ := exists_e6HeisenbergFrame hK3 hK4 K₁ hroot E hEab hcardE hd hniso
  obtain ⟨R, hR1, hRp, hRfix⟩ := h K hK3 hK4 E hEab hcardE hd F
  exact hnorm ⟨R, hR1, hRp, fun x hx =>
    mem_normalizer_of_map_conj_eq R x (hRfix _ ⟨x, hx, rfl⟩)⟩

end CFSG.LieType.SeitzGeneration.ExcHighThree
