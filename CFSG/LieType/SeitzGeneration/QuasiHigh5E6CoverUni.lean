module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311f2
import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Main

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

section E6Three

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.RankThree.E6 CFSG.HardMathSupport.Lang.AnisoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TauCeti


theorem e6ThreeUniNative_one (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (E₀ : Subgroup (adjointGroup .E6 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2)
    (hn : ¬ NormalizesRNative .E6 K E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨g, hg⟩ : ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (embE6F4 K).range :=
    conjOne_of_innerIsotropic (e6InnerIsotropic_of_frame
      (ExcWideThree.e6HeisFrameNormalizesR_of_fixedElt (ExcWideThree.e6HeisFrameFixedElt_of_classD
          ExcWideThree.e6HeisFrameFixedEltD_holds)))
      K hK E₀ hexp hcard hn
  set E₁ : Subgroup (adjointGroup .E6 K) := E₀.map (MulAut.conj g).toMonoidHom with hE₁def
  have hE₁le : E₁ ≤ (embE6F4 K).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hι := embE6F4_injective K
  set E₃ : Subgroup (adjointGroup .F4 K) := E₁.comap (embE6F4 K) with hE₃def
  have hE₃map : E₃.map (embE6F4 K) = E₁ := Subgroup.map_comap_eq_self hE₁le
  have hcardE₁ : Nat.card E₁ = 3 ^ 2 := by
    rw [hE₁def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map (embE6F4 K)) = Nat.card E₃ := Subgroup.card_map_of_injective hι
    rw [← h1, hE₃map, hcardE₁]
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    have hmem : (embE6F4 K) x ∈ E₀.map (MulAut.conj g).toMonoidHom := hx
    obtain ⟨y, hy, hyx⟩ := hmem
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hnF : ¬ NormalizesRNative .F4 K E₃ :=
    not_normalizesRIn_comap_of_map (embE6F4 K) hι g hn E₃ hE₃map
  refine uniClosure_eq_top_of_conj g ?_
  rw [← hE₁def, ← hE₃map]
  exact e6UniClose_one_of_card K hK E₃ hexp₃ hcardE₃ hnF

theorem uniSeitzPlanes_E6_inner_three_one :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ q.card % 3 = 1) ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, ⟨q, hq, hq1⟩, hn⟩
  obtain rfl : d = .E6 q := hq
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E6 q).symm)
  have hnd : ¬ 3 ∣ Nat.card K := by
    rw [hKq, PrimePower.card_def]
    intro hd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd))
  have hK : Nat.card K % 3 = 1 := by rw [hKq]; exact hq1
  have h := uniPlaneGen_of_native_uniClosure (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => e6ThreeUniNative_one K hK E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (LieTypeIndex.E6 q).characteristic R
    rw [LieTypeIndex.characteristic_E6, ← hring]
    exact hRp

end E6Three

section E6Field

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three


theorem uniSeitzPlanes_E6_field_one :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ q.card % 3 = 1) ∧ ¬ IsE6DiagPlane d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨-, rfl, ⟨q, rfl, hq1⟩, hdiag⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hchar : ringChar K = q.p := ringChar.eq K q.p
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout : ¬ E.map (MulAut.congr e).toMonoidHom ≤ e6Inndiag K := fun h =>
    hdiag ⟨q, rfl, K, inferInstance, inferInstance, hKchar, e, h⟩
  have hK1 : Nat.card K % 3 = 1 := by rw [hKq]; exact hq1
  have h8 : Nat.card K ≠ 8 := by
    intro h
    rw [h] at hK1
    norm_num at hK1
  have h := (uniPlaneGen_map_congr e _ E).1
    (uniPlaneGen_E6_field_of_ne_eight (K := K) h8 _ hc' hout)
  rw [hchar] at h
  simpa using h

end E6Field

section TwE6Field

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.RankThree.Chevalley


theorem uniSeitzPlanes_twE6_field_ne_eight :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧
      (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card ≠ 8) ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
        ∃ e : CFSG.LieType.SeitzGeneration.Cat d ≃* twistedE6RootGroup K σ,
          E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨-, rfl, ⟨q, rfl, hq8⟩, hdiag⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hpq : 3 ≠ q.p := by simpa using hpd
  have h8 : q.p ^ q.exponent ≠ 8 := by
    intro h
    exact hq8 (by rw [TauCeti.PrimePower.card_def]; exact h)
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout : ¬ E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := fun h =>
    hdiag ⟨q, rfl, K, inferInstance, inferInstance, σ, hK, hσ, e, h⟩
  have h := (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_twE6_field_of_ne_eight q.prime_p q.exponent_pos
    h8 (fun h => hpq h.symm) hK σ hσ _ hc' hout)
  simpa using h

end TwE6Field

end CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
