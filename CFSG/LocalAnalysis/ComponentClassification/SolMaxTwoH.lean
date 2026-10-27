module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe9
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoD

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}
  (S : Sig36 X t J 9 e E D)
include S

theorem centralizer_le_of_two_of_oddCore
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {f : X}
    (hfH : f ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hf2 : f * f = 1)
    (hft : f * t = t * f) (hf2pt : (ρ ⟨f, hHN hfH⟩).support.card = 2)
    (hOf : (pPrimeCore 2 ↥(centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype ≤
      normalizer (Sol78.signalizerCompletion E E : Set X)) :
    centralizer ({f} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have hf1 : f ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨1, hHN hfH⟩ = 1 := by
      rw [show (⟨1, hHN hfH⟩ : ↥(normalizer (M : Set X))) = 1 from rfl, map_one]
    rw [h1, Perm.support_one, Finset.card_empty] at hf2pt
    omega
  have hfo : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hf2) hf1
  have htf : t ∈ centralizer ({f} : Set X) := mem_centralizer_singleton_iff.mpr hft.symm
  have hfJ : f ∈ normalizer (J : Set X) :=
    S.centralizer_le_normalizer hT13 hML hSch (mem_centralizer_singleton_iff.mpr hft)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  have hf2J : (ρJ ⟨f, hfJ⟩).support.card = 2 := by
    rw [← card_support_rho_eq_rhoJ (by norm_num) hJM hsup hρ hρJ hfJ (hHN hfH)]
    exact hf2pt
  obtain ⟨L₀, F, χ, DY, hL₀J, hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hDY4, hFY⟩ :=
    S.exists_fixed_layer_seven_of_two hρJ hfJ hf2 hf2J
  have hFH : normalizer (F : Set X) ≤ H := by
    obtain ⟨DF, hDF, hFs⟩ := hFD
    have hFW := S.completion_eq_of_four h33 h35 hFJ (klein_of_card_sq hF4 hFsq) hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  obtain ⟨N, hNC, hNpc, hL₀N, hbr⟩ := exists_pump_data_seven hPump hN1 S.nonab S.kProper
    S.unbal S.notU (by norm_num) S.pair.2.2.2.1 hfo S.pair.1.1 htf hL₀C hL₀pc χ
  rcases hbr with ⟨r, hrodd, hr7, -, ⟨θN⟩, hfix, hpc⟩ | ⟨hfix, hpc, ⟨ψ⟩⟩ | ⟨hne, ⟨ψ⟩⟩
  ·
    have hr8 : r ≠ 8 := by
      rintro rfl
      exact (by decide : ¬ Odd 8) hrodd
    obtain ⟨ρN, τ', DN, P⟩ := S.exists_pumpG_of_data ht2 htf le_rfl hL₀C hL₀pc χ
      hFL₀ hFJ hF4 hFsq hFD hDY4 hFY hNC hNpc hL₀N hr7 (by omega) θN (Or.inr ⟨hfix, hpc⟩)
    exact S.centralizer_le_of_pumpG_two h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup hρ
      hfH hf2 hf2pt hOf P hfix hr8
  ·
    exact (He9.false_of_held_pump_outer hρ hHN ht2 hCt hOf hL₀C χ hNC hNpc hL₀N hfix hpc ψ hFL₀
      (hFJ.trans hJM) hF4 hFsq hFH hDY4 hFY).elim
  ·
    exfalso
    have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
    have hNH : N ≤ H := le_of_diagonal ht2 htf (inf_le_left.trans hCt) hOf hL₀C
      hL₀pc χ hFL₀ hF2 hFH hDY4 hFY hNC hNpc hL₀N hne ψ
    have hNtH : N.map (MulAut.conj t).toMonoidHom ≤ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem htH (hNH hz)) (inv_mem htH)
    obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj hNC hNpc htf
    let ψt : ↥(N.map (MulAut.conj t).toMonoidHom) ⧸
        Open.fusionZStar ↥(N.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin 7) :=
      (Sol78.fusionZStarQuotCongr (N.equivMapOfInjective (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective)).symm.trans ψ
    have htN : t ∈ normalizer (M : Set X) := hHN htH
    have hFK := not_le_coreActionKernel_of_card_four hJM (by norm_num) hρ hFJ hF4
    have hNK : ¬ N ≤ UnbalancedLayer.coreActionKernel M := by
      intro hNK
      have hNtK : N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
        rintro _ ⟨z, hz, rfl⟩
        exact hρ.conj_mem_coreActionKernel (by norm_num) htN (hNK hz)
      exact hFK (hFL₀.trans (hL₀N.trans (sup_le hNK hNtK)))
    have hNtK : ¬ N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
      intro hNtK
      apply hNK
      intro z hz
      have h1 : t * z * t⁻¹ ∈ N.map (MulAut.conj t).toMonoidHom := ⟨z, hz, rfl⟩
      have h2 := hρ.conj_mem_coreActionKernel (by norm_num) (inv_mem htN) (hNtK h1)
      have h3 : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
      rwa [h3] at h2
    exact false_of_two_components_of_kerZ_two hρ hHN hfH hf2 hf2pt hOf hNC hNpc hNtC hNtpc
      (Ne.symm hne) hNH hNtH hNK hNtK ψ ψt

end Sig36

end CFSG.ComponentClassification.SolMax
