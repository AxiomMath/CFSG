module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11I
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCI

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem false_of_conj_four_eleven
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) {Q : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
      normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {a g : X} (ha : a ∈ Q) (hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hs2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1)
    (hs4 : (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 4) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have haH : a ∈ H := (hQK ha).1
  have haK : a ∈ UnbalancedLayer.coreActionKernel M := (hQK ha).2
  have ha2 : IsPGroup 2 (zpowers a) := hQ2.to_le (zpowers_le.mpr ha)
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h1 : (⟨g⁻¹ * 1 * g, hHN hs⟩ : ↥(normalizer (M : Set X))) = 1 :=
      Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
    rw [h1, map_one, Perm.support_one, Finset.card_empty] at hs4
    omega
  have hCa : centralizer ({a} : Set X) ≤ H := by
    have hNa := hNT _ (zpowers_le.mpr ha) (fun h => ha1 (zpowers_eq_bot.mp h))
    intro z hz
    apply hNa
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq']
    exact hz
  obtain ⟨La, hLaM, hLaC, -, hLaperf, ⟨θLa, hθLa⟩, -⟩ :=
    exists_layer_of_kernel hMH hMpc θ haH haK ha2 hCa
  obtain ⟨S₀, hS₀H, hS₀C, -, hS₀card⟩ := S.card_two_eq_of_sup h33 h35 hT13 hML hSch hMH hMpc
    hHN θ hsup
  obtain ⟨h, hhH, hhS⟩ := exists_conj_mem_of_card_eq_of_le hS₀H hS₀card hs hs2
  set c := h * (g⁻¹ * a * g) * h⁻¹ with hcdef
  set g₀ := g * h⁻¹ with hg₀def
  have hcg : c = g₀⁻¹ * a * g₀ := by rw [hcdef, hg₀def]; group
  have hcH : c ∈ H := mul_mem (mul_mem hhH hs) (inv_mem hhH)
  have hc2 : c * c = 1 := by
    calc c * c = h * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * h⁻¹ := by rw [hcdef]; group
      _ = 1 := by rw [hs2]; group
  have hct : c ∈ centralizer ({t} : Set X) := hS₀C hhS
  have hc4 : (ρ ⟨c, hHN hcH⟩).support.card = 4 := by
    have h1 : (⟨c, hHN hcH⟩ : ↥(normalizer (M : Set X))) =
        ⟨h, hHN hhH⟩ * ⟨g⁻¹ * a * g, hHN hs⟩ * (⟨h, hHN hhH⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, Perm.card_support_conj, hs4]
  have hcJ : c ∈ normalizer (J : Set X) := S.centralizer_le_normalizer hT13 hML hSch hct
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  have hcJ4 : (ρJ ⟨c, hcJ⟩).support.card = 4 := by
    rw [← card_support_rho_eq_rhoJ (by norm_num) hJM hsup hρ hρJ hcJ (hHN hcH)]
    exact hc4
  obtain ⟨L₀, F, -, -, -, hL₀C, -, hFL₀, hFJ, hF4, hFsq, ⟨DF, hDF, hFs⟩, -, -⟩ :=
    S.exists_fixed_layer_seven_of_four hρJ hcJ hc2 hcJ4
  have hFc : F ≤ centralizer ({c} : Set X) := hFL₀.trans (hL₀C.trans inf_le_right)
  have hFel : CFSG.Open.IsElemAbelian 2 F := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun u hu => by rw [sq]; exact hFsq u hu⟩
    have hu := hFsq _ u.2
    have hv := hFsq _ v.2
    have huv : (u : X) * v * ((u : X) * v) = 1 := hFsq _ (mul_mem u.2 v.2)
    change (u : X) * v = v * u
    calc (u : X) * v = ((u : X) * v)⁻¹ := (inv_eq_of_mul_eq_one_right huv).symm
      _ = (v : X)⁻¹ * (u : X)⁻¹ := mul_inv_rev _ _
      _ = v * u := by rw [inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hu]
  set Oc := (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype
    with hOcdef
  have hOcodd : Nat.Coprime 2 (Nat.card Oc) := by
    rw [hOcdef, card_map_of_injective (centralizer ({c} : Set X)).subtype_injective]
    exact pPrimeCore_coprime_card
  have hFOc : F ≤ normalizer (Oc : Set X) := fun f hf =>
    le_normalizer_pPrimeCore (le_normalizer (hFc hf))
  have hOC : Oc ≤ H := by
    have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
      Nat.prime_two F Oc hFel (by rw [hF4]; norm_num) hFOc hOcodd
    rw [← hgen]
    refine iSup₂_le fun T hT => ?_
    obtain ⟨hTF, hTcard⟩ := hT
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
    obtain ⟨⟨v, hvT⟩, hv1⟩ := exists_ne (1 : T)
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hvF := hTF hvT
    have hv2 : v * v = 1 := hFsq v hvF
    have hv4 : (ρ ⟨v, le_normalizer (hJM (hFJ hvF))⟩).support.card = 4 := by
      have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ (hFJ hvF)
      rw [card_support_coreImage_of_four e (hFJ hvF) hv2 hv1' hDF
        (fun ω hω => hFs ⟨v, hFJ hvF⟩ hvF ω hω)] at h1
      exact h1
    exact inf_le_right.trans ((centralizer_le (Set.singleton_subset_iff.mpr hvT)).trans
      (hA v (hJM (hFJ hvF)) hv2 hv4))
  have hCc : centralizer ({c} : Set X) ≤ H := S.centralizer_le_of_four_of_oddCore h33 h35 hT13
    hML hSch hPump hN1 hMH hMpc hJM hHN hsup hρ hcH hc2 hct hc4 hOC
  set Lc := La.map (MulAut.conj g₀⁻¹).toMonoidHom with hLcdef
  have hCmap : (centralizer ({a} : Set X)).map (MulAut.conj g₀⁻¹).toMonoidHom =
      centralizer ({c} : Set X) := by
    rw [map_conj_centralizer_singleton, inv_inv, hcg]
  have hLcC : Lc ≤ centralizer ({c} : Set X) := by
    rw [← hCmap]
    exact map_mono hLaC
  have hLcperf : ⁅Lc, Lc⁆ = Lc := by rw [hLcdef, ← map_commutator, hLaperf]
  let θLc : ↥Lc ⧸ pPrimeCore 2 ↥Lc ≃* alternatingGroup (Fin 11) :=
    (Sol78.coreQuotCongr (La.equivMapOfInjective (MulAut.conj g₀⁻¹).toMonoidHom
      (MulAut.conj g₀⁻¹).injective)).symm.trans θLa
  have hLcH : Lc ≤ H := hLcC.trans hCc
  have hc1 : ρ ⟨c, hHN hcH⟩ ≠ 1 := by
    intro h1
    rw [h1, Perm.support_one, Finset.card_empty] at hc4
    omega
  have hLcK := le_coreActionKernel_of_le_centralizer_of_ne_one hρ (by norm_num) (hHN hcH) hc1
    (hLcH.trans hHN) hLcC θLc hLcperf
  obtain ⟨ρa, hρa⟩ := exists_isPermAction (M := La) (by norm_num) (by norm_num) θLa
  obtain ⟨δ, hδA, hδ2, hδ4, -, -⟩ := exists_four_of_fix (1 : Perm (Fin 11))
    (by rw [Perm.support_one, Finset.card_empty]; norm_num)
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hδ4
    omega
  obtain ⟨f, hfLa, -, hf2, hρaf⟩ := hρa.exists_involution_lift (by norm_num) (one_mem _)
    (one_mul 1) hδA hδ2 hδ1 (by rw [show (⟨1, one_mem _⟩ : ↥(normalizer (La : Set X))) = 1 from
      rfl, map_one, mul_one, one_mul])
  have hfM : f ∈ M := hLaM hfLa
  have hρf : ρ ⟨f, le_normalizer hfM⟩ = δ := by
    rw [hρ.apply_of_mem (by norm_num) ⟨f, hfM⟩, ← hθLa f hfLa hfM, ← hρaf]
    exact (hρa.apply_of_mem (by norm_num) ⟨f, hfLa⟩).symm
  have hf4 : (ρ ⟨f, le_normalizer hfM⟩).support.card = 4 := by rw [hρf]; exact hδ4
  have hTg : (zpowers f).map (MulAut.conj g₀⁻¹).toMonoidHom ≤ Lc :=
    map_mono (zpowers_le.mpr hfLa)
  exact S.false_of_conj_le_coreActionKernel_of_sup_zpowers h33 h35 hT13 hML hSch hMH hMpc hHN
    hsup hρ hfM (le_normalizer hfM) hf2 hf4 (hA f hfM hf2 hf4) (hTg.trans hLcH) (hTg.trans hLcK)

end Sig36

end CFSG.ComponentClassification.SolMax
