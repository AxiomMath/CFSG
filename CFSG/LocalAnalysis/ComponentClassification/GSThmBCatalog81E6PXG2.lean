module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXS
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXRee

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer P211
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {Q : ℕ → Prop}

theorem compOrd_G2_field
    {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup .G2 K)} (g : adjointGroup .G2 K)
    (hαg : ∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹)
    (hα : α ^ 2 = 1) (hQ : Q (Open.ordG2 (p ^ e))) : CompOrd Q (fixedSubgroup α) := by
  intro L hL
  obtain ⟨E⟩ := CatLeafProof.odd_field_component_equiv hp hp2 he hKe δ hδ (g := g) (a := 1)
    (fun h => by rw [hαg h]; simp only [rootDiagUnit_one, inv_one, mul_one]) hα
    (MulEquiv.refl _) hL
  have hadm : StatedLieAdmissible .G2 0 p e :=
    ⟨hp, he, rfl, CatLeafProof.three_le_pow_of_odd_prime hp hp2 he⟩
  have hLie := CatLeafProof.lieModel_centralQuotient_of_mulEquiv_adjointGroup (t := .G2)
    (Or.inl ⟨rfl, rfl⟩) hadm (CatLeafProof.card_fixSubfield_of_sq_pow hp he hKe δ hδ) E
  rw [GH74.card_of_lieModel_G2 hp2 hLie]
  exact hQ

theorem compOrd_G2_ree
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] (b : ℕ)
    (hK : Nat.card K = 3 ^ (2 * b + 1)) (g : adjointGroup ReeTag.G2.tag K)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1)
    (hQ : ∀ v, v ∣ Open.ordRee (3 ^ (2 * b + 1)) → Q v) :
    CompOrd Q (fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) := by
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ := LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b K hK
    g hα
  have hc : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
      ReeTag.G2.finiteReeAut K b :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
      ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K b) * ψ⁻¹).trans hψ
  have hcard : Nat.card (fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) =
      Open.ordRee (3 ^ (2 * b + 1)) := by
    rw [Nat.card_congr (CatLeafProof.fixedSubgroupCongrEquiv ψ _).toEquiv, hc,
      ← card_map_of_injective (adjointGroup ReeTag.G2.tag K).subtype_injective]
    exact ComponentClassification.LiteratureLocal.G2_card_reeGamma b hK
  exact CompOrd.of_card_dvd fun v hv => hQ v (hcard ▸ hv)

theorem compOrd_G2_outer
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {α : MulAut (adjointGroup ReeTag.G2.tag K)} (hα : orderOf α = 2)
    (hout : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range)
    (hQf : ∀ e, (p ^ e) ^ 2 = p ^ f → Q (Open.ordG2 (p ^ e)))
    (hQR : ∀ b, p = 3 → f = 2 * b + 1 → ∀ v, v ∣ Open.ordRee (3 ^ (2 * b + 1)) → Q v) :
    CompOrd Q (fixedSubgroup α) := by
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  have hhalf : Even f → 1 ≤ f / 2 ∧ (p ^ (f / 2)) ^ 2 = p ^ f := fun hev => by
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ := hev
      omega
    · rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev)]
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP K ReeTag.G2.prime :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three hf hK
    obtain ⟨-, hNF, -, hk, -, hEven, hOdd⟩ := G2_three_exact_automorphism_normal_form hf K hK
    obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF α
    rcases hk α g k k.2 hgk hα2 with hk0 | hkf
    · exact (hout (MonoidHom.mem_range.mpr ⟨g, by rw [hgk, hk0, pow_zero, mul_one]⟩)).elim
    · rcases Nat.even_or_odd f with hfe | ⟨b, hb⟩
      · obtain ⟨-, σ, -, -, hσ, -, hφσ⟩ := hEven hfe
        obtain ⟨he, he2⟩ := hhalf hfe
        have hαg : ∀ h : adjointGroup ReeTag.G2.tag K, (α h : ModGL ReeTag.G2.tag K) =
            (g : ModGL ReeTag.G2.tag K) *
              Units.map (entrywiseHom σ.toRingHom) (h : ModGL ReeTag.G2.tag K) *
                (g : ModGL ReeTag.G2.tag K)⁻¹ := fun h => by
          rw [hgk, hkf, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
            Subgroup.coe_inv, hφσ]
        exact compOrd_G2_field Nat.prime_three (by decide) he (by rw [hK, he2]) σ hσ g hαg hα2
          (hQf _ he2)
      · obtain ⟨-, hFb, -⟩ := hOdd b hb
        have hαR : α = MulAut.conj g * ReeTag.G2.finiteReeAut K b := by rw [hgk, hkf, hFb]
        subst hαR
        exact compOrd_G2_ree b (by rw [hK, hb]) g hα2 (hQR b rfl hb)
  · obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK .G2
        (Or.inr ⟨rfl, hp3⟩)
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
    have hΘα : Θ α = σ := hΘ α g σ hgσ
    rcases hinv α hα2 with hσ1 | ⟨hev, hσ, -⟩
    · have h1 : α ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
        rw [← hker]
        exact MonoidHom.mem_ker.mpr hσ1
      exact (hout h1).elim
    · obtain ⟨he, he2⟩ := hhalf hev
      exact compOrd_G2_field hp hp2 he (by rw [hK, he2]) σ (fun c => by rw [← hΘα, hσ]) g hgσ
        hα2 (hQf _ he2)

theorem p211For_G2 :
    P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel G .G2 0 p f := by
  intro X _ _ hsimp hC ⟨p', f', hp', hp2', hf', hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ
    hDsyl hbound b K hb hb1 hKC hK hKt
  exfalso
  have hmodel := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLie
  have hq'odd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp2').pow
  have hq'3 := CatLeafProof.three_le_pow_of_odd_prime hp' hp2' hf'
  have hn3 := three_le_v2 hq'odd hq'3
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  refine p211_of_outer (n := padicValNat 2 ((p' ^ f') ^ 2 - 1)) hC
    (LieType.Chevalley.exceptional_Chevalley_model_Schreier _ .G2 p' f' (by decide) hmodel).1
    (CatLeaf.fixedTwoComponentsQuasisimple_exceptional (by decide) hp' hp2' hmodel)
    (by rw [GH74.card_of_lieModel_G2 hp2' hLie]; exact v2_ordG2 hq'odd hq'3)
    (fun β hβ hin => ?_) hp hp2 hf hJt hDJ hDsyl hbound hb hb1 hKC hK hKt
  have hβ' : orderOf (MulAut.congr e β) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective β).trans hβ
  have hout : MulAut.congr e β ∉ (MulAut.conj : adjointGroup .G2 F →* MulAut _).range :=
    fun h => hin ((LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff e β).1 h)
  refine CompOrd.of_mulEquiv (CatLeafProof.fixedSubgroupCongrEquiv e β) ?_
  refine compOrd_G2_outer hp' hp2' hf' hFc hβ' hout (fun e' he' => ?_) (fun k _ _ v hv => ?_)
  · have he1 : 1 ≤ e' := by
      rcases Nat.eq_zero_or_pos e' with h0 | h0
      · rw [h0, pow_zero, one_pow] at he'
        omega
      · exact h0
    have hq0 : Odd (p' ^ e') := (hp'.odd_of_ne_two hp2').pow
    have hq03 := CatLeafProof.three_le_pow_of_odd_prime hp' hp2' he1
    show padicValNat 2 (Open.ordG2 (p' ^ e')) < 2 * padicValNat 2 ((p' ^ f') ^ 2 - 1)
    rw [v2_ordG2 hq0 hq03, ← he', v2_sq_sq_sub hq0 hq03]
    omega
  · show padicValNat 2 v < 2 * padicValNat 2 ((p' ^ f') ^ 2 - 1)
    have h4 : padicValNat 2 v < 4 := Nat.lt_of_not_le fun h4 =>
      not_sixteen_dvd_ordRee k ((pow_dvd_pow 2 h4).trans (pow_padicValNat_dvd.trans hv))
    omega

end P211X

end CFSG.ComponentClassification.GSThmB
