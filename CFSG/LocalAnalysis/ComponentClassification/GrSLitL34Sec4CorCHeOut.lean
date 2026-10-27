module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCHeQuot

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X] [Finite X]

theorem held_conj_range_index
    {S : Type} [Group S] (θ₀ : S ≃* Blueprint.NativeSporadic.He) :
    (MulAut.conj : S →* MulAut S).range.index = 2 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := ctbh_full_automorphism_permutation_model
  set θ : S ≃* heP := θ₀.trans heEquivP with hθ
  have h1 : (MulAut.conj : S →* MulAut S).range =
      (MulAut.conj : heP →* MulAut heP).range.comap (MulAut.congr θ).toMonoidHom := by
    ext σ
    rw [mem_comap, MulEquiv.coe_toMonoidHom, congr_mem_range_conj_iff]
  rw [h1, index_comap_of_surjective _ (MulAut.congr θ).surjective, index_eq_card]
  exact hcard

theorem held_mul_mem_conj_range
    {S : Type} [Group S] (θ₀ : S ≃* Blueprint.NativeSporadic.He) {σ τ : MulAut S}
    (hσ : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hτ : τ ∉ (MulAut.conj : S →* MulAut S).range) :
    σ * τ ∈ (MulAut.conj : S →* MulAut S).range :=
  (mul_mem_iff_of_index_two (held_conj_range_index θ₀)).mpr (iff_of_false hσ hτ)

theorem held_inner_fixed
    (h2A : GrSLit.HeldTwoAFixedInput) (h2B : ∀ L : Subgroup ↥(centralizerIn heP heT1P), ¬
        IsPComponent 2 L)
    {S : Type} [Group S] [Finite S] (θ₀ : S ≃* Blueprint.NativeSporadic.He) (σ : MulAut S)
    (hσ : ∀ y, σ (σ y) = y) (hinn : σ ∈ (MulAut.conj : S →* MulAut S).range) (P : Subgroup S)
    (hPF : P ≤ fixedSubgroup σ) (hP : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)))
    (hPne : P ≠ ⊤) : GrSLit.IsL34Type (P ⧸ Open.fusionZStar P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2A' : ∀ L : Subgroup ↥(centralizerIn heP (heGenPerm 0)), IsPComponent 2 L →
      GrSLit.IsL34Type (L ⧸ Open.fusionZStar L) := h2A
  have h2B' : ∀ L : Subgroup ↥(centralizerIn heP heT1P), ¬ IsPComponent 2 L := h2B
  have θ : S ≃* heP := θ₀.trans heEquivP
  by_cases hσ1 : σ = 1
  · exfalso
    have hFtop : fixedSubgroup σ = ⊤ := by
      rw [hσ1, eq_top_iff]
      intro x _
      rfl
    have : IsSimpleGroup S := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He θ₀
    have : IsSimpleGroup (fixedSubgroup σ) :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    have h := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hP
    apply hPne
    rw [eq_top_iff]
    intro x _
    have hx : (⟨x, hFtop ▸ mem_top x⟩ : fixedSubgroup σ) ∈ P.subgroupOf (fixedSubgroup σ) :=
      h ▸ mem_top _
    exact hx
  have hσ2' : σ * σ = 1 := MulEquiv.ext fun t => hσ t
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2') hσ1
  have hβ : orderOf (MulAut.congr θ σ) = 2 := by rw [orderOf_congr, hσ2]
  obtain ⟨eP⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hPF).symm
  have key : ∀ (F' : Type) [Group F'] [Finite F'] (φ : fixedSubgroup σ ≃* F'),
      (∀ L' : Subgroup F', IsPComponent 2 L' → GrSLit.IsL34Type (L' ⧸ Open.fusionZStar L')) →
      GrSLit.IsL34Type (P ⧸ Open.fusionZStar P) := by
    intro F' _ _ φ hF'
    obtain ⟨hL', ⟨eL⟩⟩ := GrSLit.isPComponent_map_and_fusionZStar_equiv φ hP
    exact LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans eL).symm (hF' _ hL')
  obtain ⟨t, ht⟩ := (congr_mem_range_conj_iff θ σ).mpr hinn
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ (conj_injective_of_center heP_center_eq_bot) t, ht, hβ]
  let f : fixedSubgroup σ ≃* centralizerIn heP (t : Equiv.Perm (Fin 8330)) :=
    ((fixedSubgroupCongr θ σ).trans
      (MulEquiv.subgroupCongr (by rw [← ht, fixedSubgroup_conj]))).trans
      (heCentralizerEquiv t)
  rcases involution_conj_cases t.2 (by rw [Subgroup.orderOf_coe]; exact ht2) with
    ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
  · exact key _ (f.trans ((MulEquiv.subgroupCongr (by rw [← hct]; rfl)).trans
      (infCentralizerConjEquiv hc (heGenPerm 0)))) fun L' hL' => h2A' L' hL'
  · exact key _ (f.trans ((MulEquiv.subgroupCongr (by rw [← hct]; rfl)).trans
      (infCentralizerConjEquiv hc heT1P))) fun L' hL' => (h2B' L' hL').elim

theorem nonempty_fusionZStar_equiv_alternating
    {T : Type*} [Group T]
    (h7 : Nonempty (T ⧸ pPrimeCore 2 T ≃* alternatingGroup (Fin 7))) :
    Nonempty (T ⧸ Open.fusionZStar T ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e7⟩ := h7
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_of_alternating ⟨e7⟩)).trans e7⟩

theorem not_mem_conj_range_of_fixed_alternating
    (h2A : GrSLit.HeldTwoAFixedInput) (h2B : ∀ L : Subgroup ↥(centralizerIn heP heT1P), ¬
        IsPComponent 2 L) {M T : Subgroup X}
    (hHe : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* Blueprint.NativeSporadic.He)) {w : X}
    (hw : w ∈ normalizer (M : Set X)) (hww : w * w = 1)
    (hTM : T ≤ M ⊓ centralizer ({w} : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({w} : Set X))))
    (hT7 : Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* alternatingGroup (Fin 7))) :
    oddQuotConj M ⟨w, hw⟩ ∉
      (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut (↥M ⧸ pPrimeCore 2 ↥M)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hinn
  obtain ⟨θ₀⟩ := hHe
  obtain ⟨P, hPF, hP, ⟨eP⟩⟩ := exists_fixed_component_image hw hww hTM hT
  obtain ⟨e7⟩ := hT7
  obtain ⟨ePZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_quotient_equiv eP
  have hPZ7 : Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 7)) :=
    ⟨ePZ.symm.trans e7⟩
  have hσ : ∀ y, oddQuotConj M ⟨w, hw⟩ (oddQuotConj M ⟨w, hw⟩ y) = y := by
    intro y
    have h1 : (⟨w, hw⟩ : ↥(normalizer (M : Set X))) * ⟨w, hw⟩ = 1 := Subtype.ext hww
    have h2 := congrArg (fun g => oddQuotConj M g y) h1
    simpa only [map_mul, map_one, MulAut.mul_apply, MulAut.one_apply] using h2
  have hPne : P ≠ ⊤ := by
    intro htop
    let ePQ := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    obtain ⟨ePQZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' ePQ
    have hO : pPrimeCore 2 (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ :=
      pPrimeCore_quotient_pPrimeCore_eq_bot 2
    let eQHe := ((QuotientGroup.quotientMulEquivOfEq hO).trans
      QuotientGroup.quotientBot).trans θ₀
    obtain ⟨eQZHe⟩ := GrSLit.nonempty_fusionZStar_equiv_held eQHe
    have hcHe : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 4030387200 := by
      rw [Nat.card_congr (ePQZ.trans eQZHe).toEquiv, Sporadic.He.card_He]
    have hc7 : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 2520 := by
      obtain ⟨e⟩ := hPZ7
      rw [Nat.card_congr e.toEquiv, GSThmB.card_alternatingGroup_seven]
    omega
  have hL34 := held_inner_fixed h2A h2B θ₀ _ hσ hinn P hPF hP hPne
  have h20160 := (PSL3Four.excludes_alternating_models_stated.{0} _
    (GSLit.statedClassicalModel_of_lieModel_psl_three hL34)).1
  obtain ⟨e⟩ := hPZ7
  rw [Nat.card_congr e.toEquiv,
    GSThmB.card_alternatingGroup_seven] at h20160
  norm_num at h20160

end CFSG.ComponentClassification.GSThmB.CorC
