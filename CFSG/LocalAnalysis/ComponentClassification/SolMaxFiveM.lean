module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveK

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem exists_klein_on {n : ℕ} {D : Finset (Fin n)} (hD : D.card = 4) :
    ∃ V : Subgroup (alternatingGroup (Fin n)), Nat.card V = 4 ∧ (∀ σ ∈ V, σ * σ = 1) ∧
      (∀ σ ∈ V, ∀ ω ∉ D, (σ : Perm (Fin n)) ω = ω) ∧
      ∀ σ : alternatingGroup (Fin n), σ * σ = 1 → (∀ ω ∉ D, (σ : Perm (Fin n)) ω = ω) →
        σ ∈ V := by
  classical
  have hcardD : Fintype.card ↥D = 4 := by rw [Fintype.card_coe, hD]
  let ψ : alternatingGroup ↥D ≃* alternatingGroup (Fin 4) :=
    (Fintype.equivFinOfCardEq hcardD).altCongrHom
  set V : Subgroup (alternatingGroup (Fin n)) :=
    (altFourKlein.map ψ.symm.toMonoidHom).map (alternatingGroup.ofSubtype D) with hVdef
  have hinj : Function.Injective
      ((alternatingGroup.ofSubtype D).comp ψ.symm.toMonoidHom) :=
    alternatingGroup.ofSubtype_injective.comp ψ.symm.injective
  have hVe : V ≃* altFourKlein := by
    rw [hVdef, Subgroup.map_map]
    exact (altFourKlein.equivMapOfInjective _ hinj).symm
  refine ⟨V, by rw [Nat.card_congr hVe.toEquiv, card_altFourKlein], ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    have hτ' : τ * τ = 1 := hτ
    rw [← map_mul, ← map_mul, hτ', map_one, map_one]
  · rintro _ ⟨τ, -, rfl⟩ ω hω
    have h1 := (alternatingGroup.mem_range_ofSubtype_iff D (alternatingGroup.ofSubtype D τ)).mp
      ⟨τ, rfl⟩
    by_contra hc
    exact hω (h1 (Equiv.Perm.mem_support.mpr hc))
  · intro σ hσ2 hσD
    have hsupp : (σ : Perm (Fin n)).support ⊆ D := by
      intro ω hω
      by_contra hωD
      exact (Equiv.Perm.mem_support.mp hω) (hσD ω hωD)
    obtain ⟨s, rfl⟩ := (alternatingGroup.mem_range_ofSubtype_iff D σ).mpr hsupp
    have hs2 : s * s = 1 := by
      apply alternatingGroup.ofSubtype_injective
      rw [map_mul, hσ2, map_one]
    have hψs : ψ s ∈ altFourKlein := by
      change ψ s * ψ s = 1
      rw [← map_mul, hs2, map_one]
    exact ⟨s, ⟨ψ s, hψs, ψ.symm_apply_apply s⟩, rfl⟩

variable {X : Type} [Group X]

theorem exists_four_of_acts [Finite X] {J : Subgroup X}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)) {c e₀ a j₀ : X} (he₀ : e₀ ∈ J)
    (hcN : c ∈ normalizer (J : Set X)) (hc2 : c * c = 1)
    (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) (haN : a ∈ normalizer (J : Set X))
    (ha2 : a * a = 1) (hac : a * c = c * a) (hj₀ : j₀ ∈ J)
    (haj₀ : a * j₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hj₀F : (coreImage θ hj₀).support ⊆ (coreImage θ he₀).supportᶜ) :
    ∃ E₀ : Subgroup X, E₀ ≤ J ⊓ centralizer ({c} : Set X) ⊓ centralizer ({a} : Set X) ∧
      Nonempty (E₀ ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      ∀ (x : X) (hx : x ∈ J), x ∈ E₀ →
        (coreImage θ hx).support ⊆ (coreImage θ he₀).support := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ₀ := coreImage θ he₀ with hσ₀def
  obtain ⟨V, hV4, hVsq, hVsupp, hVmem⟩ := exists_klein_on hs4
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) θ
  have hsplit : ∀ {g e : X} (hgN : g ∈ normalizer (J : Set X)) (he : e ∈ J),
      g * e⁻¹ ∈ UnbalancedLayer.coreActionKernel J → ρJ ⟨g, hgN⟩ = coreImage θ he := by
    intro g e hgN he hge
    have h1 := hρJ.eq_one_of_mem_coreActionKernel (by norm_num) hge
    have h2 : (⟨g, hgN⟩ : ↥(normalizer (J : Set X))) =
        ⟨g * e⁻¹, hge.1⟩ * ⟨e, le_normalizer he⟩ := Subtype.ext (by simp)
    rw [h2, map_mul, h1, one_mul]
    exact hρJ.apply_of_mem (by norm_num) ⟨e, he⟩
  have hρc : ρJ ⟨c, hcN⟩ = σ₀ := hsplit hcN he₀ hce
  have hρa : ρJ ⟨a, haN⟩ = coreImage θ hj₀ := hsplit haN hj₀ haj₀
  have hσ₀V : (⟨σ₀, coreImage_mem θ he₀⟩ : alternatingGroup (Fin 9)) ∈ V := by
    refine hVmem _ (Subtype.ext ?_) fun ω hω => ?_
    · have h3 : ρJ ⟨c * c, mul_mem hcN hcN⟩ = 1 := by
        have : (⟨c * c, mul_mem hcN hcN⟩ : ↥(normalizer (J : Set X))) = 1 := Subtype.ext hc2
        rw [this, map_one]
      have h4 : ρJ ⟨c * c, mul_mem hcN hcN⟩ = σ₀ * σ₀ := by
        have : (⟨c * c, mul_mem hcN hcN⟩ : ↥(normalizer (J : Set X))) =
            ⟨c, hcN⟩ * ⟨c, hcN⟩ := rfl
        rw [this, map_mul, hρc]
      change σ₀ * σ₀ = 1
      rw [← h4, h3]
    · by_contra hc
      exact hω (Equiv.Perm.mem_support.mpr hc)
  have hcommV : ∀ b ∈ V, (b : Perm (Fin 9)) * σ₀ = σ₀ * b := by
    intro b hb
    have h1 := hVsq _ (mul_mem hb hσ₀V)
    have h2 := hVsq _ hb
    have h3 := hVsq _ hσ₀V
    have h4 : b * ⟨σ₀, coreImage_mem θ he₀⟩ = ⟨σ₀, coreImage_mem θ he₀⟩ * b := by
      calc b * ⟨σ₀, coreImage_mem θ he₀⟩ =
          (b * ⟨σ₀, coreImage_mem θ he₀⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
        _ = ⟨σ₀, coreImage_mem θ he₀⟩⁻¹ * b⁻¹ := mul_inv_rev _ _
        _ = ⟨σ₀, coreImage_mem θ he₀⟩ * b := by
          rw [inv_eq_of_mul_eq_one_left h3, inv_eq_of_mul_eq_one_left h2]
    exact congrArg Subtype.val h4
  have hcommA : ∀ b ∈ V, (b : Perm (Fin 9)) * coreImage θ hj₀ = coreImage θ hj₀ * b := by
    intro b hb
    refine (Perm.Disjoint.commute ?_).eq
    rw [Perm.disjoint_iff_disjoint_support]
    refine Finset.disjoint_of_subset_right hj₀F ?_
    rw [Finset.disjoint_right]
    intro ω hω hωb
    exact (Perm.mem_support.mp hωb) (hVsupp b hb ω (Finset.mem_compl.mp hω))
  set G : Subgroup X := J ⊓ centralizer ({c} : Set X) ⊓ centralizer ({a} : Set X) with hGdef
  have hGJ : G ≤ J := inf_le_left.trans inf_le_left
  let f : ↥G →* alternatingGroup (Fin 9) :=
    (θ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))).comp (inclusion hGJ)
  have hf : ∀ x : ↥G, f x = θ ((inclusion hGJ x : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := fun _ => rfl
  have hker : Odd (Nat.card f.ker) := by
    let g : f.ker →* pPrimeCore 2 ↥J :=
      ((inclusion hGJ).comp f.ker.subtype).codRestrict _ fun x => by
        have h1 : f (x : ↥G) = 1 := x.2
        rw [hf, map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h1
        exact h1
    have hg : Function.Injective g := fun x y h => by
      have h' : (((x : ↥G) : X)) = ((y : ↥G) : X) :=
        congrArg (fun z : pPrimeCore 2 ↥J => ((z : ↥J) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (Subgroup.card_dvd_of_injective g hg)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hVr : V ≤ f.range := by
    intro b hb
    obtain ⟨x, hxc, hxa, hxb⟩ := hρJ.exists_lift_of_two_two hcN
      (isPGroup_zpowers_of_mul_self hc2) haN ha2 (by rw [hac])
      (by rw [hρc]; exact hcommV b hb) (by rw [hρa]; exact hcommA b hb)
    exact ⟨⟨x, mem_inf.2 ⟨mem_inf.2 ⟨x.2, hxc⟩, hxa⟩⟩, hxb⟩
  obtain ⟨P, hPV, hPinj⟩ := exists_lift_two_subgroup' f hker V hV2 hVr
  have hPcard : Nat.card P = 4 := by
    have h1 : Function.Injective (f.comp P.subtype) := by
      intro x y hxy
      have hxy' : f ((x : ↥G) * (y : ↥G)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr hxy
      have := hPinj _ (mul_mem x.2 (inv_mem y.2)) hxy'
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have h2 : (f.comp P.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPV]
    rw [← hV4, ← h2]
    exact Nat.card_congr (MonoidHom.ofInjective h1).toEquiv
  refine ⟨P.map G.subtype, map_subtype_le P, ?_, fun x hx hxE => ?_⟩
  · have hE4 : Nat.card (P.map G.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective G.subtype_injective, hPcard]
    have hEsq : ∀ g : P.map G.subtype, g * g = 1 := by
      rintro ⟨_, ⟨p, hp, rfl⟩⟩
      apply Subtype.ext
      have hfp : f p ∈ V := hPV ▸ mem_map_of_mem f hp
      have h1 : f (p * p) = 1 := by rw [map_mul, hVsq _ hfp]
      have := hPinj _ (mul_mem hp hp) h1
      change (p : X) * p = 1
      rw [← Subgroup.coe_mul, this]
      rfl
    have := isKleinFour_of_card hE4 hEsq
    have := isKleinFour_prod
    exact IsKleinFour.nonempty_mulEquiv
  · obtain ⟨p, hp, rfl⟩ := hxE
    have hfp : f p ∈ V := hPV ▸ mem_map_of_mem f hp
    intro ω hω
    by_contra hωD
    have h1 := hVsupp _ hfp ω hωD
    exact (Perm.mem_support.mp hω) h1

theorem signalizerFivePumpExactDataInput_mono
    {P Q : ∀ (X : Type) [Group X], X → ∀ J : Subgroup X,
      (↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)) →
        X → ∀ e₀ : X, e₀ ∈ J → Subgroup X → Subgroup X → X → Prop}
    (hQP : ∀ (X : Type) [Group X] (t : X) (J : Subgroup X)
      (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)) (c e₀ : X) (he₀ : e₀ ∈ J)
      (Jc M : Subgroup X) (a : X), Q X t J θ c e₀ he₀ Jc M a → P X t J θ c e₀ he₀ Jc M a)
    (h : SignalizerFivePumpExactDataInput P) : SignalizerFivePumpExactDataInput Q :=
  fun X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hQ =>
  h X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv hsubP χ hχ
    M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
    (hQP X t J θ c e₀ he₀ Jc M a hQ)

@[expose] def SignalizerFivePumpThreeFixFourInput : Prop :=
  SignalizerFivePumpExactDataInput fun X _ _ J θ c _ he₀ Jc M a =>
    a ∈ Jc ∧ (∃ (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)) (haM : a ∈ normalizer (M : Set X)),
      IsPermAction θM ρ ∧ (ρ ⟨a, haM⟩).supportᶜ.card = 3) ∧
    ∃ E₀ : Subgroup X, E₀ ≤ J ⊓ centralizer ({c} : Set X) ⊓ centralizer ({a} : Set X) ∧
      Nonempty (E₀ ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      ∀ (x : X) (hx : x ∈ J), x ∈ E₀ → (coreImage θ hx).support ⊆ (coreImage θ he₀).support

theorem signalizerFivePumpThreeFixMemInput_of_four (h : SignalizerFivePumpThreeFixFourInput) :
    SignalizerFivePumpThreeFixMemInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hP
  obtain ⟨haJc, hM⟩ := hP
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  obtain ⟨haJ, haF⟩ := hsubP a haJc
  obtain ⟨E₀, hE₀, hE₀k, hE₀s⟩ := exists_four_of_acts θ he₀ hcN hc2 hce hs4 haJN ha2 hac haJ
    (by rw [mul_inv_cancel]; exact one_mem _) haF
  exact h X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv hsubP
    χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
    ⟨haJc, hM, E₀, hE₀, hE₀k, hE₀s⟩

end CFSG.ComponentClassification.SolMax
