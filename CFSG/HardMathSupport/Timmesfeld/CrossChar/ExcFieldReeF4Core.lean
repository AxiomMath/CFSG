module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Sub
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
public import CFSG.Quasithin.EmptyFaithful.R3c18G
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute mem_zpowers_of_fixed
  ringEquiv_eq_refl_of_card_two large_Ree_full_inner_field_automorphism_normal_form)


section General

variable {A B : Type*} [Group A] [Group B]

theorem map_commutator_mulEquiv (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

@[expose] noncomputable def commutatorMulEquiv (e : A ≃* B) : commutator A ≃* commutator B :=
  (e.subgroupMap (commutator A)).trans (MulEquiv.subgroupCongr (map_commutator_mulEquiv e))

theorem eq_one_of_centralizes_commutator {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) (hZD : Subgroup.center (commutator G) = ⊥) {g : G}
    (hg : ∀ c ∈ commutator G, g * c * g⁻¹ = c) : g = 1 := by
  set C := Subgroup.centralizer (commutator G : Set G)
  have hgC : g ∈ C := Subgroup.mem_centralizer_iff.2 fun c hc => by
    calc c * g = g * c * g⁻¹ * g := by rw [hg c hc]
      _ = g * c := by group
  have hconj : ∀ j : G, j * g⁻¹ * j⁻¹ ∈ C := fun j => Subgroup.mem_centralizer_iff.2 fun c hc => by
    have h1 : j⁻¹ * c * j ∈ commutator G := by
      simpa using (inferInstance : (commutator G).Normal).conj_mem c hc j⁻¹
    have h2 : (j⁻¹ * c * j) * g⁻¹ = g⁻¹ * (j⁻¹ * c * j) :=
      (Subgroup.mem_centralizer_iff.1 (inv_mem hgC) _ h1)
    calc c * (j * g⁻¹ * j⁻¹) = j * ((j⁻¹ * c * j) * g⁻¹) * j⁻¹ := by group
      _ = j * (g⁻¹ * (j⁻¹ * c * j)) * j⁻¹ := by rw [h2]
      _ = j * g⁻¹ * j⁻¹ * c := by group
  have hcomm : ∀ j : G, g * j = j * g := by
    intro j
    have hmem : g * j * g⁻¹ * j⁻¹ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top j)
    have hC : g * j * g⁻¹ * j⁻¹ ∈ C := by
      have := mul_mem hgC (hconj j)
      simpa [mul_assoc] using this
    have hz : (⟨g * j * g⁻¹ * j⁻¹, hmem⟩ : commutator G) ∈ Subgroup.center (commutator G) :=
      Subgroup.mem_center_iff.2 fun c => Subtype.ext (Subgroup.mem_centralizer_iff.1 hC c c.2)
    rw [hZD, Subgroup.mem_bot] at hz
    have h1 : g * j * g⁻¹ * j⁻¹ = 1 := congrArg Subtype.val hz
    calc g * j = g * j * g⁻¹ * j⁻¹ * (j * g) := by group
      _ = j * g := by rw [h1, one_mul]
  have hgZ : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun j => (hcomm j).symm
  rw [hZ, Subgroup.mem_bot] at hgZ
  exact hgZ

end General


theorem reeGamma_normalForm {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ α : MulAut (F4.reeGamma K a), ∃ (x : F4.reeGamma K a) (β : K ≃+* K),
      α = MulAut.conj x * F4.reeGammaFieldAut K a β) ∧
    ∀ (x x' : F4.reeGamma K a) (β β' : K ≃+* K),
      MulAut.conj x * F4.reeGammaFieldAut K a β = MulAut.conj x' * F4.reeGammaFieldAut K a β' →
        x = x' ∧ β = β' := by
  obtain ⟨-, hNF, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  refine ⟨fun α => ?_, fun x x' β β' h => ?_⟩
  · obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
    exact ⟨x, β, hxβ⟩
  · obtain ⟨q, -, huniq⟩ := hNF (MulAut.conj x * F4.reeGammaFieldAut K a β)
    have h1 := huniq (x, β) rfl
    have h2 := huniq (x', β') h
    have h3 := h1.trans h2.symm
    exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

section Core

variable {b : ℕ} {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem isQuasisimple_reeGamma (hb : 1 ≤ b) (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    CFSG.IsQuasisimple (F4.reeGamma k b) := by
  set e := ReeTag.reeFixedEquivReeGamma k b
  have hZ : Subgroup.center (F4.reeGamma k b) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial b k hk
  have hZ' : Subgroup.center (reeFixed ReeTag.F4 k b) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (F4.reeGamma k b) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [hZ, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  have : IsSimpleGroup (reeFixed ReeTag.F4 k b ⧸ Subgroup.center (reeFixed ReeTag.F4 k b)) :=
    CFSG.LieType.Simplicity.isSimpleGroup_quotient_center_reeFixed_F4 b hb hk
  have hs : IsSimpleGroup (reeFixed ReeTag.F4 k b) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hs' : IsSimpleGroup (F4.reeGamma k b) := e.symm.isSimpleGroup
  refine isQuasisimple_of_simple_nonabelian fun hcomm => ?_
  obtain ⟨x, hx⟩ := exists_ne (1 : F4.reeGamma k b)
  have hxZ : x ∈ Subgroup.center (F4.reeGamma k b) :=
    Subgroup.mem_center_iff.2 fun z => hcomm z x
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact hx hxZ

theorem commutator_reeGamma_eq_top (hb : 1 ≤ b) (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    commutator (F4.reeGamma k b) = ⊤ :=
  (isQuasisimple_reeGamma hb hk).1.commutator_eq_top

theorem isQuasisimple_commutator_reeGamma (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    CFSG.IsQuasisimple (commutator (F4.reeGamma k b)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (commutatorMulEquiv (ReeTag.reeFixedEquivReeGamma k 0))
      ((CFSG.LieType.Simplicity.titsData k hk2).isQuasisimple hk2)
  · have h := commutator_reeGamma_eq_top hb hk
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.topEquiv (G := F4.reeGamma k b)).symm.trans (MulEquiv.subgroupCongr h.symm))
      (isQuasisimple_reeGamma hb hk)

theorem not_coprime_card_commutator_reeGamma (hk : Nat.card k = 2 ^ (2 * b + 1)) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ (2 ^ (2 * b + 1)) ^ 4 - 1) :
    ¬ Nat.Coprime p (Nat.card (commutator (F4.reeGamma k b))) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    rw [← Nat.card_congr (commutatorMulEquiv (ReeTag.reeFixedEquivReeGamma k 0)).toEquiv]
    have h15 : p ∣ 15 := by simpa using hd
    have hp35 : p = 3 ∨ p = 5 := by
      have h15' : p ∣ 3 * 5 := by simpa using h15
      rcases (Nat.Prime.dvd_mul hp).1 h15' with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
    rcases hp35 with rfl | rfl
    · obtain ⟨x, y, -, -, -, -, -, -, hcard, -⟩ :=
        CFSG.SectionRank.Tits_sylow3_cubic_witness (K := k) hk2
      have h1 := Subgroup.card_subgroup_dvd_card (Subgroup.closure ({x, y} :
        Set (commutator (reeFixed ReeTag.F4 k 0))))
      rw [hcard] at h1
      exact (dvd_pow_self 3 (by norm_num)).trans h1
    · obtain ⟨x, y, -, -, -, -, hcard, -⟩ :=
        CFSG.SectionRank.Tits_sylow5_square_witness (K := k) hk2
      have h1 := Subgroup.card_subgroup_dvd_card (Subgroup.closure ({x, y} :
        Set (commutator (reeFixed ReeTag.F4 k 0))))
      rw [hcard] at h1
      exact (dvd_pow_self 5 (by norm_num)).trans h1
  · rw [commutator_reeGamma_eq_top hb hk, Subgroup.card_top,
      (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
        b k hk).1]
    set Q := 2 ^ (2 * b + 1)
    have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
    have hfac : Q ^ 4 - 1 = (Q - 1) * (Q + 1) * (Q ^ 2 + 1) := by
      have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ1
      zify [hQ1, h4]
      ring
    rw [hfac] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
          (Dvd.dvd.mul_left (dvd_pow h (by norm_num)) _) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
          (Dvd.dvd.mul_left (dvd_pow h (by norm_num)) _) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_left (dvd_pow h (by norm_num)) _) _) _

theorem reeGamma_commutator_core (hk : Nat.card k = 2 ^ (2 * b + 1)) (g : F4.reeGamma k b)
    (τ : k ≃+* k)
    (h : ∀ c ∈ commutator (F4.reeGamma k b), g * F4.reeGammaFieldAut k b τ c * g⁻¹ = c) :
    g = 1 ∧ τ = 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    have hτ : τ = 1 := ringEquiv_eq_refl_of_card_two hk2 τ
    subst hτ
    refine ⟨?_, rfl⟩
    have hone : F4.reeGammaFieldAut k 0 1 = 1 := by
      rw [← reeGammaFieldAutHom_apply, map_one]
    have hZ : Subgroup.center (F4.reeGamma k 0) = ⊥ :=
      ReeTag.large_Ree_fixed_group_center_trivial 0 k hk
    have hZD : Subgroup.center (commutator (F4.reeGamma k 0)) = ⊥ := by
      have h0 := CFSG.RankThree.PartTwo.KFacts.KS14.center_commutator_reeFixed_tits_eq_bot hk2
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv
        (commutatorMulEquiv (ReeTag.reeFixedEquivReeGamma k 0)), h0, Subgroup.map_bot]
    refine eq_one_of_centralizes_commutator hZ hZD fun c hc => ?_
    have := h c hc
    rwa [hone, MulAut.one_apply] at this
  · obtain ⟨-, huniq⟩ := reeGamma_normalForm hb hk
    have htop := commutator_reeGamma_eq_top hb hk
    have hα : MulAut.conj g * F4.reeGammaFieldAut k b τ =
        MulAut.conj 1 * F4.reeGammaFieldAut k b 1 := by
      have hone : F4.reeGammaFieldAut k b 1 = 1 := by
        rw [← reeGammaFieldAutHom_apply, map_one]
      rw [hone, map_one, mul_one]
      refine MulEquiv.ext fun c => ?_
      rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply]
      exact h c (htop ▸ Subgroup.mem_top c)
    exact huniq g 1 τ 1 hα

end Core

section Field

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem reeGammaFieldAut_hom_facts :
    (∀ β γ : K ≃+* K, F4.reeGammaFieldAut K a (β * γ) =
      F4.reeGammaFieldAut K a β * F4.reeGammaFieldAut K a γ) ∧
    F4.reeGammaFieldAut K a 1 = 1 ∧
    (∀ (β : K ≃+* K) (n : ℕ), F4.reeGammaFieldAut K a (β ^ n) = F4.reeGammaFieldAut K a β ^ n) ∧
    ∀ (β : K ≃+* K) (n : ℤ), F4.reeGammaFieldAut K a (β ^ n) = F4.reeGammaFieldAut K a β ^ n :=
  ⟨fun β γ => map_mul (F4.reeGammaFieldAutHom K a) β γ, map_one (F4.reeGammaFieldAutHom K a),
    fun β n => map_pow (F4.reeGammaFieldAutHom K a) β n,
    fun β n => map_zpow (F4.reeGammaFieldAutHom K a) β n⟩

theorem fieldCoreAt_reeGammaFieldAut (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1) (σ : K ≃+* K)
    (hσ : orderOf σ = p) : FieldCoreAt p (F4.reeGammaFieldAut K a σ) := by
  classical
  obtain ⟨b, hk, ψ, hbp, hψinj, hψfix, hψτ⟩ := exists_reeGamma_fixSubfield_hom hK hp hp2 σ hσ
  obtain ⟨hNFex, hNFuniq⟩ := reeGamma_normalForm ha hK
  obtain ⟨hmul, hone, hpow, hzpow⟩ := reeGammaFieldAut_hom_facts (K := K) (a := a)
  have hdvd₀ : p ∣ (2 ^ (2 * b + 1)) ^ 4 - 1 := by
    have h : 2 ^ (2 * a + 1) = (2 ^ (2 * b + 1)) ^ p := by rw [← pow_mul, hbp]
    rw [h] at hdvd
    exact (CFSG.Quasithin.R3c18.dvd_pow_sub_one_iff_of_pow hp (by positivity) 4).1 hdvd
  refine ⟨(commutator (F4.reeGamma (fixSubfield σ) b)).map ψ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨c, -, rfl⟩
    exact (hψfix (ψ c)).2 ⟨c, rfl⟩
  ·
    rintro f hf _ ⟨c, hc, rfl⟩
    obtain ⟨f₀, rfl⟩ := (hψfix f).1 hf
    exact ⟨f₀ * c * f₀⁻¹,
      (inferInstance : (commutator (F4.reeGamma (fixSubfield σ) b)).Normal).conj_mem c hc f₀,
      by simp [map_mul, map_inv]⟩
  ·
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator (F4.reeGamma (fixSubfield σ) b)).equivMapOfInjective ψ hψinj)
      (isQuasisimple_commutator_reeGamma hk)
  ·
    rw [Subgroup.card_map_of_injective hψinj]
    exact not_coprime_card_commutator_reeGamma hk hp hdvd₀
  ·
    intro β hβp hβσ hβT
    obtain ⟨g, τ, rfl⟩ := hNFex β
    have hg : F4.reeGammaFieldAut K a σ g = g := by
      have e1 : F4.reeGammaFieldAut K a σ * MulAut.conj g =
          MulAut.conj (F4.reeGammaFieldAut K a σ g) * F4.reeGammaFieldAut K a σ := by
        rw [← mul_conj_mul_inv (F4.reeGammaFieldAut K a σ) g, inv_mul_cancel_right]
      have e2 : MulAut.conj (F4.reeGammaFieldAut K a σ g) * F4.reeGammaFieldAut K a (τ * σ) =
          MulAut.conj g * F4.reeGammaFieldAut K a (τ * σ) := by
        calc MulAut.conj (F4.reeGammaFieldAut K a σ g) * F4.reeGammaFieldAut K a (τ * σ)
            = MulAut.conj (F4.reeGammaFieldAut K a σ g) * F4.reeGammaFieldAut K a σ *
                F4.reeGammaFieldAut K a τ := by rw [ringAut_commute τ σ, hmul, mul_assoc]
          _ = F4.reeGammaFieldAut K a σ * (MulAut.conj g * F4.reeGammaFieldAut K a τ) := by
                rw [← e1, mul_assoc]
          _ = MulAut.conj g * F4.reeGammaFieldAut K a τ * F4.reeGammaFieldAut K a σ :=
                hβσ.symm
          _ = MulAut.conj g * F4.reeGammaFieldAut K a (τ * σ) := by rw [hmul, mul_assoc]
      exact (hNFuniq _ _ _ _ e2).1
    obtain ⟨g₀, rfl⟩ := (hψfix g).1 hg
    have hcore : ∀ c ∈ commutator (F4.reeGamma (fixSubfield σ) b),
        g₀ * F4.reeGammaFieldAut (fixSubfield σ) b (fixSubfieldRestrict τ σ) c * g₀⁻¹ = c := by
      intro c hc
      have h1 := hβT (ψ c) ⟨c, hc, rfl⟩
      rw [MulAut.mul_apply, MulAut.conj_apply, hψτ, ← map_inv, ← map_mul, ← map_mul] at h1
      exact hψinj h1
    obtain ⟨hg₀, hτ₀⟩ := reeGamma_commutator_core hk g₀ _ hcore
    have hτσ : τ ∈ Subgroup.zpowers σ := by
      refine mem_zpowers_of_fixed fun x hx => ?_
      have h1 := congrArg (fun φ : fixSubfield σ ≃+* fixSubfield σ =>
        ((φ ⟨x, hx⟩ : fixSubfield σ) : K)) hτ₀
      simpa using h1
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτσ
    have hβ : MulAut.conj (ψ g₀) * F4.reeGammaFieldAut K a (σ ^ n) =
        F4.reeGammaFieldAut K a σ ^ n := by
      rw [hg₀, map_one, map_one, one_mul, hzpow]
    rw [hβ] at hβp ⊢
    have hσhp : F4.reeGammaFieldAut K a σ ^ p = 1 := by
      rw [← hpow, ← hσ, pow_orderOf_eq_one, hone]
    have hdvd' : orderOf (F4.reeGammaFieldAut K a σ ^ n) ∣ p :=
      (orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers _ n)).trans
        (orderOf_dvd_of_pow_eq_one hσhp)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hβp.symm hdvd')

theorem fieldCoreAt_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1)
    (x : MulAut (F4.reeGamma K a)) (hxp : x ^ p = 1) (hxo : x ∉ innerAut (F4.reeGamma K a)) :
    FieldCoreAt p x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNFex, hNFuniq⟩ := reeGamma_normalForm ha hK
  obtain ⟨-, hone, hpow, -⟩ := reeGammaFieldAut_hom_facts (K := K) (a := a)
  obtain ⟨y, σ, rfl⟩ := hNFex x
  have hσp : σ ^ p = 1 := by
    obtain ⟨z, hz⟩ : ∃ z, (MulAut.conj y * F4.reeGammaFieldAut K a σ) ^ p =
        MulAut.conj z * F4.reeGammaFieldAut K a σ ^ p :=
      ⟨_, CFSG.RankThree.PartOne.KE.conj_mul_pow_aut y (F4.reeGammaFieldAut K a σ) p⟩
    have h' : MulAut.conj 1 * F4.reeGammaFieldAut K a 1 =
        MulAut.conj z * F4.reeGammaFieldAut K a (σ ^ p) := by
      rw [map_one, hone, one_mul, hpow, ← hz, hxp]
    exact (hNFuniq _ _ _ _ h').2.symm
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hxo ⟨y, by rw [hone, mul_one]⟩
  have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp σ hσ _ hxp
    ⟨y, rfl⟩
  rw [hg]
  exact (fieldCoreAt_reeGammaFieldAut ha hK hp hp2 hdvd σ hσ).conj (MulAut.conj g)

theorem isLocallyBalancedAbs_reeGamma_of_dvd (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1)
    (hr : RankLE2 p (F4.reeGamma K a)) : IsLocallyBalancedAbs p 3 (F4.reeGamma K a) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  exact isLocallyBalancedAbs_of_fieldCore hp hinj
    (fun D hD hcard hin => false_of_inner_cube_of_rankLE2 hp hinj hr hD hcard hin)
    fun x hxp hxo => fieldCoreAt_reeGamma ha hK hp hp2 hdvd x hxp hxo

end Field

end CFSG.HardMathSupport.Timmesfeld.CrossChar
