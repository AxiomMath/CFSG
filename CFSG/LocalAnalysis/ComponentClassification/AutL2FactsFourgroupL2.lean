module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCentPGL
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsRank
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsShape
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylowModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

theorem exists_e8_of_centralizing {G : Type*} [Group G] [Finite G] (V : Subgroup G)
    (hV2 : ∀ v ∈ V, v * v = 1) (hV4 : Nat.card V = 4) {τ : G} (hτ2 : τ * τ = 1) (hτV : τ ∉ V)
    (hτc : ∀ v ∈ V, τ * v = v * τ) :
    ∃ F : Subgroup G, V ≤ F ∧ τ ∈ F ∧ F ≤ V ⊔ zpowers τ ∧ (∀ x ∈ F, x * x = 1) ∧
      Nat.card F = 8 := by
  classical
  have hτ1 : τ ≠ 1 := fun h => hτV (h ▸ one_mem V)
  have hτo : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1
  have hz : ∀ b ∈ zpowers τ, b = 1 ∨ b = τ := by
    intro b hb
    rw [mem_zpowers_iff_mem_range_orderOf, hτo] at hb
    simp only [Finset.mem_image, Finset.mem_range] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    interval_cases k
    · left; exact pow_zero τ
    · right; exact pow_one τ
  have comm : ∀ (a : V) (b : zpowers τ), Commute (V.subtype a) ((zpowers τ).subtype b) := by
    intro a b
    rcases hz b b.2 with h | h
    · simp only [Subgroup.coe_subtype, h]
      exact Commute.one_right _
    · simp only [Subgroup.coe_subtype, h]
      exact (hτc a a.2).symm
  let φ := V.subtype.noncommCoprod (zpowers τ).subtype comm
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have h1 : (a : G) * b = 1 := hab
    rcases hz b b.2 with hb | hb
    · rw [hb, mul_one] at h1
      exact Prod.ext (Subtype.ext h1) (Subtype.ext hb)
    · exfalso
      apply hτV
      have : (b : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [← hb, this]
      exact inv_mem a.2
  refine ⟨φ.range, ?_, ⟨(1, ⟨τ, mem_zpowers τ⟩), by simp [φ]⟩, ?_, ?_, ?_⟩
  · intro v hv
    exact ⟨(⟨v, hv⟩, 1), by simp [φ]⟩
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact mul_mem (mem_sup_left a.2) (mem_sup_right b.2)
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    show (a : G) * b * ((a : G) * b) = 1
    have hab : (a : G) * b = b * a := comm a b
    have hb2 : (b : G) * b = 1 := by
      rcases hz b b.2 with h | h <;> rw [h]
      · exact mul_one 1
      · exact hτ2
    calc (a : G) * b * ((a : G) * b) = a * a * (b * b) := by
          rw [mul_assoc, ← mul_assoc (b : G), ← hab, mul_assoc, mul_assoc]
      _ = 1 := by rw [hV2 a a.2, hb2, one_mul]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hV4,
      Nat.card_zpowers, hτo]

theorem exists_right_ne_one_of_card_eight {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (E : Subgroup (PGammaL2 F)) (hE2 : ∀ x ∈ E, x * x = 1)
    (hE8 : 8 ≤ Nat.card E) : ∃ y ∈ E, y.right ≠ 1 := by
  have hlin : Nat.card (linearPart E) ≤ 4 :=
    pgl2_card_le_four_of_sq hodd _ fun g hg => SemidirectProduct.inl_injective (by
      rw [map_mul, map_one]; exact hE2 _ hg)
  by_contra h
  push Not at h
  have hpi : Nat.card (E.map (fieldProj F)) ≤ 1 := by
    apply Finite.card_le_one_iff_subsingleton.mpr
    constructor
    rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
    apply Subtype.ext
    change a.right = b.right
    rw [h a ha, h b hb]
  have := card_eq_linearPart_mul E
  have : 8 ≤ 4 * 1 := by
    calc 8 ≤ Nat.card E := hE8
      _ = _ := this
      _ ≤ 4 * 1 := Nat.mul_le_mul hlin hpi
  omega

theorem fourgroupE8_psl2 {S : Type} [Group S] [Finite S] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hS : Blueprint.LieModel S .PSL 2 p f) (E : Subgroup (MulAut S))
    (hE2 : ∀ e ∈ E, e * e = 1) (hE8 : Nat.card E = 8) :
    (∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x) ∧
      ∀ V : Subgroup S, IsKleinFour V →
        ∃ F : Subgroup (MulAut S), F ≤ E ⊔ (MulAut.conj : S →* MulAut S).range ∧
          (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8 ∧ V.map (MulAut.conj : S →* MulAut S) ≤ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  have hodd := isOddPrimePower_of hp hp2 hf hF
  set Φ := autEquiv e with hΦ
  obtain ⟨_, ⟨e₀, he₀E, rfl⟩, he₀r⟩ := exists_right_ne_one_of_card_eight hodd
    (E.map Φ.toMonoidHom) (by
      rintro _ ⟨y, hy, rfl⟩
      change Φ y * Φ y = 1
      rw [← map_mul, hE2 y hy, map_one])
    (by rw [Subgroup.card_map_of_injective Φ.injective, hE8])
  change (Φ e₀).right ≠ 1 at he₀r
  have hg2 : Φ e₀ * Φ e₀ = 1 := by rw [← map_mul, hE2 e₀ he₀E, map_one]
  obtain ⟨hσ, -⟩ := eqLocus_equiv_fieldCent hodd e e₀ hg2 he₀r
  set σ := (Φ e₀).right with hσdef
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    have := congrArg (fun τ : F ≃+* F => τ z) h1
    simpa using this
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p', n, -, hpodd, -, hc⟩ := hodd
    rw [hc]
    exact hpodd.pow
  have hK₀odd' : Odd (Nat.card K₀) := by
    rw [hcard] at hFodd
    exact Nat.Odd.of_mul_left (by rwa [← pow_two])
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := isOddPrimePower_of_odd_card _ hK₀odd'
  obtain ⟨j, hj⟩ := hK₀odd'
  have hj1 : 1 ≤ j := by
    have := Finite.one_lt_card (α := K₀)
    omega
  have h8 : 8 ∣ Nat.card F - 1 := by
    rw [hcard, hj]
    exact ⟨j * (j + 1) / 2, by
      have : (2 * j + 1) ^ 2 - 1 = 4 * (j * (j + 1)) := Nat.sub_eq_of_eq_add (by ring)
      rw [this]
      have hev : Even (j * (j + 1)) := Nat.even_mul_succ_self j
      obtain ⟨k, hk⟩ := hev
      rw [hk]
      omega⟩
  have hq4 : Nat.card F % 4 = 1 := by
    have := Finite.one_lt_card (α := F)
    omega
  have htv : 3 ≤ twoVal F := by
    have hq1 : Nat.card F - 1 ≠ 0 := by
      have := Finite.one_lt_card (α := F)
      omega
    have := (Nat.factorization_le_iff_dvd (by norm_num) hq1).mpr
      (show 2 ^ 3 ∣ Nat.card F - 1 by simpa using h8)
    have h3 := this 2
    simp only [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h3
    exact h3
  refine ⟨?_, ?_⟩
  ·
    intro P
    obtain ⟨m, -, ⟨ψ⟩⟩ := sylow_two_dihedral_of_equiv e hodd P
    have hcardP : Nat.card (P : Subgroup S) = 2 ^ twoVal F := by
      rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv, psl2_factorization_two hodd hq4]
    have hm2 : 2 ≤ m := by
      have h := Nat.card_congr ψ.toEquiv
      rw [hcardP, DihedralGroup.nat_card, ← pow_succ'] at h
      have := Nat.pow_right_injective le_rfl h
      omega
    refine ⟨ψ.symm (DihedralGroup.r 1), (ψ.symm _).2, ψ.symm (DihedralGroup.sr 0),
      (ψ.symm _).2, fun h => ?_⟩
    have h1 : ψ.symm (DihedralGroup.r 1) * ψ.symm (DihedralGroup.sr 0) =
        ψ.symm (DihedralGroup.sr 0) * ψ.symm (DihedralGroup.r 1) := Subtype.ext h
    rw [← map_mul, ← map_mul, ψ.symm.injective.eq_iff, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq] at h1
    have h2 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
      have : (2 : ZMod (2 ^ m)) = 0 := by linear_combination -h1
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd two_pos h2
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · intro V hV
    obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥(fieldCent σ)) := inferInstance
    have hfac : (Nat.card (fieldCent σ)).factorization 2 =
        (Nat.card (PSL2 F)).factorization 2 := by
      rw [card_fieldCent_eq hK₀ h90 hσσ hcard hodd, pgl2_card_formula, psl2_card_formula F hodd,
        hcard, hj]
      exact factorization_two_pgl_psl hj1
    set P₁ : Subgroup (PSL2 F) := (P₀ : Subgroup ↥(fieldCent σ)).map (fieldCent σ).subtype
    have hP₁le : P₁ ≤ fieldCent σ := Subgroup.map_subtype_le _
    have hP₁ : Nat.card P₁ = 2 ^ (Nat.card (PSL2 F)).factorization 2 := by
      rw [Subgroup.card_map_of_injective (fieldCent σ).subtype_injective,
        Sylow.card_eq_multiplicity, hfac]
    let Q₁ : Sylow 2 (PSL2 F) := Sylow.ofCard P₁ hP₁
    set V' := V.map e.toMonoidHom with hV'
    have hV'card : Nat.card V' = 4 := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact IsKleinFour.card_four
    have hV'2 : IsPGroup 2 V' := IsPGroup.of_card (n := 2) (by rw [hV'card]; norm_num)
    obtain ⟨Q, hQ⟩ := hV'2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 F) Q₁ Q
    have hvP : ∀ v ∈ V', g⁻¹ * v * g ∈ fieldCent σ := by
      intro v hv
      have h1 : v ∈ ((g • Q₁ : Sylow 2 (PSL2 F)) : Subgroup (PSL2 F)) := by rw [hg]; exact hQ hv
      rw [mem_smul_sylow_iff_conj] at h1
      exact hP₁le h1
    set τ' : PGammaL2 F := incl F g * SemidirectProduct.inr σ * (incl F g)⁻¹ with hτ'
    have hσc : ∀ w ∈ fieldCent σ,
        SemidirectProduct.inr σ * incl F w = incl F w * SemidirectProduct.inr σ := by
      intro w hw
      rw [commute_incl_iff, semilinearAction_inr]
      exact hw
    have hτ'c : ∀ v ∈ V', τ' * incl F v = incl F v * τ' := by
      intro v hv
      have hw := hσc _ (hvP v hv)
      rw [map_mul, map_mul, map_inv] at hw
      calc τ' * incl F v = incl F g * (SemidirectProduct.inr σ *
            ((incl F g)⁻¹ * incl F v * incl F g)) * (incl F g)⁻¹ := by
              rw [hτ']; group
        _ = incl F g * (((incl F g)⁻¹ * incl F v * incl F g) *
            SemidirectProduct.inr σ) * (incl F g)⁻¹ := by rw [hw]
        _ = incl F v * τ' := by rw [hτ']; group
    have hτ'2 : τ' * τ' = 1 := by
      have hσ2 : σ * σ = 1 := by
        have := pow_orderOf_eq_one σ
        rwa [hσ, pow_two] at this
      have h1 : SemidirectProduct.inr σ * SemidirectProduct.inr σ = (1 : PGammaL2 F) := by
        rw [← map_mul, hσ2, map_one]
      calc τ' * τ' = incl F g * (SemidirectProduct.inr σ * SemidirectProduct.inr σ) *
            (incl F g)⁻¹ := by rw [hτ']; group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    have hτ'r : τ'.right = σ := by
      rw [hτ', right_conj]
      rfl
    obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd (Φ e₀)
      (orderOf_eq_prime (by rw [pow_two]; exact hg2) (fun h => he₀r (by rw [hσdef, h]; rfl)))
      he₀r
    set c : PGammaL2 F := SemidirectProduct.inl C
    set ισ : PGammaL2 F := SemidirectProduct.inr σ with hισ
    set κ : PGammaL2 F := ισ * c * ισ⁻¹ * c⁻¹ with hκ
    have hκL : κ ∈ pGammaL2PSLRange F := by
      have := commutator_mem_pslRange ισ c
      rwa [commutatorElement_def] at this
    have hσe : ισ = κ * Φ e₀ := by
      have hc' : Φ e₀ = c * ισ * c⁻¹ := by
        rw [← hC]
        group
      rw [hc', hκ]
      group
    set τ : MulAut S := Φ.symm τ' with hτ
    have hτmem : τ ∈ E ⊔ (MulAut.conj : S →* MulAut S).range := by
      have hInn : ∀ x ∈ pGammaL2PSLRange F, Φ.symm x ∈ (MulAut.conj : S →* MulAut S).range := by
        intro x hx
        rw [← map_autEquiv_innAut e] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
        exact hβ
      have hgL : incl F g ∈ pGammaL2PSLRange F := ⟨g, rfl⟩
      have hτeq : τ = Φ.symm (incl F g) * (Φ.symm κ * e₀) *
          (Φ.symm (incl F g))⁻¹ := by
        rw [hτ, hτ', hσe, map_mul, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rw [hτeq]
      refine mul_mem (mul_mem (mem_sup_right (hInn _ hgL)) (mul_mem
        (mem_sup_right (hInn _ hκL)) (mem_sup_left he₀E)))
        (inv_mem (mem_sup_right (hInn _ hgL)))
    have hconj_inj : Function.Injective (MulAut.conj : S →* MulAut S) := by
      intro a b h
      have h' : autEquiv e (MulAut.conj a) = autEquiv e (MulAut.conj b) := by rw [h]
      rw [autEquiv_conj, autEquiv_conj] at h'
      exact e.injective (incl_injective F h')
    set W := V.map (MulAut.conj : S →* MulAut S) with hW
    have hW4 : Nat.card W = 4 := by
      rw [Subgroup.card_map_of_injective hconj_inj]
      exact IsKleinFour.card_four
    have hW2 : ∀ w ∈ W, w * w = 1 := by
      rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul]
      have := IsKleinFour.mul_self (⟨v, hv⟩ : V)
      rw [show v * v = 1 from congrArg Subtype.val this, map_one]
    have hτ2 : τ * τ = 1 := by
      apply Φ.injective
      rw [map_mul, hτ, MulEquiv.apply_symm_apply, hτ'2, map_one]
    have hτW : τ ∉ W := by
      rintro ⟨v, -, hv⟩
      have h1 : Φ (MulAut.conj v) = τ' := by rw [hv, hτ, MulEquiv.apply_symm_apply]
      rw [autEquiv_conj, incl_apply] at h1
      have h2 := congrArg SemidirectProduct.right h1
      rw [SemidirectProduct.right_inl, hτ'r] at h2
      exact he₀r h2.symm
    have hτc : ∀ w ∈ W, τ * w = w * τ := by
      rintro _ ⟨v, hv, rfl⟩
      apply Φ.injective
      rw [map_mul, map_mul, hτ, MulEquiv.apply_symm_apply, autEquiv_conj]
      exact hτ'c _ ⟨v, hv, rfl⟩
    obtain ⟨F₈, hWF, -, hF₈le, hF₈2, hF₈8⟩ := exists_e8_of_centralizing W hW2 hW4 hτ2 hτW hτc
    refine ⟨F₈, hF₈le.trans (sup_le ?_ ?_), hF₈2, hF₈8, hWF⟩
    · exact (Subgroup.map_le_range _ _).trans le_sup_right
    · exact (zpowers_le).mpr hτmem

end CFSG.ComponentClassification.AutL2Facts
