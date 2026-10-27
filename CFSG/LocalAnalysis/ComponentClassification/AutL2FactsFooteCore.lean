module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsInvCommute
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSqClass
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

theorem footeOutAbelian :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel S .PSL 2 p f →
        ∀ φ ψ : MulAut S, ∃ s : S, φ * ψ * φ⁻¹ * ψ⁻¹ = MulAut.conj s := by
  intro S _ _ p f _ _ _ hS φ ψ
  obtain ⟨-, -, -, -, F, _, _, -, ⟨e⟩⟩ := lieModel_psl2_data hS
  have h := commutator_mem_pslRange (autEquiv e φ) (autEquiv e ψ)
  rw [← map_autEquiv_innAut e] at h
  obtain ⟨α, ⟨s, rfl⟩, hα⟩ := h
  refine ⟨s, (autEquiv e).injective ?_⟩
  change (autEquiv e) (MulAut.conj s) = _ at hα
  rw [hα, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem mem_eqLocus_iff_semilinear {S : Type} [Group S] {F : Type} [Field F] [Finite F]
    (e : S ≃* PSL2 F) (i : MulAut S) (s : S) :
    s ∈ MonoidHom.eqLocus i.toMonoidHom (MonoidHom.id S) ↔
      semilinearAction F (autEquiv e i) (e s) = e s := by
  rw [semilinearAction_autEquiv_apply]
  constructor
  · intro h
    have h' : i s = s := h
    rw [h']
  · intro h
    exact e.injective h

theorem eqLocus_equiv_fieldCent {S : Type} [Group S] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : S ≃* PSL2 F) (i : MulAut S)
    (hg2 : autEquiv e i * autEquiv e i = 1) (hr : (autEquiv e i).right ≠ 1) :
    orderOf (autEquiv e i).right = 2 ∧
      Nonempty (↥(MonoidHom.eqLocus i.toMonoidHom (MonoidHom.id S)) ≃*
        ↥(fieldCent (autEquiv e i).right)) := by
  set g := autEquiv e i
  have hg1 : g ≠ 1 := fun h => hr (by rw [h]; rfl)
  have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd g hgo hr
  set σ := g.right
  have hσσ' : σ * σ = 1 := by
    have := congrArg SemidirectProduct.right hg2
    simpa using this
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hσσ') hr, ?_⟩
  set c : MulAut (PSL2 F) := semilinearAction F (SemidirectProduct.inl C)
  have hsg : semilinearAction F g = c * psl2FieldAut F σ * c⁻¹ := by
    have : g = SemidirectProduct.inl C * SemidirectProduct.inr σ *
        (SemidirectProduct.inl C)⁻¹ := by
      rw [← hC]
      group
    rw [this, map_mul, map_mul, map_inv, semilinearAction_inr]
  set E : S ≃* PSL2 F := e.trans (c⁻¹ : MulAut (PSL2 F))
  have hmap : (MonoidHom.eqLocus i.toMonoidHom (MonoidHom.id S)).map E.toMonoidHom =
      fieldCent σ := by
    ext z
    rw [Subgroup.mem_map_equiv, mem_eqLocus_iff_semilinear e i, hsg]
    have hz : e (E.symm z) = c z := by simp [E]
    rw [hz]
    have hcz : (c * psl2FieldAut F σ * c⁻¹) (c z) = c (psl2FieldAut F σ z) := by
      simp [MulAut.mul_apply]
    rw [hcz]
    constructor
    · intro h
      exact c.injective h
    · intro h
      have h' : psl2FieldAut F σ z = z := h
      rw [h']
  exact ⟨(E.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)⟩

theorem footeAbelianCore :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel S .PSL 2 p f → ∀ i : MulAut S, orderOf i = 2 →
        ∀ x y : ↥(pPrimeCore 2 ↥(MonoidHom.eqLocus i.toMonoidHom (MonoidHom.id S))),
          x * y = y * x := by
  intro S _ _ p f hp hp2 hf hS i hi
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := MonoidHom.eqLocus i.toMonoidHom (MonoidHom.id S)
  intro x y
  set g := autEquiv e i
  have hi2 : i ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hi])
  have hg2 : g * g = 1 := by
    rw [← map_mul, ← pow_two, hi2, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    have : i = 1 := (autEquiv e).injective (h.trans (map_one _).symm)
    rw [this, orderOf_one] at hi
    norm_num at hi
  have hoddc : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))
  have hodd_el : ∀ z : ↥(pPrimeCore 2 H), Odd (orderOf ((z : H) : S)) := by
    intro z
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hoddc (orderOf_dvd_natCard z)
  by_cases hr : g.right = 1
  ·
    have hgt : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hr
    have ht2 : g.left * g.left = 1 := by
      have := congrArg SemidirectProduct.left hg2
      simpa [hr] using this
    have ht1 : g.left ≠ 1 := by
      intro h
      apply hg1
      rw [hgt, h, map_one]
    have hcomm : ∀ s ∈ H, Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) * g.left =
        g.left * Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) := by
      intro s hs
      have h1 := (mem_eqLocus_iff_semilinear e i s).mp hs
      change semilinearAction F g (e s) = e s at h1
      rw [hgt, semilinearAction_inl] at h1
      have h1' := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h1
      rw [toPGL_pglAction] at h1'
      exact (mul_inv_eq_iff_eq_mul.mp h1').symm
    have hord : ∀ z : ↥(pPrimeCore 2 H),
        Odd (orderOf (Matrix.ProjectiveSpecialLinearGroup.toPGL (e ((z : H) : S)))) := by
      intro z
      rw [orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        MulEquiv.orderOf_eq]
      exact hodd_el z
    have key := pgl2_commute_of_odd h2 ht2 ht1 (hcomm _ (x : H).2) (hcomm _ (y : H).2)
      (hord x) (hord y)
    apply Subtype.ext
    apply Subtype.ext
    apply e.injective
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    simpa only [Subgroup.coe_mul, map_mul] using key
  ·
    obtain ⟨hσ, ⟨ρ⟩⟩ := eqLocus_equiv_fieldCent hodd e i hg2 hr
    set σ := g.right
    have hσσ : ∀ z, σ (σ z) = z := fun z => by
      have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
      have := congrArg (fun τ : F ≃+* F => τ z) h1
      simpa using this
    obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
    have hcore : pPrimeCore 2 ↥(fieldCent σ) = ⊥ := by
      rw [pPrimeCore_eq_bot_iff]
      intro K hKn hKc
      have hKodd : Odd (Nat.card (K.map (fieldCent σ).subtype)) := by
        rw [Subgroup.card_map_of_injective (fieldCent σ).subtype_injective]
        exact Nat.coprime_two_left.mp hKc
      have hb := eq_bot_of_odd_normal_fieldCent hK₀ h90 hσσ hcard hodd
        (N := K.map (fieldCent σ).subtype) (Subgroup.map_subtype_le K) (by
          rintro c' hc' _ ⟨k, hk, rfl⟩
          exact ⟨⟨c', hc'⟩ * k * ⟨c', hc'⟩⁻¹, hKn.conj_mem k hk _, rfl⟩) hKodd
      exact (Subgroup.map_eq_bot_iff_of_injective _ (fieldCent σ).subtype_injective).mp hb
    have hcoreH : pPrimeCore 2 ↥H = ⊥ := by
      have := pPrimeCore_map_iso 2 ρ
      rw [hcore] at this
      exact (Subgroup.map_eq_bot_iff_of_injective _ ρ.injective).mp this
    have hx1 : x = 1 := by
      have h : (x : H) ∈ (⊥ : Subgroup H) := by rw [← hcoreH]; exact x.2
      exact Subtype.ext (Subgroup.mem_bot.mp h)
    have hy1 : y = 1 := by
      have h : (y : H) ∈ (⊥ : Subgroup H) := by rw [← hcoreH]; exact y.2
      exact Subtype.ext (Subgroup.mem_bot.mp h)
    rw [hx1, hy1]

end CFSG.ComponentClassification.AutL2Facts
