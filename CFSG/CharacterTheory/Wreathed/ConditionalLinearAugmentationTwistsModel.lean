module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompatibleModelData
public import CFSG.CharacterTheory.Wreathed.ConditionalLinearAugmentationTwistsBlocks
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearCuspidalCharacters
public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacySplit
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockAtoms
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Wreathed.BrauerWong
public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseCuspidalFamily
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityDescriptions

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization

section Model

variable {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {F : Type} [Field F] [Finite F]
  {Sigma : Subgroup (F ≃+* F)} {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}
  {σ₀ : Sigma} {hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀} {ζm ζd : ℂ}
  {hζm : IsPrimitiveRoot ζm (2 ^ n)} {hζd : IsPrimitiveRoot ζd (Nat.card Sigma)}

local notation "W" => SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
  (wreathModulus_even hn) Sigma hSigma
local notation "H" => centralizerOddCoreQuotient n S e
local notation "χ" => linearCharacter F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
  Sigma hSigma σ₀ hgen ζm ζd hζm hζd

theorem compatibleModel_lam_formula {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) (r : Fin (2 ^ n))
    (v : Fin (Nat.card Sigma)) (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ) :
    lam r v (Ψ ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X
      (j : ZMod (2 * 2 ^ n)), σ₀ ^ k⟩) = ζm ^ (r.val * j) * ζd ^ (v.val * k) := by
  rw [hlam, Ψ.symm_apply_apply]
  exact linearCharacter_formula F b _ _ _ Sigma hSigma σ₀ hgen ζm ζd hζm hζd r v X j k

theorem compatibleModel_lam_eq_hom {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) (r : Fin (2 ^ n))
    (v : Fin (Nat.card Sigma)) :
    lam r v = ⇑(((Units.coeHom ℂ).comp (χ r v)).comp Ψ.symm.toMonoidHom) := by
  funext h
  rw [hlam]
  rfl

theorem compatibleModel_lam_mem_blocksIrr {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) (r : Fin (2 ^ n))
    (v : Fin (Nat.card Sigma)) : lam r v ∈ BlocksIrr H ∧ lam r v 1 = 1 := by
  rw [compatibleModel_lam_eq_hom hn hlam]
  exact ⟨CentralSL2.monoidHom_mem_blocksIrr _, map_one _⟩

theorem compatibleModel_lam_mul {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) (r : Fin (2 ^ n))
    (v : Fin (Nat.card Sigma)) (x y : H) : lam r v (x * y) = lam r v x * lam r v y := by
  rw [hlam, hlam, hlam, map_mul, map_mul, Units.val_mul]

theorem compatibleModel_lam_injective {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) :
    Function.Injective (fun rv : Fin (2 ^ n) × Fin (Nat.card Sigma) => lam rv.1 rv.2) := by
  intro rv rv' h
  apply linearCharacter_values_injective F b _ _ _ Sigma hSigma σ₀ hgen ζm ζd hζm hζd
  funext g
  have := congrFun h (Ψ g)
  simp only [hlam, MulEquiv.symm_apply_apply] at this
  exact this

theorem compatibleModel_lam_exhaustive {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) (hb : ¬ IsSquare b) {θ : H → ℂ}
    (hθ : θ ∈ BlocksIrr H) (h1 : θ 1 = 1) : ∃ r v, θ = lam r v := by
  have hθW : (θ ∘ Ψ.toMonoidHom) ∈ BlocksIrr W :=
    Semidihedral.Principal.comp_mem_blocksIrr Ψ.toMonoidHom Ψ.surjective hθ
  have h1W : (θ ∘ Ψ.toMonoidHom) 1 = 1 := by
    change θ (Ψ 1) = 1
    rw [map_one, h1]
  let φ := CentralSL2.degreeOneHom hθW h1W
  obtain ⟨r, v, hrv⟩ := linearCharacter_exhaustive F b _ _ _ Sigma hSigma σ₀ hgen ζm ζd hζm hζd
    (nonsquare_ne_one F b hb) φ.toHomUnits
  refine ⟨r, v, funext fun h => ?_⟩
  rw [hlam, hrv]
  change θ h = θ (Ψ (Ψ.symm h))
  rw [MulEquiv.apply_symm_apply]

theorem compatibleModel_augmentation [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1) (g : W) :
    ΦH (Ψ g) = fixedPointCount W (Omega F) g - 1 := by
  rw [hΦ]
  exact hdata.augmentation_comp g

theorem compatibleModel_augmentation_symm [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1) (h : H) :
    ΦH h = fixedPointCount W (Omega F) (Ψ.symm h) - 1 := by
  rw [← compatibleModel_augmentation hn hdata hΦ, MulEquiv.apply_symm_apply]

theorem compatibleModel_xi [Finite G] {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {p f : ℕ}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    {lam Ξ : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ))
    (hΞ : ∀ r v h, Ξ r v h = lam r v h * ΦH h) :
    (∀ r v, Ξ r v ∈ BlocksIrr H ∧ Ξ r v 1 = Nat.card F) ∧
      Function.Injective (fun rv : Fin (2 ^ n) × Fin (Nat.card Sigma) => Ξ rv.1 rv.2) := by
  obtain ⟨hirr, hinj, -, -⟩ := CentralSL2.augmentation_twists F b _ _ _ Sigma hSigma
    (nonsquare_ne_one F b hdata.nonsquare) σ₀ hgen ζm ζd hζm hζd
  have hΞeq : ∀ r v, Ξ r v = (fun g : W => (χ r v g : ℂ) *
      (fixedPointCount W (Omega F) g - 1)) ∘ Ψ.symm.toMonoidHom := by
    intro r v
    funext h
    rw [hΞ, hlam, compatibleModel_augmentation_symm hn hdata hΦ]
    rfl
  refine ⟨fun r v => ⟨?_, ?_⟩, fun rv rv' h => hinj ?_⟩
  · rw [hΞeq]
    exact Semidihedral.Principal.comp_mem_blocksIrr _ Ψ.symm.surjective (hirr r v).1
  · rw [hΞeq]
    change _ * _ = _
    rw [map_one]
    exact (hirr r v).2
  · funext g
    have := congrFun h (Ψ g)
    simp only [hΞeq, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] at this
    exact this

theorem compatibleModel_unipotent [Finite G] {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {p f : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) :
    let u : H := Ψ ⟨specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      (CentralSL2.upperSL F 1), 1⟩
    Odd (orderOf u) ∧ ΦH u = 0 ∧ ∀ r v, lam r v u = 1 := by
  intro u
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  set uW : W := SemidirectProduct.inl (CentralSL2.unipotentElement F b (2 ^ n)
    (wreathModulus_pos n) (wreathModulus_even hn) 1) with huW
  have hu : u = Ψ uW := rfl
  refine ⟨?_, ?_, fun r v => ?_⟩
  · rw [hu, MulEquiv.orderOf_eq]
    have hpow : uW ^ p = 1 := by
      rw [huW, ← map_pow, CentralSL2.unipotentElement_pow, mul_one, CharP.cast_eq_zero,
        CentralSL2.unipotentElement_zero, map_one]
    exact (hp.odd_of_ne_two hpodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · rw [hu, compatibleModel_augmentation hn hdata hΦ, huW, CentralSL2.fixedPointCount_inl]
    have h1 := CentralSL2.card_fixed_unipotent (F := F) (b := b) (hm := wreathModulus_pos n)
      (heven := wreathModulus_even hn) (Subgroup.one_mem _) (one_ne_zero (α := F))
    rw [one_mul] at h1
    rw [h1, Nat.cast_one, sub_self]
  · have h := compatibleModel_lam_formula hn hlam r v (CentralSL2.upperSL F 1) 0 0
    simp only [Nat.cast_zero, pow_zero, mul_zero, mul_one] at h
    exact h

theorem compatibleModel_field [Finite G] {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {p f : ℕ} (hp : p.Prime)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) :
    let z : H := Ψ (SemidirectProduct.inr σ₀)
    orderOf z = Nat.card Sigma ∧ Odd (orderOf z) ∧
      ΦH z = (p : ℂ) ^ (f / Nat.card Sigma) ∧ ΦH z ≠ 0 ∧
      ∀ r v, lam r v z = ζd ^ v.val := by
  intro z
  have hord : orderOf z = Nat.card Sigma := by
    rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inr_injective,
      orderOf_eq_card_of_forall_mem_zpowers hgen]
  have hΦz : ΦH z = (p : ℂ) ^ (f / Nat.card Sigma) := by
    change ΦH (Ψ ⟨1, σ₀⟩) = _
    rw [compatibleModel_augmentation hn hdata hΦ, CentralSL2.fixedPointCount_field F b _ _ _
      Sigma hSigma hp hdata.card σ₀, orderOf_eq_card_of_forall_mem_zpowers hgen]
    ring
  refine ⟨hord, hord ▸ hdata.sigma_odd, hΦz, ?_, fun r v => ?_⟩
  · rw [hΦz]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  · rw [hlam, MulEquiv.symm_apply_apply]
    exact linearCharacter_sigma0 F b _ _ _ Sigma hSigma σ₀ hgen ζm ζd hζm hζd r v

theorem compatibleModel_lam_odd {lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ)) (r : Fin (2 ^ n))
    (v : Fin (Nat.card Sigma)) (hv : v.val = 0) {y : H} (hy : Odd (orderOf y)) :
    lam r v y = 1 := by
  set g := Ψ.symm y with hg
  have hgodd : Odd (orderOf g) := by rw [hg, MulEquiv.orderOf_eq]; exact hy
  obtain ⟨w, σ⟩ := g
  obtain ⟨X, j, rfl⟩ := CentralSL2.quotientClass_surjective F b (2 ^ n) (wreathModulus_pos n)
    (wreathModulus_even hn) w
  obtain ⟨k, hk⟩ : ∃ k : ℕ, σ₀ ^ k = σ :=
    (Submonoid.mem_powers_iff σ σ₀).mp (mem_powers_iff_mem_zpowers.mpr (hgen σ))
  have hval : lam r v y = ζm ^ (r.val * j.val) := by
    rw [hlam, ← hg, ← hk, linearCharacter_residue_formula, hv, zero_mul, pow_zero, mul_one]
  have hm : (lam r v y) ^ (2 ^ n) = 1 := by
    rw [hval, ← pow_mul, mul_comm, pow_mul, hζm.pow_eq_one, one_pow]
  have hord : (lam r v y) ^ (orderOf y) = 1 := by
    have hmul : ∀ k : ℕ, lam r v (y ^ k) = (lam r v y) ^ k := by
      intro k
      induction k with
      | zero =>
        rw [pow_zero, pow_zero]
        exact (compatibleModel_lam_mem_blocksIrr hn hlam r v).2
      | succ k ih => rw [pow_succ, compatibleModel_lam_mul hn hlam, ih, pow_succ]
    rw [← hmul, pow_orderOf_eq_one]
    exact (compatibleModel_lam_mem_blocksIrr hn hlam r v).2
  have hcop : Nat.Coprime (2 ^ n) (orderOf y) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hy)
  have := pow_gcd_eq_one.mpr ⟨hm, hord⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem compatibleModel_complete [Finite G] {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {p f : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    {lam Ξ : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (χ r v (Ψ.symm h) : ℂ))
    (hΞ : ∀ r v h, Ξ r v h = lam r v h * ΦH h) {θ : H → ℂ} (hθ : θ ∈ BlocksIrr H) :
    (∃ r v, θ = lam r v) ∨ (∃ r v, θ = Ξ r v) ∨
      ∃ u : ℕ, 0 < u ∧ u ∣ Nat.card Sigma ∧
        (θ 1 = (u : ℂ) * ((Nat.card F : ℂ) + 1) ∨ θ 1 = (u : ℂ) * ((Nat.card F : ℂ) - 1)) := by
  let : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  have hθW : θ ∘ Ψ.toMonoidHom ∈ BlocksIrr W :=
    Semidihedral.Principal.comp_mem_blocksIrr _ Ψ.surjective hθ
  have hθ1 : (θ ∘ Ψ.toMonoidHom) 1 = θ 1 := by
    change θ (Ψ 1) = θ 1
    rw [map_one]
  have hback : ∀ φ : W → ℂ, θ ∘ Ψ.toMonoidHom = φ → θ = φ ∘ Ψ.symm.toMonoidHom := by
    intro φ hφ
    rw [← hφ]
    funext h
    change θ h = θ (Ψ (Ψ.symm h))
    rw [MulEquiv.apply_symm_apply]
  obtain ⟨hcomplete, -⟩ := CentralSL2.semilinear_complete_family (hm := wreathModulus_pos n)
    (heven := wreathModulus_even hn) hSigma σ₀ hgen ζm ζd hζm hζd (hp.odd_of_ne_two hpodd)
    hdata.nonsquare hdata.sigma_odd
  rw [hcomplete] at hθW
  rcases hθW with ((h1 | h2) | h3) | h4
  · obtain ⟨⟨r, v⟩, hrv⟩ := h1
    refine Or.inl ⟨r, v, ?_⟩
    rw [hback _ hrv.symm]
    funext h
    rw [hlam]
    rfl
  · obtain ⟨⟨r, v⟩, hrv⟩ := h2
    refine Or.inr (Or.inl ⟨r, v, ?_⟩)
    rw [hback _ hrv.symm]
    funext h
    rw [hΞ, hlam, compatibleModel_augmentation_symm hn hdata hΦ]
    rfl
  · obtain ⟨P, ρ', hP, hPρ⟩ := h3
    have hdeg := ((CentralSL2.principal_clifford (hm := wreathModulus_pos n)
      (heven := wreathModulus_even hn) hSigma hdata.nonsquare hdata.sigma_odd hP).1 ρ').2
    refine Or.inr (Or.inr ⟨(CentralSL2.parameterStabilizer hSigma P).index,
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, Subgroup.index_dvd_card _,
      Or.inl ?_⟩)
    rw [← hθ1, hPρ, hdeg]
  · obtain ⟨θ', hθ', hdeg⟩ := CentralSL2.exists_degree_of_mem_aboveFamily hSigma
      (fun θ hθ => hθ.1) h4
    refine Or.inr (Or.inr ⟨(CentralSL2.twistStabilizer hSigma θ').index,
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, Subgroup.index_dvd_card _,
      Or.inr ?_⟩)
    rw [← hθ1, hdeg, hθ'.2]

end Model

end CFSG.Wreathed
