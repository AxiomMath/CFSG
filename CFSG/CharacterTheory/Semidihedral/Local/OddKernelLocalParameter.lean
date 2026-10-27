module

public import CFSG.CharacterTheory.Semidihedral.Local.OddKernelLocalParameterSupport
public import CFSG.CharacterTheory.Semidihedral.Local.LayerCoverParameter

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Semidihedral.Principal
  CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Local.OddKernel

theorem actual_odd_kernel_preserves_local_parameter_and_regularity
    {G : Type} [Group G]
    [Fintype G] (n : ℕ) (hn : 4 ≤ n) (hG : ∀ U : Subgroup G, U.index ≠ 2) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (K : Subgroup G) [K.Normal]
    (hK : Odd (Nat.card K)) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    let π := QuotientGroup.mk' K
    let s₀ : G := fS (s n)
    let L := CFSG.generalizedFitting (Gamma t)
    let barL := CFSG.generalizedFitting (Gamma (π t))
    let c := Nat.card (Subgroup.centralizer ({t} : Set G))
    let d := Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({s₀} : Set G) : Subgroup G)
    let barc := Nat.card (Subgroup.centralizer ({π t} : Set (G ⧸ K)))
    let bard := Nat.card (Subgroup.centralizer ({π t} : Set (G ⧸ K)) ⊓
      Subgroup.centralizer ({π s₀} : Set (G ⧸ K)) : Subgroup (G ⧸ K))
    let reg : Prop :=
      3 * (padicValNat p c : ℤ) - 2 * padicValNat p d ≤ padicValNat p (Nat.card G)
    let barreg : Prop :=
      3 * (padicValNat p barc : ℤ) - 2 * padicValNat p bard ≤ padicValNat p (Nat.card (G ⧸ K))
    let e : ℤ := if p ^ f % 4 = 1 then 1 else -1
    (∀ U : Subgroup (G ⧸ K), U.index ≠ 2) ∧
    (∃ barS : Sylow 2 (G ⧸ K), (barS : Subgroup (G ⧸ K)) = (S : Subgroup G).map π ∧
      Function.Injective (π.comp (S : Subgroup G).subtype) ∧
      ∃ fbar : SemidihedralGroup n ≃* (barS : Subgroup (G ⧸ K)),
        ∀ x, (fbar x : G ⧸ K) = π (fS x)) ∧
    (∃ θ : Gamma t ≃* Gamma (π t),
      (∀ (x : C t) (hx : π x ∈ C (π t)), θ (kappa t x) = kappa (π t) ⟨π x, hx⟩) ∧
      L.map θ.toMonoidHom = barL) ∧
    IsSimpleGroup barL ∧ (∃ a b : barL, a * b ≠ b * a) ∧
    Subgroup.centralizer (barL : Set (Gamma (π t))) = ⊥ ∧ (∀ U : Sylow 2 barL, ¬ IsCyclic U) ∧
    CFSG.Assembly.LowTwoRank.StatedClassicalModel barL .PSL 2 p f ∧
    (reg ↔ barreg) ∧
    (reg ∨ barreg →
      (padicValNat p (Nat.card G) : ℤ) = 3 * padicValNat p c - 2 * padicValNat p d ∧
      (padicValNat p (Nat.card (G ⧸ K)) : ℤ) = 3 * padicValNat p barc - 2 * padicValNat p bard ∧
      ∀ (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
        (basis.representation principal).character = 1 →
      ∀ (localBasis : FiniteIrreducibleCharacterBasis (C t))
        (localPrincipal : localBasis.index),
        (localBasis.representation localPrincipal).character = 1 →
      ∀ (barBasis : FiniteIrreducibleCharacterBasis (G ⧸ K)) (barPrincipal : barBasis.index),
        (barBasis.representation barPrincipal).character = 1 →
      ∀ (barLocal : FiniteIrreducibleCharacterBasis (C (π t)))
        (barLocalPrincipal : barLocal.index),
        (barLocal.representation barLocalPrincipal).character = 1 →
      ∃ (χ₂ : basis.index) (barχ₂ : barBasis.index),
        IsRegularSecondPrincipal n basis ideal principal t localBasis localPrincipal s₀ p f χ₂ ∧
        IsRegularSecondPrincipal n barBasis ideal barPrincipal (π t) barLocal barLocalPrincipal
          (π s₀) p f barχ₂ ∧
        (basis.representation χ₂).character = (barBasis.representation barχ₂).character ∘ π ∧
        (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) =
          ((p ^ f : ℕ) : ℤ) ^ 2 - e * (p ^ f : ℕ) + 1) := by
  intro π s₀ L barL c d barc bard reg barreg e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hzt, ht2, hcent, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  have hGbar : ∀ U : Subgroup (G ⧸ K), U.index ≠ 2 := quotient_index_ne_two K hG
  have hSinj : Function.Injective (π.comp (S : Subgroup G).subtype) :=
    injective_mk_comp_subtype K hK S.isPGroup'
  let barS : Sylow 2 (G ⧸ K) := S.mapSurjective (QuotientGroup.mk'_surjective K)
  have hbarS : (barS : Subgroup (G ⧸ K)) = (S : Subgroup G).map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective K) S
  have hrange : (π.comp (S : Subgroup G).subtype).range = (barS : Subgroup (G ⧸ K)) := by
    rw [hbarS, MonoidHom.range_comp, Subgroup.range_subtype]
  let fbar : SemidihedralGroup n ≃* (barS : Subgroup (G ⧸ K)) :=
    fS.trans ((MonoidHom.ofInjective hSinj).trans (MulEquiv.subgroupCongr hrange))
  have hfbar : ∀ x, (fbar x : G ⧸ K) = π (fS x) := fun x => by
    simp [fbar, MonoidHom.ofInjective_apply]
  let θ := gammaEquiv K t hK ht2
  have hθ : ∀ (x : C t) (hx : π x ∈ C (π t)), θ (kappa t x) = kappa (π t) ⟨π x, hx⟩ :=
    fun x hx => rfl
  have hLθ : L.map θ.toMonoidHom = barL := generalizedFitting_map_of_mulEquiv θ hnonab hcentral
  let eL : L ≃* barL :=
    (L.equivMapOfInjective θ.toMonoidHom θ.injective).trans (MulEquiv.subgroupCongr hLθ)
  have hbarLsimple : IsSimpleGroup barL := eL.symm.isSimpleGroup
  have hbarnonab : ∃ a b : barL, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eL a, eL b, fun h => hab (eL.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hbarcentral : Subgroup.centralizer (barL : Set (Gamma (π t))) = ⊥ := by
    rw [← hLθ]
    exact centralizer_map_eq_bot_of_mulEquiv θ L hcentral
  have hbarnc : ∀ U : Sylow 2 barL, ¬ IsCyclic U := not_isCyclic_sylow_of_mulEquiv eL.symm hnc
  have hbarmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel barL .PSL 2 p f :=
    statedClassicalModel_PSL_of_mulEquiv eL.symm hmodel
  have hex := excess_eq_of_odd_kernel n hn hG S fS t ht K hK p
  simp only at hex
  have hregiff : reg ↔ barreg := by
    simp only [reg, barreg, c, d, barc, bard, π, s₀]
    constructor <;> intro h <;> linarith
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).2 _
  have hbart2 : orderOf (π t) = 2 := by
    have h := orderOf_injective _ hSinj ⟨t, htS⟩
    rw [Subgroup.orderOf_mk] at h
    exact h.trans ht2
  have hbarcent : (fbar (r n) : G ⧸ K) ^ (modulus n / 2) = π t := by
    rw [hfbar, ← map_pow, hcent]
  have hbars : (fbar (s n) : G ⧸ K) = π s₀ := hfbar (s n)
  have : IsSimpleGroup (CFSG.generalizedFitting (Gamma (π t))) := hbarLsimple
  have hvalG : ∀ (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
      (basis.representation principal).character = 1 →
      ∀ (localBasis : FiniteIrreducibleCharacterBasis (C t))
        (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 → reg →
      ∃ χ₂, IsRegularSecondPrincipal n basis ideal principal t localBasis localPrincipal s₀
        p f χ₂ := by
    intro basis principal hprincipal localBasis localPrincipal hlocalPrincipal hreg
    obtain ⟨F, hF, hFfin, ρ, hFcard, hρ, hρL, hρlin, hrest⟩ :=
      actual_nonsimple_layer_characteristic_valuation_degree_formulas n hn S fS hG t ht2 hnonab
        hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
        localPrincipal hlocalPrincipal fS hcent hreg
    obtain ⟨-, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg, hchar⟩ := hrest
    exact ⟨χ₂, F, hF, hFfin, ρ, hFcard, hρ, hρL, hρlin, δ₁, δ₂, δ₃, δ₄, χ₁, χ₃, χ₄, ψ, ν, hfam,
      hdeg, hchar⟩
  have hvalbarG : ∀ (basis : FiniteIrreducibleCharacterBasis (G ⧸ K)) (principal : basis.index),
      (basis.representation principal).character = 1 →
      ∀ (localBasis : FiniteIrreducibleCharacterBasis (C (π t)))
        (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 → barreg →
      ∃ χ₂, IsRegularSecondPrincipal n basis ideal principal (π t) localBasis localPrincipal
        (π s₀) p f χ₂ := by
    intro basis principal hprincipal localBasis localPrincipal hlocalPrincipal hreg
    obtain ⟨F, hF, hFfin, ρ, hFcard, hρ, hρL, hρlin, hrest⟩ :=
      actual_nonsimple_layer_characteristic_valuation_degree_formulas n hn barS fbar hGbar (π t)
        hbart2 hbarnonab hbarcentral hbarnc p f hp hpodd hf hbarmodel ideal basis principal
        hprincipal localBasis localPrincipal hlocalPrincipal fbar hbarcent hreg
    obtain ⟨-, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg, hchar⟩ := hrest
    exact ⟨χ₂, F, hF, hFfin, ρ, hFcard, hρ, hρL, hρlin, δ₁, δ₂, δ₃, δ₄, χ₁, χ₃, χ₄, ψ, ν, hfam,
      hdeg, hchar⟩
  refine ⟨hGbar, ⟨barS, hbarS, hSinj, fbar, hfbar⟩, ⟨θ, hθ, hLθ⟩, hbarLsimple, hbarnonab,
    hbarcentral, hbarnc, hbarmodel, hregiff, fun hor => ?_⟩
  have hreg : reg := hor.elim id hregiff.mpr
  have hbarreg : barreg := hregiff.mp hreg
  obtain ⟨basis0⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal0, hprincipal0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis0
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal0
  obtain ⟨local0⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨lprincipal0, hlprincipal0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible local0
    (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlprincipal0
  obtain ⟨χ₀, hχ₀⟩ := hvalG basis0 principal0 hprincipal0 local0 lprincipal0 hlprincipal0 hreg
  have heqG := isRegularSecondPrincipal_valuation hχ₀
  have heqbarG : (padicValNat p (Nat.card (G ⧸ K)) : ℤ) =
      3 * padicValNat p barc - 2 * padicValNat p bard := by
    simp only [barc, bard, π, s₀] at heqG ⊢
    linarith
  refine ⟨heqG, heqbarG, ?_⟩
  intro basis principal hprincipal localBasis localPrincipal hlocalPrincipal barBasis barPrincipal
    hbarPrincipal barLocal barLocalPrincipal hbarLocalPrincipal
  obtain ⟨χ₂, hχ₂⟩ := hvalG basis principal hprincipal localBasis localPrincipal
    hlocalPrincipal hreg
  obtain ⟨barχ₂, hbarχ₂⟩ := hvalbarG barBasis barPrincipal hbarPrincipal barLocal
    barLocalPrincipal hbarLocalPrincipal hbarreg
  obtain ⟨-, hdegG, huniqG⟩ := isRegularSecondPrincipal_spec hprincipal hp hpodd hf hχ₂
  obtain ⟨hmembar, hdegbar, -⟩ := isRegularSecondPrincipal_spec hbarPrincipal hp hpodd hf hbarχ₂
  have hker2 : ¬ 2 ∣ Nat.card (QuotientGroup.mk' K).ker := by
    rw [QuotientGroup.ker_mk', ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hK
  obtain ⟨hinfl, -, -, -⟩ := normal_prime_kernel_principal_block_inflation_of_surjective π
    (QuotientGroup.mk'_surjective K) basis ideal 2 hker2 barBasis principal hprincipal
    barPrincipal hbarPrincipal
  obtain ⟨l, hl⟩ := exists_inflated_label π (QuotientGroup.mk'_surjective K) basis barBasis barχ₂
  have hlB := (hinfl l).mpr ⟨barχ₂, hmembar, hl⟩
  have hldeg : Module.finrank ℂ (basis.representation l).vector =
      Module.finrank ℂ (barBasis.representation barχ₂).vector := by
    have h1 := congrFun hl 1
    simp only [Function.comp_apply, map_one, FiniteComplexRepresentation.character,
      Representation.char_one] at h1
    exact_mod_cast h1
  have hodd : Odd (((p ^ f : ℕ) : ℤ) ^ 2 - e * (p ^ f : ℕ) + 1) := by
    obtain ⟨m, hm⟩ : Odd (p ^ f) := hpodd.pow
    rw [hm]
    have he : e = 1 ∨ e = -1 := by
      simp only [e]
      split_ifs <;> simp
    rcases he with he | he <;> rw [he]
    · exact ⟨2 * m ^ 2 + m, by push_cast; ring⟩
    · exact ⟨2 * m ^ 2 + 3 * m + 1, by push_cast; ring⟩
  have hlodd : Odd (Module.finrank ℂ (basis.representation l).vector) := by
    rw [hldeg, ← Int.odd_coe_nat, hdegbar]
    exact hodd
  have hl2 : l = χ₂ := huniqG l hlB hlodd (by rw [hldeg]; exact hdegbar)
  refine ⟨χ₂, barχ₂, hχ₂, hbarχ₂, ?_, hdegG⟩
  rw [← hl2]
  exact hl

end CFSG.Semidihedral.Local
