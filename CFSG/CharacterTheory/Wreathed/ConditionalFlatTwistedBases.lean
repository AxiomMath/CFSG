module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesRoot
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesGeneric
public import CFSG.CharacterTheory.Wreathed.FlatWreathedBlock

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.FlatTwistedBases CFSG.Wreathed.AdaptedBaseFusion

theorem conditional_flat_local_twisted_regular_bases
    {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (B : basis.index) (hflat : FlatWreathedBlock basis ideal S e B)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θB : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θB θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let N : Subgroup G := involutionCentralizer n S e
    let E : Subgroup G := BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G))
    let T : Subgroup G := Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
      wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)}
    let y : G := wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))
    let IsExtension : (N →* ℂˣ) → Prop := fun lam =>
      (∀ (v : N) (z : E), (v : G) = z → (lam v : ℂ) = (eb.representation θB).character z) ∧
      (∀ v : N, (v : G) ∈ (S : Subgroup G) → lam v = 1) ∧
      ∀ c c' : N, (c : G) ∈ Subgroup.centralizer (T : Set G) → (c' : G) = η⁻¹ * c * η →
        lam c' = lam c
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (sigmaGroup : Subgroup (F ≃+* F))
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
      Nat.card F = p ^ f ∧ Odd (Nat.card sigmaGroup) ∧ Function.Injective ρ ∧
        (centralizerSimpleLayer n hn S e).map ρ = specialLayer F ∧
        ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup) ∧
    (∃ lam, IsExtension lam) ∧
    ∀ lam, IsExtension lam →
      (∀ (u : G) (hu : IsPGroup 2 (Subgroup.zpowers u)) (hxu : x ∈ Subgroup.zpowers u),
        Subgroup.centralizer (Subgroup.zpowers u : Set G) = Subgroup.centralizer {u} ∧
        Subgroup.centralizer (Subgroup.zpowers u : Set G) ≤ N ∧
        ∀ (localBasis : FiniteIrreducibleCharacterBasis
          (Subgroup.centralizer (Subgroup.zpowers u : Set G))),
          (∃ ℓ : localBasis.index, ∀ c, (localBasis.representation ℓ).character c =
            lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu) c)) ∧
          ∀ ℓ principal : localBasis.index,
            (∀ c, (localBasis.representation ℓ).character c =
              lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu) c)) →
            (localBasis.representation principal).character = 1 →
            brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu
                (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
                (Subgroup.centralizer_le_normalizer _) localBasis ℓ =
              centralCharacterResidueHom basis ideal B ∧
            (∀ β, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu
                (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
                (Subgroup.centralizer_le_normalizer _) localBasis β =
                  centralCharacterResidueHom basis ideal B →
              sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β ℓ) ∧
            ∀ θ', θ' ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ ↔
              ∃ χ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) principal,
                ∀ c, (localBasis.representation θ').character c =
                  (lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu)
                    c) : ℂ) * (localBasis.representation χ).character c) ∧
      (∀ (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
        Nat.card F = p ^ f → Odd (Nat.card sigmaGroup) → Function.Injective ρ →
        (centralizerSimpleLayer n hn S e).map ρ = specialLayer F →
        ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup →
        let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
          (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
            Equiv.Perm (Omega F)) x = x} : ℂ) - 1
        let ΦN : N → ℂ := fun v => ΦH (centralizerOddCoreMap n S e v)
        let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
        let M : Matrix (Fin 2) (Fin 2) ℤ := (2 ^ n : ℤ) • !![4, -2; -2, ((2 ^ n / 2 + 1 : ℕ) : ℤ)]
        (∀ (basisN : FiniteIrreducibleCharacterBasis N) (ℓ : basisN.index),
          (∀ v, (basisN.representation ℓ).character v = lam v) →
          (∀ principal : basisN.index, (basisN.representation principal).character = 1 →
            ∀ θ', θ' ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) ℓ ↔
              ∃ χ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) principal,
                ∀ v, (basisN.representation θ').character v =
                  (lam v : ℂ) * (basisN.representation χ).character v) ∧
          TwistedRegularIntegralBasisData basisN ideal ℓ (fun v => (lam v : ℂ)) ΦN ε M) ∧
        (∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
          (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
          (ℓ : basisC.index),
          (∀ c, (basisC.representation ℓ).character c =
            lam (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c)) →
          (∀ principal : basisC.index, (basisC.representation principal).character = 1 →
            ∀ θ', θ' ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) ℓ ↔
              ∃ χ ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principal,
                ∀ c, (basisC.representation θ').character c =
                  (lam (Subgroup.inclusion
                    (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c) : ℂ) *
                    (basisC.representation χ).character c) ∧
          TwistedRegularIntegralBasisData basisC ideal ℓ
            (fun c => (lam (Subgroup.inclusion
              (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c) : ℂ))
            (fun c => ΦN (Subgroup.inclusion
              (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c)) ε M) ∧
        (∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j) (c : centralSylowPowerCentralizer n S e j)
          (v : N), (c : G) = v →
          (lam (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c) :
            ℂ) = lam v ∧
          ΦN (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c) =
            ΦN v) ∧
        ∀ j : ℤ, Subgroup.centralizer {wreathModelHom S e (Original.a (2 ^ n))} ≤
          centralSylowPowerCentralizer n S e j) ∧
      (orderOf y = 2 * 2 ^ n ∧ y ^ 2 = wreathModelHom S e (Original.a (2 ^ n)) ∧
        y ^ (2 ^ n) = x ∧
        (∀ c : Subgroup.centralizer ({y} : Set G),
          c ∈ CFSG.oddCore (Subgroup.centralizer ({y} : Set G)) ↔ Odd (orderOf (c : G))) ∧
        (CFSG.oddCore (Subgroup.centralizer ({y} : Set G))).index = 2 * 2 ^ n ∧
        (∃ Ey : CFSG.oddCore (Subgroup.centralizer ({y} : Set G)) × Subgroup.zpowers y ≃*
            Subgroup.centralizer ({y} : Set G),
          ∀ k z, (Ey (k, z) : G) = ((k : Subgroup.centralizer ({y} : Set G)) : G) * (z : G)) ∧
        (∀ h : ℤ, Odd h → Subgroup.centralizer ({y ^ h} : Set G) =
          Subgroup.centralizer ({y} : Set G)) ∧
        ∀ (h : ℤ) (hh : Odd h) (localBasis : FiniteIrreducibleCharacterBasis
          (Subgroup.centralizer (Subgroup.zpowers (y ^ h) : Set G))) (ℓ : localBasis.index),
          (∀ c, (localBasis.representation ℓ).character c = lam (Subgroup.inclusion
            (centralizer_zpowers_le_involutionCentralizer S e (root_zpow_involution S e hn hh))
              c)) →
          SingletonTwistedBasisData localBasis ideal ℓ (fun c => (lam (Subgroup.inclusion
            (centralizer_zpowers_le_involutionCentralizer S e (root_zpow_involution S e hn hh))
              c) : ℂ)) (2 * 2 ^ n)) ∧
      ∀ (σ υ g : G) (hA : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
        (wreathModelHom S e (Original.z (2 ^ n))) σ υ g),
        (∀ (u : modelBase S e), u ∉ hA.exc → ∀ (hxu : x ∈ Subgroup.zpowers (u : G))
          (localBasis : FiniteIrreducibleCharacterBasis
            (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G))) (ℓ : localBasis.index),
          (∀ c, (localBasis.representation ℓ).character c =
            lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu) c)) →
          SingletonTwistedBasisData localBasis ideal ℓ (fun c => (lam (Subgroup.inclusion
            (centralizer_zpowers_le_involutionCentralizer S e hxu) c) : ℂ)) ((2 ^ n) ^ 2)) ∧
        ∀ u : modelBase S e, u ∉ hA.exc → ∃ u' : modelBase S e, u' ∉ hA.exc ∧
          x ∈ Subgroup.zpowers (u' : G) ∧ IsConj (u : G) (u' : G) := by
  intro x N E T y IsExtension
  let _ : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := centralizerOddCoreQuotient n S e)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisH
  have hpower := fun (basisN : FiniteIrreducibleCharacterBasis N) (principalN : basisN.index)
      (hprincipalN : (basisN.representation principalN).character = 1) =>
    conditional_actual_central_power_principal_regular_integral_bases.{0} hnonab n hn S e hfour p f
      hp hpodd hf hmodel ideal basisH principalH hprincipalH basisN principalN hprincipalN
  obtain ⟨basisN₀⟩ := finiteIrreducibleCharacterBasis_exists (G := N)
  obtain ⟨principalN₀, hprincipalN₀⟩ :=
    finiteIrreducibleCharacterBasis_exists_principal_label basisN₀
  obtain ⟨d, hd⟩ :=
    (BaseFourCentralizerStructure.sylow_and_base_four_group_centralizer_structure n hn S
      e).centralizer_direct
  let θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ := fun c =>
    (eb.representation θB).character (d.symm c).2
  have hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G) (w : E),
      z ∈ Subgroup.zpowers (wreathModelHom S e (Original.a (2 ^ n))) → (c : G) = z * w →
        θt c = (eb.representation θB).character w := by
    intro c z w hz hc
    rw [← BrauerWong.modelCenter_eq_zpowers S e] at hz
    have hdc : d.symm c = (⟨z, hz⟩, w) := by
      apply d.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hd]
      exact hc
    change (eb.representation θB).character (d.symm c).2 = _
    rw [hdc]
  obtain ⟨ψ, hψ⟩ := hflat.exists_family hn eb θB nb θhat hθ hB θt hθt
  refine ⟨(hpower basisN₀ principalN₀ hprincipalN₀).1, ?_, ?_⟩
  · exact exists_flat_extension S e hnonab hn hη _ θt hθt hψ
  intro lam hlam
  obtain ⟨h1, h2, h3⟩ := hlam
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro u hu hxu
    obtain ⟨hC, hlocal⟩ := flat_local_block S e hnonab hn basis ideal B eb θB nb θhat hθ hB θt
      hθt hη hord lam h1 h2 h3 u hu hxu
    exact ⟨hC, centralizer_zpowers_le_involutionCentralizer S e hxu, hlocal⟩
  ·
    intro F _ _ sigmaGroup ρ hcard hodd hρ hlayer hrange ΦH ΦN ε M
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro basisN ℓ hℓ
      obtain ⟨principalN, hprincipalN⟩ :=
        finiteIrreducibleCharacterBasis_exists_principal_label basisN
      obtain ⟨-, hNdata, -, -⟩ :=
        (hpower basisN principalN hprincipalN).2 F sigmaGroup ρ hcard hodd hρ hlayer hrange
      exact ⟨fun principal hprincipal => CompatibleFamily.linear_block_eq_twist_principal basisN
        ideal lam ℓ principal hℓ hprincipal, twistedRegularIntegralBasisData_of_principal basisN
        ideal lam ℓ principalN hℓ hprincipalN hNdata⟩
    · intro j hj basisC ℓ hℓ
      obtain ⟨principalC, hprincipalC⟩ :=
        finiteIrreducibleCharacterBasis_exists_principal_label basisC
      obtain ⟨-, -, -, hpowers⟩ :=
        (hpower basisN₀ principalN₀ hprincipalN₀).2 F sigmaGroup ρ hcard hodd hρ hlayer hrange
      obtain ⟨-, hCdata, -⟩ := hpowers j hj basisC principalC hprincipalC
      exact ⟨fun principal hprincipal => CompatibleFamily.linear_block_eq_twist_principal basisC
        ideal (lam.comp (Subgroup.inclusion
          (centralizer_zpow_le_involutionCentralizer n hn S e j hj))) ℓ principal hℓ hprincipal,
        twistedRegularIntegralBasisData_of_principal basisC ideal
          (lam.comp (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj)))
          ℓ principalC hℓ hprincipalC hCdata⟩
    · intro j hj c v hcv
      have hcv' : Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c =
          v := Subtype.ext hcv
      rw [hcv']
      exact ⟨rfl, rfl⟩
    · intro j c hc
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      exact (Commute.zpow_right (show Commute c (wreathModelHom S e (Original.a (2 ^ n))) from
        hc) j).eq
  ·
    obtain ⟨hyord, hysq, hym, hmem, hindex, hE, hcent⟩ := root_centralizer_structure S e hn
    exact ⟨hyord, hysq, hym, hmem, hindex, hE, hcent,
      fun h hh localBasis ℓ hℓ => root_singleton_basis S e hn ideal lam hh localBasis ℓ hℓ⟩
  ·
    intro σ υ g hA
    exact ⟨fun u hu hxu localBasis ℓ hℓ =>
      generic_singleton_basis hA hn ideal lam hu hxu localBasis ℓ hℓ,
      fun u hu => exists_generic_representative hA hnonab hn hu⟩

end CFSG.Wreathed
