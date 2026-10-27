module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderLocalHyp
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderSix
public import CFSG.CharacterTheory.BrauerLinearThree.LayerOrder
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderGroup
public import CFSG.CharacterTheory.Wreathed.ConditionalExactOrder

public section

open scoped Classical

namespace CFSG.Wreathed.BrauerWreathedOrder

open Matrix CFSG CFSG.TwoRankLowerBound.Helpers CFSG.DesarguesianPlanes CFSG.BrauerLinearThree
  CFSG.Wreathed.BrauerWong

theorem card_centralizer_inf_conj {G : Type} [Group G] {J t h : G} (hh : J * h = h * J) :
    Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({h * t * h⁻¹} : Set G) : Subgroup G) =
      Nat.card (Subgroup.centralizer ({J} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :
        Subgroup G) := by
  have hhJ : Commute h J := hh.symm
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨h⁻¹ * x * h, ?_⟩
      invFun := fun y => ⟨h * y * h⁻¹, ?_⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }
  · obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hx1 hx2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩ <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · exact ((hhJ.inv_left.mul_left hx1).mul_left hhJ).eq
    · calc h⁻¹ * x * h * t = h⁻¹ * (x * (h * t * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * t * h⁻¹) * x) * h := by rw [hx2]
        _ = t * (h⁻¹ * x * h) := by group
  · obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hy1 hy2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩ <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · exact ((hhJ.mul_left hy1).mul_left hhJ.inv_left).eq
    · calc h * y * h⁻¹ * (h * t * h⁻¹) = h * (y * t) * h⁻¹ := by group
        _ = h * (t * y) * h⁻¹ := by rw [hy2]
        _ = h * t * h⁻¹ * (h * y * h⁻¹) := by group

theorem brauer_wreathed_type_one_principal_block
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (S₁ S₂ T : G)
    (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1))
    (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
    (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂) :
    let A := S₁⁻¹ * S₂⁻¹
    let J := A ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let S₀ := Subgroup.closure {S₁, S₂}
    let D := Subgroup.closure {J, J₁}
    let c : Set G → ℕ := fun X => Nat.card (Subgroup.centralizer X)
    let idx := (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G))
    let caseA : Prop := ∃ g ∈ Subgroup.centralizer {J}, g⁻¹ * T * g = J₁
    idx = 6 → caseA →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F % 4 = 1 →
    ∀ (L : Subgroup (GL (Fin 2) F)) [L.Normal],
      (∀ x ∈ L, ∃ a : F, (x : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a) →
      Odd (Nat.card L) →
      Nonempty (Subgroup.centralizer {J} ≃* GL (Fin 2) F ⧸ L) →
    let q : ℕ := Fintype.card F
    Nat.card G * (c (D : Set G) ^ 2 * (q + 1) ^ 2) = c {J} ^ 3 * (q ^ 2 + q + 1) ∧
    ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
      [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
      (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
      (basis.representation principal).character = 1 →
      ∃ χ : Fin 6 → basis.index,
        (∀ i, χ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
        χ 0 = principal ∧
        (basis.representation (χ 0)).character 1 = 1 ∧
        (basis.representation (χ 1)).character 1 = (q : ℂ) ^ 3 ∧
        (basis.representation (χ 2)).character 1 = (q : ℂ) * ((q : ℂ) ^ 2 + q + 1) ∧
        (basis.representation (χ 3)).character 1 = (q : ℂ) ^ 2 + q + 1 ∧
        (basis.representation (χ 4)).character 1 = (q : ℂ) ^ 3 - 1 ∧
        (basis.representation (χ 5)).character 1 = ((q : ℂ) + 1) * ((q : ℂ) ^ 2 + q + 1) ∧
        ∀ g : G, Odd (orderOf g) →
          -1 + (basis.representation (χ 1)).character g =
              (basis.representation (χ 2)).character g -
                (basis.representation (χ 3)).character g ∧
            (basis.representation (χ 2)).character g -
                (basis.representation (χ 3)).character g =
              (basis.representation (χ 4)).character g ∧
            (basis.representation (χ 2)).character g + (basis.representation (χ 3)).character g =
              (basis.representation (χ 5)).character g := by
  intro A J J₁ S₀ D c idx caseA h6 hA F _ _ hq4 L _ hLsc hLodd hiso q
  have hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T :=
    ⟨hgen, hcard, hS₁, hS₂, hT, hcomm, hconj⟩
  have hn1 : 1 ≤ n := by omega
  set e := hW.equiv hn1 with he
  have hJx : wreathModelHom S e (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁x : wreathModelHom S e (Original.x2 (2 ^ n)) = J₁ := hW.modelHom_x2 hn1
  have hB : modelBase S e = S₀ := hW.modelBase_eq hn1
  obtain ⟨φ⟩ := hiso
  have hcentJ : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) =
      Subgroup.centralizer {J} := by rw [hJx]
  let φx := (MulEquiv.subgroupCongr hcentJ).trans φ
  have hqN : Nat.card F % 4 = 1 := by rwa [Nat.card_eq_fintype_card]
  have h2 : (2 : F) ≠ 0 := by
    intro h20
    have hdvd : ringChar F ∣ 2 := ringChar.dvd (by exact_mod_cast h20)
    have hchar : ringChar F = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h (CharP.ringChar_ne_one)
      · exact h
    have := FiniteField.even_card_of_char_two hchar
    omega
  have hZ : L ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F := by
    intro x hx
    obtain ⟨a, ha⟩ := hLsc x hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hdet := (x.isUnit.map Matrix.detMonoidHom).ne_zero
      apply hdet
      change (x : Matrix (Fin 2) (Fin 2) F).det = 0
      rw [ha]
      simp
    exact ⟨Units.mk0 a ha0, Units.ext (by rw [GeneralLinearGroup.coe_scalar, ha]; rfl)⟩
  obtain ⟨f, hp, hpf⟩ := FiniteField.card F (ringChar F)
  set p := ringChar F with hpdef
  have hcardpf : Nat.card F = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hpf]
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hpodd : p ≠ 2 := by
    intro hp2
    have := FiniteField.even_card_of_char_two hp2
    omega
  have hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) := by
    rcases base_relIndex_cases n hn S e with h2' | ⟨-, h⟩
    · rw [hB] at h2'
      exact absurd (h2'.symm.trans h6) (by norm_num)
    · exact h
  have hinv := case_one_a_all_involutions_conjugate n hn S S₁ S₂ T hW h6 hA
  have hno2 := case_one_a_no_index_two n hn S S₁ S₂ T hW h6 hA
  have hloc : ConditionalLocalHyp n hn S e p f :=
    conditionalLocalHyp_of_linear n hn S e φx hZ hLodd h2 hqN p f hp hf hcardpf hbase hinv hno2
  refine ⟨?_, fun ideal _ _ basis principal hprincipal =>
    six_principal_characters_of_localHyp n hn S e p f hp hpodd hf hloc hpf.symm hq4 ideal basis
      principal hprincipal⟩
  have hJord : orderOf J = 2 := hJx ▸ orderOf_modelHom_x (S := S) (e := e) hn
  have hq5 := five_le_card hqN
  have hq3 : 3 ≤ Nat.card F := by omega
  have hcJ := card_centralizer_J φ
  have hJ₁S : J₁ ∈ (S : Subgroup G) := hJ₁x ▸ wreathModelHom_mem S e _
  have hJJ₁ : J * J₁ = J₁ * J := by
    have h := modelHom_x_central S e hn hJ₁S
    rw [hJx] at h
    calc J * J₁ = J₁ * (J₁⁻¹ * J * J₁) := by group
      _ = J₁ * J := by rw [h]
  have hJ₁ord : orderOf J₁ = 2 := by
    rw [← hJ₁x, orderOf_injective _ (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.2.1
  have hJ₁2 : J₁ * J₁ = 1 := by rw [← sq, ← hJ₁ord, pow_orderOf_eq_one]
  have hJ₁1 : J₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hJ₁ord
    exact absurd hJ₁ord (by norm_num)
  have hJ₁J : J₁ ≠ J := fun h => modelHom_x_ne_x2 S e hn1 (hJx.trans (h.symm.trans hJ₁x.symm))
  obtain ⟨h, hhJ, hh⟩ := exists_conj_invJ₁ φ hZ hLodd h2 hJord hJJ₁ hJ₁2 hJ₁1 hJ₁J
  have hcD : Nat.card (Subgroup.centralizer (D : Set G)) * Nat.card L =
      (Nat.card F - 1) ^ 2 := by
    rw [Subgroup.centralizer_closure, centralizer_pair_eq, ← hh, card_centralizer_inf_conj hhJ]
    exact card_centralizer_inf_invJ₁ φ hZ hLodd h2
  have hl : 0 < Nat.card L := Nat.card_pos
  have hcJD : c {J} = Nat.card F * (Nat.card F + 1) * c (D : Set G) := by
    apply Nat.eq_of_mul_eq_mul_right hl
    change Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card L =
      Nat.card F * (Nat.card F + 1) * Nat.card (Subgroup.centralizer (D : Set G)) * Nat.card L
    rw [hcJ, mul_assoc _ (Nat.card (Subgroup.centralizer (D : Set G))), hcD]
    ring
  let _ : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  obtain ⟨F', _, _, Sigma, b, hSigma, ρ, Ψ, hdata⟩ := hloc.modelData
  obtain ⟨-, -, ⟨y, hy2, hyπ⟩, hall⟩ :=
    (ConditionalExactOrder.conditional_exact_group_order_with_original_odd_factors_of_localHyp n
      hn S e p f hp hpodd hf hloc).2 F' Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, -, hidx⟩ := hall y hy2 hyπ
  have hR : (CFSG.Wreathed.OddNormalQuotientInvolutions.kernelCentralizer
      (centralizerOddCore n S e) y).index = 1 := by
    rw [Subgroup.index_eq_one, CFSG.Wreathed.OddNormalQuotientInvolutions.kernelCentralizer,
      Subgroup.subgroupOf_eq_top]
    intro r hr
    obtain ⟨A, rfl⟩ := centralizerHom_surjective φx r
    obtain ⟨a, -, rfl⟩ := (centralizerHom_mem_oddCore_iff φx hZ hLodd h2 hq3 A).mp hr
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    obtain ⟨B, hB'⟩ := centralizerHom_surjective φx y
    rw [← hB']
    change centralizerHom φx _ * centralizerHom φx B = centralizerHom φx B * centralizerHom φx _
    rw [← map_mul, ← map_mul, (scalar_commute a B).eq]
  have hF' : Nat.card F' = q := hdata.card.trans (hpf.symm)
  have hq4' : q % 4 = 1 := hq4
  simp only [hR, hF', hq4', ↓reduceIte] at hidx
  have hidx' : (involutionCentralizer n S e).index = q ^ 2 * (q ^ 2 + q + 1) := by
    have : ((involutionCentralizer n S e).index : ℤ) = ((q ^ 2 * (q ^ 2 + q + 1) : ℕ) : ℤ) := by
      rw [hidx]
      push_cast
      ring
    exact_mod_cast this
  have hNcard : Nat.card (involutionCentralizer n S e) = c {J} := by
    change Nat.card (Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G)) = _
    rw [hcentJ]
  have hG : Nat.card G = q ^ 2 * (q ^ 2 + q + 1) * c {J} := by
    rw [← (involutionCentralizer n S e).index_mul_card, hidx', hNcard]
  have hqF : Nat.card F = q := Nat.card_eq_fintype_card
  rw [hqF] at hcJD
  rw [hG, hcJD]
  ring

end CFSG.Wreathed.BrauerWreathedOrder
