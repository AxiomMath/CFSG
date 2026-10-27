module

public import CFSG.CharacterTheory.BrauerLinearThree.QOneSetting

public section

namespace CFSG.BrauerLinearThree.QOne

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers

theorem card_mul_eq_of_order_formula {g cJ cD l q : ℕ} (hq : 2 ≤ q)
    (hcJ : cJ * l = q * (q - 1) ^ 2 * (q + 1)) (hcD : cD * l = (q - 1) ^ 2)
    (h : g * (cD ^ 2 * (q + 1) ^ 2) = cJ ^ 3 * (q ^ 2 + q + 1)) :
    g * l = q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by
  have h1 : 1 ≤ q := by omega
  have h2' : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < (q - 1) ^ 4 * (q + 1) ^ 2 := by
    have : 0 < q - 1 := by omega
    positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc g * l * ((q - 1) ^ 4 * (q + 1) ^ 2)
      = g * l * ((cD * l) ^ 2 * (q + 1) ^ 2) := by rw [hcD]; ring
    _ = g * (cD ^ 2 * (q + 1) ^ 2) * l ^ 3 := by ring
    _ = (cJ * l) ^ 3 * (q ^ 2 + q + 1) := by rw [h]; ring
    _ = q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) * ((q - 1) ^ 4 * (q + 1) ^ 2) := by
      rw [hcJ]
      zify [h1, h2', h3]
      ring

theorem exists_scalar_of_le_statedScalars {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)}
    (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) :
    ∀ x ∈ Z, ∃ a : F, (x : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a := by
  intro x hx
  obtain ⟨u, rfl⟩ := hZ hx
  exact ⟨u, rfl⟩

section General

variable (h5 : BrauerWreathedTypeOnePrincipalBlockStatement) {H : Type} [Group H] {F : Type}
  [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (hq : Nat.card F % 4 = 1) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (S₁ S₂ T : H)
  (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup H))
  (hcard : Nat.card (S : Subgroup H) = 2 ^ (2 * n + 1))
  (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
  (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂) {J₀ J₁ : H}
  (hJ₀ : (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1) = J₀) (hJ₁ : S₁ ^ 2 ^ (n - 1) = J₁)
  (hA : ∃ g ∈ Subgroup.centralizer ({J₀} : Set H), g⁻¹ * T * g = J₁)
  (ψ : Subgroup.centralizer ({J₀} : Set H) ≃* GL (Fin 2) F ⧸ Z)

include h5 hZ hZodd hq hn hgen hcard hS₁ hS₂ hT hcomm hconj hJ₀ hJ₁ hA ψ in
theorem typeOne_order_formula [Finite H]
    (h6 : (Subgroup.centralizer ((Subgroup.closure {S₁, S₂} : Subgroup H) : Set H)).relIndex
      (Subgroup.normalizer ((Subgroup.closure {S₁, S₂} : Subgroup H) : Set H)) = 6) :
    Nat.card H * (Nat.card (Subgroup.centralizer
        ((Subgroup.closure {J₀, J₁} : Subgroup H) : Set H)) ^ 2 * (Nat.card F + 1) ^ 2) =
      Nat.card (Subgroup.centralizer ({J₀} : Set H)) ^ 3 *
        (Nat.card F ^ 2 + Nat.card F + 1) := by
  let : Fintype H := Fintype.ofFinite H
  let : Fintype F := Fintype.ofFinite F
  subst hJ₀ hJ₁
  have key := h5 n hn S S₁ S₂ T hgen hcard hS₁ hS₂ hT hcomm hconj
  simp only at key
  have hqF : Fintype.card F % 4 = 1 := by rwa [← Nat.card_eq_fintype_card]
  have h := (key h6 hA F hqF Z (exists_scalar_of_le_statedScalars hZ) hZodd ⟨ψ⟩).1
  rwa [← Nat.card_eq_fintype_card] at h

include h5 hZ hZodd hq hn hgen hcard hS₁ hS₂ hT hcomm hconj hJ₀ hJ₁ hA ψ in
theorem typeOne_characters [Fintype H]
    (h6 : (Subgroup.centralizer ((Subgroup.closure {S₁, S₂} : Subgroup H) : Set H)).relIndex
      (Subgroup.normalizer ((Subgroup.closure {S₁, S₂} : Subgroup H) : Set H)) = 6)
    (basis : FiniteIrreducibleCharacterBasis H) :
    ∃ χ : Fin 6 → basis.index,
      (basis.representation (χ 1)).character 1 = (Nat.card F : ℂ) ^ 3 ∧
      (basis.representation (χ 4)).character 1 = (Nat.card F : ℂ) ^ 3 - 1 ∧
      (basis.representation (χ 5)).character 1 =
        ((Nat.card F : ℂ) + 1) * ((Nat.card F : ℂ) ^ 2 + Nat.card F + 1) ∧
      ∀ g : H, Odd (orderOf g) →
        -1 + (basis.representation (χ 1)).character g =
            (basis.representation (χ 2)).character g -
              (basis.representation (χ 3)).character g ∧
          (basis.representation (χ 2)).character g -
              (basis.representation (χ 3)).character g =
            (basis.representation (χ 4)).character g ∧
          (basis.representation (χ 2)).character g + (basis.representation (χ 3)).character g =
            (basis.representation (χ 5)).character g := by
  let : Fintype F := Fintype.ofFinite F
  subst hJ₀ hJ₁
  have key := h5 n hn S S₁ S₂ T hgen hcard hS₁ hS₂ hT hcomm hconj
  simp only at key
  have hqF : Fintype.card F % 4 = 1 := by rwa [← Nat.card_eq_fintype_card]
  have h := (key h6 hA F hqF Z (exists_scalar_of_le_statedScalars hZ) hZodd ⟨ψ⟩).2
  obtain ⟨ideal, hmax, h2mem⟩ := (CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 :=
    (CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two).2 ideal hmax h2mem
  obtain ⟨principal, hprincipal⟩ :=
    CFSG.Semidihedral.Principal.finiteIrreducibleCharacterBasis_exists_principal_label basis
  obtain ⟨χ, -, -, -, h1, -, -, h4, h5', hrel⟩ := h ideal basis principal hprincipal
  rw [← Nat.card_eq_fintype_card] at h1 h4 h5'
  exact ⟨χ, h1, h4, h5', hrel⟩

include h5 hZ hZodd hq hn hgen hcard hS₁ hS₂ hT hcomm hconj hJ₀ hJ₁ hA ψ in
theorem typeOne_or_typeTwo_order [Finite H] :
    Nat.card H * (Nat.card (Subgroup.centralizer
        ((Subgroup.closure {J₀, J₁} : Subgroup H) : Set H)) ^ 2 * (Nat.card F + 1) ^ 2) =
      Nat.card (Subgroup.centralizer ({J₀} : Set H)) ^ 3 * (Nat.card F ^ 2 + Nat.card F + 1) ∨
    Nat.card H * Nat.card (Subgroup.centralizer
        ((Subgroup.closure {J₀, J₁} : Subgroup H) : Set H)) ^ 2 =
      Nat.card (Subgroup.centralizer ({J₀} : Set H)) *
        Nat.card (Subgroup.centralizer ({J₁} : Set H)) ^ 2 := by
  let : Fintype H := Fintype.ofFinite H
  have hcases := CFSG.Wreathed.BrauerWreathedOrder.brauer_wreathed_order_group_cases n hn S S₁
    S₂ T hgen hcard hS₁ hS₂ hT hcomm hconj
  simp only [hJ₀, hJ₁] at hcases
  obtain ⟨h1, -, -, -, -, -, h4⟩ := hcases
  rcases h1 with h | h
  · exact Or.inr (h4 h hA)
  · exact Or.inl (typeOne_order_formula h5 hZ hZodd hq n hn S S₁ S₂ T hgen hcard hS₁ hS₂ hT
      hcomm hconj hJ₀ hJ₁ hA ψ h)

end General

section Group

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem card_mul_card_Z_eq (h5 : BrauerWreathedTypeOnePrincipalBlockStatement) [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 1) :
    Nat.card G * Nat.card Z = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  obtain ⟨n, S, S₁, S₂, T, hn, hgen, hcard, hS₁, hS₂, hT, hcomm, hconj, -, hJpow, hJ₂pow⟩ :=
    exists_wreath_sylow_of_G φ hZ hZodd h2 hJ hq
  obtain ⟨h6, hA⟩ := caseOneA_of_simple φ hnonab n hn S S₁ S₂ T hgen hcard hS₁ hS₂ hT hcomm
    hconj hJpow hJ₂pow
  have h := typeOne_order_formula h5 hZ hZodd hq n hn S S₁ S₂ T hgen hcard hS₁ hS₂ hT hcomm
    hconj hJpow hJ₂pow hA φ h6
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  exact card_mul_eq_of_order_formula hq2 (card_centralizer_J φ)
    (card_centralizer_closure_J_invJ₂ φ hZ hZodd h2 hJ) h

end Group

end CFSG.BrauerLinearThree.QOne
