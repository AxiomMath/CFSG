module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueColumnBlock
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueColumnSum

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.UnitaryDValue.DValueData

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.UnitaryDValue.Columns

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem false_of_exceptional_columns (hpair : D.PrincipalPair) (h : ℕ) (hh : 3 ≤ h)
    (hq : (D.q + 1).factorization 3 = h) (Q P : Subgroup G) (hPQ : P ≤ Q)
    (hQ : Nat.card Q = 3 ^ (h + 2)) (hP : Nat.card P = 3 ^ (h + 1)) (t₀ : G) (ht₀Q : t₀ ∈ Q)
    (ht₀P : t₀ ∉ P)
    (hodd : ∀ v ∈ Q, v ∉ P →
      Odd (Nat.card (Subgroup.centralizer (Subgroup.zpowers v : Set G))))
    (hsyl : ∀ v ∈ Q, v ∉ P →
      (Nat.card (Subgroup.centralizer (Subgroup.zpowers v : Set G))).factorization 3 = h)
    (hcompl : ∀ v ∈ Q, v ∉ P →
      ∃ (K : Subgroup (Subgroup.centralizer (Subgroup.zpowers v : Set G))) (_ : K.Normal),
        Nat.Coprime 3 (Nat.card K) ∧
          IsPGroup 3 (Subgroup.centralizer (Subgroup.zpowers v : Set G) ⧸ K))
    (hclass : ∀ v ∈ Q, v ∉ P →
      {u : G | IsConj v u ∧ u * t₀⁻¹ ∈ P}.ncard = 9 ∧
        {u : G | IsConj v u ∧ u * t₀ ∈ P}.ncard = 9) :
    False := by
  have h3 : 3 ∣ D.q + 1 := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨ideal, hmax, hchar⟩ := exists_maximal_ideal_residue_three
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := exists_principal_label basis
  obtain ⟨χ₁, ψ, hχ₁deg, hψdeg, hψx, hψodd⟩ := hpair basis
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set χ : basis.index → G → ℂ := fun c => (basis.representation c).character with hχ
  have horder : ∀ u : Q, orderOf (u : G) ∣ 3 ^ (h + 2) := fun u => by
    rw [← hQ, Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard u
  have hψB : ψ ∉ B := D.not_mem_principal_block basis ideal principal hprincipal h3 ψ hψdeg hψx
  have hχ₁ : ∀ v ∈ Q, v ∉ P → χ₁ ∈ B ∧ χ χ₁ v = -1 := fun v hvQ hvP =>
    mem_block_and_eq_neg_one basis ideal 3 principal hprincipal χ₁ ψ hψB hψodd v (h + 2)
      (horder ⟨v, hvQ⟩) (hodd v hvQ hvP)
  have hχ₁B : χ₁ ∈ B := (hχ₁ t₀ ht₀Q ht₀P).1
  obtain ⟨μ, hμ1, hμω, hμω2, hμcases⟩ := exists_linear_character hPQ hQ hP ht₀Q ht₀P
  have hμsum : ∑ u : Q, (1 - ((μ u : ℂˣ) : ℂ)) = Nat.card Q := by
    have hne : (Units.coeHom ℂ).comp μ ≠ 1 := by
      intro h1
      have h2 := congrArg (fun f => f ⟨t₀, ht₀Q⟩) h1
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
        MonoidHom.one_apply] at h2
      exact ht₀P ((hμ1 _).mp h2)
    have hzero := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp μ) hne
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply] at hzero
    rw [Finset.sum_sub_distrib, hzero, sub_zero, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
  have hweight : ∀ u : Q, (u : G) ∉ P →
      ∑ u' : Q, (if IsConj (u : G) (u' : G) then 1 - ((μ u'⁻¹ : ℂˣ) : ℂ) else 0) = 27 :=
    fun u hu => class_weight_sum hPQ ht₀Q μ hμω hμω2 hμcases u (hclass u u.2 hu)
  have hnorm : ∀ u u' : Q, (u : G) ∉ P → (u' : G) ∉ P →
      ∑ c ∈ B, χ c u * χ c (u' : G)⁻¹ = if IsConj (u : G) (u' : G) then (3 : ℂ) ^ h else 0 := by
    intro u u' hu hu'
    split_ifs with hconj
    · have hinv : ∀ c, χ c (u' : G)⁻¹ = χ c (u : G)⁻¹ := by
        intro c
        obtain ⟨g, hg⟩ := isConj_iff.mp hconj
        rw [← hg, show (g * (u : G) * g⁻¹)⁻¹ = g * (u : G)⁻¹ * g⁻¹ by group]
        exact Representation.char_conj _ _ _
      simp_rw [hinv]
      have hn := principal_column_norm basis ideal 3 principal hprincipal u (h + 2) (horder u) h
        (hsyl u u.2 hu) (hcompl u u.2 hu)
      rw [hn]
      norm_num
    · exact block_column_orthogonal basis ideal 3 principal u u' (h + 2) (h + 2) (horder u)
        (horder u') hconj
  have hone : ∀ u : Q, (u : G) ∉ P → ∑ c ∈ B, χ c 1 * χ c u = 0 := by
    intro u hu
    have hnot : ¬ IsConj (u : G) 1 := by
      rw [isConj_one_left]
      intro h1
      exact hu (h1 ▸ P.one_mem)
    have h0 := block_column_orthogonal basis ideal 3 principal u 1 (h + 2) 0 (horder u)
      (by simp) hnot
    rw [inv_one] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  obtain ⟨hsq, hdeg⟩ := column_sums basis B Q P μ h hQ hμ1 hμsum hweight hnorm hone
  choose n hn using fun c => exists_int_column Q μ (basis.representation c)
  have hR1 : column Q μ (χ principal) = 1 :=
    column_eq_of_const Q P μ hμ1 hμsum _ 1 fun u _ => by simp only [hχ, hprincipal, Pi.one_apply]
  have hRχ₁ : column Q μ (χ χ₁) = -1 :=
    column_eq_of_const Q P μ hμ1 hμsum _ (-1) fun u hu => (hχ₁ u u.2 hu).2
  set d : basis.index → ℤ := fun c => (Module.finrank ℂ (basis.representation c).vector : ℤ)
    with hd
  have hdeg1 : ∀ c, (basis.representation c).character 1 = (d c : ℂ) := fun c => by
    simp only [hd, FiniteComplexRepresentation.character, Representation.char_one,
      Int.cast_natCast]
  have hn1 : n principal = 1 := by
    have e := hn principal
    rw [hR1] at e
    exact_mod_cast e.symm
  have hnχ₁ : n χ₁ = -1 := by
    have e := hn χ₁
    rw [hRχ₁] at e
    exact_mod_cast e.symm
  have hsqZ : ∑ c ∈ B, n c ^ 2 = 3 := by
    simp only [hn] at hsq
    exact_mod_cast hsq
  have hdegZ : ∑ c ∈ B, d c * n c = 0 := by
    simp only [hn, hdeg1] at hdeg
    exact_mod_cast hdeg
  have hda : d principal = 1 := by
    have e := hdeg1 principal
    simp only [hprincipal, Pi.one_apply] at e
    exact_mod_cast e.symm
  have hdχ₁ : d χ₁ = (D.q : ℤ) ^ 3 := by
    simp only [hd, hχ₁deg]
    push_cast
    ring
  have hq7 := D.seven_le_q
  have hq3 : 1 < (D.q : ℤ) ^ 3 := by
    have : 1 < D.q ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    exact_mod_cast this
  have hab : principal ≠ χ₁ := by
    intro heq
    rw [heq, hdχ₁] at hda
    omega
  obtain ⟨c, -, hc⟩ := exists_third_entry B n d (coefficientBlock_self_mem _ _ _) hχ₁B hab hn1
    hnχ₁ hda (fun c => by simp only [hd]; positivity) (by rw [hdχ₁]; exact hq3) hsqZ hdegZ
  apply D.not_cube_sub_one_dvd_card_G
  have hfin : Module.finrank ℂ (basis.representation c).vector = D.q ^ 3 - 1 := by
    rw [hdχ₁] at hc
    simp only [hd] at hc
    have h1 : 1 ≤ D.q ^ 3 := Nat.one_le_pow _ _ D.q_pos
    zify [h1]
    linarith
  rw [← hfin]
  exact finrank_dvd_card basis c

end CFSG.Semidihedral.UnitaryDValue.DValueData
