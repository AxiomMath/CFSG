module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneBlockColumns
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneCharacterInputs
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneMoments
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneTable
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneTableDegrees
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSylowSum

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes
open CFSG.Semidihedral.Principal CFSG.Wreathed.LinearLocalTwistMoment

theorem one_lt_abs_of_signed_degree_congruences {k : ℕ} (hk : 2 ≤ k) {x eq : ℤ}
    (hqe : eq - 1 ≡ 2 * k [ZMOD 4 * k]) (hx : x ≠ 0)
    (hcong : x ≡ 2 - eq [ZMOD 8 * k] ∨ x ≡ -eq [ZMOD 8 * k] ∨ x ≡ 4 * k - 1 [ZMOD 8 * k]) :
    1 < |x| := by
  have hk0 : (0 : ℤ) < k := by exact_mod_cast (show 0 < k by omega)
  have h4 : ∀ {a b : ℤ}, a ≡ b [ZMOD 8 * k] → a ≡ b [ZMOD 4 * k] := fun h =>
    Int.ModEq.of_mul_right 2 (by rwa [show (4 : ℤ) * k * 2 = 8 * k by ring])
  have hnd : ∀ c : ℤ, (c = 0 ∨ c = 2 ∨ c = -2) → ¬ (4 * (k : ℤ)) ∣ 2 * k + c := by
    rintro c hc ⟨m, hm⟩
    have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk
    rcases hc with rfl | rfl | rfl
    · have : (k : ℤ) * (2 * m - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · omega
      · omega
    · rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · subst h; linarith
      · nlinarith
    · rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · subst h; linarith
      · nlinarith
  have hx1 : x ≠ 1 ∧ x ≠ -1 := by
    rcases hcong with h | h | h
    · refine ⟨fun h1 => ?_, fun h1 => ?_⟩
      · subst h1
        apply hnd 0 (Or.inl rfl)
        have h' : 2 * (k : ℤ) ≡ 0 [ZMOD 4 * k] := by
          calc 2 * (k : ℤ) ≡ eq - 1 [ZMOD 4 * k] := hqe.symm
            _ = 1 - (2 - eq) := by ring
            _ ≡ 1 - 1 [ZMOD 4 * k] := Int.ModEq.sub_left 1 (h4 h).symm
            _ = 0 := by ring
        simpa using (Int.modEq_zero_iff_dvd.mp h')
      · subst h1
        apply hnd (-2) (Or.inr (Or.inr rfl))
        have h' : 2 * (k : ℤ) - 2 ≡ 0 [ZMOD 4 * k] := by
          calc 2 * (k : ℤ) - 2 ≡ (eq - 1) - 2 [ZMOD 4 * k] := hqe.symm.sub_right 2
            _ = -((2 - eq) - (-1)) := by ring
            _ ≡ -((-1) - (-1)) [ZMOD 4 * k] := ((h4 h).symm.sub_right (-1)).neg
            _ = 0 := by ring
        simpa [sub_eq_add_neg] using Int.modEq_zero_iff_dvd.mp h'
    · refine ⟨fun h1 => ?_, fun h1 => ?_⟩
      · subst h1
        apply hnd 2 (Or.inr (Or.inl rfl))
        have h' : 2 * (k : ℤ) + 2 ≡ 0 [ZMOD 4 * k] := by
          calc 2 * (k : ℤ) + 2 ≡ (eq - 1) + 2 [ZMOD 4 * k] := hqe.symm.add_right 2
            _ = 1 - -eq := by ring
            _ ≡ 1 - 1 [ZMOD 4 * k] := Int.ModEq.sub_left 1 (h4 h).symm
            _ = 0 := by ring
        exact Int.modEq_zero_iff_dvd.mp h'
      · subst h1
        apply hnd 0 (Or.inl rfl)
        have h' : 2 * (k : ℤ) ≡ 0 [ZMOD 4 * k] := by
          calc 2 * (k : ℤ) ≡ eq - 1 [ZMOD 4 * k] := hqe.symm
            _ = -(-eq) - 1 := by ring
            _ ≡ -(-1) - 1 [ZMOD 4 * k] := ((h4 h).symm.neg).sub_right 1
            _ = 0 := by ring
        simpa using Int.modEq_zero_iff_dvd.mp h'
    · refine ⟨fun h1 => ?_, fun h1 => ?_⟩
      · subst h1
        obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp h
        rcases lt_trichotomy m 0 with h' | h' | h'
        · nlinarith
        · subst h'; have : (4 : ℤ) * k = 2 := by linarith
          omega
        · nlinarith
      · subst h1
        obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp h
        rcases lt_trichotomy m 0 with h' | h' | h'
        · nlinarith
        · subst h'; omega
        · nlinarith
  rcases lt_trichotomy x 0 with h | h | h
  · rw [abs_of_neg h]; omega
  · exact absurd h hx
  · rw [abs_of_pos h]; omega

theorem sign_mul_sq_div {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) (z d : ℂ) :
    (δ : ℂ) * (((δ : ℂ) * z) ^ 2 / d) = z ^ 2 / ((δ : ℂ) * d) := by
  rcases hδ with rfl | rfl <;> push_cast <;> ring

theorem sign_cube_div {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) (z d : ℂ) :
    ((δ : ℂ) * z) ^ 3 / d = z ^ 3 / ((δ : ℂ) * d) := by
  rcases hδ with rfl | rfl <;> push_cast <;> ring

theorem typeStar_signed_degrees {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (lambdaLabel : normalizerBasis.index)
    (hlambda : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x =
          thetaG t θ (c : G))
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B) :
    ∃ (e a₀ a₁ a₂ a₃ : ℤ) (c₀ : basis.index),
      (p ^ f % 4 = 1 → e = 1) ∧ (p ^ f % 4 = 3 → e = -1) ∧ (e = 1 ∨ e = -1) ∧
      e * ((p ^ f : ℕ) : ℤ) - 1 ≡ 2 * ((2 ^ (n - 3) : ℕ) : ℤ) [ZMOD 4 * ((2 ^ (n - 3) : ℕ) : ℤ)] ∧
      a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0 ∧ a₀ + a₁ ≠ 0 ∧ a₀ + a₂ ≠ 0 ∧
      a₀ + a₁ + a₂ + a₃ = 0 ∧
      (1 : ℚ) / a₀ + (((p ^ f : ℕ) : ℤ) : ℚ) ^ 2 / a₁ + (((p ^ f : ℕ) : ℤ) : ℚ) ^ 2 / a₂ +
        1 / a₃ = 0 ∧
      a₀ ≡ 1 [ZMOD 8 * ((2 ^ (n - 3) : ℕ) : ℤ)] ∧
      a₁ ≡ 2 - e * ((p ^ f : ℕ) : ℤ) [ZMOD 8 * ((2 ^ (n - 3) : ℕ) : ℤ)] ∧
      a₂ ≡ -(e * ((p ^ f : ℕ) : ℤ)) [ZMOD 8 * ((2 ^ (n - 3) : ℕ) : ℤ)] ∧
      a₃ ≡ 4 * ((2 ^ (n - 3) : ℕ) : ℤ) - 1 [ZMOD 8 * ((2 ^ (n - 3) : ℕ) : ℤ)] ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          (basis.representation χ).character t ^ 3 / (basis.representation χ).character 1 =
        1 / (a₀ : ℂ) + (e : ℂ) * ((p ^ f : ℕ) : ℂ) ^ 3 / a₁ -
          (e : ℂ) * ((p ^ f : ℕ) : ℂ) ^ 3 / a₂ - 1 / a₃ -
          (1 - (e : ℂ) * ((p ^ f : ℕ) : ℂ)) ^ 3 / ((a₀ : ℂ) + a₂) -
          (1 + (e : ℂ) * ((p ^ f : ℕ) : ℂ)) ^ 3 / ((a₀ : ℂ) + a₁) ∧
      (∀ x ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        Module.finrank ℂ (basis.representation x).vector = 1 →
        multiplicityColumn basis (fS (r n) : G) (modulus n) 0 x -
          multiplicityColumn basis (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) x = 1 →
        multiplicityColumn basis (fS (r n) : G) (modulus n) 0 x -
          multiplicityColumn basis (fS (r n) : G) (modulus n) 2 x = 1 → a₀ = 1) ∧
      c₀ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B ∧
      (a₀ = 1 → Module.finrank ℂ (basis.representation c₀).vector = 1 ∧
        ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
          (basis.representation c₀).character (t * y) = thetaG t θ (y : G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, φ, U, V, I, o, he1, he3, he, hφ1, hval, hI, ho0, hoinj, homem, hosurj, H⟩ :=
    typeStar_table_hyp fS hn ht hindex hnonab hcentral hnc p f hp hpodd hf hmodel θ hθS hθT basis
      ideal normalizerBasis lambdaLabel hlambda B hB
  set Bs := coefficientBlock basis (localizedComplexIntegerRing ideal) B with hBs
  obtain ⟨hM4, hKeven, hK2, hhalf⟩ := modulus_eq_four_mul hn
  set k : ℕ := 2 ^ (n - 3) with hk
  set L := multiplicityColumn basis (fS (r n) : G) (modulus n) with hL
  set deg : basis.index → ℤ := fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)
    with hdegdef
  have hkpow : ∃ m : ℕ, k = 2 ^ m := ⟨n - 3, rfl⟩
  obtain ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, δ, ψ, ν, hδ₀, hδ₁, hδ₂, hδ₃, hδ₄, hδ, hnodup,
      hψinj, hνinj, hψne, hνne, hνψ, hsub, hΘv, hEv, hFv, hUv, hVv, -, hd0123, hdψ, hdν,
      hd024⟩ :=
    type_star_table_coordinates_weak k hK2 hkpow Bs deg H.hdeg
      (fun χ => L 0 χ - L ((modulus n / 2 : ℕ) : ℤ) χ) (fun l χ => L 0 χ - L (2 * (l : ℤ)) χ)
      (fun j χ => L ((o j).val : ℤ) χ - L 1 χ) U V H.hΘΘ H.hΘE H.hEE H.hΘF H.hEF H.hFF
      H.hUU H.hUV H.hVV H.hUΘ H.hVΘ H.hUE H.hVE H.hUF H.hVF H.hdegΘ H.hdegE H.hdegF H.hdegU
      H.hdegV H.hcong
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnodup
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hnodup
  have hmem : ∀ x, x = c₀ ∨ x = c₁ ∨ x = c₂ ∨ x = c₃ ∨ x = c₄ → x ∈ Bs := fun x hx =>
    hsub (Finset.mem_union_left _ (Finset.mem_union_left _ (by
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)))
  have hc₀B := hmem c₀ (Or.inl rfl)
  have hc₁B := hmem c₁ (Or.inr (Or.inl rfl))
  have hc₂B := hmem c₂ (Or.inr (Or.inr (Or.inl rfl)))
  have hc₃B := hmem c₃ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hc₄B := hmem c₄ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hψB : ∀ l ∈ Finset.Icc 1 (k - 1), ψ l ∈ Bs := fun l hl =>
    hsub (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem ψ hl)))
  have hνB : ∀ i ∈ Finset.range k, ν i ∈ Bs := fun i hi =>
    hsub (Finset.mem_union_right _ (Finset.mem_image_of_mem ν hi))
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h40 := Ne.symm h04
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h43 := Ne.symm h34
  have hk1 : 1 ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hindex t
    (orderOf_t fS hn ht) hnonab hcentral hnc p f hp hpodd hf hmodel
  have h2part : 2 ^ padicValNat 2 ((p ^ f) ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [h]
    rfl
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨m, hm⟩ := hpodd
      omega
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have hqe : e * ((p ^ f : ℕ) : ℤ) - 1 ≡ 2 * (k : ℤ) [ZMOD 4 * (k : ℤ)] :=
    sign_mul_sub_one_modEq hn hq3 hqodd h2part he1 he3
  have hvt : ∀ x ∈ Bs, (basis.representation x).character t =
      (U x : ℂ) + V x * (1 + e * ((p ^ f : ℕ) : ℂ)) := fun x hx => by
    have h := hval x hx 1 (by rw [orderOf_one]; exact odd_one)
    rw [OneMemClass.coe_one, mul_one, hφ1, thetaG_of_mem θ (Subgroup.one_mem _)] at h
    rw [h]
    have h1 : θ ⟨1, Subgroup.one_mem _⟩ = 1 := map_one θ
    rw [h1, Units.val_one, mul_one]
  have hdeg1 : ∀ x : basis.index, (basis.representation x).character 1 = (deg x : ℂ) := fun x => by
    rw [(basis_character_one basis x).1]
    simp [hdegdef]
  have hdegpos : ∀ x ∈ Bs, 0 < deg x := H.hdeg
  have hψc : ∀ l ∈ Finset.Icc 1 (k - 1), c₀ ≠ ψ l ∧ c₁ ≠ ψ l ∧ c₂ ≠ ψ l ∧ c₃ ≠ ψ l ∧
      c₄ ≠ ψ l := fun l hl => by
    obtain ⟨a0, a1, a2, a3, a4⟩ := hψne l hl
    exact ⟨Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4⟩
  have hνc : ∀ i ∈ Finset.range k, c₀ ≠ ν i ∧ c₁ ≠ ν i ∧ c₂ ≠ ν i ∧ c₃ ≠ ν i ∧
      c₄ ≠ ν i := fun i hi => by
    obtain ⟨a0, a1, a2, a3, a4⟩ := hνne i hi
    exact ⟨Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4⟩
  have hsumψ : ∀ x, (∀ l ∈ Finset.Icc 1 (k - 1), x ≠ ψ l) →
      ∑ l ∈ Finset.Icc 1 (k - 1), (if x = ψ l then (1 : ℤ) else 0) = 0 := fun x hx =>
    Finset.sum_eq_zero fun l hl => by rw [ite_eq_right (hx l hl)]
  have hsumν : ∀ x, (∀ i ∈ Finset.range k, x ≠ ν i) →
      ∑ i ∈ Finset.range k, (if x = ν i then (1 : ℤ) else 0) = 0 := fun x hx =>
    Finset.sum_eq_zero fun i hi => by rw [ite_eq_right (hx i hi)]
  have hcol : ∀ x ∈ Bs, x ≠ c₄ → (∀ l ∈ Finset.Icc 1 (k - 1), x ≠ ψ l) →
      (∀ i ∈ Finset.range k, x ≠ ν i) →
      (deg x = deg x) ∧
      (L 0 x - L ((modulus n / 2 : ℕ) : ℤ) x = δ₀ * (if x = c₀ then 1 else 0) +
        δ₁ * (if x = c₁ then 1 else 0) + δ₂ * (if x = c₂ then 1 else 0) +
        δ₃ * (if x = c₃ then 1 else 0)) ∧
      (∀ l ∈ Finset.Icc 1 (k - 1), L 0 x - L (2 * (l : ℤ)) x =
        δ₀ * (if x = c₀ then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0)) ∧
      (∀ j ∈ Finset.Icc 1 (k - 1), L ((o j).val : ℤ) x - L 1 x = 0) ∧
      U x = δ₀ * (if x = c₀ then 1 else 0) - δ₁ * (if x = c₁ then 1 else 0) +
        δ₂ * (if x = c₂ then 1 else 0) - δ₃ * (if x = c₃ then 1 else 0) ∧
      V x = δ₁ * (if x = c₁ then 1 else 0) - δ₂ * (if x = c₂ then 1 else 0) := by
    intro x hx hx4 hxψ hxν
    refine ⟨rfl, hΘv x hx, fun l hl => ?_, fun j hj => ?_, ?_, ?_⟩
    · have h := hEv l hl x hx
      rw [ite_eq_right (hxψ l hl), mul_zero, sub_zero] at h
      exact h
    · have h := hFv j hj x hx
      have hj' : j ∈ Finset.range k := Finset.mem_range.mpr (by
        have := (Finset.mem_Icc.mp hj).2
        omega)
      rw [ite_eq_right (hxν j hj'), ite_eq_right (hxν 0 (Finset.mem_range.mpr (by omega))),
        sub_zero, mul_zero] at h
      exact h
    · have h := hUv x hx
      rw [ite_eq_right hx4, mul_zero, add_zero] at h
      exact h
    · have h := hVv x hx
      rw [ite_eq_right hx4, hsumψ x hxψ, hsumν x hxν, mul_zero, mul_zero, sub_zero,
        add_zero, sub_zero] at h
      exact h
  obtain ⟨ho, htrans⟩ := transversal_enum_inputs hn hI ho0 homem hosurj
  have hT2 : ∀ x ∈ Bs, (∀ i ∈ Finset.range k, x ≠ ν i) → ∀ δ' : ℤ, (δ' = 1 ∨ δ' = -1) →
      (L 0 x - L ((modulus n / 2 : ℕ) : ℤ) x = δ' →
        (∀ l ∈ Finset.Icc 1 (k - 1), L 0 x - L (2 * (l : ℤ)) x = δ') → U x = δ' → V x = 0 →
        δ' * deg x ≡ 1 [ZMOD 8 * k]) ∧
      (L 0 x - L ((modulus n / 2 : ℕ) : ℤ) x = δ' →
        (∀ l ∈ Finset.Icc 1 (k - 1), L 0 x - L (2 * (l : ℤ)) x = δ') → U x = -δ' →
        V x = δ' → δ' * deg x ≡ 2 - e * ((p ^ f : ℕ) : ℤ) [ZMOD 8 * k]) ∧
      (L 0 x - L ((modulus n / 2 : ℕ) : ℤ) x = δ' →
        (∀ l ∈ Finset.Icc 1 (k - 1), L 0 x - L (2 * (l : ℤ)) x = 0) → U x = δ' →
        V x = -δ' → δ' * deg x ≡ -(e * ((p ^ f : ℕ) : ℤ)) [ZMOD 8 * k]) ∧
      (L 0 x - L ((modulus n / 2 : ℕ) : ℤ) x = δ' →
        (∀ l ∈ Finset.Icc 1 (k - 1), L 0 x - L (2 * (l : ℤ)) x = 0) → U x = -δ' → V x = 0 →
        δ' * deg x ≡ 4 * k - 1 [ZMOD 8 * k]) := by
    intro x hx hxν δ' hδ'
    obtain ⟨hsymm, hdegx, hvalx⟩ := character_multiplicity_inputs hn fS basis x
    have hinv : ∑ j ∈ Finset.range (4 * k), (-1) ^ j * L (j : ℤ) x =
        U x + V x * (1 + e * ((p ^ f : ℕ) : ℤ)) := by
      have h := hvalx
      rw [← ht, hvt x hx] at h
      exact_mod_cast h.symm
    have hS := sylow_character_sum_congruence hindex n hn S fS basis x
    have hF0 : ∀ j ∈ Finset.Icc 1 (k - 1), L ((o j).val : ℤ) x - L 1 x = 0 := fun j hj => by
      have h := hFv j hj x hx
      have hj' : j ∈ Finset.range k := Finset.mem_range.mpr (by
        have := (Finset.mem_Icc.mp hj).2
        omega)
      rw [ite_eq_right (hxν j hj'), ite_eq_right (hxν 0 (Finset.mem_range.mpr (by omega))),
        sub_zero, mul_zero] at h
      exact h
    have hM2 : modulus n / 2 = 2 * k := by omega
    exact type_star_degree_congruences k hK2 hkpow ((p ^ f : ℕ) : ℤ) e he hqe
      (fun j => (o j).val) (deg x) (U x) (V x) δ' hδ' (L 0 x - L ((modulus n / 2 : ℕ) : ℤ) x)
      (fun l => L 0 x - L (2 * (l : ℤ)) x) (fun j => L ((o j).val : ℤ) x - L 1 x)
      (fun j => L (j : ℤ) x) hsymm ho htrans (by rw [hM2]; push_cast; rfl)
      (fun l _ => by push_cast; rfl) (fun j _ => by push_cast; rfl) hdegx hinv
      (by
        unfold orderFourValue
        push_cast at hS ⊢
        exact hS)
      hF0
  obtain ⟨-, hΘ0, hE0, -, hU0, hV0⟩ := hcol c₀ hc₀B h04 (fun l hl => (hψc l hl).1)
    (fun i hi => (hνc i hi).1)
  obtain ⟨-, hΘ1, hE1, -, hU1, hV1⟩ := hcol c₁ hc₁B h14 (fun l hl => (hψc l hl).2.1)
    (fun i hi => (hνc i hi).2.1)
  obtain ⟨-, hΘ2, hE2, -, hU2, hV2⟩ := hcol c₂ hc₂B h24 (fun l hl => (hψc l hl).2.2.1)
    (fun i hi => (hνc i hi).2.2.1)
  obtain ⟨-, hΘ3, hE3, -, hU3, hV3⟩ := hcol c₃ hc₃B h34 (fun l hl => (hψc l hl).2.2.2.1)
    (fun i hi => (hνc i hi).2.2.2.1)
  simp only [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32, ite_true, ite_false,
    mul_one, mul_zero, add_zero, zero_add] at hΘ0 hΘ1 hΘ2 hΘ3
  simp only [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32, ite_true, ite_false,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, zero_sub] at hU0 hU1 hU2 hU3
  simp only [h01, h02, h12, h21, h31, h32, ite_true, ite_false, mul_one, mul_zero, sub_zero,
    zero_sub] at hV0 hV1 hV2 hV3
  have hE0' : ∀ l ∈ Finset.Icc 1 (k - 1), L 0 c₀ - L (2 * (l : ℤ)) c₀ = δ₀ := fun l hl => by
    simpa [h01] using hE0 l hl
  have hE1' : ∀ l ∈ Finset.Icc 1 (k - 1), L 0 c₁ - L (2 * (l : ℤ)) c₁ = δ₁ := fun l hl => by
    simpa [h10] using hE1 l hl
  have hE2' : ∀ l ∈ Finset.Icc 1 (k - 1), L 0 c₂ - L (2 * (l : ℤ)) c₂ = 0 := fun l hl => by
    simpa [h20, h21] using hE2 l hl
  have hE3' : ∀ l ∈ Finset.Icc 1 (k - 1), L 0 c₃ - L (2 * (l : ℤ)) c₃ = 0 := fun l hl => by
    simpa [h30, h31] using hE3 l hl
  have hcg0 := (hT2 c₀ hc₀B (fun i hi => (hνc i hi).1) δ₀ hδ₀).1 hΘ0 hE0' hU0 hV0
  have hcg1 := (hT2 c₁ hc₁B (fun i hi => (hνc i hi).2.1) δ₁ hδ₁).2.1 hΘ1 hE1' hU1 hV1
  have hcg2 := (hT2 c₂ hc₂B (fun i hi => (hνc i hi).2.2.1) δ₂ hδ₂).2.2.1 hΘ2 hE2' hU2 hV2
  have hcg3 := (hT2 c₃ hc₃B (fun i hi => (hνc i hi).2.2.2.1) δ₃ hδ₃).2.2.2 hΘ3 hE3' hU3 hV3
  have hsign : ∀ {δ' : ℤ}, (δ' = 1 ∨ δ' = -1) → δ' ≠ 0 := fun h => by
    rcases h with rfl | rfl <;> norm_num
  have hsq : ∀ {δ' : ℤ}, (δ' = 1 ∨ δ' = -1) → δ' * δ' = 1 := fun h => by
    rcases h with rfl | rfl <;> norm_num
  have ha : ∀ {δ' : ℤ} {x : basis.index}, (δ' = 1 ∨ δ' = -1) → x ∈ Bs → δ' * deg x ≠ 0 :=
    fun h hx => mul_ne_zero (hsign h) (hdegpos _ hx).ne'
  have h01' : δ₀ * deg c₀ + δ₁ * deg c₁ ≠ 0 := by
    rw [← hdψ 1 hk1]
    exact ha hδ (hψB 1 hk1)
  have h02' : δ₀ * deg c₀ + δ₂ * deg c₂ ≠ 0 := by
    have h : δ₀ * deg c₀ + δ₂ * deg c₂ = -(δ₄ * deg c₄) := by linarith [hd024]
    rw [h, neg_ne_zero]
    exact ha hδ₄ hc₄B
  set qC : ℂ := ((p ^ f : ℕ) : ℂ) with hqC
  have hval0 : (basis.representation c₀).character t = (δ₀ : ℂ) * 1 := by
    rw [hvt c₀ hc₀B, hU0, hV0]
    push_cast
    ring
  have hval1 : (basis.representation c₁).character t = (δ₁ : ℂ) * ((e : ℂ) * qC) := by
    rw [hvt c₁ hc₁B, hU1, hV1]
    push_cast
    ring
  have hval2 : (basis.representation c₂).character t = (δ₂ : ℂ) * (-((e : ℂ) * qC)) := by
    rw [hvt c₂ hc₂B, hU2, hV2]
    push_cast
    ring
  have hval3 : (basis.representation c₃).character t = (δ₃ : ℂ) * (-1) := by
    rw [hvt c₃ hc₃B, hU3, hV3]
    push_cast
    ring
  have he2 : (e : ℂ) ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hR2 : 1 / ((δ₀ * deg c₀ : ℤ) : ℂ) + qC ^ 2 / ((δ₁ * deg c₁ : ℤ) : ℂ) +
      qC ^ 2 / ((δ₂ * deg c₂ : ℤ) : ℂ) + 1 / ((δ₃ * deg c₃ : ℤ) : ℂ) = 0 := by
    have h := theta_involution_moment fS hn ht basis ideal B
    have hexp : ∑ χ ∈ Bs, (((L 0 χ - L ((modulus n / 2 : ℕ) : ℤ) χ : ℤ)) : ℂ) *
        ((basis.representation χ).character t ^ 2 / (basis.representation χ).character 1) =
        (δ₀ : ℂ) * ((basis.representation c₀).character t ^ 2 / deg c₀) +
        (δ₁ : ℂ) * ((basis.representation c₁).character t ^ 2 / deg c₁) +
        (δ₂ : ℂ) * ((basis.representation c₂).character t ^ 2 / deg c₂) +
        (δ₃ : ℂ) * ((basis.representation c₃).character t ^ 2 / deg c₃) := by
      rw [Finset.sum_congr rfl fun χ hχ => by rw [hΘv χ hχ, hdeg1 χ]]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul,
        zero_mul, Finset.sum_ite_eq', hc₀B, hc₁B, hc₂B, hc₃B, ite_true]
    rw [hexp, hval0, hval1, hval2, hval3, sign_mul_sq_div hδ₀, sign_mul_sq_div hδ₁,
      sign_mul_sq_div hδ₂, sign_mul_sq_div hδ₃] at h
    rw [← h]
    push_cast
    rw [show ((e : ℂ) * qC) ^ 2 = qC ^ 2 by rw [mul_pow, he2, one_mul],
      show (-((e : ℂ) * qC)) ^ 2 = qC ^ 2 by rw [neg_sq, mul_pow, he2, one_mul]]
    ring
  have hval4 : (basis.representation c₄).character t = (δ₄ : ℂ) * (1 - (e : ℂ) * qC) := by
    have hU := hUv c₄ hc₄B
    have hV := hVv c₄ hc₄B
    simp only [h40, h41, h42, h43, ite_true, ite_false, mul_one, mul_zero, sub_zero,
      zero_sub, zero_add, add_zero] at hU hV
    rw [hsumψ c₄ fun l hl => (hψc l hl).2.2.2.2, hsumν c₄ fun i hi => (hνc i hi).2.2.2.2,
      mul_zero, add_zero, sub_zero] at hV
    rw [hvt c₄ hc₄B, hU, hV]
    push_cast
    ring
  have hψsum : ∀ l ∈ Finset.Icc 1 (k - 1),
      ∑ l' ∈ Finset.Icc 1 (k - 1), (if ψ l = ψ l' then (1 : ℤ) else 0) = 1 := fun l hl => by
    rw [Finset.sum_eq_single_of_mem l hl fun l' hl' hne => by
      rw [ite_eq_right fun h =>
        hne (hψinj (Finset.mem_coe.mpr hl) (Finset.mem_coe.mpr hl') h).symm]]
    rw [ite_eq_left rfl]
  have hνsum : ∀ i ∈ Finset.range k,
      ∑ i' ∈ Finset.range k, (if ν i = ν i' then (1 : ℤ) else 0) = 1 := fun i hi => by
    rw [Finset.sum_eq_single_of_mem i hi fun i' hi' hne => by
      rw [ite_eq_right fun h =>
        hne (hνinj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hi') h).symm]]
    rw [ite_eq_left rfl]
  have hvalψ : ∀ l ∈ Finset.Icc 1 (k - 1),
      (basis.representation (ψ l)).character t = (δ : ℂ) * (1 + (e : ℂ) * qC) := fun l hl => by
    obtain ⟨a0, a1, a2, a3, a4⟩ := hψne l hl
    have hU := hUv (ψ l) (hψB l hl)
    have hV := hVv (ψ l) (hψB l hl)
    simp only [a0, a1, a2, a3, a4, ite_false, mul_zero, sub_zero, add_zero] at hU hV
    rw [hψsum l hl, hsumν (ψ l) fun i hi h => hνψ i hi l hl h.symm, mul_zero, sub_zero,
      mul_one] at hV
    rw [hvt (ψ l) (hψB l hl), hU, hV]
    push_cast
    ring
  have hvalν : ∀ i ∈ Finset.range k,
      (basis.representation (ν i)).character t = (δ : ℂ) * (-(1 + (e : ℂ) * qC)) :=
    fun i hi => by
    obtain ⟨a0, a1, a2, a3, a4⟩ := hνne i hi
    have hU := hUv (ν i) (hνB i hi)
    have hV := hVv (ν i) (hνB i hi)
    simp only [a0, a1, a2, a3, a4, ite_false, mul_zero, sub_zero, add_zero] at hU hV
    rw [hνsum i hi, hsumψ (ν i) fun l hl => hνψ i hi l hl, mul_zero, add_zero, mul_one,
      zero_sub] at hV
    rw [hvt (ν i) (hνB i hi), hU, hV]
    push_cast
    ring
  have hoff : ∀ x ∈ Bs, x ∉ ({c₀, c₁, c₂, c₃, c₄} ∪ (Finset.Icc 1 (k - 1)).image ψ ∪
      (Finset.range k).image ν : Finset basis.index) →
      (basis.representation x).character t ^ 3 / (basis.representation x).character 1 = 0 := by
    intro x hx hnot
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or, not_exists, not_and] at hnot
    obtain ⟨⟨⟨x0, x1, x2, x3, x4⟩, xψ⟩, xν⟩ := hnot
    have hU := hUv x hx
    have hV := hVv x hx
    simp only [x0, x1, x2, x3, x4, ite_false, mul_zero, sub_zero, add_zero] at hU hV
    rw [hsumψ x fun l hl h => xψ l hl h.symm, hsumν x fun i hi h => xν i hi h.symm, mul_zero,
      sub_zero] at hV
    rw [hvt x hx, hU, hV]
    simp
  have hS : ∑ χ ∈ Bs, (basis.representation χ).character t ^ 3 /
      (basis.representation χ).character 1 =
      1 / ((δ₀ * deg c₀ : ℤ) : ℂ) + (e : ℂ) * qC ^ 3 / ((δ₁ * deg c₁ : ℤ) : ℂ) -
        (e : ℂ) * qC ^ 3 / ((δ₂ * deg c₂ : ℤ) : ℂ) - 1 / ((δ₃ * deg c₃ : ℤ) : ℂ) -
        (1 - (e : ℂ) * qC) ^ 3 / (((δ₀ * deg c₀ : ℤ) : ℂ) + ((δ₂ * deg c₂ : ℤ) : ℂ)) -
        (1 + (e : ℂ) * qC) ^ 3 / (((δ₀ * deg c₀ : ℤ) : ℂ) + ((δ₁ * deg c₁ : ℤ) : ℂ)) := by
    rw [← Finset.sum_subset hsub hoff]
    have hdisj1 : Disjoint ({c₀, c₁, c₂, c₃, c₄} : Finset basis.index)
        ((Finset.Icc 1 (k - 1)).image ψ) := by
      rw [Finset.disjoint_left]
      intro x hx hxψ
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hxψ
      obtain ⟨a0, a1, a2, a3, a4⟩ := hψne l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h | h | h <;> contradiction
    have hdisj2 : Disjoint (({c₀, c₁, c₂, c₃, c₄} : Finset basis.index) ∪
        (Finset.Icc 1 (k - 1)).image ψ) ((Finset.range k).image ν) := by
      rw [Finset.disjoint_left]
      intro x hx hxν
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxν
      obtain ⟨a0, a1, a2, a3, a4⟩ := hνne i hi
      rcases Finset.mem_union.mp hx with hx | hx
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h | h <;> contradiction
      · obtain ⟨l, hl, hlν⟩ := Finset.mem_image.mp hx
        exact hνψ i hi l hl hlν.symm
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj1,
      Finset.sum_image fun x hx y hy hxy => hψinj (Finset.mem_coe.mpr hx)
        (Finset.mem_coe.mpr hy) hxy,
      Finset.sum_image fun x hx y hy hxy => hνinj (Finset.mem_coe.mpr hx)
        (Finset.mem_coe.mpr hy) hxy]
    rw [Finset.sum_insert (by simp [h01, h02, h03, h04]),
      Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
      Finset.sum_insert (by simp [h34]), Finset.sum_singleton]
    have hdψC : ∀ l ∈ Finset.Icc 1 (k - 1), (δ : ℂ) * (deg (ψ l) : ℂ) =
        ((δ₀ * deg c₀ : ℤ) : ℂ) + ((δ₁ * deg c₁ : ℤ) : ℂ) := fun l hl => by
      exact_mod_cast hdψ l hl
    have hdνC : ∀ i ∈ Finset.range k, (δ : ℂ) * (deg (ν i) : ℂ) =
        ((δ₀ * deg c₀ : ℤ) : ℂ) + ((δ₁ * deg c₁ : ℤ) : ℂ) := fun i hi => by
      exact_mod_cast hdν i hi
    have hd4C : (δ₄ : ℂ) * (deg c₄ : ℂ) =
        -(((δ₀ * deg c₀ : ℤ) : ℂ) + ((δ₂ * deg c₂ : ℤ) : ℂ)) := by
      have h : δ₄ * deg c₄ = -(δ₀ * deg c₀ + δ₂ * deg c₂) := by linarith [hd024]
      exact_mod_cast h
    have hk1' : (((k - 1 + 1 - 1 : ℕ)) : ℂ) = (k : ℂ) - 1 := by
      rw [show k - 1 + 1 - 1 = k - 1 by omega, Nat.cast_sub (by omega), Nat.cast_one]
    have hψpart : ∑ l ∈ Finset.Icc 1 (k - 1), (basis.representation (ψ l)).character t ^ 3 /
        (basis.representation (ψ l)).character 1 = ((k : ℂ) - 1) * ((1 + (e : ℂ) * qC) ^ 3 /
          (((δ₀ * deg c₀ : ℤ) : ℂ) + ((δ₁ * deg c₁ : ℤ) : ℂ))) := by
      rw [Finset.sum_congr rfl fun (l : ℕ) (hl : l ∈ Finset.Icc 1 (k - 1)) => by
        rw [hvalψ l hl, hdeg1 (ψ l), sign_cube_div hδ, hdψC l hl], Finset.sum_const,
        Nat.card_Icc, nsmul_eq_mul, hk1']
    have hνpart : ∑ i ∈ Finset.range k, (basis.representation (ν i)).character t ^ 3 /
        (basis.representation (ν i)).character 1 = (k : ℂ) * ((-(1 + (e : ℂ) * qC)) ^ 3 /
          (((δ₀ * deg c₀ : ℤ) : ℂ) + ((δ₁ * deg c₁ : ℤ) : ℂ))) := by
      rw [Finset.sum_congr rfl fun (i : ℕ) (hi : i ∈ Finset.range k) => by
        rw [hvalν i hi, hdeg1 (ν i), sign_cube_div hδ, hdνC i hi], Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    rw [hψpart, hνpart, hval0, hval1, hval2, hval3, hval4, hdeg1, hdeg1, hdeg1, hdeg1, hdeg1,
      sign_cube_div hδ₀, sign_cube_div hδ₁, sign_cube_div hδ₂, sign_cube_div hδ₃,
      sign_cube_div hδ₄, hd4C, div_neg]
    push_cast
    rcases he with rfl | rfl <;> ring
  refine ⟨e, δ₀ * deg c₀, δ₁ * deg c₁, δ₂ * deg c₂, δ₃ * deg c₃, c₀, he1, he3, he, hqe,
    ha hδ₀ hc₀B, ha hδ₁ hc₁B, ha hδ₂ hc₂B, ha hδ₃ hc₃B, h01', h02', hd0123, ?_, hcg0, hcg1, hcg2,
    hcg3, hS, ?_, hc₀B, ?_⟩
  ·
    have h : (((1 : ℚ) / (δ₀ * deg c₀ : ℤ) + (((p ^ f : ℕ) : ℤ) : ℚ) ^ 2 / (δ₁ * deg c₁ : ℤ) +
        (((p ^ f : ℕ) : ℤ) : ℚ) ^ 2 / (δ₂ * deg c₂ : ℤ) + 1 / (δ₃ * deg c₃ : ℤ) : ℚ) : ℂ) =
        ((0 : ℚ) : ℂ) := by
      have h' := hR2
      rw [hqC] at h'
      push_cast at h' ⊢
      exact h'
    exact_mod_cast h
  ·
    intro x hx hx1 hΘx hEx
    have hΘ := hΘv x hx
    have hE := hEv 1 hk1 x hx
    rw [show (2 : ℤ) * ((1 : ℕ) : ℤ) = 2 by norm_num] at hE
    rw [hΘx] at hΘ
    rw [hEx] at hE
    have hdx : deg x = 1 := by simp [hdegdef, hx1]
    by_cases hx0 : x = c₀
    · rw [hx0] at hΘ hdx
      simp only [ite_true, h01, h02, h03, ite_false, mul_one, mul_zero, add_zero] at hΘ
      rw [hdx, ← hΘ, mul_one]
    by_cases hx1' : x = c₁
    · exfalso
      rw [hx1'] at hΘ hdx
      simp only [ite_true, h10, h12, h13, ite_false, mul_one, mul_zero, add_zero,
        zero_add] at hΘ
      have ha1 : δ₁ * deg c₁ = 1 := by rw [hdx, ← hΘ, mul_one]
      have h := one_lt_abs_of_signed_degree_congruences hK2 hqe (ha hδ₁ hc₁B) (Or.inl hcg1)
      rw [ha1] at h
      norm_num at h
    by_cases hx2 : x = c₂
    · exfalso
      rw [hx2] at hE
      simp [h20, h21, (hψc 1 hk1).2.2.1] at hE
    by_cases hx3 : x = c₃
    · exfalso
      rw [hx3] at hE
      simp [h30, h31, (hψc 1 hk1).2.2.2.1] at hE
    · exfalso
      simp [hx0, hx1', hx2, hx3] at hΘ
  ·
    intro ha0
    have hδ0 : δ₀ = 1 ∧ deg c₀ = 1 := by
      have hpos := hdegpos c₀ hc₀B
      rcases hδ₀ with rfl | rfl
      · exact ⟨rfl, by linarith⟩
      · exfalso
        linarith
    refine ⟨?_, fun y hy => ?_⟩
    · have h := hδ0.2
      simp only [hdegdef] at h
      exact_mod_cast h
    · rw [hval c₀ hc₀B y hy, hU0, hV0, hδ0.1]
      push_cast
      ring

end CFSG.Semidihedral.FieldFactorOne
