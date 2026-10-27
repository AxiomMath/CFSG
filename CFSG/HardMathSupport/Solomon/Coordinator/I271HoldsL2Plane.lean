module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2PlaneCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard
public import CFSG.RankThree.PartTwo.KFacts.KS10L27

public noncomputable section

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator

namespace CFSG.HardMathSupport.Solomon.Coordinator.L2Plane

variable {F : Type} [Field F] [Finite F]

open CFSG.Open

open CFSG.ComponentClassification.CatalogueBHigherLinearField in
theorem card_fixedField_eq {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hF : Nat.card F = p ^ n)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) :
    Nat.card (fixedField F σ) = p ^ (n / 3) := by
  have h := (CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf hp hn hF σ hσ).2
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [mem_fixedField]; rfl)

open CFSG.ComponentClassification.CatalogueBHigherLinearField in
theorem bound_twentySeven (hF : Nat.card F = 27) :
    ∀ σ : F ≃+* F, orderOf σ = 3 → ∀ A₀ : Subgroup (PGL2 F), IsElemAbelian 3 A₀ →
      (∀ g ∈ A₀, pgl2FieldAut F σ g = g) → Nat.card A₀ ≤ 3 := by
  intro σ hσ A₀ hA₀ hfix
  have hF0 : Nat.card (fixedField F σ) = 3 := by
    have := card_fixedField_eq (n := 3) Nat.prime_three (by norm_num) (by rw [hF]; norm_num) σ hσ
    simpa using this
  have hle : A₀ ≤ (subfieldPGLMap (Fin 2) F (fixedField F σ)).range := by
    intro g hg
    rw [← pgl_fixed_iff_mem_subfield_range (Fin 2) F σ g, pglFieldAut_two]
    exact hfix g hg
  have : Finite (fixedField F σ) := inferInstance
  have hrange : Nat.card (subfieldPGLMap (Fin 2) F (fixedField F σ)).range = 24 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (subfieldPGLMap_injective (Fin 2) F (fixedField F σ))).toEquiv,
      CFSG.GorensteinWalter.pgl2_card_formula, hF0]
    norm_num
  have hdvd : Nat.card A₀ ∣ 24 := hrange ▸ Subgroup.card_dvd_of_le hle
  have hpg : IsPGroup 3 A₀ := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hA₀.2 x x.2)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  rw [hk] at hdvd ⊢
  by_contra hcon
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k ≤ 1 := by omega
    exact hcon (by calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
                      _ = 3 := by norm_num)
  have h9 : 9 ∣ 3 ^ k := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ∣ 3 ^ k := pow_dvd_pow 3 hk2
  have := h9.trans hdvd
  omega

theorem exists_psl_lift {g : PGL2 F} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ g' : PSL2 F, Matrix.ProjectiveSpecialLinearGroup.toPGL g' = g ∧ g' ≠ 1 ∧ g' ^ 3 = 1 := by
  have hodd : Odd (orderOf g) := by
    have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> rw [h] <;> decide
  obtain ⟨g', hg'⟩ := mem_psl2Range_of_odd g hodd
  refine ⟨g', hg', ?_, ?_⟩
  · rintro rfl
    exact hg1 (by rw [← hg', map_one])
  · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_pow, hg', hg3, map_one]

theorem mem_cSL_inl_toPGL (g' x : PSL2 F) :
    x ∈ cSL (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g') : PGammaL2 F) ↔
      g' * x * g'⁻¹ = x := by
  rw [mem_cSL, semilinearAction_inl, pglAction_toPGL, MulAut.conj_apply]

theorem top_of_dickson_twentySeven (hF : Nat.card F = 27)
    (K : Subgroup (PSL2 F)) (h27 : 27 ∣ Nat.card K) (hw : ∃ w ∈ K, orderOf w = 2) : K = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : Nat.card F = 3 ^ 3 := by rw [hF]; norm_num
  have hS : Nat.card (PSL2 F) = 9828 := by
    have := CFSG.GorensteinWalter.psl2_card_formula F
      ⟨3, 3, Nat.prime_three, by decide, by norm_num, hF3⟩
    rw [this, hF]
    norm_num
  obtain ⟨w, hwK, hw2⟩ := hw
  have h2K : 2 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K hwK
    rwa [hw2] at this
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF3 K with
    h | ⟨z, hz, hK, hcyc⟩ | ⟨z, hz, hK, hD⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨h5, -⟩ |
      ⟨m, t, ht1, ht2, N, C, hN, hNel, hNcard, hC, hCcard, hdisj, hsup⟩ | ⟨m, hm0, hm3, ⟨e⟩⟩ |
      ⟨m, hm0, hm2, -⟩
  · exfalso
    have h2 : orderOf (⟨w, hwK⟩ : K) ∣ Monoid.exponent K := Monoid.order_dvd_exponent _
    have h3 : Monoid.exponent K ∣ 3 := IsElementaryAbelian.exponent_dvd_p 3 K
    have h4 : orderOf (⟨w, hwK⟩ : K) = 2 := by rw [Subgroup.orderOf_mk, hw2]
    rw [h4] at h2
    have := h2.trans h3
    omega
  · exfalso
    rw [hF] at hz
    norm_num at hz
    have hz27 : 27 ∣ z := by rw [← hK]; exact h27
    rcases hz with hz | hz <;>
    · have := Nat.le_of_dvd (by norm_num) hz
      have := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hz (by norm_num)) hz27
      omega
  · exfalso
    rw [hF] at hz
    norm_num at hz
    have hz27 : 27 ∣ 2 * z := by rw [← hK]; exact h27
    have hz27' : 27 ∣ z := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hz27)
    rcases hz with hz | hz <;>
    · have := Nat.le_of_dvd (by norm_num) hz
      have := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hz (by norm_num)) hz27'
      omega
  · exfalso
    rw [Nat.card_congr e.toEquiv] at h27
    have : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide
    omega
  · exfalso
    norm_num at h16
  · exfalso
    norm_num at h5
  · exfalso
    have hcompl : N.IsComplement' C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hcard := hcompl.card_mul_card
    rw [hNcard, hCcard] at hcard
    have ht : t ∣ 13 := by simpa using ht2
    have hodd : Odd t := (by decide : Odd 13).of_dvd_nat ht
    have hK : Odd (Nat.card K) := by
      rw [← hcard]
      exact (Odd.pow (by decide : Odd 3)).mul hodd
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h2K)
  · rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with rfl | rfl
    · exfalso
      have hc : Nat.card (PSL2 (GaloisField 3 1)) = 12 := by
        have := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 1)
          ⟨3, 1, Nat.prime_three, by decide, le_refl _, GaloisField.card 3 1 one_ne_zero⟩
        rw [GaloisField.card 3 1 one_ne_zero] at this
        exact this
      rw [Nat.card_congr e.toEquiv, hc] at h27
      omega
    · refine Subgroup.eq_top_of_card_eq K ?_
      rw [Nat.card_congr e.toEquiv, hS]
      have := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 3)
        ⟨3, 3, Nat.prime_three, by decide, by norm_num, GaloisField.card 3 3 (by norm_num)⟩
      rw [GaloisField.card 3 3 (by norm_num)] at this
      exact this.trans (by norm_num)
  · exfalso
    rcases (Nat.dvd_prime Nat.prime_three).1 hm2 with h | h <;> omega

theorem gen_twentySeven (hF : Nat.card F = 27) :
    ∀ σ : F ≃+* F, orderOf σ = 3 → ∀ g : PGL2 F, g ≠ 1 → g ^ 3 = 1 → pgl2FieldAut F σ g = g →
      cSL (SemidirectProduct.inr σ : PGammaL2 F) ⊔ cSL (SemidirectProduct.inl g : PGammaL2 F) =
        ⊤ := by
  intro σ hσ g hg1 hg3 hfix
  obtain ⟨g', hg', hg'1, hg'3⟩ := exists_psl_lift hg3 hg1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  haveI : CharP F 3 := charP_of_card_eq_prime_pow (p := 3) (f := 3)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hS : Nat.card (PSL2 F) = 9828 := by
    have := CFSG.GorensteinWalter.psl2_card_formula F
      ⟨3, 3, Nat.prime_three, by decide, by norm_num, by rw [hF]; norm_num⟩
    rw [this, hF]
    norm_num
  apply top_of_dickson_twentySeven hF
  · have hpg : IsPGroup 3 (Subgroup.zpowers g') :=
      IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, orderOf_eq_prime hg'3 hg'1]; norm_num⟩
    obtain ⟨P, hP⟩ := hpg.exists_le_sylow
    have hPel := (CFSG.RankThree.PartTwo.KFacts.isElemAbelian_of_isPGroup_three_psl2 (K := F) (n := 3)
      (by rw [hF]; norm_num) P.isPGroup').1
    have hPle : (P : Subgroup (PSL2 F)) ≤
        cSL (SemidirectProduct.inl g : PGammaL2 F) := by
      intro x hx
      rw [← hg', mem_cSL_inl_toPGL]
      have := hPel.1.is_comm.comm ⟨g', hP (Subgroup.mem_zpowers g')⟩ ⟨x, hx⟩
      have h2 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h2
      rw [h2]
      group
    have h27P : 27 ∣ Nat.card P := by
      have h1 := Subgroup.card_mul_index (P : Subgroup (PSL2 F))
      rw [hS] at h1
      have h3 : ¬ 3 ∣ (P : Subgroup (PSL2 F)).index := P.not_dvd_index
      have hcop : Nat.Coprime 27 (P : Subgroup (PSL2 F)).index := by
        have : Nat.Coprime 3 (P : Subgroup (PSL2 F)).index :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
        simpa using this.pow_left 3
      have h27 : 27 ∣ Nat.card P * (P : Subgroup (PSL2 F)).index := by
        rw [h1]; norm_num
      exact hcop.dvd_of_dvd_mul_right h27
    exact h27P.trans (Subgroup.card_dvd_of_le (hPle.trans le_sup_right))
  · let A : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
    refine ⟨psl2QuotientMap F A, ?_, ?_⟩
    · apply Subgroup.mem_sup_left
      rw [mem_cSL, semilinearAction_inr]
      show psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) A) =
        QuotientGroup.mk' (Subgroup.center _) A
      rw [psl2RingEquiv_mk]
      congr 1
      apply Subtype.ext
      ext i j
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      fin_cases i <;> fin_cases j <;> simp [A]
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      apply orderOf_eq_prime
      · rw [← map_pow]
        apply (QuotientGroup.eq_one_iff _).2
        rw [Matrix.SpecialLinearGroup.mem_center_iff]
        refine ⟨-1, by simp, ?_⟩
        rw [Matrix.SpecialLinearGroup.coe_pow]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [A, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
      · intro h
        have h1 := (QuotientGroup.eq_one_iff _).1 h
        rw [Matrix.SpecialLinearGroup.mem_center_iff] at h1
        obtain ⟨r, -, hr⟩ := h1
        have := congrFun (congrFun hr 0) 1
        simp [A, Matrix.scalar_apply, Matrix.diagonal_apply] at this

theorem arith_even_contra {m e : ℕ} (hmodd : m % 2 = 1)
    (hS : ¬ 3 ^ (e + 1) ∣ (2 ^ (3 * m)) * ((2 ^ (3 * m)) ^ 2 - 1))
    (hK : 3 ^ e ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1)) : False := by
  set t : ℕ := 2 ^ m with ht
  have ht3 : t % 3 = 2 := by
    obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
    rw [ht, hj, pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  obtain ⟨a, ha⟩ : ∃ a, t = 3 * a + 2 := ⟨t / 3, by omega⟩
  have hsq : t ^ 2 - 1 = (3 * a + 1) * (3 * a + 3) := by
    rw [ha]
    have : (3 * a + 2) ^ 2 = (3 * a + 1) * (3 * a + 3) + 1 := by ring
    omega
  have hcop1 : Nat.Coprime (3 ^ e) t := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  have hcop2 : Nat.Coprime (3 ^ e) (3 * a + 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  rw [hsq] at hK
  have h1 := hcop1.dvd_of_dvd_mul_left hK
  have h2 := hcop2.dvd_of_dvd_mul_left h1
  have h3 : 3 ^ (e + 1) ∣ (3 * a + 3) * (3 * (3 * a * a + 3 * a + 1)) := by
    rw [pow_succ]
    exact mul_dvd_mul h2 (dvd_mul_right 3 _)
  have hq : (3 * a + 3) * (3 * (3 * a * a + 3 * a + 1)) = (t ^ 3) + 1 := by
    rw [ha]; ring
  rw [hq] at h3
  apply hS
  have hS' : (2 ^ (3 * m)) = t ^ 3 := by rw [ht, ← pow_mul, mul_comm, pow_mul]
  rw [hS']
  have : t ^ 3 + 1 ∣ t ^ 3 * ((t ^ 3) ^ 2 - 1) := by
    have hq1 : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
    have : (t ^ 3) ^ 2 - 1 = (t ^ 3 - 1) * (t ^ 3 + 1) := by
      obtain ⟨u, hu⟩ : ∃ u, t ^ 3 = u + 1 := ⟨t ^ 3 - 1, by omega⟩
      rw [hu]
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [this]
    exact Dvd.intro_left (t ^ 3 * (t ^ 3 - 1)) (by rw [mul_assoc])
  exact h3.trans this

theorem two_pow_odd_mod_three {n : ℕ} (hn : n % 2 = 1) : 2 ^ n % 3 = 2 := by
  obtain ⟨j, hj⟩ : ∃ j, n = 2 * j + 1 := ⟨n / 2, by omega⟩
  rw [hj, pow_succ, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

theorem card_psl2_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    Nat.card (PSL2 K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [← Nat.card_congr (slEquivPsl2 K).toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hK]

theorem top_of_dickson_even {n m : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : n = 3 * m) (hm : 3 ≤ m) (hmodd : m % 2 = 1) (K : Subgroup (PSL2 F))
    (h3 : ∀ k, 3 ^ k ∣ Nat.card (PSL2 F) → 3 ^ k ∣ Nat.card K) (h2 : 2 ^ m ∣ Nat.card K) :
    K = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have hnodd : n % 2 = 1 := by omega
  have hS : Nat.card (PSL2 F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := card_psl2_of_charTwo hF
  have hq3 : 2 ^ n % 3 = 2 := two_pow_odd_mod_three hnodd
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h8 : 8 ∣ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ∣ 2 ^ m := pow_dvd_pow 2 hm
  have h3S : 3 ∣ Nat.card (PSL2 F) := by
    rw [hS]
    apply Dvd.dvd.mul_left
    have : ((2 ^ n) ^ 2) % 3 = 1 := by norm_num [Nat.pow_mod, hq3]
    have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have h3K : 3 ∣ Nat.card K := by simpa using h3 1 (by simpa using h3S)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
  have hodd1 : Odd (2 ^ n - 1) := by
    have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rcases h2n with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hodd2 : Odd (2 ^ n + 1) := by
    rcases h2n with ⟨c, hc⟩
    exact ⟨c, by omega⟩
  have hgcd : (2 ^ n - 1).gcd 2 = 1 := by
    have : Nat.Coprime (2 ^ n - 1) 2 := Nat.coprime_two_right.2 hodd1
    exact this
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF K with
    h | ⟨z, hz, hK, hcyc⟩ | ⟨z, hz, hK, hD⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, ht1, ht2, N, C, hN, hNel, hNcard, hC, hCcard, hdisj, hsup⟩ | ⟨m', hm0, hm3, ⟨e⟩⟩ |
      ⟨m', hm0, hm2, -⟩
  · exfalso
    have h1 : orderOf x ∣ Monoid.exponent K := Monoid.order_dvd_exponent x
    have h2' : Monoid.exponent K ∣ 2 := IsElementaryAbelian.exponent_dvd_p 2 K
    rw [hx] at h1
    have := h1.trans h2'
    omega
  · exfalso
    rw [hF, hgcd] at hz
    simp only [Nat.div_one] at hz
    have hzodd : Odd z := by
      rcases hz with hz | hz
      · exact hodd1.of_dvd_nat hz
      · exact hodd2.of_dvd_nat hz
    have h2z : 2 ∣ z := by
      rw [← hK]
      exact (dvd_pow_self 2 (by omega)).trans h2
    exact (Nat.not_even_iff_odd.2 hzodd) (even_iff_two_dvd.2 h2z)
  · exfalso
    rw [hF, hgcd] at hz
    simp only [Nat.div_one] at hz
    have hzodd : Odd z := by
      rcases hz with hz | hz
      · exact hodd1.of_dvd_nat hz
      · exact hodd2.of_dvd_nat hz
    have h2z : 2 ^ (m - 1) ∣ z := by
      have : 2 * 2 ^ (m - 1) ∣ 2 * z := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega), ← hK]
        exact h2
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
    have h2z' : 2 ∣ z := (dvd_pow_self 2 (by omega)).trans h2z
    exact (Nat.not_even_iff_odd.2 hzodd) (even_iff_two_dvd.2 h2z')
  · exfalso
    have hc : Nat.card K = 12 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    rw [hc] at h2
    have := h8.trans h2
    omega
  · exfalso
    have : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
    have : 1 ≤ 2 ^ (2 * n) := Nat.one_le_pow _ _ (by norm_num)
    omega
  · exfalso
    have hc : Nat.card K = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    rw [hc] at h2
    have := h8.trans h2
    omega
  · exfalso
    have hcompl : N.IsComplement' C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hcard := hcompl.card_mul_card
    rw [hNcard, hCcard] at hcard
    rw [hgcd] at ht2
    simp only [Nat.div_one] at ht2
    have h3t : 3 ∣ t := by
      have h3c : 3 ∣ 2 ^ m' * t := by rw [hcard]; exact h3K
      exact (Nat.Coprime.pow_right m' (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h3c
    have := h3t.trans ht2
    have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  · have hcardK : Nat.card K = 2 ^ m' * ((2 ^ m') ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      haveI : CharP (GaloisField 2 m') 2 := inferInstance
      exact card_psl2_of_charTwo (GaloisField.card 2 m' hm0)
    by_cases hmn : m' = n
    · subst hmn
      exact Subgroup.eq_top_of_card_eq K (by rw [hcardK, hS])
    · exfalso
      obtain ⟨d, hd⟩ := hm3
      have hnd : Odd (m' * d) := by rw [← hd]; exact Nat.odd_iff.2 hnodd
      have hdodd : Odd d := (Nat.odd_mul.1 hnd).2
      have hd1 : d ≠ 1 := fun h => hmn (by rw [hd, h, mul_one])
      have hd3 : 3 ≤ d := by
        obtain ⟨c, hc⟩ := hdodd
        omega
      have hm'm : m' ≤ m := by
        have : m' * 3 ≤ m' * d := Nat.mul_le_mul_left m' hd3
        omega
      have hodd' : Odd ((2 ^ m') ^ 2 - 1) := by
        have : 2 ∣ (2 ^ m') ^ 2 := dvd_pow (dvd_pow_self 2 hm0) (by norm_num)
        have : 1 ≤ (2 ^ m') ^ 2 := Nat.one_le_pow _ _ (by positivity)
        rcases ‹2 ∣ (2 ^ m') ^ 2› with ⟨c, hc⟩
        exact ⟨c - 1, by omega⟩
      have hmm' : m ≤ m' := by
        rw [hcardK] at h2
        have hcop : Nat.Coprime (2 ^ m) ((2 ^ m') ^ 2 - 1) :=
          Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd')
        have := hcop.dvd_of_dvd_mul_right h2
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
      have hmeq : m' = m := le_antisymm hm'm hmm'
      subst hmeq
      subst hn
      have hSne : Nat.card (PSL2 F) ≠ 0 := Nat.card_pos.ne'
      have h3e := h3 _ (Nat.ordProj_dvd (Nat.card (PSL2 F)) 3)
      have hnd3 := Nat.pow_succ_factorization_not_dvd hSne Nat.prime_three
      rw [hS] at hnd3
      rw [hcardK, hS] at h3e
      exact arith_even_contra hmodd hnd3 h3e
  · exfalso
    have : 2 ∣ n := (dvd_mul_right 2 m').trans hm2
    omega

theorem bound_even {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ∀ σ : F ≃+* F, orderOf σ = 3 → ∀ A₀ : Subgroup (PGL2 F), IsElemAbelian 3 A₀ →
      (∀ g ∈ A₀, pgl2FieldAut F σ g = g) → Nat.card A₀ ≤ 3 := by
  intro σ _ A₀ hA₀ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hinj : Function.Injective f := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hle : A₀ ≤ f.range := by
    intro g hg
    have hg3 : g ^ 3 = 1 := hA₀.2 g hg
    have hodd : Odd (orderOf g) := by
      have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> rw [h] <;> decide
    exact mem_psl2Range_of_odd g hodd
  let E : Subgroup (PSL2 F) := A₀.comap f
  have hEmap : E.map f = A₀ := Subgroup.map_comap_eq_self hle
  have hEcard : Nat.card E = Nat.card A₀ := by
    calc Nat.card E = Nat.card (E.map f) := (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card A₀ := by rw [hEmap]
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hA₀.2 (f x) hx
  have hpg : IsPGroup 3 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE3 x x.2)⟩
  obtain ⟨R, hR⟩ := hpg.exists_le_sylow
  have h7 : 7 ≤ Nat.card F := by
    rw [hF]
    calc 7 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcop : Nat.Coprime 3 (Nat.card F) := by
    rw [hF]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hcyc : IsCyclic (R : Subgroup (PSL2 F)) :=
    psl2_sylow_isCyclic_of_coprime_field_card F hF h7 3 (by norm_num) hcop R
  classical
  haveI := Fintype.ofFinite (R : Subgroup (PSL2 F))
  have hbound : Nat.card {x : (R : Subgroup (PSL2 F)) // x ^ 3 = 1} ≤ 3 := by
    have := IsCyclic.card_pow_eq_one_le (α := (R : Subgroup (PSL2 F))) (n := 3) (by norm_num)
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using this
  rw [← hEcard]
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : E => (⟨⟨x.1, hR x.2⟩, Subtype.ext (hE3 x.1 x.2)⟩ :
      {y : (R : Subgroup (PSL2 F)) // y ^ 3 = 1})) ?_) hbound
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : {y : (R : Subgroup (PSL2 F)) // y ^ 3 = 1} => ((z : _) : PSL2 F)) hxy
  exact this

theorem psl2UpperUnipotentHom_inj (K : Type) [Field K] :
    Function.Injective (psl2UpperUnipotentHom K) := by
  intro x y hxy
  have hcenter : sl2UpperUnipotent (x.toAdd - y.toAdd) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    have hq : psl2QuotientMap K (sl2UpperUnipotent (x.toAdd - y.toAdd)) = 1 := by
      rw [sub_eq_add_neg, ← sl2UpperUnipotent_mul, map_mul, ← sl2UpperUnipotent_inv, map_inv]
      change psl2UpperUnipotentHom K x * (psl2UpperUnipotentHom K y)⁻¹ = 1
      rw [hxy, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hscalar := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have h01 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply Multiplicative.ext
  apply sub_eq_zero.mp
  simpa [sl2UpperUnipotent] using h01.symm

theorem fixedRoot_card_dvd (σ : F ≃+* F) :
    Nat.card {t : F // σ t = t} ∣ Nat.card (cSL (SemidirectProduct.inr σ : PGammaL2 F)) := by
  let ψ := psl2UpperUnipotentHom F
  have hψ : Function.Injective ψ := psl2UpperUnipotentHom_inj F
  let T₀ : Subgroup (Multiplicative F) := (cSL (SemidirectProduct.inr σ : PGammaL2 F)).comap ψ
  have hT₀ : ∀ t : F, Multiplicative.ofAdd t ∈ T₀ ↔ σ t = t := by
    intro t
    have h1 : psl2FieldAut F σ (ψ (Multiplicative.ofAdd t)) = ψ (Multiplicative.ofAdd (σ t)) := by
      show psl2FieldAut F σ (psl2QuotientMap F (sl2UpperUnipotent t)) =
        psl2QuotientMap F (sl2UpperUnipotent (σ t))
      rw [psl2FieldAut_apply]
      show psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (sl2UpperUnipotent t)) = _
      rw [psl2RingEquiv_mk]
      congr 1
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent]
    show ψ (Multiplicative.ofAdd t) ∈ cSL (SemidirectProduct.inr σ : PGammaL2 F) ↔ _
    rw [mem_cSL, semilinearAction_inr, h1, hψ.eq_iff]
    exact ⟨fun h => by simpa using h, fun h => by rw [h]⟩
  have hcard : Nat.card T₀ = Nat.card {t : F // σ t = t} :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.toAdd, (hT₀ _).1 x.2⟩
        invFun := fun t => ⟨Multiplicative.ofAdd t.1, (hT₀ _).2 t.2⟩
        left_inv := fun x => rfl
        right_inv := fun t => rfl }
  have hle : T₀.map ψ ≤ cSL (SemidirectProduct.inr σ : PGammaL2 F) := Subgroup.map_comap_le ψ _
  calc Nat.card {t : F // σ t = t} = Nat.card T₀ := hcard.symm
    _ = Nat.card (T₀.map ψ) := (Subgroup.card_map_of_injective hψ).symm
    _ ∣ _ := Subgroup.card_dvd_of_le hle

open CFSG.ComponentClassification.CatalogueBHigherLinearField in
theorem card_fixed_points_eq {n : ℕ} (hF : Nat.card F = 2 ^ n) (σ : F ≃+* F) (hσ : orderOf σ = 3)
    (hn : 1 ≤ n) {m : ℕ} (hm : n = 3 * m) : Nat.card {t : F // σ t = t} = 2 ^ m := by
  have h := (CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf
    Nat.prime_two hn hF σ hσ).2
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num)] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)

theorem gen_even {n : ℕ} (hn : 3 < n) (hnodd : n % 2 = 1)
    (hF : Nat.card F = 2 ^ n) :
    ∀ σ : F ≃+* F, orderOf σ = 3 → ∀ g : PGL2 F, g ≠ 1 → g ^ 3 = 1 → pgl2FieldAut F σ g = g →
      cSL (SemidirectProduct.inr σ : PGammaL2 F) ⊔ cSL (SemidirectProduct.inl g : PGammaL2 F) =
        ⊤ := by
  intro σ hσ g hg1 hg3 hfix
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g', hg', hg'1, hg'3⟩ := exists_psl_lift hg3 hg1
  obtain ⟨m, hm⟩ := (CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf
    Nat.prime_two (by omega) hF σ hσ).1
  have hm3 : 3 ≤ m := by omega
  have hmodd : m % 2 = 1 := by omega
  apply top_of_dickson_even hF hm hm3 hmodd
  · intro k hk
    have hpg : IsPGroup 3 (Subgroup.zpowers g') :=
      IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, orderOf_eq_prime hg'3 hg'1]; norm_num⟩
    obtain ⟨R, hR⟩ := hpg.exists_le_sylow
    have h7 : 7 ≤ Nat.card F := by
      rw [hF]
      calc 7 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcop : Nat.Coprime 3 (Nat.card F) := by
      rw [hF]
      exact Nat.Coprime.pow_right n (by norm_num)
    have hcyc : IsCyclic (R : Subgroup (PSL2 F)) :=
      psl2_sylow_isCyclic_of_coprime_field_card F hF h7 3 (by norm_num) hcop R
    have hRle : (R : Subgroup (PSL2 F)) ≤ cSL (SemidirectProduct.inl g : PGammaL2 F) := by
      intro x hx
      rw [← hg', mem_cSL_inl_toPGL]
      have := (IsCyclic.commGroup (α := (R : Subgroup (PSL2 F)))).mul_comm
        ⟨g', hR (Subgroup.mem_zpowers g')⟩ ⟨x, hx⟩
      have h2 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h2
      rw [h2]
      group
    have h1 := Subgroup.card_mul_index (R : Subgroup (PSL2 F))
    have h3idx : ¬ 3 ∣ (R : Subgroup (PSL2 F)).index := R.not_dvd_index
    have hcop' : Nat.Coprime (3 ^ k) (R : Subgroup (PSL2 F)).index :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3idx)
    have hk' : 3 ^ k ∣ Nat.card R * (R : Subgroup (PSL2 F)).index := by rw [h1]; exact hk
    have hkR : 3 ^ k ∣ Nat.card R := hcop'.dvd_of_dvd_mul_right hk'
    exact hkR.trans (Subgroup.card_dvd_of_le (hRle.trans le_sup_right))
  · have := fixedRoot_card_dvd σ
    rw [card_fixed_points_eq hF σ hσ (by omega) hm] at this
    exact this.trans (Subgroup.card_dvd_of_le le_sup_left)

theorem planeCase_twentySeven (hF : Nat.card F = 27) :
    PlaneCase F := ⟨bound_twentySeven hF, gen_twentySeven hF⟩

theorem planeCase_even {n : ℕ} (hn : 3 < n) (hnodd : n % 2 = 1)
    (hF : Nat.card F = 2 ^ n) : PlaneCase F :=
  ⟨bound_even (by omega) hF, gen_even hn hnodd hF⟩

end CFSG.HardMathSupport.Solomon.Coordinator.L2Plane

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem l2FieldPlane_holds : L2FieldPlane :=
  L2Plane.l2FieldPlane_of_case fun F _ _ h => by
    rcases h with h | ⟨n, hn, hn3, hF⟩
    · exact L2Plane.planeCase_twentySeven h
    · exact L2Plane.planeCase_even hn3 (by omega) hF

end CFSG.HardMathSupport.Solomon.Coordinator
