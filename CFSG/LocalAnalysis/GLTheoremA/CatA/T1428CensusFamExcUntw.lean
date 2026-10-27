module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamExcTL
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResKac

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.RecipeExcLang CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Dickson.Sec6.I1431
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem isTypeL2_of_catalogIs_isL2n {X : Type} [Group X] {r : ℕ} (hr : Odd r)
    (h : catalogIs (X ⧸ Subgroup.center X) (S10.isL2n r)) : IsTypeL2 (2 ^ r) X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isL2n] at hi
  | alternating m hm =>
      simp only [S10.isL2n] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact absurd hr (by norm_num : ¬ Odd 2)
  | sporadic s => simp [S10.isL2n] at hi
  | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A n q =>
          rcases n with _ | _ | n <;> simp [S10.isL2n] at hi
          obtain ⟨hp, hn⟩ := hi
          haveI : Fact q.p.Prime := ⟨q.prime_p⟩
          refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, ?_,
            ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)).trans
              (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
                (GaloisField q.p q.exponent))⟩⟩
          rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp, hn]
      | _ => simp [S10.isL2n] at hi



private theorem exc_untw_three_components_false {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hKac : ExcKac τ) {K : Type} [Field K]
    [Finite K] (hK2 : ringChar K = 2)
    (hinn : ∀ β : MulAut ↥(adjointGroup τ K), β ∈ innAutDerived ↥(adjointGroup τ K) →
      β ^ 3 = 1 → β ≠ 1 → ∃ h ∈ inndiagGroup τ K,
        (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1)
    (β : MulAut ↥(adjointGroup τ K)) (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {q : ℕ} (hq8 : 8 ≤ q) {J₁ J₂ J₃ : Subgroup ↥(adjointGroup τ K)}
    (hJ₁ : IsComponentOf J₁ (fixSubgroup β)) (hJ₂ : IsComponentOf J₂ (fixSubgroup β))
    (hJ₃ : IsComponentOf J₃ (fixSubgroup β)) (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃)
    (hL₁ : IsTypeL2 q ↥J₁) (hL₂ : IsTypeL2 q ↥J₂) (hL₃ : IsTypeL2 q ↥J₃) : False := by
  classical
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := hinn β hβmem hβ3 hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hpℓ : 3 ≠ ringChar K := by rw [hK2]; norm_num
  have hpK : ¬ 3 ∣ Nat.card K := by
    intro h'
    rw [hK, hK2] at h'
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp3 Nat.prime_two).1 (hp3.dvd_of_dvd_pow h'))
      (by norm_num)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp3 (by norm_num) hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl | rfl <;> simp) hp3 (by norm_num)
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h' | h' <;> exact single_edge_perfect τ K (by simp [h'])
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr1, hFr2⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ5 hp3 hpK hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp3 (by rw [hℓL]; exact hpℓ.symm)
  exact exc_three_components_false hτ hKac (by exact_mod_cast hpL) S ι hinj hrange hT hap h1 β
    hconj hq8 hJ₁ hJ₂ hJ₃ h12 h13 h23 hL₁ hL₂ hL₃


private theorem exc_untw_census_of_equiv {S : Type} [Group S] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hKac : ExcKac τ) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2)
    (hinn : ∀ β : MulAut ↥(adjointGroup τ K), β ∈ innAutDerived ↥(adjointGroup τ K) →
      β ^ 3 = 1 → β ≠ 1 → ∃ h ∈ inndiagGroup τ K,
        (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1)
    (eK : S ≃* ↥(adjointGroup τ K)) (η : MulAut S) (hmem : η ∈ innAutDerived S) (hη3 : η ^ 3 = 1)
    (hη1 : η ≠ 1) {r : ℕ} (hr : Odd r) (hr1 : 1 < r) {J₁ J₂ J₃ : Subgroup S}
    (hJ₁ : IsComponentOf J₁ (fixSubgroup η)) (hJ₂ : IsComponentOf J₂ (fixSubgroup η))
    (hJ₃ : IsComponentOf J₃ (fixSubgroup η)) (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃)
    (hL1 : catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r))
    (hL2 : catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r))
    (hL3 : catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r)) : False := by
  classical
  let β : MulAut ↥(adjointGroup τ K) := MulAut.congr eK η
  have hβmem : β ∈ innAutDerived ↥(adjointGroup τ K) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr eK).2 hmem
  have hβ3 : β ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr eK) η 3
    rw [hη3, map_one] at h3
    exact h3.symm
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hη1
    exact (MulAut.congr eK).injective (by rw [map_one]; exact h1)
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup eK η
  have hJ' : ∀ {J : Subgroup S}, IsComponentOf J (fixSubgroup η) →
      IsComponentOf (J.map eK.toMonoidHom) (fixSubgroup β) := by
    intro J hJ
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eK hJ
    exact hfix ▸ h1
  have hLT : ∀ {J : Subgroup S}, IsTypeL2 (2 ^ r) ↥J → IsTypeL2 (2 ^ r) ↥(J.map eK.toMonoidHom) :=
    fun {J} h => p6_isTypeL2_of_equiv (J.equivMapOfInjective eK.toMonoidHom eK.injective) h
  have hq8 : 8 ≤ 2 ^ r := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨c, hc⟩ := hr; omega)
  exact exc_untw_three_components_false hτ hKac hK2 hinn β hβmem hβ3 hβ1 hq8 (hJ' hJ₁) (hJ' hJ₂)
    (hJ' hJ₃) (fun h => h12 (Subgroup.map_injective eK.injective h))
    (fun h => h13 (Subgroup.map_injective eK.injective h))
    (fun h => h23 (Subgroup.map_injective eK.injective h))
    (hLT (isTypeL2_of_catalogIs_isL2n hr hL1)) (hLT (isTypeL2_of_catalogIs_isL2n hr hL2))
    (hLT (isTypeL2_of_catalogIs_isL2n hr hL3))

theorem censusBodyF4 : CensusBodyF4 := by
  intro q hv hq2 η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  exfalso
  obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  haveI := hKc
  have hchar : ringChar K = 2 := (ringChar.eq K q.p).trans hq2
  exact exc_untw_census_of_equiv (τ := .F4) (Or.inl rfl) excKac_f4 hchar
    (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_F4 β hβ hβp hβ1) eK η hmem hη3 hη1
    hr hr1 hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3

theorem censusBodyE6 : CensusBodyE6 := by
  intro q hv hq2 η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  exfalso
  obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  haveI := hKc
  have hchar : ringChar K = 2 := (ringChar.eq K q.p).trans hq2
  exact exc_untw_census_of_equiv (τ := .E6) (Or.inr (Or.inl rfl)) excKac_e6 hchar
    (fun β hβ hβp hβ1 =>
      exists_inndiag_of_mem_innAutDerived_E (Or.inl rfl) Nat.prime_three β hβ hβp hβ1)
    eK η hmem hη3 hη1 hr hr1 hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3

theorem censusBodyE7 : CensusBodyE7 := by
  intro q hv hq2 η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  exfalso
  obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
  haveI := hKc
  have hchar : ringChar K = 2 := (ringChar.eq K q.p).trans hq2
  exact exc_untw_census_of_equiv (τ := .E7) (Or.inr (Or.inr (Or.inl rfl))) excKac_e7 hchar
    (fun β hβ hβp hβ1 =>
      exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inl rfl)) Nat.prime_three β hβ hβp hβ1)
    eK η hmem hη3 hη1 hr hr1 hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3

theorem censusBodyE8 : CensusBodyE8 := by
  intro q hv hq2 η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  exfalso
  obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  haveI := hKc
  have hchar : ringChar K = 2 := (ringChar.eq K q.p).trans hq2
  exact exc_untw_census_of_equiv (τ := .E8) (Or.inr (Or.inr (Or.inr rfl))) excKac_e8 hchar
    (fun β hβ hβp hβ1 =>
      exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inr rfl)) Nat.prime_three β hβ hβp hβ1)
    eK η hmem hη3 hη1 hr hr1 hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3

end CFSG.LocalAnalysis.GLTheoremA.T1428
