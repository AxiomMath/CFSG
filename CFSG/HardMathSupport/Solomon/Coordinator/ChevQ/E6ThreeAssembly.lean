module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighExc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree

theorem isTwoPow_of_card_eq {q : TauCeti.PrimePower} {k : ℕ} (h : q.card = 2 ^ k) :
    IsTwoPow q k := by
  have h' : q.p ^ q.exponent = 2 ^ k := by rw [← TauCeti.PrimePower.card_def, h]
  have hp2 : q.p = 2 := by
    have hd : q.p ∣ 2 ^ k := h' ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hd)
  refine ⟨hp2, ?_⟩
  rw [hp2] at h'
  exact Nat.pow_right_injective le_rfl h'

theorem card_ne_four_of_not_excIndex_e6 {q : TauCeti.PrimePower} (h : ¬ ExcIndex 3 (.E6 q)) :
    q.card ≠ 4 := by
  intro hq
  refine h (Or.inr ⟨rfl, Or.inr (Or.inl ?_)⟩)
  show IsTwoPow q 1 ∨ IsTwoPow q 2 ∨ IsTwoPow q 3
  exact Or.inr (Or.inl (isTwoPow_of_card_eq (by rw [hq]; norm_num)))

theorem card_ne_of_not_excIndex_twE6 {q : TauCeti.PrimePower} (h : ¬ ExcIndex 3 (.twistedE6 q)) :
    q.card ≠ 2 ∧ q.card ≠ 4 ∧ q.card ≠ 8 := by
  refine ⟨fun hq => h (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl ?_))⟩),
    fun hq => h (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩),
    fun hq => h (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))⟩)⟩
  · show IsTwoPow q 1
    exact isTwoPow_of_card_eq (by rw [hq]; norm_num)
  · show IsTwoPow q 2
    exact isTwoPow_of_card_eq (by rw [hq]; norm_num)
  · show IsTwoPow q 3
    exact isTwoPow_of_card_eq (by rw [hq]; norm_num)

theorem ringChar_ne_three_of_not_dvd_card {K : Type} [Field K] [Finite K]
    (h : ¬ 3 ∣ Nat.card K) : ringChar K ≠ 3 := by
  classical
  intro h3
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  apply h
  rw [Nat.card_eq_fintype_card, hn, h3]
  exact dvd_pow_self 3 n.ne_zero

section Assembly

set_option linter.unusedSectionVars false


theorem seitzGoodOuterHighAt_e6_of_cubes (hF : E6FieldCubes) (hP : E6DiagParCubes)
    (hN : E6DiagNonParCubes) :
    SeitzGoodOuterHighAt fun d p => p = 3 ∧ ∃ q : PrimePower, d.1 = .E6 q ∧ 3 ∣ q.card - 1 := by
  intro p _ _ S _ _ _ _ d hdp he hpd _ hx _ _ E hE hc hout
  obtain ⟨rfl, q, hdq, h3⟩ := hdp
  obtain ⟨d, hv⟩ := d
  simp only at hdq
  subst hdq
  have hpq : 3 ≠ q.p := by simpa using hpd
  have hq4 : q.card ≠ 4 := card_ne_four_of_not_excIndex_e6 hx
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  obtain ⟨ψ⟩ := he
  let θ : S ≃* adjointGroup Tag.E6 K := ψ.trans e
  have hE' : IsElemAbelian 3 (E.map (MulAut.congr θ).toMonoidHom) :=
    CFSG.LieType.SeitzGeneration.isElemAbelian_map_congr θ hE
  have hc' : Nat.card (E.map (MulAut.congr θ).toMonoidHom) = 3 ^ 3 :=
    (CFSG.LieType.SeitzGeneration.card_map_congr θ E).trans hc
  have hout' := CFSG.LieType.SeitzGeneration.not_le_range_conj_map_congr θ hout
  have hpK : ringChar K ≠ 3 := by rw [ringChar.eq K q.p]; exact fun h => hpq h.symm
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  have hK8 : Nat.card K ≠ 8 := by
    intro h
    rw [h] at hK3
    omega
  have hK4 : Nat.card K ≠ 4 := by rw [hK]; exact hq4
  have htop : seitzHyperGamma 3 (E.map (MulAut.congr θ).toMonoidHom) = ⊤ := by
    by_cases hdiag : E.map (MulAut.congr θ).toMonoidHom ≤ e6Inndiag K
    · by_cases hR : E6NormalizesR K (E.map (MulAut.congr θ).toMonoidHom)
      · exact hP K hpK _ hE' hc' hdiag hR
      · exact hN K hpK hK3 hK4 _ hE' hc' hdiag hout' hR
    · exact hF K hpK hK8 _ hE' hc' hdiag
  exact CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map θ
    (MulAut.congr θ).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
    (MulAut.congr θ).injective htop

theorem seitzGoodOuterHighAt_twE6_of_cubes (hF : TwE6FieldCubes) (hP : TwE6DiagParCubes)
    (hN : TwE6DiagNonParCubes) :
    SeitzGoodOuterHighAt fun d p => p = 3 ∧ ∃ q : PrimePower, d.1 = .twistedE6 q := by
  intro p _ _ S _ _ _ _ d hdp he hpd _ hx _ _ E hE hc hout
  obtain ⟨rfl, q, hdq⟩ := hdp
  obtain ⟨d, hv⟩ := d
  simp only at hdq
  subst hdq
  have hpq : 3 ≠ q.p := by simpa using hpd
  obtain ⟨hq2, -, hq8⟩ := card_ne_of_not_excIndex_twE6 hx
  have hq3 : ¬ 3 ∣ q.card := not_dvd_card_of_ne Nat.prime_three hpq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have hK2 : Nat.card K = q.card ^ 2 := by rw [hK, TauCeti.PrimePower.card_def]
  have hσ2 : ∀ c, σ c = c ^ q.card := fun c => by rw [hσ, TauCeti.PrimePower.card_def]
  have hpK : ringChar K ≠ 3 := by
    refine ringChar_ne_three_of_not_dvd_card fun h => hq3 ?_
    rw [hK2] at h
    exact Nat.prime_three.dvd_of_dvd_pow h
  obtain ⟨ψ⟩ := he
  let θ : S ≃* twistedE6RootGroup K σ := ψ.trans e
  have hE' : IsElemAbelian 3 (E.map (MulAut.congr θ).toMonoidHom) :=
    CFSG.LieType.SeitzGeneration.isElemAbelian_map_congr θ hE
  have hc' : Nat.card (E.map (MulAut.congr θ).toMonoidHom) = 3 ^ 3 :=
    (CFSG.LieType.SeitzGeneration.card_map_congr θ E).trans hc
  have hout' := CFSG.LieType.SeitzGeneration.not_le_range_conj_map_congr θ hout
  have htop : seitzHyperGamma 3 (E.map (MulAut.congr θ).toMonoidHom) = ⊤ := by
    by_cases hdiag : E.map (MulAut.congr θ).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
    · by_cases hR : TwE6NormalizesR K σ (E.map (MulAut.congr θ).toMonoidHom)
      · exact hP K σ q.card hpK hσ2 hK2 _ hE' hc' hdiag hR
      · refine hN K σ q.card hpK hσ2 hK2 ?_ hq2 _ hE' hc' hdiag hout' hR
        rcases (by omega : q.card % 3 = 1 ∨ q.card % 3 = 2) with h1 | h2
        · exfalso
          have hK' : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
          have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := hσ
          have hI := twistedE6Inndiag_eq_inn_of_mod_three (ℓ := q.p) (f := q.exponent) K hK' σ hσ'
            (by rw [← TauCeti.PrimePower.card_def]; exact h1)
          rw [hI] at hdiag
          exact hout' hdiag
        · omega
    · exact hF K σ q.card hpK hσ2 hK2 hq2 hq8 _ hE' hc' hdiag
  exact CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map θ
    (MulAut.congr θ).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
    (MulAut.congr θ).injective htop

theorem seitzGoodOuterHighE6Three_of_cubes (h₁ : E6FieldCubes) (h₂ : TwE6FieldCubes)
    (h₃ : E6DiagParCubes) (h₄ : TwE6DiagParCubes) (h₅ : E6DiagNonParCubes)
    (h₆ : TwE6DiagNonParCubes) : SeitzGoodOuterHighE6Three := by
  refine SeitzGoodOuterHighAt.of_cover (fun d p h => ?_)
    (seitzGoodOuterHighAt_e6_of_cubes h₁ h₃ h₅) (seitzGoodOuterHighAt_twE6_of_cubes h₂ h₄ h₆)
  obtain ⟨h3, hd⟩ := h
  rcases hd with ⟨q, hq, h⟩ | ⟨q, hq⟩
  · exact Or.inl ⟨h3, q, hq, h⟩
  · exact Or.inr ⟨h3, q, hq⟩

theorem twE6EightDiagCubes_of_cubes (h₄ : TwE6DiagParCubes) (h₆ : TwE6DiagNonParCubes) :
    OuterFourSeitz.TwE6EightDiagCubes := by
  intro K _ _ hK σ hσ E hE hc hD hI
  have hK' : Nat.card K = 8 ^ 2 := by rw [hK]; norm_num
  have hσ' : ∀ c, σ c = c ^ 8 := fun c => by rw [hσ c]; norm_num
  have hpK : ringChar K ≠ 3 := by
    refine ringChar_ne_three_of_not_dvd_card ?_
    rw [hK']
    norm_num
  by_cases hR : TwE6NormalizesR K σ E
  · exact h₄ K σ 8 hpK hσ' hK' E hE hc hD hR
  · exact h₆ K σ 8 hpK hσ' hK' (by norm_num) (by norm_num) E hE hc hD hI hR

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

end
