module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab
public import CFSG.GH74.Orders.LieType

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog82A10

open CFSG Subgroup GorensteinWalter AutL2Facts

section Field

variable {F : Type} [Field F] [Finite F]

theorem charP_three_of_card (hF : Nat.card F = 9) : CharP F 3 := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

theorem exists_unit_orderOf_eight (hF : Nat.card F = 9) : ∃ g : Fˣ, orderOf g = 8 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨g, hg.trans ?_⟩
  rw [Nat.card_units, hF]

@[expose] def cube (hF : Nat.card F = 9) : F ≃+* F :=
  haveI := charP_three_of_card hF
  haveI : ExpChar F 3 := ExpChar.prime Nat.prime_three
  RingEquiv.ofBijective (frobenius F 3)
    (Finite.injective_iff_bijective.mp (frobenius F 3).injective)

theorem cube_apply (hF : Nat.card F = 9) (x : F) : cube hF x = x ^ 3 := rfl

theorem cube_ne_one (hF : Nat.card F = 9) : cube hF ≠ 1 := by
  intro h
  obtain ⟨g, hg⟩ := exists_unit_orderOf_eight hF
  have h1 : ((g : F)) ^ 3 = g := by
    rw [← cube_apply hF, h]
    rfl
  have h2 : g ^ 2 = 1 := by
    apply Units.ext
    have hg0 : (g : F) ≠ 0 := g.ne_zero
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have : (g : F) * ((g : F) ^ 2 - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg0
    · linear_combination h
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hg] at this
  norm_num at this

theorem ringAut_eq_cube (hF : Nat.card F = 9) {σ : F ≃+* F} (hσ : σ ≠ 1) : σ = cube hF := by
  classical
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have hc : Fintype.card (F ≃+* F) = 2 := by
    rw [← Nat.card_eq_fintype_card, card_ringAut F (f := 2) Nat.prime_three (by rw [hF]; norm_num)]
  by_contra hne
  have h3 : ({1, σ, cube hF} : Finset (F ≃+* F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hσ, Ne.symm (cube_ne_one hF)⟩
  have := Finset.card_le_univ ({1, σ, cube hF} : Finset (F ≃+* F))
  omega

theorem fu_eq_pow (hF : Nat.card F = 9) {σ : F ≃+* F} (hσ : σ ≠ 1) (u : Fˣ) :
    fu F σ u = u ^ 3 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ringAut_eq_cube hF hσ]
  rfl

end Field

section Stabilizer

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem nm_mem_centralizer (h2 : (2 : F) ≠ 0) (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nm F a ε σ ∈ centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F)) := by
  rw [mem_centralizer_iff]
  rintro _ rfl
  exact ((commute_tor_neg_one_iff h2 _).mpr ⟨a, ε, rfl⟩).symm

omit [Finite F] in
theorem nm_sq (a : Fˣ) : nm F a false 1 ^ 2 = nm F (a ^ 2) false 1 := by
  rw [pow_two, nm_mul, pow_two]
  rfl

omit [Finite F] in
theorem pow_four_ne_one {u : Fˣ} (hu : orderOf u = 8) : u ^ 4 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hu] at this
  norm_num at this

theorem nm_cases (hF : Nat.card F = 9) {g : Fˣ} (hg : orderOf g = 8) (ε : Bool)
    (σ : F ≃+* F) (h : twist F ε (fu F σ (g ^ 2)) = g ^ 2) :
    (ε = false ∧ σ = 1) ∨ (ε = true ∧ σ = cube hF) := by
  cases ε
  · left
    refine ⟨rfl, ?_⟩
    by_contra hσ
    rw [twist_false, fu_eq_pow hF hσ, ← pow_mul] at h
    apply pow_four_ne_one hg
    have h1 : g ^ 2 * g ^ 4 = g ^ 2 * 1 := by
      rw [← pow_add, mul_one]
      exact h
    exact mul_left_cancel h1
  · right
    refine ⟨rfl, ringAut_eq_cube hF ?_⟩
    intro hσ
    rw [hσ, twist_true, fu_one] at h
    apply pow_four_ne_one hg
    have h1 : (g ^ 2)⁻¹ * g ^ 4 = (g ^ 2)⁻¹ * 1 := by
      rw [show g ^ 4 = g ^ 2 * g ^ 2 by rw [← pow_add], ← mul_assoc, inv_mul_cancel, one_mul,
        mul_one]
      exact h.symm
    exact mul_left_cancel h1

theorem nm_not_commute (hF : Nat.card F = 9) {g : Fˣ} (hg : orderOf g = 8) :
    nm F 1 true (cube hF) * nm F g false 1 ≠ nm F g false 1 * nm F 1 true (cube hF) := by
  intro h
  rw [nm_commute_tor_iff, twist_true, fu_eq_pow hF (cube_ne_one hF)] at h
  apply pow_four_ne_one hg
  have h1 : g ^ 3 * g ^ 4 = g ^ 3 * 1 := by
    rw [← pow_add, mul_one]
    calc g ^ (3 + 4) = g ^ 3 * g * g ^ 3 := by rw [← pow_succ, ← pow_add]
      _ = g ^ 3 * (g ^ 3)⁻¹ * g ^ 3 := by rw [h]
      _ = g ^ 3 := by rw [mul_inv_cancel, one_mul]
  exact mul_left_cancel h1

theorem card_le_eight_of_commute (hF : Nat.card F = 9) (B : Subgroup (PGammaL2 F))
    (hz : SemidirectProduct.inl (tor F (-1)) ∈ B) (hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Nat.card B ≤ 8 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 :=
    two_ne_zero_of_isOddPrimePower ⟨3, 2, Nat.prime_three, by decide, by norm_num,
      by rw [hF]; norm_num⟩
  set C := centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F))
  have hBC : B ≤ C := by
    intro x hx
    rw [mem_centralizer_iff]
    rintro _ rfl
    exact hab _ hz x hx
  have hC : Nat.card C = 32 := by
    rw [card_centralizer_tor_neg_one h2, Nat.card_units, hF,
      card_ringAut F (f := 2) Nat.prime_three (by rw [hF]; norm_num)]
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card B ∣ 32 := hC ▸ Subgroup.card_dvd_of_le hBC
  have h16 : 16 ≤ Nat.card B := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card B <;> omega
  have hidx : (B.subgroupOf C).index ≤ 2 := by
    have h1 := (B.subgroupOf C).card_mul_index
    rw [hC, Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv] at h1
    nlinarith
  have hsq : ∀ x ∈ C, x ^ 2 ∈ B := by
    intro x hx
    have hpos : (B.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : (B.subgroupOf C).index = 1 ∨ (B.subgroupOf C).index = 2) with h1 | h1
    · rw [Subgroup.index_eq_one] at h1
      have : (⟨x, hx⟩ : C) ^ 2 ∈ B.subgroupOf C := by rw [h1]; exact mem_top _
      exact this
    · exact Subgroup.sq_mem_of_index_two h1 (⟨x, hx⟩ : C)
  obtain ⟨g, hg⟩ := exists_unit_orderOf_eight hF
  have hμ : nm F (g ^ 2) false 1 ∈ B := by
    rw [← nm_sq]
    exact hsq _ (nm_mem_centralizer h2 g false 1)
  set ν : Fˣ × Bool → PGammaL2 F := fun w => nm F w.1 w.2 (if w.2 then cube hF else 1)
  have hν : ∀ x ∈ B, ∃ w, ν w = x := by
    intro x hx
    obtain ⟨a, ε, hxa⟩ := (commute_tor_neg_one_iff h2 x).mp (hab x hx _ hz)
    have hc := hab x hx _ hμ
    rw [hxa, nm_commute_tor_iff] at hc
    rcases nm_cases hF hg ε _ hc with ⟨rfl, hσ⟩ | ⟨rfl, hσ⟩
    · refine ⟨(a, false), ?_⟩
      rw [hxa, hσ]
      rfl
    · refine ⟨(a, true), ?_⟩
      rw [hxa, hσ]
      rfl
  set W : Finset (Fˣ × Bool) := Finset.univ.filter fun w => ν w ∈ B
  have hW : Nat.card B ≤ W.card := by
    have hsurj : Function.Surjective
        (fun w : W => (⟨ν w.val, (Finset.mem_filter.mp w.2).2⟩ : B)) := by
      rintro ⟨x, hx⟩
      obtain ⟨w, hw⟩ := hν x hx
      exact ⟨⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw ▸ hx⟩⟩, Subtype.ext hw⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [show Nat.card W = W.card by rw [Nat.card_eq_fintype_card, Fintype.card_coe]] at this
  have hcard : Fintype.card (Fˣ × Bool) = 16 := by
    rw [Fintype.card_prod, Fintype.card_bool, ← Nat.card_eq_fintype_card, Nat.card_units, hF]
  have hWuniv : W = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := Finset.card_le_univ W
    omega
  have hg' : ν (g, false) ∈ B := by
    have hm : (g, false) ∈ W := by rw [hWuniv]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hm).2
  have h1' : ν (1, true) ∈ B := by
    have hm : ((1 : Fˣ), true) ∈ W := by rw [hWuniv]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hm).2
  exact nm_not_commute hF hg (hab _ h1' _ hg')

end Stabilizer

theorem cf82L2NineAbelian : CF82L2NineAbelian := by
  intro Y _ _ hY A hA2 hAab
  classical
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' := A.map (autEquiv e).toMonoidHom
  have hcardA : Nat.card A' = Nat.card A := card_map_of_injective (autEquiv e).injective
  rw [← hcardA]
  by_contra hlt
  push Not at hlt
  have hY360 : Nat.card Y = 360 := by
    rw [GH74.card_of_lieModel_PSL (by norm_num) hY]
    decide
  have hPSL : Nat.card (pGammaL2PSLRange F) = 360 := by
    rw [← Nat.card_congr (pGammaL2PSLRangeEquiv F).toEquiv, ← Nat.card_congr e.toEquiv, hY360]
  have hPΓL : Nat.card (PGammaL2 F) = 1440 := by
    rw [SemidirectProduct.card, pgl2_card_formula, hF9,
      card_ringAut F (f := 2) Nat.prime_three (by rw [hF9]; norm_num)]
    norm_num
  have hindex : (pGammaL2PSLRange F).index = 4 := by
    have h1 := (pGammaL2PSLRange F).card_mul_index
    rw [hPSL, hPΓL] at h1
    omega
  have hrel : (pGammaL2PSLRange F).relIndex A' ≤ 4 := by
    have h1 := relIndex_le_of_le_right (H := pGammaL2PSLRange F) (le_top : A' ≤ ⊤)
      (by rw [relIndex_top_right, hindex]; norm_num)
    rwa [relIndex_top_right, hindex] at h1
  have hA'2 : IsPGroup 2 A' := hA2.map _
  have h16 : 16 ≤ Nat.card A' := by
    obtain ⟨m, hm⟩ := hA'2.exists_card_eq
    rw [hm] at hlt ⊢
    by_contra h
    push Not at h
    have hm4 : m < 4 := by
      by_contra hm4
      push Not at hm4
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm4
      omega
    interval_cases m <;> norm_num at hlt
  have hinner : 4 ≤ Nat.card ((pGammaL2PSLRange F).subgroupOf A') := by
    have h1 := ((pGammaL2PSLRange F).subgroupOf A').card_mul_index
    change _ * (pGammaL2PSLRange F).relIndex A' = _ at h1
    nlinarith
  obtain ⟨n, hn⟩ := (hA'2.to_subgroup ((pGammaL2PSLRange F).subgroupOf A')).exists_card_eq
  have h2dvd : 2 ∣ Nat.card ((pGammaL2PSLRange F).subgroupOf A') := by
    rw [hn] at hinner ⊢
    rcases n with _ | n
    · norm_num at hinner
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨⟨⟨x, hxA⟩, hxP⟩, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  rw [mem_subgroupOf] at hxP
  obtain ⟨z, rfl⟩ : ∃ z, incl F z = x := hxP
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective (incl F) (incl_injective F) z]
    simpa [Subgroup.orderOf_mk] using hx
  have hodd := isOddPrimePower_of Nat.prime_three (by norm_num) (by norm_num : 1 ≤ 2) hF
  have hsq := isSquare_neg_one_of_card_sq (f := 1) Nat.prime_three (by norm_num) hF
  obtain ⟨z₀, hz₀⟩ := exists_psl2_tor_neg_one hsq
  have h2F := two_ne_zero_of_isOddPrimePower hodd
  have hinv : ∀ y : PSL2 F, orderOf y = 2 → BenderSuzuki.PFAppendixIII.IsInvolution y := by
    intro y hy
    refine ⟨fun h1 => ?_, by have := pow_orderOf_eq_one y; rwa [hy] at this⟩
    rw [h1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hz₀2 : orderOf z₀ = 2 := by
    rw [← orderOf_injective (incl F) (incl_injective F) z₀, hz₀,
      orderOf_injective _ SemidirectProduct.inl_injective]
    apply orderOf_eq_prime
    · rw [← map_pow, neg_one_sq, map_one]
    · exact tor_neg_one_ne_one h2F
  obtain ⟨k, hk⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd z z₀ (hinv z hz2)
    (hinv z₀ hz₀2)
  set B := A'.map (MulAut.conj (incl F k)).toMonoidHom
  have hB : Nat.card B = Nat.card A' := card_map_of_injective (MulAut.conj (incl F k)).injective
  have hzB : SemidirectProduct.inl (tor F (-1)) ∈ B := by
    refine ⟨incl F z, hxA, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hk, hz₀]
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, hAab x' hx' y' hy']
  have := card_le_eight_of_commute hF9 B hzB hBab
  omega

end CFSG.ComponentClassification.GSThmB.Catalog82A10
