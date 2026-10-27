module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSocle
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EType

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem prime_eq_of_pow_eq {p ℓ m a : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hm : 1 ≤ m)
    (h : p ^ m = ℓ ^ a) : p = ℓ := by
  have h1 : p ∣ ℓ ^ a := h ▸ dvd_pow_self p (by omega)
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h1)

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

theorem false_of_psl_ge_five (hnab : ∃ a b : Y, a * b ≠ b * a) {n ℓ e : ℕ} (hn : 5 ≤ n)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSL n ℓ e) {p m : ℕ} (hp2 : p ≠ 2)
    {τ : MulAut Y} (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : False := by
  classical
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, -, -, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨⟨-, he, -⟩, k, _, _, hk, ⟨φ₀⟩⟩ := hY
  let φ : ↥(generalizedFitting (MulAut Y)) ≃* projectiveSL n k :=
    eW.symm.trans (φ₀.trans
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n k).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k)))
  have hZP := OddSelector.center_projectiveSL_eq_bot (k := k) (by omega : 3 ≤ n)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hWC φ hZP
  obtain ⟨-, -, -, hL₁⟩ :=
    OddSelector.socle_images φ hinj hρW (hLW τ) (isComponentOf_map_conj_layer hZ hL)
  set L' := (GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y) with hL'
  have hsrc : Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 2 p m ∨
      Nonempty (↥L' ⧸ center ↥L' ≃* alternatingGroup (Fin 7)) ∨
      Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 3 2 2 :=
    Or.inl (statedSrc_layerMap hZ hL)
  have hrank : Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 2 p m →
      2 ≤ CFSG.pRank 2 L' ∨ Odd (Nat.card (center ↥L')) :=
    fun _ => Or.inr (by rw [center_layerMap_eq_bot hZ hL, card_bot]; exact odd_one)
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (n := n) (by omega)
  obtain ⟨B, σ, ε, hε, hρa⟩ := hform (ρ τ)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      obtain ⟨-, -, -, hm4⟩ := OddSelector.inner_case_reduction hτ (by omega) hℓ hℓ2 he hk hinj
        hL₁ hρa hp2 hsrc hrank
      omega
    · exact OddSelector.field_case_false hτ (by omega) hℓ hℓ2 he hk hinj hL₁ hσ hρa hp2 hsrc
  · rw [pow_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut n k B * dualAut n k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← hτ, pow_orderOf_eq_one, map_one]
      rcases OddSelector.transpose_eq_or_eq_neg_of_pureGraph (by omega) B hα2 with hB | hB
      · exact OddSelector.orthogonal_case_false hn hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
      · exact OddSelector.symplectic_case_false (by omega) hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
    · exact OddSelector.graph_field_case_false hτ (by omega) hℓ hℓ2 he hk hinj hL₁ hσ hρa hp2
        hsrc

theorem false_of_psu_ge_five (hnab : ∃ a b : Y, a * b ≠ b * a) {n ℓ e : ℕ} (hn : 5 ≤ n)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSU n ℓ e) {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : False := by
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hM : Blueprint.LieModel ↥(generalizedFitting (MulAut Y)) .PSU n ℓ e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eW (Or.inl ⟨by simp [Blueprint.classicalTags], hY⟩)
  exact OddClassSelector.su_family_false hWs hWnab hWC hτ (hLW τ)
    (isComponentOf_map_conj_layer hZ hL) (smallSource_layerMap hZ hp hp2 hm h16 hL) hℓ hℓ2 he
    hn hM

theorem eq_of_psl4 (hnab : ∃ a b : Y, a * b ≠ b * a) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSL 4 ℓ e) {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : p = ℓ := by
  classical
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, -, -, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨⟨-, he, -⟩, k, _, _, hk, ⟨φ₀⟩⟩ := hY
  let φ : ↥(generalizedFitting (MulAut Y)) ≃* projectiveSL 4 k :=
    eW.symm.trans (φ₀.trans
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 k).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 k)))
  have hZP := OddSelector.center_projectiveSL_eq_bot (k := k) (by norm_num : 3 ≤ 4)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hWC φ hZP
  have h5 : 5 ≤ p ^ m := by
    have := seven_le_of_sixteen_dvd hp hp2 hm h16
    omega
  obtain ⟨-, h⟩ := GSThmB.Catalog7L4M.psl4_component_type hWC hℓ hℓ2 he hk φ hinj hρW hτ
    (hLW τ) (isComponentOf_map_conj_layer hZ hL).1 (isPComponent_map_conj_layer hZ hp2 hL) hp
    hp2 h5 (lieModel_pcore_layerMap hZ hp2 hL)
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · rw [hk, ← pow_mul] at h
    exact prime_eq_of_pow_eq hp hℓ hm h
  · rw [hk] at h
    exact prime_eq_of_pow_eq hp hℓ hm h

theorem eq_of_psu4 (hnab : ∃ a b : Y, a * b ≠ b * a) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSU 4 ℓ e) {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : p = ℓ := by
  classical
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, -, -, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨⟨-, he, -⟩, K, _, _, hK, ⟨φ₀⟩⟩ := hY
  have hud : UnitaryFieldData ℓ e K := ⟨hℓ, he, by rw [hK, ← pow_mul, mul_comm]⟩
  let φ : ↥(generalizedFitting (MulAut Y)) ≃*
      Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 4 (ℓ ^ e) K) :=
    eW.symm.trans φ₀
  have : IsSimpleGroup
      (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 4 (ℓ ^ e) K)) :=
    φ₀.symm.isSimpleGroup
  have hZP : center (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 4 (ℓ ^ e) K)) =
      ⊥ := by
    obtain ⟨a, b, hab⟩ := hnab
    exact CatLeaf.center_eq_bot_of_simple
      ⟨φ₀ a, φ₀ b, fun h => hab (φ₀.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hWC φ hZP
  have h5 : 5 ≤ p ^ m := by
    have := seven_le_of_sixteen_dvd hp hp2 hm h16
    omega
  obtain ⟨-, -, A, ψ, -, -, h⟩ := GSThmB.Catalog7L4EU.psu4_component_type hud hWC hℓ2 φ hinj hρW
    hZP hτ (hLW τ) (isComponentOf_map_conj_layer hZ hL).1
    (isPComponent_map_conj_layer hZ hp2 hL) hp hp2 h5 (lieModel_pcore_layerMap hZ hp2 hL)
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rw [← pow_mul] at h
    exact prime_eq_of_pow_eq hp hℓ hm h
  · rw [← pow_mul] at h
    exact prime_eq_of_pow_eq hp hℓ hm h
  · exact prime_eq_of_pow_eq hp hℓ hm h

end CFSG.ComponentClassification.HarrisLit.Hin
