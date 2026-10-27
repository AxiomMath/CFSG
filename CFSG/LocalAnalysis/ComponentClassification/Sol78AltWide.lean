module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Maximal
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup Equiv Equiv.Perm

theorem exists_sq_eq_one_of_independent {P : Type*} [Group P] {z : P} (hz : z * z = 1)
    (hzc : ∀ x : P, x * z = z * x) {a b c : P}
    (ha : a * a = 1 ∨ a * a = z) (hb : b * b = 1 ∨ b * b = z) (hc : c * c = 1 ∨ c * c = z)
    (hab : a * b * (a * b) = 1 ∨ a * b * (a * b) = z)
    (hac : a * c * (a * c) = 1 ∨ a * c * (a * c) = z)
    (hbc : b * c * (b * c) = 1 ∨ b * c * (b * c) = z) :
    a * a = 1 ∨ b * b = 1 ∨ c * c = 1 ∨ a * b * (a * b) = 1 ∨ a * c * (a * c) = 1 ∨
      b * c * (b * c) = 1 ∨ a * b * c * (a * b * c) = 1 := by
  by_contra h
  push Not at h
  obtain ⟨ha1, hb1, hc1, hab1, hac1, hbc1, -⟩ := id h
  have ha' := ha.resolve_left ha1
  have hb' := hb.resolve_left hb1
  have hc' := hc.resolve_left hc1
  have hab' := hab.resolve_left hab1
  have hac' := hac.resolve_left hac1
  have hbc' := hbc.resolve_left hbc1
  have hzm : ∀ w v : P, w * (z * v) = z * (w * v) := fun w v => by
    rw [← mul_assoc, hzc w, mul_assoc]
  have hzz : ∀ w : P, z * (z * w) = w := fun w => by rw [← mul_assoc, hz, one_mul]
  have hsq : ∀ x : P, x * x = z → ∀ w : P, x * (x * w) = z * w := fun x hx w => by
    rw [← mul_assoc, hx]
  have hanti : ∀ x y : P, x * x = z → y * y = z → x * y * (x * y) = z →
      ∀ w : P, y * (x * w) = z * (x * (y * w)) := by
    intro x y hx hy hxy w
    have hxinv : x⁻¹ = z * x := by
      rw [inv_eq_iff_mul_eq_one, hzm, hx, hz]
    have hyinv : y⁻¹ = z * y := by
      rw [inv_eq_iff_mul_eq_one, hzm, hy, hz]
    have h1 : y * x = z * (x * y) := by
      calc y * x = x⁻¹ * (x * y * (x * y)) * y⁻¹ := by group
        _ = z * x * z * (z * y) := by rw [hxy, hxinv, hyinv]
        _ = z * (x * y) := by rw [mul_assoc (z * x) z, hzz, mul_assoc]
    rw [← mul_assoc, h1, mul_assoc, mul_assoc]
  have hba := hanti a b ha' hb' hab'
  have hca := hanti a c ha' hc' hac'
  have hcb := hanti b c hb' hc' hbc'
  apply h.2.2.2.2.2.2
  simp only [mul_assoc]
  rw [hca, hzm, hzm, hba, hzm, hzz, hsq a ha', hcb, hzm, hzz, hsq b hb', hc', hz]

theorem commute_of_mul_self {P : Type*} [Group P] {x y : P} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  have h := eq_inv_of_mul_eq_one_left hxy
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy] at h

theorem exists_regular_triple {n : ℕ} (hn : 8 ≤ n) :
    ∃ a b c : alternatingGroup (Fin n), a * a = 1 ∧ b * b = 1 ∧ c * c = 1 ∧
      a * b = b * a ∧ a * c = c * a ∧ b * c = c * b ∧
      a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a * b ≠ 1 ∧ a * c ≠ 1 ∧ b * c ≠ 1 ∧ a * b * c ≠ 1 ∧
      IsConj a b ∧ IsConj a c ∧ IsConj a (a * b) ∧ IsConj a (a * c) ∧ IsConj a (b * c) ∧
      IsConj a (a * b * c) := by
  let w : ∀ {i j k l : Fin 8}, i ≠ j → k ≠ l → alternatingGroup (Fin 8) := fun {i j k l} h h' =>
    ⟨swap i j * swap k l,
      UnbalancedGS.AlternatingModel.swap_mul_swap_mem_alternatingGroup h h'⟩
  let a₀ : alternatingGroup (Fin 8) :=
    w (i := 0) (j := 1) (k := 2) (l := 3) (by decide) (by decide) *
      w (i := 4) (j := 5) (k := 6) (l := 7) (by decide) (by decide)
  let b₀ : alternatingGroup (Fin 8) :=
    w (i := 0) (j := 2) (k := 1) (l := 3) (by decide) (by decide) *
      w (i := 4) (j := 6) (k := 5) (l := 7) (by decide) (by decide)
  let c₀ : alternatingGroup (Fin 8) :=
    w (i := 0) (j := 4) (k := 1) (l := 5) (by decide) (by decide) *
      w (i := 2) (j := 6) (k := 3) (l := 7) (by decide) (by decide)
  let g₁ : alternatingGroup (Fin 8) := w (i := 0) (j := 3) (k := 4) (l := 7) (by decide) (by decide)
  let g₂ : alternatingGroup (Fin 8) := w (i := 0) (j := 5) (k := 2) (l := 7) (by decide) (by decide)
  let g₃ : alternatingGroup (Fin 8) := w (i := 0) (j := 2) (k := 4) (l := 6) (by decide) (by decide)
  let g₄ : alternatingGroup (Fin 8) := w (i := 0) (j := 4) (k := 2) (l := 6) (by decide) (by decide)
  let g₅ : alternatingGroup (Fin 8) := w (i := 0) (j := 7) (k := 2) (l := 5) (by decide) (by decide)
  let g₆ : alternatingGroup (Fin 8) := w (i := 0) (j := 6) (k := 2) (l := 4) (by decide) (by decide)
  have ha : a₀ * a₀ = 1 := Subtype.ext (by decide)
  have hb : b₀ * b₀ = 1 := Subtype.ext (by decide)
  have hc : c₀ * c₀ = 1 := Subtype.ext (by decide)
  have hab : a₀ * b₀ = b₀ * a₀ := Subtype.ext (by decide)
  have hac : a₀ * c₀ = c₀ * a₀ := Subtype.ext (by decide)
  have hbc : b₀ * c₀ = c₀ * b₀ := Subtype.ext (by decide)
  have ha1 : a₀ ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hb1 : b₀ ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hc1 : c₀ ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hab1 : a₀ * b₀ ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hac1 : a₀ * c₀ ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hbc1 : b₀ * c₀ ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have habc1 : a₀ * b₀ * c₀ ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have h₁ : g₁ * a₀ * g₁⁻¹ = b₀ := Subtype.ext (by decide)
  have h₂ : g₂ * a₀ * g₂⁻¹ = c₀ := Subtype.ext (by decide)
  have h₃ : g₃ * a₀ * g₃⁻¹ = a₀ * b₀ := Subtype.ext (by decide)
  have h₄ : g₄ * a₀ * g₄⁻¹ = a₀ * c₀ := Subtype.ext (by decide)
  have h₅ : g₅ * a₀ * g₅⁻¹ = b₀ * c₀ := Subtype.ext (by decide)
  have h₆ : g₆ * a₀ * g₆⁻¹ = a₀ * b₀ * c₀ := Subtype.ext (by decide)
  let f : Fin 8 ≃ {i : Fin n // i.val < 8} :=
    { toFun := fun i => ⟨Fin.castLE hn i, i.2⟩
      invFun := fun j => ⟨j.1.val, j.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let φ : alternatingGroup (Fin 8) →* alternatingGroup (Fin n) :=
    ((extendDomainHom f).comp (alternatingGroup (Fin 8)).subtype).codRestrict _ fun σ => by
      rw [mem_alternatingGroup, MonoidHom.comp_apply, extendDomainHom_apply, sign_extendDomain]
      exact σ.2
  have hφ : Function.Injective φ := fun x y hxy =>
    Subtype.ext (extendDomainHom_injective f (congrArg Subtype.val hxy))
  have hconj : ∀ {x y : alternatingGroup (Fin 8)} (g : alternatingGroup (Fin 8)),
      g * x * g⁻¹ = y → IsConj (φ x) (φ y) := fun g h =>
    φ.map_isConj (isConj_iff.mpr ⟨g, h⟩)
  refine ⟨φ a₀, φ b₀, φ c₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [← map_mul, ha, map_one]
  · rw [← map_mul, hb, map_one]
  · rw [← map_mul, hc, map_one]
  · rw [← map_mul, hab, map_mul]
  · rw [← map_mul, hac, map_mul]
  · rw [← map_mul, hbc, map_mul]
  · exact (map_ne_one_iff φ hφ).mpr ha1
  · exact (map_ne_one_iff φ hφ).mpr hb1
  · exact (map_ne_one_iff φ hφ).mpr hc1
  · rw [← map_mul]; exact (map_ne_one_iff φ hφ).mpr hab1
  · rw [← map_mul]; exact (map_ne_one_iff φ hφ).mpr hac1
  · rw [← map_mul]; exact (map_ne_one_iff φ hφ).mpr hbc1
  · rw [← map_mul, ← map_mul]; exact (map_ne_one_iff φ hφ).mpr habc1
  · exact hconj g₁ h₁
  · exact hconj g₂ h₂
  · rw [← map_mul]; exact hconj g₃ h₃
  · rw [← map_mul]; exact hconj g₄ h₄
  · rw [← map_mul]; exact hconj g₅ h₅
  · rw [← map_mul, ← map_mul]; exact hconj g₆ h₆

theorem three_le_pRank_of_card_center_le_two {Q : Type*} [Group Q] [Finite Q]
    (hZ : Nat.card (center Q) ≤ 2) {n : ℕ} (hn : 8 ≤ n)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin n)) : 3 ≤ CFSG.pRank 2 Q := by
  classical
  set ψ : Q →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
    with hψ
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x : Q, ψ x = 1 ↔ x ∈ center Q := by
    intro x
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : ∀ z ∈ center Q, z * z = 1 := by
    intro z hz
    have hpos : 0 < Nat.card (center Q) := Nat.card_pos
    have hdvd : orderOf (⟨z, hz⟩ : center Q) ∣ 2 := by
      have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : center Q)
      rcases (show Nat.card (center Q) = 1 ∨ Nat.card (center Q) = 2 by omega) with h | h
      · rw [h] at h1; exact h1.trans (one_dvd 2)
      · rwa [h] at h1
    have h2 : (⟨z, hz⟩ : center Q) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [← sq]
    exact congrArg Subtype.val h2
  obtain ⟨a, b, c, ha, -, -, -, -, -, ha1, hb1, hc1, hab1, hac1, hbc1, habc1, hcb, hcc, hcab,
    hcac, hcbc, hcabc⟩ := exists_regular_triple hn
  obtain ⟨a', rfl⟩ := hψs a
  obtain ⟨b', rfl⟩ := hψs b
  obtain ⟨c', rfl⟩ := hψs c
  set s := a' * a' with hs
  have hsZ : s ∈ center Q := (hker _).mp (by rw [hs, map_mul, ha])
  have hsc : ∀ w : Q, w * s = s * w := fun w => mem_center_iff.mp hsZ w
  have hsq : ∀ x : Q, IsConj (ψ a') (ψ x) → x * x = s := by
    intro x hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    obtain ⟨d, rfl⟩ := hψs g
    set z := (d * a' * d⁻¹)⁻¹ * x with hz
    have hzZ : z ∈ center Q := (hker _).mp (by
      rw [hz, map_mul, map_inv, map_mul, map_mul, map_inv, hg, inv_mul_cancel])
    have hzc : ∀ w : Q, w * z = z * w := fun w => mem_center_iff.mp hzZ w
    have hx' : x = d * a' * d⁻¹ * z := by rw [hz]; group
    rw [hx']
    calc d * a' * d⁻¹ * z * (d * a' * d⁻¹ * z) = d * a' * d⁻¹ * (z * (d * a' * d⁻¹)) * z := by
          group
      _ = d * s * d⁻¹ * (z * z) := by rw [← hzc, hs]; group
      _ = s := by rw [hZ2 z hzZ, mul_one, hsc d, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : b' * b' = s := hsq b' hcb
  have h3 : c' * c' = s := hsq c' hcc
  have h4 : a' * b' * (a' * b') = s := hsq _ (by rw [map_mul]; exact hcab)
  have h5 : a' * c' * (a' * c') = s := hsq _ (by rw [map_mul]; exact hcac)
  have h6 : b' * c' * (b' * c') = s := hsq _ (by rw [map_mul]; exact hcbc)
  have h7 : a' * b' * c' * (a' * b' * c') = s := hsq _ (by rw [map_mul, map_mul]; exact hcabc)
  have hs1 : s = 1 := by
    rcases exists_sq_eq_one_of_independent (hZ2 s hsZ) hsc (Or.inr rfl) (Or.inr h2) (Or.inr h3)
        (Or.inr h4) (Or.inr h5) (Or.inr h6) with h | h | h | h | h | h | h
    · exact h
    · rwa [h2] at h
    · rwa [h3] at h
    · rwa [h4] at h
    · rwa [h5] at h
    · rwa [h6] at h
    · rwa [h7] at h
  rw [hs1] at h2 h3 h4 h5 h6
  have h1 : a' * a' = 1 := hs1
  have hind : ∀ i j k : ZMod 2, a' ^ i.val * b' ^ j.val * c' ^ k.val = 1 →
      i = 0 ∧ j = 0 ∧ k = 0 := by
    have h01 : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
    have hv0 : (0 : ZMod 2).val = 0 := rfl
    have hv1 : (1 : ZMod 2).val = 1 := rfl
    intro i j k h
    have h' := congrArg ψ h
    simp only [map_mul, map_pow, map_one] at h'
    rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl <;>
      rcases h01 k with rfl | rfl <;>
      simp only [hv0, hv1, pow_zero, pow_one, one_mul, mul_one] at h' <;>
      first
      | exact ⟨rfl, rfl, rfl⟩
      | exact absurd h' ha1
      | exact absurd h' hb1
      | exact absurd h' hc1
      | exact absurd h' hab1
      | exact absurd h' hac1
      | exact absurd h' hbc1
      | exact absurd h' habc1
  obtain ⟨E, hE, hEcard, -⟩ :=
    LocalAnalysis.ComponentInitial.LinearThreeFourOuter.exists_elementaryAbelian_eight
      (commute_of_mul_self h1 h2 h4) (commute_of_mul_self h1 h3 h5)
      (commute_of_mul_self h2 h3 h6) h1 h2 h3 hind
  exact le_pRank_of_elementaryAbelian one_lt_two hE (k := 3) (by rw [hEcard]; norm_num)

theorem three_le_pRank_of_fusionZStar (hS : SolAltLit.SchurAlternatingMultiplierInput)
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] {n : ℕ} (hn : 8 ≤ n)
    (e : K ⧸ Open.fusionZStar K ≃* alternatingGroup (Fin n)) : 3 ≤ CFSG.pRank 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e' : (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K) ≃* alternatingGroup (Fin n) :=
    (coreQuotientCenterEquiv K).trans e
  have hZ : Nat.card (center (K ⧸ pPrimeCore 2 K)) ≤ 2 :=
    card_center_le_two hS (pPrimeCore_quotient_pPrimeCore_eq_bot 2) (by omega) e'
  have h3 := three_le_pRank_of_card_center_le_two hZ hn e'
  have h4 : CFSG.pRank 2 (K ⧸ pPrimeCore 2 K) = CFSG.pRank 2 K :=
    GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (pPrimeCore_coprime_card (p := 2) (G := K)))
  omega

theorem nonempty_fusionZStar_equiv_of_coreQuotient {K : Type*} [Group K] {n : ℕ} (hn : 4 ≤ n)
    (e : K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin n)) :
    Nonempty (K ⧸ Open.fusionZStar K ≃* alternatingGroup (Fin n)) := by
  have hZ : center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using hn)
  exact ⟨((coreQuotientCenterEquiv K).symm.trans (centerQuotCongr e)).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

end CFSG.ComponentClassification.Sol78
