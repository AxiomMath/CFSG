module

public import CFSG.FeitThompson.Foundations.CounterorderedPrimeParity
public import CFSG.FeitThompson.OddOrder.NormalFormWordCoordinates
public import CFSG.FeitThompson.OddOrder.ComparisonWordAfterFrobenius
public import CFSG.FeitThompson.OddOrder.ComparisonWordsCancel
public import CFSG.FeitThompson.OddOrder.ConjugateAffineIntersection

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Subgroup

variable {p q : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

theorem eq_one_of_comparison_words {U H P₀ : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    {t r₁ r₂ r₃ w₁ w₂ w₃ : G}
    (hw₁ : w₁ ∈ U) (hw₂ : w₂ ∈ U) (hw₃ : w₃ ∈ U) (hUH : U ≤ H)
    (hr₁ : r₁ ∈ P₀) (hr₃ : r₃ ∈ P₀) (hP₀H : P₀ ≤ H)
    (hinter : H ⊓ H.map (MulAut.conj ((t ^ 2)⁻¹) : G →* G) = U)
    (hrig : ∀ x ∈ P₀, ∀ u ∈ U, ∀ z ∈ P₀, x * u * z ∈ U → (x = 1 ∧ z = 1) ∨ (u = 1 ∧ x * z = 1))
    (hr₁1 : r₁ ≠ 1) (hr₃1 : r₃ ≠ 1) (hU1 : ∀ u ∈ U, u ^ (n - 1) = 1 → u = 1)
    (hword : t * r₂⁻¹ * t = w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃)
    (hpow : t * r₂⁻¹ * t = w₁ ^ n * r₃ * w₂ ^ n * t ^ 2 * r₁ * w₃ ^ n) :
    w₁ = 1 ∧ w₂ = 1 ∧ w₃ = 1 ∧ t * r₂⁻¹ * t = r₃ * t ^ 2 * r₁ := by
  set k : ℕ := n - 1 with hk
  have hkz : (n : ℤ) - 1 = (k : ℤ) := by simp only [hk]; omega
  have h : w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃
      = w₁ ^ (n : ℤ) * r₃ * w₂ ^ (n : ℤ) * t ^ 2 * r₁ * w₃ ^ (n : ℤ) := by
    simp only [zpow_natCast]
    rw [← hword, hpow]
  have hcancel := comparison_words_cancel (n : ℤ) t r₁ r₃ w₁ w₂ w₃ h
  rw [inv_inv, hkz] at hcancel
  set X : G := r₃⁻¹ * w₁ ^ (-(k : ℤ)) * r₃ with hX
  set A : G := w₂ ^ (-(n : ℤ)) * X * w₂ with hA
  set B : G := r₁ * w₃ ^ (k : ℤ) * r₁⁻¹ with hB
  have hXH : X ∈ H := by
    rw [hX]
    exact mul_mem (mul_mem (inv_mem (hP₀H hr₃)) (zpow_mem (hUH hw₁) _)) (hP₀H hr₃)
  have hAH : A ∈ H := by
    rw [hA]; exact mul_mem (mul_mem (zpow_mem (hUH hw₂) _) hXH) (hUH hw₂)
  have hBH : B ∈ H := by
    rw [hB]
    exact mul_mem (mul_mem (hP₀H hr₁) (zpow_mem (hUH hw₃) _)) (inv_mem (hP₀H hr₁))
  have hBmap : B ∈ H.map (MulAut.conj ((t ^ 2)⁻¹) : G →* G) := by
    rw [mem_map_conj_inv, ← hcancel, show t ^ 2 * ((t ^ 2)⁻¹ * A * t ^ 2) * (t ^ 2)⁻¹ = A from
      by group]
    exact hAH
  have hBU : B ∈ U := by rw [← hinter]; exact Subgroup.mem_inf.2 ⟨hBH, hBmap⟩
  have hw₃k : w₃ ^ (k : ℤ) = 1 := by
    rcases hrig r₁ hr₁ (w₃ ^ (k : ℤ)) (zpow_mem hw₃ _) r₁⁻¹ (inv_mem hr₁) hBU with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hr₁1
    · exact h1
  have hw₃1 : w₃ = 1 := hU1 w₃ hw₃ (by rw [← zpow_natCast]; exact hw₃k)
  have hA1 : A = 1 := by
    have hB1 : B = 1 := by rw [hB, hw₃k]; group
    rw [← hcancel] at hB1
    calc A = t ^ 2 * ((t ^ 2)⁻¹ * A * t ^ 2) * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [hB1]; group
  have hXeq : X = w₂ ^ (k : ℤ) := by
    have hA1' : w₂ ^ (-(n : ℤ)) * X * w₂ = 1 := hA1
    calc X = w₂ ^ (n : ℤ) * (w₂ ^ (-(n : ℤ)) * X * w₂) * w₂⁻¹ := by group
      _ = w₂ ^ ((n : ℤ) - 1) := by rw [hA1']; group
      _ = w₂ ^ (k : ℤ) := by rw [hkz]
  have hXU : X ∈ U := by rw [hXeq]; exact zpow_mem hw₂ _
  have hw₁k : w₁ ^ (-(k : ℤ)) = 1 := by
    rcases hrig r₃⁻¹ (inv_mem hr₃) (w₁ ^ (-(k : ℤ))) (zpow_mem hw₁ _) r₃ hr₃ (hX ▸ hXU) with
      ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 hr₃1
    · exact h1
  have hw₁1 : w₁ = 1 := by
    refine hU1 w₁ hw₁ ?_
    rw [← zpow_natCast, ← inv_inj, ← zpow_neg, hw₁k, inv_one]
  have hw₂1 : w₂ = 1 := by
    refine hU1 w₂ hw₂ ?_
    have hk1 : w₂ ^ (k : ℤ) = 1 := by rw [← hXeq, hX, hw₁k]; group
    rw [← zpow_natCast]; exact hk1
  exact ⟨hw₁1, hw₂1, hw₃1, by rw [hword, hw₁1, hw₂1, hw₃1, one_mul, mul_one, mul_one]⟩

section Bridge

variable [Finite F] {hp : p.Prime} {hq : q.Prime} {hqp : q < p}
    {hcard : Nat.card F = p ^ q} {hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)}
    {P U : Subgroup G} {Pe : Multiplicative F ≃* P} {Ue : normOneUnits F ≃* U}
    {hPU : P ⊓ U = ⊥}
    {hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G)}

private noncomputable def rootsEquiv (hp : p.Prime) (hcard : Nat.card F = p ^ q) :
    rootsOfUnity (normExponent p q) F ≃* normOneUnits F :=
  MulEquiv.subgroupCongr (rootsOfUnity_normExponent_eq_normOneUnits hp hcard)

noncomputable def appendixCSetupOfMulEquiv (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hcard : Nat.card F = p ^ q) (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G)) :
    AppendixCSetup p q F G where
  p_prime := hp
  q_prime := hq
  q_lt_p := hqp
  card_field := hcard
  coprime_normExponent := normExponent_def p q ▸ hcop
  pt := P.subtype.comp Pe.toMonoidHom
  pt_injective := P.subtype_injective.comp Pe.injective
  ut := U.subtype.comp (Ue.toMonoidHom.comp (rootsEquiv hp hcard).toMonoidHom)
  ut_injective := U.subtype_injective.comp (Ue.injective.comp (rootsEquiv hp hcard).injective)
  disjoint_ranges := by
    have hP : (P.subtype.comp Pe.toMonoidHom).range = P := by
      ext x
      simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ (Pe a).2, fun hx => ⟨Pe.symm ⟨x, hx⟩, by simp⟩⟩
    have hU : (U.subtype.comp (Ue.toMonoidHom.comp
        (rootsEquiv hp hcard (F := F)).toMonoidHom)).range = U := by
      ext x
      simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
      refine ⟨fun ⟨a, ha⟩ => ha ▸ (Ue _).2,
        fun hx => ⟨(rootsEquiv hp hcard).symm (Ue.symm ⟨x, hx⟩), ?_⟩⟩
      simp
    rw [hP, hU, disjoint_iff]; exact hPU
  conj_pt := by
    intro z u
    have h := hact z (rootsEquiv hp hcard u)
    simpa [rootsEquiv] using h

theorem appendixCSetupOfMulEquiv_pt :
    (appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact).pt
      = P.subtype.comp Pe.toMonoidHom := (rfl)

theorem appendixCSetupOfMulEquiv_U :
    (appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact).U = U := by
  rw [AppendixCSetup.U_def,
    show (appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact).ut
      = U.subtype.comp (Ue.toMonoidHom.comp (rootsEquiv hp hcard).toMonoidHom) from (rfl)]
  ext x
  simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
  refine ⟨fun ⟨a, ha⟩ => ha ▸ (Ue _).2,
    fun hx => ⟨(rootsEquiv hp hcard).symm (Ue.symm ⟨x, hx⟩), by simp⟩⟩

theorem appendixCSetupOfMulEquiv_P :
    (appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact).P = P := by
  rw [AppendixCSetup.P_def, appendixCSetupOfMulEquiv_pt]
  ext x
  simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ (Pe a).2, fun hx => ⟨Pe.symm ⟨x, hx⟩, by simp⟩⟩

theorem appendixCSetupOfMulEquiv_H :
    (appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact).H = P ⊔ U := by
  rw [AppendixCSetup.H_def, appendixCSetupOfMulEquiv_P, appendixCSetupOfMulEquiv_U]

theorem appendixCSetupOfMulEquiv_P₀ :
    (appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact).P₀
      = primeLine (P.subtype.comp Pe.toMonoidHom) := by
  rw [AppendixCSetup.P₀_def, appendixCSetupOfMulEquiv_pt]
  ext x
  rw [mem_primeLine, Subgroup.mem_map]
  exact ⟨fun ⟨w, hw, h⟩ => ⟨toAdd w, hw, h⟩, fun ⟨c, hc, h⟩ => ⟨ofAdd c, hc, h⟩⟩

end Bridge

theorem sup_inf_map_conj_inv_eq [Finite G] (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hcard : Nat.card F = p ^ q) (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {P₀ P₁ Q : Subgroup G} (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    (hQp : Nat.Coprime (Nat.card Q) p) (hQnorm : P₀ ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G))
    {z : G} (hz : z ∈ P₁) (hz1 : z ≠ 1) :
    (P ⊔ U) ⊓ (P ⊔ U).map (MulAut.conj z⁻¹ : G →* G) = U := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  set S := appendixCSetupOfMulEquiv hp hq hqp hcard hcop Pe Ue hPU hact with hS
  have hSU : S.U = U := appendixCSetupOfMulEquiv_U
  have hSP₀ : S.P₀ = P₀ := by rw [appendixCSetupOfMulEquiv_P₀, hP₀]
  rw [← show S.H = P ⊔ U from appendixCSetupOfMulEquiv_H, ← hSU]
  exact S.H_inf_map_conj_inv_eq_U (Q := Q) hQp (hSP₀ ▸ hQnorm) hy
    (by rw [hSP₀, hSU, ← hP₁]; exact hP₁U) (by rw [hSP₀, ← hP₁]; exact hz) hz1

theorem sq_conj_apply_ofAdd_one_ne_one (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hcard : Nat.card F = p ^ q) (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {P : Subgroup G} (Pe : Multiplicative F ≃* P) (y : G) :
    (y⁻¹ * (Pe (ofAdd (1 : F)) : G) * y) ^ 2 ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have hchar : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  set s : G := (Pe (ofAdd (1 : F)) : G) with hsdef
  have hs1 : s ≠ 1 := by
    intro h
    have h2 : (ofAdd (1 : F)) = 1 := Pe.map_eq_one_iff.mp (OneMemClass.coe_eq_one.mp h)
    exact one_ne_zero (α := F) (by simpa using congrArg toAdd h2)
  have hsp : s ^ p = 1 := by
    rw [hsdef, ← Subgroup.coe_pow, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one,
      show ((p : ℕ) : F) = 0 from by exact_mod_cast CharP.cast_eq_zero F p]
    simp
  have hpodd : Odd p := (odd_of_coprime_pow_sub_one_div_sub_one hp hq hqp hcop).2.2.1
  have hs2 : s ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_eq_prime hsp hs1] at hd
    rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd] at hpodd
    simp [Nat.odd_iff] at hpodd
  intro h
  refine hs2 ?_
  rw [show (y⁻¹ * s * y) ^ 2 = y⁻¹ * s ^ 2 * y from by rw [pow_two, pow_two]; group] at h
  calc s ^ 2 = y * (y⁻¹ * s ^ 2 * y) * y⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem eq_one_of_pow_sub_one_eq_one_of_normOneUnits (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {U : Subgroup G} (Ue : normOneUnits F ≃* U) {u : G} (hu : u ∈ U) (h : u ^ (p - 1) = 1) :
    u = 1 := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have hcardU : Nat.card U = (p ^ q - 1) / (p - 1) := by
    rw [← natCard_normOneUnits_eq_div hp hcard, Nat.card_congr Ue.toEquiv]
  have h1 : orderOf u ∣ (p ^ q - 1) / (p - 1) := hcardU ▸ Subgroup.orderOf_dvd_natCard U hu
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop h1 (orderOf_dvd_of_pow_eq_one h))

theorem not_intModEq_of_sub_eq_neg_one (hp : p.Prime) {i k : ℤ} (hik : i - k = -1) :
    ¬ (i ≡ k [ZMOD (p : ℤ)]) := by
  intro h
  have hd : (p : ℤ) ∣ i - k := Int.ModEq.dvd h.symm
  rw [hik] at hd
  have h1 := Int.le_of_dvd one_pos ((dvd_neg).mp hd)
  have h2 := hp.two_le
  omega

theorem comparison_units_eq_one_and_word_eq [Finite G]
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) {P U : Subgroup G}
    (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U) (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y) (_hyc : y ∈ ⁅Q, P₀⁆)
    {a b : normOneUnits F} (hab : ((a : Fˣ) : F) + ((b : Fˣ) : F) = 2)
    {u₁ u₂ u₃ v₁ v₂ v₃ : normOneUnits F} {c₁ c₂ c₃ : F}
    (hc₁ : c₁ ∈ (⊥ : Subfield F)) (hc₂ : c₂ ∈ (⊥ : Subfield F)) (hc₃ : c₃ ∈ (⊥ : Subfield F))
    {r₁ r₂ r₃ : G} (hr₁ : r₁ = (Pe (ofAdd c₁) : G)) (hr₂ : r₂ = (Pe (ofAdd c₂) : G))
    (hr₃ : r₃ = (Pe (ofAdd c₃) : G))
    (h₁ : s * ((t ^ 3)⁻¹ * (Ue a : G)⁻¹ * t ^ 3) * (s ^ 2)⁻¹ = (Ue u₁ : G) * r₁ * (Ue v₁ : G))
    (h₂ : s ^ 3 * ((t ^ 2)⁻¹ * ((Ue a : G) * (Ue b : G)⁻¹) * t ^ 2) * s⁻¹
      = (Ue u₂ : G) * r₂ * (Ue v₂ : G))
    (h₃ : s ^ 2 * (t⁻¹ * (Ue b : G) * t) * (s ^ 3)⁻¹ = (Ue u₃ : G) * r₃ * (Ue v₃ : G))
    {w₁ w₂ w₃ : G} (hw₁ : w₁ = t * (Ue v₂ : G) * t⁻¹ * (Ue u₃ : G))
    (hw₂ : w₂ = (Ue v₃ : G) * (t ^ 2 * (Ue u₁ : G) * (t ^ 2)⁻¹))
    (hw₃ : w₃ = (Ue v₁ : G) * (t⁻¹ * (Ue u₂ : G) * t)) :
    w₁ = 1 ∧ w₂ = 1 ∧ w₃ = 1 ∧ t * r₂⁻¹ * t = r₃ * t ^ 2 * r₁ := by
  have hsP₀ : s ∈ P₀ := by rw [hP₀, hs]; exact apply_ofAdd_mem_primeLine _ (one_mem _)
  have htP₁ : t ∈ P₁ := by rw [hP₁, ht]; exact ⟨s, hsP₀, by simp [MulAut.conj]⟩
  have htU : t ∈ normalizer (U : Set G) := hP₁U htP₁
  have hconj : ∀ g ∈ normalizer (U : Set G), ∀ x ∈ U, g * x * g⁻¹ ∈ U :=
    fun g hg x hx => ((Subgroup.mem_normalizer_iff (H := U) (g := g)).1 hg x).1 hx
  have hw₁U : w₁ ∈ U := by
    rw [hw₁]
    exact mul_mem (by simpa [mul_assoc] using hconj t htU _ (Ue v₂).2) (Ue u₃).2
  have hw₂U : w₂ ∈ U := by
    rw [hw₂]; exact mul_mem (Ue v₃).2 (hconj (t ^ 2) (pow_mem htU 2) _ (Ue u₁).2)
  have hw₃U : w₃ ∈ U := by
    rw [hw₃]
    exact mul_mem (Ue v₁).2 (by simpa using hconj t⁻¹ (inv_mem htU) _ (Ue u₂).2)
  have hr₁P₀ : r₁ ∈ P₀ := by rw [hP₀, hr₁]; exact apply_ofAdd_mem_primeLine _ hc₁
  have hr₃P₀ : r₃ ∈ P₀ := by rw [hP₀, hr₃]; exact apply_ofAdd_mem_primeLine _ hc₃
  have hUH : U ≤ H := hH ▸ le_sup_right
  have hP₀H : P₀ ≤ H := by
    rw [hH, hP₀]
    refine (primeLine_le_range _).trans ?_
    rintro x ⟨w, rfl⟩
    exact le_sup_left (α := Subgroup G) (Pe w).2
  have ht21 : t ^ 2 ≠ 1 := by
    rw [ht, hs]; exact sq_conj_apply_ofAdd_one_ne_one hp hq hqp hcard hcop Pe y
  have hinter : H ⊓ H.map (MulAut.conj ((t ^ 2)⁻¹) : G →* G) = U := by
    rw [hH]
    exact sup_inf_map_conj_inv_eq hp hq hqp hcard hcop Pe Ue hPU hact hP₀ hQp hQnorm hy hP₁ hP₁U
      (pow_mem htP₁ 2) ht21
  have hrig : ∀ x ∈ P₀, ∀ u ∈ U, ∀ z ∈ P₀, x * u * z ∈ U →
      (x = 1 ∧ z = 1) ∨ (u = 1 ∧ x * z = 1) := by
    intro x hx u hu z hz hmem
    exact eq_one_of_mul_mul_mem hp hq hqp hcard hcop Pe Ue hPU hact (H := H) (P₁ := P₁) (Q := Q)
      hH hP₀ hs hQab hQp hQnorm hy hP₁ hP₁U ht (hP₀ ▸ hx) (hP₀ ▸ hz) hu hmem
  have hcoord := fun (i j k : ℤ) (c : F) (hc : c ∈ (⊥ : Subfield F))
      (z u v : normOneUnits F)
      (heq : s ^ i * ((t ^ j)⁻¹ * (Ue z : G) * t ^ j) * s ^ (-k)
        = (Ue u : G) * (Pe (ofAdd c) : G) * (Ue v : G)) =>
    (coord_eq_and_apply_ofAdd_ne_one_of_mul_mul_eq hp hq hqp hcard hcop Pe Ue hPU hact
      (H := H) (P₁ := P₁) (Q := Q) hH hP₀ hs hQab hQp hQnorm hy hP₁ hP₁U ht
      (i := i) (j := j) (k := k) (a := z) (u := u) (v := v) (c := c) hc heq).2.2
  have hr₁1 : r₁ ≠ 1 := by
    refine hr₁ ▸ hcoord 1 3 2 c₁ hc₁ a⁻¹ u₁ v₁ ?_ (not_intModEq_of_sub_eq_neg_one hp (by norm_num))
    rw [show (Ue a⁻¹ : G) = (Ue a : G)⁻¹ from by rw [map_inv, Subgroup.coe_inv]]
    simpa [hr₁] using h₁
  have hr₃1 : r₃ ≠ 1 := by
    refine hr₃ ▸ hcoord 2 1 3 c₃ hc₃ b u₃ v₃ ?_ (not_intModEq_of_sub_eq_neg_one hp (by norm_num))
    simpa [hr₃] using h₃
  obtain ⟨hword, hpow⟩ := comparison_word_and_pow hp hq hqp hcard hcop Pe Ue hPU hact
    (H := H) (P₀ := P₀) (P₁ := P₁) (Q := Q) hH hP₀ hs hQab hQp hQnorm hy hP₁ hP₁U ht _hyc
    hab hc₁ hc₂ hc₃ hr₁ hr₂ hr₃ h₁ h₂ h₃ hw₁ hw₂ hw₃
  exact eq_one_of_comparison_words (n := p) hp.one_lt.le hw₁U hw₂U hw₃U hUH hr₁P₀ hr₃P₀ hP₀H
    hinter hrig hr₁1 hr₃1
    (fun u hu h => eq_one_of_pow_sub_one_eq_one_of_normOneUnits hp hcard hcop Ue hu h) hword hpow

end

end CFSG.FeitThompson
