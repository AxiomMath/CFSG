module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TE

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Idx

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def FixCat (Y : Type) [Group Y] (n : ℕ) : Prop :=
  ∀ α τ : MulAut Y, α * α = 1 → α ≠ 1 → τ * α = α * τ → (∃ k : ℕ, τ ^ 2 ^ k = 1) →
    ∀ X : Subgroup Y, ⁅X, X⁆ = X → n ∣ Nat.card X → (∀ x ∈ X, α x = x) →
      (∀ x ∈ X, τ x = x) → τ = 1 ∨ τ = α

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] noncomputable def imK (Y : Subgroup H) : Subgroup (OddBar h.K) :=
  (Y.subgroupOf h.K).map (QuotientGroup.mk' (pPrimeCore 2 h.K))

@[expose] noncomputable def toK {Y : Subgroup H} (hY : Y ≤ h.K) : ↥Y →* OddBar h.K :=
  (QuotientGroup.mk' (pPrimeCore 2 h.K)).comp (Subgroup.inclusion hY)

theorem toK_apply {Y : Subgroup H} (hY : Y ≤ h.K) (y : ↥Y) :
    toK h hY y = QuotientGroup.mk ⟨(y : H), hY y.2⟩ := rfl

theorem range_toK {Y : Subgroup H} (hY : Y ≤ h.K) : (toK h hY).range = imK h Y := by
  apply le_antisymm
  · rintro _ ⟨j, rfl⟩
    exact ⟨⟨j, hY j.2⟩, mem_subgroupOf.mpr j.2, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, mem_subgroupOf.mp hk⟩, rfl⟩

theorem ker_toK_le {Y : Subgroup H} (hY : Y ≤ h.K) : (toK h hY).ker ≤ pPrimeCore 2 ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_pPrimeCore_of_normal
  set φ := toK h hY
  let f : φ.ker →* pPrimeCore 2 h.K :=
    ((Subgroup.inclusion hY).comp φ.ker.subtype).codRestrict _ (by
      intro j
      have hj := j.2
      rw [MonoidHom.mem_ker, toK_apply, QuotientGroup.eq_one_iff] at hj
      exact hj)
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z : pPrimeCore 2 h.K => ((z : h.K) : H)) hxy
    exact Subtype.ext (Subtype.ext this)
  exact Nat.Coprime.coprime_dvd_right (card_dvd_of_injective f hf) pPrimeCore_coprime_card

theorem card_dvd_imK {Y : Subgroup H} (hY : Y ≤ h.K)
    (e : ↥Y ⧸ pPrimeCore 2 ↥Y ≃* OddBar h.J) : Nat.card (OddBar h.J) ∣ Nat.card (imK h Y) := by
  rw [← Nat.card_congr e.toEquiv, ← range_toK h hY,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (toK h hY)).toEquiv]
  refine card_dvd_of_surjective (QuotientGroup.map _ _ (MonoidHom.id _) (ker_toK_le h hY))
    fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem imK_commutator_eq {Y : Subgroup H} (hY : Y ≤ h.K) (hYp : ⁅Y, Y⁆ = Y) :
    ⁅imK h Y, imK h Y⁆ = imK h Y := by
  have h1 : ⁅Y.subgroupOf h.K, Y.subgroupOf h.K⁆ = Y.subgroupOf h.K := by
    apply map_injective h.K.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hY, hYp]
  rw [imK, ← map_commutator, h1]

theorem actW_apply_of_mem_imK (hKa : conjugate h.K h.a = h.K) {Y : Subgroup H} {w : h.W}
    (hYw : ∀ y ∈ Y, (w : H) * y = y * w) {x : OddBar h.K} (hx : x ∈ imK h Y) :
    actW h hKa w x = x := by
  obtain ⟨j, hj, rfl⟩ := hx
  have hjw : (w : H) * j = j * w := hYw _ (mem_subgroupOf.mp hj)
  rw [QuotientGroup.mk'_apply, actW_apply_mk]
  congr 1
  apply Subtype.ext
  show (w : H) * (j : H) * (w : H)⁻¹ = j
  rw [hjw, mul_inv_cancel_right]

theorem mem_B_of_V {w : H} (hwW : w ∈ h.W) (hwV : w ∈ coreActionKernel h.V)
    (hw2 : ∃ n : ℕ, w ^ 2 ^ n = 1) : w ∈ h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBC, R₀, hR₀⟩ := sylowKernelStatement H h
  have hw2' : IsPGroup 2 (zpowers w) := by
    obtain ⟨n, hn⟩ := hw2
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨n, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hn, one_zpow]
  set X : Subgroup H := zpowers w ⊔ h.B with hX
  have hX2 : IsPGroup 2 X := hw2'.to_sup_of_normal_right' h.isPGroup_B (zpowers_le.mpr hwW)
  have hXC : X ≤ coreActionKernel h.V := sup_le (zpowers_le.mpr hwV) hBC
  obtain ⟨Q, hQ⟩ := (hX2.comap_subtype (K := coreActionKernel h.V)).exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup ↥(coreActionKernel h.V)) = Nat.card h.B := by
    rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity R₀, hR₀,
      ← Subgroup.card_map_of_injective (coreActionKernel h.V).subtype_injective,
      subgroupOf_map_subtype, inf_of_le_left hBC]
  have h3 : Nat.card (X.subgroupOf (coreActionKernel h.V)) = Nat.card X := by
    rw [← Subgroup.card_map_of_injective (coreActionKernel h.V).subtype_injective,
      subgroupOf_map_subtype, inf_of_le_left hXC]
  have hcard : Nat.card X ≤ Nat.card h.B := by
    rw [← h3, ← hQcard]
    exact Subgroup.card_le_of_le hQ
  have hXB : h.B = X := eq_of_le_of_card_ge le_sup_right hcard
  rw [hXB]
  exact mem_sup_left (mem_zpowers w)

theorem mem_W_of_mem_T {t : H} (ht : t ∈ h.T) : t ∈ h.W := (mem_inf.mp (mem_inf.mp ht).1).2

theorem mem_S_of_mem_T {t : H} (ht : t ∈ h.T) : t ∈ h.S := (mem_inf.mp (mem_inf.mp ht).1).1

theorem mem_kernel_of_mem_T {t : H} (ht : t ∈ h.T) : t ∈ coreActionKernel h.J :=
  (mem_inf.mp (mem_inf.mp ht).2).2

abbrev E (t : H) : Subgroup H := zpowers t ⊔ h.B

theorem isPGroup_E {t : H} (ht : t ∈ h.T) : IsPGroup 2 (E h t) := by
  have h1 : IsPGroup 2 (zpowers t) := h.isPGroup_S.to_le (zpowers_le.mpr (mem_S_of_mem_T h ht))
  exact h1.to_sup_of_normal_right' h.isPGroup_B (zpowers_le.mpr (mem_W_of_mem_T h ht))

theorem E_le_kernel {t : H} (ht : t ∈ h.T) : E h t ≤ coreActionKernel h.J :=
  sup_le (zpowers_le.mpr (mem_kernel_of_mem_T h ht)) h.B_le_coreActionKernel

theorem fixedLayer_E_le {t : H} (ht : t ∈ h.T) :
    GSLit.fixedLayer h.J (E h t) ≤ GSLit.fixedLayer h.J h.B :=
  (GSLit.fixedLayer_nested h.isQuasisimple_J (E_le_kernel h ht) (isPGroup_E h ht)
    le_sup_right).1

theorem nonempty_equiv_E {t : H} (ht : t ∈ h.T) :
    Nonempty (↥(GSLit.fixedLayer h.J (E h t)) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer h.J (E h t)) ≃*
      OddBar h.J) := by
  have hle : GSLit.fixedLayer h.J (E h t) ≤ h.J :=
    (GSLit.fixedLayer_le_inf h.J _).trans inf_le_left
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore h.isQuasisimple_J (E_le_kernel h ht)
    (isPGroup_E h ht)).1
  obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hle hsup
  exact ⟨e⟩

theorem exists_fixed (hKa : conjugate h.K h.a = h.K) {t : H} (ht : t ∈ h.T) :
    ∃ X : Subgroup (OddBar h.K), ⁅X, X⁆ = X ∧ Nat.card (OddBar h.J) ∣ Nat.card X ∧
      (∀ x ∈ X, actW h hKa ⟨h.a, h.a_mem_normalizer⟩ x = x) ∧
      (∀ x ∈ X, actW h hKa ⟨t, mem_W_of_mem_T h ht⟩ x = x) := by
  set Y := GSLit.fixedLayer h.J (E h t) with hYdef
  have hYK : Y ≤ h.K := (fixedLayer_E_le h ht).trans (fixedLayer_le_K h hKa)
  obtain ⟨e⟩ := nonempty_equiv_E h ht
  refine ⟨imK h Y, imK_commutator_eq h hYK (fixedLayer_commutator_eq _ _), card_dvd_imK h hYK e,
    fun x hx => actW_apply_of_mem_imK h hKa (fun y hy => ?_) hx,
    fun x hx => actW_apply_of_mem_imK h hKa (fun y hy => ?_) hx⟩
  · have hyJ : y ∈ h.J := (mem_inf.mp ((GSLit.fixedLayer_le_inf h.J _) hy)).1
    exact (mem_centralizer_singleton_iff.mp (h.J_le hyJ)).symm
  · have hyC := (mem_inf.mp ((GSLit.fixedLayer_le_inf h.J _) hy)).2
    exact mem_centralizer_iff.mp hyC t (mem_sup_left (mem_zpowers t))

theorem mem_of_actW (hKa : conjugate h.K h.a = h.K) {t : H} (ht : t ∈ h.T)
    (hcase : actW h hKa ⟨t, mem_W_of_mem_T h ht⟩ = 1 ∨
      actW h hKa ⟨t, mem_W_of_mem_T h ht⟩ = actW h hKa ⟨h.a, h.a_mem_normalizer⟩) :
    t ∈ zpowers h.a ⊔ h.B := by
  obtain ⟨k, hk⟩ := h.orderOf_eq_two_pow_of_mem_S (mem_S_of_mem_T h ht)
  have ht2 : t ^ 2 ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  rcases hcase with h1 | h1
  · have htK : t ∈ coreActionKernel h.K :=
      mem_coreActionKernel_of_oddBarConj_eq_one
        (g := inclusion (W_le_normalizer_K h hKa) ⟨t, mem_W_of_mem_T h ht⟩) h1
    exact mem_sup_right (mem_B_of_mem_coreActionKernel' h hKa (mem_W_of_mem_T h ht) htK
      ⟨k, ht2⟩)
  · set w : h.W := ⟨t, mem_W_of_mem_T h ht⟩ * (⟨h.a, h.a_mem_normalizer⟩ : h.W)⁻¹ with hw
    have hw1 : actW h hKa w = 1 := by rw [hw, map_mul, map_inv, h1, mul_inv_cancel]
    have hwK : (w : H) ∈ coreActionKernel h.K :=
      mem_coreActionKernel_of_oddBarConj_eq_one (g := inclusion (W_le_normalizer_K h hKa) w) hw1
    have hta : Commute t h.a := h.comm_a (mem_S_of_mem_T h ht)
    have hc : Commute t h.a⁻¹ := hta.inv_right
    have ha2' : h.a⁻¹ ^ 2 = 1 := by rw [inv_pow, pow_two, ha2, inv_one]
    have hw2 : ∃ n : ℕ, (w : H) ^ 2 ^ n = 1 := by
      refine ⟨k + 1, ?_⟩
      show (t * h.a⁻¹) ^ 2 ^ (k + 1) = 1
      rw [hc.mul_pow, pow_succ, pow_mul, ht2, one_pow, one_mul, pow_mul', ha2', one_pow]
    have hwB := mem_B_of_mem_coreActionKernel' h hKa w.2 hwK hw2
    have htw : t = (w : H) * h.a := by
      show t = t * h.a⁻¹ * h.a
      rw [inv_mul_cancel_right]
    rw [htw]
    exact mul_mem (mem_sup_right hwB) (mem_sup_left (mem_zpowers _))

theorem T_le_of_fixCat (hKa : conjugate h.K h.a = h.K)
    (hcat : FixCat (OddBar h.K) (Nat.card (OddBar h.J))) : h.T ≤ zpowers h.a ⊔ h.B := by
  intro t ht
  obtain ⟨k, hk⟩ := h.orderOf_eq_two_pow_of_mem_S (mem_S_of_mem_T h ht)
  have ht2 : t ^ 2 ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  set α := actW h hKa ⟨h.a, h.a_mem_normalizer⟩ with hα
  set τ := actW h hKa ⟨t, mem_W_of_mem_T h ht⟩ with hτ
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul]
    have : (⟨h.a, h.a_mem_normalizer⟩ * ⟨h.a, h.a_mem_normalizer⟩ : h.W) = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hα1 : α ≠ 1 := oddBarConj_a_ne_one h hKa
  have hτα : τ * α = α * τ := by
    rw [hτ, hα, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.comm_a (mem_S_of_mem_T h ht))
  have hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1 := by
    refine ⟨k, ?_⟩
    rw [hτ, ← map_pow]
    have : (⟨t, mem_W_of_mem_T h ht⟩ : h.W) ^ 2 ^ k = 1 := Subtype.ext ht2
    rw [this, map_one]
  obtain ⟨X, hXp, hXd, hXa, hXt⟩ := exists_fixed h hKa ht
  exact mem_of_actW h hKa ht (hcat α τ hα2 hα1 hτα hτ2 X hXp hXd hXa hXt)

end Idx

end CFSG.ComponentClassification.CatFactsL4U4
