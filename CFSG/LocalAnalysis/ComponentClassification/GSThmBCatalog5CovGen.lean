module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovBase

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open Subgroup

theorem card_of_smallQ' {Y : Type} [Group Y] (h : SmallQ Y) :
    (∃ q, 5 ≤ q ∧ Nat.card Y = Open.ordA 1 q) ∨ Nat.card Y = 2520 := by
  rcases h with ⟨p, f, -, hp2, -, hq, hm⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨p ^ f, hq, (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hm)).1 rfl⟩
  · exact Or.inr ((Nat.card_congr e.toEquiv).trans card_alternatingGroup_seven)

theorem not_ordA_dvd_of_lt {N B : ℕ} (hN : 0 < N) (hB : 2 * (N + 1) ≤ B * (B ^ 2 - 1))
    (hsmall : ∀ m, 5 ≤ m → m < B → ¬ m * (m ^ 2 - 1) / Nat.gcd 2 (m - 1) ∣ N) (m : ℕ)
    (hm5 : 5 ≤ m) : ¬ Open.ordA 1 m ∣ N := by
  unfold Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge m B with hm | hm
  · exact hsmall m hm5 hm
  · intro hd
    have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (N + 1) ≤ m * (m ^ 2 - 1) := by
      refine hB.trans (Nat.mul_le_mul hm (Nat.sub_le_sub_right ?_ 1))
      exact Nat.pow_le_pow_left hm 2
    have h1 : N < m * (m ^ 2 - 1) / Nat.gcd (1 + 1) (m - 1) := lt_div_of_mul_succ_le hg hle hX
    have h2 := Nat.le_of_dvd hN hd
    omega

theorem false_of_smallQ_dvd {Y : Type} [Group Y] (h : SmallQ Y) {N : ℕ} (hd : Nat.card Y ∣ N)
    (hq : ∀ q, 5 ≤ q → ¬ Open.ordA 1 q ∣ N) (h7 : ¬ 2520 ∣ N) : False := by
  rcases card_of_smallQ' h with ⟨q, hq5, hc⟩ | hc
  · exact hq q hq5 (hc ▸ hd)
  · exact h7 (hc ▸ hd)

theorem false_of_component_card {G : Type} [Group G] [Finite G] {M C : Subgroup G}
    (hM : CFSG.Assembly.IsComponentOf M C) (hMt : SmallQ (↥M ⧸ center ↥M)) {N : ℕ}
    (hC : Nat.card C ∣ N) (hq : ∀ q, 5 ≤ q → ¬ Open.ordA 1 q ∣ N) (h7 : ¬ 2520 ∣ N) :
    False := by
  refine false_of_smallQ_dvd hMt ?_ hq h7
  refine (Subgroup.card_quotient_dvd_card (center ↥M)).trans ?_
  exact (Subgroup.card_dvd_of_le hM.1).trans hC

theorem nonempty_quotient_center_equiv {L X : Type*} [Group L] [Group X] (π : L →* X)
    (hπ : Function.Surjective π) (hker : π.ker = center L) :
    Nonempty (L ⧸ center L ≃* X) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩

theorem false_of_top' {L X : Type} [Group L] [Group X] [Finite X]
    (hLq : CFSG.Assembly.IsQuasisimple L) (π : L →* X) (hπ : Function.Surjective π)
    (hker : π.ker = center L) {M : Subgroup X} (hM : CFSG.Assembly.IsComponentOf M ⊤)
    (hMt : SmallQ (↥M ⧸ center ↥M)) (hq : ∀ q, Open.ordA 1 q ≠ Nat.card X)
    (h7 : Nat.card X ≠ 2520) : False := by
  obtain ⟨e⟩ := nonempty_quotient_center_equiv π hπ hker
  have hs : IsSimpleGroup (L ⧸ center L) := hLq.2
  have : IsSimpleGroup X := MulEquiv.isSimpleGroup e.symm
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hZ : center L = ⊤ := by
      rw [eq_top_iff, ← hLq.1, commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [← hker, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
        map_inv, hc (π x) (π y)]
      group
    have hsub : Subsingleton (L ⧸ center L) := by
      rw [hZ]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_subsingleton (L ⧸ center L)) hsub
  exact false_of_component_top hnc hM hMt hq h7

section Outer

variable {L : Type*} [Group L] (α : MulAut L)

theorem isQuasisimple_Lsub (hLq : CFSG.Assembly.IsQuasisimple L) :
    CFSG.Assembly.IsQuasisimple (Lsub α) := by
  rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hLq ⊢
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr (eL α)).1 hLq

theorem center_Lsub {t : L} (hZ : center L = zpowers t) :
    center (Lsub α) = zpowers (eL α t) := by
  rw [← Subgroup.map_center_eq (eL α), hZ, MonoidHom.map_zpowers]
  rfl

theorem centralizer_Lsub_eq (hα : α * α = 1) (hout : ∀ n : L, ¬ ∀ y, α y = n * y * n⁻¹)
    {t : L} (hZ : center L = zpowers t) :
    centralizer ((Lsub α : Subgroup (Semi α)) : Set (Semi α)) =
      zpowers ((eL α t : Lsub α) : Semi α) := by
  rw [centralizer_Lsub α hα hout, hZ, MonoidHom.map_zpowers]
  rfl

theorem ker_comp_eL_symm {X : Type*} [Group X] (π : L →* X) {t : L} (hker : π.ker = zpowers t) :
    (π.comp (eL α).symm.toMonoidHom).ker = zpowers (eL α t) := by
  ext v
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, mem_zpowers_iff,
    mem_zpowers_iff]
  simp only [MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, (eL α).symm.injective ?_⟩
    rw [map_zpow, MulEquiv.symm_apply_apply]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, map_zpow, MulEquiv.symm_apply_apply]

theorem twist_of_ext {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t)
    (hα : α * α = 1) (hα1 : α ≠ 1)
    (hext : ∀ x y : Semi α, x ∉ Lsub α → orderOf x = 2 → y ∉ Lsub α → orderOf y = 2 →
      ∃ l : Lsub α, (l : Semi α) * x * (l : Semi α)⁻¹ = y) :
    ∃ h : L, α h = h * t := by
  have htc : t ∈ center L := hZ ▸ mem_zpowers t
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set p := pElt α
  have hp : orderOf p = 2 := orderOf_pElt α hα hα1
  have hpL : p ∉ Lsub α := pElt_not_mem α hα1
  have hαt : α t = t := by
    have hc : α t ∈ center L := by
      rw [mem_center_iff]
      intro g
      calc g * α t = α (α.symm g * t) := by rw [map_mul, MulEquiv.apply_symm_apply]
        _ = α (t * α.symm g) := by rw [mem_center_iff.mp htc]
        _ = α t * g := by rw [map_mul, MulEquiv.apply_symm_apply]
    rw [hZ] at hc
    rcases eq_one_or_eq_of_mem_zpowers ht2 hc with h | h
    · exfalso
      have h1 : t = 1 := α.injective (by rw [h, map_one])
      rw [h1, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · exact h
  set y : Semi α := SemidirectProduct.inl t * p with hydef
  have htL : (SemidirectProduct.inl t : Semi α) ∈ Lsub α := ⟨t, rfl⟩
  have hyL : y ∉ Lsub α := fun hy => hpL (by
    have := (Lsub α).mul_mem ((Lsub α).inv_mem htL) hy
    rwa [hydef, ← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hy2 : y * y = 1 := by
    calc y * y = SemidirectProduct.inl t * (p * SemidirectProduct.inl t * p⁻¹) * (p * p) := by
          rw [hydef]; group
      _ = 1 := by
        rw [pElt_conj, pElt_mul_self α hα, hαt, mul_one, ← map_mul, ht2, map_one]
  have hyo : orderOf y = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hy2) fun h => hyL (h ▸ one_mem _)
  obtain ⟨l, hl⟩ := hext p y hpL hp hyL hyo
  obtain ⟨l₀, hl₀⟩ := l.2
  refine ⟨l₀, ?_⟩
  rw [← hl₀] at hl
  have h1 : SemidirectProduct.inl l₀ * p * (SemidirectProduct.inl l₀)⁻¹ =
      SemidirectProduct.inl (l₀ * (α l₀)⁻¹) * p := by
    calc SemidirectProduct.inl l₀ * p * (SemidirectProduct.inl l₀)⁻¹ =
        SemidirectProduct.inl l₀ * (p * SemidirectProduct.inl l₀⁻¹ * p⁻¹) * p := by
          rw [map_inv]; group
      _ = SemidirectProduct.inl (l₀ * (α l₀)⁻¹) * p := by
          rw [pElt_conj, map_inv, ← map_mul]
  rw [h1, hydef] at hl
  have h2 : l₀ * (α l₀)⁻¹ = t := SemidirectProduct.inl_injective (mul_right_cancel hl)
  calc α l₀ = t⁻¹ * l₀ := by rw [← h2]; group
    _ = l₀ * t := by rw [htinv, mem_center_iff.mp htc]

end Outer

theorem exists_disp_of_pair {L X : Type*} [Group L] [Group X] (π : L →* X)
    (hπ : Function.Surjective π) {t : L} (ht : orderOf t = 2) (P : X → Prop)
    (hinv : ∀ (w : X) (W : L), π W = w → orderOf w = 2 → ¬ P w → W * W = 1)
    {x y : X} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) (hc : x * y = y * x)
    (hd : ∀ U V : L, π U = x → π V = y → U⁻¹ * V⁻¹ * U * V = t) :
    ∃ u v : X, orderOf u = 2 ∧ P u ∧ ∀ U V : L, π U = u → π V = v → U⁻¹ * V⁻¹ * U * V = t := by
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  by_cases h1 : P x
  · exact ⟨x, y, hx, h1, hd⟩
  by_cases h2 : P y
  · refine ⟨y, x, hy, h2, fun U V hU hV => ?_⟩
    have := hd V U hV hU
    calc U⁻¹ * V⁻¹ * U * V = (V⁻¹ * U⁻¹ * V * U)⁻¹ := by group
      _ = t := by rw [this, htinv]
  have hx2 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hxy2 : orderOf (x * y) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (x * y) ^ 2 = x * (y * x) * y := by rw [sq]; group
        _ = (x * x) * (y * y) := by rw [← hc]; group
        _ = 1 := by rw [hx2, hy2, one_mul]
    · intro h
      apply hxy
      calc x = x * (y * y) := by rw [hy2, mul_one]
        _ = (x * y) * y := by group
        _ = y := by rw [h, one_mul]
  by_cases h3 : P (x * y)
  · refine ⟨x * y, x, hxy2, h3, fun U V hU hV => ?_⟩
    have hY' : π (V⁻¹ * U) = y := by
      rw [map_mul, map_inv, hU, hV, ← mul_assoc, inv_mul_cancel, one_mul]
    have := hd V (V⁻¹ * U) hV hY'
    calc U⁻¹ * V⁻¹ * U * V = (V⁻¹ * (V⁻¹ * U)⁻¹ * V * (V⁻¹ * U))⁻¹ := by group
      _ = t := by rw [this, htinv]
  exfalso
  obtain ⟨X₁, hX⟩ := hπ x
  obtain ⟨Y₁, hY⟩ := hπ y
  have hX2 := hinv x X₁ hX hx h1
  have hY2 := hinv y Y₁ hY hy h2
  have hXY2 := hinv (x * y) (X₁ * Y₁) (by rw [map_mul, hX, hY]) hxy2 h3
  have hXi : X₁⁻¹ = X₁ := inv_eq_of_mul_eq_one_right hX2
  have hYi : Y₁⁻¹ = Y₁ := inv_eq_of_mul_eq_one_right hY2
  have h1' : t = 1 := by
    rw [← hd X₁ Y₁ hX hY, hXi, hYi, ← hXY2]
    group
  rw [h1', orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem twist_of_disp {L X : Type*} [Group L] [Group X] (π : L →* X)
    (hπ : Function.Surjective π) {t : L} (htc : t ∈ center L) (ht2 : t * t = 1) (Y : L)
    (hY2 : Y * Y ∈ center L) {u v g : X} (hg : g * u * g⁻¹ = π Y)
    (hd : ∀ U V : L, π U = u → π V = v → U⁻¹ * V⁻¹ * U * V = t) :
    ∃ h : L, Y * h * Y⁻¹ = h * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨G, hG⟩ := hπ g
  obtain ⟨V, hV⟩ := hπ v
  set U := G⁻¹ * Y * G with hUdef
  have hU : π U = u := by
    rw [hUdef, map_mul, map_mul, map_inv, hG, ← hg]
    group
  have hd' := hd U V hU hV
  have hU2 : U * U ∈ center L := by
    have h1 : U * U = G⁻¹ * (Y * Y) * G := by rw [hUdef]; group
    rw [h1, mem_center_iff.mp hY2 G⁻¹, inv_mul_cancel_right]
    exact hY2
  have h1 : U⁻¹ * V * U = V * t := by
    calc U⁻¹ * V * U = V * (U⁻¹ * V⁻¹ * U * V)⁻¹ := by group
      _ = V * t := by rw [hd', htinv]
  have hconj : U * V * U⁻¹ = V * t := by
    calc U * V * U⁻¹ = (U * U) * (U⁻¹ * V * U) * (U * U)⁻¹ := by group
      _ = (U * U) * (V * t) * (U * U)⁻¹ := by rw [h1]
      _ = V * t := by rw [(mem_center_iff.mp hU2 (V * t)).symm]; group
  refine ⟨G * V * G⁻¹, ?_⟩
  have hYU : Y = G * U * G⁻¹ := by rw [hUdef]; group
  calc Y * (G * V * G⁻¹) * Y⁻¹ = G * (U * V * U⁻¹) * G⁻¹ := by rw [hYU]; group
    _ = G * V * (t * G⁻¹) := by rw [hconj]; group
    _ = G * V * G⁻¹ * t := by rw [← mem_center_iff.mp htc G⁻¹]; group

end CFSG.ComponentClassification.GSThmB.Cov
