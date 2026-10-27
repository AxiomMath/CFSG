module

public import CFSG.ClassicalInvolution.Asc77.AscE187EndA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem E187C.exists_v_sq_centralizes_of (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    {K₁ : Subgroup G} {t x : G}
    (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) (hx : IsPGroup 2 (Subgroup.zpowers x))
    (hxK : conjSub x K₁ = K₁) :
    ∃ v ∈ K₁, orderOf v = 4 ∧ (x * x) * v = v * (x * x) := by
  set D : Subgroup G := Subgroup.zpowers x with hD
  have hDN : D ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [hD, Subgroup.zpowers_le]
    exact mem_normalizer_iff_conjSub_eq.mpr hxK
  obtain ⟨Q, hQ, hQD⟩ := exists_sylow_normalized hx hDN
  have hQR : Q ∈ RSet Ω := mem_RSet_of_isSylow2In hK₁ hQ
  have h8 : 8 ≤ Nat.card Q := h8R hQR
  have htQ : t ∈ Q := mem_of_isUniqueInvolution_of_isPGroup ht hQ.1 hQ.2.1 (by omega)
  have hQt : IsUniqueInvolution Q t :=
    ⟨htQ, ht.ne_one, ht.sq, fun y hy hy2 => ht.unique y (hQ.1 hy) hy2⟩
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := fun d hd =>
    mem_normalizer_iff_conjSub_eq.mpr (hQD d hd)
  have hPp : IsPGroup 2 ↥(D ⊔ Q) := hx.to_sup_of_normal_right' hQ.2.1 hDQ
  have hTn : ∀ y ∈ D ⊔ Q, conjSub y Q = Q := by
    intro y hy
    have hle : D ⊔ Q ≤ Subgroup.normalizer (Q : Set G) := sup_le hDQ Subgroup.le_normalizer
    exact mem_normalizer_iff_conjSub_eq.mp (hle hy)
  obtain ⟨A, hAQ, hAcyc, hAcard, hAinv⟩ :=
    exists_invariant_cyclic_order_four hPp le_sup_right hTn hQt (by omega)
  obtain ⟨v, hv⟩ := IsCyclic.exists_generator (α := ↥A)
  have hv4 : orderOf (v : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hv, hAcard]
  have hvA : (v : G) ∈ A := v.2
  have hAz : ∀ y ∈ A, y ∈ Subgroup.zpowers (v : G) := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hv ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hxD : x ∈ D := Subgroup.mem_zpowers x
  have hact : ∀ w : G, w ∈ A → x * w * x⁻¹ ∈ A := by
    intro w hw
    have := conj_mem_conjSub (n := x) hw
    rwa [hAinv x (Subgroup.mem_sup_left hxD)] at this
  have hvx : x * (v : G) * x⁻¹ = v ∨ x * (v : G) * x⁻¹ = (v : G)⁻¹ :=
    eq_or_eq_inv_of_orderOf_four hv4 (hAz _ (hact _ hvA)) (by rw [orderOf_conj_mul_inv_eq, hv4])
  refine ⟨v, hQ.1 (hAQ hvA), hv4, ?_⟩
  have h2 : x * (x * (v : G) * x⁻¹) * x⁻¹ = v := by
    rcases hvx with h | h
    · rw [h, h]
    · rw [h]
      have : x * (v : G)⁻¹ * x⁻¹ = (x * v * x⁻¹)⁻¹ := by group
      rw [this, h, inv_inv]
  have e : (x * x) * (v : G) * (x * x)⁻¹ = (v : G) := by
    calc (x * x) * (v : G) * (x * x)⁻¹ = x * (x * (v : G) * x⁻¹) * x⁻¹ := by group
      _ = v := h2
  exact (mul_inv_eq_iff_eq_mul.mp e)

theorem exists_v_sq_centralizes (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K₁ : Subgroup G} {t x : G}
    (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) (hx : IsPGroup 2 (Subgroup.zpowers x))
    (hxK : conjSub x K₁ = K₁) :
    ∃ v ∈ K₁, orderOf v = 4 ∧ (x * x) * v = v * (x * x) :=
  E187C.exists_v_sq_centralizes_of (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ) hK₁ ht hx hxK

end CFSG.ClassicalInvolution.Asc77
