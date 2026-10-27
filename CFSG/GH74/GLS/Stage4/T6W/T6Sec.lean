module

public import CFSG.GH74.GLS.Stage4.T6W.T6Ord
public import CFSG.GH74.GLS.Stage4.T6Mod

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6W

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem t6_coord_equiv {F : Type} [Field F] {φ : SL2 F →* G} (hinj : Function.Injective φ) {K : Subgroup G}
    (hrange : φ.range = K) {z : G} (hz : φ (negOne F) = z) (hzK : z ∈ K) :
    ∃ e : ↥K ≃* SL2 F, e ⟨z, hzK⟩ = negOne F := by
  refine ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm, ?_⟩
  show (MonoidHom.ofInjective hinj).symm (MulEquiv.subgroupCongr hrange.symm ⟨z, hzK⟩) = negOne F
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  show z = φ (negOne F)
  rw [hz]

structure T6Mod (N : T2N3 G) (p m : ℕ) : Prop where
  card : ∀ A B : Subgroup G, B ≤ A → (∀ k ∈ N.K₁, ∀ a ∈ A, k * a * k⁻¹ ∈ A) →
    (∀ k ∈ N.K₁, ∀ b ∈ B, k * b * k⁻¹ ∈ B) → (∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) →
    (∀ a ∈ A, a ^ p ∈ B) → (∀ a ∈ A, N.z * a * N.z⁻¹ * a ∈ B) → B ≠ A →
    p ^ (2 * m) ≤ B.relIndex A
  fpf : ∀ A B : Subgroup G, B ≤ A → (∀ k ∈ N.K₁, ∀ a ∈ A, k * a * k⁻¹ ∈ A) →
    (∀ k ∈ N.K₁, ∀ b ∈ B, k * b * k⁻¹ ∈ B) → (∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) →
    (∀ a ∈ A, a ^ p ∈ B) → (∀ a ∈ A, N.z * a * N.z⁻¹ * a ∈ B) → B.relIndex A = p ^ (2 * m) →
    ∀ y ∈ N.K₁, y ≠ 1 → ¬ p ∣ orderOf y → ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B → a ∈ B

theorem t6Mod_of (h11b : IVK_11_1b_nat) {N : T2N3 G} {u : G} {p m : ℕ} (h : T6CtxW N u p)
    (hm : N.q₁ = p ^ m) : T6Mod N p m := by
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₁
  obtain ⟨e, he⟩ := t6_coord_equiv hinj hrange hz h.sec5.loc.z_mem_K₁
  have hF : Nat.card F = p ^ m := hcard.trans hm
  exact
    { card := fun A B hBA hKA hKB hcomm hexp hinv hne =>
        t6_modB_card h.prime h.p_ne_two hF e h.sec5.loc.z_mem_K₁ he hBA hKA hKB hcomm hexp hinv hne
      fpf := fun A B hBA hKA hKB hcomm hexp hinv hcd y hy hy1 hyp =>
        t6_modB_fpf h11b h.prime h.p_ne_two hF e h.sec5.loc.z_mem_K₁ he hBA hKA hKB hcomm hexp hinv hcd hy hy1 hyp }

section Order

variable {N : T2N3 G} {u : G} {p m n : ℕ}

theorem R₂_sec_card (h : T6CtxW N u p) (hm₁ : ∃ m : ℕ, N.q₁ = p ^ m) (hMod : T6Mod N p m) {A B : Subgroup G} (hXB : N.X₂ ≤ B)
    (hBA : B ≤ A) (hAR : A ≤ R₂ N p) (hKA : ∀ k ∈ N.K₁, ∀ a ∈ A, k * a * k⁻¹ ∈ A)
    (hKB : ∀ k ∈ N.K₁, ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hne : B ≠ A) : p ^ (2 * m) ≤ B.relIndex A :=
  hMod.card A B hBA hKA hKB (fun a ha a' ha' => hXB ((R₂_inv_comm h).2 a (hAR ha) a' (hAR ha')))
    (fun a ha => hXB (R₂_exp h hm₁ a (hAR ha))) (fun a ha => hXB ((R₂_inv_comm h).1 a (hAR ha))) hne

theorem R₂_sec_fpf (h : T6CtxW N u p) (hm₁ : ∃ m : ℕ, N.q₁ = p ^ m) (hMod : T6Mod N p m) {A B : Subgroup G} (hXB : N.X₂ ≤ B)
    (hBA : B ≤ A) (hAR : A ≤ R₂ N p) (hKA : ∀ k ∈ N.K₁, ∀ a ∈ A, k * a * k⁻¹ ∈ A)
    (hKB : ∀ k ∈ N.K₁, ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hcd : B.relIndex A = p ^ (2 * m)) {y : G}
    (hyK : y ∈ N.K₁) (hy1 : y ≠ 1) (hyp : ¬ p ∣ orderOf y) :
    ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B → a ∈ B :=
  hMod.fpf A B hBA hKA hKB (fun a ha a' ha' => hXB ((R₂_inv_comm h).2 a (hAR ha) a' (hAR ha')))
    (fun a ha => hXB (R₂_exp h hm₁ a (hAR ha))) (fun a ha => hXB ((R₂_inv_comm h).1 a (hAR ha))) hcd y hyK hy1
    hyp

theorem K₁_sec_X₂R₂ (h : T6CtxW N u p) :
    (∀ k ∈ N.K₁, ∀ a ∈ R₂ N p, k * a * k⁻¹ ∈ R₂ N p) ∧
      ∀ k ∈ N.K₁, ∀ b ∈ N.X₂, k * b * k⁻¹ ∈ N.X₂ :=
  ⟨fun k hk a ha => R₂_norm N p (K₁_le_M₂ h hk) ha,
    fun k hk b hb => by rw [K₁_cent_X₂ h hk hb]; exact hb⟩

theorem R₂_order (h : T6CtxW N u p) (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) (hMod : T6Mod N p m)
    {y : G} (hyK : y ∈ N.K₁) (hy1 : y ≠ 1) (hyp : ¬ p ∣ orderOf y) {R : Subgroup G}
    (hRR : R ≤ R₂ N p) (hRcard : Nat.card ↥R = N.q₂ ^ 3) (hRy : ∀ r ∈ R, y * r = r * y) :
    Nat.card ↥(R₂ N p) = N.q₁ ^ 2 * N.q₂ ^ 3 := by
  have hloc := h.sec5.loc
  have hq₂ : 3 ≤ N.q₂ := hloc.q₂_ge
  have hX₂R := X₂_le_R₂ h
  have hp1 : 1 < p := h.prime.one_lt
  have hq₂lt : N.q₂ < N.q₂ ^ 3 := by
    calc N.q₂ = N.q₂ ^ 1 := (pow_one _).symm
      _ < N.q₂ ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  obtain ⟨hKR, hKX⟩ := K₁_sec_X₂R₂ h
  have hne : N.X₂ ≠ R₂ N p := by
    intro heq
    have h1 : Nat.card ↥R ≤ Nat.card ↥(R₂ N p) := Subgroup.card_le_of_le hRR
    rw [← heq, hloc.card_X₂, hRcard] at h1
    omega
  have hnat : N.X₂.relIndex (R₂ N p) ≠ p ^ (2 * m) := by
    intro hcd
    have hfp := R₂_sec_fpf h ⟨m, hm⟩ hMod le_rfl hX₂R le_rfl hKR hKX hcd hyK hy1 hyp
    have hRX : R ≤ N.X₂ := by
      intro r hr
      apply hfp r (hRR hr)
      rw [show y * r * y⁻¹ * r⁻¹ = 1 by rw [hRy r hr]; group]
      exact N.X₂.one_mem
    have h1 : Nat.card ↥R ≤ Nat.card ↥N.X₂ := Subgroup.card_le_of_le hRX
    rw [hloc.card_X₂, hRcard] at h1
    omega
  have hle := R₂_sec_card h ⟨m, hm⟩ hMod le_rfl hX₂R le_rfl hKR hKX hne
  have hrel : N.X₂.relIndex (R₂ N p) * N.q₂ = Nat.card ↥(R₂ N p) := by
    have := Subgroup.relIndex_mul_card N.X₂ (R₂ N p)
    rwa [inf_eq_left.2 hX₂R, hloc.card_X₂] at this
  have hcR := R₂_card_RA h
  have hq₂pos : 0 < N.q₂ := by omega
  have hrelRA : N.X₂.relIndex (R₂ N p) = Nat.card ↥(RA N p u) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hq₂pos
    rw [hrel, hcR]; ring
  have hnm : n ≤ m := by
    have := hloc.q₂_le
    rw [hm, hn] at this
    exact (Nat.pow_le_pow_iff_right hp1).1 this
  rcases (RA_struct h ⟨m, hm⟩).1 with h1 | h1 | h1 | h1
  · exfalso
    rw [hrelRA, h1] at hle
    have : 1 < p ^ (2 * m) := Nat.one_lt_pow (by
      have := hloc.q₁_ge
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [hm, h0] at this; simp at this
      · omega) hp1
    omega
  · exfalso
    apply hnat
    rw [hrelRA, h1, hm, ← pow_mul, mul_comm m 2]
  · exfalso
    rw [hrelRA, h1, hn] at hle
    have h2 : 2 * m ≤ 2 * n := by
      have : p ^ (2 * m) ≤ p ^ (2 * n) := by calc p ^ (2 * m) ≤ (p ^ n) ^ 2 := by simpa using hle
        _ = p ^ (2 * n) := by rw [← pow_mul, mul_comm]
      exact (Nat.pow_le_pow_iff_right hp1).1 this
    have hmn : m = n := by omega
    apply hnat
    rw [hrelRA, h1, hn, ← hmn, ← pow_mul, mul_comm m 2]
  · rw [hcR, h1]; ring

theorem K₁_irred_of (h : T6CtxW N u p) (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) (hMod : T6Mod N p m)
    {y : G} (hyK : y ∈ N.K₁) (hy1 : y ≠ 1) (hyp : ¬ p ∣ orderOf y) {R : Subgroup G}
    (hRR : R ≤ R₂ N p) (hRcard : Nat.card ↥R = N.q₂ ^ 3) (hRy : ∀ r ∈ R, y * r = r * y) :
    ∀ V : Subgroup G, N.X₂ ≤ V → V ≤ R₂ N p → (∀ x ∈ N.K₁, ∀ v ∈ V, x * v * x⁻¹ ∈ V) →
      V = N.X₂ ∨ V = R₂ N p := by
  intro V hXV hVR hKV
  by_contra hcon
  push Not at hcon
  obtain ⟨hVX, hVR'⟩ := hcon
  have hloc := h.sec5.loc
  have hX₂R := X₂_le_R₂ h
  have hp1 : 1 < p := h.prime.one_lt
  have hq₂lt : N.q₂ < N.q₂ ^ 3 := by
    calc N.q₂ = N.q₂ ^ 1 := (pow_one _).symm
      _ < N.q₂ ^ 3 := Nat.pow_lt_pow_right (by have := hloc.q₂_ge; omega) (by norm_num)
  obtain ⟨hKR, hKX⟩ := K₁_sec_X₂R₂ h
  have hne₁ : N.X₂ ≠ V := fun e => hVX e.symm
  have hne₂ : V ≠ R₂ N p := hVR'
  have hc₁ := R₂_sec_card h ⟨m, hm⟩ hMod le_rfl hXV hVR hKV hKX hne₁
  have hc₂ := R₂_sec_card h ⟨m, hm⟩ hMod hXV hVR le_rfl hKR hKV hne₂
  have hOrd := R₂_order h hm hn hMod hyK hy1 hyp hRR hRcard hRy
  have hrel : N.X₂.relIndex (R₂ N p) * N.q₂ = Nat.card ↥(R₂ N p) := by
    have := Subgroup.relIndex_mul_card N.X₂ (R₂ N p)
    rwa [inf_eq_left.2 hX₂R, hloc.card_X₂] at this
  have hq₂pos : 0 < N.q₂ := by have := hloc.q₂_ge; omega
  have hrelv : N.X₂.relIndex (R₂ N p) = N.q₁ ^ 2 * N.q₂ ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hq₂pos
    rw [hrel, hOrd]; ring
  have hprod : N.X₂.relIndex V * V.relIndex (R₂ N p) = N.X₂.relIndex (R₂ N p) :=
    Subgroup.relIndex_mul_relIndex N.X₂ V (R₂ N p) hXV hVR
  have hnm : n ≤ m := by
    have := hloc.q₂_le
    rw [hm, hn] at this
    exact (Nat.pow_le_pow_iff_right hp1).1 this
  have hpp : ∀ a b : ℕ, p ^ a * p ^ b = p ^ (a + b) := fun a b => (pow_add p a b).symm
  have hval : N.X₂.relIndex V * V.relIndex (R₂ N p) = p ^ (2 * m + 2 * n) := by
    rw [hprod, hrelv, hm, hn, ← pow_mul, ← pow_mul, ← pow_add]
    ring_nf
  have hmn : m = n := by
    have h1 : p ^ (2 * m) * p ^ (2 * m) ≤ p ^ (2 * m + 2 * n) := by
      rw [← hval]; exact Nat.mul_le_mul hc₁ hc₂
    rw [hpp] at h1
    have := (Nat.pow_le_pow_iff_right hp1).1 h1
    omega
  subst hmn
  have hppos : 0 < p ^ (2 * m) := pow_pos (by omega) _
  have hA : N.X₂.relIndex V = p ^ (2 * m) := by
    apply le_antisymm _ hc₁
    have h1 : N.X₂.relIndex V * p ^ (2 * m) ≤ p ^ (2 * m) * p ^ (2 * m) := by
      calc N.X₂.relIndex V * p ^ (2 * m) ≤ N.X₂.relIndex V * V.relIndex (R₂ N p) :=
            Nat.mul_le_mul_left _ hc₂
        _ = p ^ (2 * m) * p ^ (2 * m) := by rw [hval, hpp]
    exact Nat.le_of_mul_le_mul_right h1 hppos
  have hB : V.relIndex (R₂ N p) = p ^ (2 * m) := by
    apply le_antisymm _ hc₂
    have h1 : p ^ (2 * m) * V.relIndex (R₂ N p) ≤ p ^ (2 * m) * p ^ (2 * m) := by
      calc p ^ (2 * m) * V.relIndex (R₂ N p) ≤ N.X₂.relIndex V * V.relIndex (R₂ N p) :=
            Nat.mul_le_mul_right _ hc₁
        _ = p ^ (2 * m) * p ^ (2 * m) := by rw [hval, hpp]
    exact Nat.le_of_mul_le_mul_left h1 hppos
  have hf₁ := R₂_sec_fpf h ⟨m, hm⟩ hMod le_rfl hXV hVR hKV hKX hA hyK hy1 hyp
  have hf₂ := R₂_sec_fpf h ⟨m, hm⟩ hMod hXV hVR le_rfl hKR hKV hB hyK hy1 hyp
  have hRX : R ≤ N.X₂ := by
    intro r hr
    have h1 : y * r * y⁻¹ * r⁻¹ = 1 := by rw [hRy r hr]; group
    have hrV : r ∈ V := hf₂ r (hRR hr) (by rw [h1]; exact V.one_mem)
    exact hf₁ r hrV (by rw [h1]; exact N.X₂.one_mem)
  have h1 : Nat.card ↥R ≤ Nat.card ↥N.X₂ := Subgroup.card_le_of_le hRX
  rw [hloc.card_X₂, hRcard] at h1
  omega

end Order

end CFSG.GH74.GLS.Stage4.Rest.T6W
