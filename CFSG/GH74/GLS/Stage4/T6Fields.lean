module

public import CFSG.GH74.GLS.Stage4.T6Sec

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure T6TSdata (N : T2N3 G) (p : ℕ) (y : G) (R : Subgroup G) : Prop where
  yK : y ∈ N.K₁
  y_ne : y ∉ Subgroup.zpowers N.z
  y_ord : ¬ p ∣ orderOf y
  R_p : IsPGroup p ↥R
  X_le : N.X₂ ≤ R
  R_cent : R ≤ Subgroup.centralizer (N.X₂ : Set G)
  R_card : Nat.card ↥R = N.q₂ ^ 3
  R_center : ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ N.X₂
  X_comm : N.X₂ ≤ ⁅R, R⁆
  R_comm : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ N.X₂
  R_inv : ∀ r ∈ R, N.z * r * N.z⁻¹ * r ∈ N.X₂
  y_cent : ∀ r ∈ R, y * r = r * y

omit [Finite G] in
theorem t6_not_dvd_pow_sub_one {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) : ¬ p ∣ p ^ m - 1 := by
  intro hd
  have h1 : p ∣ p ^ m := dvd_pow_self p (by omega)
  have h2 : p ∣ p ^ m - (p ^ m - 1) := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem H_pPrime_of {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    ∀ x ∈ N.H, ¬ p ∣ orderOf x := by
  have hloc := h.sec5.loc
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have := hloc.q₁_ge; rw [hm, h0] at this; simp at this
    · exact h0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := hloc.q₂_ge; rw [hn, h0] at this; simp at this
    · exact h0
  intro x hx hpx
  have hsq := Subgroup.mul_self_mem_of_index_two hloc.H_idx ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf] at hsq
  have hcomm : ∀ a ∈ N.H ⊓ N.K₁, ∀ b ∈ N.H ⊓ N.K₂, a * b = b * a := fun a ha b hb =>
    hloc.K_comm a ha.2 b hb.2
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hcomm _).1 hsq
  have hxx : x * x = a * b := hab
  have hoa : orderOf a ∣ N.q₁ - 1 := by
    rw [← hloc.card_H_K₁]
    exact Subgroup.orderOf_dvd_natCard (N.H ⊓ N.K₁) ha |> fun h' => by simpa using h'
  have hob : orderOf b ∣ N.q₂ - 1 := by
    rw [← hloc.card_H_K₂]
    exact Subgroup.orderOf_dvd_natCard (N.H ⊓ N.K₂) hb |> fun h' => by simpa using h'
  have hcab : Commute a b := hcomm a ha b hb
  have ha1 : a ^ ((N.q₁ - 1) * (N.q₂ - 1)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hoa.trans (dvd_mul_right _ _))
  have hb1 : b ^ ((N.q₁ - 1) * (N.q₂ - 1)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hob.trans (dvd_mul_left _ _))
  have hpow : x ^ (2 * ((N.q₁ - 1) * (N.q₂ - 1))) = 1 := by
    rw [pow_mul, pow_two, hxx, hcab.mul_pow, ha1, hb1, one_mul]
  have hdvd : p ∣ 2 * ((N.q₁ - 1) * (N.q₂ - 1)) :=
    hpx.trans (orderOf_dvd_of_pow_eq_one hpow)
  rcases (Nat.Prime.dvd_mul h.prime).1 hdvd with h2 | h2
  · exact h.p_ne_two ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 h2)
  · rcases (Nat.Prime.dvd_mul h.prime).1 h2 with h3 | h3
    · rw [hm] at h3; exact t6_not_dvd_pow_sub_one h.prime hm1 h3
    · rw [hn] at h3; exact t6_not_dvd_pow_sub_one h.prime hn1 h3

theorem X₁_le_K₁ {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) : N.X₁ ≤ N.K₁ := by
  rw [h.sec5.loc.K₁_eq]; exact le_sup_left

theorem ch6S6_of_parts (h11b : IVK_11_1b_nat) {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p)
    {y : G} {R : Subgroup G} (hTS : T6TSdata N p y R) (hRle : R ≤ R₂ N p) (P₀ : Subgroup G)
    (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hSyl : ∃ T : Sylow p G, (T : Subgroup G) = (R₂ N p ⊔ N.X₁) ⊔ P₀) :
    Ch6S6 (T2N4.toCh6 ⟨N, p, P₀, R₂ N p ⊔ N.X₁⟩) := by
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hMod := t6Mod_of h11b h hm
  have hy1 : y ≠ 1 := fun e => hTS.y_ne (e ▸ Subgroup.one_mem _)
  have hord := R₂_order h hm hn hMod hTS.yK hy1 hTS.y_ord hRle hTS.R_card hTS.y_cent
  have hloc := h.sec5.loc
  have hF := h.sec5.F5
  have hpgR := R₂_pGroup N h.prime
  have hX₁K := X₁_le_K₁ h
  have hnormX₁R : N.X₁ ≤ Subgroup.normalizer (R₂ N p : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype (fun n hn => R₂_norm N p (K₁_le_M₂ h (hX₁K hg)) hn)
  have hdisj : Disjoint (R₂ N p) N.X₁ := by
    rw [disjoint_iff, eq_bot_iff, ← R₂_inf_K₁ h]
    exact inf_le_inf_left _ hX₁K
  have hPcard : Nat.card ↥(R₂ N p ⊔ N.X₁) = N.q₁ ^ 3 * N.q₂ ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormX₁R hdisj,
      hord, hloc.card_X₁]
    ring
  have hFR : ∀ f ∈ N.F, ∀ r ∈ R₂ N p, f * r * f⁻¹ ∈ R₂ N p := fun f hf r hr =>
    R₂_norm N p (F_le_M₂ h hf) hr
  have hFX₁ : ∀ f ∈ N.F, ∀ x ∈ N.X₁, f * x * f⁻¹ ∈ N.X₁ := fun f hf x hx => hF.F_normX₁ f hf x hx
  have hFH : ∀ f ∈ N.F, ∀ x ∈ N.H, f * x * f⁻¹ ∈ N.H := fun f hf x hx =>
    (Subgroup.mem_normalizer_iff.1 (hF.F_normH hf) x).1 hx
  have hHR : ∀ x ∈ N.H, ∀ r ∈ R₂ N p, x * r * x⁻¹ ∈ R₂ N p := fun x hx r hr =>
    R₂_norm N p (H_le_M₂ h hx) hr
  have hHX₁ : ∀ x ∈ N.H, ∀ w ∈ N.X₁, x * w * x⁻¹ ∈ N.X₁ := fun x hx w hw =>
    hloc.H_norm_X₁ x hx w hw
  exact
    { H_pPrime := H_pPrime_of h
      X₂_le_R₂ := X₂_le_R₂ h
      R₂_card := hord
      R₂_center := R₂_center_of h hm hn hMod hTS.yK hy1 hTS.y_ord hRle hTS.R_card hTS.y_cent hTS.X_comm
      R₂_comm := (R₂_inv_comm h).2
      R₂_inv := (R₂_inv_comm h).1
      R₂_normH := hHR
      K₁_normR₂ := fun x hx r hr => R₂_norm N p (K₁_le_M₂ h hx) hr
      K₁_irred := K₁_irred_of h hm hn hMod hTS.yK hy1 hTS.y_ord hRle hTS.R_card hTS.y_cent
      P_eq := rfl
      P_pGroup := IsPGroup.of_card (n := 3 * m + 3 * n) (by
        show Nat.card ↥(R₂ N p ⊔ N.X₁) = p ^ (3 * m + 3 * n)
        rw [hPcard, hm, hn, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf)
      P_card := hPcard
      P_normH := fun x hx => t6_norm_sup (hHR x hx) (hHX₁ x hx)
      X₂_central := by
        intro x hx
        refine t6_comm_sup (fun r hr => ?_) (fun w hw => ?_)
        · have := R₂_cent h r hr x hx
          calc x * r = (r * x * r⁻¹) * r := by rw [this]
            _ = r * x := by group
        · have hwK := hX₁K hw
          have hxK : x ∈ N.K₂ := by rw [hloc.K₂_eq]; exact Subgroup.mem_sup_left hx
          exact (hloc.K_comm w hwK x hxK).symm
      P₀_le := hP₀F
      P₀_pGroup := hP₀p
      F_normB := fun f hf => by
        apply Subgroup.mem_normalizer_fintype
        exact t6_norm_sup (hFH f hf) (t6_norm_sup (hFR f hf) (hFX₁ f hf))
      P₀_normP := fun f hf => by
        apply Subgroup.mem_normalizer_fintype
        exact t6_norm_sup (hFR f (hP₀F hf)) (hFX₁ f (hP₀F hf))
      Sylow_PP₀ := hSyl }

end CFSG.GH74.GLS.Stage4.Rest.T6
