module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsField

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] {K : Type*} [Field K]

@[expose] def szSqMap (a : ℕ) (γ c : K) (x : K × K × K) : K :=
  x.1 ^ (2 ^ (a + 1) + 1) + γ * (x.1 * x.2.1) ^ 2 ^ a + (c + x.2.2) * x.2.1

structure SzRCoords2 [CharP K 2] (T₁ R₂ : Subgroup G) (t : G) (a : ℕ) (u v : G → K)
    (φ : G → K × K × K) (γ c : K) : Prop where
  v_mul : ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, v (b * b') = v b + v b'
  v_inj : ∀ b ∈ szA₁ T₁, v b = 0 → b = 1
  v_surj : ∀ w, ∃ b ∈ szA₁ T₁, v b = w
  central : ∀ x ∈ szR T₁ R₂ t, ∀ b ∈ szA₁ T₁, x * b = b * x
  comm_mem : ∀ x ∈ szR T₁ R₂ t, ∀ x' ∈ szR T₁ R₂ t, x * x' * x⁻¹ * x'⁻¹ ∈ szA₁ T₁
  sq_mem : ∀ x ∈ szR T₁ R₂ t, x ^ 2 ∈ szA₁ T₁
  mul : ∀ x ∈ szR T₁ R₂ t, ∀ x' ∈ szR T₁ R₂ t, φ (x * x') = φ x + φ x'
  ker : ∀ x ∈ szR T₁ R₂ t, φ x = 0 ↔ x ∈ szA₁ T₁
  mem : ∀ x ∈ szR T₁ R₂ t, φ x ∈ szCoordSpace K
  surj : ∀ z ∈ szCoordSpace K, ∃ x ∈ szR T₁ R₂ t, φ x = z
  thd_eq_zero_iff : ∀ x ∈ szR T₁ R₂ t, (φ x).2.2 = 0 ↔ x ∈ T₁ ⊔ R₂
  snd_eq : ∀ x ∈ szR T₁ R₂ t, (φ x).2.1 = v (x * t * x⁻¹ * t⁻¹)
  of_T₁ : ∀ y ∈ T₁, φ y = (u y, 0, 0)
  of_R₂ : ∀ r ∈ R₂, φ r = (0, v (r * t * r⁻¹ * t⁻¹), 0)
  of_t : φ t = (0, 0, 1)
  sq : ∀ x ∈ szR T₁ R₂ t, v (x ^ 2) = szSqMap a γ c (φ x)
  comm : ∀ x ∈ szR T₁ R₂ t, ∀ x' ∈ szR T₁ R₂ t,
    v (x * x' * x⁻¹ * x'⁻¹) = szCommMap a γ (φ x) (φ x')

namespace SzR2

variable {T₁ R₂ : Subgroup G} {t d : G}

section Constants

variable [Fintype K] [CharP K 2] {a : ℕ} {u v : G → K} {κ : K}
  (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
  (hK : Fintype.card K = 2 ^ (2 * a + 1))
include hS hc ha hK

theorem commutator_mul_szA₁_left {x z b : G} (hx : x ∈ szR T₁ R₂ t) (hz : z ∈ szR T₁ R₂ t)
    (hb : b ∈ szA₁ T₁) : x * b * z * (x * b)⁻¹ * z⁻¹ = x * z * x⁻¹ * z⁻¹ := by
  rw [hS.commutator_mul_left hc ha hK hx (le_szR_left T₁ R₂ t (szA₁_le T₁ hb)) hz]
  have h1 := hS.commute_szA₁ z hz b hb
  have e : b * z * b⁻¹ * z⁻¹ = 1 := by rw [← h1]; group
  rw [e, mul_one]

theorem commutator_mul_szA₁_right {x z b : G} (hx : x ∈ szR T₁ R₂ t) (hz : z ∈ szR T₁ R₂ t)
    (hb : b ∈ szA₁ T₁) : x * (z * b) * x⁻¹ * (z * b)⁻¹ = x * z * x⁻¹ * z⁻¹ := by
  rw [hS.commutator_mul_right hc ha hK hx hz (le_szR_left T₁ R₂ t (szA₁_le T₁ hb))]
  have h1 := hS.commute_szA₁ x hx b hb
  have e : x * b * x⁻¹ * b⁻¹ = 1 := by rw [h1]; group
  rw [e, mul_one]

theorem sq_eq_of_rho_eq {r r' : G} (hr : r ∈ R₂) (hr' : r' ∈ R₂)
    (h : v (r * t * r⁻¹ * t⁻¹) = v (r' * t * r'⁻¹ * t⁻¹)) : r' ^ 2 = r ^ 2 := by
  have hb := hS.inv_mul_mem_szA₁_of_rho_eq hc ha hK hr hr' h
  have hcomm := hS.commute_szA₁ r (le_szR_mid T₁ R₂ t hr) _ hb
  have key : (r * (r⁻¹ * r')) ^ 2 = r ^ 2 := by
    calc (r * (r⁻¹ * r')) ^ 2 = r * ((r⁻¹ * r') * r) * (r⁻¹ * r') := by simp only [sq]; group
      _ = r * (r * (r⁻¹ * r')) * (r⁻¹ * r') := by rw [← hcomm]
      _ = r ^ 2 * (r⁻¹ * r') ^ 2 := by simp only [sq]; group
      _ = r ^ 2 := by rw [hc.sq_eq_one_of_mem_szA₁ ha hK hb, mul_one]
  rwa [mul_inv_cancel_left] at key

theorem exists_sq_const (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) :
    ∃ c : K, ∀ r ∈ R₂, v (r ^ 2) = c * v (r * t * r⁻¹ * t⁻¹) := by
  choose! ρ hρ hρw using hS.exists_rho_eq hc ha hK
  refine ⟨v (ρ 1 ^ 2), fun r hr => ?_⟩
  have hf : ∀ w, v (ρ (κ ^ (2 ^ (a + 1) + 1) * w) ^ 2) = κ ^ (2 ^ (a + 1) + 1) * v (ρ w ^ 2) := by
    intro w
    have hdr : d⁻¹ * ρ w * d ∈ R₂ := hS.conj_d_mem (hρ w)
    rw [hS.sq_eq_of_rho_eq hc ha hK hdr (hρ _) (by rw [hS.rho_conj hc ha hK (hρ w), hρw, hρw])]
    have e : (d⁻¹ * ρ w * d) ^ 2 = d⁻¹ * ρ w ^ 2 * d := by simp only [sq]; group
    rw [e, hc.v_conj_szA₁ ha hK (hS.sq_mem_szA₁_of_mem_R₂ hc ha hK (hρ w))]
  have h0 : v (ρ 0 ^ 2) = 0 := by
    have hA : ρ 0 ∈ szA₁ T₁ := (hS.rho_eq_zero_iff hc ha hK (hρ 0)).mp (hρw 0)
    rw [hc.sq_eq_one_of_mem_szA₁ ha hK hA, hc.v_one]
  have hlin := SzCoords.linear_of_equivariant (f := fun w => v (ρ w ^ 2)) hf h0 hμ
    (v (r * t * r⁻¹ * t⁻¹))
  rw [← hS.sq_eq_of_rho_eq hc ha hK (hρ _) hr (hρw _)] at hlin
  exact hlin

theorem commutator_eq_of_coord_eq {y y' r r' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁)
    (hr : r ∈ R₂) (hr' : r' ∈ R₂) (hu : u y = u y')
    (h : v (r * t * r⁻¹ * t⁻¹) = v (r' * t * r'⁻¹ * t⁻¹)) :
    y' * r' * y'⁻¹ * r'⁻¹ = y * r * y⁻¹ * r⁻¹ := by
  have hb := hS.inv_mul_mem_szA₁_of_rho_eq hc ha hK hr hr' h
  have hb' := hc.inv_mul_mem_szA₁_of_u_eq ha hK hy hy' hu
  have hyR := le_szR_left T₁ R₂ t hy
  have e1 : y' = y * (y⁻¹ * y') := by group
  have e2 : r' = r * (r⁻¹ * r') := by group
  rw [e1, hS.commutator_mul_szA₁_left hc ha hK hyR (le_szR_mid T₁ R₂ t hr') hb', e2,
    hS.commutator_mul_szA₁_right hc ha hK hyR (le_szR_mid T₁ R₂ t hr) hb]

theorem exists_comm_const (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) :
    ∃ γ : K, ∀ y ∈ T₁, ∀ r ∈ R₂,
      v (y * r * y⁻¹ * r⁻¹) = γ * (u y * v (r * t * r⁻¹ * t⁻¹)) ^ 2 ^ a := by
  choose! ρ hρ hρw using hS.exists_rho_eq hc ha hK
  choose! τ hτ hτu using fun α => hc.surj α 0
  have hτu' : ∀ α, u (τ α) = α := fun α => (hτu α).1
  have hτR : ∀ α, τ α ∈ szR T₁ R₂ t := fun α => le_szR_left T₁ R₂ t (hτ α)
  have hρR : ∀ w, ρ w ∈ szR T₁ R₂ t := fun w => le_szR_mid T₁ R₂ t (hρ w)
  have hcomm := hS.comm_mem_szA₁ hc ha hK
  obtain ⟨β, hβ⟩ : ∃ β : K → K → K, ∀ α w, β α w = v (τ α * ρ w * (τ α)⁻¹ * (ρ w)⁻¹) :=
    ⟨_, fun _ _ => rfl⟩
  have hwd : ∀ y ∈ T₁, ∀ r ∈ R₂, v (y * r * y⁻¹ * r⁻¹) = β (u y) (v (r * t * r⁻¹ * t⁻¹)) :=
    fun y hy r hr => by
      rw [hβ, hS.commutator_eq_of_coord_eq hc ha hK hy (hτ (u y)) hr (hρ _) (hτu' _).symm
        (hρw _).symm]
  have h1 : ∀ α α' w, β (α + α') w = β α w + β α' w := by
    intro α α' w
    have hm := (hc.mul _ (hτ α) _ (hτ α')).1
    rw [hβ, hβ, hβ, hS.commutator_eq_of_coord_eq hc ha hK (mul_mem (hτ α) (hτ α'))
      (hτ (α + α')) (hρ w) (hρ w) (by rw [hm, hτu', hτu', hτu']) rfl,
      hS.commutator_mul_left hc ha hK (hτR α) (hτR α') (hρR w),
      hc.v_mul_szA₁ ha hK (hcomm _ (hτR α) _ (hρR w)) (hcomm _ (hτR α') _ (hρR w))]
  have h2' : ∀ α w w', β α (w + w') = β α w + β α w' := by
    intro α w w'
    rw [hβ, hβ, hβ, hS.commutator_eq_of_coord_eq hc ha hK (hτ α) (hτ α)
      (mul_mem (hρ w) (hρ w')) (hρ (w + w')) rfl
      (by rw [hS.rho_mul hc ha hK (hρR w) (hρR w'), hρw, hρw, hρw]),
      hS.commutator_mul_right hc ha hK (hτR α) (hρR w) (hρR w'),
      hc.v_mul_szA₁ ha hK (hcomm _ (hτR α) _ (hρR w)) (hcomm _ (hτR α) _ (hρR w'))]
  have hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w := fun w hw => by
    obtain ⟨m, hm⟩ := hμ w hw
    exact ⟨(2 ^ (a + 1) + 1) * m, by rw [pow_mul]; exact hm⟩
  have heq : ∀ α w, β (κ * α) (κ ^ (2 ^ (a + 1) + 1) * w) = κ ^ (2 ^ (a + 1) + 1) * β α w := by
    intro α w
    have hdt : d⁻¹ * τ α * d ∈ T₁ := hc.conj_mem _ (hτ α)
    have hdr : d⁻¹ * ρ w * d ∈ R₂ := hS.conj_d_mem (hρ w)
    have e : d⁻¹ * τ α * d * (d⁻¹ * ρ w * d) * (d⁻¹ * τ α * d)⁻¹ * (d⁻¹ * ρ w * d)⁻¹ =
        d⁻¹ * (τ α * ρ w * (τ α)⁻¹ * (ρ w)⁻¹) * d := by group
    rw [hβ, hβ, hS.commutator_eq_of_coord_eq hc ha hK hdt (hτ _) hdr (hρ _)
      (by rw [hc.conj_u _ (hτ α), hτu', hτu']) (by rw [hS.rho_conj hc ha hK (hρ w), hρw, hρw]),
      e, hc.v_conj_szA₁ ha hK (hcomm _ (hτR α) _ (hρR w))]
  obtain ⟨γ, hγ⟩ := SzCoords.bilinear_of_equivariant' ha hK β h1 h2' hκ heq
  exact ⟨γ, fun y hy r hr => by rw [hwd y hy r hr, hγ]⟩

omit [CharP K 2] hS hc in
theorem not_forall_pow_sigma_eq : ¬ ∀ w : K, w ^ 2 ^ a = w := by
  classical
  intro h
  have hall : ∀ w : K, w = 0 ∨ w = 1 := by
    intro w
    have h1 : w ^ 2 ^ (a + 1) = w ^ 2 := by rw [pow_succ, pow_mul, h]
    have h2 : w = w ^ 2 := by
      calc w = (w ^ 2 ^ (a + 1)) ^ 2 ^ a := (SzRadical.pow_theta_pow_sigma hK w).symm
        _ = (w ^ 2) ^ 2 ^ a := by rw [h1]
        _ = (w ^ 2 ^ a) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = w ^ 2 := by rw [h]
    have h3 : w * (w - 1) = 0 := by rw [mul_sub, mul_one, ← sq, ← h2, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact Or.inl h4
    · exact Or.inr (sub_eq_zero.mp h4)
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
    rcases hall w with hw | hw <;> simp [hw]
  have h4 := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, hK] at h4
  have h5 : 2 ^ 2 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact absurd (h5.trans h4) (by norm_num)

theorem t_not_mem_sup (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) :
    t ∉ T₁ ⊔ R₂ := by
  intro htH
  obtain ⟨γ, hγ⟩ := hS.exists_comm_const hc ha hK hμ
  have h1 : ((T₁ ⊔ R₂ : Subgroup G) : Set G) = (T₁ : Set G) * (R₂ : Set G) :=
    coe_mul_of_left_le_normalizer_right T₁ R₂ hS.le_normalizer_R₂
  rw [← SetLike.mem_coe, h1] at htH
  obtain ⟨y, hy, r, hr, hyr⟩ := htH
  have key : ∀ r' ∈ R₂, v (r' * t * r'⁻¹ * t⁻¹) =
      γ * (u y) ^ 2 ^ a * (v (r' * t * r'⁻¹ * t⁻¹)) ^ 2 ^ a := by
    intro r' hr'
    have hr'R := le_szR_mid T₁ R₂ t hr'
    have hyR := le_szR_left T₁ R₂ t hy
    have hrR := le_szR_mid T₁ R₂ t hr
    have e1 : r' * t * r'⁻¹ * t⁻¹ = (r' * y * r'⁻¹ * y⁻¹) * (r' * r * r'⁻¹ * r⁻¹) := by
      rw [← hS.commutator_mul_right hc ha hK hr'R hyR hrR]
      simp only [hyr]
    have e2 : r' * r * r'⁻¹ * r⁻¹ = 1 := by rw [hS.R₂_comm r' hr' r hr]; group
    have e3 : r' * y * r'⁻¹ * y⁻¹ = (y * r' * y⁻¹ * r'⁻¹)⁻¹ := by group
    have hL : v (r' * t * r'⁻¹ * t⁻¹) = v (y * r' * y⁻¹ * r'⁻¹) := by
      rw [e1, e2, mul_one, e3, hc.v_inv_szA₁ ha hK (hS.comm_mem y hy r' hr')]
    conv_lhs => rw [hL, hγ y hy r' hr', mul_pow]
    ring
  apply not_forall_pow_sigma_eq ha hK (a := a)
  have hall : ∀ w : K, w = γ * (u y) ^ 2 ^ a * w ^ 2 ^ a := by
    intro w
    obtain ⟨r', hr', hw⟩ := hS.exists_rho_eq hc ha hK w
    rw [← hw]
    exact key r' hr'
  have hC : γ * (u y) ^ 2 ^ a = 1 := by
    have := hall 1
    rw [one_pow, mul_one] at this
    exact this.symm
  intro w
  have := hall w
  rw [hC, one_mul] at this
  exact this.symm

omit [Fintype K] [CharP K 2] hc ha hK in
theorem eq_one_or_eq_t {s : G} (hs : s ∈ zpowers t) : s = 1 ∨ s = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hS.t_sq]
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    rw [zpow_mul, ht2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

omit [Fintype K] [CharP K 2] hc ha hK in
theorem exists_decomp' {x : G} (hx : x ∈ szR T₁ R₂ t) :
    ∃ y ∈ T₁, ∃ r ∈ R₂, ∃ s ∈ zpowers t, y * r * s = x := by
  obtain ⟨y, hy, r, hr, h | h⟩ := hS.exists_decomp hx
  · exact ⟨y, hy, r, hr, 1, one_mem _, by rw [mul_one, h]⟩
  · exact ⟨y, hy, r, hr, t, mem_zpowers t, h.symm⟩

theorem decomp_unique (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    {y r s y' r' s' : G} (hy : y ∈ T₁) (hr : r ∈ R₂) (hs : s ∈ zpowers t) (hy' : y' ∈ T₁)
    (hr' : r' ∈ R₂) (hs' : s' ∈ zpowers t) (h : y * r * s = y' * r' * s') :
    s = s' ∧ y⁻¹ * y' ∈ szA₁ T₁ := by
  have htH := hS.t_not_mem_sup hc ha hK hμ
  have hmem : ∀ {z w : G}, z ∈ T₁ → w ∈ R₂ → z * w ∈ T₁ ⊔ R₂ := fun hz hw =>
    mul_mem (mem_sup_left hz) (mem_sup_right hw)
  have hss : s = s' := by
    have e : s * s'⁻¹ = (y * r)⁻¹ * (y' * r') := by
      have e' : s = (y * r)⁻¹ * (y' * r' * s') := by rw [← h]; group
      rw [e']
      group
    rcases hS.eq_one_or_eq_t hs with h1 | h1 <;> rcases hS.eq_one_or_eq_t hs' with h1' | h1'
    · rw [h1, h1']
    · exfalso
      apply htH
      rw [h1, h1', one_mul, hS.t_inv] at e
      rw [e]
      exact mul_mem (inv_mem (hmem hy hr)) (hmem hy' hr')
    · exfalso
      apply htH
      rw [h1, h1', inv_one, mul_one] at e
      rw [e]
      exact mul_mem (inv_mem (hmem hy hr)) (hmem hy' hr')
    · rw [h1, h1']
  subst hss
  have h2 : y * r = y' * r' := mul_right_cancel h
  have h3 : y⁻¹ * y' = r * r'⁻¹ := by
    calc y⁻¹ * y' = y⁻¹ * (y' * r') * r'⁻¹ := by group
      _ = y⁻¹ * (y * r) * r'⁻¹ := by rw [h2]
      _ = r * r'⁻¹ := by group
  refine ⟨rfl, hS.inf_le (mem_inf.mpr ⟨mul_mem (inv_mem hy) hy', ?_⟩)⟩
  rw [h3]
  exact mul_mem hr (inv_mem hr')

theorem exists_coords (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) :
    ∃ (φ : G → K × K × K) (γ c : K), SzRCoords2 T₁ R₂ t a u v φ γ c := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨γ, hγ⟩ := hS.exists_comm_const hc ha hK hμ
  obtain ⟨c, hcc⟩ := hS.exists_sq_const hc ha hK hμ
  have htH := hS.t_not_mem_sup hc ha hK hμ
  have ht1 : t ≠ 1 := fun h => htH (h ▸ one_mem _)
  have hcomm := hS.comm_mem_szA₁ hc ha hK
  have htR := mem_szR_right T₁ R₂ t
  have hsR : ∀ s ∈ zpowers t, s ∈ szR T₁ R₂ t := fun s hs => mem_sup_right hs
  have hsN : ∀ s ∈ zpowers t, s ∈ normalizer (R₂ : Set G) := fun s hs =>
    zpowers_le.mpr hS.t_mem_normalizer_R₂ hs
  have hys : ∀ s ∈ zpowers t, ∀ y ∈ T₁, y * s = s * y := by
    intro s hs y hy
    rcases hS.eq_one_or_eq_t hs with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]; exact hS.t_comm y hy
  obtain ⟨ρ, hρ⟩ : ∃ ρ : G → K, ∀ x, ρ x = v (x * t * x⁻¹ * t⁻¹) := ⟨_, fun _ => rfl⟩
  simp only [← hρ] at hγ hcc
  have hρmul : ∀ x ∈ szR T₁ R₂ t, ∀ x' ∈ szR T₁ R₂ t, ρ (x * x') = ρ x + ρ x' :=
    fun x hx x' hx' => by simp only [hρ]; exact hS.rho_mul hc ha hK hx hx'
  have hρT : ∀ y ∈ T₁, ρ y = 0 := fun y hy => by rw [hρ]; exact hS.rho_eq_zero_of_mem_T₁ hc hy
  have hρs : ∀ s ∈ zpowers t, ρ s = 0 := by
    intro s hs
    rcases hS.eq_one_or_eq_t hs with h | h
    · rw [h, hρ, show (1 : G) * t * 1⁻¹ * t⁻¹ = 1 by group, hc.v_one]
    · rw [h, hρ, show t * t * t⁻¹ * t⁻¹ = 1 by group, hc.v_one]
  have hρzero : ∀ r ∈ R₂, ρ r = 0 ↔ r ∈ szA₁ T₁ := fun r hr => by
    rw [hρ]; exact hS.rho_eq_zero_iff hc ha hK hr
  have hρsurj : ∀ w, ∃ r ∈ R₂, ρ r = w := fun w => by
    simp only [hρ]; exact hS.exists_rho_eq hc ha hK w
  let lam : G → K := fun s => if s = 1 then 0 else 1
  have hlam1 : lam 1 = 0 := by simp [lam]
  have hlamt : lam t = 1 := by simp [lam, ht1]
  have hlam : ∀ s ∈ zpowers t, ∀ r ∈ R₂, v (r * s * r⁻¹ * s⁻¹) = lam s * ρ r := by
    intro s hs r hr
    rcases hS.eq_one_or_eq_t hs with h | h
    · rw [h, hlam1, zero_mul, show r * 1 * r⁻¹ * 1⁻¹ = 1 by group, hc.v_one]
    · rw [h, hlamt, one_mul, hρ]
  have htt : t * t = 1 := by rw [← sq, hS.t_sq]
  have hlam_mul : ∀ s ∈ zpowers t, ∀ s' ∈ zpowers t, lam (s * s') = lam s + lam s' := by
    intro s hs s' hs'
    rcases hS.eq_one_or_eq_t hs with h | h <;> rcases hS.eq_one_or_eq_t hs' with h' | h' <;>
      rw [h, h']
    · rw [mul_one, hlam1, add_zero]
    · rw [one_mul, hlam1, zero_add]
    · rw [mul_one, hlam1, add_zero]
    · rw [htt, hlam1, hlamt, CharTwo.add_self_eq_zero]
  have hlam_mem : ∀ s ∈ zpowers t, lam s = 0 ∨ lam s = 1 := by
    intro s hs
    rcases hS.eq_one_or_eq_t hs with h | h
    · rw [h]; exact Or.inl hlam1
    · rw [h]; exact Or.inr hlamt
  have hlam_zero : ∀ s ∈ zpowers t, lam s = 0 → s = 1 := by
    intro s hs h0
    rcases hS.eq_one_or_eq_t hs with h | h
    · exact h
    · rw [h, hlamt] at h0; exact absurd h0 one_ne_zero
  choose! tc htc rc hrc sc hsc htrs using fun x (hx : x ∈ szR T₁ R₂ t) => hS.exists_decomp' hx
  have hφu : ∀ x ∈ szR T₁ R₂ t, ∀ y ∈ T₁, ∀ r ∈ R₂, ∀ s ∈ zpowers t,
      y * r * s = x → u (tc x) = u y ∧ sc x = s := by
    intro x hx y hy r hr s hs hx'
    obtain ⟨hs', hb⟩ := hS.decomp_unique hc ha hK hμ (htc x hx) (hrc x hx) (hsc x hx) hy hr hs
      ((htrs x hx).trans hx'.symm)
    refine ⟨?_, hs'⟩
    have hu := hc.u_eq_zero_of_mem_szA₁ ha hK hb
    rw [(hc.mul _ (inv_mem (htc x hx)) _ hy).1, (hc.inv (htc x hx)).1] at hu
    linear_combination hu - u y * h2
  have hρx : ∀ x ∈ szR T₁ R₂ t, ρ (rc x) = ρ x := by
    intro x hx
    have hyR := le_szR_left T₁ R₂ t (htc x hx)
    have hrR := le_szR_mid T₁ R₂ t (hrc x hx)
    conv_rhs => rw [← htrs x hx]
    rw [hρmul _ (mul_mem hyR hrR) _ (hsR _ (hsc x hx)), hρmul _ hyR _ hrR,
      hρT _ (htc x hx), hρs _ (hsc x hx)]
    ring
  have hv0 : ∀ x z, x * z = z * x → v (x * z * x⁻¹ * z⁻¹) = 0 := fun x z h => by
    have e : x * z * x⁻¹ * z⁻¹ = 1 := by rw [h]; group
    rw [e, hc.v_one]
  have hvs : ∀ x ∈ szR T₁ R₂ t, ∀ z ∈ szR T₁ R₂ t,
      v (z * x * z⁻¹ * x⁻¹) = v (x * z * x⁻¹ * z⁻¹) := by
    intro x hx z hz
    have e : z * x * z⁻¹ * x⁻¹ = (x * z * x⁻¹ * z⁻¹)⁻¹ := by group
    rw [e, hc.v_inv_szA₁ ha hK (hcomm _ hx _ hz)]
  have hsq : ∀ y ∈ T₁, ∀ r ∈ R₂, ∀ s ∈ zpowers t,
      v ((y * r * s) ^ 2) = szSqMap a γ c (u y, ρ r, lam s) := by
    intro y hy r hr s hs
    have hyR := le_szR_left T₁ R₂ t hy
    have hrR := le_szR_mid T₁ R₂ t hr
    have hsR' := hsR s hs
    have hs2 : s ^ 2 = 1 := by
      rcases hS.eq_one_or_eq_t hs with h | h
      · rw [h, one_pow]
      · rw [h, hS.t_sq]
    rw [hS.sq_mul hc ha hK (mul_mem hyR hrR) hsR', hS.sq_mul hc ha hK hyR hrR, hs2, mul_one,
      hS.commutator_mul_left hc ha hK hyR hrR hsR']
    have e1 : y * s * y⁻¹ * s⁻¹ = 1 := by rw [hys s hs y hy]; group
    have hy2 := hc.sq_mem_szA₁ ha hK hy
    have hr2 := hS.sq_mem_szA₁_of_mem_R₂ hc ha hK hr
    rw [e1, one_mul, hc.v_mul_szA₁ ha hK (hcomm _ hrR _ hsR')
      (mul_mem (mul_mem (hcomm _ hyR _ hrR) hy2) hr2),
      hc.v_mul_szA₁ ha hK (mul_mem (hcomm _ hyR _ hrR) hy2) hr2,
      hc.v_mul_szA₁ ha hK (hcomm _ hyR _ hrR) hy2, hlam s hs r hr, hγ y hy r hr, (hc.sq hy).2,
      hcc r hr]
    simp only [szSqMap]
    ring
  have hcm : ∀ y ∈ T₁, ∀ r ∈ R₂, ∀ s ∈ zpowers t, ∀ y' ∈ T₁, ∀ r' ∈ R₂, ∀ s' ∈ zpowers t,
      v (y * r * s * (y' * r' * s') * (y * r * s)⁻¹ * (y' * r' * s')⁻¹) =
        szCommMap a γ (u y, ρ r, lam s) (u y', ρ r', lam s') := by
    intro y hy r hr s hs y' hy' r' hr' s' hs'
    have hyR := le_szR_left T₁ R₂ t hy
    have hrR := le_szR_mid T₁ R₂ t hr
    have hsR' := hsR s hs
    have hy'R := le_szR_left T₁ R₂ t hy'
    have hr'R := le_szR_mid T₁ R₂ t hr'
    have hs'R := hsR s' hs'
    have hz : y' * r' * s' ∈ szR T₁ R₂ t := mul_mem (mul_mem hy'R hr'R) hs'R
    have hL : v (y * r * s * (y' * r' * s') * (y * r * s)⁻¹ * (y' * r' * s')⁻¹) =
        v (y * (y' * r' * s') * y⁻¹ * (y' * r' * s')⁻¹) +
          v (r * (y' * r' * s') * r⁻¹ * (y' * r' * s')⁻¹) +
            v (s * (y' * r' * s') * s⁻¹ * (y' * r' * s')⁻¹) := by
      rw [hS.commutator_mul_left hc ha hK (mul_mem hyR hrR) hsR' hz,
        hS.commutator_mul_left hc ha hK hyR hrR hz,
        hc.v_mul_szA₁ ha hK (mul_mem (hcomm _ hyR _ hz) (hcomm _ hrR _ hz)) (hcomm _ hsR' _ hz),
        hc.v_mul_szA₁ ha hK (hcomm _ hyR _ hz) (hcomm _ hrR _ hz)]
    have hR' : ∀ α ∈ szR T₁ R₂ t, v (α * (y' * r' * s') * α⁻¹ * (y' * r' * s')⁻¹) =
        v (α * y' * α⁻¹ * y'⁻¹) + v (α * r' * α⁻¹ * r'⁻¹) + v (α * s' * α⁻¹ * s'⁻¹) := by
      intro α hα
      rw [hS.commutator_mul_right hc ha hK hα (mul_mem hy'R hr'R) hs'R,
        hS.commutator_mul_right hc ha hK hα hy'R hr'R,
        hc.v_mul_szA₁ ha hK (mul_mem (hcomm _ hα _ hy'R) (hcomm _ hα _ hr'R)) (hcomm _ hα _ hs'R),
        hc.v_mul_szA₁ ha hK (hcomm _ hα _ hy'R) (hcomm _ hα _ hr'R)]
    have hys' : y * s' = s' * y := hys s' hs' y hy
    have hsy' : s * y' = y' * s := (hys s hs y' hy').symm
    have hss' : s * s' = s' * s := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
      obtain ⟨k', rfl⟩ := mem_zpowers_iff.mp hs'
      rw [← zpow_add, ← zpow_add, add_comm]
    rw [hL, hR' y hyR, hR' r hrR, hR' s hsR', (hc.comm hy hy').2, hγ y hy r' hr', hv0 _ _ hys',
      hvs y' hy'R r hrR, hγ y' hy' r hr, hv0 _ _ (hS.R₂_comm r hr r' hr'), hlam s' hs' r hr,
      hv0 _ _ hsy', hvs r' hr'R s hsR', hlam s hs r' hr', hv0 _ _ hss']
    simp only [szCommMap]
    ring
  refine ⟨fun x => (u (tc x), ρ x, lam (sc x)), γ, c,
    ⟨fun b hb b' hb' => hc.v_mul_szA₁ ha hK hb hb',
      fun b hb h => hc.eq_one_of_v_eq_zero ha hK hb h, hc.exists_v_eq ha hK, hS.commute_szA₁,
      hcomm, fun x hx => hS.sq_mem_szA₁ hc ha hK hx, ?_, ?_, fun x hx => hlam_mem _ (hsc x hx),
      ?_, ?_, fun x _ => hρ x, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro x hx x' hx'
    have hy := htc x hx
    have hs := hsc x hx
    have hy' := htc x' hx'
    have hs' := hsc x' hx'
    have hρ₀ : (tc x')⁻¹ * rc x * tc x' * (sc x * rc x' * (sc x)⁻¹) ∈ R₂ := by
      refine mul_mem ?_ ((mem_normalizer_iff.mp (hsN _ hs) _).mp (hrc x' hx'))
      simpa using (mem_normalizer_iff.mp (hS.le_normalizer_R₂ (inv_mem hy')) _).mp (hrc x hx)
    have hts : tc x' * sc x = sc x * tc x' := hys _ hs _ hy'
    have e : x * x' = tc x * tc x' * ((tc x')⁻¹ * rc x * tc x' * (sc x * rc x' * (sc x)⁻¹)) *
        (sc x * sc x') := by
      calc x * x' = tc x * rc x * sc x * (tc x' * rc x' * sc x') := by
            rw [htrs x hx, htrs x' hx']
        _ = tc x * rc x * (sc x * tc x') * rc x' * sc x' := by group
        _ = tc x * rc x * (tc x' * sc x) * rc x' * sc x' := by rw [hts]
        _ = _ := by group
    obtain ⟨hu, hsc'⟩ := hφu (x * x') (mul_mem hx hx') _ (mul_mem hy hy') _ hρ₀ _
      (mul_mem hs hs') e.symm
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show u (tc (x * x')) = u (tc x) + u (tc x')
      rw [hu, (hc.mul _ hy _ hy').1]
    · exact hρmul x hx x' hx'
    · show lam (sc (x * x')) = lam (sc x) + lam (sc x')
      rw [hsc', hlam_mul _ hs _ hs']
  ·
    intro x hx
    constructor
    · intro h
      have h1 : u (tc x) = 0 := congrArg Prod.fst h
      have h3 : ρ x = 0 := congrArg (fun p => p.2.1) h
      have h4 : lam (sc x) = 0 := congrArg (fun p => p.2.2) h
      have hyA : tc x ∈ szA₁ T₁ := (hc.mem_szA₁_iff ha hK (htc x hx)).mpr h1
      have hrA : rc x ∈ szA₁ T₁ := (hρzero _ (hrc x hx)).mp (by rw [hρx x hx]; exact h3)
      rw [← htrs x hx, hlam_zero _ (hsc x hx) h4, mul_one]
      exact mul_mem hyA hrA
    · intro h
      obtain ⟨hu, hs1⟩ := hφu x hx x (szA₁_le T₁ h) 1 (one_mem _) 1 (one_mem _) (by group)
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show u (tc x) = 0
        rw [hu]
        exact hc.u_eq_zero_of_mem_szA₁ ha hK h
      · exact hρT x (szA₁_le T₁ h)
      · show lam (sc x) = 0
        rw [hs1, hlam1]
  ·
    intro z hz
    obtain ⟨s, hs, hsz⟩ : ∃ s ∈ zpowers t, lam s = z.2.2 := by
      rcases hz with h0 | h1
      · exact ⟨1, one_mem _, by rw [hlam1, h0]⟩
      · exact ⟨t, mem_zpowers t, by rw [hlamt, h1]⟩
    obtain ⟨y, hy, hyu, -⟩ := hc.surj z.1 0
    obtain ⟨r, hr, hrz⟩ := hρsurj z.2.1
    have hyR := le_szR_left T₁ R₂ t hy
    have hrR := le_szR_mid T₁ R₂ t hr
    have hx : y * r * s ∈ szR T₁ R₂ t := mul_mem (mul_mem hyR hrR) (hsR s hs)
    obtain ⟨hu, hs'⟩ := hφu _ hx y hy r hr s hs rfl
    refine ⟨y * r * s, hx, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
    · show u (tc (y * r * s)) = z.1
      rw [hu, hyu]
    · show ρ (y * r * s) = z.2.1
      rw [hρmul _ (mul_mem hyR hrR) _ (hsR s hs), hρmul _ hyR _ hrR, hρT _ hy, hρs _ hs, hrz]
      ring
    · show lam (sc (y * r * s)) = z.2.2
      rw [hs', hsz]
  ·
    intro x hx
    constructor
    · intro h0
      have h1 : sc x = 1 := hlam_zero _ (hsc x hx) h0
      rw [← htrs x hx, h1, mul_one]
      exact mul_mem (mem_sup_left (htc x hx)) (mem_sup_right (hrc x hx))
    · intro hxH
      have h1 : ((T₁ ⊔ R₂ : Subgroup G) : Set G) = (T₁ : Set G) * (R₂ : Set G) :=
        coe_mul_of_left_le_normalizer_right T₁ R₂ hS.le_normalizer_R₂
      rw [← SetLike.mem_coe, h1] at hxH
      obtain ⟨y, hy, r, hr, hyr⟩ := hxH
      obtain ⟨-, hs1⟩ := hφu x hx y hy r hr 1 (one_mem _) (by rw [mul_one]; exact hyr)
      show lam (sc x) = 0
      rw [hs1, hlam1]
  ·
    intro y hy
    obtain ⟨hu, hs1⟩ := hφu y (le_szR_left T₁ R₂ t hy) y hy 1 (one_mem _) 1 (one_mem _)
      (by group)
    refine Prod.ext hu (Prod.ext (hρT y hy) ?_)
    show lam (sc y) = 0
    rw [hs1, hlam1]
  ·
    intro r hr
    obtain ⟨hu, hs1⟩ := hφu r (le_szR_mid T₁ R₂ t hr) 1 (one_mem _) r hr 1 (one_mem _)
      (by group)
    refine Prod.ext ?_ (Prod.ext (hρ r) ?_)
    · show u (tc r) = 0
      rw [hu]; exact hc.u_one
    · show lam (sc r) = 0
      rw [hs1, hlam1]
  ·
    obtain ⟨hu, hs1⟩ := hφu t htR 1 (one_mem _) 1 (one_mem _) t (mem_zpowers t) (by group)
    refine Prod.ext ?_ (Prod.ext (hρs t (mem_zpowers t)) ?_)
    · show u (tc t) = 0
      rw [hu]; exact hc.u_one
    · show lam (sc t) = 1
      rw [hs1, hlamt]
  ·
    intro x hx
    have h := hsq _ (htc x hx) _ (hrc x hx) _ (hsc x hx)
    rw [htrs x hx, hρx x hx] at h
    exact h
  ·
    intro x hx x' hx'
    have h := hcm _ (htc x hx) _ (hrc x hx) _ (hsc x hx) _ (htc x' hx') _ (hrc x' hx') _
      (hsc x' hx')
    rw [htrs x hx, htrs x' hx', hρx x hx, hρx x' hx'] at h
    exact h

end Constants

end SzR2

end CFSG.SeitzReduction.RankOne
