module

public import CFSG.GH74.GLS.SP.Local.SPLM1b

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section J1

variable [Finite G] (D : SPLNot4 G)

theorem J₁_eq (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) : D.J₁ = D.X₄ ⊔ conjBy D.t D.X₄ := by
  obtain ⟨u, hu0, hu2, hasq, hauw⟩ := h3.a_facts.a_u
  obtain ⟨δ, hδ, hn⟩ := n_mem_tH D.toSPLNot3 hs h1 h3.a_facts.a_z
    ⟨u, SPLNot1.H₀_le_H D.toSPLNot1 hu0, hauw⟩
  have hX₄ : D.X₄ = conjBy (D.a * D.w₁) D.Y₁ := X₄_eq_conjBy D
  have hzw : (D.z * D.w) * (D.a * D.w₁) = (D.a * D.w₁) * (D.t * δ) := by
    rw [← hn]; group
  show conjBy (D.a * D.w₁) D.J = _
  rw [hJ]
  unfold CFSG.GH74.BNPair.conjBy
  rw [Subgroup.map_sup]
  congr 1
  · rw [hX₄]; rfl
  · show conjBy (D.a * D.w₁) (conjBy (D.z * D.w) D.Y₁) = conjBy D.t D.X₄
    rw [conjBy_conjBy, hzw, hX₄, conjBy_conjBy]
    have hHt : Normalizes D.H (conjBy D.t D.X₄) :=
      (H_X₄ D.toSPLNot3 hs h1 h3).map_conjBy (t_mem_normalizer D.toSPLNot3 hs h1)
    have hY : conjBy (D.a * D.w₁ * D.t) D.Y₁ = conjBy D.t D.X₄ := by
      rw [hX₄]; exact (conjBy_conjBy _ _ _).symm
    rw [← mul_assoc, BNPair.conjBy_mul, hY, conjBy_eq_of_mem hHt hδ]

omit [Finite G] in
theorem conjBy_t_t_eq (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (A : Subgroup G) :
    conjBy D.t (conjBy D.t A) = A := by
  rw [conjBy_conjBy, t_mul_t D hs, conjBy_one']

theorem t_conj_H₀ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H₀, D.t * h * D.t⁻¹ ∈ D.H₀ := by
  intro h hh
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
  have hcomm : Commute D.h₁ D.h₂ := H₁_H₂_comm D.toSPLNot3 hs h1 _ (mem_zpowers _) _ (mem_zpowers _)
  have e : D.t * (D.h₁ * D.h₂) * D.t⁻¹ = D.h₂ * D.h₁ := by
    have htt := t_mul_t D.toSPLNot3 hs
    have h2 : D.t * D.h₂ * D.t⁻¹ = D.h₁ := by
      show D.t * (D.t * D.h₁ * D.t⁻¹) * D.t⁻¹ = D.h₁
      calc D.t * (D.t * D.h₁ * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * D.h₁ * (D.t * D.t)⁻¹ := by group
        _ = D.h₁ := by rw [htt]; group
    calc D.t * (D.h₁ * D.h₂) * D.t⁻¹ = (D.t * D.h₁ * D.t⁻¹) * (D.t * D.h₂ * D.t⁻¹) := by group
      _ = D.h₂ * D.h₁ := by rw [h2]; rfl
  have : D.t * (D.h₁ * D.h₂) ^ j * D.t⁻¹ = (D.t * (D.h₁ * D.h₂) * D.t⁻¹) ^ j := by
    rw [conj_zpow]
  rw [this, e, ← hcomm.eq]
  exact zpow_mem (mem_zpowers _) j

theorem J₁_le_M₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) : D.J₁ ≤ D.M₁ := by
  rw [J₁_eq D hs h1 h3 hJ]
  refine sup_le ?_ ?_
  · exact (D.toSPLNot3.X₄_le_P).trans ((P_le_B D.toSPLNot3).trans le_sup_left)
  · intro x hx
    rw [mem_conjBy_iff] at hx
    have hM : D.t ∈ D.M₁ := (le_sup_right : zpowers D.t ≤ D.M₁) (mem_zpowers _)
    have hx4 : D.t * x * D.t⁻¹ ∈ D.M₁ :=
      (D.toSPLNot3.X₄_le_P.trans ((P_le_B D.toSPLNot3).trans le_sup_left)) hx
    have : x = D.t⁻¹ * (D.t * x * D.t⁻¹) * D.t := by group
    rw [this]
    exact D.M₁.mul_mem (D.M₁.mul_mem (D.M₁.inv_mem hM) hx4) hM

theorem P_le_R₁J₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) : D.P ≤ D.R₁ ⊔ D.J₁ := by
  have hJ₁ := J₁_eq D hs h1 h3 hJ
  have hX₄ : D.X₄ ≤ D.J₁ := by rw [hJ₁]; exact le_sup_left
  calc D.P = D.R₁ ⊔ D.X₄ := D.toSPLNot3.P_eq_R₁_sup_X₄
    _ ≤ D.R₁ ⊔ D.J₁ := sup_le_sup le_rfl hX₄

theorem H_J₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) : Normalizes D.H D.J₁ := by
  rw [J₁_eq D hs h1 h3 hJ]
  exact normalizes_sup (H_X₄ D.toSPLNot3 hs h1 h3)
    ((H_X₄ D.toSPLNot3 hs h1 h3).map_conjBy (t_mem_normalizer D.toSPLNot3 hs h1))

theorem R₁J₁_normal' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) :
    D.M₁ ≤ normalizer ((D.R₁ ⊔ D.J₁ : Subgroup G) : Set G) := by
  have hJ₁ := J₁_eq D hs h1 h3 hJ
  have hHN : D.H ≤ normalizer ((D.R₁ ⊔ D.J₁ : Subgroup G) : Set G) :=
    le_normalizer_of_normalizes (normalizes_sup (H_R₁ D.toSPLNot3 hs h1 h3)
      (H_J₁ D hs h1 h3 hJ))
  have hPQ : D.P ≤ D.R₁ ⊔ D.J₁ := P_le_R₁J₁ D hs h1 h3 hJ
  have hPN : D.P ≤ normalizer ((D.R₁ ⊔ D.J₁ : Subgroup G) : Set G) :=
    hPQ.trans Subgroup.le_normalizer
  have htN : D.t ∈ normalizer ((D.R₁ ⊔ D.J₁ : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conjBy_eq
    have hJt : conjBy D.t D.J₁ = D.J₁ := by
      rw [hJ₁]
      unfold CFSG.GH74.BNPair.conjBy
      rw [Subgroup.map_sup]
      have e : D.X₄.map (MulAut.conj D.t⁻¹).toMonoidHom = conjBy D.t D.X₄ := rfl
      have e2 : (conjBy D.t D.X₄).map (MulAut.conj D.t⁻¹).toMonoidHom = D.X₄ :=
        conjBy_t_t_eq D.toSPLNot3 hs D.X₄
      rw [e, e2, sup_comm]
    have hRt := conjBy_t_R₁ D.toSPLNot3 hs h3
    unfold CFSG.GH74.BNPair.conjBy at hJt hRt ⊢
    rw [Subgroup.map_sup, hJt, hRt]
  exact sup_le (sup_le hHN hPN) (by rw [zpowers_le]; exact htN)

theorem t_mem_J₁_H (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hzJ : D.z * D.w ∈ D.J) : ∃ n ∈ D.J₁, ∃ δ ∈ D.H, D.t = n * δ⁻¹ := by
  obtain ⟨u, hu0, hu2, hasq, hauw⟩ := h3.a_facts.a_u
  obtain ⟨δ, hδ, hn⟩ := n_mem_tH D.toSPLNot3 hs h1 h3.a_facts.a_z
    ⟨u, SPLNot1.H₀_le_H D.toSPLNot1 hu0, hauw⟩
  refine ⟨(D.a * D.w₁)⁻¹ * (D.z * D.w) * (D.a * D.w₁), ?_, δ, hδ, ?_⟩
  · show (D.a * D.w₁)⁻¹ * (D.z * D.w) * (D.a * D.w₁) ∈ conjBy (D.a * D.w₁) D.J
    rw [mem_conjBy_iff]
    have : (D.a * D.w₁) * ((D.a * D.w₁)⁻¹ * (D.z * D.w) * (D.a * D.w₁)) * (D.a * D.w₁)⁻¹ =
        D.z * D.w := by group
    rw [this]; exact hzJ
  · rw [hn]; group

theorem M₁_eq_RJH' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) (hzJ : D.z * D.w ∈ D.J) :
    D.M₁ = D.R₁ ⊔ D.J₁ ⊔ D.H := by
  obtain ⟨n, hn, δ, hδ, htn⟩ := t_mem_J₁_H D hs h1 h3 hzJ
  have hPQ := P_le_R₁J₁ D hs h1 h3 hJ
  have hRM : D.R₁ ≤ D.M₁ := (D.toSPLNot3.R₁_le_P).trans ((P_le_B D.toSPLNot3).trans le_sup_left)
  have hHM : D.H ≤ D.M₁ := (H_le_B D.toSPLNot3).trans le_sup_left
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_right
    · exact hPQ.trans le_sup_left
    · rw [zpowers_le, htn]
      exact (D.R₁ ⊔ D.J₁ ⊔ D.H).mul_mem
        ((le_sup_left : D.R₁ ⊔ D.J₁ ≤ D.R₁ ⊔ D.J₁ ⊔ D.H) ((le_sup_right : D.J₁ ≤ D.R₁ ⊔ D.J₁) hn))
        ((le_sup_right : D.H ≤ D.R₁ ⊔ D.J₁ ⊔ D.H) (D.H.inv_mem hδ))
  · exact sup_le (sup_le hRM (J₁_le_M₁ D hs h1 h3 hJ)) hHM

theorem M₁_eq_BJ' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) (hzJ : D.z * D.w ∈ D.J) :
    D.M₁ = D.B ⊔ D.J₁ := by
  obtain ⟨n, hn, δ, hδ, htn⟩ := t_mem_J₁_H D hs h1 h3 hzJ
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [zpowers_le, htn]
    exact (D.B ⊔ D.J₁).mul_mem ((le_sup_right : D.J₁ ≤ D.B ⊔ D.J₁) hn)
      ((le_sup_left : D.B ≤ D.B ⊔ D.J₁) ((H_le_B D.toSPLNot3) (D.H.inv_mem hδ)))
  · exact sup_le le_sup_left (J₁_le_M₁ D hs h1 h3 hJ)

theorem H₀_cen_J₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D.toSPLNot3)
    (hJ : D.J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁) :
    ∀ i ∈ D.H₀, ∀ j ∈ D.J₁, i * j = j * i := by
  intro i hi j hj
  have hJ₁ := J₁_eq D hs h1 h3 hJ
  have hker : ∀ g ∈ D.H₀, ∀ x ∈ D.X₄, g * x = x * g := fun g hg x hx =>
    (mem_kernelOf_iff.mp (H₀_le_ker₄ D.toSPLNot3 hs h1 h3 hg)).2 x hx
  have hle : D.J₁ ≤ centralizer ({i} : Set G) := by
    rw [hJ₁]
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact (hker i hi x hx).symm
    · rw [mem_centralizer_singleton_iff]
      have h2 : ∀ a ∈ D.X₄, (D.t * i * D.t⁻¹) * a = a * (D.t * i * D.t⁻¹) := fun a ha =>
        hker _ (t_conj_H₀ D hs h1 i hi) a ha
      have := (centralizes_conjBy_iff (g := D.t) (c := i) (A := D.X₄)).mpr h2 y hy
      exact this.symm
  exact (mem_centralizer_singleton_iff.mp (hle hj)).symm

end J1

section H0Order

variable [Finite G] (D : SPLNot3 G)

theorem h₂_pow_half (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.h₂ ^ ((D.q - 1) / 2) = D.z := by
  have h := pow_half_eq_z D.toSPLNot1 hs h1.h₁_mem h1.h₁_ord
  have e : D.h₂ ^ ((D.q - 1) / 2) = D.t * D.h₁ ^ ((D.q - 1) / 2) * D.t⁻¹ := by
    unfold SPLNot1.h₂
    rw [conj_pow]
  rw [e, h]
  have hc := hs.syl.comm_z hs.syl.t_mem
  calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [hc]
    _ = D.z := by group

theorem orderOf_h₁h₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    orderOf (D.h₁ * D.h₂) = (D.q - 1) / 2 := by
  have hq2 : D.q - 1 = 2 * ((D.q - 1) / 2) := by obtain ⟨m, hm⟩ := hs.odd_q; omega
  have hcomm : Commute D.h₁ D.h₂ := H₁_H₂_comm D hs h1 _ (mem_zpowers _) _ (mem_zpowers _)
  have hh1 : D.h₁ ^ ((D.q - 1) / 2) = D.z := pow_half_eq_z D.toSPLNot1 hs h1.h₁_mem h1.h₁_ord
  have hh2 := h₂_pow_half D hs h1
  have hz2 := z_mul_z D hs
  have hg : (D.h₁ * D.h₂) ^ ((D.q - 1) / 2) = 1 := by rw [hcomm.mul_pow, hh1, hh2, hz2]
  have key : ∀ j : ℕ, (D.h₁ * D.h₂) ^ j = 1 → (D.q - 1) / 2 ∣ j := by
    intro j hj
    rw [hcomm.mul_pow] at hj
    have h12 : D.h₁ ^ j = (D.h₂ ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hj
    have hmem : D.h₁ ^ j ∈ D.H₁ ⊓ D.H₂ :=
      ⟨pow_mem (mem_zpowers _) j, by rw [h12]; exact D.H₂.inv_mem (pow_mem (mem_zpowers _) j)⟩
    rw [h1.H_inter] at hmem
    have hsq : D.h₁ ^ j * D.h₁ ^ j = 1 := by
      rcases eq_one_or_z hs hmem with h | h
      · rw [h, mul_one]
      · rw [h]; exact hz2
    have : D.h₁ ^ (2 * j) = 1 := by rw [two_mul, pow_add]; exact hsq
    have hd : orderOf D.h₁ ∣ 2 * j := orderOf_dvd_of_pow_eq_one this
    rw [h1.h₁_ord, hq2] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hg) (key _ (pow_orderOf_eq_one _))

theorem H₀_card' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    Nat.card ↥D.H₀ = (D.q - 1) / 2 := by
  show Nat.card ↥(zpowers (D.h₁ * D.h₂)) = _
  rw [Nat.card_zpowers, orderOf_h₁h₂ D hs h1]

theorem H_split' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.H₁ ⊓ D.H₀ = ⊥ ∧ D.H₁ ⊔ D.H₀ = D.H := by
  have hq2 : D.q - 1 = 2 * ((D.q - 1) / 2) := by obtain ⟨m, hm⟩ := hs.odd_q; omega
  have hcomm : Commute D.h₁ D.h₂ := H₁_H₂_comm D hs h1 _ (mem_zpowers _) _ (mem_zpowers _)
  have hz2 := z_mul_z D hs
  constructor
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx0⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx1
    obtain ⟨m, hm0⟩ := mem_zpowers_iff.mp hx0
    have hm : D.h₁ ^ m * D.h₂ ^ m = D.h₁ ^ n := by rw [← hcomm.mul_zpow]; exact hm0
    have h2m : D.h₂ ^ m = D.h₁ ^ (n - m) := by
      calc D.h₂ ^ m = (D.h₁ ^ m)⁻¹ * (D.h₁ ^ m * D.h₂ ^ m) := by group
        _ = (D.h₁ ^ m)⁻¹ * D.h₁ ^ n := by rw [hm]
        _ = D.h₁ ^ (n - m) := by
          rw [← zpow_neg, ← zpow_add]; congr 1; ring
    have hmem : D.h₂ ^ m ∈ D.H₁ ⊓ D.H₂ :=
      ⟨by rw [h2m]; exact zpow_mem (mem_zpowers _) _, zpow_mem (mem_zpowers _) _⟩
    rw [h1.H_inter] at hmem
    have hsq : D.h₂ ^ m * D.h₂ ^ m = 1 := by
      rcases eq_one_or_z hs hmem with h | h
      · rw [h, mul_one]
      · rw [h]; exact hz2
    have h2 : D.h₂ ^ (2 * m) = 1 := by rw [two_mul, zpow_add]; exact hsq
    have hd : (orderOf D.h₂ : ℤ) ∣ 2 * m := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [orderOf_h₂ D h1] at hd
    have hk : (((D.q - 1) / 2 : ℕ) : ℤ) ∣ m := by
      have : (((D.q - 1 : ℕ)) : ℤ) = 2 * (((D.q - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hq2
      rw [this] at hd
      exact Int.dvd_of_mul_dvd_mul_left (by norm_num) hd
    have hg : (D.h₁ * D.h₂) ^ m = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.mp
      rw [orderOf_h₁h₂ D hs h1]; exact hk
    rw [← hm0, hg]
    exact Subgroup.one_mem _
  · apply le_antisymm
    · exact sup_le (H₁_le_H D) (SPLNot1.H₀_le_H D.toSPLNot1)
    · show D.H₁ ⊔ D.H₂ ≤ D.H₁ ⊔ D.H₀
      refine sup_le le_sup_left ?_
      show zpowers D.h₂ ≤ _
      rw [zpowers_le]
      have : D.h₂ = D.h₁⁻¹ * (D.h₁ * D.h₂) := by group
      rw [this]
      exact (D.H₁ ⊔ D.H₀).mul_mem
        ((D.H₁ ⊔ D.H₀).inv_mem (Subgroup.mem_sup_left (mem_zpowers _)))
        (Subgroup.mem_sup_right (mem_zpowers _))

end H0Order

end CFSG.GH74.GLS.SP.Local
