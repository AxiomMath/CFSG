module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoSetup
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28Elem
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis SzPartition CFSG.ABGLocalTools

@[expose] def NoStronglyClosedAbelianTwo (G : Type) [Group G] : Prop :=
  ∀ (S : Sylow 2 G) (A : Subgroup G), A ≤ S → IsMulCommutative A → A ≠ ⊥ →
    (∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A) → False

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]

namespace SzRSetup

variable {T₁ R : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K}
  (h : SzRSetup T₁ R t d a u v κ)
include h

theorem t_ne_one : t ≠ 1 := fun h1 => h.t_not_mem (h1 ▸ one_mem T₁)

theorem isMulCommutative_szA : IsMulCommutative (szA₁ T₁ ⊔ zpowers t : Subgroup G) :=
  IsMulCommutative.of_comm fun x y => Subtype.ext (h.commute_of_mem_szA y.2 (h.szA_le_T x.2))

theorem conj_pow_mul_inv_mem (k : ℕ) {w : G} (hw : w ∈ szA₁ T₁ ⊔ zpowers t) :
    (d ^ k)⁻¹ * w * d ^ k * w⁻¹ ∈ szA₁ T₁ := by
  obtain ⟨b, hb, s, hs, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.t_mem_szA₁ hw
  have hds : d * s = s * d := commute_of_mem_zpowers hs h.d_comm
  have hs' : (d ^ k)⁻¹ * s * d ^ k = s := by
    rw [mul_assoc, ← ((Commute.pow_left hds k).eq)]
    group
  have hb' : (d ^ k)⁻¹ * b * d ^ k ∈ szA₁ T₁ := by
    have := (mem_normalizer_iff.mp (inv_mem (pow_mem h.d_mem_normalizer_szA₁ k)) b).mp hb
    simpa using this
  have e : (d ^ k)⁻¹ * (b * s) * d ^ k * (b * s)⁻¹ =
      (d ^ k)⁻¹ * b * d ^ k * ((d ^ k)⁻¹ * s * d ^ k) * s⁻¹ * b⁻¹ := by group
  rw [e, hs', mul_inv_cancel_right]
  exact mul_mem hb' (inv_mem hb)

theorem sq_mem_szA (h34 : NoStronglyClosedAbelianTwo G) {r : G} (hr : r ∈ R) :
    r ^ 2 ∈ szA₁ T₁ ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsq : ∀ z ∈ T₁ ⊔ zpowers t, z ^ 2 ∈ szA₁ T₁ ⊔ zpowers t := fun z hz =>
    mem_sup_left (h.sq_mem_szA₁_of_mem_T hz)
  by_cases hA : ∃ r₀ ∈ R, r₀ ∉ T₁ ⊔ zpowers t ∧ r₀ ^ 2 ∈ szA₁ T₁ ⊔ zpowers t
  · obtain ⟨r₀, hr₀, hr₀T, hr₀A⟩ := hA
    by_cases hrT : r ∈ T₁ ⊔ zpowers t
    · exact hTsq r hrT
    obtain ⟨k, hk⟩ := h.exists_conj_mem hr₀ hr hr₀T hrT
    set c := (d ^ k)⁻¹ * r₀ * d ^ k with hc
    have hc2 : c ^ 2 ∈ szA₁ T₁ ⊔ zpowers t := by
      have e : c ^ 2 = (d ^ k)⁻¹ * r₀ ^ 2 * d ^ k := by rw [hc, sq, sq]; group
      rw [e]
      have := (mem_normalizer_iff.mp (inv_mem (pow_mem h.d_mem_normalizer_szA k)) _).mp hr₀A
      simpa using this
    have hv₁ := h.conj_mul_inv_mem_szA (inv_mem hr) hk
    have hw2 := hTsq _ hk
    have e : r ^ 2 = c * c * (r⁻¹ * c * (r⁻¹ * c))⁻¹ *
        (r⁻¹ * (r⁻¹ * c) * r⁻¹⁻¹ * (r⁻¹ * c)⁻¹)⁻¹ := by group
    rw [e]
    rw [sq] at hc2 hw2
    exact mul_mem (mul_mem hc2 (inv_mem hw2)) (inv_mem hv₁)
  · exfalso
    push Not at hA
    have hinv : ∀ x ∈ R, x ^ 2 = 1 → x ∈ szA₁ T₁ ⊔ zpowers t := by
      intro x hx hx2
      by_cases hxT : x ∈ T₁ ⊔ zpowers t
      · exact h.coords.mem_of_sq_eq_one h.one_le h.card h.t_mem h.t_sq hxT hx2
      · exact absurd (hx2 ▸ one_mem _) (hA x hx hxT)
    have hconj : ∀ w ∈ szA₁ T₁ ⊔ zpowers t, ∀ g : G, (g⁻¹ * w * g) ^ 2 = 1 := by
      intro w hw g
      have e : (g⁻¹ * w * g) ^ 2 = g⁻¹ * w ^ 2 * g := by rw [sq, sq]; group
      rw [e, h.sq_eq_one_of_mem_szA hw]
      group
    have hNR : normalizer (R : Set G) ≤
        normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) := fun g hg =>
      mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => hinv _ (by
        have := (mem_normalizer_iff.mp (inv_mem hg) w).mp (h.szA_le_R hw)
        simpa using this) (hconj w hw g)
    have hRG : IsSylowOf 2 R ⊤ := by
      by_contra hnot
      obtain ⟨S, hRS, z, hzS, hzN, hzR⟩ :=
        GMS28.exists_mem_normalizer_of_not_isSylowOf h.isPGroup hnot
      have hP : IsPGroup 2 (R ⊔ zpowers z : Subgroup G) :=
        S.isPGroup'.to_le (sup_le hRS (zpowers_le.mpr hzS))
      exact hzR (h.mem_of_isPGroup z (hNR hzN) hP)
    obtain ⟨-, hR2, hRidx⟩ := isSylowOf_iff.mp hRG
    rw [relIndex_top_right] at hRidx
    let S : Sylow 2 G := hR2.toSylow hRidx
    have hSc : (S : Subgroup G) = R := IsPGroup.toSylow_coe hR2 hRidx
    have hA1 : szA₁ T₁ ⊔ zpowers t ≠ ⊥ := fun hb => h.t_ne_one (by
      have ht := mem_sup_right (S := szA₁ T₁) (mem_zpowers t)
      rw [hb, mem_bot] at ht
      exact ht)
    refine h34 S (szA₁ T₁ ⊔ zpowers t) (hSc ▸ h.szA_le_R) h.isMulCommutative_szA hA1
      fun w hw g hg => ?_
    exact hinv _ (hSc ▸ hg) (hconj w hw g)

theorem comm_mem_szA (h34 : NoStronglyClosedAbelianTwo G) {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * x⁻¹ * y⁻¹ ∈ szA₁ T₁ ⊔ zpowers t :=
  comm_mem_of_sq_mem_of_conj_mem (fun n hn => by
      have := (mem_normalizer_iff.mp (inv_mem (h.le_normalizer hy)) n).mp hn
      simpa using this)
    (h.sq_mem_szA h34 hx) (h.sq_mem_szA h34 hy) (h.sq_mem_szA h34 (mul_mem hx hy))

theorem comm_mem_szA₁_of_mem_T₁ (h34 : NoStronglyClosedAbelianTwo G) {y : G} (hy : y ∈ T₁)
    {x : G} (hx : x ∈ R) : y * x * y⁻¹ * x⁻¹ ∈ szA₁ T₁ := by
  by_cases hxT : x ∈ T₁ ⊔ zpowers t
  · obtain ⟨y', hy', s, hs, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.t_mem hxT
    have hys : y * s = s * y := commute_of_mem_zpowers hs (mem_centralizer_iff.mp h.t_mem y hy)
    have e : y * (y' * s) * y⁻¹ * (y' * s)⁻¹ = y * y' * (s * y⁻¹ * s⁻¹) * y'⁻¹ := by group
    have hs' : s * y⁻¹ * s⁻¹ = y⁻¹ := by
      have : y⁻¹ * s = s * y⁻¹ := by
        calc y⁻¹ * s = y⁻¹ * (s * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * s) * y⁻¹ := by rw [hys]
          _ = s * y⁻¹ := by group
      rw [← this]
      group
    rw [e, hs']
    exact h.coords.comm_mem_szA₁ h.one_le h.card hy hy'
  set b := x⁻¹ * y * x * y⁻¹ with hb
  have hbA : b ∈ szA₁ T₁ ⊔ zpowers t := by
    have := h.conj_mul_inv_mem_szA (inv_mem hx) (mem_sup_left hy)
    simpa [hb] using this
  have hx2 := h.sq_mem_szA h34 hx
  have hyx2 : y * x ^ 2 * y⁻¹ = x ^ 2 := by
    rw [h.commute_of_mem_szA hx2 (mem_sup_left hy)]
    group
  have hb2 : b * b = 1 := by rw [← sq]; exact h.sq_eq_one_of_mem_szA hbA
  have hxb : x * b = b * x := by
    have e1 : (x * b) * (x * b) = x * x := by
      have : (x * b) * (x * b) = y * x ^ 2 * y⁻¹ := by rw [hb, sq]; group
      rw [this, hyx2, sq]
    have e2 : b * x * b = x := by
      have := congrArg (fun g => x⁻¹ * g) e1
      simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact this
    calc x * b = b * b * x * b := by rw [hb2, one_mul]
      _ = b * (b * x * b) := by group
      _ = b * x := by rw [e2]
  have hbA₁ : b ∈ szA₁ T₁ := by
    rcases mem_sup_zpowers_cases h.t_mem_szA₁ h.t_sq hbA with hb1 | ⟨c, hc, hbc⟩
    · exact hb1
    · exfalso
      apply hxT
      have hxc := h.commute_szA₁_of_mem hx hc
      rw [hbc] at hxb
      have hxt : x * t = t * x := by
        have e3 : c * (x * t) = c * (t * x) := by
          calc c * (x * t) = x * c * t := by rw [← mul_assoc, hxc]
            _ = x * (c * t) := by group
            _ = c * t * x := hxb
            _ = c * (t * x) := by group
        exact mul_left_cancel e3
      rw [← h.inf_centralizer]
      exact mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr hxt⟩
  have e : y * x * y⁻¹ * x⁻¹ = x * b * x⁻¹ := by rw [hb]; group
  rw [e, h.conj_szA₁ hx hbA₁]
  exact hbA₁

theorem conj_mul_inv_mem_szA₁ (h34 : NoStronglyClosedAbelianTwo G) {x : G} (hx : x ∈ R) {z : G}
    (hz : z ∈ T₁ ⊔ zpowers t) : x * z * x⁻¹ * z⁻¹ ∈ szA₁ T₁ := by
  obtain ⟨y, hy, s, hs, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.t_mem hz
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ szA₁ T₁ := by
    have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (h.comm_mem_szA₁_of_mem_T₁ h34 hy hx)
  have h2 : x * s * x⁻¹ * s⁻¹ ∈ szA₁ T₁ := by
    rcases mem_zpowers_involution_eq_one_or_eq h.t_sq hs with rfl | rfl
    · rw [show x * 1 * x⁻¹ * 1⁻¹ = 1 by group]
      exact one_mem _
    · exact h.rho_mem x hx
  have e : x * (y * s) * x⁻¹ * (y * s)⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (y * (x * s * x⁻¹ * s⁻¹) * y⁻¹) := by group
  rw [e]
  refine mul_mem h1 ?_
  rw [mem_centralizer_iff.mp (mem_szA₁.mp h2).2 y hy, mul_inv_cancel_right]
  exact h2

theorem sq_mul_inv_sq_mem (h34 : NoStronglyClosedAbelianTwo G) {x x' : G} (hx : x ∈ R)
    (hx' : x' ∈ R) (hxT : x ∉ T₁ ⊔ zpowers t) (hx'T : x' ∉ T₁ ⊔ zpowers t) :
    x ^ 2 * (x' ^ 2)⁻¹ ∈ szA₁ T₁ := by
  obtain ⟨k, hk⟩ := h.exists_conj_mem hx hx' hxT hx'T
  set c := (d ^ k)⁻¹ * x * d ^ k with hc
  have h1 : c ^ 2 * (x ^ 2)⁻¹ ∈ szA₁ T₁ := by
    have e : c ^ 2 * (x ^ 2)⁻¹ = (d ^ k)⁻¹ * x ^ 2 * d ^ k * (x ^ 2)⁻¹ := by
      rw [hc, sq, sq]
      group
    rw [e]
    exact h.conj_pow_mul_inv_mem k (h.sq_mem_szA h34 hx)
  have h2 : c ^ 2 * (x' ^ 2)⁻¹ ∈ szA₁ T₁ := by
    set w := x'⁻¹ * c with hw
    have hcw : c = x' * w := by rw [hw]; group
    have ha : x'⁻¹ * w * x'⁻¹⁻¹ * w⁻¹ ∈ szA₁ T₁ := h.conj_mul_inv_mem_szA₁ h34 (inv_mem hx') hk
    have hw2 : w * w ∈ szA₁ T₁ := by rw [← sq]; exact h.sq_mem_szA₁_of_mem_T hk
    have e : c ^ 2 * (x' ^ 2)⁻¹ =
        x' ^ 2 * ((x'⁻¹ * w * x'⁻¹⁻¹ * w⁻¹) * (w * w)) * (x' ^ 2)⁻¹ := by
      rw [hcw, sq, sq]
      group
    rw [e, h.conj_szA₁ (pow_mem hx' 2) (mul_mem ha hw2)]
    exact mul_mem ha hw2
  have e : x ^ 2 * (x' ^ 2)⁻¹ = (c ^ 2 * (x ^ 2)⁻¹)⁻¹ * (c ^ 2 * (x' ^ 2)⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem h1) h2

theorem eq_of_mul_eq_one {b b' : G} (hb : b ∈ szA₁ T₁) (h1 : b * b' = 1) : b' = b := by
  have hb2 : b * b = 1 := by rw [← sq]; exact h.sq_eq_one_of_mem_szA₁ hb
  exact (mul_left_cancel (h1.trans hb2.symm))

theorem sq_mem_szA₁ (h34 : NoStronglyClosedAbelianTwo G) {x : G} (hx : x ∈ R) :
    x ^ 2 ∈ szA₁ T₁ := by
  by_cases hxT : x ∈ T₁ ⊔ zpowers t
  · exact h.sq_mem_szA₁_of_mem_T hxT
  set b₀ := x * t * x⁻¹ * t⁻¹ with hb₀
  have hb₀A := h.rho_mem x hx
  have hq : 4 < Nat.card (szA₁ T₁) := by
    rw [h.card_szA₁]
    have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by have := h.one_le; omega)
    omega
  have hnotT : ∀ z ∈ R, z * t * z⁻¹ * t⁻¹ ≠ 1 → z ∉ T₁ ⊔ zpowers t := fun z hz h1 h2 =>
    h1 ((h.rho_eq_one_iff hz).mpr h2)
  have hρ : ∀ b ∈ szA₁ T₁, ∃ y ∈ R, y * t * y⁻¹ * t⁻¹ = b := by
    intro b hb
    obtain ⟨y, hy, hye⟩ := h.exists_conj b hb
    exact ⟨y, hy, by rw [hye]; group⟩
  obtain ⟨b₁, hb₁, hb₁S⟩ := exists_mem_not_mem_of_ncard_lt (H := szA₁ T₁)
    (S := ({1, b₀, 1, 1} : Set G)) (Set.toFinite _)
    ((ncard_insert_four_le _ _ _ _).trans_lt hq)
  obtain ⟨b₂, hb₂, hb₂S⟩ := exists_mem_not_mem_of_ncard_lt (H := szA₁ T₁)
    (S := ({1, b₀, b₁, b₀ * b₁} : Set G)) (Set.toFinite _)
    ((ncard_insert_four_le _ _ _ _).trans_lt hq)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb₁S hb₂S
  obtain ⟨y₁, hy₁, hρ₁⟩ := hρ b₁ hb₁
  obtain ⟨y₂, hy₂, hρ₂⟩ := hρ b₂ hb₂
  have hne : ∀ b ∈ szA₁ T₁, ∀ b' : G, b' ≠ b → b * b' ≠ 1 := fun b hb b' hb' h1 =>
    hb' (h.eq_of_mul_eq_one hb h1)
  refine sq_mem_of_sq_mul_inv_sq_mem (X := R) (A := T₁ ⊔ zpowers t) (A₁ := szA₁ T₁)
    (fun x hx b hb => by rw [h.conj_szA₁ hx hb]; exact hb)
    (fun x hx y hy => h.szA_le_T (h.comm_mem_szA h34 hx hy))
    (fun x hx w hw => h.conj_mul_inv_mem_szA₁ h34 hx hw)
    (fun x hx x' hx' hxT hx'T => h.sq_mul_inv_sq_mem h34 hx hx' hxT hx'T) hx hxT hy₁ hy₂
    (hnotT y₁ hy₁ (by rw [hρ₁]; exact hb₁S.1)) (hnotT y₂ hy₂ (by rw [hρ₂]; exact hb₂S.1))
    (hnotT _ (mul_mem hy₁ hy₂) ?_) (hnotT _ (mul_mem hx hy₁) ?_) (hnotT _ (mul_mem hx hy₂) ?_)
    (hnotT _ (mul_mem hx (mul_mem hy₁ hy₂)) ?_)
  · rw [h.rho_mul hy₁ hy₂, hρ₁, hρ₂]
    exact hne b₁ hb₁ b₂ hb₂S.2.2.1
  · rw [h.rho_mul hx hy₁, hρ₁]
    exact hne b₀ hb₀A b₁ hb₁S.2.1
  · rw [h.rho_mul hx hy₂, hρ₂]
    exact hne b₀ hb₀A b₂ hb₂S.2.1
  · rw [h.rho_mul hx (mul_mem hy₁ hy₂), h.rho_mul hy₁ hy₂, hρ₁, hρ₂]
    intro h1
    apply hb₂S.2.2.2
    have h2 : b₁ * b₂ = b₀ := h.eq_of_mul_eq_one hb₀A h1
    have hb₁2 : b₁ * b₁ = 1 := by rw [← sq]; exact h.sq_eq_one_of_mem_szA₁ hb₁
    calc b₂ = b₁ * b₁ * b₂ := by rw [hb₁2, one_mul]
      _ = b₁ * (b₁ * b₂) := by group
      _ = b₁ * b₀ := by rw [h2]
      _ = b₀ * b₁ := h.commute_szA₁ hb₁ hb₀A

theorem comm_mem_szA₁ (h34 : NoStronglyClosedAbelianTwo G) {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * x⁻¹ * y⁻¹ ∈ szA₁ T₁ :=
  comm_mem_of_sq_mem_of_conj_mem (fun n hn => by
      have := h.conj_szA₁ (inv_mem hy) hn
      rw [inv_inv] at this
      rw [this]
      exact hn)
    (h.sq_mem_szA₁ h34 hx) (h.sq_mem_szA₁ h34 hy) (h.sq_mem_szA₁ h34 (mul_mem hx hy))

end SzRSetup

end CFSG.SeitzReduction.RankOne
