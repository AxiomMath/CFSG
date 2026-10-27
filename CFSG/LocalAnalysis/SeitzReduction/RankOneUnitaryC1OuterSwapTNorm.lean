module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterSwapTMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

section Norm

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
include hS hL

theorem swapT_mem_U₁_cases
    (hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t)
    {w : G} (hwT : w ∈ T) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {h : G} (hh : h ∈ U ⊔ T) :
    h ∈ U₁ ∨ h * t⁻¹ ∈ U₁ ∨ h * w⁻¹ ∈ U₁ ∨ h * (t * w)⁻¹ ∈ U₁ := by
  have htT := (hS.start.start_of_card_sylow hS.card_sylow).1
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hTU₁ : ∀ x ∈ T, ∀ u ∈ U₁, x * u * x⁻¹ ∈ U₁ := fun x hx u hu =>
    (mem_normalizer_iff.mp (hL.T_le hx) u).mp hu
  rw [hL.muOne_sup_eq hS] at hh
  obtain ⟨x, hx, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hh
  have key : ∀ z : G, z ∈ T → x * z⁻¹ ∈ szT₁ L T ⊔ zpowers t →
      (x * u * z⁻¹ ∈ U₁ ∨ x * u * (t * z)⁻¹ ∈ U₁) := by
    intro z hz hxz
    obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers
      hS.start.mem_centralizer_szT₁ hxz
    rcases mem_zpowers_involution_eq_one_or_eq hS.start.sq_eq_one he with he1 | he1
    · left
      rw [he1, mul_one] at hye
      rw [show x * u * z⁻¹ = (x * z⁻¹) * (z * u * z⁻¹) by group, ← hye]
      exact mul_mem (hT₁U₁ hy) (hTU₁ z hz u hu)
    · right
      rw [he1] at hye
      have e1 : x * u * (t * z)⁻¹ = (x * z⁻¹ * t⁻¹) * ((t * z) * u * (t * z)⁻¹) := by group
      rw [e1, ← hye, show y * t * t⁻¹ = y by group]
      exact mul_mem (hT₁U₁ hy) (hTU₁ _ (mul_mem htT hz) u hu)
  by_cases hxH : x ∈ szT₁ L T ⊔ zpowers t
  · rcases key 1 (one_mem _) (by simpa using hxH) with h1 | h1
    · left; simpa using h1
    · right; left; simpa using h1
  · have h1 := hidx x hx w hwT hxH hwS
    rcases key w hwT h1 with h2 | h2
    · right; right; left; exact h2
    · right; right; right; exact h2

theorem swapT_comm_szA₁
    (hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t)
    {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) :
    U ⊔ T ≤ centralizer (szA₁ (szT₁ L T) : Set G) := by
  have htT := (hS.start.start_of_card_sylow hS.card_sylow).1
  have hU : U ≤ centralizer (szA₁ (szT₁ L T) : Set G) := fun u hu =>
    mem_centralizer_iff.mpr fun a ha => by
      have h1 := hL.conj_szA₁ u hu a ha
      calc a * u = (u * a * u⁻¹) * u := by rw [h1]
        _ = u * a := by group
  have hH : szT₁ L T ⊔ zpowers t ≤ centralizer (szA₁ (szT₁ L T) : Set G) := by
    refine sup_le (fun y hy => mem_centralizer_iff.mpr fun a ha => ?_) (zpowers_le.mpr ?_)
    · exact (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy).symm
    · exact mem_centralizer_iff.mpr fun a ha =>
        (mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ a (szA₁_le _ ha))
  have hw : w ∈ centralizer (szA₁ (szT₁ L T) : Set G) := mem_centralizer_iff.mpr fun a ha =>
    ((hS.start.outer_facts_of_card_sylow hS.card_sylow hwT hw2 hwS).2.1 a ha).symm
  refine sup_le hU fun τ hτ => ?_
  by_cases hτH : τ ∈ szT₁ L T ⊔ zpowers t
  · exact hH hτH
  · rw [show τ = (τ * w⁻¹) * w by group]
    exact mul_mem (hH (hidx τ hτ w hwT hτH hwS)) hw

theorem swapT_mem_szA₁_of_comm {z : G} (hz : z ∈ U ⊔ T)
    (hzc : ∀ σ ∈ U ⊔ T, z * σ = σ * z) : z ∈ szA₁ (szT₁ L T) := by
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hzT : z ∈ T := U3C1OuterLevelData.norm_mem_T_of_commute hS hL.isSylowOf.isPGroup
    le_sup_right hz (hzc t (mem_sup_right htT))
  have hzT₁ : ∀ y ∈ szT₁ L T, y * z = z * y := fun y hy =>
    (hzc y (mem_sup_right (szT₁_le_left L T hy))).symm
  have hzH : z ∈ szT₁ L T ⊔ zpowers t := by
    by_contra hzH
    obtain ⟨E, _, _, _, σ, u, v, hSC⟩ := h.exists_semilinearCoords_of_card_sylow hS2
    have hcent := U3SemilinearCoords.card_centralizer_le hSC h hS2 hzT hzH
    have h1 : szT₁ L T ⊓ centralizer ({z} : Set G) = szT₁ L T :=
      inf_eq_left.mpr fun y hy => mem_centralizer_singleton_iff.mpr (hzT₁ y hy)
    have h2 : Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 2 ^ f := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le inf_le_left
    rw [h1, hT₁card] at hcent
    have h3 : (2 ^ f) ^ 3 ≤ 2 * 2 ^ f := hcent.trans (Nat.mul_le_mul_left 2 h2)
    have h4 : 2 * 2 ^ f < (2 ^ f) ^ 3 := by
      calc 2 * 2 ^ f < 4 * (4 * 2 ^ f) := by omega
        _ ≤ 2 ^ f * (2 ^ f * 2 ^ f) := Nat.mul_le_mul hq4 (Nat.mul_le_mul_right _ hq4)
        _ = (2 ^ f) ^ 3 := by ring
    omega
  obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hzH
  have hyA : y ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun y' hy' => ?_⟩
    have h1 := hzT₁ y' hy'
    have het : e ∈ centralizer (szT₁ L T : Set G) :=
      (zpowers_le.mpr h.mem_centralizer_szT₁) he
    have h2 := mem_centralizer_iff.mp het y' hy'
    have hy1 : y = z * e⁻¹ := by rw [← hye]; group
    rw [hy1]
    calc y' * (z * e⁻¹) = (y' * z) * e⁻¹ := by group
      _ = z * y' * e⁻¹ := by rw [h1]
      _ = z * (e⁻¹ * (e * y') * e⁻¹) := by group
      _ = z * (e⁻¹ * (y' * e) * e⁻¹) := by rw [h2]
      _ = z * e⁻¹ * y' := by group
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
  · rw [← hye, he1, mul_one]
    exact hyA
  ·
    exfalso
    rw [he1] at hye
    have htU : ∀ u ∈ U₁, u * t = t * u := by
      intro u hu
      have h1 := hzc u (mem_sup_left (hL.U₁_le hu))
      have h2 := hL.conj_szA₁ u (hL.U₁_le hu) y hyA
      have hyu : y * u = u * y := by
        calc y * u = (u * y * u⁻¹) * u := by rw [h2]
          _ = u * y := by group
      rw [← hye] at h1
      calc u * t = y⁻¹ * (u * (y * t)) := by rw [← mul_assoc u y t, ← hyu]; group
        _ = y⁻¹ * (y * t * u) := by rw [h1]
        _ = t * u := by group
    have hU₁T₁ : U₁ ≤ szT₁ L T := fun u hu => by
      have h1 : u ∈ U ⊓ centralizer ({t} : Set G) :=
        mem_inf.mpr ⟨hL.U₁_le hu, mem_centralizer_singleton_iff.mpr (htU u hu)⟩
      rw [hL.inf_centralizer] at h1
      exact hL.muOne_mem_T₁_of_mem_T hS hu
        ((sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)) h1)
    have h1 := Subgroup.card_le_of_le hU₁T₁
    rw [hL.muOne_card_U₁ hS, hT₁card] at h1
    have h2 : (2 ^ f) ^ 3 < (2 ^ f) ^ 5 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem swapT_conj_szA₁
    (hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t)
    {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {g : G}
    (hg : g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G)) {a : G}
    (ha : a ∈ szA₁ (szT₁ L T)) : g * a * g⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hcen := hL.swapT_comm_szA₁ hS hidx hwT hw2 hwS
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have haS : a ∈ U ⊔ T := mem_sup_left (hL.U₁_le (hT₁U₁ (szA₁_le _ ha)))
  refine hL.swapT_mem_szA₁_of_comm hS ((mem_normalizer_iff.mp hg a).mp haS) fun σ hσ => ?_
  have hσ' : g⁻¹ * σ * g ∈ U ⊔ T := by
    have := (mem_normalizer_iff.mp (inv_mem hg) σ).mp hσ
    rwa [inv_inv] at this
  have h1 := mem_centralizer_iff.mp (hcen hσ') a ha
  calc g * a * g⁻¹ * σ = g * (a * (g⁻¹ * σ * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * σ * g) * a) * g⁻¹ := by rw [h1]
    _ = σ * (g * a * g⁻¹) := by group

theorem swapT_le_U₁ (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t)
    {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {X : Subgroup G}
    (hXS : X ≤ U ⊔ T) (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ szA₁ (szT₁ L T))
    (hXcard : (2 ^ f) ^ 5 ≤ Nat.card X) : X ≤ U₁ := by
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W, hWT₁, -, hWcard, -, -, -, hWiff⟩ := h.exists_W_of_card_sylow hS2 hwT hw2 hwS
  have hcommA := hL.muOne_comm_mem_szA₁ hS hc hμV hK hμ
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hVU₁ : V ≤ U₁ := le_sup_right.trans hL.sup_le_U₁
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (h.le hwT)
  have htN : ∀ u ∈ U₁, t * u * t⁻¹ ∈ U₁ := fun u hu =>
    (mem_normalizer_iff.mp (hL.T_le htT) u).mp hu
  have hred : ∀ y ∈ U₁, ∀ u ∈ U₁, ∀ z : G, y * (u * z) * y⁻¹ * (u * z)⁻¹ ∈ szA₁ (szT₁ L T) →
      y * z * y⁻¹ * z⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro y hy u hu z hz
    have e : u * (y * z * y⁻¹ * z⁻¹) * u⁻¹ =
        (y * u * y⁻¹ * u⁻¹)⁻¹ * (y * (u * z) * y⁻¹ * (u * z)⁻¹) := by group
    have h1 : u * (y * z * y⁻¹ * z⁻¹) * u⁻¹ ∈ szA₁ (szT₁ L T) := by
      rw [e]
      exact mul_mem (inv_mem (hcommA y hy u hu)) hz
    have h2 := hL.conj_szA₁ u⁻¹ (hL.U₁_le (inv_mem hu)) _ h1
    rw [show u⁻¹ * (u * (y * z * y⁻¹ * z⁻¹) * u⁻¹) * u⁻¹⁻¹ = y * z * y⁻¹ * z⁻¹ by group] at h2
    rw [h2]
    exact h1
  have hTV : Nat.card (szT₁ L T ⊔ V : Subgroup G) = (2 ^ f) ^ 4 := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := V) (B := szT₁ L T) (hL.muOne_T₁_le_normalizer hS)
    have hinf : V ⊓ szT₁ L T = szA₁ (szT₁ L T) := le_antisymm
      (fun z hz => mem_szA₁.mpr ⟨(mem_inf.mp hz).2, hS.conf.le_centralizer (mem_inf.mp hz).1⟩)
      (le_inf hS.conf.le (szA₁_le _))
    rw [hinf, hA₁card, hS.conf.card, hT₁card, sup_comm] at h1
    apply Nat.eq_of_mul_eq_mul_right hq0
    rw [h1]
    ring
  have hrT₁U₁ : (szT₁ L T).relIndex U₁ = (2 ^ f) ^ 2 := by
    have e2 := relIndex_mul_card (H := szT₁ L T) (K := U₁)
    rw [inf_of_le_left hT₁U₁, hT₁card, hL.muOne_card_U₁ hS] at e2
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq0 3)
    rw [e2]
    ring
  have hrT₁TV : (szT₁ L T).relIndex (szT₁ L T ⊔ V) = 2 ^ f := by
    have e2 := relIndex_mul_card (H := szT₁ L T) (K := szT₁ L T ⊔ V)
    rw [inf_of_le_left le_sup_left, hT₁card, hTV] at e2
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq0 3)
    rw [e2]
    ring
  have hrU₁SU : U₁.relIndex (U ⊔ T) = 4 := by
    obtain ⟨hTK, hKcard⟩ := h.swapT_card_eq_of_index_two hS2 hidx hwT hwS
    have hKT : (szT₁ L T ⊔ zpowers t) ⊔ zpowers w ≤ T :=
      sup_le (sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)) (zpowers_le.mpr hwT)
    have heq : (szT₁ L T ⊔ zpowers t) ⊔ zpowers w = T := le_antisymm hKT hTK
    rw [heq] at hKcard
    have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := U₁) (B := T) hL.T_le
    have hU₁T : U₁ ⊓ T = szT₁ L T :=
      le_antisymm (fun z hz => hL.muOne_mem_T₁_of_mem_T hS (mem_inf.mp hz).1 (mem_inf.mp hz).2)
        (le_inf hT₁U₁ (szT₁_le_left L T))
    have hSU : U ⊔ T = U₁ ⊔ T := by rw [hL.muOne_sup_eq hS, sup_comm]
    rw [hU₁T, hT₁card, hL.muOne_card_U₁ hS, hKcard, ← hSU] at hprod
    have hSUcard : Nat.card (U ⊔ T : Subgroup G) = 4 * (2 ^ f) ^ 5 := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hq0 3)
      rw [hprod]
      ring
    have h1 := relIndex_mul_card (H := U₁) (K := U ⊔ T)
    rw [inf_of_le_left (hL.U₁_le.trans le_sup_left), hL.muOne_card_U₁ hS, hSUcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 5) h1
  have hrel2 : ∀ z ∈ T, z ^ 2 = 1 → z ∉ U₁ → U₁.relIndex (U₁ ⊔ zpowers z) = 2 := fun z hz hz2 hzU =>
    RankOne.Endings.relIndex_sup_zpowers_eq_two hzU (hL.T_le hz) (by rw [← sq]; exact hz2)
  have htw2 : (t * w) ^ 2 = 1 := by
    rw [Commute.mul_pow hwt.symm 2, h.sq_eq_one, hw2, one_mul]
  have hnotU : ∀ z ∈ T, z ∉ szT₁ L T → z ∉ U₁ := fun z hz hzT₁ hzU =>
    hzT₁ (hL.muOne_mem_T₁_of_mem_T hS hzU hz)
  have htU : t ∉ U₁ := hL.t_not_mem
  have hwU : w ∉ U₁ := hnotU w hwT fun h' => hwS (mem_sup_left h')
  have htwU : t * w ∉ U₁ := hnotU _ (mul_mem htT hwT) fun h' => hwS (by
    rw [show w = t⁻¹ * (t * w) by group]
    exact mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) (mem_sup_left h'))
  set Y := U₁ ⊓ X with hYdef
  have hYcard := relIndex_mul_card (H := U₁) (K := X)
  have hYT := relIndex_mul_card (H := szT₁ L T) (K := Y)
  have hcover : ∀ x ∈ X, x ∈ U₁ ∨ x * t⁻¹ ∈ U₁ ∨ x * w⁻¹ ∈ U₁ ∨ x * (t * w)⁻¹ ∈ U₁ :=
    fun x hx => hL.swapT_mem_U₁_cases hS hidx hwT hwS (hXS hx)
  have hYA : (∃ x ∈ X, x * t⁻¹ ∈ U₁) → Y ≤ szT₁ L T ⊔ V := by
    rintro ⟨x₁, hx₁, hx₁U⟩ y hy
    obtain ⟨hyU, hyX⟩ := mem_inf.mp hy
    have h1 := hXc y hyX x₁ hx₁
    rw [show x₁ = (x₁ * t⁻¹) * t by group] at h1
    exact hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hyU (hred y hyU _ hx₁U t h1)
  have hYB : (∃ x ∈ X, x * w⁻¹ ∈ U₁ ∨ x * (t * w)⁻¹ ∈ U₁) → szT₁ L T ⊓ Y ≤ W := by
    rintro ⟨x₂, hx₂, hx₂U⟩ y hy
    obtain ⟨hyT₁, hyY⟩ := mem_inf.mp hy
    obtain ⟨hyU, hyX⟩ := mem_inf.mp hyY
    have h1 := hXc y hyX x₂ hx₂
    have hyw : y * w * y⁻¹ * w⁻¹ ∈ szA₁ (szT₁ L T) := by
      rcases hx₂U with h2 | h2
      · rw [show x₂ = (x₂ * w⁻¹) * w by group] at h1
        exact hred y hyU _ h2 w h1
      · rw [show x₂ = (x₂ * (t * w)⁻¹) * (t * w) by group] at h1
        have h3 := hred y hyU _ h2 (t * w) h1
        have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hyT₁
        have e : y * (t * w) * y⁻¹ * (t * w)⁻¹ = t * (y * w * y⁻¹ * w⁻¹) * t⁻¹ := by
          calc y * (t * w) * y⁻¹ * (t * w)⁻¹ = (y * t) * w * y⁻¹ * w⁻¹ * t⁻¹ := by group
            _ = (t * y) * w * y⁻¹ * w⁻¹ * t⁻¹ := by rw [hyt]
            _ = t * (y * w * y⁻¹ * w⁻¹) * t⁻¹ := by group
        rw [e] at h3
        have h4 := hL.conj_szA₁ t⁻¹ (inv_mem hL.t_mem_U) _ h3
        rw [show t⁻¹ * (t * (y * w * y⁻¹ * w⁻¹) * t⁻¹) * t⁻¹⁻¹ = y * w * y⁻¹ * w⁻¹ by group]
          at h4
        rw [h4]
        exact h3
    refine (hWiff y hyT₁).mp ?_
    have e : y⁻¹ * (w * y * w⁻¹) = y⁻¹ * (y * w * y⁻¹ * w⁻¹)⁻¹ * y := by group
    rw [e]
    have h5 := mem_centralizer_iff.mp (mem_szA₁.mp (inv_mem hyw)).2 y hyT₁
    rw [mul_assoc, ← h5, ← mul_assoc, inv_mul_cancel, one_mul]
    exact inv_mem hyw
  have hrU₁X : U₁.relIndex X ≤ 4 := by
    have := Subgroup.relIndex_le_of_le_right hXS (by rw [hrU₁SU]; norm_num)
    rwa [hrU₁SU] at this
  have hcardX : Nat.card X = U₁.relIndex X * Nat.card Y := hYcard.symm
  have hcardY : Nat.card Y = (szT₁ L T).relIndex Y * Nat.card (szT₁ L T ⊓ Y : Subgroup G) :=
    hYT.symm
  have hq5 : 2 * (2 ^ f) ^ 4 < (2 ^ f) ^ 5 := by
    calc 2 * (2 ^ f) ^ 4 < 2 ^ f * (2 ^ f) ^ 4 :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = (2 ^ f) ^ 5 := by ring
  have hq5' : 4 * (2 ^ f) ^ 3 < (2 ^ f) ^ 5 := by
    calc 4 * (2 ^ f) ^ 3 ≤ 2 ^ f * (2 ^ f) ^ 3 := Nat.mul_le_mul_right _ hq4
      _ = (2 ^ f) ^ 4 := by ring
      _ < (2 ^ f) ^ 5 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  by_contra hXU
  by_cases hA : ∃ x ∈ X, x * t⁻¹ ∈ U₁
  · by_cases hB : ∃ x ∈ X, x * w⁻¹ ∈ U₁ ∨ x * (t * w)⁻¹ ∈ U₁
    ·
      have r1 : (szT₁ L T).relIndex Y ≤ 2 ^ f := by
        have := Subgroup.relIndex_le_of_le_right (hYA hA) (by rw [hrT₁TV]; positivity)
        rwa [hrT₁TV] at this
      have c1 : Nat.card (szT₁ L T ⊓ Y : Subgroup G) ≤ (2 ^ f) ^ 2 := by
        rw [← hWcard]
        exact Subgroup.card_le_of_le (hYB hB)
      have h1 : Nat.card X ≤ 4 * (2 ^ f * (2 ^ f) ^ 2) := by
        rw [hcardX, hcardY]
        exact Nat.mul_le_mul hrU₁X (Nat.mul_le_mul r1 c1)
      have e : 4 * (2 ^ f * (2 ^ f) ^ 2) = 4 * (2 ^ f) ^ 3 := by ring
      omega
    ·
      push Not at hB
      have hXle : X ≤ U₁ ⊔ zpowers t := fun x hx => by
        rcases hcover x hx with h1 | h1 | h1 | h1
        · exact mem_sup_left h1
        · rw [show x = (x * t⁻¹) * t by group]
          exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers t))
        · exact absurd h1 (hB x hx).1
        · exact absurd h1 (hB x hx).2
      have hr := hrel2 t htT h.sq_eq_one htU
      have r : U₁.relIndex X ≤ 2 := by
        have := Subgroup.relIndex_le_of_le_right hXle (by rw [hr]; norm_num)
        rwa [hr] at this
      have c1 : Nat.card Y ≤ (2 ^ f) ^ 4 := by
        rw [← hTV]
        exact Subgroup.card_le_of_le (hYA hA)
      have h1 : Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
        rw [hcardX]
        exact Nat.mul_le_mul r c1
      omega
  · push Not at hA
    by_cases hB : ∃ x ∈ X, x * w⁻¹ ∈ U₁ ∨ x * (t * w)⁻¹ ∈ U₁
    ·
      have c1 : Nat.card Y ≤ (2 ^ f) ^ 4 := by
        have r1 : (szT₁ L T).relIndex Y ≤ (2 ^ f) ^ 2 := by
          have := Subgroup.relIndex_le_of_le_right (inf_le_left : Y ≤ U₁)
            (by rw [hrT₁U₁]; positivity)
          rwa [hrT₁U₁] at this
        have c2 : Nat.card (szT₁ L T ⊓ Y : Subgroup G) ≤ (2 ^ f) ^ 2 := by
          rw [← hWcard]
          exact Subgroup.card_le_of_le (hYB hB)
        rw [hcardY, show (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 by ring]
        exact Nat.mul_le_mul r1 c2
      have hz : ∃ z ∈ T, z ^ 2 = 1 ∧ z ∉ U₁ ∧ X ≤ U₁ ⊔ zpowers z := by
        by_cases hw' : ∃ x ∈ X, x * w⁻¹ ∈ U₁
        · obtain ⟨x₁, hx₁, hx₁U⟩ := hw'
          refine ⟨w, hwT, hw2, hwU, fun x hx => ?_⟩
          rcases hcover x hx with h1 | h1 | h1 | h1
          · exact mem_sup_left h1
          · exact absurd h1 (hA x hx)
          · rw [show x = (x * w⁻¹) * w by group]
            exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers w))
          · exfalso
            apply hA (x * x₁⁻¹) (mul_mem hx (inv_mem hx₁))
            rw [show x * x₁⁻¹ * t⁻¹ = (x * (t * w)⁻¹) * (t * (x₁ * w⁻¹)⁻¹ * t⁻¹) by group]
            exact mul_mem h1 (htN _ (inv_mem hx₁U))
        · push Not at hw'
          refine ⟨t * w, mul_mem htT hwT, htw2, htwU, fun x hx => ?_⟩
          rcases hcover x hx with h1 | h1 | h1 | h1
          · exact mem_sup_left h1
          · exact absurd h1 (hA x hx)
          · exact absurd h1 (hw' x hx)
          · rw [show x = (x * (t * w)⁻¹) * (t * w) by group]
            exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers _))
      obtain ⟨z, hzT, hz2, hzU, hXz⟩ := hz
      have hr := hrel2 z hzT hz2 hzU
      have r : U₁.relIndex X ≤ 2 := by
        have := Subgroup.relIndex_le_of_le_right hXz (by rw [hr]; norm_num)
        rwa [hr] at this
      have h1 : Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
        rw [hcardX]
        exact Nat.mul_le_mul r c1
      omega
    · push Not at hB
      apply hXU
      intro x hx
      rcases hcover x hx with h1 | h1 | h1 | h1
      · exact h1
      · exact absurd h1 (hA x hx)
      · exact absurd h1 (hB x hx).1
      · exact absurd h1 (hB x hx).2

end Norm

end U3C1OuterLevelData

theorem u3C1OuterSwapNormInput_holds : U3C1OuterSwapNormInput := by
  intro G _ _ L f t T R₂ D d V U U₁ hS hL hμV hidx w hwT hw2 hwS _ s hsN _ _ u hu
  set X : Subgroup G := U₁.map (MulAut.conj s).toMonoidHom with hXdef
  have hXmem : ∀ y ∈ U₁, s * y * s⁻¹ ∈ X := fun y hy => ⟨y, hy, by simp⟩
  have hXS : X ≤ U ⊔ T := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.mp hsN y).mp (mem_sup_left (hL.U₁_le hy))
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ szA₁ (szT₁ L T) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := hL.muOne_comm_mem_szA₁ hS hc hμV hK hμ a ha b hb
    have h2 := hL.swapT_conj_szA₁ hS hidx hwT hw2 hwS hsN h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show s * a * s⁻¹ * (s * b * s⁻¹) * (s * a * s⁻¹)⁻¹ * (s * b * s⁻¹)⁻¹ =
      s * (a * b * a⁻¹ * b⁻¹) * s⁻¹ by group]
    exact h2
  have h1 : Nat.card X = Nat.card U₁ := card_map_of_injective (MulAut.conj s).injective
  have hXcard : (2 ^ f) ^ 5 ≤ Nat.card X := (h1.trans (hL.muOne_card_U₁ hS)).ge
  exact hL.swapT_le_U₁ hS hμV hidx hwT hw2 hwS hXS hXc hXcard (hXmem u hu)

theorem u3C1OuterMuOneSwapInput_of_high'
    (hH : U3C1OuterSwapHighInput) : U3C1OuterMuOneSwapInput :=
  u3C1OuterMuOneSwapInput_of_high u3C1OuterSwapNormInput_holds hH

end CFSG.SeitzReduction.RankOne
