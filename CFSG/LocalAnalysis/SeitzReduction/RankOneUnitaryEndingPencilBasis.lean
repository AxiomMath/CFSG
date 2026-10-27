module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilCoords

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pencilB_card_sup_mul_card_inf_of_normal {G : Type*} [Group G] (A N : Subgroup G)
    [N.Normal] :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
  have h1 := Subgroup.relIndex_mul_card (H := N) (K := A ⊔ N)
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : N ≤ A ⊔ N)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

private theorem pencilB_card_sup_mul_card_inf {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := pencilB_card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem u_commutator (hc : U3RootCoords T₁ σ u v) {y y' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁) :
    u ⁅y, y'⁆ = 0 := by
  rw [commutatorElement_def, hc.mul_u _ (mul_mem (mul_mem hy hy') (inv_mem hy)) _ (inv_mem hy'),
    hc.mul_u _ (mul_mem hy hy') _ (inv_mem hy), hc.mul_u _ hy _ hy', hc.u_inv hy, hc.u_inv hy']
  ring

theorem v_commutator (hc : U3RootCoords T₁ σ u v) {y y' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁) :
    v ⁅y, y'⁆ = u y' * σ (u y) - u y * σ (u y') := by
  have hcT : ⁅y, y'⁆ ∈ T₁ := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
  have e : ⁅y, y'⁆ * (y' * y) = y * y' := by
    rw [commutatorElement_def]
    group
  have h1 := hc.mul_v _ hcT _ (mul_mem hy' hy)
  rw [e, hc.u_commutator hy hy', zero_mul, sub_zero, hc.mul_v _ hy' _ hy,
    hc.mul_v _ hy _ hy'] at h1
  linear_combination -h1

end U3RootCoords

namespace U3PencilCoords

variable {G : Type} [Group G] [Finite G] {L T R₂ U₁ : Subgroup G} {t : G} {f : ℕ} {E : Type}
  [Field E] [Fintype E] [CharP E 2] {σ : E →+* E} {u w : G → E} {d : G} {μ : E}
  {a χ₁ χ₂ : G → E}

theorem exists_bcoord
    (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hU : U3U1Data G L f t T R₂ U₁) :
    ∃ b : G → E, (∀ x ∈ U₁, ∀ y ∈ U₁, b (x * y) = b x + b y) ∧
      (∀ y ∈ szT₁ L T, ∀ r ∈ R₂, b (y * r) = u y) ∧
      (∀ x ∈ U₁, b (d * x * d⁻¹) = μ * b x) ∧
      (∀ x ∈ U₁, b (t * x * t⁻¹) = a x + b x) ∧
      (∀ x ∈ U₁, a x = 0 → b x = 0 → x ∈ R₂) ∧
      ∀ α β : E, ∃ x ∈ U₁, a x = α ∧ b x = β := by
  classical
  have hSc := hP.semilinear
  have hc := hSc.coords
  have hσ := hSc.sigma
  have hf : 2 ≤ f := h.two_le
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have hRU : R₂ ≤ U₁ := le_sup_right.trans hU.le
  have hTU : szT₁ L T ≤ U₁ := le_sup_left.trans hU.le
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hcomR : ∀ x ∈ U₁, ∀ y ∈ U₁, ⁅x, y⁆ ∈ R₂ := fun x hx y hy => by
    rw [commutatorElement_def]
    exact hU.comm_mem x hx y hy
  have hkey : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := by
    intro x
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  have hdT := hP.d_mem_normalizer
  have hdR := hP.d_mem_normalizer_R₂
  have hdU := hP.d_mem_normalizer_U₁
  have hμ0 := hP.mu_ne_zero
  have hdpowU : ∀ i : ℕ, ∀ x ∈ U₁, d ^ i * x * (d ^ i)⁻¹ ∈ U₁ := fun i x hx =>
    (mem_normalizer_iff.mp (pow_mem hdU i) x).mp hx
  have hdpowR : ∀ i : ℕ, ∀ r ∈ R₂, d ^ i * r * (d ^ i)⁻¹ ∈ R₂ := fun i r hr =>
    (mem_normalizer_iff.mp (pow_mem hdR i) r).mp hr
  have hdpowT : ∀ i : ℕ, ∀ y ∈ szT₁ L T, d ^ i * y * (d ^ i)⁻¹ ∈ szT₁ L T := fun i y hy =>
    (mem_normalizer_iff.mp (pow_mem hdT i) y).mp hy
  have hdpowu : ∀ i : ℕ, ∀ y ∈ szT₁ L T, u (d ^ i * y * (d ^ i)⁻¹) = μ ^ i * u y :=
    fun i => U3RootCoords.u_conj_pow hdT hP.u_conj_d i
  have hdn : d ^ orderOf d = 1 := pow_orderOf_eq_one d
  obtain ⟨x₁, hx₁T, hx₁u⟩ := hc.u_surj 1
  have hx₁U := hTU hx₁T
  have hμn : μ ^ orderOf d = 1 := by
    have h1 := hdpowu (orderOf d) x₁ hx₁T
    rw [hdn, one_mul, inv_one, mul_one, hx₁u, mul_one] at h1
    exact h1.symm
  have hμq : μ ^ (2 ^ f - 1) ≠ 1 := by
    intro h1
    have hq4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hle := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h1)
    rw [hP.orderOf_mu] at hle
    have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg0 : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h3 : 2 ^ f ≤ ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) := by
      rw [Nat.le_div_iff_mul_le hg0]
      have h4 : 2 ^ f * Nat.gcd 3 (2 ^ f + 1) ≤ 2 ^ f * 3 := Nat.mul_le_mul_left _ hg
      have h5 : 4 * 2 ^ f ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ hq4
      rw [sq]
      omega
    omega
  have hgeom : ∑ i ∈ Finset.range (orderOf d), (μ ^ (2 ^ f - 1)) ^ i = 0 := by
    have h1 : (μ ^ (2 ^ f - 1)) ^ orderOf d = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hμn, one_pow]
    rw [geom_sum_eq hμq, h1, sub_self, zero_div]
  have hnE : ((orderOf d : ℕ) : E) = 1 := by
    obtain ⟨m, hm⟩ := hP.odd_orderOf_d
    rw [hm]
    push_cast
    rw [h2, zero_mul, zero_add]
  set b : G → E := fun x =>
    ∑ i ∈ Finset.range (orderOf d), (μ⁻¹) ^ i * χ₂ ⁅d ^ i * x * (d ^ i)⁻¹, x₁⁆ with hb
  have hb_add : ∀ x ∈ U₁, ∀ y ∈ U₁, b (x * y) = b x + b y := by
    intro x hx y hy
    simp only [hb]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hX := hdpowU i x hx
    have hY := hdpowU i y hy
    have e : d ^ i * (x * y) * (d ^ i)⁻¹ =
        (d ^ i * x * (d ^ i)⁻¹) * (d ^ i * y * (d ^ i)⁻¹) := by group
    rw [e, SplitComm.mul_left_eq (hUR _ hX _ (hcomR _ hY _ hx₁U)).symm
      (hR.comm _ (hcomR _ hY _ hx₁U) _ (hcomR _ hX _ hx₁U)),
      hP.chi₂_mul _ (hcomR _ hX _ hx₁U) _ (hcomR _ hY _ hx₁U)]
    ring
  have hb_T : ∀ y ∈ szT₁ L T, ∀ r ∈ R₂, b (y * r) = u y := by
    intro y hy r hr
    have hterm : ∀ i : ℕ, (μ⁻¹) ^ i * χ₂ ⁅d ^ i * (y * r) * (d ^ i)⁻¹, x₁⁆ =
        (μ ^ (2 ^ f - 1)) ^ i * σ (u y) + u y := by
      intro i
      have hY := hdpowT i y hy
      have hRi := hdpowR i r hr
      have e : d ^ i * (y * r) * (d ^ i)⁻¹ =
          (d ^ i * y * (d ^ i)⁻¹) * (d ^ i * r * (d ^ i)⁻¹) := by group
      have hcomm' : (d ^ i * r * (d ^ i)⁻¹) * x₁ = x₁ * (d ^ i * r * (d ^ i)⁻¹) :=
        (hR.commT₁ x₁ hx₁T _ hRi).symm
      have hCT : ⁅d ^ i * y * (d ^ i)⁻¹, x₁⁆ ∈ szT₁ L T := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hY hx₁T) (inv_mem hY)) (inv_mem hx₁T)
      have hA : ⁅d ^ i * y * (d ^ i)⁻¹, x₁⁆ ∈ szA₁ (szT₁ L T) :=
        (hSc.mem_szA₁_iff _ hCT).mpr (hc.u_commutator hY hx₁T)
      have hinv : (μ⁻¹) ^ i * μ ^ i = 1 := by rw [← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
      have hμq' : μ ^ (2 ^ f) = μ ^ (2 ^ f - 1) * μ := by
        rw [← pow_succ]
        congr 1
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
      rw [e, SplitComm.mul_right_of_commute hcomm', hP.chi₂_of_mem_szA₁ _ hA,
        hc.v_commutator hY hx₁T, hx₁u, map_one, mul_one, one_mul, hdpowu i y hy, map_mul,
        map_pow, hσ μ, hμq']
      linear_combination ((μ ^ (2 ^ f - 1)) ^ i * σ (u y) - u y) * hinv - u y * h2
    simp only [hb]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.sum_mul, hgeom,
      zero_mul, zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnE, one_mul]
  have hb_d : ∀ x ∈ U₁, b (d * x * d⁻¹) = μ * b x := by
    intro x hx
    simp only [hb]
    set F : ℕ → E := fun j => (μ⁻¹) ^ j * χ₂ ⁅d ^ j * x * (d ^ j)⁻¹, x₁⁆ with hF
    have hshift : ∀ i : ℕ,
        d ^ i * (d * x * d⁻¹) * (d ^ i)⁻¹ = d ^ (i + 1) * x * (d ^ (i + 1))⁻¹ := by
      intro i
      rw [pow_succ]
      group
    have hFn : F (orderOf d) = F 0 := by
      simp only [hF, hdn, pow_zero, inv_pow, hμn, inv_one]
    have hμμ : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
    have h1 := Finset.sum_range_succ' F (orderOf d)
    have h3 := Finset.sum_range_succ F (orderOf d)
    calc ∑ i ∈ Finset.range (orderOf d), (μ⁻¹) ^ i * χ₂ ⁅d ^ i * (d * x * d⁻¹) * (d ^ i)⁻¹, x₁⁆
        = μ * ∑ i ∈ Finset.range (orderOf d), F (i + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hshift]
          simp only [hF]
          rw [pow_succ μ⁻¹ i]
          linear_combination (-(μ⁻¹) ^ i * χ₂ ⁅d ^ (i + 1) * x * (d ^ (i + 1))⁻¹, x₁⁆) * hμμ
      _ = μ * ∑ i ∈ Finset.range (orderOf d), F i := by
          congr 1
          rw [h3, hFn] at h1
          exact (add_right_cancel h1).symm
  have hψ : ∀ x ∈ U₁, x * (t * x * t⁻¹) ∈ szT₁ L T ⊔ R₂ := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp hx
    refine hU.mem_sup_of_comm_mem hR htt (mul_mem hx hx') ?_
    have e : x * (t * x * t⁻¹) * t * (x * (t * x * t⁻¹))⁻¹ * t⁻¹ =
        x * (t * x * t⁻¹) * x⁻¹ * (t * x * t⁻¹)⁻¹ := by
      calc x * (t * x * t⁻¹) * t * (x * (t * x * t⁻¹))⁻¹ * t⁻¹
          = x * (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ := by group
        _ = x * (t * x * t⁻¹) * x⁻¹ * (t * x * t⁻¹)⁻¹ := by rw [hkey]
    rw [e]
    exact hU.comm_mem x hx _ hx'
  have hb_t : ∀ x ∈ U₁, b (t * x * t⁻¹) = a x + b x := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp hx
    obtain ⟨y, hy, r, hr, hyr⟩ := hR.mem_sup_iff.mp (hψ x hx)
    have h1 := hb_add x hx _ hx'
    rw [← hyr, hb_T y hy r hr, ← hP.a_spec x hx y hy r hr hyr] at h1
    linear_combination -h1 - b x * h2
  have hTR : ∀ x ∈ U₁, a x = 0 → x ∈ szT₁ L T ⊔ R₂ := by
    intro x hx ha
    have h1 := (hP.a_eq_zero_iff x hx).mp ha
    have hx' : t * x * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp hx
    have hcomm : x * t * x⁻¹ * t⁻¹ ∈ R₂ := by
      have e : x * t * x⁻¹ * t⁻¹ = (x * (t * x * t⁻¹)) * ((t * x * t⁻¹) ^ 2)⁻¹ := by
        rw [sq]
        group
      rw [e]
      exact mul_mem h1 (inv_mem (hU.sq_mem _ hx'))
    exact hU.mem_sup_of_comm_mem hR htt hx hcomm
  have hinj : ∀ x ∈ U₁, a x = 0 → b x = 0 → x ∈ R₂ := by
    intro x hx ha hb0
    obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp (hTR x hx ha)
    rw [hb_T y hy r hr] at hb0
    have hyA : y ∈ szA₁ (szT₁ L T) := (hSc.mem_szA₁_iff y hy).mpr hb0
    exact mul_mem (hR.le hyA) hr
  have ha_onto : ∀ α : E, ∃ x ∈ U₁, a x = α := by
    let Aim : AddSubgroup E :=
      { carrier := {z | ∃ x ∈ U₁, a x = z}
        zero_mem' := ⟨1, one_mem _, hP.a_one⟩
        add_mem' := by
          rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
          exact ⟨x * x', mul_mem hx hx', hP.a_mul x hx x' hx'⟩
        neg_mem' := by
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨x⁻¹, inv_mem hx, hP.a_inv hx⟩ }
    have hAim : ∀ z ∈ Aim, μ * z ∈ Aim := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨d * x * d⁻¹, (mem_normalizer_iff.mp hdU x).mp hx, hP.a_conj_d hx⟩
    rcases SemilinearField.eq_bot_or_eq_top_of_orderOf hf hSc.card hP.orderOf_mu Aim hAim with
      hbot | htop
    · exfalso
      have hle : U₁ ≤ szT₁ L T ⊔ R₂ := fun x hx => hTR x hx (by
        have hm : a x ∈ Aim := ⟨x, hx, rfl⟩
        rw [hbot] at hm
        exact (AddSubgroup.mem_bot).mp hm)
      have hcard := Subgroup.card_le_of_le hle
      have hprod := pencilB_card_sup_mul_card_inf (A := R₂) (B := szT₁ L T) hR.T₁_le_normalizer
      obtain ⟨hT₁card, hA₁card, -⟩ := h.facts_of_card_sylow hS2
      rw [sup_comm, inf_comm, hR.inf, hR.card, hT₁card, hA₁card] at hprod
      rw [hU.card] at hcard
      have h5 := Nat.mul_le_mul_right (2 ^ f) hcard
      rw [hprod] at h5
      have hq2 : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 : (2 ^ f) ^ 5 < (2 ^ f) ^ 7 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      have e1 : (2 ^ f) ^ 6 * 2 ^ f = (2 ^ f) ^ 7 := by ring
      have e2 : (2 ^ f) ^ 2 * (2 ^ f) ^ 3 = (2 ^ f) ^ 5 := by ring
      omega
    · intro z
      have hm : z ∈ Aim := htop ▸ AddSubgroup.mem_top z
      exact hm
  have hsurj : ∀ α β : E, ∃ x ∈ U₁, a x = α ∧ b x = β := by
    intro α β
    obtain ⟨x', hx', hax'⟩ := ha_onto α
    obtain ⟨y, hy, hyu⟩ := hc.u_surj (β - b x')
    have hyt : t * y * t⁻¹ = y := by rw [← hR.t_comm y hy, mul_inv_cancel_right]
    have hay : a y = 0 := (hP.a_eq_zero_iff y (hTU hy)).mpr (by
      rw [hyt, ← sq]
      exact hU.sq_mem y (hTU hy))
    have hby : b y = u y := by
      have := hb_T y hy 1 (one_mem _)
      rwa [mul_one] at this
    refine ⟨x' * y, mul_mem hx' (hTU hy), ?_, ?_⟩
    · rw [hP.a_mul _ hx' _ (hTU hy), hax', hay, add_zero]
    · rw [hb_add _ hx' _ (hTU hy), hby, hyu]
      ring
  exact ⟨b, hb_add, hb_T, hb_d, hb_t, hinj, hsurj⟩

end U3PencilCoords

end CFSG.SeitzReduction.RankOne
