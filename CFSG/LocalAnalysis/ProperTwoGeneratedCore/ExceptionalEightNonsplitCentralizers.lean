module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneSplitting

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

open scoped Pointwise

variable {Y : Type*} [Group Y]

theorem ncard_subgroup_conj_mul_card_inf_centralizer (H : Subgroup Y) [Finite H] (g : Y) :
    {y | ∃ h ∈ H, h * g * h⁻¹ = y}.ncard *
        Nat.card (H ⊓ Subgroup.centralizer {g} : Subgroup Y) = Nat.card H := by
  let _ : MulAction H Y :=
    MulAction.compHom Y ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (y : Y), h • y = (h : Y) * y * (h : Y)⁻¹ := fun h y =>
    ConjAct.toConjAct_smul (h : Y) y
  have horb : MulAction.orbit H g = {y | ∃ h ∈ H, h * g * h⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h g).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul _ g⟩
  have hstab : MulAction.stabilizer H g = (Subgroup.centralizer {g}).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hcard := (MulAction.stabilizer H g).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  exact hcard

theorem le_normalizer_of_commute {H K : Subgroup Y}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : K ≤ Subgroup.normalizer (H : Set Y) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [← hcomm z hz k hk, mul_inv_cancel_right]
    exact hz
  · intro hz
    have h1 := hcomm _ hz k hk
    have heq : z = k * z * k⁻¹ := by
      calc z = k⁻¹ * (k * z * k⁻¹ * k) := by group
        _ = k⁻¹ * (k * (k * z * k⁻¹)) := by rw [h1]
        _ = k * z * k⁻¹ := by group
    rw [heq]
    exact hz

section IndependentFacts

variable {V : Type*} [Group V] {e : Fin 3 → V}

theorem Independent.zero_ne_one (he : Independent e) : e 0 ≠ 1 := fun h1 =>
  absurd (he 1 0 0 (by simp [h1])).1 (by decide)

theorem Independent.one_ne_one (he : Independent e) : e 1 ≠ 1 := fun h1 =>
  absurd (he 0 1 0 (by simp [h1])).2.1 (by decide)

theorem Independent.two_ne_one (he : Independent e) : e 2 ≠ 1 := fun h1 =>
  absurd (he 0 0 1 (by simp [h1])).2.2 (by decide)

theorem Independent.two_ne_zero [IsElementaryAbelian 2 V] (he : Independent e) : e 2 ≠ e 0 :=
  fun h1 => absurd (he 1 0 1 (by
    simp only [zmod_two_val_one, pow_one, ZMod.val_zero, pow_zero, mul_one, h1]
    rw [← pow_two]; exact sq_eq_one_of_isElementaryAbelian _)).1 (by decide)

end IndependentFacts

section Outside

variable {U : Subgroup Y} [U.Normal] [IsElementaryAbelian 2 U]

theorem exists_outside_plane [Finite Y] (hU8 : Nat.card U = 8)
    (hcent : Subgroup.centralizer (U : Set Y) = U)
    (hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹)
    {x : Y} (hx2 : x * x ∈ U) (hxU : x ∉ U) :
    ∃ b₁ b₂ u₀ : Y, PlaneHyp U (U ⊓ Subgroup.centralizer {x}) b₁ b₂ u₀ := by
  classical
  let a : MulAut U := MulAut.conjNormal x
  have ha : ∀ z : U, ((a z : U) : Y) = x * z * x⁻¹ := fun z => MulAut.conjNormal_apply x z
  have ha1 : a ≠ 1 := by
    intro h1
    apply hxU
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro z hz
    have h2 := congrArg (fun σ : MulAut U => ((σ ⟨z, hz⟩ : U) : Y)) h1
    simp only [ha, MulAut.one_apply] at h2
    calc z * x = x * z * x⁻¹ * x := by rw [h2]
      _ = x * z := by group
  have ha2 : a * a = 1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rw [MulAut.mul_apply, ha, ha, MulAut.one_apply]
    calc x * (x * (z : Y) * x⁻¹) * x⁻¹ = (x * x) * z * (x * x)⁻¹ := by group
      _ = z := by rw [mul_comm_of_mem hx2 z.2, mul_inv_cancel_right]
  obtain ⟨e, he, hae0, hae1, hae2⟩ := exists_transvection_basis hU8 ha1 ha2
  have hfix : ∀ z : U, a z = z ↔ (z : Y) ∈ Subgroup.centralizer {x} := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 := congrArg Subtype.val h1
      rw [ha] at h2
      calc (z : Y) * x = x * z * x⁻¹ * x := by rw [h2]
        _ = x * z := by group
    · intro h1
      apply Subtype.ext
      rw [ha, ← h1, mul_inv_cancel_right]
  have hval : ∀ {p q : U}, p ≠ q → (p : Y) ≠ q := fun hpq e => hpq (Subtype.ext e)
  have he0 := he.zero_ne_one
  have he2 := he.two_ne_one
  have he20 := he.two_ne_zero
  have he1 : a (e 1) ≠ e 1 := fun h1 => he0 (mul_eq_right.mp (hae1 ▸ h1))
  have hBmem : ∀ z : U, (z : Y) ∈ U ⊓ Subgroup.centralizer {x} ↔ a z = z := fun z => by
    rw [Subgroup.mem_inf, hfix]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨z.2, h1⟩⟩
  have hB : U ⊓ Subgroup.centralizer {x} =
      Subgroup.zpowers (e 0 : Y) ⊔ Subgroup.zpowers (e 2 : Y) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨α, β, γ, hz⟩ := exists_coords he hU8 ⟨y, hy.1⟩
      have hfixy : a ⟨y, hy.1⟩ = ⟨y, hy.1⟩ := (hBmem ⟨y, hy.1⟩).mp hy
      rw [← hz, map_mul, map_mul, map_pow, map_pow, map_pow, hae0, hae1, hae2] at hfixy
      have hβ : β = 0 := by
        rcases zmod_two_cases β with hβ | hβ
        · exact hβ
        · exfalso
          rw [hβ, zmod_two_val_one, pow_one, pow_one] at hfixy
          have h1 : e 0 ^ α.val * (e 0 * e 1) = e 0 ^ α.val * e 1 := mul_right_cancel hfixy
          exact he0 (mul_eq_right.mp (mul_left_cancel h1))
      subst hβ
      have hy' : y = (e 0 : Y) ^ α.val * (e 2 : Y) ^ γ.val := by
        have := congrArg Subtype.val hz
        simpa using this.symm
      rw [hy']
      exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact (hBmem (e 0)).mpr hae0
      · rw [Subgroup.zpowers_le]
        exact (hBmem (e 2)).mpr hae2
  have horder : ∀ z : U, z ≠ 1 → orderOf (z : Y) = 2 := by
    intro z hz
    have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ (hval hz)
    rw [pow_two]
    exact mul_self_eq_one_of_mem z.2
  have hzU : ∀ i, Subgroup.zpowers (e i : Y) ≤ U := fun i => by
    rw [Subgroup.zpowers_le]; exact (e i).2
  have hcardB : Nat.card (U ⊓ Subgroup.centralizer {x} : Subgroup Y) = 4 := by
    rw [hB, card_sup_of_le_normalizer_of_inf_eq_bot]
    · rw [Nat.card_zpowers, Nat.card_zpowers, horder _ he0, horder _ he2]
    · exact le_normalizer_of_commute fun h hh k hk => mul_comm_of_mem (hzU 0 hh) (hzU 2 hk)
    · rw [eq_bot_iff]
      rintro y ⟨hy0, hy2⟩
      rcases mem_zpowers_of_orderOf_eq_two (horder _ he0) hy0 with rfl | rfl
      · exact Subgroup.one_mem _
      · rcases mem_zpowers_of_orderOf_eq_two (horder _ he2) hy2 with h1 | h1
        · exact absurd h1 (hval he0)
        · exact absurd h1.symm (hval he20)
  exact ⟨e 0, e 2, e 1,
    { card_U := hU8
      centralizer_U := hcent
      full := hfull
      le := inf_le_left
      card_B := hcardB
      b₁_mem := (hBmem (e 0)).mpr hae0
      b₂_mem := (hBmem (e 2)).mpr hae2
      b₁_ne_one := hval he0
      b₂_ne_one := hval he2
      b₂_ne_b₁ := hval he20
      u₀_mem := (e 1).2
      u₀_not_mem := fun h1 => he1 ((hBmem (e 1)).mp h1) }⟩

theorem outside_involution_centralizer [Finite Y] (hU8 : Nat.card U = 8)
    (hcent : Subgroup.centralizer (U : Set Y) = U)
    (hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹)
    (hnosplit : ¬ ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤)
    {x : Y} (hx2 : x * x = 1) (hxU : x ∉ U) :
    Nat.card (Subgroup.centralizer {x}) = 16 ∧
      (∃ y ∈ Subgroup.centralizer {x}, orderOf y = 4) ∧
      ∀ z ∈ Subgroup.centralizer ((U ⊓ Subgroup.centralizer {x} : Subgroup Y) : Set Y),
        z * z = 1 → z ∉ U → ∃ n : Y, n * x * n⁻¹ = z := by
  classical
  obtain ⟨b₁, b₂, u₀, h⟩ := exists_outside_plane hU8 hcent hfull (by rw [hx2]; exact U.one_mem)
    hxU
  set B := U ⊓ Subgroup.centralizer {x} with hB
  obtain ⟨c₁, hc₁, c₂, hc₂, hτ₁, hτ₂, hcc⟩ := h.exists_commuting_lifts
  have hl : PlaneLifts B b₁ b₂ u₀ c₁ c₂ := ⟨hc₁, hc₂, hτ₁, hτ₂, hcc⟩
  have hsq : ∀ d ∈ planeD B c₁ c₂, d * d = planeTau u₀ d := by
    rcases h.sq_dichotomy hl with hel | hsq
    · exact absurd (h.exists_complement_of_elementary hl hel) hnosplit
    · exact hsq
  set C := Subgroup.centralizer (B : Set Y) with hC
  set N := Subgroup.normalizer (B : Set Y) with hN
  set D := planeD B c₁ c₂ with hD
  have hxC : x ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp hb.2
  have hxD : x ∉ D := by
    intro hxD
    have h1 := hsq x hxD
    rw [hx2] at h1
    exact hxU ((h.planeTau_eq_one_iff hxC).mp h1.symm)
  have hCN : C ≤ N := PlaneHyp.centralizer_le_normalizer
  have hclass : {y | ∃ n ∈ N, n * x * n⁻¹ = y} = (C : Set Y) \ ((D : Set Y) ∪ (U : Set Y)) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨PlaneHyp.conj_mem_centralizer hn hxC, fun hzD => hxD ?_, fun hzU => hxU ?_⟩
      · have := h.conj_mem_planeD hl (Subgroup.inv_mem _ hn) hzD
        rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this
      · have := PlaneHyp.conj_mem_U (U := U) (y := n⁻¹) hzU
        rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this
    · rintro ⟨hzC, hzD, hzU⟩
      have _ := h.isKleinFour_B
      have hτxB := h.planeTau_mem hxC
      have hτzB := h.planeTau_mem hzC
      have hτx1 : planeTau u₀ x ≠ 1 := fun e => hxU ((h.planeTau_eq_one_iff hxC).mp e)
      have hτz1 : planeTau u₀ z ≠ 1 := fun e => hzU ((h.planeTau_eq_one_iff hzC).mp e)
      obtain ⟨α, hα⟩ : ∃ α : MulAut B, α ⟨_, hτxB⟩ = ⟨_, hτzB⟩ := by
        by_cases hxz : planeTau u₀ x = planeTau u₀ z
        · exact ⟨1, Subtype.ext hxz⟩
        · refine ⟨IsKleinFour.mulEquiv (Equiv.swap ⟨_, hτxB⟩ ⟨_, hτzB⟩)
            (Equiv.swap_apply_of_ne_of_ne ?_ ?_), Equiv.swap_apply_left _ _⟩
          · intro e; exact hτx1 (congrArg Subtype.val e).symm
          · intro e; exact hτz1 (congrArg Subtype.val e).symm
      obtain ⟨n, hn, hnα⟩ := h.exists_normalizer_of_mulAut α
      set w := n * x * n⁻¹ with hw
      have hwC : w ∈ C := PlaneHyp.conj_mem_centralizer hn hxC
      have hwD : w ∉ D := by
        intro hwD
        apply hxD
        have := h.conj_mem_planeD hl (Subgroup.inv_mem _ hn) hwD
        rwa [hw, show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this
      have hτw : planeTau u₀ w = planeTau u₀ z := by
        rw [hw, h.planeTau_conj hn hxC]
        have := hnα ⟨_, hτxB⟩
        rw [hα] at this
        exact this.symm
      have hvC : w⁻¹ * z ∈ C := Subgroup.mul_mem _ (Subgroup.inv_mem _ hwC) hzC
      have hτ1 : planeTau u₀ (1 : Y) = 1 := h.planeTau_of_mem_U U.one_mem
      have hvU : w⁻¹ * z ∈ U := by
        refine (h.planeTau_eq_one_iff hvC).mp ?_
        have h1 := h.planeTau_mul (Subgroup.inv_mem _ hwC) hwC
        rw [inv_mul_cancel, hτ1] at h1
        rw [h.planeTau_mul (Subgroup.inv_mem _ hwC) hzC, ← hτw]
        exact h1.symm
      have hvB : w⁻¹ * z ∈ B := by
        by_contra hvB
        obtain ⟨d, hd, hwd⟩ := h.eq_mul_u₀_of_not_mem hl hwC hwD
        have hub := (h.not_mem_iff hvU).mp hvB
        apply hzD
        have : z = d * (u₀ * (w⁻¹ * z)) := by rw [← mul_assoc, ← hwd]; group
        rw [this]
        exact Subgroup.mul_mem _ hd (h.B_le_planeD hl hub)
      have hzmem : z ∈ w • (B : Set Y) :=
        Set.mem_smul_set.mpr ⟨w⁻¹ * z, hvB, by rw [smul_eq_mul]; group⟩
      rw [← h.outside_class hl hwC hwD] at hzmem
      obtain ⟨c, hc, hcz⟩ := hzmem
      refine ⟨c * n, Subgroup.mul_mem _ (hCN hc) hn, ?_⟩
      rw [← hcz, hw]
      group
  have hncard : ((C : Set Y) \ ((D : Set Y) ∪ (U : Set Y))).ncard = 12 := by
    have hsub : (D : Set Y) ∪ (U : Set Y) ⊆ C := Set.union_subset
      (planeD_le_centralizer B c₁ c₂) h.U_le_centralizer
    have hC32 : (C : Set Y).ncard = 32 := by rw [← Nat.card_coe_set_eq]; exact h.card_C
    have hD16 : (D : Set Y).ncard = 16 := by rw [← Nat.card_coe_set_eq]; exact h.card_planeD hl
    have hU8' : (U : Set Y).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hU8
    have hB4 : (B : Set Y).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact h.card_B
    have hu := Set.ncard_union_add_ncard_inter (D : Set Y) (U : Set Y)
    have hinter : (D : Set Y) ∩ (U : Set Y) = (B : Set Y) := by
      rw [← Subgroup.coe_inf, h.planeD_inf_U hl]
    rw [hinter, hD16, hU8', hB4] at hu
    rw [Set.ncard_sdiff hsub, hC32]
    omega
  have hconjB : ∀ g : Y, g * x = x * g → ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hgx b hb
    obtain ⟨hbU, hbx⟩ := Subgroup.mem_inf.mp hb
    rw [Subgroup.mem_centralizer_singleton_iff] at hbx
    refine Subgroup.mem_inf.mpr ⟨PlaneHyp.conj_mem_U hbU, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgxg : g * x * g⁻¹ = x := by rw [hgx, mul_inv_cancel_right]
    calc g * b * g⁻¹ * x = g * b * g⁻¹ * (g * x * g⁻¹) := by rw [hgxg]
      _ = g * (b * x) * g⁻¹ := by group
      _ = g * (x * b) * g⁻¹ := by rw [hbx]
      _ = (g * x * g⁻¹) * (g * b * g⁻¹) := by group
      _ = x * (g * b * g⁻¹) := by rw [hgxg]
  have hCxN : Subgroup.centralizer {x} ≤ N := by
    intro g hg
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgx' : g⁻¹ * x = x * g⁻¹ := by
      calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hgx]
        _ = x * g⁻¹ := by group
    rw [hN, Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨hconjB g hgx b, fun hb => ?_⟩
    have := hconjB g⁻¹ hgx' _ hb
    rwa [show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group] at this
  have horb := ncard_subgroup_conj_mul_card_inf_centralizer N x
  rw [hclass, hncard, h.card_N, inf_eq_right.mpr hCxN] at horb
  have hcard16 : Nat.card (Subgroup.centralizer {x}) = 16 := by omega
  refine ⟨hcard16, ?_, ?_⟩
  rotate_left
  · intro z hzC hz2 hzU
    have hzD : z ∉ D := by
      intro hzD
      have h1 := hsq z hzD
      rw [hz2] at h1
      exact hzU ((h.planeTau_eq_one_iff hzC).mp h1.symm)
    have hz : z ∈ {y | ∃ n ∈ N, n * x * n⁻¹ = y} := by
      rw [hclass]
      exact ⟨hzC, by simp only [Set.mem_union, SetLike.mem_coe, not_or]; exact ⟨hzD, hzU⟩⟩
    obtain ⟨n, -, hn⟩ := hz
    exact ⟨n, hn⟩
  by_contra hno
  push Not at hno
  have hsq1 : ∀ y ∈ Subgroup.centralizer {x}, y * y = 1 := by
    intro y hy
    have hdvd : orderOf y ∣ 2 ^ 4 := by
      rw [show (2 : ℕ) ^ 4 = 16 by rfl, ← hcard16]
      exact Subgroup.orderOf_dvd_natCard _ hy
    obtain ⟨k, hk, hyk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hyk
      rw [hyk, one_mul]
    · rw [← pow_two, ← show 2 ^ 1 = 2 by rfl, ← hyk, pow_orderOf_eq_one]
    · exact absurd (by simpa using hyk) (hno y hy)
    · exfalso
      have h4 : orderOf (y ^ 2) = 4 := by
        rw [orderOf_pow_of_dvd (by norm_num) (by rw [hyk]; norm_num), hyk]
        norm_num
      exact hno _ (Subgroup.pow_mem _ hy 2) h4
    · exfalso
      have h4 : orderOf (y ^ 4) = 4 := by
        rw [orderOf_pow_of_dvd (by norm_num) (by rw [hyk]; norm_num), hyk]
        norm_num
      exact hno _ (Subgroup.pow_mem _ hy 4) h4
  have habel : ∀ y ∈ Subgroup.centralizer {x}, ∀ z ∈ Subgroup.centralizer {x},
      y * z = z * y := by
    intro y hy z hz
    have h1 := hsq1 (y * z) (Subgroup.mul_mem _ hy hz)
    have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq1 y hy)
    have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right (hsq1 z hz)
    calc y * z = (y * z)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = z * y := by rw [mul_inv_rev, hy1, hz1]
  have hle : Subgroup.centralizer {x} ≤ Subgroup.centralizer {x} ⊓ C := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
    rw [hC, Subgroup.mem_centralizer_iff]
    intro b hb
    exact habel b (Subgroup.mem_inf.mp hb).2 g hg
  have := Subgroup.card_le_of_le hle
  rw [hcard16, h.outside_card hl hsq hxC hxD] at this
  omega

end Outside

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
