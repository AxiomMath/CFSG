module

public import CFSG.LargeExtraspecial.AS35ZNIrr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification.Unitary

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

structure ZULocal (t : S.O) (P : Subgroup S.O) : Prop where
  le : P ≤ closure S.DbarAsc
  mem : t ∈ P
  extra : CFSG.IsExtraspecialPGroup 2 P
  card : Nat.card P = 2 ^ (2 * S.width - 3)
  center : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = t
  norm : ∀ c ∈ S.Mbar, c * t = t * c → ∀ x ∈ P, c * x * c⁻¹ ∈ P
  triv : ∀ x ∈ P, ∀ v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
  fix : ∀ x ∈ P, ∀ v ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  sym : ∀ W : Submodule (ZMod 2) S.Qt,
    (∀ m ∈ S.Mbar, ∀ w ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) →
    W ≤ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) → ¬ W ≤ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →
    ∃ Y : Subgroup S.O, Y ≤ P ∧ t ∈ Y ∧ ¬ Y ≤ zpowers t ∧ Nat.card Y ≤ 2 * Nat.card W ∧
      ∀ c ∈ S.Mbar, c * t = t * c → ∀ y ∈ Y, c * y * c⁻¹ ∈ Y

variable {S}

theorem sub_mem_fixSpace_of_triv {x t : S.O}
    (hx : ∀ v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (v : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  rw [fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate t.2,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro a ha
  change polarBilin S.q a _ = 0
  rw [polarBilin_apply_apply, polar_sub_right,
    ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2 a v, hx a ha, sub_self]

theorem mem_orthogonal_of_fix {x : S.O} {W : Submodule (ZMod 2) S.Qt}
    (hx : ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) {u : S.Qt}
    (hu : u ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin W) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
  rw [OrthoF2.mem_orthogonal_iff_polar] at hu ⊢
  intro w hw
  rw [← hx w hw, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2]
  exact hu w hw

theorem finrank_add_finrank_orthogonal_Qt (W : Submodule (ZMod 2) S.Qt) :
    finrank (ZMod 2) W + finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin W) =
      finrank (ZMod 2) S.Qt := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal
    S.polarBilin_isRefl W
  rw [LinearMap.BilinForm.orthogonal_top_eq_bot S.q_nondegenerate, inf_bot_eq, finrank_bot,
    add_zero] at h
  exact h

theorem card_submodule_Qt (W : Submodule (ZMod 2) S.Qt) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  have : Fintype W := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

namespace ZULocal

variable {t : S.O} {P : Subgroup S.O} (hP : S.ZULocal t P)
include hP

theorem mul_comm_t {y : S.O} (hy : y ∈ P) : y * t = t * y := by
  have h2 := hP.extra.2.2.2
  have hne : Subgroup.center P ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 (by rw [h2]; norm_num)
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzc : ∀ y ∈ P, (z : S.O) * y = y * z := by
    intro y hy
    have := (Subgroup.mem_center_iff.1 hz) ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  rcases hP.center z.1 z.2 hzc with h1 | h1
  · exact absurd (Subtype.ext h1) hz1'
  · rw [← h1]
    exact (hzc y hy).symm

theorem not_forall_comm (hn : 3 ≤ S.width) : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  intro hc
  have htop : Subgroup.center P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc _ y.2 _ x.2)
  have h2 := hP.extra.2.2.2
  rw [htop, Subgroup.card_top, hP.card] at h2
  have h3 : 2 ^ 3 ≤ 2 ^ (2 * S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end ZULocal

variable (S) in
@[expose] def fixDbar : Submodule (ZMod 2) S.Qt where
  carrier := {v | ∀ d ∈ S.DbarAsc, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  add_mem' {a b} ha hb d hd := by rw [map_add, ha d hd, hb d hd]
  zero_mem' d _ := map_zero _
  smul_mem' c v hv d hd := by rw [map_smul, hv d hd]

theorem fix_of_mem_closure {x : S.O} (hx : x ∈ closure S.DbarAsc) {v : S.Qt}
    (hv : v ∈ S.fixDbar) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  induction hx using Subgroup.closure_induction with
  | mem d hd => exact hv d hd
  | one => rfl
  | mul a b _ _ ha hb =>
    change (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ((b : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
    rw [hb, ha]
  | inv a _ ha =>
    calc ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
        = ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by rw [ha]
      _ = v := by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]; rfl

namespace ZUHyp

variable {k : ℕ} (h : S.ZUHyp k)
include h

omit h in
theorem fixDbar_inv {m : S.O} (hm : m ∈ S.Mbar) {w : S.Qt} (hw : w ∈ S.fixDbar) :
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.fixDbar := by
  intro d hd
  have hd' : m⁻¹ * d * m ∈ S.DbarAsc := by
    have := conj_mem (S.Mbar.inv_mem hm) hd
    rwa [inv_inv] at this
  have e : d * m = m * (m⁻¹ * d * m) := by group
  have h1 := hw _ hd'
  calc (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
      = ((d * m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := rfl
    _ = ((m * (m⁻¹ * d * m) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by rw [e]
    _ = (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ * d * m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := rfl
    _ = (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by rw [h1]

theorem nonempty : S.DbarAsc.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨ψ⟩ := h.psu
  have hk2 : 2 ≤ k + 2 := by omega
  obtain ⟨l, hl⟩ := AS35L.exists_mk_eq ψ (tq (isoVec hk2))
  have hbot : closure S.DbarAsc = ⊥ := by rw [hne, Subgroup.closure_empty]
  have hl1 : l = 1 := by
    have : (l : S.O) ∈ (⊥ : Subgroup S.O) := hbot ▸ l.2
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  rw [hl1, QuotientGroup.mk_one, map_one] at hl
  have hk := h.two_le
  exact tq_ne_one (by omega) (isoVec_ne_zero hk2) (isoVec_isotropic hk2) hl.symm

theorem exists_orderOf_mul_eq_three {t : S.O} (ht : t ∈ S.DbarAsc) :
    ∃ s ∈ S.DbarAsc, orderOf (s * t) = 3 := by
  by_contra hall
  push Not at hall
  have hcomm : ∀ s ∈ S.DbarAsc, s * t = t * s := by
    intro s hs
    rcases h.three hs ht with h1 | h2 | h3
    · exact AS35J.commute_of_orderOf_mul_le_two (mul_self hs) (mul_self ht) (Or.inl h1)
    · exact AS35J.commute_of_orderOf_mul_le_two (mul_self hs) (mul_self ht) (Or.inr h2)
    · exact absurd h3 (hall s hs)
  apply h.not_mem_center (d := mkL ht) ht
  rw [mem_center_iff']
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem s hs => exact (hcomm s hs).symm
  | one => rw [mul_one, one_mul]
  | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | inv a _ ha =>
    calc t * a⁻¹ = a⁻¹ * (a * t) * a⁻¹ := by group
      _ = a⁻¹ * (t * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * t := by group

theorem eq_zero_of_fix (hloc : ∀ t ∈ S.DbarAsc, ∃ P, S.ZULocal t P) {v : S.Qt}
    (hv : v ∈ S.fixDbar) : v = 0 := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hk := h.two_le
  have hw := h.width_eq
  have hfinQ : finrank (ZMod 2) S.Qt = 2 * (k + 2) := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  set W := S.fixDbar with hW
  by_cases hall : ∀ t ∈ S.DbarAsc, W ≤ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  · obtain ⟨t₀, ht₀⟩ := h.nonempty
    obtain ⟨ψ⟩ := h.psu
    obtain ⟨a, ha, b, hb, h3⟩ := (h.hyp.isTClass ht₀).exists_orderOf_eq_three hk ψ
    have h3' : orderOf (((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
        = 3 := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, ← Subgroup.coe_mul, Subgroup.orderOf_coe, h3]
    have hbot := (commSpace_mul_of_orderOf_eq_three S.q_nondegenerate (h.isTypeA ha)
      (h.isTypeA hb) h3').1
    have hva : v ∈ commSpace ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := hall _ ha hv
    have hvb : v ∈ commSpace ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := hall _ hb hv
    have hvab := Submodule.mem_inf.2 ⟨hva, hvb⟩
    rwa [hbot, Submodule.mem_bot] at hvab
  push Not at hall
  obtain ⟨t, ht, hWt⟩ := hall
  obtain ⟨P, hP⟩ := hloc t ht
  have hWfix : W ≤ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun w hw => mem_fixSpace.2 (hw t ht)
  have hWinv : ∀ m ∈ S.Mbar, ∀ w ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W :=
    fun m hm w hw => fixDbar_inv hm hw
  obtain ⟨Y, hYP, htY, hYz, hYcard, hYn⟩ := hP.sym W hWinv hWfix hWt
  have hY2 : IsPGroup 2 Y := hP.extra.1.to_le hYP
  have hne : ∃ y ∈ Y, y ≠ 1 ∧ y ≠ t := by
    by_contra hne
    push Not at hne
    apply hYz
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact one_mem _
    · rw [hne y hy hy1]; exact mem_zpowers t
  have hbound := h.two_pow_le_card ht (hYP.trans hP.le) hY2 htY
    (fun y hy => hP.mul_comm_t (hYP hy)) (fun c hc hct y hy => hYn c (closure_le hc) hct y hy)
    hne
  have hdimW : 2 * k ≤ finrank (ZMod 2) W := by
    have h1 := hbound.trans hYcard
    rw [card_submodule_Qt, pow_succ, mul_comm] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h1 (by norm_num))
  obtain ⟨s, hs, hst⟩ := h.exists_orderOf_mul_eq_three ht
  set α : S.Qt ≃ₗ[ZMod 2] S.Qt := (s : S.Qt ≃ₗ[ZMod 2] S.Qt) with hα
  set β : S.Qt ≃ₗ[ZMod 2] S.Qt := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hβ
  have hαA := h.isTypeA hs
  have hβA := h.isTypeA ht
  have h3 : orderOf (α * β) = 3 := by
    rw [hα, hβ, ← Subgroup.coe_mul, Subgroup.orderOf_coe, hst]
  obtain ⟨-, hsup, hfin4, hnd, hfixst⟩ :=
    commSpace_mul_of_orderOf_eq_three S.q_nondegenerate hαA hβA h3
  have hAperp := (orderOf_mul_eq_three_iff_of_isTypeA S.q_nondegenerate hαA hβA).1 h3
  set Wp := LinearMap.BilinForm.orthogonal S.q.polarBilin W with hWp
  have hfixα : fixSpace α = LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace α) :=
    fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate s.2
  have hfixβ : fixSpace β = LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace β) :=
    fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate t.2
  have hcommle : ∀ d ∈ S.DbarAsc, commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wp := by
    intro d hd x hx
    rw [hWp, OrthoF2.mem_orthogonal_iff_polar]
    intro w hwW
    have hwfix : w ∈ fixSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) := mem_fixSpace.2 (hwW d hd)
    rw [fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate d.2,
      OrthoF2.mem_orthogonal_iff_polar] at hwfix
    rw [polar_comm]
    exact hwfix x hx
  have hle : commSpace (α * β) ≤ Wp := by
    rw [hsup]
    exact sup_le (hcommle s hs) (hcommle t ht)
  have hdimWp : finrank (ZMod 2) Wp ≤ 4 := by
    have h1 := finrank_add_finrank_orthogonal_Qt (S := S) W
    change finrank (ZMod 2) W + finrank (ZMod 2) Wp = _ at h1
    omega
  have hWpeq : commSpace (α * β) = Wp :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hfin4]; exact hdimWp)
  have hαβO : α * β ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (s * t).2
  have hWinf : W ⊓ Wp = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxWp⟩ := Submodule.mem_inf.1 hx
    have hx1 : x ∈ fixSpace (α * β) := by
      rw [hfixst]
      exact Submodule.mem_inf.2 ⟨mem_fixSpace.2 (hxW s hs), mem_fixSpace.2 (hxW t ht)⟩
    rw [fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate hαβO] at hx1
    rw [← hWpeq] at hxWp
    have := Submodule.mem_inf.2 ⟨hxWp, hx1⟩
    rwa [hnd] at this
  have hWsup : W ⊔ Wp = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Wp
    rw [hWinf, finrank_bot, add_zero, finrank_add_finrank_orthogonal_Qt] at h1
    exact h1
  have hBorth : commSpace β ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace β) := by
    rw [← hfixβ]
    exact commSpace_le_fixSpace hβA.2.2.1
  have hmove : ∀ x ∈ P, ∀ u : S.Qt, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ commSpace β := by
    intro x hx u
    have hu : u ∈ W ⊔ Wp := by rw [hWsup]; exact Submodule.mem_top
    obtain ⟨w, hwW, y, hyWp, rfl⟩ := Submodule.mem_sup.1 hu
    have hxw : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fix_of_mem_closure (hP.le hx) hwW
    have hxy : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Wp :=
      Submodule.sub_mem _ (mem_orthogonal_of_fix (fun w hw => fix_of_mem_closure (hP.le hx) hw)
        hyWp) hyWp
    have hxy' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ fixSpace β :=
      sub_mem_fixSpace_of_triv (hP.triv x hx) y
    rw [← hWpeq, hsup, sup_comm] at hxy
    rw [hfixβ] at hxy'
    have hmem := Submodule.mem_inf.2 ⟨hxy, hxy'⟩
    rw [sup_inf_assoc_of_le _ hBorth, hAperp, sup_bot_eq] at hmem
    rw [map_add, hxw, add_sub_add_left_eq_sub]
    exact hmem
  exfalso
  apply hP.not_forall_comm (by omega)
  intro x hx y hy
  refine Subtype.ext (LinearEquiv.ext fun u => ?_)
  change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
  have hyu : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
  have hxu : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
  rw [hyu, map_add, hP.triv x hx _ (hmove y hy u), hxu, map_add, hP.triv y hy _ (hmove x hx u)]
  abel

end ZUHyp

end Setting

end CFSG.LargeExtraspecial
