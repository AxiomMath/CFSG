module

public import CFSG.CGT.Timmesfeld75.Sec5Eight
public import CFSG.CGT.Timmesfeld75.Sec5NineLift
public import CFSG.CGT.Timmesfeld75.Sec5NineExcl
public import CFSG.CGT.Timmesfeld75.Step511Card

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Action

variable {G : Type} [Group G] {T L₁ : Subgroup G}

@[expose] def actQuot (T : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    NQuot T →* MulAut ↥T :=
  QuotientGroup.lift (T.subgroupOf (Subgroup.normalizer (T : Set G))) T.normalizerMonoidHom (by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun t => Subtype.ext ?_
    have hxT : (x : G) ∈ T := hx
    show (x : G) * (t : G) * (x : G)⁻¹ = (t : G)
    rw [hT _ hxT _ t.2, mul_inv_cancel_right])

theorem actQuot_barElt (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {x : G}
    (hx : x ∈ Subgroup.normalizer (T : Set G)) (t : ↥T) :
    ((actQuot T hT (barElt T hx) t : ↥T) : G) = x * t * x⁻¹ := rfl

@[expose] def actHBar (T L₁ : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    ↥(hBar T L₁) →* MulAut ↥T :=
  (actQuot T hT).comp (hBar T L₁).subtype

variable {T₁ : Subgroup G}

theorem mem_center_hBar_of_centralizes (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G))
    (hnine : ∀ c ∈ hSub T L₁, (∀ t ∈ T, c * t = t * c) → ∀ x ∈ hSub T L₁, ⁅c, x⁆ ∈ T)
    {u : G} (hu : u ∈ Subgroup.normalizer (T : Set G)) (huH : u ∈ hSub T L₁)
    (huc : ∀ t ∈ T, u * t * u⁻¹ = t) :
    (⟨barElt T hu, barElt_mem_hBar hL₁ hu huH⟩ : ↥(hBar T L₁)) ∈ Subgroup.center ↥(hBar T L₁) := by
  refine Subgroup.mem_center_iff.2 fun z => ?_
  obtain ⟨x, hx, hxH, hxz⟩ := exists_mem_hSub_of_mem_hBar hL₁ z.2
  have hcomm := hnine u huH (fun t ht => by
    have := huc t ht
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this) x hxH
  have h := bar_comm_of_commutator_mem hu hx hcomm
  apply Subtype.ext
  show (z : NQuot T) * barElt T hu = barElt T hu * (z : NQuot T)
  rw [← hxz]
  exact h.symm

theorem ker_actHBar_le_center (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G))
    (hnine : ∀ c ∈ hSub T L₁, (∀ t ∈ T, c * t = t * c) → ∀ x ∈ hSub T L₁, ⁅c, x⁆ ∈ T) :
    (actHBar T L₁ hT).ker ≤ Subgroup.center ↥(hBar T L₁) := by
  intro y hy
  obtain ⟨u, hu, huH, hux⟩ := exists_mem_hSub_of_mem_hBar hL₁ y.2
  have hyk : actHBar T L₁ hT y = 1 := hy
  have e : actHBar T L₁ hT y = actQuot T hT (barElt T hu) := by
    show actQuot T hT (y : NQuot T) = _
    rw [← hux]
  have huc : ∀ t ∈ T, u * t * u⁻¹ = t := by
    intro t ht
    have h1 : actQuot T hT (barElt T hu) = 1 := e ▸ hyk
    have h2 := actQuot_barElt hT hu ⟨t, ht⟩
    rw [h1] at h2
    exact h2.symm
  have hy' : y = ⟨barElt T hu, barElt_mem_hBar hL₁ hu huH⟩ := Subtype.ext hux.symm
  rw [hy']
  exact mem_center_hBar_of_centralizes hL₁ hnine hu huH huc

section O2

variable [Finite G]

theorem hBar_O2_le_center (hT : IsElemAbelian 2 T) (hT1 : T ≠ ⊥)
    (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G))
    (hnine : ∀ c ∈ hSub T L₁, (∀ t ∈ T, c * t = t * c) → ∀ x ∈ hSub T L₁, ⁅c, x⁆ ∈ T)
    (htr : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T L₁, h * x * h⁻¹ = y)
    (P : Subgroup ↥(hBar T L₁)) (hPn : P.Normal) (hP2 : IsPGroup 2 P) :
    P ≤ Subgroup.center ↥(hBar T L₁) := by
  have hHN := hSub_le_normalizer hL₁
  set Q : Subgroup (NQuot T) := P.map (hBar T L₁).subtype with hQ
  have hQ2 : IsPGroup 2 Q := hP2.map _
  have hQn : ∀ h (hh : h ∈ hSub T L₁), ∀ y ∈ Q,
      barElt T (hHN hh) * y * (barElt T (hHN hh))⁻¹ ∈ Q := by
    intro h hh y hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hy
    have hb : barElt T (hHN hh) ∈ hBar T L₁ := barElt_mem_hBar hL₁ (hHN hh) hh
    exact Subgroup.mem_map.2 ⟨⟨barElt T (hHN hh), hb⟩ * p * ⟨barElt T (hHN hh), hb⟩⁻¹,
      hPn.conj_mem p hp _, rfl⟩
  intro x hx
  obtain ⟨u, hu, huH, hux⟩ := exists_mem_hSub_of_mem_hBar hL₁ x.2
  have huQ : u ∈ liftBar T Q :=
    mem_liftBar.2 ⟨hu, by rw [hux]; exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩⟩
  have huc := centralizes_of_normal_pGroup hT hT1 hHN htr hQ2 hQn huQ
  have hx' : x = ⟨barElt T hu, barElt_mem_hBar hL₁ hu huH⟩ := Subtype.ext hux.symm
  rw [hx']
  exact mem_center_hBar_of_centralizes hL₁ hnine hu huH huc

theorem not_comm_hBar (hT : IsElemAbelian 2 T) (hT4 : 4 ≤ Nat.card T)
    (hWC : IsWC (barSub T L₁)) (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G))
    (hL₁2 : IsPGroup 2 L₁)
    (htr : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T L₁, h * x * h⁻¹ = y) :
    ∃ a b : ↥(hBar T L₁), a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    simp at hT4
  have hHN := hSub_le_normalizer hL₁
  have hcl : Subgroup.normalClosure (((barSub T L₁).subgroupOf (hBar T L₁) :
      Subgroup ↥(hBar T L₁)) : Set ↥(hBar T L₁)) = ⊤ := normalClosure_subgroupOf_eq_top hWC
  set E : Subgroup ↥(hBar T L₁) := (barSub T L₁).subgroupOf (hBar T L₁) with hE
  have hEn : E.Normal := ⟨fun n hn g => by
    rwa [show g * n * g⁻¹ = n by rw [hcomm g n, mul_inv_cancel_right]]⟩
  have hle : Subgroup.normalClosure (E : Set ↥(hBar T L₁)) ≤ E :=
    Subgroup.normalClosure_le_normal fun x hx => hx
  rw [hcl] at hle
  have hBL : hBar T L₁ ≤ barSub T L₁ := fun x hx =>
    Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_top (⟨x, hx⟩ : ↥(hBar T L₁))))
  have hQ2 : IsPGroup 2 (hBar T L₁) := (isPGroup_barSub hL₁2).to_le hBL
  have hQn : ∀ h (hh : h ∈ hSub T L₁), ∀ y ∈ hBar T L₁,
      barElt T (hHN hh) * y * (barElt T (hHN hh))⁻¹ ∈ hBar T L₁ := fun h hh y hy =>
    (hBar T L₁).mul_mem ((hBar T L₁).mul_mem (barElt_mem_hBar hL₁ (hHN hh) hh) hy)
      ((hBar T L₁).inv_mem (barElt_mem_hBar hL₁ (hHN hh) hh))
  have hcen : ∀ h ∈ hSub T L₁, ∀ t ∈ T, h * t * h⁻¹ = t := fun h hh =>
    centralizes_of_normal_pGroup hT hT1 hHN htr hQ2 hQn
      (mem_liftBar.2 ⟨hHN hh, barElt_mem_hBar hL₁ (hHN hh) hh⟩)
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_mul_ne_one_of_four_le_card hT hT4
  obtain ⟨h, hh, hhx⟩ := htr x hx hx1 y hy hy1
  rw [hcen h hh x hx] at hhx
  exact hxy (by rw [hhx]; exact elemAbelian_mul_self hT hy)

end O2

end Action

section Numerics

theorem card_quotient_lt {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T : Subgroup G}
    (hT1 : T ≠ ⊥) (hTtop : T ≠ ⊤) (Q : Subgroup (NQuot T)) (Z : Subgroup ↥Q) [Z.Normal] :
    Nat.card (↥Q ⧸ Z) < Nat.card G := by
  have h1 : Nat.card (↥Q ⧸ Z) ≤ Nat.card ↥Q := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have h0 : 0 < Nat.card ↥Z := Nat.card_pos
    calc Nat.card (↥Q ⧸ Z) ≤ Nat.card (↥Q ⧸ Z) * Nat.card ↥Z := Nat.le_mul_of_pos_right _ h0
      _ = Nat.card ↥Q := h.symm
  have h2 : Nat.card ↥Q ≤ Nat.card (NQuot T) := Subgroup.card_le_card_group Q
  have h3 : Nat.card (NQuot T) ≤ Nat.card ↥(Subgroup.normalizer (T : Set G)) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (T.subgroupOf (Subgroup.normalizer (T : Set G)))
    have h0 : 0 < Nat.card ↥(T.subgroupOf (Subgroup.normalizer (T : Set G))) := Nat.card_pos
    calc Nat.card (NQuot T) ≤ Nat.card (NQuot T) *
          Nat.card ↥(T.subgroupOf (Subgroup.normalizer (T : Set G))) :=
        Nat.le_mul_of_pos_right _ h0
      _ = _ := h.symm
  have hne : Subgroup.normalizer (T : Set G) ≠ ⊤ := by
    intro h
    have hn : T.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h' | h'
    exacts [hT1 h', hTtop h']
  have h4 : Nat.card ↥(Subgroup.normalizer (T : Set G)) < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _)
      (fun h => hne ((Subgroup.card_eq_iff_eq_top _).1 h))
  omega

theorem card_normIn_facts (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) {G : Type} [Group G] {T T₁ : Subgroup G} (hy : StepHyp T T₁)
    (hS3 : Sec3 T T₁) (h4 : 4 < Nat.card T) :
    4 ≤ Nat.card (normIn T₁ T) ∧ Nat.card T ≤ Nat.card (normIn T₁ T) ^ 2 := by
  have : Finite G := hy.finite
  obtain ⟨m, r, hm, hr, hq, hT⟩ := step511_card h214 hInv hIso hy
  have hdvd : Nat.card (normIn T T₁) ∣ Nat.card T :=
    Subgroup.card_dvd_of_le (normIn_le T T₁)
  have hmul : 2 ^ m * Nat.card (normIn T T₁) = Nat.card T := by
    rw [← hq]
    exact Nat.div_mul_cancel hdvd
  have hL : Nat.card (normIn T T₁) = (2 ^ m) ^ r := by
    have h2 : 0 < 2 ^ m := pow_pos (by norm_num) m
    refine Nat.eq_of_mul_eq_mul_left h2 ?_
    rw [hmul, hT, pow_succ, mul_comm]
  rw [hS3.card_normIn_swap, hL]
  have hmr : 2 ≤ m * r := by
    by_contra hlt
    push Not at hlt
    have h1 : m * r = 1 := by
      have : 1 ≤ m * r := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hr1 : r = 1 := Nat.eq_one_of_mul_eq_one_left h1
    subst hm1
    subst hr1
    rw [hT] at h4
    norm_num at h4
  refine ⟨?_, ?_⟩
  · rw [← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m * r) := Nat.pow_le_pow_right (by norm_num) hmr
  · rw [hT]
    calc (2 ^ m) ^ (r + 1) ≤ (2 ^ m) ^ (r * 2) :=
        Nat.pow_le_pow_right (pow_pos (by norm_num) m) (by omega)
      _ = ((2 ^ m) ^ r) ^ 2 := pow_mul _ _ _

end Numerics

theorem sec59
    (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    (h215 : Lemma215Stmt) (hList : ListWCIdentification) (h9 : A9Input)
    (h1 : Sec4NoA) (h3 : Sec4Nine) (h57 : Step57)
    {G : Type} [Group G] {T T₁ : Subgroup G} (hy : StepHyp T T₁) (h4 : 4 < Nat.card T) :
    Ident59Out ↥(hBar T (normIn T₁ T))
      ((barSub T (normIn T₁ T)).subgroupOf (hBar T (normIn T₁ T))) := by
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hP.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  have hS3 : Sec3 T T₁ := hP.sec3 hS
  have hT := hP.wc
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => elemAbelian_mul_comm hT.1 ha hb
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun x hx => (mem_normIn.1 hx).2
  have hL₁2 : IsPGroup 2 (normIn T₁ T) :=
    (isPGroup_two_of_isElemAbelian hS3.cfg.wc₁.1).to_le (normIn_le _ _)
  have hWC : IsWC (barSub T (normIn T₁ T)) := sec48_of_noA h1 G T T₁ hy hS hI
  have hsec58 := sec58 h1 hy hS hI
  have htr := h57 G T T₁ hy
  have hnine : ∀ c ∈ hSub T (normIn T₁ T), (∀ t ∈ T, c * t = t * c) →
      ∀ x ∈ hSub T (normIn T₁ T), ⁅c, x⁆ ∈ T := by
    intro c hc hct x hx
    rw [← hsec58] at hc hx
    exact h3 G T T₁ hy hS hI h4 c hc hct x hx
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    simp at h4
  have hTtop : T ≠ ⊤ := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := hy.nonab
    exact hab (hTc a (Subgroup.mem_top a) b (Subgroup.mem_top b))
  obtain ⟨hL4, hTL⟩ := card_normIn_facts h214 hInv hIso hy hS3 h4
  have hEcard : Nat.card ((barSub T (normIn T₁ T)).subgroupOf (hBar T (normIn T₁ T))) =
      Nat.card (normIn T₁ T) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe barSub_le_hBar).toEquiv]
    exact card_barSub hL₁N (le_antisymm (le_trans (le_inf inf_le_right
      (le_trans inf_le_left (normIn_le T₁ T))) hS3.cfg.inf.le) bot_le)
  exact ident59_abstract hy.ind h215 hList h9 (isWC_subgroupOf hWC _ barSub_le_hBar)
    (normalClosure_subgroupOf_eq_top hWC) (not_comm_hBar hT.1 (by omega) hWC hL₁N hL₁2 htr)
    (hEcard ▸ hL4) (hBar_O2_le_center hT.1 hT1 hL₁N hnine htr)
    (card_quotient_lt hT1 hTtop _ _) (fun a b => Subtype.ext (hTc a a.2 b b.2))
    (fun a => Subtype.ext (elemAbelian_mul_self hT.1 a.2)) (actHBar T (normIn T₁ T) hTc)
    (ker_actHBar_le_center hTc hL₁N hnine) (hEcard ▸ hTL)

end CFSG.CGT.Timmesfeld75
