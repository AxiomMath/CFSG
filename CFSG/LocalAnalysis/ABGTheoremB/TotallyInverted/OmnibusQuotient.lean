module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusSylow
public import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Omnibus

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

@[expose] def Centralizing (σ : Setting G) (H : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, Y ≤ H → Odd (Nat.card Y) → σ.T ≤ Subgroup.normalizer (Y : Set G) →
    ∃ t ∈ σ.T, t ≠ 1 ∧ ∀ y ∈ Y, y * t * y⁻¹ * t⁻¹ ∈ oddCoreIn H

@[expose] def Conjugate (σ : Setting G) (H : Subgroup G) (r : ℕ) : Prop :=
  ∀ X ∈ maximals (liftedSignalizers σ H r), ∀ X' ∈ maximals (liftedSignalizers σ H r),
    ∃ m ∈ H ⊓ Subgroup.normalizer (σ.T : Set G), conjSub m X' = X

section Lifted

theorem odd_card_of_mem_liftedSignalizers (Δ : Data σ r) {H X : Subgroup G}
    (hX : X ∈ liftedSignalizers σ H r) : Odd (Nat.card X) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨hOX, hXH, hXr, -, -⟩ := hX
  set O : Subgroup G := oddCoreIn H with hOdef
  have hnormal : (O.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr
      (hXH.trans (le_normalizer_oddCoreIn H))
  have hq : IsPGroup r (X ⧸ O.subgroupOf X) := by
    intro g
    induction g using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨k, hk⟩ := hXr x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hq
  have h1 := Subgroup.relIndex_mul_card O X
  rw [inf_eq_left.mpr hOX, Subgroup.relIndex, Subgroup.index_eq_card, hn] at h1
  rw [← h1]
  exact ((Δ.prime.odd_of_ne_two Δ.ne_two).pow).mul (odd_card_oddCoreIn H)

theorem oddCoreIn_sup_mem_liftedSignalizers (hσ : σ.IsValid) (Δ : Data σ r) {H U : Subgroup G}
    (hCH : σ.C ≤ H) (hU : U ∈ signalizersPerm H σ.T σ.C r) :
    oddCoreIn H ⊔ U ∈ liftedSignalizers σ H r := by
  obtain ⟨-, hTY, hperm⟩ := oddCoreIn_sup_props hσ Δ hCH hU
  obtain ⟨⟨hUH, hUp, -, -⟩, -⟩ := hU
  refine ⟨le_sup_left, sup_le (oddCoreIn_le H) hUH, ?_, hTY, hperm⟩
  intro g hg
  have hUO : U ≤ Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
    hUH.trans (le_normalizer_oddCoreIn H)
  have hg' : g ∈ ((oddCoreIn H ⊔ U : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hUO] at hg'
  obtain ⟨o, ho, u, hu, rfl⟩ := hg'
  obtain ⟨k, hk⟩ := hUp ⟨u, hu⟩
  have hk' : u ^ r ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have hmem : ∀ j : ℕ, ∃ o' ∈ oddCoreIn H, (o * u) ^ j = o' * u ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨o', ho', he⟩ := ih
      refine ⟨o' * (u ^ j * o * (u ^ j)⁻¹), Subgroup.mul_mem _ ho'
        ((Subgroup.mem_normalizer_iff.mp (hUO (Subgroup.pow_mem _ hu j)) o).mp ho), ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨o', ho', he⟩ := hmem (r ^ k)
  change (o * u) ^ r ^ k ∈ oddCoreIn H
  rw [he, hk', mul_one]
  exact ho'

theorem eq_oddCoreIn_sup_of_mem_liftedSignalizers (hσ : σ.IsValid) (Δ : Data σ r)
    (hN : ABG_II_4_11_Input Δ) {H U X : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) (hX : X ∈ liftedSignalizers σ H r)
    (hUX : U ≤ X) : X = oddCoreIn H ⊔ U := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hXodd := odd_card_of_mem_liftedSignalizers Δ hX
  obtain ⟨hOX, hXH, hXr, hTX, hXperm⟩ := hX
  have hsyl : IsSylowOf r U X := (isSylowOf_sup_of_le hσ Δ hN hCH hXH hXodd hTX hXperm hU
    hUX).of_le hUX le_sup_left
  set O : Subgroup G := oddCoreIn H with hOdef
  have hOUX : O ⊔ U ≤ X := sup_le hOX hUX
  apply le_antisymm _ hOUX
  have hnormal : (O.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr
      (hXH.trans (le_normalizer_oddCoreIn H))
  have hq : IsPGroup r (X ⧸ O.subgroupOf X) := by
    intro g
    induction g using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨k, hk⟩ := hXr x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hq
  have hOidx : O.relIndex X = r ^ n := by rw [Subgroup.relIndex, Subgroup.index_eq_card, hn]
  have h1 : (O ⊔ U).relIndex X ∣ r ^ n := by
    rw [← hOidx, ← Subgroup.relIndex_mul_relIndex O (O ⊔ U) X le_sup_left hOUX]
    exact dvd_mul_left _ _
  have h2 : (O ⊔ U).relIndex X ∣ U.relIndex X := by
    rw [← Subgroup.relIndex_mul_relIndex U (O ⊔ U) X le_sup_right hOUX]
    exact dvd_mul_left _ _
  obtain ⟨-, -, hUidx⟩ := isSylowOf_iff.mp hsyl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Δ.prime).mp h1
  have hj0 : j = 0 := by
    by_contra hj0
    apply hUidx
    rw [hj] at h2
    exact (dvd_pow_self r hj0).trans h2
  have h1' : (O ⊔ U).relIndex X = 1 := by rw [hj, hj0, pow_zero]
  exact Subgroup.relIndex_eq_one.mp h1'

theorem oddCoreIn_sup_mem_maximals (hσ : σ.IsValid) (Δ : Data σ r) (hN : ABG_II_4_11_Input Δ)
    {H U : Subgroup G} (hCH : σ.C ≤ H) (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) :
    oddCoreIn H ⊔ U ∈ maximals (liftedSignalizers σ H r) :=
  ⟨oddCoreIn_sup_mem_liftedSignalizers hσ Δ hCH hU.1, fun _ hX hle =>
    eq_oddCoreIn_sup_of_mem_liftedSignalizers hσ Δ hN hCH hU hX (le_sup_right.trans hle)⟩

end Lifted

section Trivial

theorem centralizing_conjugate_of_le_oddCoreIn (hσ : σ.IsValid) (Δ : Data σ r)
    {H : Subgroup G} (hCH : σ.C ≤ H)
    (h : ∀ Y : Subgroup G, Y ≤ H → Odd (Nat.card Y) → σ.T ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ oddCoreIn H) :
    Centralizing σ H ∧ Conjugate σ H r := by
  refine ⟨fun Y hYH hY hTY => ⟨σ.x, σ.x_mem_T, x_ne_one hσ, fun y hy => ?_⟩, ?_⟩
  · have hyO : y ∈ oddCoreIn H := h Y hYH hY hTY hy
    have hxH : σ.x ∈ H := hCH ((σ.T_le_C hσ) σ.x_mem_T)
    have : σ.x * y⁻¹ * σ.x⁻¹ ∈ oddCoreIn H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H hxH) _).mp
        (Subgroup.inv_mem _ hyO)
    rw [show y * σ.x * y⁻¹ * σ.x⁻¹ = y * (σ.x * y⁻¹ * σ.x⁻¹) by group]
    exact Subgroup.mul_mem _ hyO this
  · have heq : ∀ X ∈ maximals (liftedSignalizers σ H r), X = oddCoreIn H := by
      intro X hX
      exact le_antisymm (h X hX.1.2.1 (odd_card_of_mem_liftedSignalizers Δ hX.1) hX.1.2.2.2.1)
        hX.1.1
    intro X hX X' hX'
    refine ⟨1, ⟨H.one_mem, Subgroup.one_mem _⟩, ?_⟩
    rw [conjSub_one, heq X hX, heq X' hX']

end Trivial

section Transfer

variable {m : G}

omit [Finite G] in
theorem conjSub_C (hm : m ∈ Subgroup.normalizer (σ.T : Set G)) : conjSub m σ.C = σ.C :=
  conjSub_eq_self (normalizer_T_le_M hm)

theorem conjSub_mem_liftedSignalizers (hm : m ∈ Subgroup.normalizer (σ.T : Set G))
    {H X : Subgroup G} (hX : X ∈ liftedSignalizers σ H r) :
    conjSub m X ∈ liftedSignalizers σ (conjSub m H) r := by
  obtain ⟨hOX, hXH, hXr, hTX, hXperm⟩ := hX
  refine ⟨?_, conjSub_mono hXH, ?_, le_normalizer_conjSub hTX hm,
    conjSub_mul_comm (normalizer_T_le_M hm) hXperm⟩
  · rw [oddCoreIn_conjSub]
    exact conjSub_mono hOX
  · intro g hg
    rw [mem_conjSub] at hg
    obtain ⟨k, hk⟩ := hXr _ hg
    refine ⟨k, ?_⟩
    have hpow : (m⁻¹ * g * m) ^ r ^ k = m⁻¹ * g ^ r ^ k * m := by
      rw [show m⁻¹ * g * m = m⁻¹ * g * m⁻¹⁻¹ by group, conj_pow]
      group
    rw [oddCoreIn_conjSub, mem_conjSub, ← hpow]
    exact hk

theorem conjSub_mem_maximals_liftedSignalizers (hm : m ∈ Subgroup.normalizer (σ.T : Set G))
    {H X : Subgroup G} (hX : X ∈ maximals (liftedSignalizers σ H r)) :
    conjSub m X ∈ maximals (liftedSignalizers σ (conjSub m H) r) := by
  refine ⟨conjSub_mem_liftedSignalizers hm hX.1, fun Z hZ hle => ?_⟩
  have hm' : m⁻¹ ∈ Subgroup.normalizer (σ.T : Set G) := Subgroup.inv_mem _ hm
  have hZ' := conjSub_mem_liftedSignalizers hm' hZ
  rw [conjSub_inv_conjSub] at hZ'
  have hXZ : X ≤ conjSub m⁻¹ Z := by
    rw [← conjSub_le_conjSub_iff (g := m), conjSub_conjSub_inv]
    exact hle
  have := hX.2 _ hZ' hXZ
  rw [← this, conjSub_conjSub_inv]

theorem centralizing_of_conjSub (hm : m ∈ Subgroup.normalizer (σ.T : Set G))
    {H : Subgroup G} (h : Centralizing σ (conjSub m H)) : Centralizing σ H := by
  intro Y hYH hY hTY
  obtain ⟨t', ht', ht'1, hY'⟩ := h (conjSub m Y) (conjSub_mono hYH)
    (by rw [card_conjSub]; exact hY) (le_normalizer_conjSub hTY hm)
  have hm' : m⁻¹ ∈ Subgroup.normalizer (σ.T : Set G) := Subgroup.inv_mem _ hm
  refine ⟨m⁻¹ * t' * m, by simpa using (Subgroup.mem_normalizer_iff.mp hm' t').mp ht', ?_, ?_⟩
  · intro h1
    apply ht'1
    have : t' = m * (m⁻¹ * t' * m) * m⁻¹ := by group
    rw [this, h1]
    group
  · intro y hy
    have := hY' (m * y * m⁻¹) (conj_mem_conjSub hy)
    rw [oddCoreIn_conjSub, mem_conjSub] at this
    rw [show y * (m⁻¹ * t' * m) * y⁻¹ * (m⁻¹ * t' * m)⁻¹ =
      m⁻¹ * (m * y * m⁻¹ * t' * (m * y * m⁻¹)⁻¹ * t'⁻¹) * m by group]
    exact this

theorem conjugate_of_conjSub (hm : m ∈ Subgroup.normalizer (σ.T : Set G)) {H : Subgroup G}
    (h : Conjugate σ (conjSub m H) r) : Conjugate σ H r := by
  intro X hX X' hX'
  obtain ⟨m', ⟨hm'H, hm'T⟩, hm'⟩ := h _ (conjSub_mem_maximals_liftedSignalizers hm hX) _
    (conjSub_mem_maximals_liftedSignalizers hm hX')
  refine ⟨m⁻¹ * m' * m, ⟨?_, ?_⟩, ?_⟩
  · exact mem_conjSub.mp hm'H
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hm'T) hm
  · rw [conjSub_mul, conjSub_mul, hm', conjSub_inv_conjSub]

end Transfer

section QGroup

theorem centralizing_of_isQGroup (hσ : σ.IsValid) (Δ : Data σ r) (hQ : ABG_II_3_1_Input G)
    {H : Subgroup G} (hCH : σ.C ≤ H) (hHQ : IsQGroup H) : Centralizing σ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCH
  obtain ⟨Q, hTQ⟩ := ((T_isPGroup hσ).comap_subtype (K := H)).exists_le_sylow
  set S₁ : Subgroup G := (Q : Subgroup H).map H.subtype with hS₁def
  have hS₁ : IsSylowOf 2 S₁ H := ⟨Q, rfl⟩
  have hTS₁ : σ.T ≤ S₁ := fun t ht => ⟨⟨t, hTH ht⟩, hTQ ht, rfl⟩
  obtain ⟨z, hzS, hzZ, hz2⟩ : ∃ z ∈ S₁, z ∈ Subgroup.centralizer (S₁ : Set G) ∧
      orderOf z = 2 := by
    have hS₁p : IsPGroup 2 S₁ := hS₁.isPGroup
    have : Nontrivial S₁ := ⟨⟨1, ⟨σ.x, hTS₁ σ.x_mem_T⟩, fun h => x_ne_one hσ
      (congrArg Subtype.val h).symm⟩⟩
    have hZ := hS₁p.center_nontrivial
    have hZp : IsPGroup 2 (Subgroup.center S₁) := hS₁p.to_subgroup _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hn
    have h2 : 2 ∣ Nat.card (Subgroup.center S₁) := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2 h2
    refine ⟨((z₀ : S₁) : G), (z₀ : S₁).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have := Subgroup.mem_center_iff.mp z₀.2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hzC : z ∈ σ.C := by
    rw [Setting.C, Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp hzZ) t (hTS₁ ht)
  have hzT : z ∈ σ.T := mem_T_of_mem_C_of_sq Δ hzC (by rw [← hz2]; exact pow_orderOf_eq_one z)
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hdec := hQ H hHQ S₁ hS₁
  intro Y hYH hY hTY
  refine ⟨z, hzT, hz1, fun y hy => ?_⟩
  have hzH : z ∈ H := hTH hzT
  have hHO : H ≤ Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
    le_normalizer_oddCoreIn H
  have hy' : y ∈ ((oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer (centerOf S₁ : Set G)) :
      Subgroup G) : Set G) := hdec (hYH hy)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hHO)] at hy'
  obtain ⟨o, ho, c, hc, rfl⟩ := hy'
  have hcz : c * z = z * c :=
    (Subgroup.mem_centralizer_iff.mp hc.2) z ⟨hzS, hzZ⟩ |>.symm
  have hzo : z * o⁻¹ * z⁻¹ ∈ oddCoreIn H :=
    (Subgroup.mem_normalizer_iff.mp (hHO hzH) _).mp (Subgroup.inv_mem _ ho)
  change o * c * z * (o * c)⁻¹ * z⁻¹ ∈ oddCoreIn H
  rw [show o * c * z * (o * c)⁻¹ * z⁻¹ = o * (c * z) * c⁻¹ * o⁻¹ * z⁻¹ by group, hcz,
    show o * (z * c) * c⁻¹ * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) by group]
  exact Subgroup.mul_mem _ ho hzo

end QGroup

section Ambient

omit [Finite G] in
theorem le_oddCoreIn_of_subgroupOf {H Y : Subgroup G} (hYH : Y ≤ H)
    (h : Y.subgroupOf H ≤ CFSG.oddCore H) : Y ≤ oddCoreIn H :=
  fun y hy => ⟨⟨y, hYH hy⟩, h hy, rfl⟩

omit [Finite G] in
theorem isKleinFour_subgroupOf {T H : Subgroup G} (hTH : T ≤ H) (hT : IsKleinFour T) :
    IsKleinFour (T.subgroupOf H) :=
  ⟨by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv]; exact hT.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTH)]
       exact hT.exponent_two⟩

omit [Finite G] in
theorem subgroupOf_le_normalizer {H A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup H) : Set H) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (h ha) b

omit [Finite G] in
theorem odd_card_subgroupOf {H Y : Subgroup G} (hYH : Y ≤ H) (hY : Odd (Nat.card Y)) :
    Odd (Nat.card (Y.subgroupOf H)) := by
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]

theorem oddCoreIn_top_eq_bot (hσ : σ.IsValid) : oddCoreIn (⊤ : Subgroup G) = ⊥ := by
  have hsimple := hσ.simple
  have hG : CFSG.oddCore G = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exfalso
      have hodd := odd_card_oddCore G
      rw [h, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card G := hσ.x_order ▸ orderOf_dvd_natCard σ.x
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have h := oddCore_map_mulEquiv' (Subgroup.topEquiv (G := G))
  rw [hG, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv (G := G)).injective] at h
  rw [oddCoreIn, h, Subgroup.map_bot]

end Ambient

section Wreathed

theorem hasWreathedSylow_of_height (hσ : σ.IsValid) (hh : σ.height ≠ 1) :
    HasWreathedSylow G σ.height := by
  rcases hσ.sylow with ⟨h1, -⟩ | h
  · exact absurd h1 hh
  · exact h

theorem D_eq_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) : σ.D = σ.S :=
  inf_eq_left.mpr (hσ.T_normal hh)

omit [Finite G] in
theorem F₀_le_S : σ.F₀ ≤ σ.S := inf_le_left.trans σ.D_le_S

theorem conj_x_of_mem_S (hσ : σ.IsValid) {s : G} (hs : s ∈ (σ.S : Subgroup G)) :
    s * σ.x * s⁻¹ = σ.x := by
  rw [show s * σ.x = σ.x * s from (Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) s hs]
  group

theorem mem_C_iff_of_mem_S (hσ : σ.IsValid) {s : G} (hs : s ∈ (σ.S : Subgroup G)) :
    s ∈ σ.C ↔ s * σ.x₂ * s⁻¹ = σ.x₂ := by
  rw [← Ns_inf_Ns hσ (show (0 : Fin 3) ≠ 1 by decide), Subgroup.mem_inf, mem_Ns_iff, mem_Ns_iff,
    xs_zero, xs_one]
  constructor
  · rintro ⟨-, h⟩
    rw [← h]
    group
  · intro h
    refine ⟨?_, ?_⟩
    · have := conj_x_of_mem_S hσ hs
      calc σ.x * s = s * σ.x * s⁻¹ * s := by rw [this]
        _ = s * σ.x := by group
    · calc σ.x₂ * s = s * σ.x₂ * s⁻¹ * s := by rw [h]
        _ = s * σ.x₂ := by group

theorem conj_x₂_of_mem_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) {s : G}
    (hs : s ∈ (σ.S : Subgroup G)) : s * σ.x₂ * s⁻¹ = σ.x₂ ∨ s * σ.x₂ * s⁻¹ = σ.x * σ.x₂ := by
  have hsT : s ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) := hσ.T_normal hh hs
  obtain ⟨j, hj⟩ := exists_conj_xs_eq hσ hsT 1
  rw [xs_one] at hj
  fin_cases j
  · exfalso
    apply hσ.x_ne_x₂
    have h1 : σ.x₂ = s⁻¹ * σ.x * s := by
      simp only [Fin.zero_eta, xs_zero] at hj
      rw [← hj]
      group
    rw [h1, show s⁻¹ * σ.x * s = s⁻¹ * σ.x * s⁻¹⁻¹ by group,
      conj_x_of_mem_S hσ (Subgroup.inv_mem _ hs)]
  · exact Or.inl hj
  · exact Or.inr hj

theorem relIndex_F₀_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) : σ.F₀.relIndex σ.S = 2 := by
  have hF₀ : σ.F₀ = (σ.S : Subgroup G) ⊓ σ.C := by rw [Setting.F₀, D_eq_S hσ hh]; rfl
  obtain ⟨s₀, hs₀S, hs₀C⟩ : ∃ s₀ ∈ (σ.S : Subgroup G), s₀ ∉ σ.C := by
    by_contra hcon
    push Not at hcon
    have hz : σ.x₂ ∈ centerOf (σ.S : Subgroup G) := by
      refine Subgroup.mem_inf.mpr ⟨hσ.x₂_mem, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (comm_of_mem_C (hcon s hs) σ.x₂_mem_T).symm
    exact hσ.x_ne_x₂ (hσ.center_involution _ hz hσ.x₂_order).symm
  have hs₀ : s₀ * σ.x₂ * s₀⁻¹ = σ.x * σ.x₂ := by
    rcases conj_x₂_of_mem_S hσ hh hs₀S with h | h
    · exact absurd ((mem_C_iff_of_mem_S hσ hs₀S).mpr h) hs₀C
    · exact h
  have hx₂ne : σ.x * σ.x₂ ≠ σ.x₂ := fun h => x_ne_one hσ (by simpa using h)
  have key : ∀ g : (σ.S : Subgroup G),
      g ∈ σ.F₀.subgroupOf σ.S ↔ (g : G) * σ.x₂ * (g : G)⁻¹ = σ.x₂ := by
    intro g
    rw [Subgroup.mem_subgroupOf, hF₀, Subgroup.mem_inf, mem_C_iff_of_mem_S hσ g.2]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  have hxx : σ.x * σ.x = 1 := by
    have := T_isKleinFour hσ
    exact kleinFour_mul_self σ.x_mem_T
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨s₀, hs₀S⟩, fun b => ?_⟩
  rw [key, key]
  have hcalc : ((b * ⟨s₀, hs₀S⟩ : (σ.S : Subgroup G)) : G) * σ.x₂ *
      ((b * ⟨s₀, hs₀S⟩ : (σ.S : Subgroup G)) : G)⁻¹ = σ.x * ((b : G) * σ.x₂ * (b : G)⁻¹) := by
    rw [Subgroup.coe_mul, show (b : G) * s₀ * σ.x₂ * ((b : G) * s₀)⁻¹ =
      (b : G) * (s₀ * σ.x₂ * s₀⁻¹) * (b : G)⁻¹ by group, hs₀,
      show (b : G) * (σ.x * σ.x₂) * (b : G)⁻¹ =
      ((b : G) * σ.x * (b : G)⁻¹) * ((b : G) * σ.x₂ * (b : G)⁻¹) by group,
      conj_x_of_mem_S hσ b.2]
  rw [hcalc]
  rcases conj_x₂_of_mem_S hσ hh b.2 with h | h
  · rw [h]
    exact Or.inr ⟨rfl, hx₂ne⟩
  · rw [h, ← mul_assoc, hxx, one_mul]
    exact Or.inl ⟨rfl, hx₂ne⟩

theorem card_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) :
    Nat.card (σ.S : Subgroup G) = 2 * 4 ^ σ.height := by
  obtain ⟨e⟩ := (hasWreathedSylow_of_height hσ hh).2 σ.S
  rw [Nat.card_congr e.toEquiv, CFSG.Wreathed.card_wreath, ← pow_mul, mul_comm σ.height 2,
    pow_mul]
  norm_num

theorem card_F₀ (hσ : σ.IsValid) (hh : σ.height ≠ 1) : Nat.card σ.F₀ = 4 ^ σ.height := by
  have h := Subgroup.relIndex_mul_card σ.F₀ σ.S
  rw [relIndex_F₀_S hσ hh, inf_eq_left.mpr F₀_le_S, card_S hσ hh] at h
  omega

theorem nonempty_baseSubgroup_mulEquiv (m : ℕ) :
    Nonempty (CFSG.Wreathed.baseSubgroup m ≃*
      Multiplicative (ZMod m) × Multiplicative (ZMod m)) := by
  refine ⟨MulEquiv.mk' ((CFSG.Wreathed.baseCoordinateEquiv m).trans
    (Multiplicative.ofAdd.prodCongr Multiplicative.ofAdd)) fun x y => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (CFSG.Wreathed.baseCoordinateEquiv m).symm.surjective x
  obtain ⟨⟨c, d⟩, rfl⟩ := (CFSG.Wreathed.baseCoordinateEquiv m).symm.surjective y
  have hmul : (CFSG.Wreathed.baseCoordinateEquiv m).symm (a, b) *
      (CFSG.Wreathed.baseCoordinateEquiv m).symm (c, d) =
      (CFSG.Wreathed.baseCoordinateEquiv m).symm (a + c, b + d) :=
    Subtype.ext (CFSG.Wreathed.element_base_mul m a b c d 0)
  simp only [Equiv.trans_apply, hmul, Equiv.apply_symm_apply]
  rfl

theorem nonempty_F₀_mulEquiv (hσ : σ.IsValid) (Δ : Data σ r) (hh : σ.height ≠ 1) :
    Nonempty (σ.F₀ ≃* CFSG.RankTwoShapes.HomocyclicGroup σ.height) := by
  have hW := hasWreathedSylow_of_height hσ hh
  have hn : 2 ≤ σ.height := hW.1
  obtain ⟨e⟩ := hW.2 σ.S
  have : IsMulCommutative σ.F₀ := ⟨⟨fun a b => Subtype.ext (Δ.F₀_abelian _ a.2 _ b.2)⟩⟩
  have hbase : (σ.F₀.subgroupOf σ.S).map e.toMonoidHom =
      CFSG.Wreathed.baseSubgroup (2 ^ σ.height) := by
    have h2n : 2 < 2 ^ σ.height := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ σ.height := Nat.pow_le_pow_right (by norm_num) hn
    apply CFSG.Wreathed.unique_abelian_index_two (2 ^ σ.height) h2n
    · have := Subgroup.subgroupOf_isMulCommutative (σ.S : Subgroup G) σ.F₀
      exact Subgroup.map_isMulCommutative _ _
    · have hc : Nat.card ((σ.F₀.subgroupOf σ.S).map e.toMonoidHom) = 4 ^ σ.height := by
        rw [Subgroup.card_map_of_injective e.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe F₀_le_S).toEquiv, card_F₀ hσ hh]
      have h := ((σ.F₀.subgroupOf σ.S).map e.toMonoidHom).card_mul_index
      rw [hc, CFSG.Wreathed.card_wreath, ← pow_mul, mul_comm σ.height 2, pow_mul,
        show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm] at h
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  exact ⟨(Subgroup.subgroupOfEquivOfLe F₀_le_S).symm.trans
    (((σ.F₀.subgroupOf σ.S).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hbase).trans
        (nonempty_baseSubgroup_mulEquiv (2 ^ σ.height)).some))⟩

theorem not_hasDihedralSylowTwo_of_hasWreathedSylow {K : Type} [Group K] [Finite K] {n : ℕ}
    (hW : HasWreathedSylow K n) : ¬ CFSG.GorensteinWalter.HasDihedralSylowTwo K := by
  intro hD
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨e₁⟩ := hW.2 P
  obtain ⟨m, -, ⟨e₂⟩⟩ := hD P
  let e : CFSG.Wreathed.Wreath (2 ^ n) ≃* DihedralGroup (2 ^ m) := e₁.symm.trans e₂
  have hcard := Nat.card_congr e.toEquiv
  rw [CFSG.Wreathed.card_wreath, DihedralGroup.nat_card, ← pow_mul,
    show n * 2 = 2 * n by ring] at hcard
  have hm : m = 2 * n :=
    Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_left (by norm_num) hcard).symm
  have hord : orderOf (e.symm (DihedralGroup.r 1)) = 2 ^ m := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hdvd : 2 ^ m ∣ 2 ^ (n + 1) := by
    rw [← hord, pow_succ']
    exact orderOf_dvd_of_pow_eq_one (CFSG.Wreathed.element_pow_twice_modulus _ _)
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  have := hW.1
  omega

theorem hasWreathedSylow_of_le (hσ : σ.IsValid) (hh : σ.height ≠ 1) {H : Subgroup G}
    (hSH : (σ.S : Subgroup G) ≤ H) : HasWreathedSylow H σ.height := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW := hasWreathedSylow_of_height hσ hh
  refine ⟨hW.1, fun P => ?_⟩
  have hS' : IsPGroup 2 ((σ.S : Subgroup G).subgroupOf H) := σ.S.isPGroup'.comap_subtype
  have hidx : ¬ 2 ∣ ((σ.S : Subgroup G).subgroupOf H).index := by
    intro h2
    apply σ.S.not_dvd_index
    rw [← Subgroup.relIndex_mul_index hSH]
    exact h2.mul_right _
  set S' : Sylow 2 H := hS'.toSylow hidx with hS'def
  have hcardP : Nat.card (P : Subgroup H) = Nat.card (σ.S : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S', hS'def,
      IsPGroup.toSylow_coe, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]
  set P' : Subgroup G := (P : Subgroup H).map H.subtype with hP'def
  have hcardP' : Nat.card P' = 2 ^ (Nat.card G).factorization 2 := by
    rw [hP'def, Subgroup.card_map_of_injective H.subtype_injective, hcardP,
      Sylow.card_eq_multiplicity]
  obtain ⟨e⟩ := hW.2 (Sylow.ofCard P' hcardP')
  exact ⟨((P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans e⟩

theorem le_oddCoreIn_of_isDGroup (hσ : σ.IsValid) (hh : σ.height ≠ 1) {H : Subgroup G}
    (hSH : (σ.S : Subgroup G) ≤ H) (hD : IsDGroup H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hY : Odd (Nat.card Y)) (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ oddCoreIn H := by
  have hW := hasWreathedSylow_of_le hσ hh hSH
  have hTH : σ.T ≤ H := (σ.T_le_S hσ).trans hSH
  rcases hD with ⟨hdih, -⟩ | ⟨K, hK⟩
  · exact absurd hdih (not_hasDihedralSylowTwo_of_hasWreathedSylow hW)
  · exact le_oddCoreIn_of_subgroupOf hYH
      (CFSG.ABGDGroups.wreathed_dGroup_odd_four_invariant_le_oddCore hK hW
        (isKleinFour_subgroupOf hTH (T_isKleinFour hσ)) (odd_card_subgroupOf hYH hY)
        (subgroupOf_le_normalizer hTY))

theorem le_oddCoreIn_of_isSylowOf_F₀ (hσ : σ.IsValid) (Δ : Data σ r) (hh : σ.height ≠ 1)
    {H : Subgroup G} (hF : IsSylowOf 2 σ.F₀ H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hY : Odd (Nat.card Y)) (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ oddCoreIn H := by
  obtain ⟨Q, hQ⟩ := hF
  have hTH : σ.T ≤ H := (T_le_F₀ hσ).trans (hQ ▸ Subgroup.map_subtype_le _)
  obtain ⟨eF⟩ := nonempty_F₀_mulEquiv hσ Δ hh
  let e : (Q : Subgroup H) ≃* CFSG.RankTwoShapes.HomocyclicGroup σ.height :=
    (((Q : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ)).trans eF
  exact le_oddCoreIn_of_subgroupOf hYH
    (CFSG.ABGDGroups.homocyclic_sylow_odd_four_invariant_le_oddCore Q
      (hasWreathedSylow_of_height hσ hh).1 e
      (isKleinFour_subgroupOf hTH (T_isKleinFour hσ)) (odd_card_subgroupOf hYH hY)
      (subgroupOf_le_normalizer hTY))

theorem exists_conj_eq_S (hσ : σ.IsValid) (Δ : Data σ r) (hh : σ.height ≠ 1) {S₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁) (hFS₁ : σ.F₀ ≤ S₁) (hne : S₁ ≠ σ.F₀) :
    ∃ m ∈ Subgroup.normalizer (σ.T : Set G), conjSub m S₁ = σ.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hS₁.exists_le_sylow
  have hcardS' : Nat.card (S' : Subgroup G) = 2 * Nat.card σ.F₀ := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity σ.S, card_S hσ hh,
      card_F₀ hσ hh]
  have hidx : σ.F₀.relIndex S₁ = 2 := by
    have h1 := Subgroup.relIndex_mul_card σ.F₀ S₁
    rw [inf_eq_left.mpr hFS₁] at h1
    have h2 : Nat.card S₁ ≤ 2 * Nat.card σ.F₀ := hcardS' ▸ Subgroup.card_le_of_le hS'
    have h3 : σ.F₀.relIndex S₁ ≠ 1 := fun h =>
      hne (le_antisymm (Subgroup.relIndex_eq_one.mp h) hFS₁)
    have h4 : 0 < Nat.card σ.F₀ := Nat.card_pos
    have h5 : 0 < σ.F₀.relIndex S₁ := by
      rcases Nat.eq_zero_or_pos (σ.F₀.relIndex S₁) with h | h
      · rw [h, zero_mul] at h1
        exact absurd h1.symm Nat.card_pos.ne'
      · exact h
    have h6 : σ.F₀.relIndex S₁ ≤ 2 := by
      by_contra h7
      push Not at h7
      have : 3 * Nat.card σ.F₀ ≤ σ.F₀.relIndex S₁ * Nat.card σ.F₀ :=
        Nat.mul_le_mul_right _ h7
      omega
    omega
  have hcardS₁ : Nat.card S₁ = Nat.card (S' : Subgroup G) := by
    have h1 := Subgroup.relIndex_mul_card σ.F₀ S₁
    rw [inf_eq_left.mpr hFS₁, hidx] at h1
    rw [← h1, hcardS']
  have hS₁S' : S₁ = S' := Subgroup.eq_of_le_of_card_ge hS' hcardS₁.ge
  have hnormal : (σ.F₀.subgroupOf S₁).Normal := Subgroup.normal_of_index_eq_two hidx
  have hS₁F : S₁ ≤ Subgroup.normalizer (σ.F₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFS₁).mp hnormal
  have hS₁T : S₁ ≤ Subgroup.normalizer (σ.T : Set G) := by
    intro s hs
    apply mem_normalizer_of_conj_le
    intro t ht
    have h1 : s * t * s⁻¹ ∈ σ.F₀ :=
      (Subgroup.mem_normalizer_iff.mp (hS₁F hs) t).mp (T_le_F₀ hσ ht)
    apply Δ.F₀_omega _ h1
    have := T_isKleinFour hσ
    rw [show (s * t * s⁻¹) ^ 2 = s * (t * t) * s⁻¹ by rw [pow_two]; group,
      kleinFour_mul_self ht]
    group
  have hsyl : ∀ {P : Sylow 2 G} {Q : Subgroup G}, Q = P →
      Q ≤ Subgroup.normalizer (σ.T : Set G) →
      IsSylowOf 2 Q (Subgroup.normalizer (σ.T : Set G)) := by
    rintro P Q rfl hQ
    refine isSylowOf_iff.mpr ⟨hQ, P.isPGroup', fun h2 => P.not_dvd_index ?_⟩
    rw [← Subgroup.relIndex_mul_index hQ]
    exact h2.mul_right _
  obtain ⟨m, hm, hmS⟩ := exists_conjSub_eq_of_isSylowOf (hsyl hS₁S' hS₁T)
    (hsyl rfl (hσ.T_normal hh))
  exact ⟨m, hm, hmS⟩

end Wreathed

section Structure

theorem centralizing_conjugate_of_fusion (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) (hI : OmnibusInputs Δ) {H : Subgroup G} (hCH : σ.C ≤ H)
    (hO : oddCoreIn H ≠ ⊥) (hDH : σ.D ≤ H ∨ σ.height = 1) :
    Centralizing σ H ∧ Conjugate σ H r := by
  have hHtop : H ≠ ⊤ := by
    rintro rfl
    exact hO (oddCoreIn_top_eq_bot hσ)
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCH
  have hcover : ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      (H : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) := fun g hg =>
    ⟨g, hCH hg.1, 1, Subgroup.one_mem _, mul_one g⟩
  rcases hF.fusion_cases H hHtop hTH hDH with hQD | hQ | hD | hC
  · exact absurd hQD (hF.not_qd_of_cover H hTH hO hcover)
  · exact ⟨centralizing_of_isQGroup hσ Δ hI.qCentralizer hCH hQ,
      hI.qConjugacy H hCH hO hQ⟩
  · by_cases hh : σ.height = 1
    · exact ⟨fun Y hYH hY hTY =>
        hI.dCentralizer hh H hD σ.T hTH (T_isKleinFour hσ) Y hYH hY hTY,
        hI.dConjugacy hh H hCH hO hD⟩
    · have hSH : (σ.S : Subgroup G) ≤ H := by
        rw [← D_eq_S hσ hh]
        exact hDH.resolve_right hh
      exact centralizing_conjugate_of_le_oddCoreIn hσ Δ hCH fun Y hYH hY hTY =>
        le_oddCoreIn_of_isDGroup hσ hh hSH hD hYH hY hTY
  · exact centralizing_conjugate_of_le_oddCoreIn hσ Δ hCH fun Y hYH hY _ =>
      le_oddCoreIn_of_hasNormalPComplement hC hYH hY

theorem centralizing_conjugate (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hI : OmnibusInputs Δ) {H : Subgroup G} (hCH : σ.C ≤ H) (hO : oddCoreIn H ≠ ⊥) :
    Centralizing σ H ∧ Conjugate σ H r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hDH : σ.D ≤ H ∨ σ.height = 1
  · exact centralizing_conjugate_of_fusion hσ hF Δ hI hCH hO hDH
  have hh : σ.height ≠ 1 := fun h => hDH (Or.inr h)
  have hFH : σ.F₀ ≤ H := F₀_le_C.trans hCH
  obtain ⟨Q, hFQ⟩ := ((Δ.F₀_sylow.isPGroup).comap_subtype (K := H)).exists_le_sylow
  set S₁ : Subgroup G := (Q : Subgroup H).map H.subtype with hS₁def
  have hS₁ : IsSylowOf 2 S₁ H := ⟨Q, rfl⟩
  have hFS₁ : σ.F₀ ≤ S₁ := fun f hf => ⟨⟨f, hFH hf⟩, hFQ hf, rfl⟩
  by_cases hS₁F : S₁ = σ.F₀
  · rw [hS₁F] at hS₁
    exact centralizing_conjugate_of_le_oddCoreIn hσ Δ hCH fun Y hYH hY hTY =>
      le_oddCoreIn_of_isSylowOf_F₀ hσ Δ hh hS₁ hYH hY hTY
  obtain ⟨m, hm, hmS⟩ := exists_conj_eq_S hσ Δ hh hS₁.isPGroup hFS₁ hS₁F
  have hCH' : σ.C ≤ conjSub m H := by
    rw [← conjSub_C hm]
    exact conjSub_mono hCH
  have hO' : oddCoreIn (conjSub m H) ≠ ⊥ := by
    rw [oddCoreIn_conjSub, Ne, conjSub_eq_bot_iff]
    exact hO
  have hDH' : σ.D ≤ conjSub m H := by
    rw [D_eq_S hσ hh, ← hmS]
    exact conjSub_mono hS₁.le
  obtain ⟨h1, h2⟩ := centralizing_conjugate_of_fusion hσ hF Δ hI hCH' hO' (Or.inl hDH')
  exact ⟨centralizing_of_conjSub hm h1, conjugate_of_conjSub hm h2⟩

end Structure

end CFSG.ABGTheoremB.TotallyInverted.Omnibus
