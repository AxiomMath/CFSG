module

public import CFSG.GH74.GLS.C3.Layer1.BkP46W
public import CFSG.GH74.GLS.C3.Layer1.BkP46TI

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem aconfigW_five_fix_x [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {y : G} (hyT : y ∈ T) (hyQ : ∃ q ∈ Q, y * q ≠ q * y)
    {H : Subgroup G} (hH2 : IsPGroup 2 ↥H) (hHN : H ≤ normalizer (Q : Set G)) (hyH : y ∈ H) :
    ∀ n ∈ H, n * x * n⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxQ := h.x_mem_Q
  have hx1 := h.x_ne_one
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht =>
    (mem_centralizer_singleton_iff.1 (h.T_le_C ht)).symm
  let ρ : ↥H →* MulAut ↥Q :=
    (Stage1.Thm6.Sec13.actHom Q).comp (Subgroup.inclusion hHN)
  let _inst : MulAction ↥H ↥Q := MulAction.compHom ↥Q ρ
  have hsmul : ∀ (g : ↥H) (q : ↥Q), ((g • q : ↥Q) : G) = (g : G) * (q : G) * (g : G)⁻¹ :=
    fun g q => rfl
  have hmod := IsPGroup.card_modEq_card_fixedPoints hH2 (α := ↥Q)
  have hxF : (⟨x, hxQ⟩ : ↥Q) ∈ MulAction.fixedPoints ↥H ↥Q := by
    by_contra hxF
    have hC := card_inf_centralizer_le_two h.card_Q hyQ
    have hxC : x ∈ Q ⊓ centralizer ({y} : Set G) :=
      ⟨hxQ, mem_centralizer_singleton_iff.2 (hxT y hyT)⟩
    have hFeq : (MulAction.fixedPoints ↥H ↥Q) = {1} := by
      ext q
      constructor
      · intro hq
        have hqy : (⟨y, hyH⟩ : ↥H) • q = q := hq ⟨y, hyH⟩
        have hqy' : y * (q : G) * y⁻¹ = q := by
          have := congrArg Subtype.val hqy
          rwa [hsmul] at this
        have hqC : (q : G) ∈ Q ⊓ centralizer ({y} : Set G) := by
          refine ⟨q.2, mem_centralizer_singleton_iff.2 ?_⟩
          calc (q : G) * y = (y * (q : G) * y⁻¹) * y := by rw [hqy']
            _ = y * q := by group
        rcases eq_one_or_eq_of_card_le_two hC hxC hx1 hqC with h1 | h1
        · exact Set.mem_singleton_iff.2 (Subtype.ext h1)
        · exfalso
          apply hxF
          have : q = ⟨x, hxQ⟩ := Subtype.ext h1
          rw [← this]
          exact hq
      · intro hq
        rw [Set.mem_singleton_iff] at hq
        rw [hq]
        intro g
        exact Subtype.ext (by rw [hsmul]; simp)
    have hcard1 : Nat.card ↥(MulAction.fixedPoints ↥H ↥Q) = 1 := by
      rw [hFeq]
      simp
    rw [hcard1, h.card_Q] at hmod
    have := hmod
    unfold Nat.ModEq at this
    omega
  intro n hn
  have hfix := hxF ⟨n, hn⟩
  have := congrArg Subtype.val hfix
  rwa [hsmul] at this

theorem aconfigW_five_T_sylow [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    IsSylowOf 2 T (normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ⊓ normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyT, hyy, hyR, hTcases, hyQ⟩ := aconfigW_five_y h
  have hCD := aconfigW_five_commDisj h
  set NRQ : Subgroup G := normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ⊓ normalizer (Q : Set G)
    with hNRQ
  have hTN : T ≤ NRQ := by
    intro t ht
    refine ⟨mem_normalizer_of_two_sided (fun w hw => aconfigW_five_R_norm h hCD t ht w hw)
      (fun w hw => ?_), mem_normalizer_of_two_sided (fun w hw => aconfigW_Q_norm h t ht w hw)
      (fun w hw => ?_)⟩
    · simpa using aconfigW_five_R_norm h hCD t⁻¹ (T.inv_mem ht) w hw
    · simpa using aconfigW_Q_norm h t⁻¹ (T.inv_mem ht) w hw
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hTsub : IsPGroup 2 ↥(T.subgroupOf NRQ) := hT2.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hTsub.exists_le_sylow
  have hT₁ : IsSylowOf 2 ((S₁ : Subgroup ↥NRQ).map NRQ.subtype) NRQ := ⟨S₁, rfl⟩
  have hTT₁ : T ≤ (S₁ : Subgroup ↥NRQ).map NRQ.subtype := by
    intro t ht
    exact ⟨⟨t, hTN ht⟩, hS₁ (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hT₁2 := hT₁.isPGroup
  have hT₁N := hT₁.le
  have hfix := aconfigW_five_fix_x h hyT hyQ hT₁2 (hT₁N.trans inf_le_right) (hTT₁ hyT)
  have hT₁C : (S₁ : Subgroup ↥NRQ).map NRQ.subtype ≤ centralizer ({x} : Set G) := by
    intro n hn
    exact mem_centralizer_singleton_iff.2 (by
      have := hfix n hn
      calc n * x = n * x * n⁻¹ * n := by group
        _ = x * n := by rw [this])
  have heq := h.sylowT.eq_of_le hTT₁ hT₁C hT₁2
  rw [heq] at hT₁
  exact hT₁

theorem aconfigW_five_T_le_normalizer_R [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) : T ≤ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) := by
  have hCD := aconfigW_five_commDisj h
  intro t ht
  refine mem_normalizer_of_two_sided (fun w hw => aconfigW_five_R_norm h hCD t ht w hw)
    (fun w hw => ?_)
  simpa using aconfigW_five_R_norm h hCD t⁻¹ (T.inv_mem ht) w hw

theorem aconfigW_five_a_mem_normalizer [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) : a ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) := by
  obtain ⟨y, hyT, hyy, hyR, hTcases, q₀, hq₀, hyq₀⟩ := aconfigW_five_y h
  obtain ⟨p, hp, hyp⟩ := aconfigW_five_y_nontriv h hyT hyR
  have hCy := aconfigW_five_card_centralizer_R h hyT ⟨p, hp, hyp⟩ ⟨q₀, hq₀, hyq₀⟩
  exact aconfigW_five_a_normalizes_R h hTcases hCy

theorem aconfigW_five_A [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    IsPGroup 2 ↥(T ⊔ zpowers a) ∧ T ⊔ zpowers a ≤ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ∧
      Nat.card ↥T < Nat.card ↥(T ⊔ zpowers a) := by
  have hle : T ≤ T ⊔ zpowers a := le_sup_left
  refine ⟨h.sylowS.isPGroup.to_le (sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1)),
    sup_le (aconfigW_five_T_le_normalizer_R h) (zpowers_le.2 (aconfigW_five_a_mem_normalizer h)),
    ?_⟩
  by_contra hcon
  have hcard : Nat.card ↥(T ⊔ zpowers a) ≤ Nat.card ↥T := not_lt.1 hcon
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  exact h.a_mem.2.2.1 (heq ▸ Subgroup.mem_sup_right (mem_zpowers a))

theorem aconfigW_five_card_le_T [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {g : G}
    (hg : g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G)) {B : Subgroup G}
    (hB2 : IsPGroup 2 ↥B) (hBR : B ≤ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G))
    (hBQ : B ≤ normalizer ((conjugate Q g : Subgroup G) : Set G)) :
    Nat.card ↥B ≤ Nat.card ↥T := by
  have hS := aconfigW_five_T_sylow h
  set NRQ : Subgroup G := normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ⊓ normalizer (Q : Set G)
    with hNRQ
  have key : ∀ b ∈ B, ∀ q ∈ Q, (g * b * g⁻¹) * q * (g * b * g⁻¹)⁻¹ ∈ Q := by
    intro b hb q hq
    have hb' := hBQ hb
    have h1 : g⁻¹ * q * g ∈ conjugate Q g := by
      rw [mem_conjugate_iff']
      have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
      rw [e]
      exact hq
    have h2 := (Subgroup.mem_normalizer_iff.1 hb' (g⁻¹ * q * g)).1 h1
    rw [mem_conjugate_iff'] at h2
    have e : g * (b * (g⁻¹ * q * g) * b⁻¹) * g⁻¹ = (g * b * g⁻¹) * q * (g * b * g⁻¹)⁻¹ := by group
    rw [e] at h2
    exact h2
  have hB'2 : IsPGroup 2 ↥(Th2.cj g B) := hB2.map (MulAut.conj g).toMonoidHom
  have hB'N : Th2.cj g B ≤ NRQ := by
    rintro _ ⟨b, hb, rfl⟩
    have hz : (MulAut.conj g).toMonoidHom b = g * b * g⁻¹ := by simp [MulAut.conj_apply]
    rw [hz]
    refine ⟨?_, ?_⟩
    · exact (normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G)).mul_mem
        ((normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G)).mul_mem hg (hBR hb))
        ((normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G)).inv_mem hg)
    · refine mem_normalizer_of_two_sided (fun q hq => key b hb q hq) (fun q hq => ?_)
      have := key b⁻¹ (B.inv_mem hb) q hq
      have e : g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ := by group
      rw [e] at this
      simpa using this
  obtain ⟨k, hk, hkB⟩ := Th2.exists_cj_le_of_isSylowOf hS hB'N hB'2
  have h1 : Nat.card ↥(Th2.cj k (Th2.cj g B)) = Nat.card ↥B := by
    unfold Th2.cj
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← h1]
  exact Subgroup.card_le_of_le hkB

@[expose] def NRConj (R Q : Subgroup G) : Set (Subgroup G) :=
  {Q' | ∃ g ∈ normalizer (R : Set G), Q' = conjugate Q g}

theorem aconfigW_five_TI' [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {g₁ g₂ : G}
    (hg₁ : g₁ ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G))
    (hg₂ : g₂ ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G))
    (hne : conjugate Q g₁ ⊓ conjugate Q g₂ ≠ ⊥) : conjugate Q g₁ = conjugate Q g₂ := by
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hu₁ : g₁ * u * g₁⁻¹ ∈ Q := mem_conjugate_iff'.1 hu.1
  have hu₂ : g₂ * u * g₂⁻¹ ∈ Q := mem_conjugate_iff'.1 hu.2
  have hhN : g₂ * g₁⁻¹ ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) :=
    (normalizer _).mul_mem hg₂ ((normalizer _).inv_mem hg₁)
  have hne' : Q ⊓ conjugate Q (g₂ * g₁⁻¹) ≠ ⊥ := by
    intro hbot
    have hmem : g₁ * u * g₁⁻¹ ∈ Q ⊓ conjugate Q (g₂ * g₁⁻¹) := by
      refine ⟨hu₁, mem_conjugate_iff'.2 ?_⟩
      have e : (g₂ * g₁⁻¹) * (g₁ * u * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * u * g₂⁻¹ := by group
      rw [e]
      exact hu₂
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hu1
    apply Subtype.ext
    have : u = g₁⁻¹ * (g₁ * u * g₁⁻¹) * g₁ := by group
    show u = 1
    rw [this, hmem]
    group
  have hTI := aconfigW_five_TI h hhN hne'
  ext z
  rw [mem_conjugate_iff', mem_conjugate_iff']
  have hiff : ∀ v, v ∈ Q ↔ (g₂ * g₁⁻¹) * v * (g₂ * g₁⁻¹)⁻¹ ∈ Q := by
    intro v
    have := (Subgroup.ext_iff.1 hTI v)
    rw [mem_conjugate_iff'] at this
    exact this.symm
  rw [hiff (g₁ * z * g₁⁻¹)]
  have e : (g₂ * g₁⁻¹) * (g₁ * z * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * z * g₂⁻¹ := by group
  rw [e]

theorem NRConj_le [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {Q' : Subgroup G}
    (hQ' : Q' ∈ NRConj ((T ⊓ K) ⊔ Q) Q) : Q' ≤ (T ⊓ K) ⊔ Q ∧ Nat.card ↥Q' = 4 := by
  obtain ⟨g, hg, rfl⟩ := hQ'
  refine ⟨fun z hz => ?_, by rw [card_conjugate', h.card_Q]⟩
  have h1 : g * z * g⁻¹ ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_right (mem_conjugate_iff'.1 hz)
  have h2 := (Subgroup.mem_normalizer_iff.1 ((normalizer _).inv_mem hg) (g * z * g⁻¹)).1 h1
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at h2

theorem aconfigW_five_NRConj_even [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) : Even (Nat.card ↥(NRConj ((T ⊓ K) ⊔ Q) Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hA2, hAN, hAcard⟩ := aconfigW_five_A h
  set A : Subgroup G := T ⊔ zpowers a with hA
  have hinv : ∀ (s : ↥A) (Q' : ↥(NRConj ((T ⊓ K) ⊔ Q) Q)),
      Th2.cj (s : G) (Q' : Subgroup G) ∈ NRConj ((T ⊓ K) ⊔ Q) Q := by
    intro s Q'
    obtain ⟨g, hg, hgQ⟩ := Q'.2
    refine ⟨g * (s : G)⁻¹, (normalizer _).mul_mem hg ((normalizer _).inv_mem (hAN s.2)), ?_⟩
    rw [hgQ]
    ext z
    rw [Th2.mem_cj_iff, mem_conjugate_iff', mem_conjugate_iff']
    have e : g * ((s : G)⁻¹ * z * (s : G)) * g⁻¹ = (g * (s : G)⁻¹) * z * (g * (s : G)⁻¹)⁻¹ := by
      group
    rw [e]
  let inst : MulAction ↥A ↥(NRConj ((T ⊓ K) ⊔ Q) Q) :=
    { smul := fun s Q' => ⟨Th2.cj (s : G) (Q' : Subgroup G), hinv s Q'⟩
      one_smul := fun Q' => Subtype.ext (by
        ext z
        show z ∈ Th2.cj (((1 : ↥A)) : G) (Q' : Subgroup G) ↔ z ∈ (Q' : Subgroup G)
        rw [Th2.mem_cj_iff]
        simp)
      mul_smul := fun s t Q' => Subtype.ext (by
        ext z
        show z ∈ Th2.cj ((s * t : ↥A) : G) (Q' : Subgroup G) ↔
          z ∈ Th2.cj (s : G) (Th2.cj (t : G) (Q' : Subgroup G))
        rw [Th2.mem_cj_iff, Th2.mem_cj_iff, Th2.mem_cj_iff]
        have e : ((s * t : ↥A) : G)⁻¹ * z * ((s * t : ↥A) : G) =
            (t : G)⁻¹ * ((s : G)⁻¹ * z * (s : G)) * (t : G) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
        rw [e]) }
  have hmod := IsPGroup.card_modEq_card_fixedPoints hA2 (α := ↥(NRConj ((T ⊓ K) ⊔ Q) Q))
  have hfix : MulAction.fixedPoints ↥A ↥(NRConj ((T ⊓ K) ⊔ Q) Q) = ∅ := by
    ext Q'
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hQ'
    obtain ⟨g, hg, hgQ⟩ := Q'.2
    have hBQ : A ≤ normalizer ((conjugate Q g : Subgroup G) : Set G) := by
      intro s hs
      have hs' : (⟨s, hs⟩ : ↥A) • Q' = Q' := hQ' ⟨s, hs⟩
      have h1 : Th2.cj s (Q' : Subgroup G) = (Q' : Subgroup G) := congrArg Subtype.val hs'
      have h2 : s ∈ normalizer ((Q' : Subgroup G) : Set G) := Th2.mem_normalizer_of_cj_eq h1
      rw [hgQ] at h2
      exact h2
    have := aconfigW_five_card_le_T h hg hA2 hAN hBQ
    omega
  rw [hfix] at hmod
  have h0 : Nat.card ↥(∅ : Set ↥(NRConj ((T ⊓ K) ⊔ Q) Q)) = 0 := by simp
  rw [h0] at hmod
  exact even_iff_two_dvd.2 ((Nat.modEq_zero_iff_dvd).1 hmod)

theorem eq_P_of_w_normalizes [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {w : G} (hwK : w ∈ K)
    (hwR : w ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G))
    (hwQ : ∀ q ∈ Q, w * q = q * w) (hwfpf : ∀ p ∈ T ⊓ K, w * p * w⁻¹ = p → p = 1)
    {Q₃ : Subgroup G} (hQ₃R : Q₃ ≤ (T ⊓ K) ⊔ Q) (hQ₃c : Nat.card ↥Q₃ = 4)
    (hQ₃Q : Q₃ ⊓ Q = ⊥) (hwQ₃ : w ∈ normalizer (Q₃ : Set G)) : Q₃ = T ⊓ K := by
  have hCD := aconfigW_five_commDisj h
  obtain ⟨hPcard, hPel⟩ := aconfigW_five_P h
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  have hwP : ∀ p ∈ T ⊓ K, w * p * w⁻¹ ∈ T ⊓ K := by
    intro p hp
    have h1 : w * p * w⁻¹ ∈ (T ⊓ K) ⊔ Q :=
      (Subgroup.mem_normalizer_iff.1 hwR p).1 (Subgroup.mem_sup_left hp)
    exact ⟨hRT h1, K.mul_mem (K.mul_mem hwK hp.2) (K.inv_mem hwK)⟩
  have hwQ' : ∀ q ∈ Q, w * q * w⁻¹ = q := fun q hq => by
    rw [hwQ q hq]
    group
  have hcent : ∀ c ∈ Q₃, w * c * w⁻¹ = c → c = 1 := by
    intro c hc hwc
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm (hQ₃R hc)
    have h1 : w * p * w⁻¹ = p := by
      have e : w * (p * q) * w⁻¹ = (w * p * w⁻¹) * (w * q * w⁻¹) := by group
      rw [e, hwQ' q hq] at hwc
      exact mul_right_cancel hwc
    have hp1 := hwfpf p hp h1
    subst hp1
    have hqQ₃ : q ∈ Q₃ ⊓ Q := ⟨by simpa using hc, hq⟩
    rw [hQ₃Q, Subgroup.mem_bot] at hqQ₃
    rw [hqQ₃]
    group
  let d : ↥Q₃ → ↥Q₃ := fun q' => ⟨(q' : G)⁻¹ * (w * q' * w⁻¹),
    Q₃.mul_mem (Q₃.inv_mem q'.2) ((Subgroup.mem_normalizer_iff.1 hwQ₃ q').1 q'.2)⟩
  have hdinj : Function.Injective d := by
    intro a₁ b₁ hab
    have h1 : (a₁ : G)⁻¹ * (w * a₁ * w⁻¹) = (b₁ : G)⁻¹ * (w * b₁ * w⁻¹) := congrArg Subtype.val hab
    have hc : w * ((a₁ : G) * (b₁ : G)⁻¹) * w⁻¹ = (a₁ : G) * (b₁ : G)⁻¹ := by
      have e1 : w * a₁ * w⁻¹ = a₁ * ((b₁ : G)⁻¹ * (w * b₁ * w⁻¹)) := by
        calc w * a₁ * w⁻¹ = a₁ * ((a₁ : G)⁻¹ * (w * a₁ * w⁻¹)) := by group
          _ = _ := by rw [h1]
      calc w * ((a₁ : G) * (b₁ : G)⁻¹) * w⁻¹ = (w * a₁ * w⁻¹) * (w * b₁ * w⁻¹)⁻¹ := by group
        _ = (a₁ : G) * (b₁ : G)⁻¹ := by rw [e1]; group
    have hmem : (a₁ : G) * (b₁ : G)⁻¹ ∈ Q₃ := Q₃.mul_mem a₁.2 (Q₃.inv_mem b₁.2)
    have h2 := hcent _ hmem hc
    apply Subtype.ext
    have : (a₁ : G) = (a₁ * (b₁ : G)⁻¹) * b₁ := by group
    rw [this, h2]
    group
  have hdsurj : Function.Surjective d := Finite.injective_iff_surjective.1 hdinj
  have hle : Q₃ ≤ T ⊓ K := by
    intro q' hq'
    obtain ⟨a', ha'⟩ := hdsurj ⟨q', hq'⟩
    have hq'eq : q' = (a' : G)⁻¹ * (w * a' * w⁻¹) := (congrArg Subtype.val ha').symm
    obtain ⟨p, hp, q, hq, hpq⟩ := mem_sup_of_commute hCD.comm (hQ₃R a'.2)
    have hu : p⁻¹ * (w * p * w⁻¹) ∈ T ⊓ K := (T ⊓ K).mul_mem ((T ⊓ K).inv_mem hp) (hwP p hp)
    have hcomm : q⁻¹ * (p⁻¹ * (w * p * w⁻¹)) * q = p⁻¹ * (w * p * w⁻¹) := by
      have := hCD.comm _ hu q hq
      calc q⁻¹ * (p⁻¹ * (w * p * w⁻¹)) * q = q⁻¹ * ((p⁻¹ * (w * p * w⁻¹)) * q) := by group
        _ = q⁻¹ * (q * (p⁻¹ * (w * p * w⁻¹))) := by rw [this]
        _ = _ := by group
    have hz : (a' : G)⁻¹ * (w * a' * w⁻¹) = q⁻¹ * (p⁻¹ * (w * p * w⁻¹)) * q := by
      rw [hpq]
      have e : w * (p * q) * w⁻¹ = (w * p * w⁻¹) * (w * q * w⁻¹) := by group
      rw [e, hwQ' q hq]
      group
    rw [hq'eq, hz, hcomm]
    exact hu
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard, hQ₃c])

theorem conjugate_eq_of_mem_normalizer' {H : Subgroup G} {m : G}
    (hm : m ∈ normalizer (H : Set G)) : conjugate H m = H := by
  rw [Stage1.Thm2.Recip.conjugate_eq_cj]
  exact Th2.cj_eq_of_mem_normalizer ((normalizer (H : Set G)).inv_mem hm)

theorem eq_of_conjugate_eq' {C H : Subgroup G} {m : G} (hm : m ∈ normalizer (H : Set G))
    (hC : conjugate C m = H) : C = H := by
  have h1 := Stage1.Thm2.Recip.cj_cancel m C
  have h2 : Stage1.Thm2.Recip.cj m⁻¹ C = H := hC
  rw [h2] at h1
  rw [← h1]
  exact Th2.cj_eq_of_mem_normalizer hm

theorem mem_normalizer_of_conjugate_eq' {C : Subgroup G} {m : G} (hC : conjugate C m = C) :
    m ∈ normalizer (C : Set G) := by
  have h1 : Th2.cj m⁻¹ C = C := hC
  have := Th2.mem_normalizer_of_cj_eq h1
  simpa using (normalizer (C : Set G)).inv_mem this

theorem conjugate_conjugate' (C : Subgroup G) (g m : G) :
    conjugate (conjugate C g) m = conjugate C (g * m) := by
  rw [Stage1.Thm2.Recip.conjugate_eq_cj, Stage1.Thm2.Recip.conjugate_eq_cj,
    Stage1.Thm2.Recip.conjugate_eq_cj, Stage1.Thm2.Recip.cj_cj, mul_inv_rev]

theorem card_le_five_of_disjoint [Finite G] {R : Subgroup G} (hR : Nat.card ↥R = 16)
    {O : Set (Subgroup G)} (hOR : ∀ Q' ∈ O, Q' ≤ R) (hO4 : ∀ Q' ∈ O, Nat.card ↥Q' = 4)
    (hOd : ∀ Q₁ ∈ O, ∀ Q₂ ∈ O, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥) : Nat.card ↥O ≤ 5 := by
  classical
  have := Fintype.ofFinite G
  have hfin : O.Finite := Set.toFinite O
  let F : Finset (Subgroup G) := hfin.toFinset
  have hFO : ∀ Q', Q' ∈ F ↔ Q' ∈ O := fun Q' => hfin.mem_toFinset
  have hcardF : Nat.card ↥O = F.card := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_eq_toFinset_card O hfin
  have hfilter : ∀ Q' : Subgroup G, (Finset.univ.filter (· ∈ Q')).card = Nat.card ↥Q' := by
    intro Q'
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let t : Subgroup G → Finset G := fun Q' => (Finset.univ.filter (· ∈ Q')).erase 1
  have ht_card : ∀ Q' ∈ F, (t Q').card = 3 := by
    intro Q' hQ'
    have h4 := hO4 Q' ((hFO Q').1 hQ')
    show ((Finset.univ.filter (· ∈ Q')).erase 1).card = 3
    rw [Finset.card_erase_of_mem (by simp), hfilter, h4]
  have ht_disj : ∀ Q₁ ∈ F, ∀ Q₂ ∈ F, Q₁ ≠ Q₂ → Disjoint (t Q₁) (t Q₂) := by
    intro Q₁ h₁ Q₂ h₂ hne
    have hbot := hOd Q₁ ((hFO Q₁).1 h₁) Q₂ ((hFO Q₂).1 h₂) hne
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [t, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    have : z ∈ Q₁ ⊓ Q₂ := ⟨hz1.2, hz2.2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1.1 this
  have hsub : F.biUnion t ⊆ (Finset.univ.filter (· ∈ R)).erase 1 := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨Q', hQ', hz⟩ := hz
    simp only [t, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨hz.1, hOR Q' ((hFO Q').1 hQ') hz.2⟩
  have hRc : ((Finset.univ.filter (· ∈ R)).erase 1).card = 15 := by
    rw [Finset.card_erase_of_mem (by simp), hfilter, hR]
  have h1 := Finset.card_biUnion ht_disj
  have h2 : (F.biUnion t).card ≤ 15 := hRc ▸ Finset.card_le_card hsub
  have h3 : ∑ Q' ∈ F, (t Q').card = 3 * F.card := by
    rw [Finset.sum_congr rfl ht_card]
    simp [mul_comm]
  omega

theorem aconfigW_five_orbit_of_P [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a)
    (hP : ∃ g₁ ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G), conjugate Q g₁ = T ⊓ K) :
    ∀ g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G),
      conjugate Q g = Q ∨ conjugate Q g = T ⊓ K := by
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨hgQ, hgP⟩ := hcon
  have hCD := aconfigW_five_commDisj h
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  obtain ⟨w, hwK, hwodd, hwR, hwQ, hwfpf⟩ := aconfigW_five_w h
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  have hwNQ : w ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_of_conj_le (fun q hq => ?_)
    have : w * q * w⁻¹ = q := by rw [hwQ q hq]; group
    rw [this]
    exact hq
  have hwNP : w ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_le (fun p hp => ?_)
    have h1 : w * p * w⁻¹ ∈ (T ⊓ K) ⊔ Q :=
      (Subgroup.mem_normalizer_iff.1 hwR p).1 (Subgroup.mem_sup_left hp)
    exact ⟨hRT h1, K.mul_mem (K.mul_mem hwK hp.2) (K.inv_mem hwK)⟩
  have hww : w * w ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) :=
    (normalizer _).mul_mem hwR hwR
  have hwwQ : w * w ∈ normalizer (Q : Set G) := (normalizer _).mul_mem hwNQ hwNQ
  have hwwP : w * w ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) := (normalizer _).mul_mem hwNP hwNP
  have hgw : g * w ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) :=
    (normalizer _).mul_mem hg hwR
  have hgww : g * w * w ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) :=
    (normalizer _).mul_mem hgw hwR
  have hTIQ : ∀ g' ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G),
      conjugate Q g' ≠ Q → conjugate Q g' ⊓ Q = ⊥ := by
    intro g' hg' hne
    by_contra hbot
    have h1 : conjugate Q 1 = Q := conjugate_eq_of_mem_normalizer' (one_mem _)
    have := aconfigW_five_TI' h hg' (one_mem _) (by rwa [h1])
    rw [h1] at this
    exact hne this
  have hfixP : ∀ g' ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G), conjugate Q g' ≠ Q →
      w ∈ normalizer ((conjugate Q g' : Subgroup G) : Set G) → conjugate Q g' = T ⊓ K :=
    fun g' hg' hne hw => eq_P_of_w_normalizes h hwK hwR hwQ hwfpf
      (NRConj_le h ⟨g', hg', rfl⟩).1 (NRConj_le h ⟨g', hg', rfl⟩).2 (hTIQ g' hg' hne) hw
  have hC1 : conjugate Q (g * w) = conjugate (conjugate Q g) w := (conjugate_conjugate' Q g w).symm
  have hC2 : conjugate Q (g * w * w) = conjugate (conjugate Q (g * w)) w :=
    (conjugate_conjugate' Q (g * w) w).symm
  have hC2' : conjugate Q (g * w * w) = conjugate (conjugate Q g) (w * w) := by
    rw [conjugate_conjugate', mul_assoc]
  have hQP : Q ≠ T ⊓ K := by
    intro hQP
    have hbot := hCD.inf
    rw [← hQP, inf_idem] at hbot
    have := h.card_Q
    rw [hbot, Subgroup.card_bot] at this
    omega
  have h01 : conjugate Q (g * w) ≠ conjugate Q g := by
    intro hEq
    rw [hC1] at hEq
    exact hgP (hfixP g hg hgQ (mem_normalizer_of_conjugate_eq' hEq))
  have h12 : conjugate Q (g * w * w) ≠ conjugate Q (g * w) := by
    intro hEq
    rw [hC2] at hEq
    have hwN1 := mem_normalizer_of_conjugate_eq' hEq
    have hne1 : conjugate Q (g * w) ≠ Q := by
      intro h1
      rw [hC1] at h1
      exact hgQ (eq_of_conjugate_eq' hwNQ h1)
    have h1P := hfixP (g * w) hgw hne1 hwN1
    rw [hC1] at h1P
    exact hgP (eq_of_conjugate_eq' hwNP h1P)
  have h02 : conjugate Q (g * w * w) ≠ conjugate Q g := by
    intro hEq
    rw [hC2'] at hEq
    have hwwN := mem_normalizer_of_conjugate_eq' hEq
    obtain ⟨k, hk⟩ := hwodd
    have hwk : w = (w * w) ^ (k + 1) := by
      have h1 : w ^ (orderOf w) = 1 := pow_orderOf_eq_one w
      rw [hk] at h1
      calc w = w ^ (2 * k + 1 + 1) * (w ^ (2 * k + 1))⁻¹ := by group
        _ = w ^ (2 * k + 1 + 1) := by rw [h1]; group
        _ = (w * w) ^ (k + 1) := by rw [← pow_two, ← pow_mul]; ring_nf
    have hwN : w ∈ normalizer ((conjugate Q g : Subgroup G) : Set G) := by
      rw [hwk]
      exact Subgroup.pow_mem _ hwwN _
    exact hgP (hfixP g hg hgQ hwN)
  have hQ1 : Q ≠ conjugate Q (g * w) := by
    intro hEq
    rw [hC1] at hEq
    exact hgQ (eq_of_conjugate_eq' hwNQ hEq.symm)
  have hP1 : T ⊓ K ≠ conjugate Q (g * w) := by
    intro hEq
    rw [hC1] at hEq
    exact hgP (eq_of_conjugate_eq' hwNP hEq.symm)
  have hQ2 : Q ≠ conjugate Q (g * w * w) := by
    intro hEq
    rw [hC2'] at hEq
    exact hgQ (eq_of_conjugate_eq' hwwQ hEq.symm)
  have hP2 : T ⊓ K ≠ conjugate Q (g * w * w) := by
    intro hEq
    rw [hC2'] at hEq
    exact hgP (eq_of_conjugate_eq' hwwP hEq.symm)
  have hOQ : Q ∈ NRConj ((T ⊓ K) ⊔ Q) Q :=
    ⟨1, one_mem _, (conjugate_eq_of_mem_normalizer' (one_mem _)).symm⟩
  have hOP : T ⊓ K ∈ NRConj ((T ⊓ K) ⊔ Q) Q := by
    obtain ⟨g₁, hg₁, hg₁P⟩ := hP
    exact ⟨g₁, hg₁, hg₁P.symm⟩
  have hO0 : conjugate Q g ∈ NRConj ((T ⊓ K) ⊔ Q) Q := ⟨g, hg, rfl⟩
  have hO1 : conjugate Q (g * w) ∈ NRConj ((T ⊓ K) ⊔ Q) Q := ⟨g * w, hgw, rfl⟩
  have hO2 : conjugate Q (g * w * w) ∈ NRConj ((T ⊓ K) ⊔ Q) Q := ⟨g * w * w, hgww, rfl⟩
  classical
  have hfin : (NRConj ((T ⊓ K) ⊔ Q) Q).Finite := Set.toFinite _
  have hnodup : [Q, T ⊓ K, conjugate Q g, conjugate Q (g * w),
      conjugate Q (g * w * w)].Nodup := by
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
      List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hQP, fun h' => hgQ h'.symm, hQ1, hQ2⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h' => hgP h'.symm, hP1, hP2⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h01.symm, h02.symm⟩
    · simp only [List.mem_singleton]
      exact h12.symm
  have h5 : ([Q, T ⊓ K, conjugate Q g, conjugate Q (g * w),
      conjugate Q (g * w * w)] : List (Subgroup G)).toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup hnodup]
    rfl
  have hsub : (([Q, T ⊓ K, conjugate Q g, conjugate Q (g * w),
      conjugate Q (g * w * w)] : List (Subgroup G)).toFinset : Set (Subgroup G)) ⊆
      NRConj ((T ⊓ K) ⊔ Q) Q := by
    intro z hz
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
      or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hOQ
    · exact hOP
    · exact hO0
    · exact hO1
    · exact hO2
  have hge : 5 ≤ Nat.card ↥(NRConj ((T ⊓ K) ⊔ Q) Q) := by
    rw [Nat.card_coe_set_eq]
    calc 5 = (([Q, T ⊓ K, conjugate Q g, conjugate Q (g * w),
          conjugate Q (g * w * w)] : List (Subgroup G)).toFinset : Set (Subgroup G)).ncard := by
          rw [Set.ncard_coe_finset, h5]
      _ ≤ _ := Set.ncard_le_ncard hsub hfin
  have hle : Nat.card ↥(NRConj ((T ⊓ K) ⊔ Q) Q) ≤ 5 := by
    refine card_le_five_of_disjoint hRcard (fun Q' hQ' => (NRConj_le h hQ').1)
      (fun Q' hQ' => (NRConj_le h hQ').2) (fun Q₁ h₁ Q₂ h₂ hne => ?_)
    by_contra hbot
    obtain ⟨g₁, hg₁, rfl⟩ := h₁
    obtain ⟨g₂, hg₂, rfl⟩ := h₂
    exact hne (aconfigW_five_TI' h hg₁ hg₂ hbot)
  obtain ⟨k, hk⟩ := aconfigW_five_NRConj_even h
  omega

@[expose] def B_P46_shadow : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K T Q S : Subgroup G) (a : G),
    IsAConfigW 5 x K T Q S a →
      (∀ g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G), conjugate Q g ≠ T ⊓ K) → False

theorem b_P46_orbit_of_shadow (hs : B_P46_shadow) : B_P46_orbit := by
  intro G _ _ hG x K T Q S a h g hg
  by_cases hP : ∃ g₁ ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G), conjugate Q g₁ = T ⊓ K
  · exact aconfigW_five_orbit_of_P h hP g hg
  · push Not at hP
    exact (hs G hG x K T Q S a h hP).elim

theorem b_L114_fusion5_of_shadow (hs : B_P46_shadow) : B_L114_fusion5 :=
  b_L114_fusion5_of_orbit (b_P46_orbit_of_shadow hs)

end CFSG.GH74.GLS.C3.Layer1.Bk
