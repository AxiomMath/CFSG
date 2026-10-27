module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem eq_nine_of_modEq_thirteen : ∀ k ≤ 9, 2 ^ 9 ≡ 2 ^ k [MOD 13] → k = 9 := by decide

theorem le_centralizer_of_isPGroup_thirteen {T Q : Subgroup G} (hT : IsPGroup 13 T)
    (hTQ : T ≤ normalizer (Q : Set G)) (hQ : Nat.card Q = 2 ^ 9) :
    T ≤ centralizer (Q : Set G) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥T ↥Q := MulAction.compHom ↥Q (SL2MinimalFaithful.conjAction hTQ)
  have hsmul : ∀ (t : ↥T) (q : ↥Q), ((t • q : ↥Q) : G) = t * q * (t : G)⁻¹ := fun t q => rfl
  have hmod := hT.card_modEq_card_fixedPoints ↥Q
  have hfix : MulAction.fixedPoints ↥T ↥Q =
      (((centralizer (T : Set G)).subgroupOf Q : Subgroup ↥Q) : Set ↥Q) := by
    ext q
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro h t ht
      have h1 := congrArg Subtype.val (h ⟨t, ht⟩)
      rw [hsmul] at h1
      calc t * (q : G) = t * q * t⁻¹ * t := by group
        _ = q * t := by rw [h1]
    · intro h t
      apply Subtype.ext
      rw [hsmul, h t t.2, mul_inv_cancel_right]
  have hcard : Nat.card (MulAction.fixedPoints ↥T ↥Q) =
      Nat.card ((centralizer (T : Set G)).subgroupOf Q) := by
    rw [hfix]
    rfl
  have hQ2 : IsPGroup 2 ↥Q := IsPGroup.of_card hQ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hQ2.to_subgroup ((centralizer (T : Set G)).subgroupOf Q))
  have hk9 : k ≤ 9 := by
    have h1 := Subgroup.card_le_card_group ((centralizer (T : Set G)).subgroupOf Q)
    rw [hk, hQ] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  rw [hcard, hk, hQ] at hmod
  have hk' := eq_nine_of_modEq_thirteen k hk9 hmod
  subst hk'
  have htop : (centralizer (T : Set G)).subgroupOf Q = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hk, hQ]
  intro t ht
  rw [mem_centralizer_iff]
  intro q hq
  have h1 : (⟨q, hq⟩ : ↥Q) ∈ (centralizer (T : Set G)).subgroupOf Q := htop ▸ mem_top _
  rw [mem_subgroupOf, mem_centralizer_iff] at h1
  exact (h1 t ht).symm

omit [Finite G] in
theorem mem_normalizer_sup_of_mem_of_mem {X L : Subgroup G} {n : G}
    (hX : n ∈ normalizer (X : Set G)) (hL : n ∈ normalizer (L : Set G)) :
    n ∈ normalizer ((X ⊔ L : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hX hL ⊢
  rw [Subgroup.map_sup, hX, hL]

omit [Finite G] in
theorem mem_normalizer_centralizer_of_normalizes {Q : Subgroup G} {n : G}
    (hn : n ∈ normalizer (Q : Set G)) : n ∈ normalizer (centralizer (Q : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  have key : ∀ m ∈ normalizer (Q : Set G), ∀ c ∈ centralizer (Q : Set G),
      m * c * m⁻¹ ∈ centralizer (Q : Set G) := by
    intro m hm c hc
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : m⁻¹ * q * m ∈ Q := by
      have := (mem_normalizer_iff.mp (inv_mem hm) q).mp hq
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp hc _ hq'
    calc q * (m * c * m⁻¹) = m * ((m⁻¹ * q * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * q * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * q := by group
  refine ⟨key n hn c, fun h => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ h
  rwa [show n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c by group] at this

theorem false_of_thirteen {K Q₁ O : Subgroup G} {z : G}
    (hK : ∀ N : Subgroup G, N ≤ K → K ≤ normalizer (N : Set G) → N = ⊥ ∨ N = K)
    (hK2 : 2 ^ 10 ∣ Nat.card K) (hK13 : 13 ∣ Nat.card K)
    (hKX : K ≤ normalizer ((Q₁ ⊔ O : Subgroup G) : Set G)) (hQ₁O : Q₁ ≤ normalizer (O : Set G))
    (hO : Odd (Nat.card O)) (hQ₁ : Nat.card Q₁ = 2 ^ 9)
    (hz : z ∈ Q₁) (hzC : z ∈ centralizer (Q₁ : Set G))
    (hC : ∀ T₂ : Subgroup G, T₂ ≤ centralizer (Q₁ : Set G) → IsPGroup 2 T₂ → T₂ ≤ zpowers z) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = Q₁ ⊔ O := ⟨_, rfl⟩
  rw [← hXdef] at hKX
  have hQ₁2 : IsPGroup 2 Q₁ := IsPGroup.of_card hQ₁
  have hOQ : O ⊓ Q₁ = ⊥ := two_subgroup_of_odd_eq_bot _ O (hQ₁2.to_le inf_le_right) hO inf_le_left
  have hcardX : Nat.card X = Nat.card O * 2 ^ 9 := by
    have h := card_sup_mul_card_inf (H := O) (R := Q₁) hQ₁O
    rwa [hOQ, Subgroup.card_bot, mul_one, sup_comm, ← hXdef, hQ₁] at h
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hOv : (Nat.card O).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h =>
      (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h)
  have hXv : (Nat.card X).factorization 2 = 9 := by
    rw [hcardX, Nat.factorization_mul hO0 (by norm_num), Finsupp.coe_add, Pi.add_apply, hOv,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, zero_add]
  have hQ₁X : Q₁ ≤ X := hXdef ▸ le_sup_left
  have hsyl : IsSylowOf 2 Q₁ X := isSylowOf_of_card hQ₁X (by rw [hQ₁, hXv])
  have hKN : ∀ M : Subgroup G, K ≤ normalizer (M : Set G) →
      K ≤ normalizer ((K ⊓ M : Subgroup G) : Set G) := fun M hM k hk => by
    rw [mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨K.mul_mem (K.mul_mem hk h1) (K.inv_mem hk), (mem_normalizer_iff.mp (hM hk) w).mp h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (mem_normalizer_iff.mp (hM hk) w).mpr h2⟩
      have h3 := K.mul_mem (K.mul_mem (K.inv_mem hk) h1) hk
      rwa [show k⁻¹ * (k * w * k⁻¹) * k = w by group] at h3
  have hKX1 : K ⊓ X = ⊥ := by
    rcases hK (K ⊓ X) inf_le_left (hKN X hKX) with h | h
    · exact h
    · exfalso
      have hKX' : K ≤ X := h ▸ inf_le_right
      have h1 := (hK2.trans (Subgroup.card_dvd_of_le hKX'))
      rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', hXv] at h1
      omega
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = X ⊔ K := ⟨_, rfl⟩
  have hXY : X ≤ Y := hYdef ▸ le_sup_left
  have hKY : K ≤ Y := hYdef ▸ le_sup_right
  have hYX : Y ≤ normalizer (X : Set G) := hYdef ▸ sup_le le_normalizer hKX
  have hcardY : Nat.card Y = Nat.card X * Nat.card K := by
    have h := card_sup_mul_card_inf (H := X) (R := K) hKX
    rwa [inf_comm, hKX1, Subgroup.card_bot, mul_one, ← hYdef] at h
  obtain ⟨N, hNdef⟩ : ∃ N, N = Y ⊓ normalizer (Q₁ : Set G) := ⟨_, rfl⟩
  have hNY : N ≤ Y := hNdef ▸ inf_le_left
  have hNQ : N ≤ normalizer (Q₁ : Set G) := hNdef ▸ inf_le_right
  have hfr : X ⊔ N = Y := by
    refine le_antisymm (sup_le hXY hNY) ?_
    intro y hy
    have hle : Q₁.map (MulAut.conj y).toMonoidHom ≤ X := by
      rintro _ ⟨q, hq, rfl⟩
      exact (mem_normalizer_iff.mp (hYX hy) q).mp (hQ₁X hq)
    have hy' : IsSylowOf 2 (Q₁.map (MulAut.conj y).toMonoidHom) X :=
      isSylowOf_of_card hle (by rw [card_map_of_injective (MulAut.conj y).injective, hQ₁, hXv])
    obtain ⟨x, hx, hxw⟩ := hsyl.exists_mem_conj hy'
    have hn : x⁻¹ * y ∈ N := by
      rw [hNdef]
      refine ⟨mul_mem (hXY (inv_mem hx)) hy, AS76b.mem_normalizer_of_map_conj_le ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      have h1 : (MulAut.conj y).toMonoidHom q ∈ Q₁.map (MulAut.conj y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hq
      have h2 := (hxw _).1 h1
      change x⁻¹ * (y * q * y⁻¹) * x ∈ Q₁ at h2
      show x⁻¹ * y * q * (x⁻¹ * y)⁻¹ ∈ Q₁
      have e : x⁻¹ * y * q * (x⁻¹ * y)⁻¹ = x⁻¹ * (y * q * y⁻¹) * x := by group
      rw [e]
      exact h2
    have e : y = x * (x⁻¹ * y) := by group
    rw [e]
    exact mul_mem (mem_sup_left hx) (mem_sup_right hn)
  have hNX : N ≤ normalizer (X : Set G) := hNY.trans hYX
  have hcardN : Nat.card N = Nat.card K * Nat.card (X ⊓ N : Subgroup G) := by
    have h := card_sup_mul_card_inf (H := X) (R := N) hNX
    rw [hfr, hcardY, mul_assoc] at h
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h).symm
  obtain ⟨T13, hT13⟩ := exists_isSylowOf 13 N
  have hT13C : T13 ≤ centralizer (Q₁ : Set G) :=
    le_centralizer_of_isPGroup_thirteen hT13.isPGroup (hT13.le.trans hNQ) hQ₁
  obtain ⟨L, hLdef⟩ : ∃ L, L = Y ⊓ centralizer (Q₁ : Set G) := ⟨_, rfl⟩
  have hLY : L ≤ Y := hLdef ▸ inf_le_left
  have hLC : L ≤ centralizer (Q₁ : Set G) := hLdef ▸ inf_le_right
  have hLX : L ≤ normalizer (X : Set G) := hLY.trans hYX
  obtain ⟨M, hMdef⟩ : ∃ M, M = X ⊔ L := ⟨_, rfl⟩
  have hXM : X ≤ M := hMdef ▸ le_sup_left
  have hLM : L ≤ M := hMdef ▸ le_sup_right
  have hMY : M ≤ Y := hMdef ▸ sup_le hXY hLY
  have hYM : Y ≤ normalizer (M : Set G) := by
    rw [← hfr]
    refine sup_le (hXM.trans le_normalizer) ?_
    intro n hn
    rw [hMdef]
    refine mem_normalizer_sup_of_mem_of_mem (hNX hn) ?_
    rw [hLdef]
    have h1 : n ∈ normalizer (Y : Set G) := le_normalizer (hNY hn)
    have h2 : n ∈ normalizer (centralizer (Q₁ : Set G) : Set G) :=
      mem_normalizer_centralizer_of_normalizes (hNQ hn)
    rw [mem_normalizer_iff] at h1 h2 ⊢
    intro w
    rw [mem_inf, mem_inf, h1 w, h2 w]
  rcases hK (K ⊓ M) inf_le_left (hKN M (hKY.trans hYM)) with hKM | hKM
  ·
    have hcard := card_sup_mul_card_inf (H := M) (R := K) (hKY.trans hYM)
    rw [inf_comm, hKM, Subgroup.card_bot, mul_one] at hcard
    have hle : Nat.card (M ⊔ K : Subgroup G) ≤ Nat.card Y := Subgroup.card_le_of_le (sup_le hMY hKY)
    rw [hcard, hcardY] at hle
    have hMX : Nat.card M ≤ Nat.card X := Nat.le_of_mul_le_mul_right hle Nat.card_pos
    have hMeq : X = M := Subgroup.eq_of_le_of_card_ge hXM hMX
    have hT13L : T13 ≤ L := hLdef ▸ le_inf (hT13.le.trans hNY) hT13C
    have hT13X : T13 ≤ X ⊓ N := le_inf ((hT13L.trans hLM).trans hMeq.symm.le) hT13.le
    have h2 := Subgroup.card_dvd_of_le hT13X
    rw [hT13.card_eq, Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne',
      hcardN, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.coe_add,
      Pi.add_apply] at h2
    have h3 : 1 ≤ (Nat.card K).factorization 13 :=
      (Nat.Prime.dvd_iff_one_le_factorization (by norm_num) Nat.card_pos.ne').mp hK13
    omega
  ·
    have hKM' : K ≤ M := hKM ▸ inf_le_right
    have hcard := card_sup_mul_card_inf (H := X) (R := L) hLX
    rw [← hMdef] at hcard
    obtain ⟨PL, hPL⟩ := exists_isSylowOf 2 L
    have hPLz : PL ≤ zpowers z := hC PL (hPL.le.trans hLC) hPL.isPGroup
    have hzXL : zpowers z ≤ X ⊓ L := by
      rw [zpowers_le]
      exact ⟨hQ₁X hz, hLdef ▸ ⟨hXY (hQ₁X hz), hzC⟩⟩
    have hPLd := Subgroup.card_dvd_of_le (hPLz.trans hzXL)
    rw [hPL.card_eq, Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne']
      at hPLd
    have hMd := hK2.trans (Subgroup.card_dvd_of_le hKM')
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne'] at hMd
    have h2 : (Nat.card M * Nat.card (X ⊓ L : Subgroup G)).factorization 2 =
        (Nat.card X * Nat.card L).factorization 2 := by rw [hcard]
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.coe_add, Pi.add_apply,
      Finsupp.coe_add, Pi.add_apply, hXv] at h2
    omega

section Sec3

variable {A A₁ R : Subgroup G} {x : G}

theorem Sec3Pre.card_A
    (hS : Sec3Pre G A A₁ R x) :
    Nat.card A = 251596800 := by
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hS.type.2
  have e : RankTwoStandard.rankTwoQuot A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hS.center_eq).trans QuotientGroup.quotientBot
  rw [← Nat.card_congr e.toEquiv, h]
  unfold ordG2
  norm_num

theorem Sec3Pre.eq_bot_or_eq (hS : Sec3Pre G A A₁ R x) {N : Subgroup G} (hNA : N ≤ A)
    (hAN : A ≤ normalizer (N : Set G)) : N = ⊥ ∨ N = A := by
  have hq : Open.IsQuasisimple ↥A := hS.base.hyp.standard.1
  have : IsSimpleGroup (↥A ⧸ center ↥A) := hq.2
  have e : ↥A ⧸ center ↥A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hS.center_eq).trans QuotientGroup.quotientBot
  have : IsSimpleGroup ↥A := e.symm.isSimpleGroup
  have : (N.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    have h1 : (⟨n, hNA hn⟩ : ↥A) ∈ N.subgroupOf A := hn
    rw [h, mem_bot] at h1
    exact (mem_bot).2 (congrArg Subtype.val h1)
  · right
    refine le_antisymm hNA fun a ha => ?_
    have h1 : (⟨a, ha⟩ : ↥A) ∈ N.subgroupOf A := h ▸ mem_top _
    exact h1

end Sec3

theorem sec3ZNotPoint_of
    (h37 : Step37) :
    Sec3ZNotPoint := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ0 hN h hzh
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hcard9, hsyl, -⟩ := h37 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ0
  have hsuz := hQ0.dData.suz
  have hS := hsuz.setting.toSec3Pre
  have hzQ : z ∈ centerIn Q := hsuz.Q_center ▸ mem_zpowers z
  have hzQ₀ : z ∈ centerIn Q₀ := hQ0.center_Q₀ ▸ hzQ
  have hQz : Q ≤ centralizer ({z} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzQ.2 q hq)
  have hQ₀z : Q₀ ≤ centralizer ({z} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzQ₀.2 q hq)
  have hQ₁z : Q₀ ⊔ Q ≤ centralizer ({z} : Set G) := sup_le hQ₀z hQz
  have hzQ₁ : z ∈ Q₀ ⊔ Q := mem_sup_right hzQ.1
  have hzC : z ∈ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun q hq => mem_centralizer_singleton_iff.mp (hQ₁z hq)
  have hzh' : h * z * h⁻¹ ∈ R := (mem_rightConjugate_iff R h z).mp hzh
  have hKz : rightConjugate A h ≤ centralizer ({z} : Set G) := by
    intro k hk
    rw [mem_rightConjugate_iff] at hk
    have h1 := mem_centralizer_iff.mp (hS.sylowR.le hzh') _ hk
    have e1 : h * k * h⁻¹ * (h * z * h⁻¹) = h * (k * z) * h⁻¹ := by group
    have e2 : h * z * h⁻¹ * (h * k * h⁻¹) = h * (z * k) * h⁻¹ := by group
    rw [e1, e2] at h1
    exact mem_centralizer_singleton_iff.mpr (mul_left_cancel (mul_right_cancel h1))
  have hK : ∀ N : Subgroup G, N ≤ rightConjugate A h →
      rightConjugate A h ≤ normalizer (N : Set G) → N = ⊥ ∨ N = rightConjugate A h := by
    intro N hNK hKN
    obtain ⟨N', hN'⟩ : ∃ N' : Subgroup G, N' = rightConjugate N h⁻¹ := ⟨_, rfl⟩
    have hmem : ∀ w, w ∈ N' ↔ h⁻¹ * w * h ∈ N := fun w => by
      rw [hN', mem_rightConjugate_iff, inv_inv]
    have hN'A : N' ≤ A := by
      intro w hw
      have h1 := hNK ((hmem w).1 hw)
      rw [mem_rightConjugate_iff] at h1
      rwa [show h * (h⁻¹ * w * h) * h⁻¹ = w by group] at h1
    have hAN' : A ≤ normalizer (N' : Set G) := by
      intro a ha
      have hk : h⁻¹ * a * h ∈ rightConjugate A h := by
        rw [mem_rightConjugate_iff]
        rwa [show h * (h⁻¹ * a * h) * h⁻¹ = a by group]
      rw [mem_normalizer_iff]
      intro w
      rw [hmem, hmem, mem_normalizer_iff.mp (hKN hk) (h⁻¹ * w * h)]
      rw [show h⁻¹ * a * h * (h⁻¹ * w * h) * (h⁻¹ * a * h)⁻¹ = h⁻¹ * (a * w * a⁻¹) * h by group]
    rcases hS.eq_bot_or_eq hN'A hAN' with h0 | h0
    · left
      rw [eq_bot_iff]
      intro n hn
      have h1 : h * n * h⁻¹ ∈ N' := (hmem _).2 (by rwa [show h⁻¹ * (h * n * h⁻¹) * h = n by group])
      rw [h0, mem_bot] at h1
      rw [mem_bot]
      calc n = h⁻¹ * (h * n * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    · right
      refine le_antisymm hNK fun k hk => ?_
      rw [mem_rightConjugate_iff] at hk
      have h1 := (hmem _).1 (h0 ▸ hk)
      rwa [show h⁻¹ * (h * k * h⁻¹) * h = k by group] at h1
  have hcardK : Nat.card (rightConjugate A h) = 251596800 := by
    rw [rightConjugate_card, hS.card_A]
  have hC : ∀ T₂ : Subgroup G, T₂ ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) →
      IsPGroup 2 T₂ → T₂ ≤ zpowers z := by
    intro T₂ hT₂ h2
    have hT₂Q : T₂ ≤ centralizer (Q : Set G) :=
      hT₂.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
    have hT₂Q₀ : T₂ ≤ centralizer (Q₀ : Set G) :=
      hT₂.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
    have hsup2 : IsPGroup 2 ↥(Q₀ ⊔ T₂) := hsyl.isPGroup.to_sup_of_normal_left' h2
      (hT₂Q₀.trans (Subgroup.centralizer_le_normalizer _))
    have heq := hsyl.eq_of_le le_sup_left (sup_le hsyl.le hT₂Q) hsup2
    have hT₂le : T₂ ≤ Q₀ := heq ▸ le_sup_right
    intro t ht
    have h1 : t ∈ centerIn Q₀ := ⟨hT₂le ht, hT₂Q₀ ht⟩
    rw [hQ0.center_Q₀, hsuz.Q_center] at h1
    exact h1
  exact false_of_thirteen hK (by rw [hcardK]; norm_num) (by rw [hcardK]; norm_num)
    (hKz.trans hN) (hQ₁z.trans (AS76b.le_normalizer_oddCoreIn _)) (AS76b.odd_card_oddCoreIn _)
    hcard9 hzQ₁ hzC hC

end CFSG.ComponentClassification.AS81
