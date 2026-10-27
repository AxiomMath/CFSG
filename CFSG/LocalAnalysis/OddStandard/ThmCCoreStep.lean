module

public import CFSG.LocalAnalysis.OddStandard.ThmCCoreLocal
public import CFSG.LocalAnalysis.OddStandard.ThmCCoreOdd
public import CFSG.LocalAnalysis.OddStandard.ThmCO2Pre

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.OddStandard.ThmC CFSG.OddStandard.ThmC.T
open CFSG.GH74.GLS.Bg.TwoGroups

variable {X : Type} [Group X]

theorem inf_normal_mem {T L : Subgroup X} [L.Normal] {t d : X} (ht : t ∈ T) (hd : d ∈ T ⊓ L) :
    t * d * t⁻¹ ∈ T ⊓ L :=
  ⟨T.mul_mem (T.mul_mem ht hd.1) (T.inv_mem ht), Normal.conj_mem inferInstance d hd.2 t⟩

theorem inf_normal_mem_of_normalizer {T L : Subgroup X} [L.Normal] {m d : X}
    (hm : m ∈ normalizer (T : Set X)) (hd : d ∈ T ⊓ L) : m * d * m⁻¹ ∈ T ⊓ L :=
  ⟨(Subgroup.mem_normalizer_iff.1 hm d).1 hd.1, Normal.conj_mem inferInstance d hd.2 m⟩

theorem exists_pow_mul_mem {H K : Subgroup X} (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {m k : X} (hm : m ∈ H) (hk : k ∈ K) (i : ℕ) : ∃ k' ∈ K, (m * k) ^ i = m ^ i * k' := by
  induction i with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ i ih =>
    obtain ⟨k', hk', h⟩ := ih
    refine ⟨(m⁻¹ * k' * m) * k, K.mul_mem ?_ hk, ?_⟩
    · have := hKn m⁻¹ (H.inv_mem hm) k' hk'
      simpa using this
    · rw [pow_succ, h]
      group

theorem pow_mem_of_pow_mul_eq_one {H K : Subgroup X} (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {m k : X} (hm : m ∈ H) (hk : k ∈ K) (j : ℕ) (hj : (m * k) ^ j = 1) : m ^ j ∈ K := by
  obtain ⟨k', hk', h⟩ := exists_pow_mul_mem hKn hm hk j
  rw [hj] at h
  have : m ^ j = k'⁻¹ := by
    calc m ^ j = (m ^ j * k') * k'⁻¹ := by group
      _ = k'⁻¹ := by rw [← h]; group
  rw [this]
  exact K.inv_mem hk'

theorem conj_pow_agree {A : Subgroup X} {u v : X} (hu : u ∈ nzr A)
    (h : ∀ x ∈ A, u * x * u⁻¹ = v * x * v⁻¹) (n : ℕ) :
    ∀ x ∈ A, u ^ n * x * (u ^ n)⁻¹ = v ^ n * x * (v ^ n)⁻¹ := by
  induction n with
  | zero => intro x hx; simp
  | succ n ih =>
    intro x hx
    have hyu : u ^ n * x * (u ^ n)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 (pow_mem hu n) x).1 hx
    have e1 : u ^ (n + 1) * x * (u ^ (n + 1))⁻¹ = u * (u ^ n * x * (u ^ n)⁻¹) * u⁻¹ := by
      rw [pow_succ']; group
    have e2 : v ^ (n + 1) * x * (v ^ (n + 1))⁻¹ = v * (v ^ n * x * (v ^ n)⁻¹) * v⁻¹ := by
      rw [pow_succ']; group
    rw [e1, e2, ← ih x hx]
    exact h _ hyu

theorem comm_mem_inf {T L H K : Subgroup X} [L.Normal] (hT2 : IsPGroup 2 T) (hTH : T ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hKodd : ∀ k ∈ K, Odd (orderOf k))
    {x m k : X} (hxL : x ∈ L) (hxH : x ∈ H) (hk : k ∈ K) (hmk : m * k = x)
    (hmT : m ∈ normalizer (T : Set X)) {s : X} (hs : s ∈ T) : m * s * m⁻¹ * s⁻¹ ∈ T ⊓ L := by
  have hmx : m = x * k⁻¹ := by rw [← hmk]; group
  have hsH : s ∈ H := hTH hs
  have hκ : k⁻¹ * (s * k * s⁻¹) ∈ K := K.mul_mem (K.inv_mem hk) (hKn s hsH k hk)
  have hκ' : x * (k⁻¹ * (s * k * s⁻¹)) * x⁻¹ ∈ K := hKn x hxH _ hκ
  have hc : x * s * x⁻¹ * s⁻¹ ∈ L := by
    have h1 : s * x⁻¹ * s⁻¹ ∈ L := Normal.conj_mem inferInstance x⁻¹ (L.inv_mem hxL) s
    have := L.mul_mem hxL h1
    simpa [mul_assoc] using this
  have hsup : m * s * m⁻¹ * s⁻¹ ∈ L ⊔ K := by
    have h2 : m * s * m⁻¹ * s⁻¹ =
        (x * (k⁻¹ * (s * k * s⁻¹)) * x⁻¹) * (x * s * x⁻¹ * s⁻¹) := by
      rw [hmx]; group
    rw [h2]
    exact (sup_comm L K ▸ Subgroup.mul_mem_sup hκ' hc : _ ∈ L ⊔ K)
  have hT' : m * s * m⁻¹ * s⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.1 hmT s).1 hs) (T.inv_mem hs)
  obtain ⟨n, hn⟩ := hT2 ⟨_, hT'⟩
  have hn' : (m * s * m⁻¹ * s⁻¹) ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact ⟨hT', mem_of_two_power_of_mem_sup hKodd hsup hn'⟩

theorem exists_odd_pow_mem [Finite X] {D L : Subgroup X} (hDL : D ≤ L)
    (hidx : ¬ 2 ∣ D.relIndex L) {g : X} (hgL : g ∈ L) (hgN : g ∈ normalizer (D : Set X)) :
    ∃ j : ℕ, Odd j ∧ g ^ j ∈ D := by
  set N : Subgroup X := normalizer (D : Set X) ⊓ L with hN
  have hDN : D ≤ N := le_inf Subgroup.le_normalizer hDL
  have hnorm : (D.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDN).2 inf_le_left
  have hdvd : D.relIndex N ∣ D.relIndex L :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex D N L hDN (inf_le_right : N ≤ L))
  have hodd : Odd (D.relIndex N) := by
    have : ¬ 2 ∣ D.relIndex N := fun h => hidx (h.trans hdvd)
    exact Nat.odd_iff.2 (by omega)
  let q : N → N ⧸ D.subgroupOf N := QuotientGroup.mk
  have hcard : Nat.card (N ⧸ D.subgroupOf N) = D.relIndex N := rfl
  have h1 : orderOf (QuotientGroup.mk (⟨g, hgN, hgL⟩ : N) : N ⧸ D.subgroupOf N) ∣
      D.relIndex N := hcard ▸ orderOf_dvd_natCard _
  refine ⟨orderOf (QuotientGroup.mk (⟨g, hgN, hgL⟩ : N) : N ⧸ D.subgroupOf N),
    Odd.of_dvd_nat hodd h1, ?_⟩
  have h2 := pow_orderOf_eq_one (QuotientGroup.mk (⟨g, hgN, hgL⟩ : N) : N ⧸ D.subgroupOf N)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem exists_odd_part {A : Subgroup X} (hA : IsPGroup 2 A) {g : X} {j : ℕ} (hj : Odd j)
    (hgj : g ^ j ∈ A) :
    ∃ g' ∈ zpowers g, (∃ j' : ℕ, Odd j' ∧ g' ^ j' = 1) ∧ g * g'⁻¹ ∈ A := by
  obtain ⟨c, hc⟩ := hA ⟨g ^ j, hgj⟩
  have hc' : (g ^ j) ^ (2 ^ c) = 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  have hcop : IsCoprime ((2 ^ c : ℕ) : ℤ) (j : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr hj)
  obtain ⟨t, s, hts⟩ := hcop
  refine ⟨g ^ (t * ((2 ^ c : ℕ) : ℤ)), Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _,
    ⟨j, hj, ?_⟩, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul]
    have h1 : t * ((2 ^ c : ℕ) : ℤ) * (j : ℤ) = ((j * 2 ^ c : ℕ) : ℤ) * t := by
      push_cast; ring
    rw [h1, zpow_mul, zpow_natCast, pow_mul, hc', one_zpow]
  · have h1 : (1 : ℤ) + -(t * ((2 ^ c : ℕ) : ℤ)) = (j : ℤ) * s := by linarith
    have h2 : g * (g ^ (t * ((2 ^ c : ℕ) : ℤ)))⁻¹ = g ^ ((j : ℤ) * s) := by
      rw [← h1, zpow_add, zpow_neg, zpow_one]
    rw [h2, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hgj _

section Steps

variable [Finite X] {T : Sylow 2 X} {Z A B : Subgroup X} {L : Subgroup X} [L.Normal]

omit [Finite X] in
theorem normalized_of_center_le (hTA : TAmbient (T : Subgroup X) Z A B) {Q : Subgroup X}
    (hZQ : Z ≤ Q) (hQT : Q ≤ T) : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
  intro t ht q hq
  have h1 : t * q * t⁻¹ * q⁻¹ ∈ Z := hTA.comm_mem_Z t ht q (hQT hq)
  have := Q.mul_mem (hZQ h1) hq
  simpa using this

theorem ne_bot_of_center_le (hTA : TAmbient (T : Subgroup X) Z A B) {Q : Subgroup X}
    (hZQ : Z ≤ Q) : Q ≠ ⊥ := by
  intro h
  have h1 : Nat.card Z ≤ Nat.card Q := Subgroup.card_le_of_le hZQ
  rw [h, Subgroup.card_bot, hTA.card_Z] at h1
  omega

omit [Finite X] in
theorem normalizes_of_mem_nzr {Q : Subgroup X} : ∀ h ∈ nzr Q, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q :=
  fun _ hh q hq => (Subgroup.mem_normalizer_iff.1 hh q).1 hq

theorem map_conj_eq_A (hTA : TAmbient (T : Subgroup X) Z A B) {m : X}
    (hm : m ∈ normalizer ((T : Subgroup X) : Set X)) (hAD : A ≤ (T : Subgroup X) ⊓ L)
    (hBD : ¬ B ≤ (T : Subgroup X) ⊓ L) : A.map (MulAut.conj m).toMonoidHom = A := by
  set E : Subgroup X := A.map (MulAut.conj m).toMonoidHom with hE
  have hET : E ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hm a).1 (hTA.A_le_S ha)
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show m * a * m⁻¹ * (m * a * m⁻¹) = 1
    calc m * a * m⁻¹ * (m * a * m⁻¹) = m * (a * a) * m⁻¹ := by group
      _ = 1 := by rw [hTA.A_sq a ha]; group
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show m * a * m⁻¹ * (m * b * m⁻¹) = m * b * m⁻¹ * (m * a * m⁻¹)
    calc m * a * m⁻¹ * (m * b * m⁻¹) = m * (a * b) * m⁻¹ := by group
      _ = m * (b * a) * m⁻¹ := by rw [hTA.A_abel a ha b hb]
      _ = m * b * m⁻¹ * (m * a * m⁻¹) := by group
  have hEcard : Nat.card E = 16 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj m).injective, hTA.card_A]
  rcases hTA.elemAb_le E hET hEsq hEcomm with hEA | hEB
  · exact Subgroup.eq_of_le_of_card_ge hEA (by rw [hTA.card_A, hEcard])
  · exfalso
    have hEB' : E = B := Subgroup.eq_of_le_of_card_ge hEB (by rw [hTA.card_B, hEcard])
    apply hBD
    rw [← hEB']
    rintro _ ⟨a, ha, rfl⟩
    exact inf_normal_mem_of_normalizer hm (hAD ha)

theorem commute_of_mem_oddCore {Q T : Subgroup X} (hT2 : IsPGroup 2 T) (hTH : T ≤ nzr Q) {n : X}
    (hnT : n ∈ normalizer (T : Set X)) (hnK : n ∈ oddCoreIn (nzr Q)) :
    ∀ s ∈ T, n * s * n⁻¹ = s := by
  intro s hs
  have hT' : n * s * n⁻¹ * s⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.1 hnT s).1 hs) (T.inv_mem hs)
  have hK' : n * s * n⁻¹ * s⁻¹ ∈ oddCoreIn (nzr Q) := by
    have h1 := conj_mem_oddCoreIn (hTH hs) ((oddCoreIn (nzr Q)).inv_mem hnK)
    have := (oddCoreIn (nzr Q)).mul_mem hnK h1
    simpa [mul_assoc] using this
  have h1 := eq_one_of_mem_inf_oddCore hT2 hT' hK'
  calc n * s * n⁻¹ = (n * s * n⁻¹ * s⁻¹) * s := by group
    _ = s := by rw [h1, one_mul]

theorem frob_step (hS2 : O2Structure) (hT : IsT (T : Subgroup X))
    (hTA : TAmbient (T : Subgroup X) Z A B) {Q : Subgroup X} (hZQ : Z ≤ Q)
    (hQD : Q ≤ (T : Subgroup X) ⊓ L) (hAD : ¬ A ≤ (T : Subgroup X) ⊓ L)
    (hBD : ¬ B ≤ (T : Subgroup X) ⊓ L) {x : X} (hxL : x ∈ L) (hxN : x ∈ nzr Q)
    (hxodd : Odd (orderOf x)) : ∀ q ∈ Q, x * q * x⁻¹ = q := by
  have hQT : Q ≤ T := fun q hq => (hQD hq).1
  have hQ2 : IsPGroup 2 Q := T.isPGroup'.to_le hQT
  have hZD : Z ≤ (T : Subgroup X) ⊓ L := hZQ.trans hQD
  rcases localStructure hS2 T hT hTA Q (ne_bot_of_center_le hTA hZQ) hQT
    (normalized_of_center_le hTA hZQ hQT) with halt | ⟨hQAB, -⟩
  · obtain ⟨m, hmT, hmH, k, hk, hxmk⟩ := halt x hxN
    have hKn : ∀ h ∈ nzr Q, ∀ k ∈ oddCoreIn (nzr Q), h * k * h⁻¹ ∈ oddCoreIn (nzr Q) :=
      fun h hh k hk => conj_mem_oddCoreIn hh hk
    have hKodd : ∀ k ∈ oddCoreIn (nzr Q), Odd (orderOf k) := fun k hk =>
      odd_orderOf_of_mem_oddCore hk
    have hTH : (T : Subgroup X) ≤ nzr Q := le_nzr_of_normalizes
      (normalized_of_center_le hTA hZQ hQT)
    have hmjK : m ^ (orderOf x) ∈ oddCoreIn (nzr Q) :=
      pow_mem_of_pow_mul_eq_one hKn hmH hk _ (by rw [← hxmk]; exact pow_orderOf_eq_one x)
    have hmj : ∀ s ∈ (T : Subgroup X), m ^ (orderOf x) * s * (m ^ (orderOf x))⁻¹ = s :=
      commute_of_mem_oddCore T.isPGroup' hTH (pow_mem hmT _) hmjK
    have hD : ∀ s ∈ (T : Subgroup X), m * s * m⁻¹ * s⁻¹ ∈ (T : Subgroup X) ⊓ L := fun s hs =>
      comm_mem_inf T.isPGroup' hTH hKn hKodd hxL hxN hk hxmk.symm hmT hs
    have key := oa_trivial hT hTA hmT hxodd hmj hZD hAD hBD hD
    intro q hq
    have h1 := oddCoreIn_centralizes hQ2 Subgroup.le_normalizer normalizes_of_mem_nzr hk hq
    calc x * q * x⁻¹ = m * (k * q * k⁻¹) * m⁻¹ := by rw [hxmk]; group
      _ = m * q * m⁻¹ := by rw [h1]
      _ = q := key q (hQT hq)
  · exfalso
    rcases hQAB with rfl | rfl
    · exact hAD hQD
    · exact hBD hQD

theorem u1_step (hS2 : O2Structure) (hT : IsT (T : Subgroup X))
    (hTA : TAmbient (T : Subgroup X) Z A B) {Q : Subgroup X} (hZQ : Z ≤ Q)
    (hQD : Q ≤ (T : Subgroup X) ⊓ L) (hAD : A ≤ (T : Subgroup X) ⊓ L)
    (hBD : ¬ B ≤ (T : Subgroup X) ⊓ L) {w n : X} (hwQ : w ∈ Q) (hwA : w ∉ A)
    (hnN : n ∈ nzr Q) : n⁻¹ * w * n ∈ (T : Subgroup X) ⊓ L ∧ n⁻¹ * w * n ∉ A := by
  have hQT : Q ≤ T := fun q hq => (hQD hq).1
  have hQ2 : IsPGroup 2 Q := T.isPGroup'.to_le hQT
  rcases localStructure hS2 T hT hTA Q (ne_bot_of_center_le hTA hZQ) hQT
    (normalized_of_center_le hTA hZQ hQT) with halt | ⟨hQAB, -⟩
  · obtain ⟨m, hmT, hmH, k, hk, hxmk⟩ := halt n⁻¹ ((nzr Q).inv_mem hnN)
    have h1 := oddCoreIn_centralizes hQ2 Subgroup.le_normalizer normalizes_of_mem_nzr hk hwQ
    have hconj : n⁻¹ * w * n = m * w * m⁻¹ := by
      have h2 : n⁻¹ * w * n = (m * k) * w * (m * k)⁻¹ := by rw [← hxmk]; simp
      rw [h2]
      calc (m * k) * w * (m * k)⁻¹ = m * (k * w * k⁻¹) * m⁻¹ := by group
        _ = m * w * m⁻¹ := by rw [h1]
    have hA' := map_conj_eq_A hTA hmT hAD hBD
    rw [hconj]
    refine ⟨inf_normal_mem_of_normalizer hmT (hQD hwQ), fun hmw => hwA ?_⟩
    have : m * w * m⁻¹ ∈ A.map (MulAut.conj m).toMonoidHom := by rw [hA']; exact hmw
    obtain ⟨a, ha, hmwa⟩ := this
    have : a = w := by
      have h2 : m * a * m⁻¹ = m * w * m⁻¹ := hmwa
      simpa using h2
    rw [← this]
    exact ha
  · exfalso
    rcases hQAB with rfl | rfl
    · exact hwA hwQ
    · exact hBD hQD

theorem abel_step (hS2 : O2Structure) (hT : IsT (T : Subgroup X))
    (hTA : TAmbient (T : Subgroup X) Z A B) (hAD : A = (T : Subgroup X) ⊓ L) {g : X}
    (hgL : g ∈ L) (hgN : g ∈ nzr A) :
    (∀ a ∈ A, g * a * g⁻¹ = a) ∨
      ((∀ a ∈ A, g * a * g⁻¹ = a → a = 1) ∧ ∀ a ∈ A, g ^ 3 * a * (g ^ 3)⁻¹ = a) := by
  have hAT : A ≤ T := hTA.A_le_S
  have hZA : Z ≤ A := hTA.Z_le_A
  have hAL : A ≤ L := hAD ▸ inf_le_right
  have hA2 : IsPGroup 2 A := T.isPGroup'.to_le hAT
  have hidx : ¬ 2 ∣ A.relIndex L := by
    rw [hAD]
    exact CFSG.OddStandard.ThmC.O2.sylow_inf_normal_relIndex_odd T L
  obtain ⟨j, hj, hgj⟩ := exists_odd_pow_mem hAL hidx hgL hgN
  rcases localStructure hS2 T hT hTA A (ne_bot_of_center_le hTA hZA) hAT
    (normalized_of_center_le hTA hZA hAT) with halt | ⟨-, halt2⟩
  · obtain ⟨g', hg'z, ⟨j', hj', hg'j'⟩, hgg'⟩ := exists_odd_part hA2 hj hgj
    have hg'L : g' ∈ L := (Subgroup.zpowers_le.2 hgL) hg'z
    have hg'N : g' ∈ nzr A := (Subgroup.zpowers_le.2 hgN) hg'z
    obtain ⟨m, hmT, hmH, k, hk, hg'mk⟩ := halt g' hg'N
    have hKn : ∀ h ∈ nzr A, ∀ k ∈ oddCoreIn (nzr A), h * k * h⁻¹ ∈ oddCoreIn (nzr A) :=
      fun h hh k hk => conj_mem_oddCoreIn hh hk
    have hKodd : ∀ k ∈ oddCoreIn (nzr A), Odd (orderOf k) := fun k hk =>
      odd_orderOf_of_mem_oddCore hk
    have hTH : (T : Subgroup X) ≤ nzr A := le_nzr_of_normalizes
      (normalized_of_center_le hTA hZA hAT)
    have hmjK : m ^ j' ∈ oddCoreIn (nzr A) :=
      pow_mem_of_pow_mul_eq_one hKn hmH hk _ (by rw [← hg'mk]; exact hg'j')
    have hmj : ∀ s ∈ (T : Subgroup X), m ^ j' * s * (m ^ j')⁻¹ = s :=
      commute_of_mem_oddCore T.isPGroup' hTH (pow_mem hmT _) hmjK
    have hD : ∀ s ∈ (T : Subgroup X), m * s * m⁻¹ * s⁻¹ ∈ A := fun s hs => by
      rw [hAD]
      exact comm_mem_inf T.isPGroup' hTH hKn hKodd hg'L hg'N hk hg'mk.symm hmT hs
    obtain ⟨hact, hcube⟩ := oa_cube hT hTA hmT hj' hmj hD
    have hag' : ∀ x ∈ A, g' * x * g'⁻¹ = m * x * m⁻¹ := fun x hx => by
      have h1 := oddCoreIn_centralizes hA2 Subgroup.le_normalizer normalizes_of_mem_nzr hk hx
      calc g' * x * g'⁻¹ = m * (k * x * k⁻¹) * m⁻¹ := by rw [hg'mk]; group
        _ = m * x * m⁻¹ := by rw [h1]
    have hagg : ∀ x ∈ A, g * x * g⁻¹ = g' * x * g'⁻¹ := fun x hx => by
      have hy : g' * x * g'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg'N x).1 hx
      have h1 := hTA.A_abel _ hgg' _ hy
      calc g * x * g⁻¹ = (g * g'⁻¹) * (g' * x * g'⁻¹) * (g * g'⁻¹)⁻¹ := by group
        _ = g' * x * g'⁻¹ := by
          rw [h1]; group
    have hagm : ∀ x ∈ A, g * x * g⁻¹ = m * x * m⁻¹ := fun x hx => (hagg x hx).trans (hag' x hx)
    have hag3 : ∀ x ∈ A, g ^ 3 * x * (g ^ 3)⁻¹ = x := fun x hx => by
      rw [conj_pow_agree hgN hagm 3 x hx]
      exact hcube x (hAT hx)
    rcases hact with h | h
    · left
      intro a ha
      rw [hagm a ha]
      exact h a ha
    · right
      refine ⟨fun a ha hga => h a ha ?_, hag3⟩
      rw [← hagm a ha]
      exact hga
  · refine halt2 (nzr A ⊓ L) inf_le_left ?_ (le_inf Subgroup.le_normalizer hAL) ?_ g ⟨hgN, hgL⟩
    · intro h hh n hn
      exact ⟨(nzr A).mul_mem ((nzr A).mul_mem hh hn.1) ((nzr A).inv_mem hh),
        Normal.conj_mem inferInstance n hn.2 h⟩
    · intro n hn
      exact exists_odd_pow_mem hAL hidx hn.2 hn.1

end Steps


end CFSG.OddStandard.ThmC.Core
