module

public import CFSG.GH74.Uniqueness.Section15Derived
public import CFSG.GH74.Uniqueness.Section15Aux

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem isPGroup_zpowers_iff {p : ℕ} {x : X} :
    IsPGroup p (zpowers x) ↔ ∃ k : ℕ, x ^ (p ^ k) = 1 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h ⟨x, mem_zpowers x⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩ ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

omit [Finite X] in
private theorem isPGroup_zpowers_conj_mul {p : ℕ} {x : X} (g : X) (h : IsPGroup p (zpowers x)) :
    IsPGroup p (zpowers (g * x * g⁻¹)) := by
  have h' := isPGroup_zpowers_conj h g⁻¹
  rwa [inv_inv] at h'

omit [Finite X] in
private theorem isPGroup_zpowers_of_mem {p : ℕ} {H : Subgroup X} (hH : IsPGroup p H) {x : X}
    (hx : x ∈ H) : IsPGroup p (zpowers x) := hH.to_le (Subgroup.zpowers_le.mpr hx)

omit [Finite X] in
private theorem eq_one_of_two_pow_of_odd {H : Subgroup X} (hH : Odd (Nat.card H)) {x : X}
    (hx : x ∈ H) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hx
  have h3 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hH)) h1 h2
  exact orderOf_eq_one_iff.mp h3

omit [Finite X] in
private theorem exists_two_pow_of_mem {H : Subgroup X} (hH : IsPGroup 2 H) {x : X} (hx : x ∈ H) :
    ∃ k : ℕ, x ^ (2 ^ k) = 1 :=
  isPGroup_zpowers_iff.mp (isPGroup_zpowers_of_mem hH hx)

private structure FrobSplit (J U Y : Subgroup X) : Prop where
  U_le : U ≤ J
  Y_le : Y ≤ J
  U_pgroup : IsPGroup 2 U
  U_two : ∀ j ∈ J, IsPGroup 2 (zpowers j) → j ∈ U
  U_sq : ∀ x ∈ U, x * x = 1
  Y_odd : Odd (Nat.card Y)
  Y_comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a
  J_eq : ∀ j ∈ J, ∃ x ∈ U, ∃ y ∈ Y, j = x * y
  fpf : ∀ y ∈ Y, y ≠ 1 → ∀ x ∈ U, y * x = x * y → x = 1

namespace FrobSplit

variable {J U Y : Subgroup X}

omit [Finite X] in
private theorem U_normal (S : FrobSplit J U Y) : ∀ j ∈ J, ∀ x ∈ U, j * x * j⁻¹ ∈ U := by
  intro j hj x hx
  exact S.U_two _ (mul_mem (mul_mem hj (S.U_le hx)) (inv_mem hj))
    (isPGroup_zpowers_conj_mul j (isPGroup_zpowers_of_mem S.U_pgroup hx))

omit [Finite X] in
private theorem U_inf_Y (S : FrobSplit J U Y) : ∀ z ∈ U, z ∈ Y → z = 1 := by
  intro z hzU hzY
  by_contra hz1
  exact hz1 (S.fpf z hzY hz1 z hzU rfl)

omit [Finite X] in
private theorem card_J (S : FrobSplit J U Y) : Nat.card J = Nat.card U * Nat.card Y := by
  have hsup : U ⊔ Y = J := by
    apply le_antisymm (sup_le S.U_le S.Y_le)
    intro j hj
    obtain ⟨x, hx, y, hy, rfl⟩ := S.J_eq j hj
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
  rw [← hsup]
  refine card_sup_of_normal (fun d hd x hx => S.U_normal d (S.Y_le hd) x hx) ?_
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  exact S.U_inf_Y z hz.1 hz.2

omit [Finite X] in
private theorem cent_of_normalizes (S : FrobSplit J U Y) {Mo : Subgroup X}
    (hJMo : ∀ j ∈ J, ∀ m ∈ Mo, j * m = m * j)
    {Q : Subgroup X} (hQY : Q ≤ Y) (hQne : Q ≠ ⊥) {m j : X} (hm : m ∈ Mo) (hj : j ∈ J)
    (hgQ : ∀ a ∈ Q, (m * j) * a * (m * j)⁻¹ ∈ Q) : ∀ a ∈ Q, (m * j) * a = a * (m * j) := by
  intro a ha
  have hjQ : ∀ b ∈ Q, j * b * j⁻¹ ∈ Q := by
    intro b hb
    have h1 := hgQ b hb
    have hb' : j * b * j⁻¹ ∈ J := mul_mem (mul_mem hj (S.Y_le (hQY hb))) (inv_mem hj)
    have hcomm := hJMo _ hb' m hm
    have e : (m * j) * b * (m * j)⁻¹ = j * b * j⁻¹ := by
      calc (m * j) * b * (m * j)⁻¹ = m * (j * b * j⁻¹) * m⁻¹ := by group
        _ = ((j * b * j⁻¹) * m) * m⁻¹ := by rw [← hcomm]
        _ = j * b * j⁻¹ := by group
    rwa [e] at h1
  obtain ⟨x, hxU, y, hyY, rfl⟩ := S.J_eq j hj
  have hxQ : ∀ b ∈ Q, x * b * x⁻¹ ∈ Q := by
    intro b hb
    have h1 := hjQ b hb
    have hyb : y * b * y⁻¹ = b := by
      have := S.Y_comm y hyY b (hQY hb)
      calc y * b * y⁻¹ = b * y * y⁻¹ := by rw [this]
        _ = b := by group
    have e : x * y * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ := by group
    rw [e, hyb] at h1
    exact h1
  have hxcomm : ∀ b ∈ Q, x * b = b * x := by
    intro b hb
    have hq : x * b * x⁻¹ * b⁻¹ ∈ Q := mul_mem (hxQ b hb) (inv_mem hb)
    have hu : x * b * x⁻¹ * b⁻¹ ∈ U := by
      have : b * x⁻¹ * b⁻¹ ∈ U := S.U_normal b (S.Y_le (hQY hb)) x⁻¹ (inv_mem hxU)
      have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [e]
      exact mul_mem hxU this
    have h1 := S.U_inf_Y _ hu (hQY hq)
    calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
      _ = b * x := by rw [h1, one_mul]
  have hx1 : x = 1 := by
    obtain ⟨a₀, ha₀Q, ha₀1⟩ : ∃ a₀ ∈ Q, a₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hQne
      rw [eq_bot_iff]
      intro z hz
      rw [mem_bot]
      exact hcon z hz
    exact S.fpf a₀ (hQY ha₀Q) ha₀1 x hxU (hxcomm a₀ ha₀Q).symm
  subst hx1
  have hma : m * a = a * m := (hJMo a (S.Y_le (hQY ha)) m hm).symm
  have hya : y * a = a * y := S.Y_comm y hyY a (hQY ha)
  calc m * (1 * y) * a = m * (y * a) := by group
    _ = m * (a * y) := by rw [hya]
    _ = (m * a) * y := by group
    _ = (a * m) * y := by rw [hma]
    _ = a * (m * (1 * y)) := by group

end FrobSplit

namespace Facts15

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V : Subgroup X} {U Y : Subgroup X}

omit [Finite X] in
private theorem normalizer_cent (F : Facts15 M n L D K J Mo V) (S : FrobSplit J U Y)
    {Q : Subgroup X} (hQY : Q ≤ Y) {g : X} (hgC : g ∈ centralizer (Mo : Set X))
    (hgN : g ∈ normalizer (Q : Set X)) : ∀ a ∈ Q, g * a = a * g := by
  by_cases hQ : Q = ⊥
  · intro a ha
    rw [hQ, mem_bot] at ha
    subst ha
    simp
  · have hgL : g ∈ normalizer (L : Set X) := F.NY_le Q (hQY.trans S.Y_le) hQ hgN
    obtain ⟨m, hm, j, hj, rfl⟩ := F.cent_Mo_N g hgL
      (fun x hx => (mem_centralizer_iff.mp hgC x hx).symm)
    exact S.cent_of_normalizes (fun j hj m hm => F.J_comm_Mo hj hm) hQY hQ hm hj
      (fun a ha => (mem_normalizer_iff.mp hgN a).mp ha)

private theorem normalizer_C0_le_centralizer (F : Facts15 M n L D K J Mo V)
    (S : FrobSplit J U Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hPC : P ≤ centralizer (Mo : Set X)) (hPp : IsPGroup p P)
    (hPidx : ¬ p ∣ P.relIndex (centralizer (Mo : Set X))) :
    normalizer (P : Set X) ⊓ centralizer (Mo : Set X) ≤ centralizer (P : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hYC : Y ≤ centralizer (Mo : Set X) := S.Y_le.trans F.J_le_C0
  have hidxY : Y.relIndex (centralizer (Mo : Set X)) ∣ 2 ^ (3 * n) * Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card Y (centralizer (Mo : Set X))
    rw [inf_eq_left.mpr hYC] at h1
    have h2 := F.card_C0_dvd
    rw [S.card_J, ← h1] at h2
    have hYpos : 0 < Nat.card Y := Nat.card_pos
    refine Nat.dvd_of_mul_dvd_mul_right hYpos ?_
    calc Y.relIndex (centralizer (Mo : Set X)) * Nat.card Y
        ∣ 2 ^ (3 * n) * (Nat.card U * Nat.card Y) := h2
      _ = 2 ^ (3 * n) * Nat.card U * Nat.card Y := by ring
  obtain ⟨PY, hPY⟩ := CFSG.ABGLocalTools.exists_isSylowOf p Y
  have hPYC : CFSG.ABGLocalTools.IsSylowOf p PY (centralizer (Mo : Set X)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hPY.le.trans hYC, hPY.isPGroup, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex PY Y _ hPY.le hYC]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hPY).2.2 h1
    · obtain ⟨k, hk⟩ := S.U_pgroup.exists_card_eq
      have h2 : p ∣ 2 ^ (3 * n) * Nat.card U := h1.trans hidxY
      rw [hk, ← pow_add] at h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  have hPC' : CFSG.ABGLocalTools.IsSylowOf p P (centralizer (Mo : Set X)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPC, hPp, hPidx⟩
  obtain ⟨k, hkC, hk⟩ := hPYC.exists_mem_conj hPC'
  intro g hg
  obtain ⟨hgN, hgC⟩ := mem_inf.mp hg
  have hgN' := mem_normalizer_iff.mp hgN
  have hg'C : k⁻¹ * g * k ∈ centralizer (Mo : Set X) := mul_mem (mul_mem (inv_mem hkC) hgC) hkC
  have hg'N : k⁻¹ * g * k ∈ normalizer (PY : Set X) := by
    rw [mem_normalizer_iff]
    intro a
    have h1 : a ∈ PY ↔ k * a * k⁻¹ ∈ P := by
      rw [hk (k * a * k⁻¹)]
      have : k⁻¹ * (k * a * k⁻¹) * k = a := by group
      rw [this]
    have h2 : (k⁻¹ * g * k) * a * (k⁻¹ * g * k)⁻¹ ∈ PY ↔ g * (k * a * k⁻¹) * g⁻¹ ∈ P := by
      rw [hk (g * (k * a * k⁻¹) * g⁻¹)]
      have : k⁻¹ * (g * (k * a * k⁻¹) * g⁻¹) * k = (k⁻¹ * g * k) * a * (k⁻¹ * g * k)⁻¹ := by
        group
      rw [this]
    rw [h1, h2]
    exact hgN' (k * a * k⁻¹)
  have hcomm := F.normalizer_cent S hPY.le hg'C hg'N
  rw [mem_centralizer_iff]
  intro x hx
  have h := hcomm (k⁻¹ * x * k) ((hk x).mp hx)
  have e1 : x * g = k * ((k⁻¹ * x * k) * (k⁻¹ * g * k)) * k⁻¹ := by group
  have e2 : g * x = k * ((k⁻¹ * g * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
  rw [e1, e2, h]

private theorem mem_V_of_isPGroup (F : Facts15 M n L D K J Mo V) (S : FrobSplit J U Y) :
    ∀ g ∈ centralizer (Mo : Set X), IsPGroup 2 (zpowers g) → g ∈ V := by
  obtain ⟨T, hTC, hTp, hT2, -⟩ := exists_normal_sylow_two (C := centralizer (Mo : Set X))
    (fun p hp hp2 P hPC hPp hPidx => F.normalizer_C0_le_centralizer S hp hp2 hPC hPp hPidx)
  have hTM : ∀ m ∈ M, ∀ x ∈ T, m * x * m⁻¹ ∈ T := by
    intro m hm x hx
    exact hT2 _ (F.C0_conj hm (hTC hx))
      (isPGroup_zpowers_conj_mul m (isPGroup_zpowers_of_mem hTp hx))
  have hTV : T ≤ V := F.V_max T (hTC.trans F.cent_Mo_le) hTM hTp
  intro g hg hg2
  exact hTV (hT2 g hg hg2)

private theorem C0_eq_V_mul_Y (F : Facts15 M n L D K J Mo V) (S : FrobSplit J U Y) :
    ∀ g ∈ centralizer (Mo : Set X), ∃ v ∈ V, ∃ y ∈ Y, g = v * y := by
  classical
  have hV := F.mem_V_of_isPGroup S
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYC : Y ≤ centralizer (Mo : Set X) := S.Y_le.trans F.J_le_C0
  obtain ⟨P₂, hP₂⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (centralizer (Mo : Set X))
  have hP₂V : P₂ ≤ V := fun x hx => hV x (hP₂.le hx) (isPGroup_zpowers_of_mem hP₂.isPGroup hx)
  have hVP₂ : V = P₂ := hP₂.eq_of_le hP₂V F.V_le_C0 F.V_pgroup
  have hVsyl : CFSG.ABGLocalTools.IsSylowOf 2 V (centralizer (Mo : Set X)) := hVP₂ ▸ hP₂
  have hidx : ¬ 2 ∣ V.relIndex (centralizer (Mo : Set X)) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hVsyl).2.2
  have hcard : V.relIndex (centralizer (Mo : Set X)) * Nat.card V =
      Nat.card (centralizer (Mo : Set X)) := by
    have := Subgroup.relIndex_mul_card V (centralizer (Mo : Set X))
    rwa [inf_eq_left.mpr F.V_le_C0] at this
  obtain ⟨k, hk⟩ := S.U_pgroup.exists_card_eq
  have hdvd : V.relIndex (centralizer (Mo : Set X)) ∣ Nat.card Y := by
    have h1 : V.relIndex (centralizer (Mo : Set X)) ∣ Nat.card (centralizer (Mo : Set X)) :=
      ⟨Nat.card V, hcard.symm⟩
    have h3 := F.card_C0_dvd
    rw [S.card_J, hk] at h3
    have h4 : V.relIndex (centralizer (Mo : Set X)) ∣ 2 ^ (3 * n + k) * Nat.card Y := by
      have : 2 ^ (3 * n) * (2 ^ k * Nat.card Y) = 2 ^ (3 * n + k) * Nat.card Y := by ring
      rw [this] at h3
      exact h1.trans h3
    have hcop : Nat.Coprime (V.relIndex (centralizer (Mo : Set X))) (2 ^ (3 * n + k)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx).symm
    exact hcop.dvd_of_dvd_mul_left h4
  have hle : Nat.card (centralizer (Mo : Set X)) ≤ Nat.card V * Nat.card Y := by
    rw [← hcard, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.le_of_dvd Nat.card_pos hdvd)
  let f : ↥V × ↥Y → ↥(centralizer (Mo : Set X)) := fun q =>
    ⟨(q.1 : X) * q.2, mul_mem (F.V_le_C0 q.1.2) (hYC q.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨v, hv⟩, ⟨y, hy⟩⟩ ⟨⟨v', hv'⟩, ⟨y', hy'⟩⟩ h
    have h' : v * y = v' * y' := congrArg Subtype.val h
    have hz : v'⁻¹ * v = y' * y⁻¹ := by
      calc v'⁻¹ * v = v'⁻¹ * (v * y) * y⁻¹ := by group
        _ = v'⁻¹ * (v' * y') * y⁻¹ := by rw [h']
        _ = y' * y⁻¹ := by group
    have hzV : v'⁻¹ * v ∈ V := mul_mem (inv_mem hv') hv
    have hzY : v'⁻¹ * v ∈ Y := by rw [hz]; exact mul_mem hy' (inv_mem hy)
    obtain ⟨a, ha⟩ := exists_two_pow_of_mem F.V_pgroup hzV
    have hz1 : v'⁻¹ * v = 1 := eq_one_of_two_pow_of_odd S.Y_odd hzY ha
    have hvv : v = v' := by
      calc v = v' * (v'⁻¹ * v) := by group
        _ = v' := by rw [hz1, mul_one]
    subst hvv
    have hyy : y = y' := mul_left_cancel h'
    subst hyy
    rfl
  have hbij := hinj.bijective_of_nat_card_le (by rwa [Nat.card_prod])
  intro g hg
  obtain ⟨⟨v, y⟩, hvy⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨v, v.2, y, y.2, (congrArg Subtype.val hvy).symm⟩

private theorem V_inf_D (F : Facts15 M n L D K J Mo V) (S : FrobSplit J U Y) : V ⊓ D = U := by
  have hV := F.mem_V_of_isPGroup S
  apply le_antisymm
  · intro d hd
    obtain ⟨hdV, hdD⟩ := mem_inf.mp hd
    have hcomm : ∀ k ∈ K, d * k = k * d := by
      intro k hk
      have h1 : d * k * d⁻¹ ∈ K := F.D_conj_K hdD hk
      have h2 : k * d⁻¹ * k⁻¹ ∈ V := F.V_normal k (F.K_le_M hk) d⁻¹ (inv_mem hdV)
      have hcK : d * k * d⁻¹ * k⁻¹ ∈ K := mul_mem h1 (inv_mem hk)
      have hcV : d * k * d⁻¹ * k⁻¹ ∈ V := by
        have e : d * k * d⁻¹ * k⁻¹ = d * (k * d⁻¹ * k⁻¹) := by group
        rw [e]
        exact mul_mem hdV h2
      obtain ⟨a, ha⟩ := exists_two_pow_of_mem F.V_pgroup hcV
      have hc1 := eq_one_of_two_pow_of_odd F.odd_card_K hcK ha
      calc d * k = (d * k * d⁻¹ * k⁻¹) * (k * d) := by group
        _ = k * d := by rw [hc1, one_mul]
    obtain ⟨k, hk, j, hj, hd'⟩ := F.cent_K_D d hdD hcomm
    obtain ⟨a, ha⟩ := exists_two_pow_of_mem F.V_pgroup hdV
    have hkj : Commute k j := (F.J_comm hj (F.K_le_L hk)).symm
    rw [hd', hkj.mul_pow] at ha
    have h1 : k ^ (2 ^ a) = (j ^ (2 ^ a))⁻¹ := eq_inv_of_mul_eq_one_left ha
    have hk1 : k ^ (2 ^ a) = 1 :=
      F.eq_one_of_mem_K_J (pow_mem hk _) (by rw [h1]; exact inv_mem (pow_mem hj _))
    have hk1' : k = 1 := eq_one_of_two_pow_of_odd F.odd_card_K hk hk1
    rw [hk1', one_mul] at hd'
    rw [hd']
    refine S.U_two j hj ?_
    rw [← hd']
    exact isPGroup_zpowers_of_mem F.V_pgroup hdV
  · intro u hu
    exact mem_inf.mpr ⟨hV u (F.J_le_C0 (S.U_le hu)) (isPGroup_zpowers_of_mem S.U_pgroup hu),
      F.J_le_D (S.U_le hu)⟩

private theorem inv_mem_U (F : Facts15 M n L D K J Mo V) (S : FrobSplit J U Y) :
    ∀ d ∈ D, orderOf d = 2 → d ∈ U := by
  intro d hd hd2
  have hdC : d ∈ centralizer (Mo : Set X) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact (F.inv_comm d hd hd2 x hx).symm
  have hd2' : IsPGroup 2 (zpowers d) := isPGroup_zpowers_iff.mpr ⟨1, by
    rw [pow_one]
    have := pow_orderOf_eq_one d
    rwa [hd2] at this⟩
  have hdV : d ∈ V := F.mem_V_of_isPGroup S d hdC hd2'
  rw [← F.V_inf_D S]
  exact mem_inf.mpr ⟨hdV, hd⟩

omit [Finite X] in
private theorem mem_normalizer_of_conj (F : Facts15 M n L D K J Mo V) (S : FrobSplit J U Y) :
    ∀ g : X, (∃ x ∈ U, x ≠ 1 ∧ g * x * g⁻¹ ∈ U) → g ∈ normalizer (L : Set X) := by
  rintro g ⟨x, hxU, hx1, hgx⟩
  have hxD : x ∈ D := F.J_le_D (S.U_le hxU)
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact S.U_sq x hxU) hx1
  exact F.inv_conj x hxD hx2 g (F.J_le_D (S.U_le hgx))

omit [Finite X] in
private theorem normalizer_le_normalizer_U (F : Facts15 M n L D K J Mo V) (S : FrobSplit J U Y) :
    normalizer (L : Set X) ≤ normalizer (U : Set X) := by
  have key : ∀ h ∈ normalizer (L : Set X), ∀ y ∈ U, h * y * h⁻¹ ∈ U := by
    intro h hh y hy
    refine S.U_two _ (F.N_conj_J hh (S.U_le hy)) ?_
    exact isPGroup_zpowers_conj_mul h (isPGroup_zpowers_of_mem S.U_pgroup hy)
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

end Facts15

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V : Subgroup X}

theorem Facts15.lemma155 (F : Facts15 M n L D K J Mo V) {U Y : Subgroup X}
    (hU : U ≤ J) (hY : Y ≤ J) (hUp : IsPGroup 2 U) (hU2 : ∀ j ∈ J, IsPGroup 2 (zpowers j) → j ∈ U)
    (hUsq : ∀ x ∈ U, x * x = 1) (hYodd : Odd (Nat.card Y)) (_hYdvd : Nat.card Y ∣ 2 ^ n - 1)
    (hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hJUY : ∀ j ∈ J, ∃ x ∈ U, ∃ y ∈ Y, j = x * y)
    (hfpf : ∀ y ∈ Y, y ≠ 1 → ∀ x ∈ U, y * x = x * y → x = 1) (_hUne : U ≠ ⊥) :
    (∀ g ∈ centralizer (Mo : Set X), IsPGroup 2 (zpowers g) → g ∈ V) ∧
    (∀ g ∈ centralizer (Mo : Set X), ∃ v ∈ V, ∃ y ∈ Y, g = v * y) ∧
    (∀ d ∈ D, orderOf d = 2 → d ∈ U) ∧
    V ⊓ D = U ∧
    (∀ g : X, (∃ x ∈ U, x ≠ 1 ∧ g * x * g⁻¹ ∈ U) → g ∈ normalizer (L : Set X)) ∧
    normalizer (L : Set X) ≤ normalizer (U : Set X) := by
  have S : FrobSplit J U Y := ⟨hU, hY, hUp, hU2, hUsq, hYodd, hYcomm, hJUY, hfpf⟩
  exact ⟨F.mem_V_of_isPGroup S, F.C0_eq_V_mul_Y S, F.inv_mem_U S, F.V_inf_D S,
    F.mem_normalizer_of_conj S, F.normalizer_le_normalizer_U S⟩

end CFSG.GH74.Uniqueness
