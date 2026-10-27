module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Basic

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma37

variable {G : Type*} [Group G]

structure Ctx (P S : Subgroup G) (t x : G) (T : Set G) : Prop where
  pgroup : IsPGroup 2 P
  le : S ≤ P
  sup_eq : P = S ⊔ zpowers t
  t_normalizer : t ∈ normalizer (S : Set G)
  t_sq : t ^ 2 = 1
  t_not_mem : t ∉ S
  x_mem : x ∈ S
  x_order : orderOf x = 4
  x_comm : x * t = t * x
  cent : ∀ s ∈ S, s * t = t * s → s ∈ zpowers x
  T_t : t ∈ T
  T_conj : ∀ p ∈ P, ∀ v ∈ T, p * v * p⁻¹ ∈ T
  T_sq : ∀ v ∈ T, v ^ 2 = 1
  T_not_mem : ∀ v ∈ T, v ∉ S
  T_unique : ∀ v ∈ T, ∀ w₁ ∈ S, ∀ w₂ ∈ S, w₁ ^ 2 = 1 → w₂ ^ 2 = 1 → w₁ ≠ 1 → w₂ ≠ 1 →
    w₁ * w₂ = w₂ * w₁ → v * w₁ = w₁ * v → v * w₂ = w₂ * v → w₁ = w₂

@[expose] def Good (S : Subgroup G) (t x ρ : G) (m : ℕ) : Prop :=
  2 ≤ m ∧ ρ ∈ S ∧ t * ρ * t⁻¹ = ρ⁻¹ ∧ ρ * x = x * ρ ∧ orderOf ρ = 2 ^ (m - 1) ∧
    ρ ^ 2 ^ (m - 2) = x ^ 2

namespace Ctx

variable {P S : Subgroup G} {t x : G} {T : Set G}

theorem t_inv (h : Ctx P S t x T) : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, h.t_sq]

theorem t_mul_t (h : Ctx P S t x T) : t * t = 1 := by rw [← pow_two, h.t_sq]

theorem t_mem (h : Ctx P S t x T) : t ∈ P := h.sup_eq ▸ mem_sup_right (mem_zpowers t)

theorem x_pow_four (h : Ctx P S t x T) : x ^ 4 = 1 := by
  rw [← h.x_order]; exact pow_orderOf_eq_one x

theorem x_sq_ne_one (h : Ctx P S t x T) : x ^ 2 ≠ 1 := by
  intro h2
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h.x_order] at this
  norm_num at this

theorem mem_P (h : Ctx P S t x T) {p : G} (hp : p ∈ P) : p ∈ S ∨ t⁻¹ * p ∈ S := by
  rw [h.sup_eq] at hp
  exact (mem_sup_zpowers_iff h.t_normalizer (by rw [h.t_sq]; exact one_mem S)).1 hp

theorem normal_P (h : Ctx P S t x T) {p : G} (hp : p ∈ P) : p ∈ normalizer (S : Set G) := by
  have hle : P ≤ normalizer (S : Set G) := by
    rw [h.sup_eq]
    exact sup_le le_normalizer (zpowers_le.2 h.t_normalizer)
  exact hle hp

theorem conj_mem_S (h : Ctx P S t x T) {p s : G} (hp : p ∈ P) (hs : s ∈ S) :
    p * s * p⁻¹ ∈ S :=
  (mem_normalizer_iff.1 (h.normal_P hp) s).1 hs

theorem t_mul_mem (h : Ctx P S t x T) {p : G} (hp : p ∈ P) (hpS : p ∉ S) : t * p ∈ S := by
  rcases h.mem_P hp with h1 | h1
  · exact absurd h1 hpS
  · rwa [h.t_inv] at h1

theorem conj_t_not_mem (h : Ctx P S t x T) {p : G} (hp : p ∈ P) : p * t * p⁻¹ ∉ S := by
  intro hs
  apply h.t_not_mem
  have := h.conj_mem_S (P.inv_mem hp) hs
  simpa [mul_assoc] using this

end Ctx

namespace Good

variable {P S : Subgroup G} {t x : G} {T : Set G} {ρ : G} {m : ℕ}

theorem conj_t_zpow (hg : Good S t x ρ m) (k : ℤ) :
    t * ρ ^ k * t⁻¹ = ρ ^ (-k) := by
  rw [← _root_.conj_zpow, hg.2.2.1, inv_zpow']

theorem conj_mem_zpowers (hg : Good S t x ρ m) {w : G}
    (hw : w ∈ zpowers ρ) : t * w * t⁻¹ = w⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  rw [hg.conj_t_zpow, zpow_neg]

theorem x_comm_zpow (hg : Good S t x ρ m) (k : ℤ) : ρ ^ k * x = x * ρ ^ k :=
  (Commute.zpow_left hg.2.2.2.1 k).eq

theorem x_comm_pow (hg : Good S t x ρ m) (k : ℕ) : ρ ^ k * x = x * ρ ^ k :=
  (Commute.pow_left hg.2.2.2.1 k).eq

theorem x_sq_mem (hg : Good S t x ρ m) : x ^ 2 ∈ zpowers ρ := by
  rw [← hg.2.2.2.2.2]
  exact pow_mem (mem_zpowers ρ) _

theorem x_not_mem (hc : Ctx P S t x T) (hg : Good S t x ρ m) : x ∉ zpowers ρ := by
  intro hx
  have h1 := hg.conj_mem_zpowers hx
  have h2 : t * x * t⁻¹ = x := by rw [← hc.x_comm]; group
  rw [h2] at h1
  apply hc.x_sq_ne_one
  rw [pow_two]
  nth_rewrite 1 [h1]
  exact inv_mul_cancel x

theorem x_normalizer (hg : Good S t x ρ m) : x ∈ normalizer (zpowers ρ : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  exact hg.x_comm_zpow k

theorem mem_M (hg : Good S t x ρ m) {g : G} :
    g ∈ zpowers ρ ⊔ zpowers x ↔ g ∈ zpowers ρ ∨ x⁻¹ * g ∈ zpowers ρ :=
  mem_sup_zpowers_iff hg.x_normalizer hg.x_sq_mem

theorem M_le (hc : Ctx P S t x T) (hg : Good S t x ρ m) : zpowers ρ ⊔ zpowers x ≤ S :=
  sup_le (zpowers_le.2 hg.2.1) (zpowers_le.2 hc.x_mem)

theorem card_zpowers (hg : Good S t x ρ m) [Finite G] :
    Nat.card (zpowers ρ) = 2 ^ (m - 1) := by
  rw [Nat.card_zpowers, hg.2.2.2.2.1]

theorem card_M [Finite G] (hc : Ctx P S t x T) (hg : Good S t x ρ m) :
    Nat.card (zpowers ρ ⊔ zpowers x : Subgroup G) = 2 ^ m := by
  rw [card_sup_zpowers hg.x_normalizer hg.x_sq_mem (hg.x_not_mem hc), hg.card_zpowers]
  obtain ⟨hm, -⟩ := hg
  rw [← pow_succ']
  congr 1
  omega

theorem x_comm_M (hg : Good S t x ρ m) {g : G} (hgM : g ∈ zpowers ρ ⊔ zpowers x) :
    g * x = x * g := by
  rcases hg.mem_M.1 hgM with h | h
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
    exact hg.x_comm_zpow k
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have : g = x * ρ ^ k := by rw [hk]; group
    rw [this, mul_assoc, hg.x_comm_zpow k]

theorem M_comm (hg : Good S t x ρ m) {g₁ g₂ : G} (h₁ : g₁ ∈ zpowers ρ ⊔ zpowers x)
    (h₂ : g₂ ∈ zpowers ρ ⊔ zpowers x) : g₁ * g₂ = g₂ * g₁ := by
  have hρ : ∀ (k : ℤ) (g : G), g ∈ zpowers ρ ⊔ zpowers x → ρ ^ k * g = g * ρ ^ k := by
    intro k g hg'
    rcases hg.mem_M.1 hg' with h | h
    · obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 h
      exact (Commute.zpow_zpow_self ρ k j).eq
    · obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h
      have : g = x * ρ ^ j := by rw [hj]; group
      rw [this]
      calc ρ ^ k * (x * ρ ^ j) = (ρ ^ k * x) * ρ ^ j := by group
        _ = (x * ρ ^ k) * ρ ^ j := by rw [hg.x_comm_zpow k]
        _ = x * (ρ ^ k * ρ ^ j) := by group
        _ = x * (ρ ^ j * ρ ^ k) := by rw [(Commute.zpow_zpow_self ρ k j).eq]
        _ = (x * ρ ^ j) * ρ ^ k := by group
  rcases hg.mem_M.1 h₁ with h | h
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
    exact hρ k g₂ h₂
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have : g₁ = x * ρ ^ k := by rw [hk]; group
    rw [this, mul_assoc, hρ k g₂ h₂, ← mul_assoc, (hg.x_comm_M h₂).symm, mul_assoc]

theorem t_conj_M (hc : Ctx P S t x T) (hg : Good S t x ρ m) {g : G}
    (hgM : g ∈ zpowers ρ ⊔ zpowers x) : t * g * t⁻¹ ∈ zpowers ρ ⊔ zpowers x := by
  have htx : t * x * t⁻¹ = x := by rw [← hc.x_comm]; group
  rcases hg.mem_M.1 hgM with h | h
  · rw [hg.conj_mem_zpowers h]
    exact mem_sup_left (inv_mem h)
  · have : g = x * (x⁻¹ * g) := by group
    rw [this]
    have : t * (x * (x⁻¹ * g)) * t⁻¹ = (t * x * t⁻¹) * (t * (x⁻¹ * g) * t⁻¹) := by group
    rw [this, htx, hg.conj_mem_zpowers h]
    exact mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left (inv_mem h))

theorem t_normalizer_M (hc : Ctx P S t x T) (hg : Good S t x ρ m) :
    t ∈ normalizer ((zpowers ρ ⊔ zpowers x : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨hg.t_conj_M hc, fun h => ?_⟩
  have := hg.t_conj_M hc h
  have e : t * (t * g * t⁻¹) * t⁻¹ = g := by
    rw [hc.t_inv]
    calc t * (t * g * t) * t = (t * t) * g * (t * t) := by group
      _ = g := by rw [hc.t_mul_t, one_mul, mul_one]
  rwa [e] at this

theorem t_not_mem_M (hc : Ctx P S t x T) (hg : Good S t x ρ m) :
    t ∉ zpowers ρ ⊔ zpowers x := fun h => hc.t_not_mem (hg.M_le hc h)

theorem mem_X (hc : Ctx P S t x T) (hg : Good S t x ρ m) {g : G} :
    g ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t ↔
      g ∈ zpowers ρ ⊔ zpowers x ∨ t⁻¹ * g ∈ zpowers ρ ⊔ zpowers x :=
  mem_sup_zpowers_iff (hg.t_normalizer_M hc) (by rw [hc.t_sq]; exact one_mem _)

theorem card_X [Finite G] (hc : Ctx P S t x T) (hg : Good S t x ρ m) :
    Nat.card ((zpowers ρ ⊔ zpowers x) ⊔ zpowers t : Subgroup G) = 2 ^ (m + 1) := by
  rw [card_sup_zpowers (hg.t_normalizer_M hc) (by rw [hc.t_sq]; exact one_mem _)
    (hg.t_not_mem_M hc), hg.card_M hc, pow_succ']

theorem X_le (hc : Ctx P S t x T) (hg : Good S t x ρ m) :
    (zpowers ρ ⊔ zpowers x) ⊔ zpowers t ≤ P :=
  sup_le ((hg.M_le hc).trans hc.le) (zpowers_le.2 hc.t_mem)

theorem x_comm_X (hc : Ctx P S t x T) (hg : Good S t x ρ m) {g : G}
    (hgX : g ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t) : g * x = x * g := by
  rcases (hg.mem_X hc).1 hgX with h | h
  · exact hg.x_comm_M h
  · have : g = t * (t⁻¹ * g) := by group
    rw [this, mul_assoc, hg.x_comm_M h, ← mul_assoc, ← hc.x_comm, mul_assoc]

theorem cent_le_X (hc : Ctx P S t x T) (hg : Good S t x ρ m) {p : G} (hp : p ∈ P)
    (hpt : p * t = t * p) : p ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t := by
  rcases hc.mem_P hp with h | h
  · exact mem_sup_left (mem_sup_right (zpowers_le.2 (mem_zpowers x) (hc.cent p h hpt)))
  · have hq : (t⁻¹ * p) * t = t * (t⁻¹ * p) := by
      calc (t⁻¹ * p) * t = t⁻¹ * (p * t) := by group
        _ = t⁻¹ * (t * p) := by rw [hpt]
        _ = t * (t⁻¹ * p) := by rw [hc.t_inv]
    have hqM : t⁻¹ * p ∈ zpowers ρ ⊔ zpowers x := mem_sup_right (hc.cent _ h hq)
    exact (hg.mem_X hc).2 (Or.inr hqM)

theorem involution_X (hc : Ctx P S t x T) (hg : Good S t x ρ m) {w : G}
    (hwX : w ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t) (hw2 : w ^ 2 = 1) (hwS : w ∉ S) :
    ∃ j : ℤ, w = t * ρ ^ j := by
  rcases (hg.mem_X hc).1 hwX with h | h
  · exact absurd (hg.M_le hc h) hwS
  · rcases hg.mem_M.1 h with h' | h'
    · obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h'
      exact ⟨j, by rw [hj]; group⟩
    · exfalso
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h'
      have hw : w = t * (x * ρ ^ j) := by rw [hj]; group
      apply hc.x_sq_ne_one
      have htx : t * x * t⁻¹ = x := by rw [← hc.x_comm]; group
      calc x ^ 2 = x * x * (ρ ^ (-j) * ρ ^ j) := by
            rw [← zpow_add, neg_add_cancel, zpow_zero, mul_one, pow_two]
        _ = x * (ρ ^ (-j) * x) * ρ ^ j := by rw [hg.x_comm_zpow (-j)]; group
        _ = (t * x * t⁻¹) * (t * ρ ^ j * t⁻¹) * (x * ρ ^ j) := by
            rw [htx, hg.conj_t_zpow]; group
        _ = t * (x * ρ ^ j) * t⁻¹ * (x * ρ ^ j) := by group
        _ = w ^ 2 := by rw [hw, pow_two, hc.t_inv]; group
        _ = 1 := hw2

theorem conj_reflection (hc : Ctx P S t x T) (hg : Good S t x ρ m) (j l : ℤ) :
    ρ ^ (-l) * (t * ρ ^ j) * (ρ ^ (-l))⁻¹ = t * ρ ^ (j + 2 * l) := by
  have h1 : ρ ^ (-l) * t = t * ρ ^ l := by
    have := hg.conj_t_zpow (-l)
    rw [neg_neg] at this
    calc ρ ^ (-l) * t = t * (t⁻¹ * ρ ^ (-l) * t) := by group
      _ = t * (t * ρ ^ (-l) * t⁻¹) := by rw [hc.t_inv]
      _ = t * ρ ^ l := by rw [this]
  calc ρ ^ (-l) * (t * ρ ^ j) * (ρ ^ (-l))⁻¹ = (ρ ^ (-l) * t) * (ρ ^ j * ρ ^ l) := by group
    _ = t * ρ ^ (j + 2 * l) := by
        rw [h1, mul_assoc, ← zpow_add, ← zpow_add]
        ring_nf

theorem mem_X_of_even (hc : Ctx P S t x T) (hg : Good S t x ρ m) {g : G} (hgP : g ∈ P)
    {j : ℤ} (hj : g * t * g⁻¹ = t * ρ ^ j) (heven : Even j) :
    g ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t := by
  obtain ⟨l, rfl⟩ := heven
  have hconj := hg.conj_reflection hc 0 l
  rw [zpow_zero, mul_one, zero_add] at hconj
  rw [← two_mul] at hj
  set k := ρ ^ l * g with hk
  have hkP : k ∈ P := P.mul_mem (zpow_mem (hc.le hg.2.1) l) hgP
  have hkt : k * t = t * k := by
    have h1 : k * t * k⁻¹ = t := by
      calc k * t * k⁻¹ = ρ ^ l * (g * t * g⁻¹) * ρ ^ (-l) := by rw [hk]; group
        _ = ρ ^ l * (ρ ^ (-l) * t * (ρ ^ (-l))⁻¹) * ρ ^ (-l) := by rw [hj, hconj]
        _ = t := by group
    calc k * t = (k * t * k⁻¹) * k := by group
      _ = t * k := by rw [h1]
  have hkX := hg.cent_le_X hc hkP hkt
  have : g = ρ ^ (-l) * k := by rw [hk]; group
  rw [this]
  exact mul_mem (mem_sup_left (mem_sup_left (zpow_mem (mem_zpowers ρ) _))) hkX

theorem conj_t_odd (hc : Ctx P S t x T) (hg : Good S t x ρ m) {v : G} (hvP : v ∈ P)
    (hvN : v ∈ normalizer (((zpowers ρ ⊔ zpowers x) ⊔ zpowers t : Subgroup G) : Set G))
    (hvX : v ∉ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t) :
    ∃ j : ℤ, Odd j ∧ v * t * v⁻¹ = t * ρ ^ j := by
  have htX : t ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hwX := (mem_normalizer_iff.1 hvN t).1 htX
  have hw2 : (v * t * v⁻¹) ^ 2 = 1 := by rw [conj_pow, hc.t_sq]; group
  obtain ⟨j, hj⟩ := hg.involution_X hc hwX hw2 (hc.conj_t_not_mem hvP)
  refine ⟨j, ?_, hj⟩
  rcases Int.even_or_odd j with he | ho
  · exact absurd (hg.mem_X_of_even hc hvP hj he) hvX
  · exact ho

theorem pow_of_sq (hc : Ctx P S t x T) (hg : Good S t x ρ m) {a : G} {j : ℤ} (hjodd : Odd j)
    (ha : a ^ 2 = ρ ^ j) : a ^ 2 ^ (m - 1) = x ^ 2 := by
  obtain ⟨hm, -, -, -, -, hρ⟩ := hg
  have hexp : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hexp, pow_mul, ha, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ]
  obtain ⟨k, rfl⟩ := hjodd
  rw [zpow_add, zpow_one, zpow_mul]
  have : (x ^ 2) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← pow_mul]
    exact hc.x_pow_four
  rw [this, one_zpow, one_mul]

theorem not_mem_T (hc : Ctx P S t x T)
    (hNG : ¬ ∃ y ∈ S, y ^ 2 = x ^ 2 ∧ t * y * t⁻¹ = y⁻¹ ∧ y * x * y⁻¹ = x⁻¹)
    (hg : Good S t x ρ m) (hmax : ∀ ρ' : G, ¬ Good S t x ρ' (m + 1)) {v : G} (hvP : v ∈ P)
    (hvN : v ∈ normalizer (((zpowers ρ ⊔ zpowers x) ⊔ zpowers t : Subgroup G) : Set G))
    (hvX : v ∉ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t) (hvT : v ∈ T) : False := by
  obtain ⟨j, hjodd, hj⟩ := hg.conj_t_odd hc hvP hvN hvX
  have hv2 : v ^ 2 = 1 := hc.T_sq v hvT
  have hvinv : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hv2]
  have hvS : v ∉ S := hc.T_not_mem v hvT
  have htX : t ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hvxS : v * x * v⁻¹ ∈ S := hc.conj_mem_S hvP hc.x_mem
  have hvxt : (v * x * v⁻¹) * t = t * (v * x * v⁻¹) := by
    have hw : v⁻¹ * t * v⁻¹⁻¹ ∈ (zpowers ρ ⊔ zpowers x) ⊔ zpowers t :=
      (mem_normalizer_iff.1 (inv_mem hvN) t).1 htX
    rw [inv_inv] at hw
    have h1 := hg.x_comm_X hc hw
    calc v * x * v⁻¹ * t = v * (x * (v⁻¹ * t * v)) * v⁻¹ := by group
      _ = v * ((v⁻¹ * t * v) * x) * v⁻¹ := by rw [h1]
      _ = t * (v * x * v⁻¹) := by group
  have hvx2 : (v * x * v⁻¹) ^ 2 ≠ 1 := by
    rw [conj_pow]
    intro h
    apply hc.x_sq_ne_one
    calc x ^ 2 = v⁻¹ * (v * x ^ 2 * v⁻¹) * v := by group
      _ = 1 := by rw [h]; group
  have htv2 : (t * v) ^ 2 = ρ ^ j := by
    have : v * t * v = t * ρ ^ j := by rw [← hj, hvinv]
    calc (t * v) ^ 2 = t * (v * t * v) := by rw [pow_two]; group
      _ = t * t * ρ ^ j := by rw [this]; group
      _ = ρ ^ j := by rw [hc.t_mul_t, one_mul]
  have htvS : t * v ∈ S := hc.t_mul_mem hvP hvS
  have hpow := hg.pow_of_sq hc hjodd htv2
  rcases mem_zpowers_sq_ne_one hc.x_order (hc.cent _ hvxS hvxt) hvx2 with hvx | hvx
  ·
    apply hmax (t * v)
    have hvxc : v * x = x * v := by
      calc v * x = (v * x * v⁻¹) * v := by group
        _ = x * v := by rw [hvx]
    obtain ⟨hm, -⟩ := hg
    refine ⟨by omega, htvS, ?_, ?_, ?_, ?_⟩
    · rw [mul_inv_rev, hvinv, hc.t_inv]
      calc t * (t * v) * t = (t * t) * v * t := by group
        _ = v * t := by rw [hc.t_mul_t, one_mul]
    · calc t * v * x = t * (v * x) := by group
        _ = t * (x * v) := by rw [hvxc]
        _ = (t * x) * v := by group
        _ = (x * t) * v := by rw [hc.x_comm]
        _ = x * (t * v) := by group
    · have h1 : ¬ (t * v) ^ 2 ^ (m - 1) = 1 := by rw [hpow]; exact hc.x_sq_ne_one
      have h2 : (t * v) ^ 2 ^ (m - 1 + 1) = 1 := by
        rw [pow_succ, pow_mul, hpow, ← pow_mul]
        exact hc.x_pow_four
      rw [orderOf_eq_prime_pow h1 h2]
      congr 1
      omega
    · rw [show m + 1 - 2 = m - 1 by omega]
      exact hpow
  · rcases (by obtain ⟨hm, -⟩ := hg; omega : m = 2 ∨ 3 ≤ m) with hm2 | hm3
    ·
      apply hNG
      have hρ : ρ = x ^ 2 := by
        have := hg.2.2.2.2.2
        rw [hm2] at this
        simpa using this
      have hvtS : v * t ∈ S := by
        have : v * t = (t * v)⁻¹ := by rw [mul_inv_rev, hvinv, hc.t_inv]
        rw [this]
        exact inv_mem htvS
      refine ⟨v * t, hvtS, ?_, ?_, ?_⟩
      · have h1 : (v * t) ^ 2 = t * ρ ^ j * t⁻¹ := by
          rw [pow_two, hc.t_inv]
          calc v * t * (v * t) = (v * t * v⁻¹) * t := by rw [hvinv]; group
            _ = t * ρ ^ j * t := by rw [hj]
        rw [h1, hg.conj_t_zpow, hρ]
        obtain ⟨k, rfl⟩ := hjodd
        rw [← zpow_natCast, ← zpow_mul]
        have h4 : x ^ (4 : ℤ) = 1 := by exact_mod_cast hc.x_pow_four
        have : ((2 : ℕ) : ℤ) * -(2 * k + 1) = 4 * (-k - 1) + 2 := by push_cast; ring
        rw [this, zpow_add, zpow_mul, h4, one_zpow, one_mul]
        norm_cast
      · rw [mul_inv_rev, hvinv, hc.t_inv]
        calc t * (v * t) * t = t * v * (t * t) := by group
          _ = t * v := by rw [hc.t_mul_t, mul_one]
      · have htx : t * x * t⁻¹ = x := by rw [← hc.x_comm]; group
        calc v * t * x * (v * t)⁻¹ = v * (t * x * t⁻¹) * v⁻¹ := by group
          _ = x⁻¹ := by rw [htx, hvx]
    ·
      set y := (t * v) ^ 2 ^ (m - 2) with hy
      have hyρ : y ∈ zpowers ρ := by
        have : y = ((t * v) ^ 2) ^ 2 ^ (m - 3) := by
          rw [hy, ← pow_mul, ← pow_succ']
          congr 2
          omega
        rw [this, htv2]
        exact pow_mem (zpow_mem (mem_zpowers ρ) j) _
      have hy2 : y ^ 2 = x ^ 2 := by
        rw [hy, ← pow_mul, ← pow_succ, show m - 2 + 1 = m - 1 by omega]
        exact hpow
      have hyS : y ∈ S := zpowers_le.2 hg.2.1 hyρ
      have hyx : y * x = x * y := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyρ
        rw [← hk]
        exact hg.x_comm_zpow k
      have hvtv : v * (t * v) * v⁻¹ = (t * v)⁻¹ := by
        rw [mul_inv_rev, hvinv, hc.t_inv]
        calc v * (t * v) * v = v * t * (v * v) := by group
          _ = v * t := by rw [← pow_two, hv2, mul_one]
      have hvy : v * y * v⁻¹ = y⁻¹ := by rw [hy, ← conj_pow, hvtv, inv_pow]
      have hwS : y * x ∈ S := S.mul_mem hyS hc.x_mem
      have hw2 : (y * x) ^ 2 = 1 := by
        rw [pow_two]
        calc y * x * (y * x) = y * (x * y) * x := by group
          _ = y * (y * x) * x := by rw [hyx]
          _ = y ^ 2 * x ^ 2 := by rw [pow_two, pow_two]; group
          _ = 1 := by rw [hy2, ← pow_add]; exact hc.x_pow_four
      have hvw : v * (y * x) = (y * x) * v := by
        have h1 : v * (y * x) * v⁻¹ = y * x := by
          have hwinv : (y * x)⁻¹ = y * x := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hw2]
          calc v * (y * x) * v⁻¹ = (v * y * v⁻¹) * (v * x * v⁻¹) := by group
            _ = y⁻¹ * x⁻¹ := by rw [hvy, hvx]
            _ = (x * y)⁻¹ := by group
            _ = (y * x)⁻¹ := by rw [← hyx]
            _ = y * x := hwinv
        calc v * (y * x) = (v * (y * x) * v⁻¹) * v := by group
          _ = (y * x) * v := by rw [h1]
      have hvx2c : v * x ^ 2 = x ^ 2 * v := by
        have h1 : v * x ^ 2 * v⁻¹ = x ^ 2 := by
          rw [← conj_pow, hvx, inv_pow]
          rw [inv_eq_iff_mul_eq_one, ← pow_add]
          exact hc.x_pow_four
        calc v * x ^ 2 = (v * x ^ 2 * v⁻¹) * v := by group
          _ = x ^ 2 * v := by rw [h1]
      have hxnot := hg.x_not_mem hc
      have hw1 : y * x ≠ 1 := by
        intro h
        apply hxnot
        have : x = y⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]
        exact inv_mem hyρ
      have hwx : y * x ≠ x ^ 2 := by
        intro h
        apply hxnot
        have : x = y := by
          have h' : y * x = x * x := by rw [← pow_two, ← h]
          exact (mul_right_cancel h').symm
        rw [this]
        exact hyρ
      have hx2S : x ^ 2 ∈ S := pow_mem hc.x_mem 2
      have hx22 : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hc.x_pow_four
      have hwx2 : (y * x) * x ^ 2 = x ^ 2 * (y * x) := by
        rw [pow_two]
        calc y * x * (x * x) = y * (x * x) * x := by group
          _ = (y * x) * (x * x) := by group
          _ = (x * y) * (x * x) := by rw [hyx]
          _ = x * (y * x) * x := by group
          _ = x * (x * y) * x := by rw [hyx]
          _ = x * x * (y * x) := by group
      exact hwx (hc.T_unique v hvT (y * x) hwS (x ^ 2) hx2S hw2 hx22 hw1 hc.x_sq_ne_one hwx2 hvw
        hvx2c)

end Good

theorem good_base {P S : Subgroup G} {t x : G} {T : Set G} (hc : Ctx P S t x T) :
    Good S t x (x ^ 2) 2 := by
  have hx2inv : (x ^ 2)⁻¹ = x ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    exact hc.x_pow_four
  refine ⟨le_rfl, pow_mem hc.x_mem 2, ?_, ?_, ?_, by norm_num⟩
  · rw [hx2inv, ← conj_pow]
    congr 1
    rw [← hc.x_comm]
    group
  · rw [← pow_succ, ← pow_succ']
  · rw [show 2 - 1 = 1 by norm_num, pow_one]
    exact orderOf_eq_prime (by rw [← pow_mul]; exact hc.x_pow_four) hc.x_sq_ne_one

theorem Good.le_card [Finite G] {S : Subgroup G} {t x ρ : G} {m : ℕ} (hg : Good S t x ρ m) :
    m ≤ Nat.card G + 1 := by
  have h1 : orderOf ρ ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard ρ)
  rw [hg.2.2.2.2.1] at h1
  have h2 := Nat.lt_two_pow_self (n := m - 1)
  omega

theorem printed_branch [Finite G] {P S : Subgroup G} {t x : G} {T : Set G}
    (hc : Ctx P S t x T)
    (hNG : ¬ ∃ y ∈ S, y ^ 2 = x ^ 2 ∧ t * y * t⁻¹ = y⁻¹ ∧ y * x * y⁻¹ = x⁻¹) :
    ∃ (ρ : G) (m : ℕ), Good S t x ρ m ∧ (Nat.card S = 2 ^ m ∨ Nat.card S = 2 ^ (m + 1)) := by
  classical
  let Q : ℕ → Prop := fun m => ∃ ρ, Good S t x ρ m
  set m := Nat.findGreatest Q (Nat.card G + 1) with hm
  obtain ⟨ρ, hg⟩ : Q m := Nat.findGreatest_spec (P := Q) (good_base hc).le_card ⟨_, good_base hc⟩
  have hmax : ∀ ρ' : G, ¬ Good S t x ρ' (m + 1) := fun ρ' h' => by
    have := Nat.le_findGreatest (P := Q) h'.le_card ⟨ρ', h'⟩
    omega
  refine ⟨ρ, m, hg, ?_⟩
  have hcardP : Nat.card P = 2 * Nat.card S := by
    rw [hc.sup_eq]
    exact card_sup_zpowers hc.t_normalizer (by rw [hc.t_sq]; exact one_mem S) hc.t_not_mem
  have hcardX := hg.card_X hc
  set X := (zpowers ρ ⊔ zpowers x) ⊔ zpowers t with hX
  by_cases hXP : X = P
  · left
    rw [hXP, hcardP, pow_succ'] at hcardX
    omega
  · right
    obtain ⟨u, huP, huX, huN, hu2⟩ := exists_mem_normalizer_sq hc.pgroup (hg.X_le hc) hXP
    obtain ⟨j, hjodd, hj⟩ := hg.conj_t_odd hc huP huN huX
    have htX : t ∈ X := mem_sup_right (mem_zpowers t)
    have hX₁P : X ⊔ zpowers u = P := by
      refine eq_of_normalizer_le hc.pgroup (sup_le (hg.X_le hc) (zpowers_le.2 huP))
        fun g hgP hgN => ?_
      have hwT : g * t * g⁻¹ ∈ T := hc.T_conj g hgP t hc.T_t
      have hwX₁ : g * t * g⁻¹ ∈ X ⊔ zpowers u :=
        (mem_normalizer_iff.1 hgN t).1 (mem_sup_left htX)
      rcases (mem_sup_zpowers_iff huN hu2).1 hwX₁ with hw | hw
      · have hw2 : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hc.t_sq]; group
        obtain ⟨i, hi⟩ := hg.involution_X hc hw hw2 (hc.conj_t_not_mem hgP)
        rcases Int.even_or_odd i with he | ho
        · exact mem_sup_left (hg.mem_X_of_even hc hgP hi he)
        ·
          obtain ⟨l, hl⟩ : ∃ l : ℤ, i = j + 2 * l := by
            obtain ⟨a, ha⟩ := ho
            obtain ⟨b, hb⟩ := hjodd
            exact ⟨a - b, by rw [ha, hb]; ring⟩
          have hconj := hg.conj_reflection hc j l
          rw [← hl, ← hi, ← hj] at hconj
          set c := ρ ^ (-l) * u with hcdef
          have hcP : c ∈ P := P.mul_mem (zpow_mem (hc.le hg.2.1) _) huP
          set k := c⁻¹ * g with hk
          have hkP : k ∈ P := P.mul_mem (P.inv_mem hcP) hgP
          have hkt : k * t = t * k := by
            have h1 : k * t * k⁻¹ = t := by
              calc k * t * k⁻¹ = c⁻¹ * (g * t * g⁻¹) * c := by rw [hk]; group
                _ = c⁻¹ * (ρ ^ (-l) * (u * t * u⁻¹) * (ρ ^ (-l))⁻¹) * c := by rw [hconj]
                _ = t := by rw [hcdef]; group
            calc k * t = (k * t * k⁻¹) * k := by group
              _ = t * k := by rw [h1]
          have hkX := hg.cent_le_X hc hkP hkt
          have hg' : g = ρ ^ (-l) * u * k := by rw [hk, hcdef]; group
          rw [hg']
          refine mul_mem (mul_mem ?_ (mem_sup_right (mem_zpowers u))) (mem_sup_left hkX)
          exact mem_sup_left (mem_sup_left (mem_sup_left (zpow_mem (mem_zpowers ρ) _)))
      ·
        exfalso
        have hwP : g * t * g⁻¹ ∈ P := P.mul_mem (P.mul_mem hgP hc.t_mem) (P.inv_mem hgP)
        have hwN : g * t * g⁻¹ ∈ normalizer (X : Set G) := by
          have : g * t * g⁻¹ = u * (u⁻¹ * (g * t * g⁻¹)) := by group
          rw [this]
          exact mul_mem huN (le_normalizer hw)
        have hwX : g * t * g⁻¹ ∉ X := by
          intro h
          apply huX
          have : u⁻¹ ∈ X := by
            have := X.mul_mem hw (X.inv_mem h)
            simpa [mul_assoc] using this
          simpa using X.inv_mem this
        exact hg.not_mem_T hc hNG hmax hwP hwN hwX hwT
    have hcard₁ := card_sup_zpowers huN hu2 huX
    rw [hX₁P, hcardP, hcardX] at hcard₁
    rw [pow_succ']
    omega

end Lemma37

end CFSG.ComponentClassification.AschbacherKnownGroup
