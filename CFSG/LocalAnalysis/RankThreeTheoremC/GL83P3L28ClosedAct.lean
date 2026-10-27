module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedOrders

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x k : Y} {K₁ K₂ Q : Subgroup Y}
  {a b t : Y}

theorem zpow_eq_iff_zmod {a : Y} (ha : orderOf a = 9) {m n : ℤ} :
    a ^ m = a ^ n ↔ (m : ZMod 9) = (n : ZMod 9) := by
  rw [zpow_eq_zpow_iff_modEq, ha, ZMod.intCast_eq_intCast_iff]

structure SwapData (P K₁ K₂ Q : Subgroup Y) (a b t : Y) : Prop where
  two : TwoData P K₁ K₂
  q : QData P K₁ K₂ Q a b
  t_norm : t ∈ normalizer (P : Set Y)
  t_swap : K₁.map (MulAut.conj t).toMonoidHom = K₂

namespace SwapData

variable (sd : SwapData P K₁ K₂ Q a b t)

include sd

theorem symm : SwapData P K₂ K₁ Q b a t := by
  refine ⟨sd.two.symm, ?_, sd.t_norm, (sd.two.swap_of_ne (g := t) (by
    rw [sd.t_swap]
    exact sd.two.ne.symm)).2⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := sd.q
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h9, h8, h11, h10, by rw [h12, sup_comm], h14, h13⟩

theorem P_conj {g : Y} (hg : g ∈ P) : t * g * t⁻¹ ∈ P :=
  (mem_normalizer_iff.mp sd.t_norm g).mp hg

theorem conj_a {y : Y} (hy : y ∈ zpowers a) : t * y * t⁻¹ ∈ zpowers b := by
  rw [← sd.q.S₁_eq] at hy
  rw [← sd.q.S₂_eq]
  refine ⟨sd.P_conj hy.1, ?_⟩
  have : t * y * t⁻¹ ∈ K₁.map (MulAut.conj t).toMonoidHom := ⟨y, hy.2, rfl⟩
  rwa [sd.t_swap] at this

theorem conj_b {y : Y} (hy : y ∈ zpowers b) : t * y * t⁻¹ ∈ zpowers a :=
  sd.symm.conj_a hy

theorem t_norm_Q : t ∈ normalizer (Q : Set Y) := by
  have hab : a * b = b * a :=
    (mem_centralizer_iff.mp (sd.two.le_cent sd.q.a_mem.2) b sd.q.b_mem.2).symm
  have hle : Q.map (MulAut.conj t).toMonoidHom ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    rw [sd.q.Q_eq] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup_prod (GL83P3L28Aux.le_normalizer_of_comm
      (zpowers_comm hab)) hy
    show t * (y₁ * y₂) * t⁻¹ ∈ Q
    have e : t * (y₁ * y₂) * t⁻¹ = (t * y₁ * t⁻¹) * (t * y₂ * t⁻¹) := by group
    rw [e, sd.q.Q_eq]
    exact mul_mem (mem_sup_right (sd.conj_a hy₁)) (mem_sup_left (sd.conj_b hy₂))
  have heq : Q.map (MulAut.conj t).toMonoidHom = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])
  exact mem_normalizer_iff_map_conj_eq.mpr heq

theorem cube_mem {g : Y} (hg : g ∈ P) : g ^ 3 ∈ Q := by
  haveI : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer sd.q.Q_le).mpr sd.q.P_norm
  have hidx : (Q.subgroupOf P).index = 3 := by
    have h := Subgroup.index_mul_card (Q.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sd.q.Q_le).toEquiv, sd.q.Q_card,
      sd.two.hs.shape.1] at h
    have : (Q.subgroupOf P).index * 3 ^ 4 = 3 * 3 ^ 4 := by rw [h]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  have := Subgroup.pow_index_mem (Q.subgroupOf P) (⟨g, hg⟩ : P)
  rw [hidx] at this
  exact mem_subgroupOf.mp this

theorem P_eq_sup {u : Y} (hu : u ∈ P) (huQ : u ∉ Q) : zpowers u ⊔ Q = P := by
  refine sd.q.Q_max _ (lt_of_le_of_ne le_sup_right fun h' => huQ ?_)
    (sup_le (zpowers_le.mpr hu) sd.q.Q_le)
  rw [h']
  exact mem_sup_left (mem_zpowers u)

theorem a_mem_Q : a ∈ Q := by
  rw [sd.q.Q_eq]
  exact mem_sup_left (mem_zpowers a)

theorem b_mem_Q : b ∈ Q := by
  rw [sd.q.Q_eq]
  exact mem_sup_right (mem_zpowers b)

theorem exists_pow_mul {g : Y} (hg : g ∈ P) (hgQ : g ∉ Q) :
    ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∃ q ∈ Q, t * g * t⁻¹ = g ^ r * q := by
  have hmem : t * g * t⁻¹ ∈ zpowers g ⊔ Q := by
    rw [sd.P_eq_sup hg hgQ]
    exact sd.P_conj hg
  obtain ⟨w, hw, q, hq, hwq⟩ := mem_sup_prod (zpowers_le.mpr (sd.q.P_norm hg)) hmem
  obtain ⟨e, rfl⟩ := mem_zpowers_iff.mp hw
  obtain ⟨r, hr3, s, hs⟩ : ∃ r : ℕ, r < 3 ∧ ∃ s : ℤ, e = 3 * s + r :=
    ⟨(e % 3).toNat, by omega, e / 3, by omega⟩
  have hg3 : g ^ 3 ∈ Q := sd.cube_mem hg
  have hq' : (g ^ 3) ^ s * q ∈ Q := Q.mul_mem (Q.zpow_mem hg3 s) hq
  have hrep : g ^ e = (g ^ 3) ^ s * g ^ r := by
    rw [hs, zpow_add, zpow_mul]
    simp
  have hgq : t * g * t⁻¹ = g ^ r * ((g ^ 3) ^ s * q) := by
    rw [← hwq, hrep, ← mul_assoc, ((Commute.pow_pow_self g 3 r).zpow_left s).eq, mul_assoc]
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hgQ
    have : t * g * t⁻¹ ∈ Q := by rw [hgq, pow_zero, one_mul]; exact hq'
    exact (mem_normalizer_iff.mp sd.t_norm_Q g).mpr this
  exact ⟨r, by omega, (g ^ 3) ^ s * q, hq', hgq⟩

theorem comm_of_pow_comm {g c : Y} (hg3 : g ^ 3 ∈ Q) (hc : c ∈ Q) {r : ℕ} (hr : r = 1 ∨ r = 2)
    (h : g ^ r * c = c * g ^ r) : g * c = c * g := by
  rcases hr with rfl | rfl
  · simpa using h
  · have h2 : Commute ((g ^ 2) ^ 2) c := (show Commute (g ^ 2) c from h).pow_left 2
    have h3 : Commute (g ^ 3)⁻¹ c := (show Commute (g ^ 3) c from
      sd.q.Q_ab _ hg3 c hc).inv_left
    have h4 := h2.mul_left h3
    have e : (g ^ 2) ^ 2 * (g ^ 3)⁻¹ = g := by group
    rw [e] at h4
    exact h4.eq

theorem cent_ab {g : Y} (hg : g ∈ P) (h : g * a = a * g) : g * b = b * g := by
  by_cases hgQ : g ∈ Q
  · exact sd.q.Q_ab g hgQ b sd.b_mem_Q
  · obtain ⟨r, hr, q, hq, hgq⟩ := sd.exists_pow_mul hg hgQ
    have hb'' : t * a * t⁻¹ ∈ zpowers b := sd.conj_a (mem_zpowers a)
    have hord : orderOf (t * a * t⁻¹) = 9 := by
      have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective a
      exact this.trans sd.q.a_ord
    have hbmem : b ∈ zpowers (t * a * t⁻¹) := by
      have : zpowers (t * a * t⁻¹) = zpowers b := Subgroup.eq_of_le_of_card_ge
        (zpowers_le.mpr hb'') (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, sd.q.b_ord])
      rw [this]
      exact mem_zpowers b
    have hc1 : (t * g * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * g * t⁻¹) :=
      calc (t * g * t⁻¹) * (t * a * t⁻¹) = t * (g * a) * t⁻¹ := by group
        _ = t * (a * g) * t⁻¹ := by rw [h]
        _ = (t * a * t⁻¹) * (t * g * t⁻¹) := by group
    rw [hgq] at hc1
    have hb''Q : t * a * t⁻¹ ∈ Q := by
      rw [sd.q.Q_eq]
      exact mem_sup_right hb''
    have hqb : q * (t * a * t⁻¹) = (t * a * t⁻¹) * q := sd.q.Q_ab q hq _ hb''Q
    have hgr : g ^ r * (t * a * t⁻¹) = (t * a * t⁻¹) * g ^ r := by
      calc g ^ r * (t * a * t⁻¹) = g ^ r * q * (t * a * t⁻¹) * q⁻¹ := by
            rw [mul_assoc (g ^ r) q, hqb]
            group
        _ = (t * a * t⁻¹) * (g ^ r * q) * q⁻¹ := by rw [hc1]
        _ = (t * a * t⁻¹) * g ^ r := by group
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hbmem
    have hgrb : g ^ r * b = b * g ^ r := by
      rw [← hn]
      exact (Commute.zpow_right (show Commute (g ^ r) (t * a * t⁻¹) from hgr) n).eq
    exact sd.comm_of_pow_comm (sd.cube_mem hg) sd.b_mem_Q hr hgrb

theorem cent_iff {g : Y} (hg : g ∈ P) : g * a = a * g ↔ g * b = b * g :=
  ⟨sd.cent_ab hg, sd.symm.cent_ab hg⟩

theorem cent_Q {g : Y} (hg : g ∈ P) (h : g * a = a * g) : ∀ y ∈ Q, g * y = y * g := by
  intro y hy
  have hle : Q ≤ centralizer ({g} : Set Y) := by
    rw [sd.q.Q_eq]
    exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (sd.cent_ab hg h).symm))
  exact (mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem not_cent_Q {g : Y} (hg : g ∈ P) (hgQ : g ∉ Q) : ¬ ∀ y ∈ Q, g * y = y * g := by
  intro hc
  have hle : P ≤ centralizer ({g} : Set Y) := by
    rw [← sd.P_eq_sup hg hgQ]
    exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (fun y hy => mem_centralizer_singleton_iff.mpr (hc y hy).symm)
  have hgZ : g ∈ L28Z P := GL83P3L28Aux.mem_L28Z_iff.mpr ⟨hg, fun p hp =>
    mem_centralizer_singleton_iff.mp (hle hp)⟩
  exact hgQ ((sd.q.Z_iff g).mp hgZ).1

theorem k_mem_Q (hd : ClosedData P x k) : k ∈ Q := by
  by_contra hkQ
  have hkP := hd.k_mem
  have hWdvd : Nat.card (Q ⊓ zpowers k : Subgroup Y) ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : Q ⊓ zpowers k ≤ zpowers k)
    rwa [Nat.card_zpowers, hd.k_order] at this
  have hW9 : Nat.card (Q ⊓ zpowers k : Subgroup Y) ≠ 3 ^ 2 := by
    intro h9
    have heq : Q ⊓ zpowers k = zpowers k := Subgroup.eq_of_le_of_card_ge inf_le_right
      (by rw [Nat.card_zpowers, hd.k_order, h9]; norm_num)
    apply hkQ
    have : k ∈ Q ⊓ zpowers k := by rw [heq]; exact mem_zpowers k
    exact this.1
  have hWcard : Nat.card (Q ⊓ zpowers k : Subgroup Y) = 1 ∨
      Nat.card (Q ⊓ zpowers k : Subgroup Y) = 3 := by
    obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hWdvd
    interval_cases i
    · exact Or.inl (by simpa using hc)
    · exact Or.inr (by simpa using hc)
    · exact absurd hc hW9
  have hcomm : ∀ {K : Subgroup Y} {c : Y}, P ≤ normalizer (K : Set Y) → c ∈ P ⊓ K → c ∈ Q →
      k * c * k⁻¹ * c⁻¹ ∈ P ⊓ K ∧ k * c * k⁻¹ * c⁻¹ ∈ Q ∧ k * c * k⁻¹ * c⁻¹ ∈ zpowers k := by
    intro K c hNK hcPK hcQ
    have h1 : k * c * k⁻¹ ∈ P ⊓ K := ⟨P.mul_mem (P.mul_mem hkP hcPK.1) (P.inv_mem hkP),
      ((mem_normalizer_iff.mp (hNK hkP)) c).mp hcPK.2⟩
    refine ⟨(P ⊓ K).mul_mem h1 ((P ⊓ K).inv_mem hcPK), ?_, ?_⟩
    · exact Q.mul_mem ((mem_normalizer_iff.mp (sd.q.P_norm hkP) c).mp hcQ) (Q.inv_mem hcQ)
    · have h4 : c * k⁻¹ * c⁻¹ ∈ zpowers k := (mem_normalizer_iff.mp (hd.k_norm hcPK.1) k⁻¹).mp
        ((zpowers k).inv_mem (mem_zpowers k))
      have e : k * c * k⁻¹ * c⁻¹ = k * (c * k⁻¹ * c⁻¹) := by group
      rw [e]
      exact (zpowers k).mul_mem (mem_zpowers k) h4
  have hA := hcomm (sd.two.hs.normalizes sd.two.c₁) sd.q.a_mem sd.a_mem_Q
  have hB := hcomm (sd.two.hs.normalizes sd.two.c₂) sd.q.b_mem sd.b_mem_Q
  have hcom1 : ∀ c : Y, k * c * k⁻¹ * c⁻¹ = 1 → k * c = c * k := fun c h => by
    have := mul_inv_eq_one.mp h
    calc k * c = (k * c * k⁻¹) * k := by group
      _ = c * k := by rw [this]
  by_cases h1 : k * a * k⁻¹ * a⁻¹ = 1
  · exact sd.not_cent_Q hkP hkQ (sd.cent_Q hkP (hcom1 a h1))
  by_cases h2 : k * b * k⁻¹ * b⁻¹ = 1
  · exact sd.not_cent_Q hkP hkQ
      (sd.cent_Q hkP ((sd.cent_iff hkP).mpr (hcom1 b h2)))
  exfalso
  have hxW : k * a * k⁻¹ * a⁻¹ ∈ (Q ⊓ zpowers k : Subgroup Y) := ⟨hA.2.1, hA.2.2⟩
  have hyW : k * b * k⁻¹ * b⁻¹ ∈ (Q ⊓ zpowers k : Subgroup Y) := ⟨hB.2.1, hB.2.2⟩
  have hW3 : Nat.card (Q ⊓ zpowers k : Subgroup Y) = 3 := by
    rcases hWcard with h | h
    · exfalso
      have hbot : (Q ⊓ zpowers k : Subgroup Y) = ⊥ := Subgroup.eq_bot_of_card_eq _ h
      rw [hbot, mem_bot] at hxW
      exact h1 hxW
    · exact h
  have hxo : orderOf (k * a * k⁻¹ * a⁻¹) = 3 := by
    have hd' := Subgroup.orderOf_dvd_natCard (Q ⊓ zpowers k) hxW
    rw [hW3] at hd'
    rcases (Nat.dvd_prime Nat.prime_three).mp hd' with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have hzx : zpowers (k * a * k⁻¹ * a⁻¹) = Q ⊓ zpowers k :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxW) (by rw [hW3, Nat.card_zpowers, hxo])
  have hyx : k * b * k⁻¹ * b⁻¹ ∈ zpowers (k * a * k⁻¹ * a⁻¹) := by rw [hzx]; exact hyW
  have hxa : k * a * k⁻¹ * a⁻¹ ∈ zpowers a := by
    have := hA.1
    rwa [sd.q.S₁_eq] at this
  have hya : k * b * k⁻¹ * b⁻¹ ∈ zpowers a := (zpowers_le.mpr hxa) hyx
  have hyb : k * b * k⁻¹ * b⁻¹ ∈ zpowers b := by
    have := hB.1
    rwa [sd.q.S₂_eq] at this
  have hy : k * b * k⁻¹ * b⁻¹ ∈ K₁ ⊓ K₂ :=
    ⟨(zpowers_le.mpr sd.q.a_mem.2) hya, (zpowers_le.mpr sd.q.b_mem.2) hyb⟩
  rw [sd.two.inf_bot, mem_bot] at hy
  exact h2 hy

theorem kappa_not_mem (hd : ClosedData P x k) : k ^ 3 ∉ K₁ ∧ k ^ 3 ∉ K₂ := by
  obtain ⟨ι, hιx, hικ⟩ := hd.invert
  have hswap := hd.iota_swaps sd.two hιx hικ
  have hswap' : K₂.map (MulAut.conj ι).toMonoidHom = K₁ :=
    (sd.two.swap_of_ne (by rw [hswap]; exact sd.two.ne.symm)).2
  have hk3 : k ^ 3 ≠ 1 := fun h => by
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    rw [hd.k_order] at this
    omega
  constructor
  · intro h
    have h1 : ι * k ^ 3 * ι⁻¹ ∈ K₂ := by
      rw [← hswap]
      exact ⟨k ^ 3, h, rfl⟩
    rw [hικ] at h1
    have : (k ^ 3)⁻¹ ∈ K₁ ⊓ K₂ := ⟨K₁.inv_mem h, h1⟩
    rw [sd.two.inf_bot, mem_bot, inv_eq_one] at this
    exact hk3 this
  · intro h
    have h1 : ι * k ^ 3 * ι⁻¹ ∈ K₁ := by
      rw [← hswap']
      exact ⟨k ^ 3, h, rfl⟩
    rw [hικ] at h1
    have : (k ^ 3)⁻¹ ∈ K₁ ⊓ K₂ := ⟨h1, K₂.inv_mem h⟩
    rw [sd.two.inf_bot, mem_bot, inv_eq_one] at this
    exact hk3 this

theorem exists_diag (hd : ClosedData P x k) :
    ∃ a' b' : Y, zpowers a' = zpowers a ∧ zpowers b' = zpowers b ∧ orderOf a' = 9 ∧
      orderOf b' = 9 ∧ k = a' * b' := by
  have hab : a * b = b * a :=
    (mem_centralizer_iff.mp (sd.two.le_cent sd.q.a_mem.2) b sd.q.b_mem.2).symm
  have hkQ := sd.k_mem_Q hd
  rw [sd.q.Q_eq] at hkQ
  obtain ⟨a', ha', b', hb', hk⟩ := mem_sup_prod (GL83P3L28Aux.le_normalizer_of_comm
    (zpowers_comm hab)) hkQ
  have hcomm' : a' * b' = b' * a' := zpowers_comm hab a' ha' b' hb'
  have hk3 : k ^ 3 = a' ^ 3 * b' ^ 3 := by
    rw [← hk]
    exact (Commute.mul_pow (show Commute a' b' from hcomm') 3)
  obtain ⟨hk1, hk2⟩ := sd.kappa_not_mem hd
  have hmemK₁ : ∀ y ∈ zpowers a, y ∈ K₁ := fun y hy => (zpowers_le.mpr sd.q.a_mem.2) hy
  have hmemK₂ : ∀ y ∈ zpowers b, y ∈ K₂ := fun y hy => (zpowers_le.mpr sd.q.b_mem.2) hy
  have ha'3 : a' ^ 3 ≠ 1 := fun h => hk2 (by
    rw [hk3, h, one_mul]
    exact hmemK₂ _ ((zpowers b).pow_mem hb' 3))
  have hb'3 : b' ^ 3 ≠ 1 := fun h => hk1 (by
    rw [hk3, h, mul_one]
    exact hmemK₁ _ ((zpowers a).pow_mem ha' 3))
  have hQ9 := sd.q.Q_exp
  have ha'Q : a' ∈ Q := (zpowers_le.mpr sd.a_mem_Q) ha'
  have hb'Q : b' ∈ Q := (zpowers_le.mpr sd.b_mem_Q) hb'
  have hao : orderOf a' = 9 := by
    have : orderOf a' = 3 ^ (1 + 1) :=
      orderOf_eq_prime_pow (by simpa using ha'3) (by simpa using hQ9 a' ha'Q)
    simpa using this
  have hbo : orderOf b' = 9 := by
    have : orderOf b' = 3 ^ (1 + 1) :=
      orderOf_eq_prime_pow (by simpa using hb'3) (by simpa using hQ9 b' hb'Q)
    simpa using this
  refine ⟨a', b', ?_, ?_, hao, hbo, hk.symm⟩
  · exact Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha') (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hao, sd.q.a_ord])
  · exact Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hb') (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hbo, sd.q.b_ord])

theorem claimA (hd : ClosedData P x k) {a' b' : Y} (ha' : a' ∈ zpowers a)
    (hb' : b' ∈ zpowers b) (hk : k = a' * b') :
    ∀ g ∈ P, ∃ m : ℤ, g * a' * g⁻¹ = a' ^ m ∧ g * b' * g⁻¹ = b' ^ m := by
  intro g hg
  have hgk : g * k * g⁻¹ ∈ zpowers k :=
    (mem_normalizer_iff.mp (hd.k_norm hg) k).mp (mem_zpowers k)
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hgk
  have hab : a * b = b * a :=
    (mem_centralizer_iff.mp (sd.two.le_cent sd.q.a_mem.2) b sd.q.b_mem.2).symm
  have hcomm' : Commute a' b' := zpowers_comm hab a' ha' b' hb'
  have hkm : k ^ m = a' ^ m * b' ^ m := by
    rw [hk]
    exact hcomm'.mul_zpow m
  have ha'K : a' ∈ K₁ := (zpowers_le.mpr sd.q.a_mem.2) ha'
  have hb'K : b' ∈ K₂ := (zpowers_le.mpr sd.q.b_mem.2) hb'
  have hga : g * a' * g⁻¹ ∈ K₁ := (mem_normalizer_iff.mp (sd.two.hs.normalizes sd.two.c₁ hg) a').mp
    ha'K
  have hgb : g * b' * g⁻¹ ∈ K₂ := (mem_normalizer_iff.mp (sd.two.hs.normalizes sd.two.c₂ hg) b').mp
    hb'K
  have hprod : (g * a' * g⁻¹) * (g * b' * g⁻¹) = a' ^ m * b' ^ m := by
    rw [← hkm, hm, hk]
    group
  obtain ⟨h1, h2⟩ := sd.two.prod_unique hga (K₁.zpow_mem ha'K m) hgb (K₂.zpow_mem hb'K m) hprod
  exact ⟨m, h1, h2⟩

theorem exists_u (hd : ClosedData P x k) :
    ∃ u ∈ P, u ∉ Q ∧ ∃ q ∈ Q, t * u * t⁻¹ = u * q := by
  obtain ⟨a', b', hza, hzb, hao, hbo, hk⟩ := sd.exists_diag hd
  have ha' : a' ∈ zpowers a := hza ▸ mem_zpowers a'
  have hb' : b' ∈ zpowers b := hzb ▸ mem_zpowers b'
  have claimA := sd.claimA hd ha' hb' hk
  obtain ⟨u, huP, huQ⟩ : ∃ u ∈ P, u ∉ Q := by
    by_contra h
    push Not at h
    have hPQ : P = Q := le_antisymm h sd.q.Q_le
    have := sd.q.Q_card
    rw [← hPQ, sd.two.hs.shape.1] at this
    norm_num at this
  obtain ⟨r, hr, q, hq, hgq⟩ := sd.exists_pow_mul huP huQ
  rcases hr with rfl | rfl
  · exact ⟨u, huP, huQ, q, hq, by simpa using hgq⟩
  · exfalso
    obtain ⟨m, hma, hmb⟩ := claimA u huP
    obtain ⟨m', hma', -⟩ := claimA u⁻¹ (P.inv_mem huP)
    have h1 : a' = (a' ^ m) ^ m' :=
      calc a' = u * (u⁻¹ * a' * u⁻¹⁻¹) * u⁻¹ := by group
        _ = u * a' ^ m' * u⁻¹ := by rw [hma']
        _ = (u * a' * u⁻¹) ^ m' := conj_zpow.symm
        _ = (a' ^ m) ^ m' := by rw [hma]
    have hunit : (m : ZMod 9) * (m' : ZMod 9) = 1 := by
      have h2 : a' ^ (1 : ℤ) = a' ^ (m * m') := by rw [zpow_one, zpow_mul]; exact h1
      have := (zpow_eq_iff_zmod hao).mp h2
      push_cast at this
      exact this.symm
    have hb''mem : t * a' * t⁻¹ ∈ zpowers b' := by
      rw [hzb]
      exact sd.conj_a ha'
    have hb''ord : orderOf (t * a' * t⁻¹) = 9 :=
      (orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective a').trans hao
    obtain ⟨s, hs⟩ := mem_zpowers_iff.mp hb''mem
    have hb'Q : b' ∈ Q := (zpowers_le.mpr sd.b_mem_Q) hb'
    have hb''Q : t * a' * t⁻¹ ∈ Q := by
      rw [← hs]
      exact Q.zpow_mem hb'Q s
    have hE1 : (t * u * t⁻¹) * (t * a' * t⁻¹) * (t * u * t⁻¹)⁻¹ = (t * a' * t⁻¹) ^ m :=
      calc (t * u * t⁻¹) * (t * a' * t⁻¹) * (t * u * t⁻¹)⁻¹ = t * (u * a' * u⁻¹) * t⁻¹ := by group
        _ = t * a' ^ m * t⁻¹ := by rw [hma]
        _ = (t * a' * t⁻¹) ^ m := conj_zpow.symm
    have hub : u * (t * a' * t⁻¹) * u⁻¹ = (t * a' * t⁻¹) ^ m := by
      rw [← hs]
      calc u * b' ^ s * u⁻¹ = (u * b' * u⁻¹) ^ s := conj_zpow.symm
        _ = (b' ^ m) ^ s := by rw [hmb]
        _ = (b' ^ s) ^ m := by rw [← zpow_mul, ← zpow_mul, mul_comm]
    have hq' : q * (t * a' * t⁻¹) = (t * a' * t⁻¹) * q := sd.q.Q_ab q hq _ hb''Q
    have hq'' : q * (t * a' * t⁻¹) * q⁻¹ = t * a' * t⁻¹ := by rw [hq']; group
    rw [pow_two] at hgq
    have hE2 : (u * u * q) * (t * a' * t⁻¹) * (u * u * q)⁻¹ = ((t * a' * t⁻¹) ^ m) ^ m :=
      calc (u * u * q) * (t * a' * t⁻¹) * (u * u * q)⁻¹
          = u * (u * (q * (t * a' * t⁻¹) * q⁻¹) * u⁻¹) * u⁻¹ := by group
        _ = u * (u * (t * a' * t⁻¹) * u⁻¹) * u⁻¹ := by rw [hq'']
        _ = u * (t * a' * t⁻¹) ^ m * u⁻¹ := by rw [hub]
        _ = (u * (t * a' * t⁻¹) * u⁻¹) ^ m := conj_zpow.symm
        _ = ((t * a' * t⁻¹) ^ m) ^ m := by rw [hub]
    rw [hgq] at hE1
    have h3 : (t * a' * t⁻¹) ^ m = (t * a' * t⁻¹) ^ (m * m) := by
      rw [zpow_mul]
      exact hE1.symm.trans hE2
    have hmm : (m : ZMod 9) = (m : ZMod 9) * (m : ZMod 9) := by
      have := (zpow_eq_iff_zmod hb''ord).mp h3
      push_cast at this
      exact this
    have hm1 : (m : ZMod 9) = 1 :=
      calc (m : ZMod 9) = (m : ZMod 9) * ((m : ZMod 9) * (m' : ZMod 9)) := by rw [hunit, mul_one]
        _ = ((m : ZMod 9) * (m : ZMod 9)) * (m' : ZMod 9) := by ring
        _ = (m : ZMod 9) * (m' : ZMod 9) := by rw [← hmm]
        _ = 1 := hunit
    have hpa : a' ^ m = a' ^ (1 : ℤ) := (zpow_eq_iff_zmod hao).mpr (by push_cast; exact hm1)
    have hpb : b' ^ m = b' ^ (1 : ℤ) := (zpow_eq_iff_zmod hbo).mpr (by push_cast; exact hm1)
    have hua : u * a' * u⁻¹ = a' := by rw [hma, hpa, zpow_one]
    have hub' : u * b' * u⁻¹ = b' := by rw [hmb, hpb, zpow_one]
    have hQ' : Q = zpowers a' ⊔ zpowers b' := by rw [sd.q.Q_eq, hza, hzb]
    have hle : Q ≤ centralizer ({u} : Set Y) := by
      rw [hQ']
      refine sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))
      · calc a' * u = (u * a' * u⁻¹) * u := by rw [hua]
          _ = u * a' := by group
      · calc b' * u = (u * b' * u⁻¹) * u := by rw [hub']
          _ = u * b' := by group
    exact sd.not_cent_Q huP huQ (fun y hy => (mem_centralizer_singleton_iff.mp (hle hy)).symm)

end SwapData







end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
