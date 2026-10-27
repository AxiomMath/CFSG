module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1R

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix

variable {G : Type*} [Group G]

theorem exists_conj_le_of_maximal [Finite G] {D K T : Subgroup G} (hDK : D ≤ K)
    (hD : IsPGroup 2 D) (hmax : ∀ T : Subgroup G, T ≤ K → IsPGroup 2 T → D ≤ T → T = D)
    (hTK : T ≤ K) (hT : IsPGroup 2 T) : ∃ k ∈ K, ∀ x ∈ T, k * x * k⁻¹ ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set DK : Subgroup K := D.subgroupOf K
  have hDKp : IsPGroup 2 DK := hD.of_equiv (subgroupOfEquivOfLe hDK).symm
  have hDKmax : ∀ {Q : Subgroup K}, IsPGroup 2 Q → DK ≤ Q → Q = DK := by
    intro Q hQ hle
    have hQG : IsPGroup 2 (Q.map K.subtype) := hQ.map _
    have hDQ : D ≤ Q.map K.subtype := by
      intro x hx
      exact ⟨⟨x, hDK hx⟩, hle hx, rfl⟩
    have h := hmax _ (map_subtype_le Q) hQG hDQ
    apply Subgroup.map_injective K.subtype_injective
    rw [h]
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hDK hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  let SD : Sylow 2 K := { toSubgroup := DK, isPGroup' := hDKp, is_maximal' := hDKmax }
  have hTKp : IsPGroup 2 (T.subgroupOf K) := hT.of_equiv (subgroupOfEquivOfLe hTK).symm
  obtain ⟨S, hS⟩ := hTKp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S SD
  refine ⟨g, g.2, fun x hx => ?_⟩
  have h1 : (⟨x, hTK hx⟩ : K) ∈ S := hS hx
  have h2 : g * ⟨x, hTK hx⟩ * g⁻¹ ∈ g • S := by
    rw [← SetLike.mem_coe, Sylow.coe_smul]
    have := Set.smul_mem_smul_set (a := MulAut.conj g) (SetLike.mem_coe.2 h1)
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [hg] at h2
  exact h2

theorem mem_normalizer_centralizer {W : Subgroup G} {g : G} (hg : g ∈ normalizer (W : Set G)) :
    g ∈ normalizer (centralizer (W : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (W : Set G), ∀ x ∈ centralizer (W : Set G),
      g * x * g⁻¹ ∈ centralizer (W : Set G) := by
    intro g hg x hx
    refine mem_centralizer_iff.2 fun w hw => ?_
    have hw' : g⁻¹ * w * g ∈ W := by
      have := (mem_normalizer_iff.1 (inv_mem hg) w).1 hw
      simpa using this
    have h := mem_centralizer_iff.1 hx _ hw'
    calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * w := by group
  refine mem_normalizer_iff.2 fun x => ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem mem_sup_zpowers_iff {C : Subgroup G} {t : G} (ht : t ∈ normalizer (C : Set G))
    (ht2 : t * t = 1) {x : G} : x ∈ C ⊔ zpowers t ↔ x ∈ C ∨ x * t ∈ C := by
  have hc1 : ∀ y ∈ C, t⁻¹ * y * t ∈ C := fun y hy => by
    have := (mem_normalizer_iff.1 (inv_mem ht) y).1 hy
    simpa using this
  let S : Subgroup G :=
    { carrier := {x | x ∈ C ∨ x * t ∈ C}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem ha hb)
        · right
          have : a * b * t = a * t * (t⁻¹ * b * t) := by group
          rw [this]
          exact mul_mem ha (hc1 b hb)
        · left
          have : a * b = a * t * (t⁻¹ * (b * t) * t) * (t * t)⁻¹ := by group
          rw [this, ht2, inv_one, mul_one]
          exact mul_mem ha (hc1 _ hb)
      one_mem' := Or.inl (one_mem _)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · right
          have : a⁻¹ * t = t * t * (t⁻¹ * (a * t)⁻¹ * t) := by group
          rw [this, ht2, one_mul]
          exact hc1 _ (inv_mem ha) }
  constructor
  · intro hx
    have hle : C ⊔ zpowers t ≤ S :=
      sup_le (fun y hy => Or.inl hy) (zpowers_le.2 (Or.inr (by rw [ht2]; exact one_mem _)))
    exact hle hx
  · rintro (h | h)
    · exact mem_sup_left h
    · have : x = x * t * t⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers t)))

theorem isPGroup_zpowers_of_sq {s : G} (hs : s * s = 1) : IsPGroup 2 (zpowers s) := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro g
  refine ⟨1, ?_⟩
  rw [← Subgroup.orderOf_coe, pow_one]
  exact (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one (by rw [pow_two, hs]))

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
  (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS hZ

theorem t_mem_normalizer_Wsub [Finite G] : t ∈ normalizer (hS.Wsub hZ : Set G) :=
  hS.D_le_normalizer_Wsub hZ hS.t_mem_D

theorem Wsub_le_centralizer [Finite G] : hS.Wsub hZ ≤ centralizer (hS.Wsub hZ : Set G) :=
  fun _ hw => mem_centralizer_iff.2 fun _ hy => hS.Wsub_comm hZ hy hw

theorem mem_Q_of_comm_t [Finite G] {w : G} (hw : w ∈ hS.Wsub hZ) (h : w * t = t * w) :
    w ∈ Q := by
  refine hS.mem_Q_of_mem_Wsub hZ hw ?_
  have h1 := hS.kap_t_right hZ (hS.Wsub_le_D hZ hw)
  rw [kap_eq_one_iff.2 h, ← hS.rad.ψ_zero] at h1
  exact (hS.rad.ψ_inj h1).symm

theorem mem_Q_of_invol [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {w : G}
    (hw : w ∈ hS.Wsub hZ) (h : w * t * (w * t) = 1) : w ∈ Q := by
  refine hS.mem_Q_of_comm_t hZ hw ?_
  have hw2 := hW2 w hw
  have ht2 := hS.shape.mul_self
  calc w * t = w * t * (w * t) * (t * w) := by
        rw [show w * t * (w * t) * (t * w) = w * (t * (w * (t * t) * w)) by group, ht2,
          mul_one, hw2, mul_one]
    _ = t * w := by rw [h, one_mul]

theorem card_Q_lt_Wsub [Finite G] : Nat.card Q < Nat.card (hS.Wsub hZ) := by
  rw [hS.rad.card_Q, hS.card_Wsub hZ]; norm_num

theorem mem_Wsub_or [Finite G] {d : G} (hd : d ∈ Dsub t Q) : d ∈ hS.Wsub hZ ∨ d * t ∈ hS.Wsub hZ := by
  by_cases h : d ∈ hS.Wsub hZ
  · exact Or.inl h
  · right
    have hidx : ((hS.Wsub hZ).subgroupOf (Dsub t Q)).index = 2 := hS.relIndex_Wsub_D hZ
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨d, hd⟩) (b := ⟨t, hS.t_mem_D⟩)).2
      ⟨fun h' => absurd h' h, fun h' => absurd h' (hS.t_not_mem_Wsub hZ)⟩
    exact this

theorem mem_Wsub_of_mem_centralizer [Finite G] {d : G} (hd : d ∈ Dsub t Q)
    (hc : d ∈ centralizer (hS.Wsub hZ : Set G)) : d ∈ hS.Wsub hZ := by
  rcases hS.mem_Wsub_or hZ hd with h | h
  · exact h
  · exfalso
    have htC : t ∈ centralizer (hS.Wsub hZ : Set G) := by
      have := mul_mem (inv_mem hc) (hS.Wsub_le_centralizer hZ h)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have hWQ : hS.Wsub hZ ≤ Q := fun w hw =>
      hS.mem_Q_of_comm_t hZ hw (mem_centralizer_iff.1 htC w hw)
    exact absurd (Subgroup.card_le_of_le hWQ) (not_le.2 (hS.card_Q_lt_Wsub hZ))

theorem Dsub_le_K [Finite G] :
    Dsub t Q ≤ centralizer (hS.Wsub hZ : Set G) ⊔ zpowers t := by
  intro d hd
  rcases hS.mem_Wsub_or hZ hd with h | h
  · exact mem_sup_left (hS.Wsub_le_centralizer hZ h)
  · have : d = d * t * t⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_left (hS.Wsub_le_centralizer hZ h))
      (inv_mem (mem_sup_right (mem_zpowers t)))

theorem isPGroup_Dsub [Finite G] : IsPGroup 2 (Dsub t Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 13) (by rw [hS.card_D hZ]; norm_num)

theorem t_normalizes_C [Finite G] :
    t ∈ normalizer (centralizer (hS.Wsub hZ : Set G) : Set G) :=
  mem_normalizer_centralizer (hS.t_mem_normalizer_Wsub hZ)

theorem mem_K_iff [Finite G] {x : G} :
    x ∈ centralizer (hS.Wsub hZ : Set G) ⊔ zpowers t ↔
      x ∈ centralizer (hS.Wsub hZ : Set G) ∨ x * t ∈ centralizer (hS.Wsub hZ : Set G) :=
  mem_sup_zpowers_iff (hS.t_normalizes_C hZ) hS.shape.mul_self

theorem mem_D_of_mem_centralizer_normalizer [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1)
    {c : G} (hc : c ∈ centralizer (hS.Wsub hZ : Set G)) (hcD : c ∈ normalizer (Dsub t Q : Set G)) :
    c ∈ Dsub t Q := by
  have hcQ : c ∈ centralizer (Q : Set G) := centralizer_le (SetLike.coe_subset_coe.2
    (hS.Q_le_Wsub hZ)) hc
  have h1 : c * t * c⁻¹ ∈ Dsub t Q := (mem_normalizer_iff.1 hcD t).1 hS.t_mem_D
  have h2 : c * t * c⁻¹ ∉ hS.Wsub hZ := fun h => by
    apply hS.t_not_mem_Wsub hZ
    have := (mem_normalizer_iff.1 (centralizer_le_normalizer _ hc) t).2 h
    exact this
  have hw : c * t * c⁻¹ * t ∈ hS.Wsub hZ := (hS.mem_Wsub_or hZ h1).resolve_left h2
  have hwQ : c * t * c⁻¹ * t ∈ Q := by
    refine hS.mem_Q_of_invol hZ hW2 hw ?_
    have ht2 := hS.shape.mul_self
    have hwt : c * t * c⁻¹ * t * t = c * t * c⁻¹ := by rw [mul_assoc (c * t * c⁻¹), ht2, mul_one]
    rw [hwt]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have hcE : c ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective])
    rintro _ ⟨e, he, rfl⟩
    change c * e * c⁻¹ ∈ (Q ⊔ zpowers t : Subgroup G)
    obtain ⟨q, hq, h | h⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 he <;> rw [h]
    · rw [← mem_centralizer_iff.1 hcQ q hq, mul_inv_cancel_right]
      exact mem_sup_left hq
    · have : c * (q * t) * c⁻¹ = q * (c * t * c⁻¹ * t) * t := by
        rw [show c * (q * t) * c⁻¹ = (c * q * c⁻¹) * (c * t * c⁻¹) by group,
          ← mem_centralizer_iff.1 hcQ q hq, mul_inv_cancel_right]
        rw [mul_assoc q, mul_assoc (c * t * c⁻¹), hS.shape.mul_self, mul_one]
      rw [this]
      exact mul_mem (mul_mem (mem_sup_left hq) (mem_sup_left hwQ)) (mem_sup_right (mem_zpowers t))
  exact ⟨hcE, hcQ⟩

theorem Dsub_maximal [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (T : Subgroup G)
    (hTK : T ≤ centralizer (hS.Wsub hZ : Set G) ⊔ zpowers t) (hT : IsPGroup 2 T)
    (hDT : Dsub t Q ≤ T) : T = Dsub t Q := by
  by_contra hne
  obtain ⟨n, hnT, hnN, hnD⟩ := exists_mem_normalizer_not_mem hT (lt_of_le_of_ne hDT (Ne.symm hne))
  rcases (hS.mem_K_iff hZ).1 (hTK hnT) with hn | hn
  · exact hnD (hS.mem_D_of_mem_centralizer_normalizer hZ hW2 hn hnN)
  · have htN : t ∈ normalizer (Dsub t Q : Set G) := le_normalizer hS.t_mem_D
    have := hS.mem_D_of_mem_centralizer_normalizer hZ hW2 hn (mul_mem hnN htN)
    apply hnD
    have h2 := mul_mem this (inv_mem hS.t_mem_D)
    rwa [mul_inv_cancel_right] at h2


theorem K_le_normalizer_Wsub [Finite G] :
    centralizer (hS.Wsub hZ : Set G) ⊔ zpowers t ≤ normalizer (hS.Wsub hZ : Set G) :=
  sup_le (centralizer_le_normalizer _) (zpowers_le.2 (hS.t_mem_normalizer_Wsub hZ))

theorem K_le_normalizer_C [Finite G] :
    centralizer (hS.Wsub hZ : Set G) ⊔ zpowers t ≤
      normalizer (centralizer (hS.Wsub hZ : Set G) : Set G) :=
  sup_le le_normalizer (zpowers_le.2 (hS.t_normalizes_C hZ))

theorem sylow_Wsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (S : Subgroup G)
    (hSC : S ≤ centralizer (hS.Wsub hZ : Set G)) (hSp : IsPGroup 2 S) : S ≤ hS.Wsub hZ := by
  obtain ⟨k, hk, hkS⟩ := exists_conj_le_of_maximal (hS.Dsub_le_K hZ) (hS.isPGroup_Dsub hZ)
    (hS.Dsub_maximal hZ hW2) (hSC.trans le_sup_left) hSp
  intro x hx
  have h1 : k * x * k⁻¹ ∈ centralizer (hS.Wsub hZ : Set G) :=
    (mem_normalizer_iff.1 (hS.K_le_normalizer_C hZ hk) x).1 (hSC hx)
  have h2 := hS.mem_Wsub_of_mem_centralizer hZ (hkS x hx) h1
  exact (mem_normalizer_iff.1 (hS.K_le_normalizer_Wsub hZ hk) x).2 h2

theorem t_not_mem_centralizer [Finite G] : t ∉ centralizer (hS.Wsub hZ : Set G) := by
  intro htC
  have hWQ : hS.Wsub hZ ≤ Q := fun w hw =>
    hS.mem_Q_of_comm_t hZ hw (mem_centralizer_iff.1 htC w hw)
  exact absurd (Subgroup.card_le_of_le hWQ) (not_le.2 (hS.card_Q_lt_Wsub hZ))

theorem comm_t_mem_C [Finite G] {k : G} (hk : k ∈ centralizer (hS.Wsub hZ : Set G) ⊔ zpowers t) :
    k * t * k⁻¹ * t⁻¹ ∈ centralizer (hS.Wsub hZ : Set G) := by
  have hC := hS.t_normalizes_C hZ
  rcases (hS.mem_K_iff hZ).1 hk with h | h
  · rw [show k * t * k⁻¹ * t⁻¹ = k * (t * k⁻¹ * t⁻¹) by group]
    exact mul_mem h ((mem_normalizer_iff.1 hC _).1 (inv_mem h))
  · rw [show k * t * k⁻¹ * t⁻¹ = (k * t) * (t * (k * t)⁻¹ * t⁻¹) by group]
    exact mul_mem h ((mem_normalizer_iff.1 hC _).1 (inv_mem h))

theorem conj_Q_mem_Q [Finite G] {y : G} (hyt : y * t = t * y)
    (hyW : y ∈ normalizer (hS.Wsub hZ : Set G)) {q : G} (hq : q ∈ Q) : y * q * y⁻¹ ∈ Q := by
  have hyt' : y⁻¹ * t = t * y⁻¹ := by
    calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
      _ = t * y⁻¹ := by group
  have hqt := hS.shape.commute_of_mem (hS.rad.Q_le_L hq)
  refine hS.mem_Q_of_comm_t hZ ((mem_normalizer_iff.1 hyW q).1 (hS.Q_le_Wsub hZ hq)) ?_
  calc y * q * y⁻¹ * t = y * q * (y⁻¹ * t) := by group
    _ = y * q * (t * y⁻¹) := by rw [hyt']
    _ = y * (q * t) * y⁻¹ := by group
    _ = y * (t * q) * y⁻¹ := by rw [hqt]
    _ = y * t * q * y⁻¹ := by group
    _ = t * y * q * y⁻¹ := by rw [hyt]
    _ = t * (y * q * y⁻¹) := by group


theorem mem_P_sup_of_comm [Finite G] {y : G} (hyt : y * t = t * y)
    (hyW : y ∈ normalizer (hS.Wsub hZ : Set G)) : y ∈ P ⊔ zpowers t := by
  have key : ∀ y : G, y * t = t * y → y ∈ normalizer (hS.Wsub hZ : Set G) →
      ∀ e ∈ (Q ⊔ zpowers t : Subgroup G), y * e * y⁻¹ ∈ (Q ⊔ zpowers t : Subgroup G) := by
    intro y hyt hyW e he
    obtain ⟨q, hq, h | h⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 he <;> rw [h]
    · exact mem_sup_left (hS.conj_Q_mem_Q hZ hyt hyW hq)
    · have : y * (q * t) * y⁻¹ = y * q * y⁻¹ * (y * t * y⁻¹) := by group
      rw [this, hyt, mul_inv_cancel_right]
      exact mul_mem (mem_sup_left (hS.conj_Q_mem_Q hZ hyt hyW hq)) (mem_sup_right (mem_zpowers t))
  have hyt' : y⁻¹ * t = t * y⁻¹ := by
    calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
      _ = t * y⁻¹ := by group
  have hN : y ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
    refine mem_normalizer_iff.2 fun e => ⟨key y hyt hyW e, fun he => ?_⟩
    have := key y⁻¹ hyt' (inv_mem hyW) _ he
    simpa [mul_assoc] using this
  rw [← hS.shape.normalizer_eq]
  exact ⟨mem_centralizer_singleton_iff.2 hyt, hN⟩

theorem mem_sup_of_comm [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {x : G}
    (hx : x ∈ normalizer (hS.Wsub hZ : Set G))
    (hc : x * t * x⁻¹ * t⁻¹ ∈ centralizer (hS.Wsub hZ : Set G)) :
    x ∈ centralizer (hS.Wsub hZ : Set G) ⊔ (P ⊔ zpowers t) := by
  have ht2 := hS.shape.mul_self
  obtain ⟨s, hs⟩ : ∃ s, s = x * t * x⁻¹ := ⟨_, rfl⟩
  have hs2 : s * s = 1 := by
    rw [hs]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have hsK : s ∈ centralizer (hS.Wsub hZ : Set G) ⊔ zpowers t := by
    rw [show s = (x * t * x⁻¹ * t⁻¹) * t by rw [hs]; group]
    exact mul_mem (mem_sup_left hc) (mem_sup_right (mem_zpowers t))
  obtain ⟨k, hk, hks⟩ := exists_conj_le_of_maximal (hS.Dsub_le_K hZ) (hS.isPGroup_Dsub hZ)
    (hS.Dsub_maximal hZ hW2) (zpowers_le.2 hsK) (isPGroup_zpowers_of_sq hs2)
  have hd : k * s * k⁻¹ ∈ Dsub t Q := hks s (mem_zpowers s)
  have hdC : k * s * k⁻¹ * t⁻¹ ∈ centralizer (hS.Wsub hZ : Set G) := by
    have h1 := hS.comm_t_mem_C hZ hk
    have h2 : k * (x * t * x⁻¹ * t⁻¹) * k⁻¹ ∈ centralizer (hS.Wsub hZ : Set G) :=
      (mem_normalizer_iff.1 (hS.K_le_normalizer_C hZ hk) _).1 hc
    rw [show k * s * k⁻¹ * t⁻¹ = k * (x * t * x⁻¹ * t⁻¹) * k⁻¹ * (k * t * k⁻¹ * t⁻¹) by
      rw [hs]; group]
    exact mul_mem h2 h1
  have hdW : k * s * k⁻¹ ∉ hS.Wsub hZ := fun h => hS.t_not_mem_centralizer hZ (by
    have := mul_mem (inv_mem hdC) (hS.Wsub_le_centralizer hZ h)
    rwa [show (k * s * k⁻¹ * t⁻¹)⁻¹ * (k * s * k⁻¹) = t by group] at this)
  have hw : k * s * k⁻¹ * t ∈ hS.Wsub hZ := (hS.mem_Wsub_or hZ hd).resolve_left hdW
  have hwQ : k * s * k⁻¹ * t ∈ Q := by
    refine hS.mem_Q_of_invol hZ hW2 hw ?_
    rw [mul_assoc (k * s * k⁻¹) t t, ht2, mul_one]
    calc k * s * k⁻¹ * (k * s * k⁻¹) = k * (s * s) * k⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  obtain ⟨v, hv⟩ := hS.rad.mem_ψ _ hwQ
  obtain ⟨r, hrW, hrv⟩ := hS.tauD_surj_Wsub hZ v
  have hr : r * t * r⁻¹ = k * s * k⁻¹ := by
    rw [hS.conj_t_D hZ (hS.Wsub_le_D hZ hrW), hrv, hv,
      ← hS.shape.commute_of_mem (hS.rad.Q_le_L hwQ), mul_assoc (k * s * k⁻¹) t t, ht2, mul_one]
  have hy : r⁻¹ * k * x * t * (r⁻¹ * k * x)⁻¹ = t := by
    calc r⁻¹ * k * x * t * (r⁻¹ * k * x)⁻¹ = r⁻¹ * (k * (x * t * x⁻¹) * k⁻¹) * r := by group
      _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [← hs, hr]
      _ = t := by group
  have hyt : r⁻¹ * k * x * t = t * (r⁻¹ * k * x) := by
    calc r⁻¹ * k * x * t = r⁻¹ * k * x * t * (r⁻¹ * k * x)⁻¹ * (r⁻¹ * k * x) := by group
      _ = t * (r⁻¹ * k * x) := by rw [hy]
  have hyN : r⁻¹ * k * x ∈ normalizer (hS.Wsub hZ : Set G) :=
    mul_mem (mul_mem (inv_mem (le_normalizer hrW)) (hS.K_le_normalizer_Wsub hZ hk)) hx
  have e : k⁻¹ * r * (r⁻¹ * k * x) = x := by group
  rw [← e]
  exact mul_mem (mul_mem (sup_le_sup_left (le_sup_right : zpowers t ≤ P ⊔ zpowers t)
    (centralizer (hS.Wsub hZ : Set G)) (inv_mem hk))
    (mem_sup_left (hS.Wsub_le_centralizer hZ hrW))) (mem_sup_right (hS.mem_P_sup_of_comm hZ hyt hyN))

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
