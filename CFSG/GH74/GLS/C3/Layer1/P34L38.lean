module

public import CFSG.GH74.GLS.C3.Layer1.P34Cyc
public import CFSG.GH74.GLS.C3.Layer1.P34T0Card

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}

theorem lemma38 (c : Cfg34 X T P Q x z f h) (hD : DihedralShapeFacts) (hQ : QShapeFacts)
    (h37 : Lemma37 T z) : Lemma38 T P z := by
  intro g hgT
  by_contra hgz
  have hnotZ0 : g⁻¹ * z * g ∉ Z0 T := fun hmem => hgz (h37 g hmem)
  obtain ⟨h8, hPp, hPgen, hPz⟩ := hD X P c.P_dihedral
  obtain ⟨-, -, hzcomm, A, hAP, hAcyc, -, hAuniq, hAinv⟩ :=
    hPz z c.z_mem c.z_order c.z_central
  obtain ⟨-, ⟨Q₀, hQ₀Q, hQ₀norm, hQ₀cyc, hQ₀inv⟩, hQ3, -⟩ :=
    hQ X T Q x c.T_pgroup c.Q_le c.Q_norm c.x_mem_Q c.x_order c.x_central c.Q_shape
  have := hAcyc
  have := hQ₀cyc
  have hAnorm := normalized_of_unique_cyclic hAP hAcyc hAuniq c.P_norm
  set Pg : Subgroup X := conjSubgroup P g with hPg
  have hPgT : ∀ b ∈ Pg, b ∈ T := by
    intro b hb
    rw [hPg, mem_conjSubgroup_iff] at hb
    have := hgT _ hb
    have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    rwa [e] at this
  obtain ⟨hz_Pg, hzc_Pg, huniq_Pg⟩ := c.conj_basic g
  set K : Subgroup X := ((P ⊔ Q) ⊓ centralizer (A : Set X)) ⊓ centralizer (Q₀ : Set X) with hK
  have hKcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ K := by
    intro a ha b hb
    refine ⟨⟨c.kf_abelian a ha b hb, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
      exact (comm_cent_cyclic (A := A) hAnorm ha hb y hy).symm
    · refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
      exact (comm_cent_cyclic (A := Q₀) hQ₀norm ha hb y hy).symm
  have hzgK : g⁻¹ * z * g ∈ K := by
    have h1 : g⁻¹ * z * g ∈ ⁅Pg, Pg⁆ := by
      have hz' : g⁻¹ * z * g = (MulAut.conj g⁻¹).toMonoidHom z := by simp
      have : (MulAut.conj g⁻¹).toMonoidHom z ∈ ⁅P, P⁆.map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨z, hzcomm, rfl⟩
      rw [Subgroup.map_commutator] at this
      rw [hz']
      exact this
    refine (Subgroup.commutator_le.2 ?_ : ⁅Pg, Pg⁆ ≤ K) h1
    intro a ha b hb
    exact hKcomm a (hPgT a ha) b (hPgT b hb)
  obtain ⟨⟨hzgR, hzgA⟩, hzgQ₀⟩ := hzgK
  obtain ⟨p, hp, q, hq, hpq⟩ := c.mem_PQ.1 hzgR
  have hzg2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [c.z_sq]; group
  have hpq_comm := c.PQ_comm p hp q hq
  have hp2 : p * p = 1 ∧ q * q = 1 := by
    have h1 : (p * q) * (p * q) = (p * p) * (q * q) := by
      calc (p * q) * (p * q) = p * (q * p) * q := by group
        _ = p * (p * q) * q := by rw [← hpq_comm]
        _ = (p * p) * (q * q) := by group
    rw [← hpq, hzg2] at h1
    have h2 : p * p = (q * q)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
    have h3 : p * p ∈ P ⊓ Q := ⟨P.mul_mem hp hp, by rw [h2]; exact Q.inv_mem (Q.mul_mem hq hq)⟩
    rw [c.PQ_inf, Subgroup.mem_bot] at h3
    refine ⟨h3, ?_⟩
    rw [h3, one_mul] at h1
    exact h1.symm
  have hpA : ∀ a ∈ A, p * a = a * p := by
    intro a ha
    have hqa := c.PQ_comm a (hAP ha) q hq
    have : a * p * q = p * a * q := by
      calc a * p * q = a * (p * q) := by group
        _ = (p * q) * a := by rw [← hpq]; exact hzgA a ha
        _ = p * (q * a) := by group
        _ = p * (a * q) := by rw [hqa]
        _ = p * a * q := by group
    exact (mul_right_cancel this).symm
  have hp1z : p = 1 ∨ p = z := hAinv p hp hp2.1 hpA
  have hqQ₀ : ∀ y ∈ Q₀, q * y = y * q := by
    intro y hy
    have hpy := c.PQ_comm p hp y (hQ₀Q hy)
    have h1 : y * (p * q) = (p * q) * y := by rw [← hpq]; exact hzgQ₀ y hy
    have : p * (y * q) = p * (q * y) := by
      calc p * (y * q) = (p * y) * q := by group
        _ = (y * p) * q := by rw [hpy]
        _ = y * (p * q) := by group
        _ = (p * q) * y := h1
        _ = p * (q * y) := by group
    exact (mul_left_cancel this).symm
  have hqcen : ∀ y ∈ Q, q * y = y * q := hQ₀inv q hq hp2.2 hqQ₀
  have hzgcentR : ∀ r ∈ P ⊔ Q, (g⁻¹ * z * g) * r = r * (g⁻¹ * z * g) := by
    intro r hr
    obtain ⟨p', hp', q', hq', rfl⟩ := c.mem_PQ.1 hr
    have hpp' : p * p' = p' * p := by
      rcases hp1z with h1 | h1
      · rw [h1, one_mul, mul_one]
      · rw [h1]; exact (c.z_central p' hp').symm
    have hqq' : q * q' = q' * q := hqcen q' hq'
    have hpq' : p * q' = q' * p := c.PQ_comm p hp q' hq'
    have hqp' : q * p' = p' * q := (c.PQ_comm p' hp' q hq).symm
    rw [hpq]
    calc p * q * (p' * q') = p * (q * p') * q' := by group
      _ = p * (p' * q) * q' := by rw [hqp']
      _ = (p * p') * (q * q') := by group
      _ = (p' * p) * (q' * q) := by rw [hpp', hqq']
      _ = p' * (p * q') * q := by group
      _ = p' * (q' * p) * q := by rw [hpq']
      _ = p' * q' * (p * q) := by group
  have hzgT : g⁻¹ * z * g ∈ T := hPgT _ hz_Pg
  by_cases hq1 : q = 1
  · rw [hq1, mul_one] at hpq
    rcases hp1z with h1 | h1
    · apply c.z_ne_one
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [hpq, h1]; group
    · exact hgz (hpq.trans h1)
  by_cases hqx : q = x
  · apply hnotZ0
    rw [hpq, hqx]
    rcases hp1z with h1 | h1
    · rw [h1, one_mul]; exact mem_Z0 c.x_mem c.x_sq c.x_central
    · rw [h1]; exact Z0_mul (mem_Z0 c.z_mem_T c.z_sq c.z_cent_T) (mem_Z0 c.x_mem c.x_sq c.x_central)
  have hQ4 : Nat.card ↥Q = 4 := hQ3 q hq hqcen hp2.2 hq1 hqx
  have hT0card : Nat.card ↥(T0 T) ≤ 16 * Nat.card ↥P := by
    have := c.card_T0_le
    rw [hQ4] at this
    omega
  have hx2 : x * x = 1 := c.x_sq
  have hxP : x ∉ P := fun hx => c.x_ne_one (by
    have : x ∈ P ⊓ Q := ⟨hx, c.x_mem_Q⟩
    rw [c.PQ_inf, Subgroup.mem_bot] at this
    exact this)
  have hPx : P ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyP, hyx⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hyx
    rw [Subgroup.mem_bot]
    have hmod : x ^ k = x ^ (k % 2) := by
      have := zpow_mod_orderOf x k
      rw [c.x_order] at this
      simpa using this.symm
    have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk with hk | hk
    · rw [hmod, hk]; simp
    · exfalso
      apply hxP
      rw [hmod, hk] at hyP
      simpa using hyP
  have hxnorm : zpowers x ≤ normalizer (P : Set X) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact c.P_norm x c.x_mem a ha
    · intro ha
      have := c.P_norm x⁻¹ (T.inv_mem c.x_mem) _ ha
      simpa [mul_assoc] using this
  have hcoeXP : ((P ⊔ zpowers x : Subgroup X) : Set X) = (P : Set X) * (zpowers x : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P (zpowers x) hxnorm
  have hcardXP : Nat.card ↥(P ⊔ zpowers x) = Nat.card ↥P * 2 := by
    have h1 : Nat.card ↥((P ⊔ zpowers x : Subgroup X) : Set X) = Nat.card ↥(P ⊔ zpowers x) := rfl
    rw [← h1, hcoeXP, card_mul_of_inf_bot hPx, Nat.card_zpowers, c.x_order]
  have hXPT : P ⊔ zpowers x ≤ T := sup_le c.P_le (zpowers_le.2 c.x_mem)
  have hXPnorm : ∀ t ∈ T, ∀ y ∈ P ⊔ zpowers x, t * y * t⁻¹ ∈ P ⊔ zpowers x := by
    intro t ht y hy
    have hy' : y ∈ ((P ⊔ zpowers x : Subgroup X) : Set X) := hy
    rw [hcoeXP] at hy'
    obtain ⟨a, ha, xx, hxx, rfl⟩ := hy'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxx
    have hxk : t * x ^ k * t⁻¹ = x ^ k := by
      have := (Commute.zpow_right (show Commute t x from c.x_central t ht) k).eq
      calc t * x ^ k * t⁻¹ = (t * x ^ k) * t⁻¹ := rfl
        _ = (x ^ k * t) * t⁻¹ := by rw [this]
        _ = x ^ k := by group
    have : t * (a * x ^ k) * t⁻¹ = (t * a * t⁻¹) * x ^ k := by
      calc t * (a * x ^ k) * t⁻¹ = (t * a * t⁻¹) * (t * x ^ k * t⁻¹) := by group
        _ = (t * a * t⁻¹) * x ^ k := by rw [hxk]
    rw [this]
    exact (P ⊔ zpowers x).mul_mem (mem_sup_left (c.P_norm t ht a ha)) (mem_sup_right (mem_zpowers_iff.2 ⟨k, rfl⟩))
  have hPgle : Pg ≤ T := fun b hb => hPgT b hb
  have hPgp : IsPGroup 2 ↥Pg := c.T_pgroup.to_le hPgle
  have hPT0 : P ≤ T0 T := fun a ha => closure_mono
    (show {p : X | p ∈ P ∧ p * p = 1} ⊆ {t : X | t ∈ T ∧ t * t = 1} from
      fun p hp => ⟨c.P_le hp.1, hp.2⟩) (hPgen a ha)
  have hclos : ∀ y ∈ closure {p : X | p ∈ P ∧ p * p = 1},
      (MulAut.conj g⁻¹).toMonoidHom y ∈ T0 T := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem p hp =>
      have hpg : (MulAut.conj g⁻¹).toMonoidHom p ∈ Pg := ⟨p, hp.1, rfl⟩
      refine mem_T0 (hPgT _ hpg) ?_
      rw [← map_mul, hp.2, map_one]
    | one => rw [map_one]; exact (T0 T).one_mem
    | mul a b _ _ ha hb => rw [map_mul]; exact (T0 T).mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact (T0 T).inv_mem ha
  have hPgT0 : Pg ≤ T0 T := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact hclos a (hPgen a ha)
  have hPgXP : Pg ⊓ (P ⊔ zpowers x) = ⊥ := by
    by_contra hne
    obtain ⟨n, hn, hn1, hncent⟩ := exists_central_of_normal (W := Pg) hPgp
      (N := Pg ⊓ (P ⊔ zpowers x)) inf_le_left
      (fun w hw n hn => ⟨Pg.mul_mem (Pg.mul_mem hw hn.1) (Pg.inv_mem hw),
        hXPnorm w (hPgT w hw) n hn.2⟩) hne
    have h1 := huniq_Pg n hn.1 hncent
    have hnz : n = g⁻¹ * z * g := by
      rcases h1 with h1 | h1
      · exact absurd h1 hn1
      · exact h1
    have hzgXP : g⁻¹ * z * g ∈ P ⊔ zpowers x := hnz ▸ hn.2
    apply hnotZ0
    refine mem_Z0 hzgT hzg2 ?_
    have hzgXP' : g⁻¹ * z * g ∈ ((P ⊔ zpowers x : Subgroup X) : Set X) := hzgXP
    rw [hcoeXP] at hzgXP'
    obtain ⟨a, ha, xx, hxx, hax⟩ := hzgXP'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxx
    have hax' : a * x ^ k = g⁻¹ * z * g := hax
    have haP : ∀ b ∈ P, b * a = a * b := by
      intro b hb
      have h1 := hzgcentR b (mem_sup_left hb)
      rw [← hax'] at h1
      have hxk : x ^ k * b = b * x ^ k :=
        (Commute.zpow_left (show Commute x b from (c.PQ_comm b hb x c.x_mem_Q).symm) k).eq
      have : a * b * x ^ k = b * a * x ^ k := by
        calc a * b * x ^ k = a * (b * x ^ k) := by group
          _ = a * (x ^ k * b) := by rw [hxk]
          _ = (a * x ^ k) * b := by group
          _ = b * (a * x ^ k) := h1
          _ = b * a * x ^ k := by group
      exact (mul_right_cancel this).symm
    have ha1z : a = 1 ∨ a = z := c.z_unique a ha (fun b hb => haP b hb)
    intro s hs
    rw [← hax']
    have hsz : s * z = z * s := c.z_cent_T s hs
    have hsx : s * x = x * s := c.x_central s hs
    have hsxk : s * x ^ k = x ^ k * s := (Commute.zpow_right (show Commute s x from hsx) k).eq
    rcases ha1z with h1 | h1
    · rw [h1, one_mul]; exact hsxk
    · rw [h1]
      calc s * (z * x ^ k) = (s * z) * x ^ k := by group
        _ = (z * s) * x ^ k := by rw [hsz]
        _ = z * (s * x ^ k) := by group
        _ = z * (x ^ k * s) := by rw [hsxk]
        _ = (z * x ^ k) * s := by group
  have hcardPgXP := card_mul_of_inf_bot hPgXP
  have hPgcard : Nat.card ↥Pg = Nat.card ↥P := card_conjSubgroup P g
  rw [hPgcard, hcardXP] at hcardPgXP
  have hXPT0 : P ⊔ zpowers x ≤ T0 T :=
    sup_le hPT0 (zpowers_le.2 (mem_T0 c.x_mem c.x_sq))
  have hsubT0 : ((Pg : Subgroup X) : Set X) * ((P ⊔ zpowers x : Subgroup X) : Set X) ⊆
      ((T0 T : Subgroup X) : Set X) := by
    rw [Set.mul_subset_iff]
    intro a ha b hb
    exact (T0 T).mul_mem (hPgT0 ha) (hXPT0 hb)
  have hcard_le : Nat.card ↥(T0 T) ≤ Nat.card ↥(((Pg : Subgroup X) : Set X) *
      ((P ⊔ zpowers x : Subgroup X) : Set X)) := by
    rw [hcardPgXP]
    calc Nat.card ↥(T0 T) ≤ 16 * Nat.card ↥P := hT0card
      _ ≤ Nat.card ↥P * (Nat.card ↥P * 2) := by nlinarith
  have hset : ((Pg : Subgroup X) : Set X) * ((P ⊔ zpowers x : Subgroup X) : Set X) =
      ((T0 T : Subgroup X) : Set X) := by
    refine Set.eq_of_subset_of_ncard_le hsubT0 ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcard_le
  have hXPR : P ⊔ zpowers x ≤ P ⊔ Q := sup_le le_sup_left (zpowers_le.2 (mem_sup_right c.x_mem_Q))
  apply hnotZ0
  refine ⟨hPgT0 hz_Pg, hzg2, fun s hs => ?_⟩
  have hs' : s ∈ ((Pg : Subgroup X) : Set X) * ((P ⊔ zpowers x : Subgroup X) : Set X) := by
    rw [hset]; exact hs
  obtain ⟨a, ha, b, hb, rfl⟩ := hs'
  have h1 := hzc_Pg a ha
  have h2 : (g⁻¹ * z * g) * b = b * (g⁻¹ * z * g) := hzgcentR b (hXPR hb)
  calc a * b * (g⁻¹ * z * g) = a * (b * (g⁻¹ * z * g)) := by group
    _ = a * ((g⁻¹ * z * g) * b) := by rw [h2]
    _ = (a * (g⁻¹ * z * g)) * b := by group
    _ = ((g⁻¹ * z * g) * a) * b := by rw [h1]
    _ = (g⁻¹ * z * g) * (a * b) := by group

end CFSG.GH74.GLS.C3.Layer1.P34
