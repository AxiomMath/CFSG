module

public import CFSG.GH74.GLS.C3.Layer1.St1P89DA
public import CFSG.GH74.GLS.C3.Layer1.St1P89Z

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU1

section DB

variable {G : Type} [Group G] [Finite G] {T P Q S : Subgroup G} {u z x f r s a : G}

theorem Cfg89S.of_mul (sc : Cfg89S G T u S a) {t : G} (ht : t ∈ T) : Cfg89S G T u S (t * a) where
  sylowS := sc.sylowS
  T_le := sc.T_le
  a_mem := S.mul_mem (sc.T_le ht) sc.a_mem
  a_nmem := fun h => sc.a_nmem (by
    have := T.mul_mem (T.inv_mem ht) h
    simpa using this)
  S_split := fun g hg => by
    rcases sc.S_split g hg with h | h
    · exact Or.inl h
    · right
      have e : (t * a)⁻¹ * g = (a⁻¹ * t⁻¹ * a) * (a⁻¹ * g) := by group
      rw [e]
      exact T.mul_mem (sc.conj_inv_mem (T.inv_mem ht)) h
  T_norm := sc.T_norm
  T_cent := sc.T_cent
  Zcyc := sc.Zcyc

theorem Cfg89T.card_P_ge (c : Cfg89T G T P Q u z x f r s) : 8 ≤ Nat.card ↥P := by
  have hd := c.isD8
  have hord : orderOf r = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := r) (by simpa using hd.r2_ne) (by simpa using hd.r4)
    simpa using this
  have hle : zpowers r ≤ P := (Subgroup.zpowers_le).mpr c.r_mem
  have hc4 : Nat.card ↥(zpowers r) = 4 := by rw [Nat.card_zpowers, hord]
  have hdvd : Nat.card ↥(zpowers r) ∣ Nat.card ↥P := Subgroup.card_dvd_of_le hle
  have hge : Nat.card ↥(zpowers r) ≤ Nat.card ↥P := Subgroup.card_le_of_le hle
  by_contra hlt
  push Not at hlt
  have h4 : Nat.card ↥P = 4 := by
    rw [hc4] at hdvd hge
    obtain ⟨k, hk⟩ := hdvd
    omega
  have heq : zpowers r = P := Subgroup.eq_of_le_of_card_ge hle (by rw [hc4, h4])
  have hs : s ∈ zpowers r := by rw [heq]; exact c.s_mem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hcomm : s * r = r * s := by
    rw [← hk]
    exact ((Commute.refl r).zpow_right k).symm.eq
  exact c.s_comm_r_false hcomm

theorem Cfg89T.cent_P_eq (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {t : G} (ht : t ∈ T) (hc : ∀ p ∈ P, t * p = p * t) :
    ∃ i : ℕ, ∃ p' ∈ conjSub a P, t = z ^ i * p' := by
  classical
  have hQcard : Nat.card ↥Q = 4 := c.card_Q sc hQ
  set C : Set G := {t | t ∈ T ∧ ∀ p ∈ P, t * p = p * t} with hC
  let F : Fin 2 × ↥Q × Fin 2 → G := fun w => z ^ (w.1 : ℕ) * (w.2.1 : G) * f ^ (w.2.2 : ℕ)
  have hCsub : C ⊆ Set.range F := by
    rintro t ⟨htT, htc⟩
    obtain ⟨i, q, hq, j, rfl⟩ := c.CTP t htT htc
    refine ⟨(⟨i % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨q, hq⟩, ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [F]
    rw [← pow_eq_pow_mod i c.z_sq, ← pow_eq_pow_mod j c.f2]
  have hCfin : C.Finite := (Set.finite_range F).subset hCsub
  have hupper : C.ncard ≤ 16 := by
    have h1 : (Set.range F).ncard ≤ Nat.card (Fin 2 × ↥Q × Fin 2) := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le (Set.toFinite _)).trans_eq (Set.ncard_univ _)
    calc C.ncard ≤ (Set.range F).ncard := Set.ncard_le_ncard hCsub (Set.finite_range F)
      _ ≤ Nat.card (Fin 2 × ↥Q × Fin 2) := h1
      _ = 16 := by rw [Nat.card_prod, Nat.card_prod, hQcard]; simp
  let H : Fin 2 × ↥(conjSub a P) → G := fun w => z ^ (w.1 : ℕ) * (w.2 : G)
  have hHinj : Function.Injective H := by
    rintro ⟨i, p'⟩ ⟨k, p''⟩ h
    have h' : z ^ (i : ℕ) * (p' : G) = z ^ (k : ℕ) * (p'' : G) := h
    have hz : z ∉ conjSub a P := c.z_not_mem_Pa sc hQ
    have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by have := i.isLt; omega
    have hk : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by have := k.isLt; omega
    rcases hi with hi | hi <;> rcases hk with hk | hk <;> rw [hi, hk] at h'
    · have : (p' : G) = p'' := by simpa using h'
      exact Prod.ext (Fin.ext (by rw [hi, hk])) (Subtype.ext this)
    · exfalso; apply hz
      simp only [pow_zero, one_mul, pow_one] at h'
      have : z = (p' : G) * (p'' : G)⁻¹ := by
        calc z = z * p'' * (p'' : G)⁻¹ := by group
          _ = p' * (p'' : G)⁻¹ := by rw [← h']
      rw [this]; exact (conjSub a P).mul_mem p'.2 ((conjSub a P).inv_mem p''.2)
    · exfalso; apply hz
      simp only [pow_zero, one_mul, pow_one] at h'
      have : z = (p'' : G) * (p' : G)⁻¹ := by
        calc z = z * p' * (p' : G)⁻¹ := by group
          _ = p'' * (p' : G)⁻¹ := by rw [h']
      rw [this]; exact (conjSub a P).mul_mem p''.2 ((conjSub a P).inv_mem p'.2)
    · have : (p' : G) = p'' := by simpa using h'
      exact Prod.ext (Fin.ext (by rw [hi, hk])) (Subtype.ext this)
  have hBC : Set.range H ⊆ C := by
    rintro _ ⟨⟨i, p'⟩, rfl⟩
    have hzT : z ∈ T := c.P_le c.z_mem
    refine ⟨T.mul_mem (T.pow_mem hzT _) (sc.conjSub_le c.P_le p'.2), fun p hp => ?_⟩
    have h1 : z ^ (i : ℕ) * p = p * z ^ (i : ℕ) := (Commute.pow_left (show Commute z p from c.z_comm_P p hp) _).eq
    have h2 : (p' : G) * p = p * p' := (c.P_Pa_comm sc hQ p hp p' p'.2).symm
    calc z ^ (i : ℕ) * (p' : G) * p = z ^ (i : ℕ) * (p' * p) := by group
      _ = z ^ (i : ℕ) * (p * p') := by rw [h2]
      _ = (z ^ (i : ℕ) * p) * p' := by group
      _ = (p * z ^ (i : ℕ)) * p' := by rw [h1]
      _ = p * (z ^ (i : ℕ) * p') := by group
  have hlower : 16 ≤ (Set.range H).ncard := by
    have : (Set.range H).ncard = Nat.card (Fin 2 × ↥(conjSub a P)) := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hHinj, Set.ncard_univ]
    rw [this, Nat.card_prod, card_conjSub]
    have := c.card_P_ge
    simp
    omega
  have hEq : Set.range H = C := Set.eq_of_subset_of_ncard_le hBC (by omega) hCfin
  have htC : t ∈ C := ⟨ht, hc⟩
  rw [← hEq] at htC
  obtain ⟨⟨i, p'⟩, hw⟩ := htC
  exact ⟨i, p', p'.2, hw.symm⟩

theorem Cfg89T.conj_Pa_mem_P (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a) {p' : G}
    (hp' : p' ∈ conjSub a P) : a * p' * a⁻¹ ∈ P := by
  obtain ⟨p, hp, rfl⟩ := mem_conjSub.mp hp'
  have := c.P_norm (a * a) sc.aa_mem p hp
  convert this using 1
  group

theorem Cfg89T.cent_Pa_eq (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {t : G} (ht : t ∈ T) (hc : ∀ p' ∈ conjSub a P, t * p' = p' * t) :
    ∃ i : ℕ, ∃ p ∈ P, t = u ^ i * p := by
  have hc' : a⁻¹ * t * a ∈ T := sc.conj_inv_mem ht
  have hcomm : ∀ p ∈ P, (a⁻¹ * t * a) * p = p * (a⁻¹ * t * a) := by
    intro p hp
    have h := hc (a * p * a⁻¹) (conj_mem_conjSub hp)
    calc (a⁻¹ * t * a) * p = a⁻¹ * (t * (a * p * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * p * a⁻¹) * t) * a := by rw [h]
      _ = p * (a⁻¹ * t * a) := by group
  obtain ⟨i, p', hp', hte⟩ := c.cent_P_eq sc hQ hc' hcomm
  refine ⟨i, a * p' * a⁻¹, c.conj_Pa_mem_P sc hp', ?_⟩
  have e1 : t = a * (a⁻¹ * t * a) * a⁻¹ := by group
  have e2 : a * (z ^ i * p') * a⁻¹ = (a * z * a⁻¹) ^ i * (a * p' * a⁻¹) := by
    rw [conj_pow]; group
  rw [e1, hte, e2, c.aza sc hQ]

theorem Cfg89T.Pa_le_M0 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : conjSub a P ≤ M0 c := by
  intro p' hp'
  have hT : p' ∈ T := sc.conjSub_le c.P_le hp'
  have hcomm : ∀ p ∈ P, p' * p = p * p' := fun p hp => (c.P_Pa_comm sc hQ p hp p' hp').symm
  obtain ⟨i, q, hq, j, hqe⟩ := c.CTP p' hT hcomm
  exact ⟨z ^ i, P.pow_mem c.z_mem i, q, hq, j, hqe⟩

theorem mem_M0_iff (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {t : G} :
    t ∈ M0 c ↔ ∃ p ∈ P, ∃ p' ∈ conjSub a P, t = p * p' := by
  constructor
  · rintro ⟨p, hp, q, hq, i, rfl⟩
    have hyT : q * f ^ i ∈ T := T.mul_mem (c.Q_le hq) (c.f_pow_mem_T i)
    have hyc : ∀ g ∈ P, (q * f ^ i) * g = g * (q * f ^ i) := by
      intro g hg
      calc (q * f ^ i) * g = q * (f ^ i * g) := by group
        _ = q * (g * f ^ i) := by rw [c.f_pow_comm_P i hg]
        _ = (q * g) * f ^ i := by group
        _ = (g * q) * f ^ i := by rw [(c.PQ_comm g hg q hq).symm]
        _ = g * (q * f ^ i) := by group
    obtain ⟨k, p', hp', hk⟩ := c.cent_P_eq sc hQ hyT hyc
    refine ⟨p * z ^ k, P.mul_mem hp (P.pow_mem c.z_mem k), p', hp', ?_⟩
    calc p * q * f ^ i = p * (q * f ^ i) := by group
      _ = p * (z ^ k * p') := by rw [hk]
      _ = p * z ^ k * p' := by group
  · rintro ⟨p, hp, p', hp', rfl⟩
    exact (M0 c).mul_mem (P_le_M0 c hp) (c.Pa_le_M0 sc hQ hp')

theorem Cfg89T.a_conj_M0 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {m : G} (hm : m ∈ M0 c) : a * m * a⁻¹ ∈ M0 c := by
  obtain ⟨p, hp, p', hp', rfl⟩ := (mem_M0_iff c sc hQ).mp hm
  have e : a * (p * p') * a⁻¹ = (a * p * a⁻¹) * (a * p' * a⁻¹) := by group
  rw [e]
  exact (M0 c).mul_mem (c.Pa_le_M0 sc hQ (conj_mem_conjSub hp)) (P_le_M0 c (c.conj_Pa_mem_P sc hp'))

theorem Cfg89T.M0_norm_S (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {g m : G} (hg : g ∈ S) (hm : m ∈ M0 c) : g * m * g⁻¹ ∈ M0 c := by
  rcases sc.S_split g hg with h | h
  · exact M0_norm c h hm
  · have e : g * m * g⁻¹ = a * ((a⁻¹ * g) * m * (a⁻¹ * g)⁻¹) * a⁻¹ := by group
    rw [e]
    exact c.a_conj_M0 sc hQ (M0_norm c h hm)

theorem x_not_mem_M0 (c : Cfg89T G T P Q u z x f r s) : x ∉ M0 c := by
  intro hx
  obtain ⟨p, hp, q, hq, i, hxe⟩ := hx
  apply c.isD8.not_inner_of_shape c.x_r c.x_s
  refine ⟨p, hp, fun g hg => ?_⟩
  have hy : (q * f ^ i) * g = g * (q * f ^ i) := by
    calc (q * f ^ i) * g = q * (f ^ i * g) := by group
      _ = q * (g * f ^ i) := by rw [c.f_pow_comm_P i hg]
      _ = (q * g) * f ^ i := by group
      _ = (g * q) * f ^ i := by rw [(c.PQ_comm g hg q hq).symm]
      _ = g * (q * f ^ i) := by group
  rw [hxe]
  calc p * q * f ^ i * g * (p * q * f ^ i)⁻¹ = p * ((q * f ^ i) * g * (q * f ^ i)⁻¹) * p⁻¹ := by group
    _ = p * g * p⁻¹ := by rw [hy]; group

theorem Cfg89T.x_outer_Pa (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) :
    ¬ ∃ d' ∈ conjSub a P, ∀ p ∈ conjSub a P, x * p * x⁻¹ = d' * p * d'⁻¹ := by
  rintro ⟨d', hd', h⟩
  have hd'T : d' ∈ T := sc.conjSub_le c.P_le hd'
  have hyT : x * d'⁻¹ ∈ T := T.mul_mem c.x_mem (T.inv_mem hd'T)
  have hyc : ∀ p ∈ conjSub a P, (x * d'⁻¹) * p = p * (x * d'⁻¹) := by
    intro p hp
    have hp0 : d'⁻¹ * p * d' ∈ conjSub a P :=
      (conjSub a P).mul_mem ((conjSub a P).mul_mem ((conjSub a P).inv_mem hd') hp) hd'
    have h1 := h _ hp0
    have e : d' * (d'⁻¹ * p * d') * d'⁻¹ = p := by group
    rw [e] at h1
    calc (x * d'⁻¹) * p = (x * (d'⁻¹ * p * d') * x⁻¹) * x * d'⁻¹ := by group
      _ = p * x * d'⁻¹ := by rw [h1]
      _ = p * (x * d'⁻¹) := by group
  obtain ⟨i, p0, hp0, hte⟩ := c.cent_Pa_eq sc hQ hyT hyc
  have hmem : (u ^ i * p0) * d' ∈ M0 c :=
    (M0 c).mul_mem ((M0 c).mul_mem (Q_le_M0 c (Q.pow_mem c.u_mem i)) (P_le_M0 c hp0)) (c.Pa_le_M0 sc hQ hd')
  have hx : x = (u ^ i * p0) * d' := by
    calc x = (x * d'⁻¹) * d' := by group
      _ = (u ^ i * p0) * d' := by rw [hte]
  have key : ∀ y : G, y = (u ^ i * p0) * d' → y ∈ M0 c := fun y hy => by rw [hy]; exact hmem
  exact x_not_mem_M0 c (key x hx)

theorem Cfg89T.x_shape_Pa (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) :
    x * (a * r * a⁻¹) * x⁻¹ = (a * r * a⁻¹)⁻¹ ∧
    (x * (a * s * a⁻¹) * x⁻¹ = (a * r * a⁻¹) * (a * s * a⁻¹) ∨
      x * (a * s * a⁻¹) * x⁻¹ = (a * r * a⁻¹) ^ 3 * (a * s * a⁻¹)) :=
  (c.isD8_Pa sc hQ).outer_shape c.x2 (fun p hp => sc.conjSub_norm c.P_norm x c.x_mem p hp)
    (c.x_outer_Pa sc hQ)

theorem Cfg89T.PPa_unique (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {p π p' π' : G} (hp : p ∈ P) (hπ : π ∈ P) (hp' : p' ∈ conjSub a P)
    (hπ' : π' ∈ conjSub a P) (h : p * p' = π * π') : p = π ∧ p' = π' := by
  have h1 : π⁻¹ * p = π' * p'⁻¹ := by
    calc π⁻¹ * p = π⁻¹ * (p * p') * p'⁻¹ := by group
      _ = π⁻¹ * (π * π') * p'⁻¹ := by rw [h]
      _ = π' * p'⁻¹ := by group
  have h2 : π⁻¹ * p = 1 :=
    c.P_inf_Pa sc hQ _ (P.mul_mem (P.inv_mem hπ) hp)
      (by rw [h1]; exact (conjSub a P).mul_mem hπ' ((conjSub a P).inv_mem hp'))
  have h3 : π' * p'⁻¹ = 1 := by rw [← h1]; exact h2
  refine ⟨?_, ?_⟩
  · calc p = π * (π⁻¹ * p) := by group
      _ = π := by rw [h2, mul_one]
  · calc p' = (π' * p'⁻¹)⁻¹ * π' := by group
      _ = π' := by rw [h3]; group

theorem Cfg89T.inv_conj_x (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {t : G} (ht : t ∈ T) (htM : t ∉ M0 c) (ht2 : t ^ 2 = 1) :
    ∃ g ∈ M0 c, t = g * x * g⁻¹ := by
  rcases T_cases c ht with h | ⟨m, hm, rfl⟩
  · exact absurd h htM
  · obtain ⟨p, hp, p', hp', rfl⟩ := (mem_M0_iff c sc hQ).mp hm
    have hx2 : x * x = 1 := by rw [← sq]; exact c.x2
    have h1 : x * (p * p') * x⁻¹ = (p * p')⁻¹ := by
      have h0 : (p * p' * x) ^ 2 = 1 := ht2
      have e : p * p' * x * (p * p' * x) = (p * p') * (x * (p * p') * x⁻¹) * (x * x) := by group
      rw [sq, e, hx2, mul_one] at h0
      exact eq_inv_of_mul_eq_one_right h0
    have hcp : p⁻¹ * p'⁻¹ = p'⁻¹ * p⁻¹ := c.P_Pa_comm sc hQ p⁻¹ (P.inv_mem hp) p'⁻¹ ((conjSub a P).inv_mem hp')
    have hxp : x * p * x⁻¹ ∈ P := c.P_norm x c.x_mem p hp
    have hxp' : x * p' * x⁻¹ ∈ conjSub a P := sc.conjSub_norm c.P_norm x c.x_mem p' hp'
    have h2 : (x * p * x⁻¹) * (x * p' * x⁻¹) = p⁻¹ * p'⁻¹ := by
      calc (x * p * x⁻¹) * (x * p' * x⁻¹) = x * (p * p') * x⁻¹ := by group
        _ = (p * p')⁻¹ := h1
        _ = p'⁻¹ * p⁻¹ := mul_inv_rev p p'
        _ = p⁻¹ * p'⁻¹ := hcp.symm
    obtain ⟨hA, hB⟩ := c.PPa_unique sc hQ hxp (P.inv_mem hp) hxp' ((conjSub a P).inv_mem hp') h2
    obtain ⟨g1, hg1, hg1e⟩ := c.isD8.inverted_decomp c.x_r c.x_s hp hA
    obtain ⟨g2, hg2, hg2e⟩ := (c.isD8_Pa sc hQ).inverted_decomp (c.x_shape_Pa sc hQ).1 (c.x_shape_Pa sc hQ).2 hp' hB
    have hg : g1 * g2 ∈ M0 c := (mem_M0_iff c sc hQ).mpr ⟨g1, hg1, g2, hg2, rfl⟩
    refine ⟨g1 * g2, hg, ?_⟩
    have hxg1 : x * g1⁻¹ * x⁻¹ ∈ P := c.P_norm x c.x_mem g1⁻¹ (P.inv_mem hg1)
    have hA' : g2 * (x * g1⁻¹ * x⁻¹) = (x * g1⁻¹ * x⁻¹) * g2 :=
      (c.P_Pa_comm sc hQ _ hxg1 g2 hg2).symm
    have hB' : g1⁻¹ * g2⁻¹ = g2⁻¹ * g1⁻¹ :=
      c.P_Pa_comm sc hQ g1⁻¹ (P.inv_mem hg1) g2⁻¹ ((conjSub a P).inv_mem hg2)
    rw [hg1e, hg2e]
    calc g1 * (x * g1 * x⁻¹)⁻¹ * (g2 * (x * g2 * x⁻¹)⁻¹) * x
        = g1 * ((x * g1⁻¹ * x⁻¹) * g2) * (x * g2⁻¹ * x⁻¹) * x := by group
      _ = g1 * (g2 * (x * g1⁻¹ * x⁻¹)) * (x * g2⁻¹ * x⁻¹) * x := by rw [hA']
      _ = g1 * g2 * x * (g1⁻¹ * g2⁻¹) := by group
      _ = g1 * g2 * x * (g2⁻¹ * g1⁻¹) := by rw [hB']
      _ = (g1 * g2) * x * (g1 * g2)⁻¹ := by group

theorem Cfg89T.exists_comm_a (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : ∃ g ∈ M0 c, (g⁻¹ * a) * x = x * (g⁻¹ * a) := by
  have hy : a * x * a⁻¹ ∈ T := sc.T_norm a sc.a_mem x c.x_mem
  have hy2 : (a * x * a⁻¹) ^ 2 = 1 := by rw [conj_pow, c.x2]; group
  have hyM : a * x * a⁻¹ ∉ M0 c := by
    intro h
    apply x_not_mem_M0 c
    have := c.M0_norm_S sc hQ (S.inv_mem sc.a_mem) h
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at this
  obtain ⟨g, hg, hyg⟩ := c.inv_conj_x sc hQ hy hyM hy2
  refine ⟨g, hg, ?_⟩
  calc g⁻¹ * a * x = g⁻¹ * (a * x * a⁻¹) * a := by group
    _ = g⁻¹ * (g * x * g⁻¹) * a := by rw [hyg]
    _ = x * (g⁻¹ * a) := by group

end DB




end CFSG.GH74.GLS.C3.Layer1.P89
