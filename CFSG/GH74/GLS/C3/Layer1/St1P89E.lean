module

public import CFSG.GH74.GLS.C3.Layer1.St1P89DC
public import CFSG.GH74.GLS.C3.Layer1.St1P89Mod
public import CFSG.GH74.GLS.C3.Layer1.St1P89E16
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU1


section E

variable {G : Type} [Group G] [Finite G] {T P Q S : Subgroup G} {u z x f r s a : G}

omit [Finite G] in
theorem IsD8.no_z_prod (d : IsD8 P r s z) {y : G} (hyr : y * r * y⁻¹ = r⁻¹)
    (hys : y * s * y⁻¹ = r * s ∨ y * s * y⁻¹ = r ^ 3 * s) {p : G} (hp : p ∈ P) :
    p * (y * p * y⁻¹) ≠ z := by
  obtain ⟨ε, hε, hε13⟩ : ∃ ε : ℕ, y * s * y⁻¹ = r ^ ε * s ∧ (ε = 1 ∨ ε = 3) := by
    rcases hys with h | h
    · exact ⟨1, by rw [h, pow_one], Or.inl rfl⟩
    · exact ⟨3, h, Or.inr rfl⟩
  have hr4 := d.r4
  have hzr : z = r ^ 2 := d.z_eq
  have hr3 : r⁻¹ = r ^ 3 := d.r_inv
  have hz1 : z ≠ 1 := d.z_ne_one
  have hzz : z * z = 1 := by rw [← sq]; exact d.z_sq
  have hyz : y * z * y⁻¹ = z := by
    have h1 : y * z * y⁻¹ = (r⁻¹) ^ 2 := by rw [hzr, ← hyr]; exact (conj_pow).symm
    rw [h1, hr3, hzr]
    calc (r ^ 3) ^ 2 = r ^ 4 * r ^ 2 := by group
      _ = r ^ 2 := by rw [hr4, one_mul]
  have hodd : ∀ m : ℕ, r ^ (2 * m + 1) ≠ z := by
    intro m h
    have e : r ^ (2 * m + 1) = z ^ m * r := by rw [pow_succ, pow_mul, ← hzr]
    rw [e, pow_eq_pow_mod m d.z_sq] at h
    have hm : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize m % 2 = b at hm h
    interval_cases b
    · simp at h; exact d.r_ne_sq (h.trans hzr)
    · simp only [pow_one] at h
      apply d.r3_ne_sq
      calc r ^ 3 = z * r := by rw [hzr]; group
        _ = z := h
        _ = r ^ 2 := hzr
  have hrefl : ∀ k : ℕ, (r ^ k * s) * (y * (r ^ k * s) * y⁻¹) ≠ z := by
    intro k h
    have hyrk : y * r ^ k * y⁻¹ = (r⁻¹) ^ k := by rw [← hyr]; exact (conj_pow).symm
    have key : y * (r ^ k * s) * y⁻¹ = (r⁻¹) ^ k * (r ^ ε * s) := by
      rw [← hε, ← hyrk]; group
    have hsr : ∀ m : ℕ, s * r ^ m * s⁻¹ = (r⁻¹) ^ m := fun m => by
      rw [← d.srs]; exact (conj_pow (a := s) (b := r) (i := m)).symm
    have hsr' : ∀ m : ℕ, s * (r⁻¹) ^ m * s⁻¹ = r ^ m := fun m => by
      have : s * r⁻¹ * s⁻¹ = r := by
        calc s * r⁻¹ * s⁻¹ = (s * r * s⁻¹)⁻¹ := by group
          _ = r := by rw [d.srs, inv_inv]
      calc s * (r⁻¹) ^ m * s⁻¹ = (s * r⁻¹ * s⁻¹) ^ m := (conj_pow (a := s) (b := r⁻¹) (i := m)).symm
        _ = r ^ m := by rw [this]
    have e1 : (r ^ k * s) * ((r⁻¹) ^ k * (r ^ ε * s)) =
        r ^ k * ((s * (r⁻¹) ^ k * s⁻¹) * (s * r ^ ε * s⁻¹)) * (s * s) := by group
    rw [key, e1, hsr' k, hsr ε, ← sq, d.s2, mul_one] at h
    have e2 : r ^ k * (r ^ k * (r⁻¹) ^ ε) = r ^ (2 * k + 3 * ε) := by
      rw [hr3, ← pow_mul, ← pow_add, ← pow_add]; ring_nf
    rw [e2] at h
    have hodd' : ∃ m : ℕ, 2 * k + 3 * ε = 2 * m + 1 := by
      rcases hε13 with rfl | rfl
      · exact ⟨k + 1, by ring⟩
      · exact ⟨k + 4, by ring⟩
    obtain ⟨m, hm⟩ := hodd'
    rw [hm] at h
    exact hodd m h
  intro h
  rcases d.P_cases hp with h' | h' | h' | h' | h' | h' | h' | h'
  · rw [h'] at h
    simp at h
    exact hz1 h.symm
  · rw [h', hyr] at h
    simp at h
    exact hz1 h.symm
  · rw [h', hyz] at h
    exact hz1 (mul_eq_left.mp h)
  · rw [h'] at h
    have e : y * r ^ 3 * y⁻¹ = (r⁻¹) ^ 3 := by rw [← hyr]; exact (conj_pow (a := y) (b := r) (i := 3)).symm
    rw [e] at h
    have : r ^ 3 * (r⁻¹) ^ 3 = 1 := by group
    rw [this] at h
    exact hz1 h.symm
  · exact hrefl 0 (by rw [h'] at h; simpa using h)
  · exact hrefl 1 (by rw [h'] at h; simpa using h)
  · have e : z * s = r ^ 2 * s := by rw [hzr]
    exact hrefl 2 (by rw [h', e] at h; exact h)
  · exact hrefl 3 (by rw [h'] at h; exact h)

theorem Cfg89T.qc_of_Q' (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {q : G} (hq : q ∈ Q)
    {w : G} (hw : w ∈ T) : q * w = w * q := by
  rcases hQ' q hq with h | h
  · rw [h]; simp
  · rw [h]; exact (c.u_central w hw).symm

theorem Cfg89T.u_not_sq (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {t : G}
    (ht : t ∈ T) : t ^ 2 ≠ u := by
  intro h
  have hd := c.isD8
  have hx2 : x * x = 1 := by rw [← sq]; exact c.x2
  have hff : f * f = 1 := by rw [← sq]; exact c.f2
  have hzT : z ∈ T := c.P_le c.z_mem
  have hqc := fun {q : G} (hq : q ∈ Q) {w : G} (hw : w ∈ T) => c.qc_of_Q' hQ' hq hw
  have hq2 : ∀ q ∈ Q, q * q = 1 := by
    intro q hq
    rcases hQ' q hq with h | h
    · rw [h]; simp
    · rw [h, ← sq]; exact c.u2
  rcases T_cases c ht with hM | ⟨m, hm, rfl⟩
  ·
    obtain ⟨p, hp, q, hq, i, rfl⟩ := hM
    have hfiT : f ^ i ∈ T := c.f_pow_mem_T i
    have hyP : ∀ g ∈ P, (q * f ^ i) * g = g * (q * f ^ i) := by
      intro g hg
      calc (q * f ^ i) * g = q * (f ^ i * g) := by group
        _ = q * (g * f ^ i) := by rw [c.f_pow_comm_P i hg]
        _ = (q * g) * f ^ i := by group
        _ = (g * q) * f ^ i := by rw [(c.PQ_comm g hg q hq).symm]
        _ = g * (q * f ^ i) := by group
    have hy2 : (q * f ^ i) ^ 2 = 1 := by
      have hc : Commute q (f ^ i) := hqc hq hfiT
      rw [hc.mul_pow, sq q, hq2 q hq, one_mul, ← pow_mul, mul_comm, pow_mul, c.f2, one_pow]
    have hpy : Commute p (q * f ^ i) := (hyP p hp).symm
    have : (p * q * f ^ i) ^ 2 = p ^ 2 := by
      rw [mul_assoc, hpy.mul_pow, hy2, mul_one]
    rw [this] at h
    rcases hd.sq_mem hp with h1 | h1
    · exact c.u_ne (h.symm.trans h1)
    · exact c.u_ne_z (h.symm.trans h1)
  ·
    obtain ⟨p, hp, q, hq, i, rfl⟩ := hm
    obtain ⟨q0, hq0, hxf⟩ := c.xf
    have hqT : q ∈ T := c.Q_le hq
    have hq0T : q0 ∈ T := c.Q_le hq0
    have hfT : f ∈ T := c.f_mem
    have hxpT : x * p * x⁻¹ ∈ P := c.P_norm x c.x_mem p hp
    have hψ := hd.no_z_prod c.x_r c.x_s hp
    have hZ1 : ∀ w ∈ T, (z * q0) * w = w * (z * q0) := by
      intro w hw
      calc (z * q0) * w = z * (q0 * w) := by group
        _ = z * (w * q0) := by rw [hqc hq0 hw]
        _ = (z * w) * q0 := by group
        _ = (w * z) * q0 := by rw [(c.z_central w hw).symm]
        _ = w * (z * q0) := by group
    have hfψ : f * (x * p * x⁻¹) = (x * p * x⁻¹) * f := c.f_cent _ hxpT
    have hfq : f * q = q * f := (hqc hq hfT).symm
    have hfZ : f * (z * q0) = (z * q0) * f := (hZ1 f hfT).symm
    have hqψ : q * (x * p * x⁻¹) = (x * p * x⁻¹) * q := (c.PQ_comm _ hxpT q hq).symm
    have hxq : x * q * x⁻¹ = q := by
      calc x * q * x⁻¹ = q * x * x⁻¹ := by rw [hqc hq c.x_mem |>.symm]
        _ = q := by group
    have hxf' : x * f * x⁻¹ = (z * q0) * f := hxf
    rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    ·
      have hfi : f ^ i = 1 := by rw [hk, ← two_mul, pow_mul, c.f2, one_pow]
      rw [hfi] at h
      have e : (p * q * 1 * x) ^ 2 = (p * (x * p * x⁻¹)) * (q * q) := by
        calc (p * q * 1 * x) ^ 2 = (p * q * 1 * x) * (p * q * 1 * x) := sq _
          _ = (p * q) * (x * (p * q) * x⁻¹) * (x * x) := by group
          _ = (p * q) * ((x * p * x⁻¹) * (x * q * x⁻¹)) * (x * x) := by group
          _ = (p * q) * ((x * p * x⁻¹) * q) * (x * x) := by rw [hxq]
          _ = p * (q * (x * p * x⁻¹)) * q * (x * x) := by group
          _ = p * ((x * p * x⁻¹) * q) * q * (x * x) := by rw [hqψ]
          _ = (p * (x * p * x⁻¹)) * (q * q) * (x * x) := by group
          _ = (p * (x * p * x⁻¹)) * (q * q) := by rw [hx2, mul_one]
      rw [e, hq2 q hq, mul_one] at h
      exact c.PQ_inf u (by rw [← h]; exact P.mul_mem hp hxpT) c.u_mem |> c.u_ne
    ·
      have hfi : f ^ i = f := by rw [hk, pow_succ, pow_mul, c.f2, one_pow, one_mul]
      rw [hfi] at h
      have e : (p * q * f * x) ^ 2 = (z * q0) * (p * (x * p * x⁻¹)) := by
        have hZp : (z * q0) * (p * (x * p * x⁻¹)) = (p * (x * p * x⁻¹)) * (z * q0) :=
          hZ1 _ (T.mul_mem (c.P_le hp) (c.P_le hxpT))
        calc (p * q * f * x) ^ 2 = (p * q * f * x) * (p * q * f * x) := sq _
          _ = (p * q * f) * (x * (p * q * f) * x⁻¹) * (x * x) := by group
          _ = (p * q * f) * ((x * p * x⁻¹) * (x * q * x⁻¹) * (x * f * x⁻¹)) * (x * x) := by group
          _ = (p * q * f) * ((x * p * x⁻¹) * q * ((z * q0) * f)) * (x * x) := by rw [hxq, hxf']
          _ = p * q * (f * (x * p * x⁻¹)) * q * ((z * q0) * f) := by rw [hx2, mul_one]; group
          _ = p * q * ((x * p * x⁻¹) * f) * q * ((z * q0) * f) := by rw [hfψ]
          _ = p * q * (x * p * x⁻¹) * (f * q) * ((z * q0) * f) := by group
          _ = p * q * (x * p * x⁻¹) * (q * f) * ((z * q0) * f) := by rw [hfq]
          _ = p * q * (x * p * x⁻¹) * q * (f * (z * q0)) * f := by group
          _ = p * q * (x * p * x⁻¹) * q * ((z * q0) * f) * f := by rw [hfZ]
          _ = p * q * (x * p * x⁻¹) * q * (z * q0) * (f * f) := by group
          _ = p * q * (x * p * x⁻¹) * q * (z * q0) := by rw [hff, mul_one]
          _ = p * (q * (x * p * x⁻¹)) * q * (z * q0) := by group
          _ = p * ((x * p * x⁻¹) * q) * q * (z * q0) := by rw [hqψ]
          _ = (p * (x * p * x⁻¹)) * (q * q) * (z * q0) := by group
          _ = (p * (x * p * x⁻¹)) * (z * q0) := by rw [hq2 q hq, mul_one]
          _ = (z * q0) * (p * (x * p * x⁻¹)) := hZp.symm
      rw [e] at h
      have hPQ : (p * (x * p * x⁻¹)) * z = 1 := by
        have h1 : (p * (x * p * x⁻¹)) * z = u * q0⁻¹ := by
          have hZp : (z * q0) * (p * (x * p * x⁻¹)) = (p * (x * p * x⁻¹)) * (z * q0) :=
            hZ1 _ (T.mul_mem (c.P_le hp) (c.P_le hxpT))
          have h2 : (p * (x * p * x⁻¹)) * (z * q0) = u := by rw [← hZp]; exact h
          calc (p * (x * p * x⁻¹)) * z = (p * (x * p * x⁻¹)) * (z * q0) * q0⁻¹ := by group
            _ = u * q0⁻¹ := by rw [h2]
        apply c.PQ_inf
        · exact P.mul_mem (P.mul_mem hp hxpT) c.z_mem
        · rw [h1]; exact Q.mul_mem c.u_mem (Q.inv_mem hq0)
      apply hψ
      calc p * (x * p * x⁻¹) = (p * (x * p * x⁻¹)) * z * z⁻¹ := by group
        _ = z⁻¹ := by rw [hPQ, one_mul]
        _ = z := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact c.z_sq

theorem Cfg89T.exists_w4 (c : Cfg89T G T P Q u z x f r s) : ∃ w ∈ T, w ^ 4 = z := by
  refine ⟨s * x, T.mul_mem (c.P_le c.s_mem) c.x_mem, ?_⟩
  have hx2 : x * x = 1 := by rw [← sq]; exact c.x2
  have hss : s * s = 1 := by rw [← sq]; exact c.s2
  have hsq : (s * x) ^ 2 = s * (x * s * x⁻¹) * (x * x) := by rw [sq]; group
  have hr4 := c.r4
  have h4 : (s * x) ^ 4 = ((s * x) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, hsq, hx2, mul_one]
  rcases c.x_s with h | h <;> rw [h]
  · have e : s * (r * s) = (s * r * s⁻¹) * (s * s) := by group
    rw [e, c.srs, hss, mul_one, c.r_inv, c.z_eq]
    calc (r ^ 3) ^ 2 = r ^ 4 * r ^ 2 := by group
      _ = r ^ 2 := by rw [hr4, one_mul]
  · have e : s * (r ^ 3 * s) = (s * r * s⁻¹) ^ 3 * (s * s) := by
      rw [conj_pow]; group
    rw [e, c.srs, hss, mul_one, c.r_inv, c.z_eq]
    calc ((r ^ 3) ^ 3) ^ 2 = r ^ 16 * r ^ 2 := by group
      _ = r ^ 2 := by
        have : r ^ 16 = (r ^ 4) ^ 4 := by group
        rw [this, hr4, one_pow, one_mul]

theorem Cfg89T.aua_Q1 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) : a * u * a⁻¹ = u * z := by
  rcases c.u_a_cases sc with h | h
  · exfalso
    obtain ⟨w, hwT, hw⟩ := c.exists_w4
    have hu : (a⁻¹ * w ^ 2 * a) ^ 2 = u := by
      have e1 : (a⁻¹ * w ^ 2 * a) ^ 2 = a⁻¹ * w ^ 4 * a := by
        have := conj_pow (a := a⁻¹) (b := w ^ 2) (i := 2)
        simp only [inv_inv] at this
        rw [this, ← pow_mul]
      rw [e1, hw]
      calc a⁻¹ * z * a = a⁻¹ * (a * u * a⁻¹) * a := by rw [h]
        _ = u := by group
    exact c.u_not_sq hQ' (sc.conj_inv_mem (T.pow_mem hwT 2)) hu
  · exact h

theorem Cfg89T.aza_Q1 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) : a * z * a⁻¹ = z := by
  have h1 := Cfg89S.conj_conj sc (h := u) c.u_central
  rw [c.aua_Q1 sc hQ'] at h1
  have e : a * z * a⁻¹ = (a * u * a⁻¹)⁻¹ * (a * (u * z) * a⁻¹) := by group
  rw [e, c.aua_Q1 sc hQ', h1]
  have hu2 : u * u = 1 := by rw [← sq]; exact c.u2
  have hz2 : z * z = 1 := by rw [← sq]; exact c.z_sq
  calc (u * z)⁻¹ * u = z⁻¹ * u⁻¹ * u := by rw [mul_inv_rev]
    _ = z⁻¹ := by group
    _ = z := inv_eq_of_mul_eq_one_right hz2

omit [Finite G] in
theorem isElemAbelian_conjSub (g : G) {E : Subgroup G} (hE : Open.IsElemAbelian 2 E) :
    Open.IsElemAbelian 2 (conjSub g E) := by
  rw [isElemAbelian_iff] at hE ⊢
  constructor
  · intro y hy y' hy'
    obtain ⟨e, he, rfl⟩ := mem_conjSub.mp hy
    obtain ⟨e', he', rfl⟩ := mem_conjSub.mp hy'
    have := hE.1 e he e' he'
    calc g * e * g⁻¹ * (g * e' * g⁻¹) = g * (e * e') * g⁻¹ := by group
      _ = g * (e' * e) * g⁻¹ := by rw [this]
      _ = g * e' * g⁻¹ * (g * e * g⁻¹) := by group
  · intro y hy
    obtain ⟨e, he, rfl⟩ := mem_conjSub.mp hy
    rw [conj_pow, hE.2 e he]; group

omit [Finite G] in
theorem conjSub_injective (g : G) {E E' : Subgroup G} (h : conjSub g E = conjSub g E') : E = E' :=
  Subgroup.map_injective (MulAut.conj g).injective h

theorem Cfg89T.conj_AB (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {g : G} (hg : g ∈ S) :
    (conjSub g (EA c) = EA c ∧ conjSub g (EB c) = EB c) ∨
      (conjSub g (EA c) = EB c ∧ conjSub g (EB c) = EA c) := by
  have hT : ∀ E : Subgroup G, E ≤ T → conjSub g E ≤ T := by
    intro E hE y hy
    obtain ⟨e, he, rfl⟩ := mem_conjSub.mp hy
    exact sc.T_norm g hg e (hE he)
  have hA : conjSub g (EA c) = EA c ∨ conjSub g (EA c) = EB c :=
    E16_unique c hQ' (hT _ (EA_le_T c)) (isElemAbelian_conjSub g (isElemAbelian_EA c))
      (by rw [card_conjSub, card_EA])
  have hB : conjSub g (EB c) = EA c ∨ conjSub g (EB c) = EB c :=
    E16_unique c hQ' (hT _ (EB_le_T c)) (isElemAbelian_conjSub g (isElemAbelian_EB c))
      (by rw [card_conjSub, card_EB])
  have hne : conjSub g (EA c) ≠ conjSub g (EB c) := fun h => EA_ne_EB c (conjSub_injective g h)
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.trans hB.symm) hne
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr ⟨hA, hB⟩
  · exact absurd (hA.trans hB.symm) hne

theorem Cfg89T.conj_M0 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {g m : G} (hg : g ∈ S) (hm : m ∈ M0 c) : g * m * g⁻¹ ∈ M0 c := by
  have h : conjSub g (M0 c) = M0 c := by
    rw [M0_eq_EA_sup_EB c hQ']
    show (EA c ⊔ EB c).map (MulAut.conj g).toMonoidHom = EA c ⊔ EB c
    rw [Subgroup.map_sup]
    show conjSub g (EA c) ⊔ conjSub g (EB c) = EA c ⊔ EB c
    rcases c.conj_AB sc hQ' hg with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · rw [hA, hB]
    · rw [hA, hB, sup_comm]
  rw [← h]
  exact conj_mem_conjSub hm

theorem Cfg89T.exists_g (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) :
    ∃ g ∈ S, (∀ h ∈ EA c, g * h * g⁻¹ ∈ EA c) ∧ g * u * g⁻¹ = u * z ∧ g * z * g⁻¹ = z := by
  have hx2 : x * x = 1 := by rw [← sq]; exact c.x2
  have hzT : z ∈ T := c.P_le c.z_mem
  have hxu : x * u = u * x := c.u_central x c.x_mem
  have hxz : x * z = z * x := c.z_central x c.x_mem
  rcases c.conj_AB sc hQ' sc.a_mem with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · refine ⟨a, sc.a_mem, fun h hh => ?_, c.aua_Q1 sc hQ', c.aza_Q1 sc hQ'⟩
    have : a * h * a⁻¹ ∈ conjSub a (EA c) := conj_mem_conjSub hh
    rwa [hA] at this
  · refine ⟨x * a, S.mul_mem (sc.T_le c.x_mem) sc.a_mem, fun h hh => ?_, ?_, ?_⟩
    · have h1 : a * h * a⁻¹ ∈ conjSub a (EA c) := conj_mem_conjSub hh
      rw [hA] at h1
      obtain ⟨h', hh', he⟩ := (x_swap_EA c hQ' _).mp h1
      have : x * a * h * (x * a)⁻¹ = h' := by
        calc x * a * h * (x * a)⁻¹ = x * (a * h * a⁻¹) * x⁻¹ := by group
          _ = x * (x * h' * x⁻¹) * x⁻¹ := by rw [he]
          _ = (x * x) * h' * (x * x)⁻¹ := by group
          _ = h' := by rw [hx2]; group
      rw [this]; exact hh'
    · have e : x * a * u * (x * a)⁻¹ = x * (a * u * a⁻¹) * x⁻¹ := by group
      rw [e, c.aua_Q1 sc hQ']
      calc x * (u * z) * x⁻¹ = (x * u) * z * x⁻¹ := by group
        _ = (u * x) * z * x⁻¹ := by rw [hxu]
        _ = u * (x * z) * x⁻¹ := by group
        _ = u * (z * x) * x⁻¹ := by rw [hxz]
        _ = u * z := by group
    · have e : x * a * z * (x * a)⁻¹ = x * (a * z * a⁻¹) * x⁻¹ := by group
      rw [e, c.aza_Q1 sc hQ']
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [hxz]
        _ = z := by group

theorem Cfg89T.f_comm_M0 (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {m : G}
    (hm : m ∈ M0 c) : f * m = m * f := by
  obtain ⟨p, hp, q, hq, i, rfl⟩ := hm
  have h1 : f * p = p * f := c.f_cent p hp
  have h2 : f * q = q * f := (c.qc_of_Q' hQ' hq c.f_mem).symm
  have h3 : f * f ^ i = f ^ i * f := (Commute.self_pow f i).eq.symm.symm
  calc f * (p * q * f ^ i) = (f * p) * q * f ^ i := by group
    _ = (p * f) * q * f ^ i := by rw [h1]
    _ = p * (f * q) * f ^ i := by group
    _ = p * (q * f) * f ^ i := by rw [h2]
    _ = p * q * (f * f ^ i) := by group
    _ = p * q * (f ^ i * f) := by rw [h3]
    _ = p * q * f ^ i * f := by group

theorem Cfg89T.u_comm_M0 (c : Cfg89T G T P Q u z x f r s) {m : G} (hm : m ∈ M0 c) :
    u * m = m * u := (c.u_central m (M0_le_T c hm)).symm

theorem Cfg89T.z_comm_M0 (c : Cfg89T G T P Q u z x f r s) {m : G} (hm : m ∈ M0 c) :
    z * m = m * z := (c.z_central m (M0_le_T c hm)).symm

theorem Cfg89T.V_comm_M0 (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) (i j k : ℕ)
    {m : G} (hm : m ∈ M0 c) : (u ^ i * f ^ j * z ^ k) * m = m * (u ^ i * f ^ j * z ^ k) :=
  (((Commute.pow_left (show Commute u m from c.u_comm_M0 hm) i).mul_left
    (Commute.pow_left (show Commute f m from c.f_comm_M0 hQ' hm) j)).mul_left
    (Commute.pow_left (show Commute z m from c.z_comm_M0 hm) k)).eq

theorem Cfg89T.g_action (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {g : G} (hg : g ∈ S) (hgA : ∀ h ∈ EA c, g * h * g⁻¹ ∈ EA c)
    (hgu : g * u * g⁻¹ = u * z) (hgz : g * z * g⁻¹ = z) :
    (∃ i j : ℕ, g * f * g⁻¹ = f * u ^ i * z ^ j) ∧
      (∃ i j k : ℕ, g * s * g⁻¹ = s * u ^ i * f ^ j * z ^ k) := by
  have hgz' : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hgz]
      _ = z := by group
  have hzz : z * z = 1 := by rw [← sq]; exact c.z_sq
  have huu : u * u = 1 := by rw [← sq]; exact c.u2
  have hzT : z ∈ T := c.P_le c.z_mem
  have huz : u * z = z * u := (c.u_central z hzT).symm
  have hgu' : g⁻¹ * u * g = u * z := by
    have h1 : u = (g⁻¹ * u * g) * z := by
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * (u * z) * g := by rw [hgu]
        _ = (g⁻¹ * u * g) * (g⁻¹ * z * g) := by group
        _ = (g⁻¹ * u * g) * z := by rw [hgz']
    calc g⁻¹ * u * g = (g⁻¹ * u * g) * (z * z) := by rw [hzz, mul_one]
      _ = ((g⁻¹ * u * g) * z) * z := by group
      _ = u * z := by rw [← h1]
  have hgM : ∀ m ∈ M0 c, g * m * g⁻¹ ∈ M0 c := fun m hm => c.conj_M0 sc hQ' hg hm
  have hfA : f ∈ EA c := (mem_EA c).mpr ⟨0, 1, 0, 0, by simp⟩
  have hsA : s ∈ EA c := (mem_EA c).mpr ⟨0, 0, 0, 1, by simp⟩
  have hrM : r ∈ M0 c := P_le_M0 c c.r_mem
  have hconjpow : ∀ (w : G) (n : ℕ), (g⁻¹ * w * g) ^ n = g⁻¹ * w ^ n * g := fun w n => by
    have := conj_pow (a := g⁻¹) (b := w) (i := n)
    simpa using this
  have huz2 : (u * z) ^ 2 = 1 := by
    rw [sq]
    calc u * z * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [← huz]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [huu, hzz, mul_one]
  refine ⟨?_, ?_⟩
  · obtain ⟨i, j, k, l, hw⟩ := (mem_EA c).mp (hgA f hfA)
    have hwM : ∀ m ∈ M0 c, (g * f * g⁻¹) * m = m * (g * f * g⁻¹) := by
      intro m hm
      have hm' : g⁻¹ * m * g ∈ M0 c := by
        have := c.conj_M0 sc hQ' (S.inv_mem hg) hm
        simpa using this
      have h1 := c.f_comm_M0 hQ' hm'
      calc (g * f * g⁻¹) * m = g * (f * (g⁻¹ * m * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * m * g) * f) * g⁻¹ := by rw [h1]
        _ = m * (g * f * g⁻¹) := by group
    have hl : l % 2 = 0 := by
      by_contra hl
      have hl1 : l % 2 = 1 := by omega
      have h2 := hwM r hrM
      rw [hw, pow_eq_pow_mod l c.s2, hl1, pow_one] at h2
      have h3 := c.V_comm_M0 hQ' i j k hrM
      apply c.s_comm_r_false
      have : (u ^ i * f ^ j * z ^ k) * (s * r) = (u ^ i * f ^ j * z ^ k) * (r * s) := by
        calc (u ^ i * f ^ j * z ^ k) * (s * r) = u ^ i * f ^ j * z ^ k * s * r := by group
          _ = r * (u ^ i * f ^ j * z ^ k * s) := h2
          _ = (r * (u ^ i * f ^ j * z ^ k)) * s := by group
          _ = ((u ^ i * f ^ j * z ^ k) * r) * s := by rw [h3]
          _ = (u ^ i * f ^ j * z ^ k) * (r * s) := by group
      exact mul_left_cancel this
    have hs0 : s ^ l = 1 := by rw [pow_eq_pow_mod l c.s2, hl, pow_zero]
    rw [hs0, mul_one] at hw
    have hj : j % 2 = 1 := by
      by_contra hj
      have hj0 : j % 2 = 0 := by omega
      have hf0 : f ^ j = 1 := by rw [pow_eq_pow_mod j c.f2, hj0, pow_zero]
      rw [hf0, mul_one] at hw
      have hfe : f = (u * z) ^ i * z ^ k := by
        calc f = g⁻¹ * (g * f * g⁻¹) * g := by group
          _ = g⁻¹ * (u ^ i * z ^ k) * g := by rw [hw]
          _ = (g⁻¹ * u ^ i * g) * (g⁻¹ * z ^ k * g) := by group
          _ = (g⁻¹ * u * g) ^ i * (g⁻¹ * z * g) ^ k := by rw [hconjpow, hconjpow]
          _ = (u * z) ^ i * z ^ k := by rw [hgu', hgz']
      rw [pow_eq_pow_mod i huz2, pow_eq_pow_mod k c.z_sq] at hfe
      have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hk2 : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      generalize i % 2 = I at hi2 hfe
      generalize k % 2 = K at hk2 hfe
      interval_cases I <;> interval_cases K
      · simp at hfe; exact c.f_ne_one hfe
      · exact c.f_not 1 Q.one_mem 1 (by simpa using hfe)
      · exact c.f_not u c.u_mem 1 (by simpa using hfe)
      · have : f = u := by
          simp only [pow_one] at hfe
          rw [hfe]
          calc u * z * z = u * (z * z) := by group
            _ = u := by rw [hzz, mul_one]
        exact c.u_ne_f this
    refine ⟨i, k, ?_⟩
    rw [hw, pow_eq_pow_mod j c.f2, hj, pow_one]
    have h4 : u ^ i * f = f * u ^ i :=
      (Commute.pow_left (show Commute u f from (c.u_central f c.f_mem).symm) i).eq
    calc u ^ i * f * z ^ k = (u ^ i * f) * z ^ k := rfl
      _ = f * u ^ i * z ^ k := by rw [h4]
  · obtain ⟨i, j, k, l, hw⟩ := (mem_EA c).mp (hgA s hsA)
    have hl : l % 2 = 1 := by
      by_contra hl
      have hl0 : l % 2 = 0 := by omega
      have hs0 : s ^ l = 1 := by rw [pow_eq_pow_mod l c.s2, hl0, pow_zero]
      rw [hs0, mul_one] at hw
      have hs' : s = g⁻¹ * (u ^ i * f ^ j * z ^ k) * g := by
        calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
          _ = g⁻¹ * (u ^ i * f ^ j * z ^ k) * g := by rw [hw]
      have hgr : g * r * g⁻¹ ∈ M0 c := hgM r hrM
      have h3 := c.V_comm_M0 hQ' i j k hgr
      apply c.s_comm_r_false
      have : s * r * s⁻¹ = r := by
        rw [hs']
        calc g⁻¹ * (u ^ i * f ^ j * z ^ k) * g * r * (g⁻¹ * (u ^ i * f ^ j * z ^ k) * g)⁻¹
            = g⁻¹ * ((u ^ i * f ^ j * z ^ k) * (g * r * g⁻¹) * (u ^ i * f ^ j * z ^ k)⁻¹) * g := by group
          _ = g⁻¹ * (g * r * g⁻¹) * g := by rw [h3]; group
          _ = r := by group
      calc s * r = (s * r * s⁻¹) * s := by group
        _ = r * s := by rw [this]
    have hs1 : s ^ l = s := by rw [pow_eq_pow_mod l c.s2, hl, pow_one]
    rw [hs1] at hw
    refine ⟨i, j, k, ?_⟩
    rw [hw]
    have hV := c.V_comm_M0 hQ' i j k (P_le_M0 c c.s_mem)
    calc u ^ i * f ^ j * z ^ k * s = s * (u ^ i * f ^ j * z ^ k) := by rw [← hV]
      _ = s * u ^ i * f ^ j * z ^ k := by group

omit [Finite G] in
theorem card_le_two_mul_of_relIndex {D C : Subgroup G} (hDC : D ≤ C) (h : D.relIndex C ≤ 2) :
    Nat.card ↥C ≤ 2 * Nat.card ↥D := by
  have h2 : Nat.card ↥(D.subgroupOf C) * (D.subgroupOf C).index = Nat.card ↥C := Subgroup.card_mul_index _
  have h3 : Nat.card ↥(D.subgroupOf C) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  rw [h3] at h2
  have h4 : (D.subgroupOf C).index = D.relIndex C := rfl
  rw [h4] at h2
  calc Nat.card ↥C = Nat.card ↥D * D.relIndex C := h2.symm
    _ ≤ Nat.card ↥D * 2 := Nat.mul_le_mul_left _ h
    _ = 2 * Nat.card ↥D := by ring

omit [Finite G] in
theorem isElemAbelian_zpowers {w : G} (hw : w ^ 2 = 1) : Open.IsElemAbelian 2 (zpowers w) := by
  rw [isElemAbelian_iff]
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  · rcases mem_zpowers_of_sq hw ha with rfl | rfl
    · simp
    · exact hw

theorem Cfg89T.closing (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {C : Subgroup G} (hCS : C ≤ S)
    (hCn : ∀ s' ∈ S, ∀ c' ∈ C, s' * c' * s'⁻¹ ∈ C) (hCel : Open.IsElemAbelian 2 C)
    (hCcard : Nat.card ↥C = 16) : False := by
  have hxS : x ∈ S := sc.T_le c.x_mem
  have huT : u ∈ T := c.Q_le c.u_mem
  set D : Subgroup G := C ⊓ T with hD
  have hDC : D ≤ C := inf_le_left
  have hDT : D ≤ T := inf_le_right
  have hD8 : 16 ≤ 2 * Nat.card ↥D := by
    have h1 : D.relIndex C ≤ 2 := by
      rw [hD, inf_comm, Subgroup.inf_relIndex_right]
      exact (Subgroup.relIndex_le_of_le_right hCS
        (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card T S) Nat.card_pos).ne').trans sc.relIndex_le
    have := card_le_two_mul_of_relIndex hDC h1
    omega
  have hel_u : Open.IsElemAbelian 2 (zpowers u) := isElemAbelian_zpowers c.u2
  have hcomm : ∀ d ∈ D, ∀ b ∈ zpowers u, d * b = b * d := by
    intro d hd b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_left (show Commute u d from (c.u_central d (hDT hd)).symm) m).eq).symm
  set E : Subgroup G := D ⊔ zpowers u with hE
  have hEle : E ≤ T := sup_le hDT ((Subgroup.zpowers_le).mpr huT)
  have hEel : Open.IsElemAbelian 2 E :=
    IsElemAbelian.sup (IsElemAbelian.mono hDC hCel) hel_u hcomm
  have hEle16 : Nat.card ↥E ≤ 16 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hEp : IsPGroup 2 ↥E := c.T_two.of_injective (Subgroup.inclusion hEle) (Subgroup.inclusion_injective hEle)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hEp
    have hEA : CFSG.IsElementaryAbelian 2 ↥E := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hEel
    have h1 := le_pRank_of_elem (le_top : E ≤ ⊤) hEA (k := m) (by rw [hm])
    have h2 := Bg.pRank_subgroup_le one_lt_two (⊤ : Subgroup G)
    have : m ≤ 4 := by rw [← c.rank4]; exact h1.trans h2
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
      _ = 16 := by norm_num
  have hEge16 : 16 ≤ Nat.card ↥E := by
    by_cases hu : u ∈ C
    · have hCT : C ≤ T := by
        intro c' hc'
        apply sc.T_cent c' (hCS hc')
        exact (((isElemAbelian_iff.mp hCel).1 c' hc' u hu))
      have hDC' : D = C := le_antisymm hDC (le_inf le_rfl hCT)
      have : Nat.card ↥C ≤ Nat.card ↥E := Subgroup.card_le_of_le (by rw [← hDC']; exact le_sup_left)
      omega
    · have hinf : D ⊓ zpowers u = ⊥ := by
        rw [eq_bot_iff]
        intro g ⟨hgD, hgu⟩
        rw [Subgroup.mem_bot]
        rcases mem_zpowers_of_sq c.u2 hgu with h | h
        · exact h
        · exact absurd (h ▸ hDC hgD) hu
      have := card_sup_of_commute hcomm hinf
      rw [← hE, card_zpowers_two c.u2 c.u_ne] at this
      omega
  have hEcard : Nat.card ↥E = 16 := le_antisymm hEle16 hEge16
  have hEx : ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro e he
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sup_of_commute hcomm he
    have hxd : x * d * x⁻¹ ∈ D := Subgroup.mem_inf.mpr ⟨hCn x hxS d (hDC hd), T.mul_mem (T.mul_mem c.x_mem (hDT hd)) (T.inv_mem c.x_mem)⟩
    have hxb : x * b * x⁻¹ = b := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have : x * u ^ m * x⁻¹ = u ^ m := by
        have := (Commute.zpow_right (show Commute x u from c.u_central x c.x_mem) m).eq
        calc x * u ^ m * x⁻¹ = u ^ m * x * x⁻¹ := by rw [this]
          _ = u ^ m := by group
      exact this
    have : x * (d * b) * x⁻¹ = (x * d * x⁻¹) * (x * b * x⁻¹) := by group
    rw [this, hxb]
    exact Subgroup.mul_mem_sup hxd hb
  rcases E16_unique c hQ' hEle hEel hEcard with hEA | hEB
  ·
    have hle : EB c ≤ EA c := by
      intro g hg
      obtain ⟨h', hh', rfl⟩ := (x_swap_EA c hQ' g).mp hg
      rw [← hEA] at hh' ⊢
      exact hEx h' hh'
    exact EA_ne_EB c (Subgroup.eq_of_le_of_card_ge hle (by rw [card_EA, card_EB]) |>.symm)
  ·
    have hle : EA c ≤ EB c := by
      intro a0 ha0
      have hb : x * a0 * x⁻¹ ∈ EB c := (x_swap_EA c hQ' _).mpr ⟨a0, ha0, rfl⟩
      rw [← hEB] at hb ⊢
      have h2 := hEx _ hb
      have e : x * (x * a0 * x⁻¹) * x⁻¹ = a0 := by
        have hx2 : x * x = 1 := by rw [← sq]; exact c.x2
        calc x * (x * a0 * x⁻¹) * x⁻¹ = (x * x) * a0 * (x * x)⁻¹ := by group
          _ = a0 := by rw [hx2]; group
      rwa [e] at h2
    exact EA_ne_EB c (Subgroup.eq_of_le_of_card_ge hle (by rw [card_EA, card_EB]))

theorem Cfg89T.hnc (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) : ∀ w : G, w * u * w⁻¹ ≠ z := by
  intro w hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzS : ∀ g ∈ S, g * z * g⁻¹ = z := by
    intro g hg
    rcases sc.S_split g hg with h | h
    · have := c.z_central g h
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [this]
        _ = z := by group
    · have ht : a⁻¹ * g ∈ T := h
      have e : g * z * g⁻¹ = a * ((a⁻¹ * g) * z * (a⁻¹ * g)⁻¹) * a⁻¹ := by group
      have hzt := c.z_central _ ht
      rw [e, show (a⁻¹ * g) * z * (a⁻¹ * g)⁻¹ = z from by
        calc (a⁻¹ * g) * z * (a⁻¹ * g)⁻¹ = z * (a⁻¹ * g) * (a⁻¹ * g)⁻¹ := by rw [hzt]
          _ = z := by group]
      exact c.aza_Q1 sc hQ'
  have hle : conjSub w⁻¹ S ≤ centralizer ({u} : Set G) := by
    intro g' hg'
    obtain ⟨s', hs', rfl⟩ := mem_conjSub.mp hg'
    rw [mem_centralizer_singleton_iff]
    have hsz : s' * z = z * s' := by
      have := hzS s' hs'
      calc s' * z = (s' * z * s'⁻¹) * s' := by group
        _ = z * s' := by rw [this]
    calc w⁻¹ * s' * w⁻¹⁻¹ * u = w⁻¹ * s' * (w * u * w⁻¹) * w := by group
      _ = w⁻¹ * s' * z * w := by rw [hw]
      _ = w⁻¹ * (s' * z) * w := by group
      _ = w⁻¹ * (z * s') * w := by rw [hsz]
      _ = (w⁻¹ * z * w) * (w⁻¹ * s' * w⁻¹⁻¹) := by group
      _ = u * (w⁻¹ * s' * w⁻¹⁻¹) := by
        rw [show w⁻¹ * z * w = u from by
          calc w⁻¹ * z * w = w⁻¹ * (w * u * w⁻¹) * w := by rw [hw]
            _ = u := by group]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp sc.sylowS.isPGroup
  have hle2 := card_le_of_isSylowOf c.sylowT hle (n := n) (by rw [card_conjSub]; exact hn)
  rw [card_conjSub] at hle2
  have hlt : Nat.card ↥T < Nat.card ↥S := by
    by_contra h
    have := Subgroup.eq_of_le_of_card_ge sc.T_le (not_lt.mp h)
    exact sc.a_nmem (this ▸ sc.a_mem)
  omega

theorem Cfg89T.card_T_le (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) :
    Nat.card ↥T ≤ 64 := by
  classical
  let F : Fin 4 × Fin 2 × Fin 2 × Fin 2 × Fin 2 → G := fun w =>
    r ^ (w.1 : ℕ) * s ^ (w.2.1 : ℕ) * u ^ (w.2.2.1 : ℕ) * f ^ (w.2.2.2.1 : ℕ) * x ^ (w.2.2.2.2 : ℕ)
  have hsub : (T : Set G) ⊆ Set.range F := by
    intro t ht
    obtain ⟨p, hp, q, hq, i, j, rfl⟩ := c.T_gen t ht
    obtain ⟨a', b', rfl⟩ := c.P_gen p hp
    have ha : a' % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hb : b' % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hi : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases hQ' q hq with rfl | rfl
    · refine ⟨(⟨a' % 4, ha⟩, ⟨b' % 2, hb⟩, 0, ⟨i % 2, hi⟩, ⟨j % 2, hj⟩), ?_⟩
      simp only [F, Fin.val_zero, pow_zero, mul_one]
      rw [← pow_eq_pow_mod a' c.r4, ← pow_eq_pow_mod b' c.s2, ← pow_eq_pow_mod i c.f2,
        ← pow_eq_pow_mod j c.x2]
    · refine ⟨(⟨a' % 4, ha⟩, ⟨b' % 2, hb⟩, 1, ⟨i % 2, hi⟩, ⟨j % 2, hj⟩), ?_⟩
      simp only [F, Fin.val_one, pow_one]
      rw [← pow_eq_pow_mod a' c.r4, ← pow_eq_pow_mod b' c.s2, ← pow_eq_pow_mod i c.f2,
        ← pow_eq_pow_mod j c.x2]
  have h1 : (Set.range F).ncard ≤ Nat.card (Fin 4 × Fin 2 × Fin 2 × Fin 2 × Fin 2) := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.toFinite _)).trans_eq (Set.ncard_univ _)
  have h2 : Nat.card ↥T = (T : Set G).ncard := Nat.card_coe_set_eq _
  rw [h2]
  calc _ ≤ (Set.range F).ncard := Set.ncard_le_ncard hsub (Set.finite_range F)
    _ ≤ _ := h1
    _ = 64 := by simp

theorem Cfg89T.false_of_small (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) (n1 n2 : G)
    (n1_u : n1 * u * n1⁻¹ = u) (n1_f : n1 * f * n1⁻¹ = f)
    (n1_z : n1 * z * n1⁻¹ = s) (n1_s : n1 * s * n1⁻¹ = z)
    (n2_u : n2 * u * n2⁻¹ = u) (n2_f : n2 * f * n2⁻¹ = f)
    (n2_z : n2 * z * n2⁻¹ = z) (n2_s : n2 * s * n2⁻¹ = z * s) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzT : z ∈ T := c.P_le c.z_mem
  have hsT : s ∈ T := c.P_le c.s_mem
  obtain ⟨g, hg, hgA, hgu, hgz⟩ := c.exists_g sc hQ'
  obtain ⟨hgf, hgs⟩ := c.g_action sc hQ' hg hgA hgu hgz
  have hdvd : 2 ^ 7 ∣ Nat.card ↥(Subgroup.normalizer ((EA c : Subgroup G) : Set G)) :=
    normalizer_dvd (EA c) u f z s n1 n2 g (fun y => mem_EA c) (card_EA c) c.u2 c.f2 c.z_sq c.s2
      (c.u_central f c.f_mem).symm (c.u_central z hzT).symm (c.u_central s hsT).symm
      (c.f_cent z c.z_mem) (c.f_cent s c.s_mem) c.z_comm_s n1_u n1_f n1_z n1_s n2_u n2_f n2_z n2_s
      hgu hgz hgf hgs (c.hnc sc hQ')
  set N := Subgroup.normalizer ((EA c : Subgroup G) : Set G) with hN
  have hAN : EA c ≤ N := Subgroup.le_normalizer
  have hA2 : IsPGroup 2 ↥(EA c) := IsPGroup.of_card (n := 4) (by rw [card_EA]; norm_num)
  obtain ⟨R, hRN, hAR⟩ := CFSG.ComponentClassification.FooteLit.exists_isSylowOf_ge_of_le hAN hA2
  have hRcard := hRN.card_eq
  have h7 : 7 ≤ (Nat.card ↥N).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have hR128 : 128 ≤ Nat.card ↥R := by
    rw [hRcard]
    calc 128 = 2 ^ 7 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h7
  have hS128 : Nat.card ↥S ≤ 128 := by
    have := card_le_two_mul_of_relIndex sc.T_le sc.relIndex_le
    have := c.card_T_le hQ'
    omega
  have hRS : Nat.card ↥R ≤ Nat.card ↥S :=
    card_le_of_isSylowOf sc.sylowS (le_top : R ≤ ⊤) hRcard
  obtain ⟨k, -, hk⟩ := CFSG.ComponentClassification.FooteLit.exists_conj_le_of_isSylowOf sc.sylowS
    (le_top : R ≤ ⊤) hRN.isPGroup
  have hconjR : conjSub k⁻¹ R ≤ S := by
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := mem_conjSub.mp hy
    simpa using hk ρ hρ
  have hSconj : conjSub k⁻¹ R = S :=
    Subgroup.eq_of_le_of_card_ge hconjR (by rw [card_conjSub]; omega)
  have hCS : conjSub k⁻¹ (EA c) ≤ S := by
    rw [← hSconj]
    intro y hy
    obtain ⟨a0, ha0, rfl⟩ := mem_conjSub.mp hy
    exact conj_mem_conjSub (hAR ha0)
  have hCn : ∀ s' ∈ S, ∀ c' ∈ conjSub k⁻¹ (EA c), s' * c' * s'⁻¹ ∈ conjSub k⁻¹ (EA c) := by
    intro s' hs' c' hc'
    rw [← hSconj] at hs'
    obtain ⟨ρ, hρ, rfl⟩ := mem_conjSub.mp hs'
    obtain ⟨a0, ha0, rfl⟩ := mem_conjSub.mp hc'
    have hρN : ρ ∈ N := hRN.le hρ
    have h1 : ρ * a0 * ρ⁻¹ ∈ EA c := (Subgroup.mem_normalizer_iff.mp hρN a0).mp ha0
    have e : k⁻¹ * ρ * k⁻¹⁻¹ * (k⁻¹ * a0 * k⁻¹⁻¹) * (k⁻¹ * ρ * k⁻¹⁻¹)⁻¹ = k⁻¹ * (ρ * a0 * ρ⁻¹) * k⁻¹⁻¹ := by
      group
    show k⁻¹ * ρ * k⁻¹⁻¹ * (k⁻¹ * a0 * k⁻¹⁻¹) * (k⁻¹ * ρ * k⁻¹⁻¹)⁻¹ ∈ conjSub k⁻¹ (EA c)
    rw [e]
    exact conj_mem_conjSub h1
  exact c.closing sc hQ' hCS hCn (isElemAbelian_conjSub _ (isElemAbelian_EA c))
    (by rw [card_conjSub, card_EA])

theorem Cfg89T.false_of_cfg89 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hsmall : (∀ q ∈ Q, q = 1 ∨ q = u) → ∃ n1 n2 : G,
      n1 * u * n1⁻¹ = u ∧ n1 * f * n1⁻¹ = f ∧ n1 * z * n1⁻¹ = s ∧ n1 * s * n1⁻¹ = z ∧
      n2 * u * n2⁻¹ = u ∧ n2 * f * n2⁻¹ = f ∧ n2 * z * n2⁻¹ = z ∧ n2 * s * n2⁻¹ = z * s) : False := by
  by_cases hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u
  · exact c.false_of_hQ sc hQ
  · have hQ' : ∀ q ∈ Q, q = 1 ∨ q = u := by
      intro q hq
      by_cases h1 : q = 1
      · exact Or.inl h1
      · by_cases h2 : q = u
        · exact Or.inr h2
        · exact absurd ⟨q, hq, h1, h2⟩ hQ
    obtain ⟨n1, n2, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsmall hQ'
    exact c.false_of_small sc hQ' n1 n2 h1 h2 h3 h4 h5 h6 h7 h8

end E

end CFSG.GH74.GLS.C3.Layer1.P89
