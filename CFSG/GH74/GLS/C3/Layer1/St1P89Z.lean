module

public import CFSG.GH74.GLS.C3.Layer1.St1P89Tools
public import CFSG.GH74.GLS.C3.Layer1.St1Conj
public import CFSG.GH74.GLS.C3.Layer1.St1P89Transfer

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU1

section Zcase

variable {G : Type} [Group G] [Finite G] {T P Q : Subgroup G} {u z x f r s : G}

theorem Cfg89T.f_inv (c : Cfg89T G T P Q u z x f r s) : f⁻¹ = f := by
  have := c.f2
  rw [sq] at this
  exact inv_eq_of_mul_eq_one_right this

theorem Cfg89T.f_pow_comm_P (c : Cfg89T G T P Q u z x f r s) (i : ℕ) {p : G} (hp : p ∈ P) :
    f ^ i * p = p * f ^ i := by
  have h : Commute f p := c.f_cent p hp
  exact (h.pow_left i).eq

theorem Cfg89T.f_pow_mem_T (c : Cfg89T G T P Q u z x f r s) (i : ℕ) : f ^ i ∈ T := T.pow_mem c.f_mem i

theorem Cfg89T.f_pow_conj_Q (c : Cfg89T G T P Q u z x f r s) (i : ℕ) {q : G} (hq : q ∈ Q) :
    f ^ i * q * (f ^ i)⁻¹ ∈ Q := c.Q_norm (f ^ i) (c.f_pow_mem_T i) q hq

@[expose] def M0 (c : Cfg89T G T P Q u z x f r s) : Subgroup G where
  carrier := {t | ∃ p ∈ P, ∃ q ∈ Q, ∃ i : ℕ, t = p * q * f ^ i}
  one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨p, hp, q, hq, i, rfl⟩ ⟨p', hp', q', hq', j, rfl⟩
    have hfp : f ^ i * p' = p' * f ^ i := c.f_pow_comm_P i hp'
    have hqp : q * p' = p' * q := (c.PQ_comm p' hp' q hq).symm
    have hq'' : f ^ i * q' * (f ^ i)⁻¹ ∈ Q := c.f_pow_conj_Q i hq'
    refine ⟨p * p', P.mul_mem hp hp', q * (f ^ i * q' * (f ^ i)⁻¹), Q.mul_mem hq hq'', i + j, ?_⟩
    calc p * q * f ^ i * (p' * q' * f ^ j) = p * q * (f ^ i * p') * q' * f ^ j := by group
      _ = p * q * (p' * f ^ i) * q' * f ^ j := by rw [hfp]
      _ = p * (q * p') * f ^ i * q' * f ^ j := by group
      _ = p * (p' * q) * f ^ i * q' * f ^ j := by rw [hqp]
      _ = p * p' * (q * (f ^ i * q' * (f ^ i)⁻¹)) * f ^ (i + j) := by rw [pow_add]; group
  inv_mem' := by
    rintro _ ⟨p, hp, q, hq, i, rfl⟩
    have hfp : f ^ i * p⁻¹ = p⁻¹ * f ^ i := c.f_pow_comm_P i (P.inv_mem hp)
    have hq'' : f ^ i * q⁻¹ * (f ^ i)⁻¹ ∈ Q := c.f_pow_conj_Q i (Q.inv_mem hq)
    have hqp : (f ^ i * q⁻¹ * (f ^ i)⁻¹) * p⁻¹ = p⁻¹ * (f ^ i * q⁻¹ * (f ^ i)⁻¹) :=
      (c.PQ_comm p⁻¹ (P.inv_mem hp) _ hq'').symm
    have hfi : (f ^ i)⁻¹ = f ^ i := by rw [← inv_pow, c.f_inv]
    refine ⟨p⁻¹, P.inv_mem hp, f ^ i * q⁻¹ * (f ^ i)⁻¹, hq'', i, ?_⟩
    calc (p * q * f ^ i)⁻¹ = (f ^ i)⁻¹ * q⁻¹ * p⁻¹ := by group
      _ = f ^ i * q⁻¹ * p⁻¹ := by rw [hfi]
      _ = (f ^ i * q⁻¹ * (f ^ i)⁻¹) * f ^ i * p⁻¹ := by group
      _ = (f ^ i * q⁻¹ * (f ^ i)⁻¹) * (f ^ i * p⁻¹) := by group
      _ = (f ^ i * q⁻¹ * (f ^ i)⁻¹) * (p⁻¹ * f ^ i) := by rw [hfp]
      _ = ((f ^ i * q⁻¹ * (f ^ i)⁻¹) * p⁻¹) * f ^ i := by group
      _ = (p⁻¹ * (f ^ i * q⁻¹ * (f ^ i)⁻¹)) * f ^ i := by rw [hqp]
      _ = p⁻¹ * (f ^ i * q⁻¹ * (f ^ i)⁻¹) * f ^ i := by group

theorem M0_le_T (c : Cfg89T G T P Q u z x f r s) : M0 c ≤ T := by
  rintro _ ⟨p, hp, q, hq, i, rfl⟩
  exact T.mul_mem (T.mul_mem (c.P_le hp) (c.Q_le hq)) (c.f_pow_mem_T i)

theorem P_le_M0 (c : Cfg89T G T P Q u z x f r s) : P ≤ M0 c := fun p hp =>
  ⟨p, hp, 1, Q.one_mem, 0, by simp⟩

theorem Q_le_M0 (c : Cfg89T G T P Q u z x f r s) : Q ≤ M0 c := fun q hq =>
  ⟨1, P.one_mem, q, hq, 0, by simp⟩

theorem f_mem_M0 (c : Cfg89T G T P Q u z x f r s) : f ∈ M0 c :=
  ⟨1, P.one_mem, 1, Q.one_mem, 1, by simp⟩

theorem T_cases (c : Cfg89T G T P Q u z x f r s) {t : G} (ht : t ∈ T) :
    t ∈ M0 c ∨ ∃ m ∈ M0 c, t = m * x := by
  obtain ⟨p, hp, q, hq, i, j, rfl⟩ := c.T_gen t ht
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    have : x ^ j = 1 := by rw [hk, ← two_mul, pow_mul, c.x2, one_pow]
    exact ⟨p, hp, q, hq, i, by rw [this, mul_one]⟩
  · right
    have : x ^ j = x := by rw [hk, pow_succ, pow_mul, c.x2, one_pow, one_mul]
    exact ⟨p * q * f ^ i, ⟨p, hp, q, hq, i, rfl⟩, by rw [this]⟩

theorem x_conj_M0 (c : Cfg89T G T P Q u z x f r s) {m : G} (hm : m ∈ M0 c) :
    x * m * x⁻¹ ∈ M0 c := by
  obtain ⟨p, hp, q, hq, i, rfl⟩ := hm
  obtain ⟨q0, hq0, hxf⟩ := c.xf
  have hxf' : x * f * x⁻¹ ∈ M0 c := by
    rw [hxf]
    exact (M0 c).mul_mem ((M0 c).mul_mem (P_le_M0 c c.z_mem) (Q_le_M0 c hq0)) (f_mem_M0 c)
  have e : x * (p * q * f ^ i) * x⁻¹ = (x * p * x⁻¹) * (x * q * x⁻¹) * (x * f * x⁻¹) ^ i := by
    rw [conj_pow]; group
  rw [e]
  exact (M0 c).mul_mem ((M0 c).mul_mem (P_le_M0 c (c.P_norm x c.x_mem p hp))
    (Q_le_M0 c (c.Q_norm x c.x_mem q hq))) ((M0 c).pow_mem hxf' i)

theorem M0_norm (c : Cfg89T G T P Q u z x f r s) {t m : G} (ht : t ∈ T) (hm : m ∈ M0 c) :
    t * m * t⁻¹ ∈ M0 c := by
  rcases T_cases c ht with h | ⟨m', hm', rfl⟩
  · exact (M0 c).mul_mem ((M0 c).mul_mem h hm) ((M0 c).inv_mem h)
  · have e : m' * x * m * (m' * x)⁻¹ = m' * (x * m * x⁻¹) * m'⁻¹ := by group
    rw [e]
    exact (M0 c).mul_mem ((M0 c).mul_mem hm' (x_conj_M0 c hm)) ((M0 c).inv_mem hm')

theorem M0_cyclic (c : Cfg89T G T P Q u z x f r s) :
    ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ M0 c := by
  refine ⟨x, c.x_mem, fun t ht => ?_⟩
  rcases T_cases c ht with h | ⟨m, hm, rfl⟩
  · exact ⟨0, by simpa using h⟩
  · refine ⟨1, ?_⟩
    have := M0_norm c (T.inv_mem c.x_mem) hm
    simpa [mul_assoc] using this

theorem Cfg89T.involution_M0_data (c : Cfg89T G T P Q u z x f r s) {t : G} (ht : t ∈ M0 c) (ht2 : t ^ 2 = 1) :
    ∃ p ∈ P, ∃ q ∈ Q, ∃ i : ℕ, t = p * (q * f ^ i) ∧ p ^ 2 = 1 ∧ (q * f ^ i) ^ 2 = 1 := by
  obtain ⟨p, hp, q, hq, i, rfl⟩ := ht
  have hfi : f ^ i * f ^ i = 1 := by rw [← pow_add, ← two_mul, pow_mul, c.f2, one_pow]
  have hpy : p * (q * f ^ i) = (q * f ^ i) * p := by
    have hq' : p * q = q * p := c.PQ_comm p hp q hq
    have hf' : p * f ^ i = f ^ i * p := (c.f_pow_comm_P i hp).symm
    calc p * (q * f ^ i) = (p * q) * f ^ i := by group
      _ = (q * p) * f ^ i := by rw [hq']
      _ = q * (p * f ^ i) := by group
      _ = q * (f ^ i * p) := by rw [hf']
      _ = q * f ^ i * p := by group
  have hy2Q : (q * f ^ i) ^ 2 ∈ Q := by
    have hq'' : f ^ i * q * (f ^ i)⁻¹ ∈ Q := c.f_pow_conj_Q i hq
    have : (q * f ^ i) ^ 2 = q * (f ^ i * q * (f ^ i)⁻¹) * (f ^ i * f ^ i) := by rw [sq]; group
    rw [this, hfi, mul_one]
    exact Q.mul_mem hq hq''
  have hp2P : p ^ 2 ∈ P := P.pow_mem hp 2
  have hsq : p ^ 2 * (q * f ^ i) ^ 2 = 1 := by
    have : (p * (q * f ^ i)) ^ 2 = p ^ 2 * (q * f ^ i) ^ 2 := by
      have hc : Commute p (q * f ^ i) := hpy
      exact hc.mul_pow 2
    rw [← this]
    simpa [mul_assoc] using ht2
  have hp2 : p ^ 2 = 1 := by
    have : p ^ 2 = ((q * f ^ i) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    apply c.PQ_inf _ hp2P
    rw [this]
    exact Q.inv_mem hy2Q
  refine ⟨p, hp, q, hq, i, mul_assoc _ _ _, hp2, ?_⟩
  rw [hp2, one_mul] at hsq
  exact hsq

theorem Cfg89T.P_inf_Qf (c : Cfg89T G T P Q u z x f r s) {g : G} (hg : g ∈ P)
    (h : ∃ q' ∈ Q, ∃ j : ℕ, g = q' * f ^ j) : g = 1 := by
  obtain ⟨q', hq', j, rfl⟩ := h
  rw [pow_eq_pow_mod j c.f2] at hg ⊢
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize j % 2 = b at hj hg ⊢
  interval_cases b
  · simp at hg ⊢
    exact c.PQ_inf _ hg hq'
  · exfalso
    simp only [pow_one] at hg ⊢
    have hcomm : ∀ p' ∈ P, q' * f * p' = p' * (q' * f) := by
      intro p' hp'
      calc q' * f * p' = q' * (f * p') := by group
        _ = q' * (p' * f) := by rw [c.f_cent p' hp']
        _ = (q' * p') * f := by group
        _ = (p' * q') * f := by rw [c.PQ_comm p' hp' q' hq']
        _ = p' * (q' * f) := by group
    rcases c.P_center hg hcomm with h1 | h1
    ·
      apply c.f_not q'⁻¹ (Q.inv_mem hq') 0
      calc f = q'⁻¹ * (q' * f) := by group
        _ = q'⁻¹ * z ^ 0 := by rw [h1]; group
    · apply c.f_not q'⁻¹ (Q.inv_mem hq') 1
      calc f = q'⁻¹ * (q' * f) := by group
        _ = q'⁻¹ * z ^ 1 := by rw [h1]; group

theorem Cfg89T.klein_P (c : Cfg89T G T P Q u z x f r s) {a : G} (haP : a ∈ P) (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) (haz : a ≠ z) :
    zpowers z ⊔ zpowers a ≤ P ∧ Open.IsElemAbelian 2 (zpowers z ⊔ zpowers a) ∧
      Nat.card ↥(zpowers z ⊔ zpowers a) = 4 := by
  have hza : z * a = a * z := c.z_comm_P a haP
  refine ⟨sup_le ((Subgroup.zpowers_le).mpr c.z_mem) ((Subgroup.zpowers_le).mpr haP), ?_, ?_⟩
  · exact isElemAbelian_pair c.z_sq ha2 hza
  · exact card_klein c.z_sq ha2 hza c.z_ne_one ha1 haz.symm

theorem Cfg89T.u_ne_f (c : Cfg89T G T P Q u z x f r s) : f ≠ u := by
  intro h
  apply c.f_not u c.u_mem 0
  rw [pow_zero, mul_one]; exact h

theorem Cfg89T.f_ne_one (c : Cfg89T G T P Q u z x f r s) : f ≠ 1 := by
  intro h
  apply c.f_not 1 Q.one_mem 0
  rw [pow_zero, mul_one]; exact h

theorem isStar2_of_mem_M0 (c : Cfg89T G T P Q u z x f r s) {t : G} (ht : t ∈ M0 c) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) : IsStar2 t := by
  obtain ⟨p, hp, q, hq, i, rfl, hp2, hy2⟩ := c.involution_M0_data ht ht2
  set y := q * f ^ i with hy
  have hyc : ∀ p' ∈ P, p' * y = y * p' := by
    intro p' hp'
    calc p' * (q * f ^ i) = (p' * q) * f ^ i := by group
      _ = (q * p') * f ^ i := by rw [c.PQ_comm p' hp' q hq]
      _ = q * (p' * f ^ i) := by group
      _ = q * (f ^ i * p') := by rw [(c.f_pow_comm_P i hp').symm]
      _ = y * p' := by rw [hy]; group
  have hyT : y ∈ T := T.mul_mem (c.Q_le hq) (c.f_pow_mem_T i)
  have hyQf : ∃ q' ∈ Q, ∃ j : ℕ, y = q' * f ^ j := ⟨q, hq, i, rfl⟩
  obtain ⟨V, hVP, hVel, hVcard, hpV⟩ : ∃ V : Subgroup G, V ≤ P ∧ Open.IsElemAbelian 2 V ∧
      Nat.card ↥V = 4 ∧ p ∈ V := by
    rcases c.P_inv hp hp2 with h | h | h | h | h | h
    · obtain ⟨h1, h2, h3⟩ := c.klein_P c.s_mem c.s2 c.s_ne_one c.s_ne_z
      exact ⟨_, h1, h2, h3, by rw [h]; exact Subgroup.one_mem _⟩
    · obtain ⟨h1, h2, h3⟩ := c.klein_P c.s_mem c.s2 c.s_ne_one c.s_ne_z
      exact ⟨_, h1, h2, h3, by rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)⟩
    · obtain ⟨h1, h2, h3⟩ := c.klein_P c.s_mem c.s2 c.s_ne_one c.s_ne_z
      exact ⟨_, h1, h2, h3, by rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
    · obtain ⟨h1, h2, h3⟩ := c.klein_P c.s_mem c.s2 c.s_ne_one c.s_ne_z
      exact ⟨_, h1, h2, h3, by
        rw [h]; exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))⟩
    · have hrs : r * s ∈ P := P.mul_mem c.r_mem c.s_mem
      obtain ⟨h1, h2, h3⟩ := c.klein_P hrs c.rs_sq c.rs_ne_one c.rs_ne_z
      exact ⟨_, h1, h2, h3, by rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
    · have hrs : r * s ∈ P := P.mul_mem c.r_mem c.s_mem
      obtain ⟨h1, h2, h3⟩ := c.klein_P hrs c.rs_sq c.rs_ne_one c.rs_ne_z
      exact ⟨_, h1, h2, h3, by
        rw [h]; exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩
  obtain ⟨E4, hE4c, hE4el, hE4card, hyE4, hE4Qf⟩ : ∃ E4 : Subgroup G, E4 ≤ centralizer (P : Set G) ∧
      Open.IsElemAbelian 2 E4 ∧ Nat.card ↥E4 = 4 ∧ y ∈ E4 ∧
      ∀ g ∈ E4, ∃ q' ∈ Q, ∃ j : ℕ, g = q' * f ^ j := by
    have hcP : ∀ w : G, (∀ p' ∈ P, p' * w = w * p') → w ∈ centralizer (P : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hw h hh
    have hucP : u ∈ centralizer (P : Set G) := hcP u (fun p' hp' => c.PQ_comm p' hp' u c.u_mem)
    have hfcP : f ∈ centralizer (P : Set G) := hcP f (fun p' hp' => (c.f_cent p' hp').symm)
    have hycP : y ∈ centralizer (P : Set G) := hcP y hyc
    have hu2 : u ^ 2 = 1 := c.u2
    have huy : ∀ w ∈ T, u * w = w * u := fun w hw => (c.u_central w hw).symm
    by_cases hyu : y = 1 ∨ y = u
    ·
      have huf : u * f = f * u := huy f c.f_mem
      refine ⟨zpowers u ⊔ zpowers f, sup_le ((Subgroup.zpowers_le).mpr hucP) ((Subgroup.zpowers_le).mpr hfcP),
        isElemAbelian_pair hu2 c.f2 huf, card_klein hu2 c.f2 huf c.u_ne c.f_ne_one c.u_ne_f.symm, ?_, ?_⟩
      · rcases hyu with h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
      · intro g hg
        have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ zpowers f, a * b = b * a := by
          intro a ha b hb
          rcases mem_zpowers_of_sq hu2 ha with rfl | rfl <;> rcases mem_zpowers_of_sq c.f2 hb with rfl | rfl <;>
            simp [huf]
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hg
        rcases mem_zpowers_of_sq hu2 ha with rfl | rfl <;> rcases mem_zpowers_of_sq c.f2 hb with rfl | rfl
        · exact ⟨1, Q.one_mem, 0, by simp⟩
        · exact ⟨1, Q.one_mem, 1, by simp⟩
        · exact ⟨a, c.u_mem, 0, by simp⟩
        · exact ⟨a, c.u_mem, 1, by simp⟩
    ·
      push Not at hyu
      have huy' : u * y = y * u := huy y hyT
      refine ⟨zpowers u ⊔ zpowers y, sup_le ((Subgroup.zpowers_le).mpr hucP) ((Subgroup.zpowers_le).mpr hycP),
        isElemAbelian_pair hu2 hy2 huy', card_klein hu2 hy2 huy' c.u_ne hyu.1 hyu.2.symm, ?_, ?_⟩
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      · intro g hg
        have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ zpowers y, a * b = b * a := by
          intro a ha b hb
          rcases mem_zpowers_of_sq hu2 ha with rfl | rfl <;> rcases mem_zpowers_of_sq hy2 hb with rfl | rfl <;>
            simp [huy']
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hg
        rcases mem_zpowers_of_sq hu2 ha with rfl | rfl <;> rcases mem_zpowers_of_sq hy2 hb with rfl | rfl
        · exact ⟨1, Q.one_mem, 0, by simp⟩
        · exact ⟨q, hq, i, by simp [hy]⟩
        · exact ⟨a, c.u_mem, 0, by simp⟩
        · exact ⟨a * q, Q.mul_mem c.u_mem hq, i, by simp [hy, mul_assoc]⟩
  have hinf : V ⊓ E4 = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgV, hgE⟩
    rw [Subgroup.mem_bot]
    exact c.P_inf_Qf (hVP hgV) (hE4Qf g hgE)
  have hcomm : ∀ a ∈ V, ∀ b ∈ E4, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.mem_centralizer_iff.mp (hE4c hb) a (hVP ha)
    exact this
  have hEel : Open.IsElemAbelian 2 (V ⊔ E4) := IsElemAbelian.sup hVel hE4el hcomm
  have hEcard : Nat.card ↥(V ⊔ E4) = 16 := by
    rw [card_sup_of_commute hcomm hinf, hVcard, hE4card]
  have htE : p * y ∈ V ⊔ E4 := Subgroup.mul_mem_sup hpV hyE4
  exact isStar2_of_elem16 c.rank4 hEel hEcard htE ht1

omit [Finite G] in
theorem centralizer_conj_eq' (g x : G) :
    centralizer ({g * x * g⁻¹} : Set G) = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext w
  rw [Subgroup.mem_map, mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g⁻¹ * w * g, ?_, by show g * (g⁻¹ * w * g) * g⁻¹ = w; group⟩
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * w * g * x = g⁻¹ * (w * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * w) * g := by rw [h]
      _ = x * (g⁻¹ * w * g) := by group
  · rintro ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff] at hv
    show g * v * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * v * g⁻¹)
    calc g * v * g⁻¹ * (g * x * g⁻¹) = g * (v * x) * g⁻¹ := by group
      _ = g * (x * v) * g⁻¹ := by rw [hv]
      _ = g * x * g⁻¹ * (g * v * g⁻¹) := by group

theorem isStar2_conj {x : G} (h : IsStar2 x) (g : G) : IsStar2 (g * x * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_conj']; exact h.1
  · rw [centralizer_conj_eq']
    have e := Bg.pRank_mulEquiv (G := ↥(centralizer ({x} : Set G))) one_lt_two
      (Subgroup.equivMapOfInjective (centralizer ({x} : Set G)) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective)
    rw [← e]
    exact h.2

theorem false_of_sylow (c : Cfg89T G T P Q u z x f r s) (hT : IsSylowOf 2 T ⊤) : False := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_cyclic_quot c.simple c.nonab hT (M0_le_T c)
    (fun s' hs q hq => M0_norm c hs hq) (M0_cyclic c) c.x_mem c.x_ord
  have hx2 : x ^ 2 = 1 := c.x2
  have hx'2 : (g⁻¹ * x * g) ^ 2 = 1 := by
    have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      have := conj_pow (a := g⁻¹) (b := x) (i := 2)
      simpa using this
    rw [this, hx2]; group
  have hx'1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    have hx1 : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have := c.x_ord
    rw [hx1, orderOf_one] at this
    omega
  have hstar := isStar2_of_mem_M0 c hg hx'2 hx'1
  apply c.x_not_star
  have := isStar2_conj hstar g
  simpa [mul_assoc] using this

end Zcase

end CFSG.GH74.GLS.C3.Layer1.P89
