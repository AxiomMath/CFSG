module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueSetup

public section

namespace CFSG.Semidihedral.UnitaryDValue

section General

variable {G : Type*} [Group G]

theorem conj_inv_eq (g a : G) : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group

theorem mem_normalizer_of_conj_mem_of_finite [Finite G] {U : Subgroup G} {g : G}
    (h : ∀ u ∈ U, g * u * g⁻¹ ∈ U) : g ∈ Subgroup.normalizer (U : Set G) := by
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have hcard : Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : U.map (MulAut.conj g).toMonoidHom = U := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← heq]
    exact ⟨a, ha, rfl⟩
  · intro ha
    rw [← heq] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have h' : g * b * g⁻¹ = g * a * g⁻¹ := hba
    have : b = a := by simpa using h'
    rw [← this]
    exact hb

theorem card_subgroupOf_of_le' {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem exists_mul_mem_normalizer_of_sylow [Finite G] {p : ℕ} [Fact p.Prime] {K U : Subgroup G}
    (hUK : U ≤ K) (P : Sylow p K) (hP : (P : Subgroup K) = U.subgroupOf K) {g : G}
    (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : ∃ c ∈ K, c * g ∈ Subgroup.normalizer (U : Set G) := by
  set U₂ := U.map (MulAut.conj g).toMonoidHom with hU₂
  have hU₂K : U₂ ≤ K := by
    rintro _ ⟨u, hu, rfl⟩
    exact hg u (hUK hu)
  have hcardU₂ : Nat.card U₂ = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcard : Nat.card (U₂.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [card_subgroupOf_of_le' hU₂K, hcardU₂, ← card_subgroupOf_of_le' hUK,
      ← hP, Sylow.card_eq_multiplicity]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K (Sylow.ofCard (U₂.subgroupOf K) hcard) P
  refine ⟨c, c.2, mem_normalizer_of_conj_mem_of_finite fun u hu => ?_⟩
  have hmem : (⟨g * u * g⁻¹, hU₂K ⟨u, hu, rfl⟩⟩ : K) ∈
      (Sylow.ofCard (U₂.subgroupOf K) hcard : Subgroup K) := by
    rw [Sylow.coe_ofCard]
    exact ⟨u, hu, rfl⟩
  have h2 : c * ⟨g * u * g⁻¹, hU₂K ⟨u, hu, rfl⟩⟩ * c⁻¹ ∈ (P : Subgroup K) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact ⟨_, hmem, rfl⟩
  rw [hP] at h2
  have h3 : ((c * ⟨g * u * g⁻¹, hU₂K ⟨u, hu, rfl⟩⟩ * c⁻¹ : K) : G) ∈ U := h2
  convert h3 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  group

end General

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem q_odd : Odd D.q := (D.prime_p.eq_two_or_odd'.resolve_left D.ne_two).pow

theorem seven_le_q : 7 ≤ D.q := by
  have h5 := D.five_lt_q
  obtain ⟨k, hk⟩ := D.q_odd
  change D.p ^ D.f = 2 * k + 1 at hk
  show 7 ≤ D.p ^ D.f
  omega

theorem q_pos : 0 < D.q := by have := D.seven_le_q; omega

theorem q_le_sq : D.q ≤ D.q ^ 2 := Nat.le_self_pow (by norm_num) _

theorem m_pos : 0 < D.m := by
  obtain ⟨k, hk⟩ := D.m_pow
  rw [hk]
  exact pow_pos (by norm_num) k

theorem card_A_pos : 0 < Nat.card D.A := Nat.card_pos

theorem card_A_dvd : Nat.card D.A ∣ D.q + 1 := (Dvd.intro_left _ rfl).trans D.A_dvd

theorem factorization_m {r : ℕ} (hr2 : r ≠ 2) : D.m.factorization r = 0 := by
  obtain ⟨k, hk⟩ := D.m_pow
  rw [hk, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_apply,
    ite_eq_right_iff.mpr (fun h => absurd h.symm hr2)]

theorem Q_cast {R : Type*} [CommRing R] :
    ((D.q ^ 2 - D.q + 1 : ℕ) : R) = (D.q : R) ^ 2 - D.q + 1 := by
  rw [Nat.cast_add, Nat.cast_sub D.q_le_sq, Nat.cast_pow, Nat.cast_one]

theorem cube_add_one_eq : D.q ^ 3 + 1 = (D.q + 1) * (D.q ^ 2 - D.q + 1) := by
  zify [D.q_le_sq]
  ring

theorem not_dvd_q_of_dvd {r : ℕ} (hr : r.Prime) (hrq : r ∣ D.q + 1) : ¬ r ∣ D.q := by
  intro h
  have := (Nat.dvd_add_right h).mp hrq
  exact hr.one_lt.ne' (Nat.dvd_one.mp this)

theorem not_dvd_q_sub_one_of_dvd {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ D.q + 1) :
    ¬ r ∣ D.q - 1 := by
  intro h
  have hq := D.q_pos
  have h2 : r ∣ D.q + 1 - (D.q - 1) := Nat.dvd_sub hrq h
  rw [show D.q + 1 - (D.q - 1) = 2 by omega] at h2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)

theorem eq_three_of_dvd_Q {r : ℕ} (hr : r.Prime) (hrq : r ∣ D.q + 1)
    (hQ : r ∣ D.q ^ 2 - D.q + 1) : r = 3 := by
  rw [← ZMod.natCast_eq_zero_iff] at hrq hQ
  rw [D.Q_cast] at hQ
  rw [Nat.cast_add, Nat.cast_one] at hrq
  have hq : (D.q : ZMod r) = -1 := eq_neg_of_add_eq_zero_left hrq
  rw [hq] at hQ
  have h3 : ((3 : ℕ) : ZMod r) = 0 := by
    have : ((3 : ℕ) : ZMod r) = (-1) ^ 2 - -1 + 1 := by push_cast; ring
    rw [this, hQ]
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)

theorem three_factorization_Q (h3 : 3 ∣ D.q + 1) : (D.q ^ 2 - D.q + 1).factorization 3 = 1 := by
  obtain ⟨j, hj⟩ := h3
  have hj1 : 1 ≤ j := by have := D.q_pos; omega
  have hQ : D.q ^ 2 - D.q + 1 = 3 * (3 * j ^ 2 - 3 * j + 1) := by
    have hq : D.q = 3 * j - 1 := by omega
    rw [hq]
    have h1 : 3 * j - 1 ≤ (3 * j - 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h2 : 3 * j ≤ 3 * j ^ 2 := by nlinarith
    zify [h1, h2, hj1, show 1 ≤ 3 * j by omega]
    ring
  have hne : 3 * j ^ 2 - 3 * j + 1 ≠ 0 := by omega
  have hnd : ¬ 3 ∣ 3 * j ^ 2 - 3 * j + 1 := by
    have h2 : 3 * j ≤ 3 * j ^ 2 := by nlinarith
    omega
  rw [hQ, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd hnd]


theorem fact_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (r : ℕ) :
    (a * b).factorization r = a.factorization r + b.factorization r := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

theorem card_C_eq : Nat.card D.C = D.m * Nat.card D.A * (D.q + 1) := D.card_C

theorem factorization_card_C {r : ℕ} (hr2 : r ≠ 2) :
    (Nat.card D.C).factorization r =
      (Nat.card D.A).factorization r + (D.q + 1).factorization r := by
  rw [D.card_C_eq, fact_mul (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne') (by omega),
    fact_mul D.m_pos.ne' D.card_A_pos.ne', D.factorization_m hr2, zero_add]

theorem factorization_card_W {r : ℕ} (hr2 : r ≠ 2) :
    (Nat.card D.W).factorization r = (D.q + 1).factorization r := by
  rw [← D.W_card, fact_mul D.m_pos.ne' Nat.card_pos.ne', D.factorization_m hr2, zero_add]

theorem factorization_q {r : ℕ} (hr : r.Prime) (hrq : r ∣ D.q + 1) :
    D.q.factorization r = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (D.not_dvd_q_of_dvd hr hrq)

theorem factorization_card_N {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ D.q + 1) :
    (Nat.card D.N).factorization r =
      (Nat.card D.A).factorization r + (D.q + 1).factorization r := by
  have hq7 := D.seven_le_q
  have hsq : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    have : 1 ≤ D.q ^ 2 := Nat.one_le_pow _ _ D.q_pos
    zify [this, show 1 ≤ D.q by omega]
    ring
  have hq0 : D.q ≠ 0 := by omega
  have hq1 : D.q - 1 ≠ 0 := by omega
  have hqp : D.q + 1 ≠ 0 := by omega
  rw [D.card_N, hsq, fact_mul (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne')
    (Nat.mul_ne_zero hq0 (Nat.mul_ne_zero hq1 hqp)),
    fact_mul D.m_pos.ne' D.card_A_pos.ne', fact_mul hq0 (Nat.mul_ne_zero hq1 hqp),
    fact_mul hq1 hqp, D.factorization_m hr2, D.factorization_q hr hrq,
    Nat.factorization_eq_zero_of_not_dvd (D.not_dvd_q_sub_one_of_dvd hr hr2 hrq)]
  ring

theorem Q_pos : 0 < D.q ^ 2 - D.q + 1 := by omega

theorem factorization_card_G {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ D.q + 1) :
    (Nat.card G).factorization r = (Nat.card D.A).factorization r +
      (D.q + 1).factorization r + (D.q ^ 2 - D.q + 1).factorization r := by
  have hq7 := D.seven_le_q
  have hq3 : D.q ^ 3 ≠ 0 := pow_ne_zero 3 D.q_pos.ne'
  have hq1 : D.q - 1 ≠ 0 := by omega
  have hqp : D.q + 1 ≠ 0 := by omega
  rw [D.card_G]
  change (D.m * Nat.card D.A * D.q ^ 3 * (D.q - 1) * (D.q ^ 3 + 1)).factorization r = _
  rw [D.cube_add_one_eq,
    fact_mul (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne')
      hq3) hq1) (Nat.mul_ne_zero hqp D.Q_pos.ne'),
    fact_mul (Nat.mul_ne_zero (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne') hq3) hq1,
    fact_mul (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne') hq3,
    fact_mul D.m_pos.ne' D.card_A_pos.ne', fact_mul hqp D.Q_pos.ne',
    D.factorization_m hr2, Nat.factorization_pow, Finsupp.smul_apply, D.factorization_q hr hrq,
    Nat.factorization_eq_zero_of_not_dvd (D.not_dvd_q_sub_one_of_dvd hr hr2 hrq)]
  simp only [smul_eq_mul, mul_zero, zero_add, add_zero]
  ring

theorem factorization_Q_of_ne_three {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hrq : r ∣ D.q + 1) : (D.q ^ 2 - D.q + 1).factorization r = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun h => hr3 (D.eq_three_of_dvd_Q hr hrq h)

theorem W_comm : ∀ a ∈ D.W, ∀ b ∈ D.W, a * b = b * a :=
  fun a ha b hb => D.C_comm a (D.W_le ha) b (D.W_le hb)

theorem A_comm : ∀ a ∈ D.A, ∀ b ∈ D.A, a * b = b * a :=
  fun a ha b hb => D.C_comm a (D.A_le_C ha) b (D.A_le_C hb)

abbrev PW (r : ℕ) [Fact r.Prime] : Subgroup G := commPrimaryPart D.W D.W_comm r

abbrev PA (r : ℕ) [Fact r.Prime] : Subgroup G := commPrimaryPart D.A D.A_comm r

variable {r : ℕ} [Fact r.Prime]

theorem PW_le_W : D.PW r ≤ D.W := commPrimaryPart_le _ _ r

theorem PA_le_A : D.PA r ≤ D.A := commPrimaryPart_le _ _ r

theorem PW_le : D.PW r ≤ D.primaryPart r := fun _ hc => ⟨D.W_le hc.1, hc.2⟩

theorem PA_le : D.PA r ≤ D.primaryPart r := fun _ hc => ⟨D.A_le_C hc.1, hc.2⟩

theorem card_PW (hr2 : r ≠ 2) : Nat.card (D.PW r) = r ^ (D.q + 1).factorization r := by
  rw [card_commPrimaryPart, D.factorization_card_W hr2]

theorem card_PA : Nat.card (D.PA r) = r ^ (Nat.card D.A).factorization r :=
  card_commPrimaryPart _ _ r

theorem card_primaryPart_odd (hr2 : r ≠ 2) :
    Nat.card (D.primaryPart r) =
      r ^ ((Nat.card D.A).factorization r + (D.q + 1).factorization r) := by
  rw [D.card_primaryPart, D.factorization_card_C hr2]

theorem disjoint_PW_PA : Disjoint (D.PW r) (D.PA r) := by
  rw [Subgroup.disjoint_def]
  intro u hW hA
  have : u ∈ D.W ⊓ D.A := ⟨hW.1, hA.1⟩
  rw [D.W_inf_A] at this
  exact this

theorem exists_mul_eq (hr2 : r ≠ 2) {u : G} (hu : u ∈ D.primaryPart r) :
    ∃ w ∈ D.PW r, ∃ a ∈ D.PA r, u = w * a := by
  let f : D.PW r × D.PA r → D.primaryPart r := fun g =>
    ⟨g.1 * g.2, (D.primaryPart r).mul_mem (D.PW_le g.1.2) (D.PA_le g.2.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subgroup.mul_injective_of_disjoint D.disjoint_PW_PA
    exact congrArg Subtype.val hab
  have hcard : Nat.card (D.PW r × D.PA r) = Nat.card (D.primaryPart r) := by
    rw [Nat.card_prod, D.card_PW hr2, D.card_PA, D.card_primaryPart_odd hr2, pow_add, mul_comm]
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcard.ge
  obtain ⟨⟨w, a⟩, hwa⟩ := hbij.2 ⟨u, hu⟩
  exact ⟨w, w.2, a, a.2, (congrArg Subtype.val hwa).symm⟩

theorem primaryPart_le_W_of_not_dvd (hr2 : r ≠ 2) (hrA : ¬ r ∣ Nat.card D.A) :
    D.primaryPart r ≤ D.W := by
  intro u hu
  obtain ⟨w, hw, a, ha, rfl⟩ := D.exists_mul_eq hr2 hu
  have hA1 : Nat.card (D.PA r) = 1 := by
    rw [D.card_PA, Nat.factorization_eq_zero_of_not_dvd hrA, pow_zero]
  have ha1 : a = 1 := by
    have := (Subgroup.card_eq_one.mp hA1)
    have h : a ∈ (⊥ : Subgroup G) := this ▸ ha
    exact h
  rw [ha1, mul_one]
  exact D.PW_le_W hw

theorem C_conj {c u : G} (hc : c ∈ D.C) (hu : u ∈ D.C) : c * u * c⁻¹ = u :=
  conj_eq_of_comm (D.C_comm c hc u hu)

theorem y_conj_A {a : G} (ha : a ∈ D.A) : D.y * a * D.y⁻¹ = a :=
  conj_eq_of_comm (D.A_central a ha D.y D.y_mem_N)

theorem y_inv_conj_W {w : G} (hw : w ∈ D.W) : D.y⁻¹ * w * D.y = w⁻¹ := by
  have h := D.y_W w⁻¹ (D.W.inv_mem hw)
  rw [inv_inv] at h
  calc D.y⁻¹ * w * D.y = D.y⁻¹ * (D.y * w⁻¹ * D.y⁻¹) * D.y := by rw [h]
    _ = w⁻¹ := by group


theorem t_conj_eq_of_le_W {P : Subgroup G} (hPW : P ≤ D.W)
    (htP : ∀ u ∈ P, D.t * u * D.t⁻¹ ∈ P) {u : G} (hu : u ∈ P) : D.t * u * D.t⁻¹ = u := by
  have hPC : ∀ v ∈ P, v ∈ D.C := fun v hv => D.W_le (hPW hv)
  have hsq : ∀ v ∈ P, D.t * (D.t * v * D.t⁻¹) * D.t⁻¹ = v := by
    intro v hv
    have hv' := htP v hv
    have h1 := D.C_conj D.y_t_y_inv_t_mem_C (hPC v hv)
    have h2 : D.y⁻¹ * (D.t * v * D.t⁻¹) * D.y = (D.t * v * D.t⁻¹)⁻¹ :=
      D.y_inv_conj_W (hPW hv')
    have he : D.y * D.t * D.y⁻¹ * D.t = D.y * (D.t * (D.y⁻¹ * D.t)) := by group
    rw [he, conj_mul_eq, conj_mul_eq, conj_mul_eq, inv_inv, h2, conj_inv_eq, conj_inv_eq,
      D.y_W _ (hPW (htP _ hv')), inv_inv] at h1
    exact h1
  have hcube : D.t ^ 3 * u * (D.t ^ 3)⁻¹ = u := D.C_conj D.t_cube_mem_C (hPC u hu)
  rw [pow_three, conj_mul_eq, conj_mul_eq] at hcube
  rw [hsq _ (htP u hu)] at hcube
  exact hcube

theorem t_pow_conj_eq_of_le_W {P : Subgroup G} (hPW : P ≤ D.W)
    (htP : ∀ u ∈ P, D.t * u * D.t⁻¹ ∈ P) (i : ℕ) {u : G} (hu : u ∈ P) :
    D.t ^ i * u * (D.t ^ i)⁻¹ = u := by
  induction i with
  | zero => simp
  | succ k ih => rw [pow_succ, conj_mul_eq, D.t_conj_eq_of_le_W hPW htP hu, ih]

theorem t_conj_primaryPart {u : G} (hu : u ∈ D.primaryPart r) :
    D.t * u * D.t⁻¹ ∈ D.primaryPart r :=
  D.conj_mem_primaryPart D.t_mem_normalizer_T hu

theorem normalizer_T_conj_of_le_W {P : Subgroup G} (hPW : P ≤ D.W)
    (htP : ∀ u ∈ P, D.t * u * D.t⁻¹ ∈ P) {g : G} (hg : g ∈ Subgroup.normalizer (D.T : Set G)) :
    (∀ u ∈ P, g * u * g⁻¹ = u) ∨ (∀ u ∈ P, g * u * g⁻¹ = u⁻¹) := by
  obtain ⟨i, j, hi, hj, hC⟩ := D.normalizer_T_cases hg
  set c := (D.t ^ i * D.y ^ j)⁻¹ * g with hc
  have hg' : g = D.t ^ i * D.y ^ j * c := by rw [hc]; group
  have hti : ∀ u ∈ P, D.t ^ i * u * (D.t ^ i)⁻¹ = u := fun u hu =>
    D.t_pow_conj_eq_of_le_W hPW htP i hu
  have hcu : ∀ u ∈ P, c * u * c⁻¹ = u := fun u hu => D.C_conj hC (D.W_le (hPW hu))
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · left
    intro u hu
    rw [hg', pow_zero, mul_one, conj_mul_eq, hcu u hu, hti u hu]
  · right
    intro u hu
    rw [hg', pow_one, conj_mul_eq, hcu u hu, conj_mul_eq, D.y_W u (hPW hu)]
    have hu' : u⁻¹ ∈ P := P.inv_mem hu
    rw [hti _ hu']

theorem isCyclic_of_le_W {P : Subgroup G} (hPW : P ≤ D.W) : IsCyclic P := by
  have := D.W_cyclic
  exact (Subgroup.subgroupOfEquivOfLe hPW).isCyclic.mp inferInstance

theorem exists_eq_zpowers_of_le_W {P : Subgroup G} (hPW : P ≤ D.W) :
    ∃ u : G, P = Subgroup.zpowers u := by
  have := D.isCyclic_of_le_W hPW
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.zpow_mem _ g.2 k

theorem normalizer_conj_of_le_W {u₀ : G} (hu₀W : u₀ ∈ D.W) (hu₀ : u₀ ≠ 1)
    (htP : ∀ u ∈ Subgroup.zpowers u₀, D.t * u * D.t⁻¹ ∈ Subgroup.zpowers u₀) {g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers u₀ : Set G)) :
    (∀ u ∈ Subgroup.zpowers u₀, g * u * g⁻¹ = u) ∨
      (∀ u ∈ Subgroup.zpowers u₀, g * u * g⁻¹ = u⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Subgroup.zpowers u₀ with hPdef
  have hPW : P ≤ D.W := by
    rw [hPdef, Subgroup.zpowers_le]
    exact hu₀W
  have ht0 : D.t * u₀ * D.t⁻¹ = u₀ :=
    D.t_conj_eq_of_le_W hPW htP (Subgroup.mem_zpowers u₀)
  have hw : ∀ g' ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      D.N ⊓ Subgroup.centralizer {g' * u₀ * g'⁻¹} ≤ D.C := by
    have hfix : ∀ g' ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G), g' * u₀ * g'⁻¹ = u₀ := by
      have ht1 : D.t⁻¹ * u₀ * D.t⁻¹⁻¹ = u₀ := by
        rw [inv_inv]
        calc D.t⁻¹ * u₀ * D.t = D.t⁻¹ * (D.t * u₀ * D.t⁻¹) * D.t := by rw [ht0]
          _ = u₀ := by group
      intro g' hg'
      rcases hg' with rfl | rfl | rfl
      · simp
      · exact ht1
      · rw [conj_mul_eq, ht1, ht1]
    intro g' hg' c hc
    rw [hfix g' hg'] at hc
    exact ⟨hc.1, D.W_centralizer u₀ hu₀W hu₀ hc⟩
  have hu₀C : u₀ ∈ D.C := D.W_le hu₀W
  set K := Subgroup.centralizer ({u₀} : Set G) with hK
  have hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro k hk
    rw [hK, Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    have hgi : g⁻¹ * u₀ * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u₀).mp
        (Subgroup.mem_zpowers u₀)
      simpa using this
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgi
    have hkn : k * u₀ ^ n = u₀ ^ n * k := ((Commute.zpow_right hk.symm.symm n).eq)
    calc g * k * g⁻¹ * u₀ = g * (k * (g⁻¹ * u₀ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u₀ * g) * k) * g⁻¹ := by rw [← hn, hkn]
      _ = u₀ * (g * k * g⁻¹) := by group
  have hUK : D.U ≤ K := by
    intro u hu
    rw [hK, Subgroup.mem_centralizer_singleton_iff]
    exact D.C_comm u hu.1 u₀ hu₀C
  obtain ⟨c, hcK, hcg⟩ := exists_mul_mem_normalizer_of_sylow hUK (D.sylowU hu₀C hw)
    (D.coe_sylowU hu₀C hw) hgK
  have hcgT := D.normalizer_U_le hcg
  have htP' : ∀ u ∈ P, D.t * u * D.t⁻¹ ∈ P := htP
  have hcP : ∀ u ∈ P, c * u * c⁻¹ = u := by
    intro u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [hK, Subgroup.mem_centralizer_singleton_iff] at hcK
    exact conj_eq_of_comm ((Commute.zpow_right hcK.symm.symm n).eq)
  have hg' : g = c⁻¹ * (c * g) := by group
  rcases D.normalizer_T_conj_of_le_W hPW htP' hcgT with h | h
  · left
    intro u hu
    have hcu := hcP u hu
    rw [hg', conj_mul_eq, h u hu, inv_inv]
    calc c⁻¹ * u * c = c⁻¹ * (c * u * c⁻¹) * c := by rw [hcu]
      _ = u := by group
  · right
    intro u hu
    have hcu := hcP u⁻¹ (P.inv_mem hu)
    rw [hg', conj_mul_eq, h u hu, inv_inv]
    calc c⁻¹ * u⁻¹ * c = c⁻¹ * (c * u⁻¹ * c⁻¹) * c := by rw [hcu]
      _ = u⁻¹ := by group

theorem relIndex_eq_two_of_act {u₀ τ : G} (hu₀ : u₀⁻¹ ≠ u₀)
    (hact : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers u₀ : Set G),
      (∀ u ∈ Subgroup.zpowers u₀, g * u * g⁻¹ = u) ∨
        (∀ u ∈ Subgroup.zpowers u₀, g * u * g⁻¹ = u⁻¹))
    (hτ : ∀ u ∈ Subgroup.zpowers u₀, τ * u * τ⁻¹ = u⁻¹) :
    (Subgroup.centralizer (Subgroup.zpowers u₀ : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u₀ : Set G)) = 2 := by
  set P := Subgroup.zpowers u₀
  have hτN : τ ∈ Subgroup.normalizer (P : Set G) := by
    apply mem_normalizer_of_conj_mem_of_finite
    intro u hu
    rw [hτ u hu]
    exact P.inv_mem hu
  have hcent : ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) ↔ ∀ u ∈ P, g * u * g⁻¹ = u := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    exact ⟨fun h u hu => conj_eq_of_comm (h u hu).symm,
      fun h u hu => (comm_of_conj_eq (h u hu)).symm⟩
  have hnot : ∀ g : G, (∀ u ∈ P, g * u * g⁻¹ = u⁻¹) → g ∉ Subgroup.centralizer (P : Set G) := by
    intro g hg hgC
    apply hu₀
    rw [← hg u₀ (Subgroup.mem_zpowers u₀), (hcent g).mp hgC u₀ (Subgroup.mem_zpowers u₀)]
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨τ, hτN⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases hact b b.2 with h | h
  · refine Or.inr ⟨(hcent b).mpr h, hnot _ fun u hu => ?_⟩
    rw [conj_mul_eq, hτ u hu, h _ (P.inv_mem hu)]
  · refine Or.inl ⟨(hcent _).mpr fun u hu => ?_, hnot _ h⟩
    rw [conj_mul_eq, hτ u hu, h _ (P.inv_mem hu), inv_inv]

theorem exists_sylow_index_two (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrq : r ∣ D.q + 1)
    (hrA : ¬ r ∣ Nat.card D.A) :
    ∃ P : Sylow r G, (P : Subgroup G) = D.primaryPart r ∧ IsCyclic (P : Subgroup G) ∧
      (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2 ∧
      Nat.card P = r ^ (D.q + 1).factorization r := by
  have hr : r.Prime := Fact.out
  have hA0 : (Nat.card D.A).factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd hrA
  have hcard : Nat.card (D.primaryPart r) = r ^ (D.q + 1).factorization r := by
    rw [D.card_primaryPart_odd hr2, hA0, zero_add]
  have hG : (Nat.card G).factorization r = (D.q + 1).factorization r := by
    rw [D.factorization_card_G hr hr2 hrq, hA0, D.factorization_Q_of_ne_three hr hr3 hrq,
      zero_add, add_zero]
  let P : Sylow r G := Sylow.ofCard (D.primaryPart r) (by rw [hcard, hG])
  have hPeq : (P : Subgroup G) = D.primaryPart r := Sylow.coe_ofCard _ _
  have hPW : D.primaryPart r ≤ D.W := D.primaryPart_le_W_of_not_dvd hr2 hrA
  obtain ⟨u₀, hu₀⟩ := D.exists_eq_zpowers_of_le_W hPW
  have hpos : 1 ≤ (D.q + 1).factorization r :=
    (hr.dvd_iff_one_le_factorization (by omega)).mp hrq
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    have : Nat.card (D.primaryPart r) = 1 := by
      rw [hu₀, h, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]
    rw [hcard] at this
    have := Nat.one_lt_pow (by omega) hr.one_lt (n := (D.q + 1).factorization r)
    omega
  have hu₀W : u₀ ∈ D.W := hPW (hu₀ ▸ Subgroup.mem_zpowers u₀)
  have hu₀inv : u₀⁻¹ ≠ u₀ := by
    intro h
    have h2 : u₀ ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [← h]; exact inv_mul_cancel u₀
    have hodd : Odd (orderOf u₀) := by
      have hmem : u₀ ∈ D.primaryPart r := hu₀ ▸ Subgroup.mem_zpowers u₀
      obtain ⟨-, k, hk⟩ := hmem
      rw [hk]
      exact (hr.eq_two_or_odd'.resolve_left hr2).pow
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    have h1 : orderOf u₀ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
      · exact h'
      · rw [h'] at hodd
        exact absurd hodd (by decide)
    exact hu₀1 (orderOf_eq_one_iff.mp h1)
  have htP : ∀ u ∈ Subgroup.zpowers u₀, D.t * u * D.t⁻¹ ∈ Subgroup.zpowers u₀ := by
    intro u hu
    rw [← hu₀] at hu ⊢
    exact D.t_conj_primaryPart hu
  have hact := fun g hg => D.normalizer_conj_of_le_W hu₀W hu₀1 htP (g := g) hg
  have hyP : ∀ u ∈ Subgroup.zpowers u₀, D.y * u * D.y⁻¹ = u⁻¹ := by
    intro u hu
    rw [← hu₀] at hu
    exact D.y_W u (hPW hu)
  refine ⟨P, hPeq, ?_, ?_, by rw [Sylow.card_eq_multiplicity, hG]⟩
  · rw [hPeq]
    exact D.isCyclic_of_le_W hPW
  · change (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 2
    rw [hPeq, hu₀]
    exact relIndex_eq_two_of_act hu₀inv hact hyP

end DValueData

end CFSG.Semidihedral.UnitaryDValue
