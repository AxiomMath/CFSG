module

public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.AGLEmbedding

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_ne_one {p : ℕ} [Fact p.Prime] {E : Subgroup G} (hE : IsPGroup p E)
    (hEne : E ≠ ⊥) {x : G} (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (hx : IsPGroup p (Subgroup.zpowers x)) :
    ∃ e ∈ E, e ≠ 1 ∧ x * e * x⁻¹ = e := by
  set S := E ⊔ Subgroup.zpowers x with hSdef
  have hS : IsPGroup p S := IsPGroup.to_sup_of_normal_left' hE hx (Subgroup.zpowers_le.mpr hxE)
  have : Group.IsNilpotent S := hS.isNilpotent
  have hES : E ≤ S := le_sup_left
  have hxS : x ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hN : (E.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).mpr
      (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxE))
  have hne : E.subgroupOf S ≠ ⊥ := by
    intro h
    apply hEne
    rw [← Subgroup.map_subgroupOf_eq_of_le hES, h, Subgroup.map_bot]
  obtain ⟨s, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨((s : S) : G), s.2.1, fun h1 => hs1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp s.2.2 ⟨x, hxS⟩)
  simp only [Subgroup.coe_mul] at hc
  rw [hc, mul_inv_cancel_right]

theorem exists_mul_eq_of_card {A B R : Subgroup G} (hA : A ≤ R) (hB : B ≤ R)
    (hAB : A ⊓ B = ⊥) (hcard : Nat.card A * Nat.card B = Nat.card R) :
    ∀ r ∈ R, ∃ a ∈ A, ∃ b ∈ B, a * b = r := by
  set f : A × B → R := fun x => ⟨(x.1 : G) * (x.2 : G), R.mul_mem (hA x.1.2) (hB x.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
      have he : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ :=
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      rw [he]
      exact B.mul_mem b'.2 (B.inv_mem b.2)
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    rw [← hmem] at h1
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext (mul_left_cancel h1))
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [Nat.card_prod, hcard]⟩
  intro r hr
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨r, hr⟩
  exact ⟨a, a.2, b, b.2, congrArg Subtype.val hab⟩

theorem zpowers_inf_zpowers_eq_bot_of_not_mem {p : ℕ} [Fact p.Prime] {z w : G}
    (hz : orderOf z = p) (hzw : z ∉ Subgroup.zpowers w) :
    Subgroup.zpowers z ⊓ Subgroup.zpowers w = ⊥ := by
  have hp : p.Prime := Fact.out
  rw [eq_bot_iff]
  intro y ⟨hyz, hyw⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hyp : orderOf y = p := by
    have h1 : orderOf y ∣ p := hz ▸ orderOf_dvd_of_mem_zpowers hyz
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have heq : Subgroup.zpowers y = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyz)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hyp, hz])
  exact hzw ((Subgroup.zpowers_le.mpr hyw) (heq ▸ Subgroup.mem_zpowers z))

omit [Finite G] in
theorem exists_conj_pow_eq {x z w : G} {i j : ℤ} (hzw : Commute z w)
    (hxz : x * z * x⁻¹ = z ^ i * w ^ j) (hxw : x * w * x⁻¹ = w) (k : ℕ) :
    ∃ c : ℤ, x ^ k * z * (x ^ k)⁻¹ = z ^ (i ^ k) * w ^ c := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨j * i ^ k + c, ?_⟩
    have hconj : ∀ g : G, x * g * x⁻¹ = MulAut.conj x g := fun g => rfl
    calc x ^ (k + 1) * z * (x ^ (k + 1))⁻¹ = x * (x ^ k * z * (x ^ k)⁻¹) * x⁻¹ := by group
      _ = MulAut.conj x (z ^ (i ^ k) * w ^ c) := by rw [hc]; rfl
      _ = (z ^ i * w ^ j) ^ (i ^ k) * w ^ c := by
        rw [map_mul, map_zpow, map_zpow, ← hconj, ← hconj, hxz, hxw]
      _ = z ^ (i ^ (k + 1)) * w ^ (j * i ^ k + c) := by
        rw [(hzw.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul, mul_assoc, ← zpow_add,
          pow_succ, mul_comm (i ^ k) i]

omit [Finite G] in
theorem conj_pow_eq_mul_pow {x z u : G} (hxz : x * z * x⁻¹ = z * u) (hxu : x * u * x⁻¹ = u)
    (k : ℕ) : x ^ k * z * (x ^ k)⁻¹ = z * u ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hconj : ∀ g : G, x * g * x⁻¹ = MulAut.conj x g := fun g => rfl
    calc x ^ (k + 1) * z * (x ^ (k + 1))⁻¹ = x * (x ^ k * z * (x ^ k)⁻¹) * x⁻¹ := by group
      _ = MulAut.conj x (z * u ^ k) := by rw [ih]; rfl
      _ = z * u * u ^ k := by rw [map_mul, map_pow, ← hconj, ← hconj, hxz, hxu]
      _ = z * u ^ (k + 1) := by rw [mul_assoc, ← pow_succ']

omit [Finite G] in
theorem zpow_eq_self_of_conj {p : ℕ} [Fact p.Prime] {x z w : G} {i j : ℤ} (hzw : Commute z w)
    (hxz : x * z * x⁻¹ = z ^ i * w ^ j) (hxw : x * w * x⁻¹ = w) {n : ℕ} (hxn : x ^ p ^ n = 1)
    (hz : orderOf z = p) (hbot : Subgroup.zpowers z ⊓ Subgroup.zpowers w = ⊥) : z ^ i = z := by
  obtain ⟨c, hc⟩ := exists_conj_pow_eq hzw hxz hxw (p ^ n)
  rw [hxn, one_mul, inv_one, mul_one] at hc
  have h1 : z ^ (i ^ p ^ n - 1) = (w ^ c)⁻¹ := by
    have this : z ^ (i ^ p ^ n) = z * (w ^ c)⁻¹ := by
      calc z ^ (i ^ p ^ n) = z ^ (i ^ p ^ n) * w ^ c * (w ^ c)⁻¹ := by group
        _ = z * (w ^ c)⁻¹ := by rw [← hc]
    have hcomm : Commute z (w ^ c)⁻¹ := (hzw.zpow_right c).inv_right
    calc z ^ (i ^ p ^ n - 1) = z ^ (i ^ p ^ n) * z⁻¹ := zpow_sub_one z _
      _ = z * (w ^ c)⁻¹ * z⁻¹ := by rw [this]
      _ = (w ^ c)⁻¹ := by rw [hcomm.eq, mul_inv_cancel_right]
  have h2 : z ^ (i ^ p ^ n - 1) ∈ Subgroup.zpowers z ⊓ Subgroup.zpowers w :=
    ⟨Subgroup.zpow_mem_zpowers z _, h1 ▸ Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers w c)⟩
  rw [hbot, Subgroup.mem_bot, ← orderOf_dvd_iff_zpow_eq_one, hz] at h2
  have h3 : ((i ^ p ^ n - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  push_cast at h3
  rw [ZMod.pow_card_pow] at h3
  have h4 : (p : ℤ) ∣ i - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; exact h3)
  have h5 : z ^ (i - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hz]; exact h4)
  rw [show i = (i - 1) + 1 by ring, zpow_add_one, h5, one_mul]

theorem exists_axis {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, Commute a b) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hEcard : Nat.card E = p ^ 2) {x : G} (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (hx : IsPGroup p (Subgroup.zpowers x)) {z : G} (hzE : z ∈ E)
    (hmove : x * z * x⁻¹ ∉ Subgroup.zpowers z) :
    ∃ w ∈ E, w ≠ 1 ∧ x * w * x⁻¹ = w ∧ ∀ e ∈ E, e ∉ Subgroup.zpowers w →
      ∃ n : ℕ, x ^ n * z * (x ^ n)⁻¹ ∈ Subgroup.zpowers e := by
  have hp : p.Prime := Fact.out
  have hEP : IsPGroup p E := IsPGroup.of_card hEcard
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨w₀, hw₀E, hw₀1, hw₀x⟩ := exists_fixed_ne_one hEP hEne hxE hx
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hmove (by rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _)
  have hzp : orderOf z = p := orderOf_eq_prime (hEp z hzE) hz1
  have hw₀p : orderOf w₀ = p := orderOf_eq_prime (hEp w₀ hw₀E) hw₀1
  have hxw₀ : ∀ k : ℤ, x * w₀ ^ k * x⁻¹ = w₀ ^ k := fun k => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hw₀x]
  have hzw : z ∉ Subgroup.zpowers w₀ := by
    intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    exact hmove (by rw [hxw₀ k]; exact Subgroup.mem_zpowers _)
  have hbot := zpowers_inf_zpowers_eq_bot_of_not_mem hzp hzw
  have hdec := exists_mul_eq_of_card (Subgroup.zpowers_le.mpr hzE)
    (Subgroup.zpowers_le.mpr hw₀E) hbot
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hzp, hw₀p, hEcard, sq])
  have hxzE : x * z * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxE z).mp hzE
  obtain ⟨a, ha, b, hb, hab⟩ := hdec _ hxzE
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hzwc : Commute z w₀ := hEc z hzE w₀ hw₀E
  obtain ⟨n, hn⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hzi := zpow_eq_self_of_conj hzwc hab.symm hw₀x hxn hzp hbot
  set u := w₀ ^ j with hu
  have hxz : x * z * x⁻¹ = z * u := by rw [← hab, hzi]
  have hu1 : u ≠ 1 := by
    intro h
    apply hmove
    rw [hxz, h, mul_one]
    exact Subgroup.mem_zpowers z
  have hxu : x * u * x⁻¹ = u := hxw₀ j
  have huE : u ∈ E := Subgroup.zpow_mem _ hw₀E j
  have hup : orderOf u = p := orderOf_eq_prime (hEp u huE) hu1
  have huw : Subgroup.zpowers u = Subgroup.zpowers w₀ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers w₀ j))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hup, hw₀p])
  refine ⟨u, huE, hu1, hxu, fun e heE heu => ?_⟩
  obtain ⟨a', ha', b', hb', rfl⟩ := hdec e heE
  obtain ⟨α, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
  rw [← huw] at hb'
  obtain ⟨γ, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
  have hα : ¬ (p : ℤ) ∣ α := by
    intro hdvd
    apply heu
    have : z ^ α = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hzp]; exact hdvd)
    rw [this, one_mul]
    exact Subgroup.zpow_mem_zpowers u γ
  have hαu : (α : ZMod p) ≠ 0 := fun h => hα ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  set α' : ℤ := (((α : ZMod p)⁻¹ : ZMod p).val : ℤ) with hα'
  have hαα' : ((α * α' - 1 : ℤ) : ZMod p) = 0 := by
    rw [hα']
    push_cast
    rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ hαu, sub_self]
  have hz' : z ^ (α * α') = z := by
    have h1 : z ^ (α * α' - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp
      (by rw [hzp]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hαα')
    rw [show α * α' = (α * α' - 1) + 1 by ring, zpow_add_one, h1, one_mul]
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  set m : ℕ := ((γ * α') % (p : ℤ)).toNat with hm
  have hmz : ((m : ℕ) : ℤ) = (γ * α') % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')
  have hum : u ^ m = u ^ (γ * α') := by
    rw [← zpow_natCast, hmz, ← hup]
    exact zpow_mod_orderOf u _
  refine ⟨m, ?_⟩
  rw [conj_pow_eq_mul_pow hxz hxu m, hum]
  have hcomm : Commute (z ^ α) (u ^ γ) := (hEc z hzE u huE).zpow_zpow α γ
  refine ⟨α', ?_⟩
  simp only
  rw [hcomm.mul_zpow, ← zpow_mul, ← zpow_mul, hz']

theorem exists_le_centralizer_of_moves {p : ℕ} [Fact p.Prime] {E Q : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, Commute a b) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hEcard : Nat.card E = p ^ 2) {x : G} (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (hx : IsPGroup p (Subgroup.zpowers x)) {z : G} (hzE : z ∈ E)
    (hmove : x * z * x⁻¹ ∉ Subgroup.zpowers z) (hQ : ¬ p ∣ Nat.card Q)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hCz : Q ⊓ Subgroup.centralizer ({z} : Set G) = ⊥) :
    ∃ w ∈ E, w ≠ 1 ∧ Q ≤ Subgroup.centralizer ({w} : Set G) := by
  have hp : p.Prime := Fact.out
  obtain ⟨w, hwE, hw1, -, hax⟩ := exists_axis hEc hEp hEcard hxE hx hzE hmove
  refine ⟨w, hwE, hw1, ?_⟩
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp E Q (fun e => Subtype.ext (by simpa using hEp e e.2)) hEcard hQ hEQ
  rw [hgen]
  refine iSup_le fun e => iSup_le fun he1 => ?_
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  have hep : orderOf (e : G) = p := orderOf_eq_prime (hEp e e.2) he1'
  by_cases hew : (e : G) ∈ Subgroup.zpowers w
  ·
    have hwp : orderOf w = p := orderOf_eq_prime (hEp w hwE) hw1
    have heq : Subgroup.zpowers (e : G) = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hew)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hep, hwp])
    have hwe : w ∈ Subgroup.zpowers (e : G) := heq ▸ Subgroup.mem_zpowers w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwe
    intro q hq
    have hqe : Commute q (e : G) := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    exact (hqe.zpow_right k).eq
  · obtain ⟨n, hn⟩ := hax e e.2 hew
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    intro q hq
    have hxnQ : (x ^ n)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      Subgroup.inv_mem _ (Subgroup.pow_mem _ hxQ n)
    have hq' : (x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hxnQ q).mp hq.1
    have hqe : Commute q (e : G) := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    have hqc : Commute q (x ^ n * z * (x ^ n)⁻¹) := by
      rw [← hk]
      exact hqe.zpow_right k
    have hq'' : (x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ ∈ Q ⊓ Subgroup.centralizer ({z} : Set G) := by
      refine ⟨hq', Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : q * (x ^ n * z * (x ^ n)⁻¹) = (x ^ n * z * (x ^ n)⁻¹) * q := hqc.eq
      calc (x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ * z
          = (x ^ n)⁻¹ * (q * (x ^ n * z * (x ^ n)⁻¹)) * x ^ n := by group
        _ = (x ^ n)⁻¹ * ((x ^ n * z * (x ^ n)⁻¹) * q) * x ^ n := by rw [h1]
        _ = z * ((x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹) := by group
    rw [hCz, Subgroup.mem_bot] at hq''
    have hq1 : q = 1 := by
      have : q = x ^ n * ((x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹) * (x ^ n)⁻¹ := by group
      rw [this, hq'']
      group
    rw [hq1]
    exact Subgroup.one_mem _

end CFSG.AGLEmbedding
