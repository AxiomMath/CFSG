module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Choose.Dvd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125

open Subgroup

variable {G : Type*} [Group G]

structure IsM125 (p : ℕ) (S : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  card : Nat.card S = p ^ 3
  nonab : ¬ IsMulCommutative S
  exp : ∀ s ∈ S, s ^ (p ^ 2) = 1
  big : ∃ s ∈ S, s ^ p ≠ 1

private theorem pow_mul_of_comm_aux {M : Type*} [Group M] {x y z : M} (hzy : Commute z y)
    (hyx : y * x = x * y * z) (m : ℕ) : y ^ m * x = x * y ^ m * z ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hzm : z * y ^ m = y ^ m * z := (hzy.pow_right m).eq
    calc y ^ (m + 1) * x = y * (y ^ m * x) := by rw [pow_succ', mul_assoc]
      _ = y * (x * y ^ m * z ^ m) := by rw [ih]
      _ = (y * x) * y ^ m * z ^ m := by simp only [mul_assoc]
      _ = (x * y * z) * y ^ m * z ^ m := by rw [hyx]
      _ = x * y * (z * y ^ m) * z ^ m := by simp only [mul_assoc]
      _ = x * y * (y ^ m * z) * z ^ m := by rw [hzm]
      _ = x * y ^ (m + 1) * z ^ (m + 1) := by
          rw [pow_succ' y m, pow_succ' z m]; simp only [mul_assoc]

private theorem mul_pow_of_comm {M : Type*} [Group M] {x y z : M} (hzx : Commute z x)
    (hzy : Commute z y) (hyx : y * x = x * y * z) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * z ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hC : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have hzCx : z ^ n.choose 2 * x = x * z ^ n.choose 2 := (hzx.pow_left _).eq
    have hzny : z ^ (n + n.choose 2) * y = y * z ^ (n + n.choose 2) := (hzy.pow_left _).eq
    have hyn := pow_mul_of_comm_aux hzy hyx n
    have T1 : y ^ n * z ^ n.choose 2 * x = x * y ^ n * z ^ (n + n.choose 2) := by
      calc y ^ n * z ^ n.choose 2 * x = y ^ n * (z ^ n.choose 2 * x) := mul_assoc _ _ _
        _ = y ^ n * (x * z ^ n.choose 2) := by rw [hzCx]
        _ = (y ^ n * x) * z ^ n.choose 2 := (mul_assoc _ _ _).symm
        _ = (x * y ^ n * z ^ n) * z ^ n.choose 2 := by rw [hyn]
        _ = x * y ^ n * z ^ (n + n.choose 2) := by rw [pow_add]; simp only [mul_assoc]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * (y ^ n * z ^ n.choose 2 * x) * y := by rw [ih]; simp only [mul_assoc]
      _ = x ^ n * (x * y ^ n * z ^ (n + n.choose 2)) * y := by rw [T1]
      _ = x ^ (n + 1) * (y ^ n * z ^ (n + n.choose 2) * y) := by
          rw [pow_succ]; simp only [mul_assoc]
      _ = x ^ (n + 1) * (y ^ n * (y * z ^ (n + n.choose 2))) := by
          rw [mul_assoc (y ^ n) (z ^ (n + n.choose 2)) y, hzny]
      _ = x ^ (n + 1) * (y ^ (n + 1) * z ^ (n + n.choose 2)) := by
          rw [pow_succ y n]; simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ (n + 1) * z ^ (n + 1).choose 2 := by
          rw [hC]; simp only [mul_assoc]

private theorem pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Group M] {w : M} {p : ℕ}
    (hw : w ^ p = 1) (n : ℕ) : w ^ n = w ^ (n % p) := by
  conv_lhs => rw [← Nat.mod_add_div n p]
  rw [pow_add, pow_mul, hw, one_pow, mul_one]

private theorem eq_of_pow_eq_of_not_dvd {M : Type*} [Group M] {p k : ℕ} (hp : p.Prime)
    {x y : M} (hx : x ^ p = 1) (hy : y ^ p = 1) (hk : ¬ p ∣ k) (hxy : x ^ k = y ^ k) :
    x = y := by
  have hcop : Nat.Coprime k p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hk).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hx1 : x = x ^ (k * m) := by rw [pow_eq_pow_mod_of_pow_eq_one hx, hm, pow_one]
  have hy1 : y = y ^ (k * m) := by rw [pow_eq_pow_mod_of_pow_eq_one hy, hm, pow_one]
  rw [hx1, hy1, pow_mul, pow_mul, hxy]

namespace IsM125

variable {p : ℕ} {S : Subgroup G}

private def Zs (S : Subgroup G) : Subgroup G := centralizer (S : Set G) ⊓ S

private theorem mem_Zs {S : Subgroup G} {z : G} :
    z ∈ Zs S ↔ z ∈ S ∧ ∀ s ∈ S, s * z = z * s := by
  unfold Zs
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact ⟨fun ⟨hc, hS⟩ => ⟨hS, fun s hs => hc s hs⟩, fun ⟨hS, hc⟩ => ⟨fun s hs => hc s hs, hS⟩⟩

private theorem Zs_le {S : Subgroup G} : Zs S ≤ S := fun _ hz => (mem_Zs.1 hz).1

private theorem finite_of_le (h : IsM125 p S) {H : Subgroup G} (hH : H ≤ S) : Finite H := by
  apply Nat.finite_of_card_ne_zero
  intro h0
  have hd : Nat.card H ∣ Nat.card S := Subgroup.card_dvd_of_le hH
  rw [h0, h.card] at hd
  exact pow_ne_zero 3 h.prime.ne_zero (zero_dvd_iff.mp hd)

private theorem finite_S (h : IsM125 p S) : Finite S := finite_of_le h le_rfl

private theorem eq_of_card_gt (h : IsM125 p S) {H : Subgroup G} (hH : H ≤ S)
    (hgt : p ^ 2 < Nat.card H) : H = S := by
  have hp := h.prime
  have hd : Nat.card H ∣ p ^ 3 := h.card ▸ Subgroup.card_dvd_of_le hH
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hk3 : k = 3 := by
    by_contra hne
    have hle : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  haveI := finite_S h
  exact Subgroup.eq_of_le_of_card_ge hH (le_of_eq (by rw [h.card, hk', hk3]))

private theorem card_Zs (h : IsM125 p S) : Nat.card (Zs S) = p := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Zs S) := finite_of_le h Zs_le
  haveI : Finite S := finite_S h
  have hd : Nat.card (Zs S) ∣ p ^ 3 := h.card ▸ Subgroup.card_dvd_of_le Zs_le
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hSp : IsPGroup p S := IsPGroup.of_card h.card
  haveI : Nontrivial S := (IsPGroup.nontrivial_iff_card hSp).2 ⟨3, by norm_num, h.card⟩
  haveI : Nontrivial (Subgroup.center S) := IsPGroup.center_nontrivial hSp
  have hZbot : Zs S ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (1 : Subgroup.center S)
    intro hbot
    apply hx
    have hxZ : (x.1 : G) ∈ Zs S := mem_Zs.2 ⟨x.1.2, fun s hs => by
      have := Subgroup.mem_center_iff.1 x.2 ⟨s, hs⟩
      simpa using congrArg Subtype.val this⟩
    rw [hbot, Subgroup.mem_bot] at hxZ
    exact Subtype.ext (Subtype.ext hxZ)
  have h1 : 1 < Nat.card (Zs S) := (Subgroup.one_lt_card_iff_ne_bot (Zs S)).2 hZbot
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp [hk'] at h1
  have hk3 : k ≠ 3 := by
    rintro rfl
    have hZS' : Zs S = S := eq_of_card_gt h Zs_le (by
      rw [hk']; exact Nat.pow_lt_pow_right hp.one_lt (by norm_num))
    apply h.nonab
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hb : (b : G) ∈ Zs S := by rw [hZS']; exact b.2
    exact (mem_Zs.1 hb).2 a a.2
  have hk2 : k ≠ 2 := by
    rintro rfl
    obtain ⟨x, hxS, hxZ⟩ : ∃ x ∈ S, x ∉ Zs S := by
      by_contra hcon
      push Not at hcon
      have hEq : Zs S = S := le_antisymm Zs_le (fun x hx => hcon x hx)
      have h3 : Nat.card (Zs S) = Nat.card S := by rw [hEq]
      rw [h.card, hk'] at h3
      have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num)
      omega
    obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = centralizer ({x} : Set G) ⊓ S := ⟨_, rfl⟩
    have hCS : C ≤ S := by rw [hC]; exact inf_le_right
    have hxC : x ∈ C := by
      rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      exact ⟨fun g hg => by rw [Set.mem_singleton_iff] at hg; rw [hg], hxS⟩
    have hZC : Zs S ≤ C := by
      intro z hz
      obtain ⟨hzS, hzc⟩ := mem_Zs.1 hz
      rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      exact ⟨fun g hg => by rw [Set.mem_singleton_iff] at hg; rw [hg]; exact hzc x hxS, hzS⟩
    have hne : Zs S ≠ C := fun heq => hxZ (by rw [heq]; exact hxC)
    haveI : Finite C := finite_of_le h hCS
    have hlt : Nat.card (Zs S) < Nat.card C := Subgroup.card_lt_of_lt (lt_of_le_of_ne hZC hne)
    have hCeq : C = S := eq_of_card_gt h hCS (by rw [hk'] at hlt; exact hlt)
    apply hxZ
    refine mem_Zs.2 ⟨hxS, fun s hs => ?_⟩
    have hsC : s ∈ C := by rw [hCeq]; exact hs
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hsC
    exact (hsC.1 x (Set.mem_singleton x)).symm
  rw [hk']
  have hk1 : k = 1 := by omega
  rw [hk1, pow_one]

private theorem pow_eq_one_of_mem_Zs (h : IsM125 p S) {z : G} (hz : z ∈ Zs S) : z ^ p = 1 := by
  have hc := card_Zs h
  have := pow_card_eq_one' (G := ↥(Zs S)) (x := ⟨z, hz⟩)
  rw [hc] at this
  simpa using congrArg Subtype.val this

private theorem commutator_mem_Zs (h : IsM125 p S) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    s * t * s⁻¹ * t⁻¹ ∈ Zs S := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Zs S) := finite_of_le h Zs_le
  obtain ⟨N, hN⟩ : ∃ N : Subgroup S, N = (Zs S).subgroupOf S := ⟨_, rfl⟩
  have hNnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * (n : G) = (n : G) * (g : G) := (mem_Zs.1 hn).2 g g.2
    have e : ((g * n * g⁻¹ : S) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hn
  have hNcard : Nat.card N = p := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Zs_le).toEquiv, card_Zs h]
  have hQcard : Nat.card (S ⧸ N) = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h.card, hNcard] at h1
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    rw [h3] at h1
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h1).symm
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQcard
  have hst : (QuotientGroup.mk (⟨s, hs⟩ : S) : S ⧸ N) * QuotientGroup.mk (⟨t, ht⟩ : S)
      = QuotientGroup.mk (⟨t, ht⟩ : S) * QuotientGroup.mk (⟨s, hs⟩ : S) :=
    hcomm.is_comm.comm _ _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hst
  have hu : (⟨s, hs⟩ * ⟨t, ht⟩ : S)⁻¹ * (⟨t, ht⟩ * ⟨s, hs⟩) ∈ N := QuotientGroup.eq.1 hst
  have hu' : (s * t)⁻¹ * (t * s) ∈ Zs S := by
    rw [hN, Subgroup.mem_subgroupOf] at hu
    simpa using hu
  obtain ⟨c, hc⟩ : ∃ c : G, c = (s * t)⁻¹ * (t * s) := ⟨_, rfl⟩
  rw [← hc] at hu'
  have hcc : Commute (s * t) c := (mem_Zs.1 hu').2 (s * t) (S.mul_mem hs ht)
  have hts : t * s = s * t * c := by rw [hc]; group
  have key : s * t * s⁻¹ * t⁻¹ = c⁻¹ := by
    calc s * t * s⁻¹ * t⁻¹ = (s * t) * (t * s)⁻¹ := by group
      _ = (s * t) * (s * t * c)⁻¹ := by rw [hts]
      _ = (s * t) * (c⁻¹ * (s * t)⁻¹) := by rw [mul_inv_rev (s * t) c]
      _ = ((s * t) * c⁻¹) * (s * t)⁻¹ := by group
      _ = (c⁻¹ * (s * t)) * (s * t)⁻¹ := by rw [hcc.inv_right.eq]
      _ = c⁻¹ := by group
  rw [key]
  exact (Zs S).inv_mem hu'

private theorem pow_mem_Zs (h : IsM125 p S) {s : G} (hs : s ∈ S) : s ^ p ∈ Zs S := by
  refine mem_Zs.2 ⟨S.pow_mem hs p, fun t ht => ?_⟩
  have hw : s⁻¹ * t * s * t⁻¹ ∈ Zs S := by
    have := commutator_mem_Zs h (S.inv_mem hs) ht
    simpa only [inv_inv] using this
  have hts : t * s * t⁻¹ = s * (s⁻¹ * t * s * t⁻¹) := by group
  have hcomm : Commute s (s⁻¹ * t * s * t⁻¹) := (mem_Zs.1 hw).2 s hs
  have h1 : (t * s * t⁻¹) ^ p = s ^ p * (s⁻¹ * t * s * t⁻¹) ^ p := by
    rw [hts, hcomm.mul_pow]
  rw [conj_pow, pow_eq_one_of_mem_Zs h hw, mul_one] at h1
  calc t * s ^ p = (t * s ^ p * t⁻¹) * t := by group
    _ = s ^ p * t := by rw [h1]

theorem card_Z (h : IsM125 p S) : Nat.card ↥(centralizer (S : Set G) ⊓ S) = p :=
  card_Zs h

theorem commutator_mem_Z (h : IsM125 p S) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    s * t * s⁻¹ * t⁻¹ ∈ centralizer (S : Set G) ⊓ S :=
  commutator_mem_Zs h hs ht

theorem mul_pow (h : IsM125 p S) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    (s * t) ^ p = s ^ p * t ^ p := by
  have hp := h.prime
  have hz : (s * t)⁻¹ * (t * s) ∈ Zs S := by
    have := commutator_mem_Zs h (S.inv_mem ht) (S.inv_mem hs)
    simp only [inv_inv] at this
    convert this using 1
    group
  have hzs : Commute ((s * t)⁻¹ * (t * s)) s := ((mem_Zs.1 hz).2 s hs).symm
  have hzt : Commute ((s * t)⁻¹ * (t * s)) t := ((mem_Zs.1 hz).2 t ht).symm
  have hyx : t * s = s * t * ((s * t)⁻¹ * (t * s)) := by group
  rw [mul_pow_of_comm hzs hzt hyx p]
  have h2p : 2 < p := by
    have := hp.two_le
    have := h.odd
    omega
  obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self (k := 2) hp (by norm_num) h2p
  rw [hc, pow_mul, pow_eq_one_of_mem_Zs h hz, one_pow, mul_one]

def E (h : IsM125 p S) : Subgroup G where
  carrier := {s | s ∈ S ∧ s ^ p = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨S.mul_mem ha hb, by rw [h.mul_pow ha hb, ha', hb', one_mul]⟩
  one_mem' := ⟨S.one_mem, one_pow p⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨S.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩

theorem mem_E (h : IsM125 p S) {s : G} : s ∈ h.E ↔ s ∈ S ∧ s ^ p = 1 := Iff.rfl

theorem E_le (h : IsM125 p S) : h.E ≤ S := fun _ hs => hs.1

private theorem Zs_le_E (h : IsM125 p S) : Zs S ≤ h.E :=
  fun z hz => ⟨(mem_Zs.1 hz).1, pow_eq_one_of_mem_Zs h hz⟩

private theorem card_eq_of_le_Zs (h : IsM125 p S) {H : Subgroup G} (hH : H ≤ Zs S)
    (hne : H ≠ ⊥) : Nat.card H = p := by
  have hd : Nat.card H ∣ p := by
    have := Subgroup.card_dvd_of_le hH
    rwa [card_Zs h] at this
  haveI : Finite H := finite_of_le h (hH.trans Zs_le)
  rcases Nat.Prime.eq_one_or_self_of_dvd h.prime _ hd with h1 | h1
  · exact absurd ((Subgroup.card_le_one_iff_eq_bot H).1 h1.le) hne
  · exact h1

theorem card_E (h : IsM125 p S) : Nat.card h.E = p ^ 2 := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : S →* G := MonoidHom.mk' (fun x : S => (x : G) ^ p) (fun x y => h.mul_pow x.2 y.2)
  have hφ : ∀ x : S, φ x = (x : G) ^ p := fun x => rfl
  have hker : φ.ker = h.E.subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, mem_E]
    exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
  have hrange_le : φ.range ≤ Zs S := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [hφ]
    exact pow_mem_Zs h x.2
  have hrange_ne : φ.range ≠ ⊥ := by
    obtain ⟨s, hs, hsp⟩ := h.big
    intro hbot
    have hmem : s ^ p ∈ φ.range := MonoidHom.mem_range.2 ⟨⟨s, hs⟩, hφ ⟨s, hs⟩⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hsp hmem
  have hrange : Nat.card φ.range = p := card_eq_of_le_Zs h hrange_le hrange_ne
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, h.card] at h1
  have hk2 : Nat.card φ.ker = p ^ 2 := by
    have h3 : p ^ 3 = p * p ^ 2 := by ring
    rw [h3] at h1
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h1).symm
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E_le h)).toEquiv, ← hker]
  exact hk2

private theorem exists_mem_not_E (h : IsM125 p S) : ∃ a ∈ S, a ∉ h.E := by
  by_contra hcon
  push Not at hcon
  have hEq : h.E = S := le_antisymm (E_le h) (fun a ha => hcon a ha)
  have h1 := card_E h
  rw [hEq, h.card] at h1
  have := Nat.pow_lt_pow_right h.prime.one_lt (show 2 < 3 by norm_num)
  omega

private theorem exists_mem_E_not_Z (h : IsM125 p S) : ∃ e ∈ h.E, e ∉ Zs S := by
  by_contra hcon
  push Not at hcon
  have hle : h.E ≤ Zs S := fun e he => hcon e he
  haveI : Finite (Zs S) := finite_of_le h Zs_le
  have h1 : Nat.card h.E ≤ Nat.card (Zs S) := Subgroup.card_le_of_le hle
  rw [card_E h, card_Zs h] at h1
  have := Nat.pow_lt_pow_right h.prime.one_lt (show 1 < 2 by norm_num)
  rw [pow_one] at this
  omega

theorem Z_le_E (h : IsM125 p S) : centralizer (S : Set G) ⊓ S ≤ h.E :=
  Zs_le_E h

theorem E_comm (h : IsM125 p S) {a b : G} (ha : a ∈ h.E) (hb : b ∈ h.E) : a * b = b * a := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hc : IsMulCommutative h.E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (card_E h)
  have h2 : (⟨a, ha⟩ : h.E) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := hc.is_comm.comm _ _
  exact congrArg Subtype.val h2

theorem mem_E_of_commute (h : IsM125 p S) {e s : G} (he : e ∈ h.E)
    (heZ : e ∉ centralizer (S : Set G)) (hs : s ∈ S) (hc : s * e = e * s) : s ∈ h.E := by
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = centralizer ({e} : Set G) ⊓ S := ⟨_, rfl⟩
  have hCS : C ≤ S := by rw [hC]; exact inf_le_right
  have hEC : h.E ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨fun g hg => ?_, hx.1⟩
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact E_comm h he hx
  have hsC : s ∈ C := by
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨fun g hg => ?_, hs⟩
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hc.symm
  have hCne : C ≠ S := by
    intro hCS'
    apply heZ
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgC : g ∈ C := by rw [hCS']; exact hg
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hgC
    exact (hgC.1 e (Set.mem_singleton e)).symm
  have hCcard : Nat.card C ≤ p ^ 2 := by
    by_contra hlt
    push Not at hlt
    exact hCne (eq_of_card_gt h hCS hlt)
  haveI : Finite C := finite_of_le h hCS
  have hEC' : h.E = C := Subgroup.eq_of_le_of_card_ge hEC (by rw [card_E h]; exact hCcard)
  rw [hEC']
  exact hsC

theorem eq_E (h : IsM125 p S) {A : Subgroup G} (hA : A ≤ S) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hcard : Nat.card A = p ^ 2) : A = h.E := by
  have hAE : A ≤ h.E := fun a ha => ⟨hA ha, hAp a ha⟩
  haveI : Finite h.E := finite_of_le h (E_le h)
  exact Subgroup.eq_of_le_of_card_ge hAE (le_of_eq (by rw [card_E h, hcard]))

private theorem comm_mul_hom (h : IsM125 p S) {g x y : G} (hg : g ∈ S) (hx : x ∈ S)
    (hy : y ∈ S) : g * (x * y) * g⁻¹ * (x * y)⁻¹ = (g * x * g⁻¹ * x⁻¹) * (g * y * g⁻¹ * y⁻¹) := by
  have hw : g * y * g⁻¹ * y⁻¹ ∈ Zs S := commutator_mem_Zs h hg hy
  have hwx : x * (g * y * g⁻¹ * y⁻¹) = (g * y * g⁻¹ * y⁻¹) * x := (mem_Zs.1 hw).2 x hx
  calc g * (x * y) * g⁻¹ * (x * y)⁻¹
      = (g * x * g⁻¹ * x⁻¹) * (x * (g * y * g⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = (g * x * g⁻¹ * x⁻¹) * ((g * y * g⁻¹ * y⁻¹) * x * x⁻¹) := by rw [hwx]
    _ = (g * x * g⁻¹ * x⁻¹) * (g * y * g⁻¹ * y⁻¹) := by group

private theorem comm_pow_hom (h : IsM125 p S) {g x : G} (hg : g ∈ S) (hx : x ∈ S) (j : ℕ) :
    g * x ^ j * g⁻¹ * (x ^ j)⁻¹ = (g * x * g⁻¹ * x⁻¹) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hxj : x ^ j ∈ S := S.pow_mem hx j
    have e1 : x ^ (j + 1) = x ^ j * x := pow_succ x j
    rw [e1, comm_mul_hom h hg hxj hx, ih, pow_succ]

private theorem exists_pow_eq_of_mem_Zs (h : IsM125 p S) {w z : G} (hw : w ∈ Zs S)
    (hw1 : w ≠ 1) (hz : z ∈ Zs S) : ∃ m : ℕ, z = w ^ m := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf w = p := orderOf_eq_prime (pow_eq_one_of_mem_Zs h hw) hw1
  have hle : Subgroup.zpowers w ≤ Zs S := Subgroup.zpowers_le.2 hw
  haveI : Finite (Zs S) := finite_of_le h Zs_le
  have hcard : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hord]
  have heq : Subgroup.zpowers w = Zs S :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard, card_Zs h]))
  have hz' : z ∈ Subgroup.zpowers w := by rw [heq]; exact hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz'
  have hne : (orderOf w : ℤ) ≠ 0 := by
    rw [hord]
    exact_mod_cast hp.ne_zero
  have hnn : 0 ≤ k % (orderOf w : ℤ) := Int.emod_nonneg _ hne
  refine ⟨(k % (orderOf w : ℤ)).toNat, ?_⟩
  rw [← hk, ← zpow_mod_orderOf, ← zpow_natCast, Int.toNat_of_nonneg hnn]

private theorem comm_ne_one (h : IsM125 p S) {a b : G} (haS : a ∈ S) (haE : a ∉ h.E)
    (hbE : b ∈ h.E) (hbZ : b ∉ Zs S) : b * a * b⁻¹ * a⁻¹ ≠ 1 := by
  intro h1
  have hbS : b ∈ S := hbE.1
  have hab : b * a = a * b := by
    calc b * a = b * a * b⁻¹ * a⁻¹ * (a * b) := by group
      _ = a * b := by rw [h1, one_mul]
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = centralizer ({b} : Set G) ⊓ S := ⟨_, rfl⟩
  have hCS : C ≤ S := by rw [hC]; exact inf_le_right
  have hEC : h.E ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨fun g hg => ?_, hx.1⟩
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact E_comm h hbE hx
  have haC : a ∈ C := by
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨fun g hg => ?_, haS⟩
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hab
  haveI : Finite C := finite_of_le h hCS
  have hgt : p ^ 2 < Nat.card C := by
    by_contra hle
    push Not at hle
    have heq : h.E = C := Subgroup.eq_of_le_of_card_ge hEC (by rw [card_E h]; exact hle)
    apply haE
    rw [heq]
    exact haC
  have hCeq : C = S := eq_of_card_gt h hCS hgt
  apply hbZ
  refine mem_Zs.2 ⟨hbS, fun s hs => ?_⟩
  have hsC : s ∈ C := by rw [hCeq]; exact hs
  rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hsC
  exact (hsC.1 b (Set.mem_singleton b)).symm

private theorem decomp_of_ne (h : IsM125 p S) {a b : G} (haS : a ∈ S) (haE : a ∉ h.E)
    (hbE : b ∈ h.E) (hbZ : b ∉ Zs S) {x : G} (hx : x ∈ S) :
    ∃ j : ℕ, ∃ e ∈ h.E, x = a ^ j * e := by
  have hbS : b ∈ S := hbE.1
  have hz0 : b * a * b⁻¹ * a⁻¹ ≠ 1 := comm_ne_one h haS haE hbE hbZ
  have hz0Z : b * a * b⁻¹ * a⁻¹ ∈ Zs S := commutator_mem_Zs h hbS haS
  have hcx : b * x * b⁻¹ * x⁻¹ ∈ Zs S := commutator_mem_Zs h hbS hx
  obtain ⟨j, hj⟩ := exists_pow_eq_of_mem_Zs h hz0Z hz0 hcx
  obtain ⟨x', hx'⟩ : ∃ x' : G, x' = (a ^ j)⁻¹ * x := ⟨_, rfl⟩
  have hx'S : x' ∈ S := by rw [hx']; exact S.mul_mem (S.inv_mem (S.pow_mem haS j)) hx
  have hx_eq : a ^ j * x' = x := by rw [hx']; group
  have hmul := comm_mul_hom h hbS (S.pow_mem haS j) hx'S
  rw [hx_eq, comm_pow_hom h hbS haS j, hj] at hmul
  have hd1 : b * x' * b⁻¹ * x'⁻¹ = 1 :=
    mul_left_cancel (a := (b * a * b⁻¹ * a⁻¹) ^ j) (by rw [mul_one]; exact hmul.symm)
  have hcomm : x' * b = b * x' := by
    have hbx : b * x' = x' * b := by
      calc b * x' = (b * x' * b⁻¹ * x'⁻¹) * (x' * b) := by group
        _ = x' * b := by rw [hd1, one_mul]
    exact hbx.symm
  have hbZ' : b ∉ centralizer (S : Set G) := fun hb =>
    hbZ (mem_Zs.2 ⟨hbS, fun s hs => (Subgroup.mem_centralizer_iff.1 hb) s hs⟩)
  exact ⟨j, x', mem_E_of_commute h hbE hbZ' hx'S hcomm, hx_eq.symm⟩

private theorem P_mul {n x y : G} (hxS : x ∈ S) (hPx : n * x * n⁻¹ * x⁻¹ ∈ Zs S)
    (hPy : n * y * n⁻¹ * y⁻¹ ∈ Zs S) : n * (x * y) * n⁻¹ * (x * y)⁻¹ ∈ Zs S := by
  have hw : x * (n * y * n⁻¹ * y⁻¹) = (n * y * n⁻¹ * y⁻¹) * x := (mem_Zs.1 hPy).2 x hxS
  have e : n * (x * y) * n⁻¹ * (x * y)⁻¹ = (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) := by
    calc n * (x * y) * n⁻¹ * (x * y)⁻¹
        = (n * x * n⁻¹ * x⁻¹) * (x * (n * y * n⁻¹ * y⁻¹) * x⁻¹) := by group
      _ = (n * x * n⁻¹ * x⁻¹) * ((n * y * n⁻¹ * y⁻¹) * x * x⁻¹) := by rw [hw]
      _ = (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) := by group
  rw [e]
  exact (Zs S).mul_mem hPx hPy

private theorem P_inv {n x : G} (hxS : x ∈ S) (hPx : n * x * n⁻¹ * x⁻¹ ∈ Zs S) :
    n * x⁻¹ * n⁻¹ * x⁻¹⁻¹ ∈ Zs S := by
  have hc : x⁻¹ * (n * x * n⁻¹ * x⁻¹)⁻¹ = (n * x * n⁻¹ * x⁻¹)⁻¹ * x⁻¹ :=
    (Commute.inv_inv (show Commute x (n * x * n⁻¹ * x⁻¹) from (mem_Zs.1 hPx).2 x hxS)).eq
  have e : n * x⁻¹ * n⁻¹ * x⁻¹⁻¹ = x⁻¹ * (n * x * n⁻¹ * x⁻¹)⁻¹ * x := by group
  have e2 : x⁻¹ * (n * x * n⁻¹ * x⁻¹)⁻¹ * x = (n * x * n⁻¹ * x⁻¹)⁻¹ := by
    rw [hc]
    group
  rw [e, e2]
  exact (Zs S).inv_mem hPx

theorem conj_mul_inv_mem_Z (h : IsM125 p S) {n : G} (hn : n ∈ normalizer (S : Set G)) {e : G}
    (he : e ∈ h.E) : n * e * n⁻¹ * e⁻¹ ∈ centralizer (S : Set G) ⊓ S := by
  show n * e * n⁻¹ * e⁻¹ ∈ Zs S
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hnS : ∀ x ∈ S, n * x * n⁻¹ ∈ S := fun x hx => (mem_set_normalizer_iff.1 hn x).1 hx
  have hnS' : ∀ x ∈ S, n⁻¹ * x * n ∈ S := by
    intro x hx
    have := (mem_set_normalizer_iff.1 (inv_mem hn) x).1 hx
    rwa [inv_inv] at this
  have hZn : ∀ z ∈ Zs S, n * z * n⁻¹ ∈ Zs S := by
    intro z hz
    obtain ⟨hzS, hzc⟩ := mem_Zs.1 hz
    refine mem_Zs.2 ⟨hnS z hzS, fun s hs => ?_⟩
    have hc := hzc _ (hnS' s hs)
    calc s * (n * z * n⁻¹) = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by rw [hc]
      _ = n * z * n⁻¹ * s := by group
  have hEn : ∀ x ∈ h.E, n * x * n⁻¹ ∈ h.E := by
    intro x hx
    refine ⟨hnS x hx.1, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  have hPZ : ∀ z ∈ Zs S, n * z * n⁻¹ * z⁻¹ ∈ Zs S := fun z hz =>
    (Zs S).mul_mem (hZn z hz) ((Zs S).inv_mem hz)
  obtain ⟨a, haS, haE⟩ := exists_mem_not_E h
  obtain ⟨b, hbE, hbZ⟩ := exists_mem_E_not_Z h
  have hbS : b ∈ S := hbE.1
  have hz₁Z : a ^ p ∈ Zs S := pow_mem_Zs h haS
  have hz₁ne : a ^ p ≠ 1 := fun h1 => haE ⟨haS, h1⟩
  have hz₁ord : orderOf (a ^ p) = p := orderOf_eq_prime (pow_eq_one_of_mem_Zs h hz₁Z) hz₁ne
  obtain ⟨lam, hlam⟩ := exists_pow_eq_of_mem_Zs h hz₁Z hz₁ne (hZn _ hz₁Z)
  have hlam_nd : ¬ p ∣ lam := by
    rintro ⟨c, hc⟩
    have h1 : n * a ^ p * n⁻¹ = 1 := by
      rw [hlam, hc, pow_mul, pow_eq_one_of_mem_Zs h hz₁Z, one_pow]
    apply hz₁ne
    calc a ^ p = n⁻¹ * (n * a ^ p * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hz0 : b * a * b⁻¹ * a⁻¹ ≠ 1 := comm_ne_one h haS haE hbE hbZ
  have hz0Z : b * a * b⁻¹ * a⁻¹ ∈ Zs S := commutator_mem_Zs h hbS haS
  obtain ⟨m, hm⟩ := exists_pow_eq_of_mem_Zs h hz₁Z hz₁ne hz0Z
  have hθz0 : n * (b * a * b⁻¹ * a⁻¹) * n⁻¹ = (b * a * b⁻¹ * a⁻¹) ^ lam := by
    rw [hm, ← conj_pow, hlam]
    exact pow_right_comm _ _ _
  obtain ⟨j, e₁, he₁, hθa⟩ := decomp_of_ne h haS haE hbE hbZ (hnS a haS)
  have hjlam : j % p = lam % p := by
    have e1 : (n * a * n⁻¹) ^ p = (a ^ p) ^ j := by
      rw [hθa, h.mul_pow (S.pow_mem haS j) he₁.1, he₁.2, mul_one, pow_right_comm]
    have h1 : (a ^ p) ^ j = (a ^ p) ^ lam := by
      rw [← e1, conj_pow, hlam]
    have h2 := pow_eq_pow_iff_modEq.1 h1
    rw [hz₁ord] at h2
    exact h2
  obtain ⟨β, hβdef⟩ : ∃ β : G, β = n * b * n⁻¹ := ⟨_, rfl⟩
  have hβE : β ∈ h.E := by rw [hβdef]; exact hEn b hbE
  have hβS : β ∈ S := hβE.1
  have hu_Z : β * a * β⁻¹ * a⁻¹ ∈ Zs S := commutator_mem_Zs h hβS haS
  have e2 : β * e₁ * β⁻¹ * e₁⁻¹ = 1 := by
    rw [E_comm h hβE he₁]
    group
  have hkey : (β * a * β⁻¹ * a⁻¹) ^ j = (b * a * b⁻¹ * a⁻¹) ^ lam := by
    calc (β * a * β⁻¹ * a⁻¹) ^ j = β * a ^ j * β⁻¹ * (a ^ j)⁻¹ :=
          (comm_pow_hom h hβS haS j).symm
      _ = β * a ^ j * β⁻¹ * (a ^ j)⁻¹ * (β * e₁ * β⁻¹ * e₁⁻¹) := by rw [e2, mul_one]
      _ = β * (a ^ j * e₁) * β⁻¹ * (a ^ j * e₁)⁻¹ :=
          (comm_mul_hom h hβS (S.pow_mem haS j) he₁.1).symm
      _ = β * (n * a * n⁻¹) * β⁻¹ * (n * a * n⁻¹)⁻¹ := by rw [hθa]
      _ = n * (b * a * b⁻¹ * a⁻¹) * n⁻¹ := by rw [hβdef]; group
      _ = (b * a * b⁻¹ * a⁻¹) ^ lam := hθz0
  have hu_pow : (β * a * β⁻¹ * a⁻¹) ^ j = (β * a * β⁻¹ * a⁻¹) ^ lam := by
    rw [pow_eq_pow_mod_of_pow_eq_one (pow_eq_one_of_mem_Zs h hu_Z) j,
      pow_eq_pow_mod_of_pow_eq_one (pow_eq_one_of_mem_Zs h hu_Z) lam, hjlam]
  have huz : β * a * β⁻¹ * a⁻¹ = b * a * b⁻¹ * a⁻¹ :=
    eq_of_pow_eq_of_not_dvd hp (pow_eq_one_of_mem_Zs h hu_Z) (pow_eq_one_of_mem_Zs h hz0Z)
      hlam_nd (hu_pow.symm.trans hkey)
  have hga : (b⁻¹ * β) * a = a * (b⁻¹ * β) := by
    have hβa : β * a * β⁻¹ = b * a * b⁻¹ := by
      calc β * a * β⁻¹ = β * a * β⁻¹ * a⁻¹ * a := by group
        _ = b * a * b⁻¹ * a⁻¹ * a := by rw [huz]
        _ = b * a * b⁻¹ := by group
    calc (b⁻¹ * β) * a = b⁻¹ * (β * a * β⁻¹) * β := by group
      _ = b⁻¹ * (b * a * b⁻¹) * β := by rw [hβa]
      _ = a * (b⁻¹ * β) := by group
  have hgE : b⁻¹ * β ∈ h.E := h.E.mul_mem (h.E.inv_mem hbE) hβE
  have hgZ : b⁻¹ * β ∈ Zs S := by
    refine mem_Zs.2 ⟨hgE.1, fun x hx => ?_⟩
    obtain ⟨k, e', he', rfl⟩ := decomp_of_ne h haS haE hbE hbZ hx
    have hcag : Commute (a ^ k) (b⁻¹ * β) := Commute.pow_left hga.symm k
    have hE' : e' * (b⁻¹ * β) = (b⁻¹ * β) * e' := E_comm h he' hgE
    calc a ^ k * e' * (b⁻¹ * β) = a ^ k * (e' * (b⁻¹ * β)) := mul_assoc _ _ _
      _ = a ^ k * ((b⁻¹ * β) * e') := by rw [hE']
      _ = (a ^ k * (b⁻¹ * β)) * e' := (mul_assoc _ _ _).symm
      _ = ((b⁻¹ * β) * a ^ k) * e' := by rw [hcag.eq]
      _ = (b⁻¹ * β) * (a ^ k * e') := mul_assoc _ _ _
  have hPb : n * b * n⁻¹ * b⁻¹ ∈ Zs S := by
    have hbg := (mem_Zs.1 hgZ).2 b hbS
    have e : n * b * n⁻¹ * b⁻¹ = b⁻¹ * β := by
      calc n * b * n⁻¹ * b⁻¹ = β * b⁻¹ := by rw [hβdef]
        _ = (b * (b⁻¹ * β)) * b⁻¹ := by group
        _ = ((b⁻¹ * β) * b) * b⁻¹ := by rw [hbg]
        _ = b⁻¹ * β := by group
    rw [e]
    exact hgZ
  obtain ⟨H', hH'⟩ : ∃ H' : Subgroup G,
      ∀ x, x ∈ H' ↔ (x ∈ h.E ∧ n * x * n⁻¹ * x⁻¹ ∈ Zs S) := by
    refine ⟨{ carrier := {x | x ∈ h.E ∧ n * x * n⁻¹ * x⁻¹ ∈ Zs S}
              mul_mem' := fun {x y} hx hy => ⟨h.E.mul_mem hx.1 hy.1, P_mul hx.1.1 hx.2 hy.2⟩
              one_mem' := ⟨h.E.one_mem, by simpa using (Zs S).one_mem⟩
              inv_mem' := fun {x} hx => ⟨h.E.inv_mem hx.1, P_inv hx.1.1 hx.2⟩ }, fun x => Iff.rfl⟩
  have hbH' : b ∈ H' := (hH' b).2 ⟨hbE, hPb⟩
  have hZH' : Zs S ≤ H' := fun z hz => (hH' z).2 ⟨Zs_le_E h hz, hPZ z hz⟩
  have hK : Subgroup.zpowers b ⊔ Zs S ≤ H' := sup_le (Subgroup.zpowers_le.2 hbH') hZH'
  have hKE : Subgroup.zpowers b ⊔ Zs S = h.E := by
    obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = Subgroup.zpowers b ⊔ Zs S := ⟨_, rfl⟩
    rw [← hK]
    have hKE_le : K ≤ h.E := by
      rw [hK]
      exact sup_le (Subgroup.zpowers_le.2 hbE) (Zs_le_E h)
    haveI : Finite K := finite_of_le h (hKE_le.trans (E_le h))
    have hZK : Zs S < K := by
      refine lt_of_le_of_ne (by rw [hK]; exact le_sup_right) ?_
      intro heq
      apply hbZ
      have hbK : b ∈ K := by rw [hK]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
      rw [← heq] at hbK
      exact hbK
    have hlt : Nat.card (Zs S) < Nat.card K := Subgroup.card_lt_of_lt hZK
    rw [card_Zs h] at hlt
    have hd : Nat.card K ∣ p ^ 2 := by
      rw [← card_E h]
      exact Subgroup.card_dvd_of_le hKE_le
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hd
    have hk2 : k = 2 := by
      by_contra hne
      have hle : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      rw [pow_one] at hle
      omega
    haveI : Finite h.E := finite_of_le h (E_le h)
    exact Subgroup.eq_of_le_of_card_ge hKE_le (le_of_eq (by rw [card_E h, hk', hk2]))
  have heK : e ∈ Subgroup.zpowers b ⊔ Zs S := by
    rw [hKE]
    exact he
  exact ((hH' e).1 (hK heK)).2

end IsM125

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125
