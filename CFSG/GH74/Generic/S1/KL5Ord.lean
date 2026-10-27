module

public import CFSG.GH74.Generic.S1.KL5Cfg
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.Generic.S1

theorem kl5_card_mul_gcd_psl {X : Type} [Group X] {p f n : ℕ} (hn : 2 ≤ n)
    (hX : StatedClassicalModel X .PSL n p f) :
    Nat.card X * Nat.gcd n (p ^ f - 1) =
      (p ^ f) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, ((p ^ f) ^ j - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega), hK]
  apply Nat.div_mul_cancel
  refine Dvd.dvd.mul_left ?_ _
  exact ((Nat.gcd_dvd_right n (p ^ f - 1)).trans
    (Nat.sub_one_dvd_pow_sub_one (p ^ f) 2)).trans
    (Finset.dvd_prod_of_mem (fun j => (p ^ f) ^ j - 1) (Finset.mem_Icc.2 ⟨le_rfl, hn⟩))

theorem kl5_card_mul_gcd_psu_three {X : Type} [Group X] {p f : ℕ}
    (hX : StatedClassicalModel X .PSU 3 p f) :
    Nat.card X * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : ((((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2)).toNat = (p ^ f) ^ 2 - 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hq2]
      ring, Int.toNat_natCast]
  have h3 : ((((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3)).toNat = (p ^ f) ^ 3 + 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) by
      push_cast
      ring, Int.toNat_natCast]
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num),
    show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), h2, h3]
  apply Nat.div_mul_cancel
  have hd : p ^ f + 1 ∣ (p ^ f) ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (p ^ f) 1 (n := 3) (by decide)
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 _).trans hd) _) _

theorem kl5_coprime_self_sub_one {q : ℕ} (hq : 1 ≤ q) : Nat.Coprime q (q - 1) := by
  have h1 : Nat.Coprime (q - 1) (q - 1 + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rw [Nat.sub_add_cancel hq] at h1
  exact h1.symm

theorem kl5_pow_dvd_card_psl {X : Type} [Group X] {p f n : ℕ} (hn : 2 ≤ n)
    (hX : StatedClassicalModel X .PSL n p f) :
    (p ^ f) ^ (n * (n - 1) / 2) ∣ Nat.card X := by
  have h := kl5_card_mul_gcd_psl hn hX
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hX.1.1.pos
  have hcop : Nat.Coprime ((p ^ f) ^ (n * (n - 1) / 2)) (Nat.gcd n (p ^ f - 1)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right n _)
      (kl5_coprime_self_sub_one hq))
  exact hcop.dvd_of_dvd_mul_right (h ▸ Dvd.intro _ rfl)

theorem kl5_cube_dvd_card_psu {X : Type} [Group X] {p f : ℕ}
    (hX : StatedClassicalModel X .PSU 3 p f) : (p ^ f) ^ 3 ∣ Nat.card X := by
  have h := kl5_card_mul_gcd_psu_three hX
  have hcop : Nat.Coprime ((p ^ f) ^ 3) (Nat.gcd 3 (p ^ f + 1)) :=
    Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _)
      (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)))
  exact hcop.dvd_of_dvd_mul_right (h ▸ Dvd.intro _ rfl)

theorem kl5_eight_dvd_sq_sub_one {q : ℕ} (hq : q % 2 = 1) : 8 ∣ q ^ 2 - 1 := by
  have h8 : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  have : q ^ 2 % 8 = 1 := by
    rcases h8 with h | h | h | h <;> simp [Nat.pow_mod, h]
  omega

theorem kl5_two_dvd_pow_sub_one {q : ℕ} (hq : q % 2 = 1) (n : ℕ) : 2 ∣ q ^ n - 1 := by
  have : q ^ n % 2 = 1 := by simp [Nat.pow_mod, hq]
  omega

theorem kl5_two_dvd_pow_add_one {q : ℕ} (hq : q % 2 = 1) (n : ℕ) : 2 ∣ q ^ n + 1 := by
  have : q ^ n % 2 = 1 := by simp [Nat.pow_mod, hq]
  omega

theorem kl5_sixteen_dvd_sl3 {q : ℕ} (hq : q % 2 = 1) :
    16 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  refine Dvd.dvd.mul_left ?_ _
  simpa using mul_dvd_mul (kl5_eight_dvd_sq_sub_one hq) (kl5_two_dvd_pow_sub_one hq 3)

theorem kl5_sixteen_dvd_su3 {q : ℕ} (hq : q % 2 = 1) :
    16 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  refine Dvd.dvd.mul_left ?_ _
  simpa using mul_dvd_mul (kl5_eight_dvd_sq_sub_one hq) (kl5_two_dvd_pow_add_one hq 3)

theorem kl5_odd_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ^ f % 2 = 1 :=
  Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)

theorem kl5_cube_dvd_card_quot_A {S : Type} [Group S] {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : p ^ (3 * f) ∣ Nat.card (↥A ⧸ Subgroup.center ↥A) := by
  obtain ⟨-, -, -, -, -, -, hA, -⟩ := h
  rw [pow_mul' p 3 f]
  rcases hA with hA | hA
  · simpa using kl5_pow_dvd_card_psl (n := 3) (by norm_num) hA
  · exact kl5_cube_dvd_card_psu hA

theorem kl5_cube_dvd_card_A {S : Type} [Group S] {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : p ^ (3 * f) ∣ Nat.card ↥A :=
  (kl5_cube_dvd_card_quot_A h).trans (Subgroup.card_quotient_dvd_card _)

theorem kl5_sixteen_dvd_card_A {S : Type} [Group S] {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : 16 ∣ Nat.card ↥A := by
  obtain ⟨-, -, -, hp, hp2, -, hA, -⟩ := h
  have hq := kl5_odd_pow (f := f) hp hp2
  refine Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (Subgroup.center ↥A))
  have hcop : Nat.Coprime 16 3 := by norm_num
  rcases hA with hA | hA
  · have hm := kl5_card_mul_gcd_psl (n := 3) (by norm_num) hA
    rw [show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
      Finset.prod_pair (by norm_num)] at hm
    have h16 : 16 ∣ Nat.card (↥A ⧸ Subgroup.center ↥A) * Nat.gcd 3 (p ^ f - 1) := by
      rw [hm]
      exact kl5_sixteen_dvd_sl3 hq
    exact (hcop.coprime_dvd_right (Nat.gcd_dvd_left 3 _)).dvd_of_dvd_mul_right h16
  · have hm := kl5_card_mul_gcd_psu_three hA
    have h16 : 16 ∣ Nat.card (↥A ⧸ Subgroup.center ↥A) * Nat.gcd 3 (p ^ f + 1) := by
      rw [hm]
      exact kl5_sixteen_dvd_su3 hq
    exact (hcop.coprime_dvd_right (Nat.gcd_dvd_left 3 _)).dvd_of_dvd_mul_right h16

theorem kl5_dvd_card_quot_B {S : Type} [Group S] {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : p ^ f ∣ Nat.card (↥B ⧸ Subgroup.center ↥B) := by
  obtain ⟨-, -, -, -, -, -, -, hB⟩ := h
  simpa using kl5_pow_dvd_card_psl (n := 2) le_rfl hB

theorem kl5_exists_involution_B {S : Type} [Group S] [Finite S] {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : ∃ b ∈ B, b * b = 1 ∧ b ≠ 1 := by
  obtain ⟨-, -, -, hp, hp2, -, -, hB⟩ := h
  have hq := kl5_odd_pow (f := f) hp hp2
  have hm := kl5_card_mul_gcd_psl (n := 2) le_rfl hB
  have hq1 : 2 ∣ p ^ f - 1 := by omega
  rw [show 2 * (2 - 1) / 2 = 1 from rfl, show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide,
    Finset.prod_singleton, pow_one, Nat.gcd_eq_left hq1] at hm
  have h4 : 4 ∣ p ^ f * ((p ^ f) ^ 2 - 1) :=
    (show 4 ∣ 8 by norm_num).trans (Dvd.dvd.mul_left (kl5_eight_dvd_sq_sub_one hq) _)
  have h2 : 2 ∣ Nat.card (↥B ⧸ Subgroup.center ↥B) := by
    generalize p ^ f * ((p ^ f) ^ 2 - 1) = M at hm h4
    omega
  have h2B : 2 ∣ Nat.card ↥B := h2.trans (Subgroup.card_quotient_dvd_card _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2B
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  refine ⟨(x : S), x.2, ?_, fun h1 => ?_⟩
  · have : x * x = 1 := by rw [← pow_two]; exact hx2
    exact congrArg Subtype.val this
  · have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem kl5_card_dvd_of_commute {S : Type} [Group S] [Finite S] {A B : Subgroup S}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card (↥A ⧸ Subgroup.center ↥A) * Nat.card ↥B ∣ Nat.card S := by
  let μ : ↥A × ↥B →* S := A.subtype.noncommCoprod B.subtype (fun a b => hcomm a a.2 b b.2)
  have hμ : ∀ x : ↥A × ↥B, μ x = (x.1 : S) * (x.2 : S) := fun x => rfl
  have hker : ∀ k : μ.ker, (k.1.1 : S) * (k.1.2 : S) = 1 := fun k => by
    have := k.2
    rwa [MonoidHom.mem_ker, hμ] at this
  have hmem : ∀ k : μ.ker, k.1.1 ∈ Subgroup.center ↥A := by
    intro k
    rw [Subgroup.mem_center_iff]
    intro a'
    have hb : (k.1.2 : S) = (k.1.1 : S)⁻¹ := eq_inv_of_mul_eq_one_right (hker k)
    apply Subtype.ext
    have h1 := hcomm (a' : S) a'.2 (k.1.2 : S) k.1.2.2
    rw [hb] at h1
    simp only [Subgroup.coe_mul]
    calc (a' : S) * (k.1.1 : S) = (k.1.1 : S) * ((k.1.1 : S)⁻¹ * (a' : S)) * (k.1.1 : S) := by group
      _ = (k.1.1 : S) * ((a' : S) * (k.1.1 : S)⁻¹) * (k.1.1 : S) := by rw [← h1]
      _ = (k.1.1 : S) * (a' : S) := by group
  let ψ : μ.ker →* ↥(Subgroup.center ↥A) :=
    ((MonoidHom.fst ↥A ↥B).comp μ.ker.subtype).codRestrict (Subgroup.center ↥A) hmem
  have hψ : Function.Injective ψ := by
    intro k₁ k₂ hk
    have h1 : k₁.1.1 = k₂.1.1 := congrArg (fun z : ↥(Subgroup.center ↥A) => (z : ↥A)) hk
    have h2 : k₁.1.2 = k₂.1.2 := by
      apply Subtype.ext
      apply mul_left_cancel (a := (k₁.1.1 : S))
      rw [hker k₁, h1, hker k₂]
    exact Subtype.ext (Prod.ext h1 h2)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_injective ψ hψ
  have h2 : Nat.card μ.ker * Nat.card μ.range = Nat.card ↥A * Nat.card ↥B := by
    rw [Subgroup.card_ker_mul_card_range, Nat.card_prod]
  have h3 : Nat.card ↥A = Nat.card (↥A ⧸ Subgroup.center ↥A) * Nat.card ↥(Subgroup.center ↥A) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h4 : Nat.card μ.range = Nat.card (↥A ⧸ Subgroup.center ↥A) * c * Nat.card ↥B := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := μ.ker))
    rw [h2, h3, hc]
    ring
  exact (Dvd.intro_left c (by rw [h4]; ring) : Nat.card (↥A ⧸ Subgroup.center ↥A) * Nat.card ↥B ∣
    Nat.card μ.range).trans (Subgroup.card_subgroup_dvd_card _)

theorem kl5_dvd_card {S : Type} [Group S] [Finite S] {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : p ^ (4 * f) ∣ Nat.card S := by
  have h3 := kl5_cube_dvd_card_quot_A h
  have h1 := kl5_dvd_card_quot_B h
  calc p ^ (4 * f) = p ^ (3 * f) * p ^ f := by ring
    _ ∣ Nat.card (↥A ⧸ Subgroup.center ↥A) * Nat.card ↥B :=
        mul_dvd_mul h3 (h1.trans (Subgroup.card_quotient_dvd_card _))
    _ ∣ Nat.card S := kl5_card_dvd_of_commute h.1

end CFSG.GH74.Generic.S1
