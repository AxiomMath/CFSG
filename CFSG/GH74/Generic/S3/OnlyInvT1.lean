module

public import CFSG.GH74.Generic.S3.L3ClassC2T2

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.Open (ordA ordTwistedA ordRee)

theorem not_cube_dvd_odd_part {q : ℕ} (hq5 : 5 ≤ q) (hqodd : q % 2 = 1) :
    ¬ q ^ 3 ∣ 2027025 := by
  intro h
  have hle : q ^ 3 ≤ 2027025 := Nat.le_of_dvd (by norm_num) h
  have hq : q ≤ 126 := by
    by_contra hc
    have : 127 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem not_cube_dvd {q N : ℕ} (hq5 : 5 ≤ q) (hqodd : q % 2 = 1) (hN : N ∣ 2 ^ 8 * 2027025) :
    ¬ q ^ 3 ∣ N := by
  intro h
  have h1 : q ^ 3 ∣ 2 ^ 8 * 2027025 := h.trans hN
  have hcop : Nat.Coprime (q ^ 3) (2 ^ 8) := by
    apply Nat.Coprime.pow
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  exact not_cube_dvd_odd_part hq5 hqodd (hcop.dvd_of_dvd_mul_left h1)

theorem sixteen_dvd_prod_sub {q : ℕ} (hq : q % 2 = 1) :
    16 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have h2 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  have h3 : (2 * m + 1) ^ 3 - 1 = 2 * (4 * m ^ 3 + 6 * m ^ 2 + 3 * m) := by
    have : (2 * m + 1) ^ 3 = 2 * (4 * m ^ 3 + 6 * m ^ 2 + 3 * m) + 1 := by ring
    omega
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
  rw [h2, h3, hk]
  exact ⟨(2 * m + 1) ^ 3 * (k * (4 * m ^ 3 + 6 * m ^ 2 + 3 * m)), by ring⟩

theorem sixteen_dvd_prod_add {q : ℕ} (hq : q % 2 = 1) :
    16 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have h2 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  have h3 : (2 * m + 1) ^ 3 + 1 = 2 * (4 * m ^ 3 + 6 * m ^ 2 + 3 * m + 1) := by ring
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
  rw [h2, h3, hk]
  exact ⟨(2 * m + 1) ^ 3 * (k * (4 * m ^ 3 + 6 * m ^ 2 + 3 * m + 1)), by ring⟩

theorem sixteen_dvd_ordA_two {q : ℕ} (hq : q % 2 = 1) : 16 ∣ ordA 2 q := by
  have h := L3Ord.ordA_two_mul q (by omega)
  have hd : 16 ∣ ordA 2 q * Nat.gcd 3 (q - 1) := by rw [h]; exact sixteen_dvd_prod_sub hq
  have hcop : Nat.Coprime 16 (Nat.gcd 3 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 (q - 1)) (by norm_num)
  exact hcop.dvd_of_dvd_mul_right hd

theorem sixteen_dvd_ordTwistedA_two {q : ℕ} (hq : q % 2 = 1) : 16 ∣ ordTwistedA 2 q := by
  have h := L3Ord.ordTwistedA_two_mul q
  have hd : 16 ∣ ordTwistedA 2 q * Nat.gcd 3 (q + 1) := by rw [h]; exact sixteen_dvd_prod_add hq
  have hcop : Nat.Coprime 16 (Nat.gcd 3 (q + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 (q + 1)) (by norm_num)
  exact hcop.dvd_of_dvd_mul_right hd


theorem not_sixteen_dvd_ordRee (k : ℕ) : ¬ 16 ∣ ordRee (3 ^ (2 * k + 1)) := by
  have hq : 3 ^ (2 * k + 1) % 16 = 3 ∨ 3 ^ (2 * k + 1) % 16 = 11 := by
    induction k with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]
      omega
  unfold ordRee
  generalize 3 ^ (2 * k + 1) = Q at *
  have hQ1 : 1 ≤ Q := by omega
  have key : (Q ^ 3 * (Q ^ 3 + 1) * (Q - 1)) % 16 = 8 := by
    have h3 : Q ^ 3 % 16 = 11 ∨ Q ^ 3 % 16 = 3 := by
      rcases hq with h | h
      · left; rw [Nat.pow_mod, h]
      · right; rw [Nat.pow_mod, h]
    rw [Nat.mul_mod, Nat.mul_mod (Q ^ 3)]
    rcases hq with h | h
    · have e1 : Q ^ 3 % 16 = 11 := by rw [Nat.pow_mod, h]
      have e2 : (Q ^ 3 + 1) % 16 = 12 := by omega
      have e3 : (Q - 1) % 16 = 2 := by omega
      rw [e1, e2, e3]
    · have e1 : Q ^ 3 % 16 = 3 := by rw [Nat.pow_mod, h]
      have e2 : (Q ^ 3 + 1) % 16 = 4 := by omega
      have e3 : (Q - 1) % 16 = 10 := by omega
      rw [e1, e2, e3]
  omega

theorem three_mul_card_ge {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h : LieModel X t 3 p f) :
    (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ≤ 3 * Nat.card X := by
  have hq1 : 1 ≤ p ^ f := by omega
  rcases ht with rfl | rfl
  · have hc := card_of_lieModel_PSL (n := 3) (by norm_num) h
    simp only [show 3 - 1 = 2 from rfl] at hc
    rw [hc]
    have h1 := L3Ord.ordA_two_mul (p ^ f) hq1
    have hg : Nat.gcd 3 (p ^ f - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    calc (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1))
        = ordA 2 (p ^ f) * Nat.gcd 3 (p ^ f - 1) := h1.symm
      _ ≤ ordA 2 (p ^ f) * 3 := Nat.mul_le_mul_left _ hg
      _ = 3 * ordA 2 (p ^ f) := by ring
  · have hc := card_of_lieModel_PSU (n := 3) (by norm_num) hp2 h
    simp only [show 3 - 1 = 2 from rfl] at hc
    rw [hc]
    have h1 := L3Ord.ordTwistedA_two_mul (p ^ f)
    have hg : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hle : (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ≤
        (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    calc (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1))
        ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := hle
      _ = ordTwistedA 2 (p ^ f) * Nat.gcd 3 (p ^ f + 1) := h1.symm
      _ ≤ ordTwistedA 2 (p ^ f) * 3 := Nat.mul_le_mul_left _ hg
      _ = 3 * ordTwistedA 2 (p ^ f) := by ring

theorem sixteen_dvd_card_l3 {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X t 3 p f) :
    16 ∣ Nat.card X := by
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  rcases ht with rfl | rfl
  · have hc := card_of_lieModel_PSL (n := 3) (by norm_num) h
    simp only [show 3 - 1 = 2 from rfl] at hc
    rw [hc]
    exact sixteen_dvd_ordA_two hodd
  · have hc := card_of_lieModel_PSU (n := 3) (by norm_num) hp2 h
    simp only [show 3 - 1 = 2 from rfl] at hc
    rw [hc]
    exact sixteen_dvd_ordTwistedA_two hodd

theorem card_lt_four_mul {X Y : Type} [Group X] [Group Y] {tX tY : StatedLieTag} {p f p' f' : ℕ}
    (htX : tX = .PSL ∨ tX = .PSU) (htY : tY = .PSL ∨ tY = .PSU)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (hq' : 5 ≤ p' ^ f') (hle : p' ^ f' ≤ p ^ f)
    (hX : LieModel X tX 3 p f) (hY : LieModel Y tY 3 p' f') :
    Nat.card Y < 4 * Nat.card X := by
  obtain ⟨-, hYle, -⟩ := l3_card_bounds htY hp' hp2' hq' hY
  have hXge := three_mul_card_ge htX hp2 hq hX
  set q := p ^ f with hqdef
  set q' := p' ^ f' with hq'def
  have hmono : q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 + 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hle 3)
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)
        (Nat.add_le_add_right (Nat.pow_le_pow_left hle 3) 1))
  have hYq : Nat.card Y ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := hYle.trans hmono
  by_contra hcon
  have h4 : 4 * Nat.card X ≤ Nat.card Y := by omega
  have ha : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hc : 24 ≤ q ^ 2 - 1 := by
    have : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  obtain ⟨a', ha'⟩ : ∃ a', q ^ 3 = a' + 1 := ⟨q ^ 3 - 1, by omega⟩
  have e1 : q ^ 3 - 1 = a' := by omega
  have e2 : q ^ 3 + 1 = a' + 2 := by omega
  rw [e1] at hXge
  rw [e2] at hYq
  set c := q ^ 2 - 1 with hcdef
  have hmain : (q ^ 3 * c) * (4 * a') ≤ (q ^ 3 * c) * (3 * (a' + 2)) := by
    calc (q ^ 3 * c) * (4 * a') = 4 * (q ^ 3 * (c * a')) := by ring
      _ ≤ 3 * Nat.card Y := by omega
      _ ≤ 3 * (q ^ 3 * (c * (a' + 2))) := by omega
      _ = (q ^ 3 * c) * (3 * (a' + 2)) := by ring
  have hpos : 0 < q ^ 3 * c := Nat.mul_pos (by omega) (by omega)
  have := Nat.le_of_mul_le_mul_left hmain hpos
  omega


theorem exists_factor_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C] (ψ : A →* B)
    (hψ : Function.Surjective ψ) (π : A →* C) (h : ψ.ker ≤ π.ker) :
    ∃ π' : B →* C, ∀ a, π' (ψ a) = π a := by
  refine ⟨(QuotientGroup.lift ψ.ker π h).comp
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom, ?_⟩
  intro a
  have : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ a) = (a : A ⧸ ψ.ker) := by
    apply (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).injective
    simp only [MulEquiv.apply_symm_apply]
    rfl
  simp [this]

theorem card_le_six_of_lt_four_mul {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L)
    {A : Subgroup L} (hA : A ≠ ⊤) (h : Nat.card L < 4 * Nat.card A) : Nat.card L ≤ 6 := by
  have hidx : A.index * Nat.card A = Nat.card L := A.index_mul_card
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hn : A.index < 4 := by
    by_contra hc
    have : 4 * Nat.card A ≤ A.index * Nat.card A := Nat.mul_le_mul_right _ (by omega)
    omega
  have hfin : A.FiniteIndex := Subgroup.finiteIndex_of_finite
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index A
  have hnc : A.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A.normalCore with h0 | h1
    · exact h0
    · exfalso
      apply hA
      rw [eq_top_iff]
      have := A.normalCore_le
      rwa [h1] at this
  rw [hnc, Subgroup.index_bot] at hdvd
  calc Nat.card L ≤ Nat.factorial A.index := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    _ ≤ Nat.factorial 3 := Nat.factorial_le (by omega)
    _ = 6 := by norm_num [Nat.factorial]

structure IsL3Cover (A K₀ : Type) [Group A] [Group K₀] (p f : ℕ) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  big : 5 ≤ p ^ f
  perfect : Group.IsPerfect A
  model : ∃ t : StatedLieTag, (t = .PSL ∨ t = .PSU) ∧ LieModel K₀ t 3 p f
  cover : ∃ π : A →* K₀, Function.Surjective π ∧ π.ker ≤ Subgroup.center A

namespace IsL3Cover

variable {A K₀ : Type} [Group A] [Group K₀] {p f : ℕ} (h : IsL3Cover A K₀ p f)

include h

theorem simple : IsSimpleGroup K₀ := by
  obtain ⟨t, ht, hm⟩ := h.model
  rcases ht with rfl | rfl
  · exact isSimpleGroup_of_lieModel_L3' (Or.inl hm)
  · exact isSimpleGroup_of_lieModel_L3' (Or.inr hm)

theorem card_bounds :
    124000 ≤ Nat.card K₀ ∧ Nat.card K₀ ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) ∧
      p ^ (3 * f) ∣ Nat.card K₀ := by
  obtain ⟨t, ht, hm⟩ := h.model
  exact l3_card_bounds ht h.prime h.ne_two h.big hm

theorem finite : Finite K₀ :=
  Nat.finite_of_card_ne_zero (by have := h.card_bounds.1; omega)

theorem odd_q : p ^ f % 2 = 1 := Nat.odd_iff.1 ((h.prime.odd_of_ne_two h.ne_two).pow)

theorem sixteen_dvd : 16 ∣ Nat.card K₀ := by
  obtain ⟨t, ht, hm⟩ := h.model
  exact sixteen_dvd_card_l3 ht h.prime h.ne_two hm

theorem perfect_target : Group.IsPerfect K₀ := by
  have := h.perfect
  obtain ⟨π, hπ, -⟩ := h.cover
  exact Group.IsPerfect.ofSurjective hπ

theorem nontrivial : Nontrivial K₀ := by
  have := h.finite
  have h1 := h.card_bounds.1
  exact Finite.one_lt_card_iff_nontrivial.1 (by omega)

theorem not_isSolvable : ¬ Group.IsSolvable K₀ := by
  have := h.perfect_target
  have := h.nontrivial
  exact Group.IsPerfect.not_isSolvable K₀

theorem nonabelian : ∃ a b : K₀, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have := h.simple
  exact h.not_isSolvable (IsSimpleGroup.comm_iff_isSolvable.1 hc)

theorem card_le [Finite A] : Nat.card K₀ ≤ Nat.card A := by
  obtain ⟨π, hπ, -⟩ := h.cover
  exact Nat.card_le_card_of_surjective π hπ

theorem card_dvd [Finite A] : Nat.card K₀ ∣ Nat.card A := by
  obtain ⟨π, hπ, -⟩ := h.cover
  have e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have h1 : Nat.card A = Nat.card (A ⧸ π.ker) * Nat.card π.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr e.toEquiv] at h1
  exact ⟨Nat.card π.ker, h1⟩

theorem center_le_ker (π : A →* K₀) (hπ : Function.Surjective π) :
    Subgroup.center A ≤ π.ker := by
  have hs := h.simple
  have hnc := h.nonabelian
  have hcen : Subgroup.center K₀ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K₀) with h0 | h1
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : a ∈ Subgroup.center K₀ := by rw [h1]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 this b).symm
  intro z hz
  rw [MonoidHom.mem_ker]
  have : π z ∈ Subgroup.center K₀ := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨a, rfl⟩ := hπ k
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz a]
  rw [hcen, Subgroup.mem_bot] at this
  exact this

theorem of_mulEquiv {A' : Type} [Group A'] (e : A' ≃* A) : IsL3Cover A' K₀ p f := by
  refine ⟨h.prime, h.ne_two, h.big, ?_, h.model, ?_⟩
  · have := h.perfect
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · obtain ⟨π, hπ, hker⟩ := h.cover
    refine ⟨π.comp e.toMonoidHom, hπ.comp e.surjective, ?_⟩
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ha
    have hz : e a ∈ Subgroup.center A := hker ha
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hz (e g)

end IsL3Cover

end CFSG.GH74.Generic.S3
