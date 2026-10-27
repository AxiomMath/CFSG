module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveNineteenCoreSupport

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

namespace LocalParameterFiveOddCore

theorem prime_not_dvd_card_oddCore_centralizer_of_five {G : Type} [Group G] [Fintype G] {n : ℕ}
    (hn : 4 ≤ n) {S : Subgroup G} (fS : SemidihedralGroup n ≃* S) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G), v ≠ 1 →
      ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (h36 : 36 % ℓ = 1)
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hdeg : Module.finrank ℂ θ.vector < 4 * (ℓ - 1) + 5)
    (hrat : ∀ g, ∃ q : ℚ, θ.character g = q) (hfaith : Function.Injective θ.representation)
    (htval : θ.character t = 5) (hNval : ∀ y : C t, y ∈ N t → θ.character (t * y) = 5)
    (hD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) =
      12 * Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
        (N t))) :
    ¬ ℓ ∣ Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
      (N t)) := by
  intro hℓdvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) with hV
  have : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  obtain ⟨-, ht2, -, hsC, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hℓdvd
  set u : G := (((x : N t) : C t) : G) with hu
  have huℓ : orderOf u = ℓ := by
    rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have huC : u ∈ C t := ((x : N t) : C t).property
  have hus : u ∈ Subgroup.centralizer {(fS (s n) : G)} := (Subgroup.mem_subgroupOf.mp x.property)
  set P : Subgroup G := Subgroup.zpowers u with hP
  have hPcard : Nat.card P = ℓ := by rw [hP, Nat.card_zpowers, huℓ]
  have hPV : P ≤ Subgroup.centralizer V := by
    rw [hP, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro v hv
    have hle : V ≤ Subgroup.centralizer {u} := by
      rw [hV]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp huC).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hus).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv))
  have hconst : ∀ v ∈ V, v ≠ 1 → ∀ z ∈ P, θ.representation.character (v * z) =
      θ.representation.character v := by
    intro v hv hv1 z hz
    obtain ⟨g, hg, hgv⟩ := hfus v hv hv1
    have hzV : z ∈ Subgroup.centralizer V := hPV hz
    have hyV : g * z * g⁻¹ ∈ Subgroup.centralizer V := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : g⁻¹ * w * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hzV _ hw'
      calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
        _ = g * z * g⁻¹ * w := by group
    have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have hsV : (fS (s n) : G) ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hyC : g * z * g⁻¹ ∈ C t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyV t htV).symm
    have hys : g * z * g⁻¹ ∈ Subgroup.centralizer {(fS (s n) : G)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyV _ hsV).symm
    have hzℓ : z ^ ℓ = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← huℓ,
        pow_orderOf_eq_one, one_zpow]
    have hyℓ : (g * z * g⁻¹) ^ ℓ = 1 := by rw [conj_pow, hzℓ]; group
    have hyN := mem_oddCore_of_pow_prime h36 hD hyC hys hyℓ
    have hval := hNval ⟨g * z * g⁻¹, hyC⟩ hyN
    have hconj : θ.representation.character (v * z) =
        θ.representation.character (g * (v * z) * g⁻¹) :=
      (Representation.char_conj θ.representation (v * z) g).symm
    rw [hconj, show g * (v * z) * g⁻¹ = (g * v * g⁻¹) * (g * z * g⁻¹) by group, hgv]
    have hconjv : θ.representation.character v =
        θ.representation.character (g * v * g⁻¹) :=
      (Representation.char_conj θ.representation v g).symm
    rw [hconjv, hgv]
    exact hval.trans htval.symm
  have hker : ¬ P ≤ MonoidHom.ker θ.representation := by
    intro hle
    have huker : u ∈ MonoidHom.ker θ.representation := hle (Subgroup.mem_zpowers u)
    have hu1 : u = 1 := hfaith ((MonoidHom.mem_ker.mp huker).trans (map_one _).symm)
    rw [hu1, orderOf_one] at huℓ
    exact hℓ.one_lt.ne huℓ
  obtain ⟨-, hbound⟩ := four_group_central_prime_coset_constant_degree_bound θ.representation V
    P hPV hℓ hℓodd hPcard
    (fun z _ => hrat z) hker hconst
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    norm_num at ht2
  have h := hbound t htV ht1
  rw [show θ.representation.character t = 5 from htval] at h
  have hnorm : ‖(5 : ℂ)‖ = 5 := by norm_num
  rw [hnorm] at h
  have hdeg' : (Module.finrank ℂ θ.vector : ℝ) < ((4 * (ℓ - 1) : ℕ) : ℝ) + 5 := by
    exact_mod_cast hdeg
  linarith

theorem exists_card_five_subgroup_of_pow_five {N : Type} [Group N] [Fintype N]
    (hN : Nat.card N ∣ 3 ^ 4 * 5) (h5 : 5 ∣ Nat.card N) (τ : FiniteComplexRepresentation.{0, 0} N)
    (hfaith : Function.Injective τ.representation) (hrat : ∀ x, ∃ q : ℚ, τ.character x = q)
    (hdeg : Module.finrank ℂ τ.vector < 10) :
    ∃ P : Subgroup N, Nat.card P = 5 ∧ ∀ y : N, y ^ 5 = 1 → y ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨i, hi, hNi⟩ : ∃ i, i ≤ 4 ∧ Nat.card N = 3 ^ i * 5 := by
    obtain ⟨d₁, d₂, h1, h2, hd⟩ := Nat.dvd_mul.mp hN
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h2 with rfl | rfl
    · exfalso
      rw [← hd, mul_one] at h5
      have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5)
      norm_num at this
    · exact ⟨i, hi, hd.symm⟩
  have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hfac3 : (Nat.card N).factorization 3 = i := by
    rw [hNi, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hfac5 : (Nat.card N).factorization 5 = 1 := by
    rw [hNi, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => by
        have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h
        norm_num at this), zero_add, Nat.Prime.factorization_self (by norm_num)]
  obtain ⟨R⟩ : Nonempty (Sylow 3 N) := inferInstance
  obtain ⟨P⟩ : Nonempty (Sylow 5 N) := inferInstance
  have hRcard : Nat.card R = 3 ^ i := by rw [R.card_eq_multiplicity, hfac3]
  have hPcard : Nat.card P = 5 := by rw [P.card_eq_multiplicity, hfac5, pow_one]
  have hRnormal : (R : Subgroup N).Normal := by
    have hidx : (R : Subgroup N).index = 5 := by
      have h := (R : Subgroup N).card_mul_index
      rw [hRcard, hNi] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    have hdvd := Sylow.card_dvd_index R
    rw [hidx] at hdvd
    have hmod := card_sylow_modEq_one 3 N
    have h1 : Nat.card (Sylow 3 N) = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
      · exact h
      · rw [h] at hmod
        norm_num [Nat.ModEq] at hmod
    rw [Sylow.card_eq_index_normalizer R, Subgroup.index_eq_one] at h1
    change Subgroup.normalizer ((R : Subgroup N) : Set N) = ⊤ at h1
    exact Subgroup.normalizer_eq_top_iff.mp h1
  obtain ⟨u, hu⟩ : ∃ u : (P : Subgroup N), orderOf u = 5 :=
    exists_prime_orderOf_dvd_card' 5 (by rw [hPcard])
  have hu5 : orderOf (u : N) = 5 := by rw [Subgroup.orderOf_coe, hu]
  have hPu : (P : Subgroup N) = Subgroup.zpowers (u : N) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.2)
    rw [hPcard, Nat.card_zpowers, hu5]
  let α : MulAut R := MulAut.conjNormal (H := (R : Subgroup N)) (u : N)
  have hu5' : (u : N) ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hu5])
  have hα : α ^ 5 = 1 := by
    change (MulAut.conjNormal (H := (R : Subgroup N)) (u : N)) ^ 5 = 1
    rw [← map_pow, hu5', map_one]
  let τR : FiniteComplexRepresentation.{0, 0} R :=
    { vector := τ.vector
      representation := τ.representation.comp (R : Subgroup N).subtype }
  have hτRfaith : Function.Injective τR.representation :=
    hfaith.comp (R : Subgroup N).subtype_injective
  have hR3 : IsPGroup 3 R := R.isPGroup'
  have hR81 : Nat.card R ≤ 81 := by
    rw [hRcard]
    calc 3 ^ i ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi
      _ = 81 := by norm_num
  have hαR := order_five_automorphism_small_three_group_rational_character_obstruction hR3 hR81
    α hα τR hτRfaith (fun x => hrat x) hdeg (fun x => by
      change τ.character ((MulAut.conjNormal (H := (R : Subgroup N)) (u : N) x : R) : N) =
        τ.character (x : N)
      rw [MulAut.conjNormal_apply]
      exact Representation.char_conj τ.representation (x : N) (u : N))
  have hcomm : ∀ x ∈ (R : Subgroup N), (u : N) * x = x * u := by
    intro x hx
    have h := congrArg (fun β : MulAut R => ((β ⟨x, hx⟩ : R) : N)) hαR
    simp only [α, MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc (u : N) * x = u * x * (u : N)⁻¹ * u := by group
      _ = x * u := by rw [h]
  have hsup : (R : Subgroup N) ⊔ P = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    have h3 : Nat.card (R : Subgroup N) ∣ Nat.card ((R : Subgroup N) ⊔ P : Subgroup N) :=
      Subgroup.card_dvd_of_le le_sup_left
    have h5' : Nat.card (P : Subgroup N) ∣ Nat.card ((R : Subgroup N) ⊔ P : Subgroup N) :=
      Subgroup.card_dvd_of_le le_sup_right
    rw [hRcard] at h3
    rw [hPcard] at h5'
    have hcop : Nat.Coprime (3 ^ i) 5 := Nat.Coprime.pow_left _ (by norm_num)
    rw [hNi]
    exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h3 h5')
  refine ⟨P, hPcard, fun y hy => ?_⟩
  have hytop : y ∈ (R : Subgroup N) ⊔ P := hsup ▸ Subgroup.mem_top y
  obtain ⟨x, hx, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hytop
  have hpx : Commute x p := by
    rw [hPu] at hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact ((Commute.zpow_left (show Commute (u : N) x from hcomm x hx) k)).symm
  have hp5 : p ^ 5 = 1 := by
    have := Subgroup.orderOf_dvd_natCard (P : Subgroup N) hp
    rw [hPcard] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hx5 : x ^ 5 = 1 := by
    rw [hpx.mul_pow, hp5, mul_one] at hy
    exact hy
  have hx1 : x = 1 := by
    have h1 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hx5
    have h2 : orderOf x ∣ 3 ^ i := hRcard ▸ Subgroup.orderOf_dvd_natCard _ hx
    have h3 : orderOf x ∣ Nat.gcd 5 (3 ^ i) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right _ (by norm_num)), Nat.dvd_one] at h3
    exact orderOf_eq_one_iff.mp h3
  rw [hx1, one_mul]
  exact hp

end LocalParameterFiveOddCore

end CFSG.Semidihedral.Principal
