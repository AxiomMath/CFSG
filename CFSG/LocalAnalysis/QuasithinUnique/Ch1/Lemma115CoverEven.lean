module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverDihedral
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Datum

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.ShultStronglyClosedTI
open scoped Pointwise commutatorElement

section TwoElements

theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {ζ : G} {n : ℕ} (h : ζ ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers ζ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])

variable {L A : Type*} [Group L] [Finite L] [Group A]

omit [Finite L] in
theorem mem_sylow_of_central_pow {ζ : L} (hζ : ζ ∈ Subgroup.center L) {n : ℕ} (h : ζ ^ 2 ^ n = 1)
    (P : Sylow 2 L) : ζ ∈ P :=
  central_pSubgroup_le_sylow P (Subgroup.zpowers ζ) (Subgroup.zpowers_le.2 hζ)
    (isPGroup_zpowers_of_pow h) (Subgroup.mem_zpowers ζ)

omit [Finite L] in
theorem mem_sylow_of_map_mem (π : L →* A) (hker : π.ker ≤ Subgroup.center L) (P : Sylow 2 L)
    {g : L} {k : ℕ} (hgk : g ^ 2 ^ k = 1) (hmem : π g ∈ (P : Subgroup L).map π) : g ∈ P := by
  obtain ⟨p, hp, hpg⟩ := hmem
  set ζ := p⁻¹ * g with hζ
  have hζ1 : π ζ = 1 := by rw [hζ, map_mul, map_inv, hpg, inv_mul_cancel]
  have hζc : ζ ∈ Subgroup.center L := hker (MonoidHom.mem_ker.2 hζ1)
  have hgp : g = p * ζ := by rw [hζ, mul_inv_cancel_left]
  have hcomm : Commute p ζ := Subgroup.mem_center_iff.1 hζc p
  have hζk : ζ ^ 2 ^ k = (p ^ 2 ^ k)⁻¹ := by
    have h1 : p ^ 2 ^ k * ζ ^ 2 ^ k = 1 := by rw [← hcomm.mul_pow, ← hgp, hgk]
    exact eq_inv_of_mul_eq_one_right h1
  have hmemP : ζ ^ 2 ^ k ∈ (P : Subgroup L) := by
    rw [hζk]
    exact inv_mem (pow_mem hp _)
  obtain ⟨e, he⟩ := P.isPGroup' ⟨ζ ^ 2 ^ k, hmemP⟩
  have he' : (ζ ^ 2 ^ k) ^ 2 ^ e = 1 := congrArg Subtype.val he
  have hζ2 : ζ ^ 2 ^ (k + e) = 1 := by rw [pow_add, pow_mul, he']
  rw [hgp]
  exact mul_mem hp (mem_sylow_of_central_pow hζc hζ2 P)

end TwoElements

section SylowInSubgroup

variable {A : Type*} [Group A] [Finite A]

theorem exists_conj_mem_sylow_of_le (S : Sylow 2 A) (C : Subgroup A)
    (hSC : (S : Subgroup A) ≤ C) {t : A} (htC : t ∈ C) (ht : t * t = 1) :
    ∃ c ∈ C, c⁻¹ * t * c ∈ (S : Subgroup A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SC : Subgroup C := (S : Subgroup A).subgroupOf C
  have hcardSC : Nat.card SC = Nat.card (S : Subgroup A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hSA : Nat.card (S : Subgroup A) = 2 ^ (Nat.card A).factorization 2 :=
    S.card_eq_multiplicity
  have hle : (Nat.card C).factorization 2 ≤ (Nat.card A).factorization 2 :=
    (Nat.factorization_le_iff_dvd hC0 hA0).2 (Subgroup.card_subgroup_dvd_card C) 2
  have hdvdSC : Nat.card SC ∣ Nat.card C := Subgroup.card_subgroup_dvd_card SC
  have hge : (Nat.card A).factorization 2 ≤ (Nat.card C).factorization 2 := by
    have h2 : 2 ^ (Nat.card A).factorization 2 ∣ Nat.card C := by
      rw [← hSA, ← hcardSC]
      exact hdvdSC
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC0).1 h2
  let SylSC : Sylow 2 C :=
    Sylow.ofCard SC (by rw [hcardSC, hSA, le_antisymm hle hge])
  let tC : C := ⟨t, htC⟩
  have ht2 : tC ^ 2 ^ 1 = 1 := Subtype.ext (by simpa [sq] using ht)
  obtain ⟨R, hR⟩ := (isPGroup_zpowers_of_pow ht2).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C SylSC R
  have htR : tC ∈ (R : Subgroup C) := hR (Subgroup.mem_zpowers tC)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htR
  obtain ⟨s, hs, hst⟩ := htR
  have hs' : (c : A)⁻¹ * t * c = (s : A) := by
    have h1 : c * s * c⁻¹ = tC := by simpa [MulAut.smul_def, MulAut.conj_apply] using hst
    have h2 : s = c⁻¹ * tC * c := by rw [← h1]; group
    rw [h2]
    rfl
  refine ⟨c, c.2, ?_⟩
  rw [hs']
  exact hs

end SylowInSubgroup

section Lift

variable {A L : Type} [Group A] [Finite A] [Group L] [Finite L]

theorem exists_involution_lift_aux_cover (γ : A ≃* A) (hγ : ∀ a, γ (γ a) = a)
    (π : L →* A) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L)
    (α : L ≃* L) (hα : ∀ x, α (α x) = x) (hact : ∀ x, π (α x) = γ (π x))
    (P₀ : Sylow 2 L) (hP₀ : ∀ t ∈ (P₀ : Subgroup L), α t = t)
    (x₀ : A) (hyb2 : (x₀⁻¹ * γ x₀) * (x₀⁻¹ * γ x₀) = 1) :
    ∃ y : L, y * y = 1 ∧ π y = x₀⁻¹ * γ x₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set yb := x₀⁻¹ * γ x₀ with hyb
  obtain ⟨x, hx⟩ := hπ x₀
  set y₀ : L := x⁻¹ * α x with hy₀
  have hπy₀ : π y₀ = yb := by rw [hy₀, map_mul, map_inv, hact, hx]
  have hαy₀ : α y₀ = y₀⁻¹ := by
    rw [hy₀, map_mul, map_inv, hα, mul_inv_rev, inv_inv]
  have hybinv : yb⁻¹ = yb := inv_eq_of_mul_eq_one_right hyb2
  have hγyb : γ yb = yb := by
    have h1 : γ yb = yb⁻¹ := by rw [hyb, map_mul, map_inv, hγ, mul_inv_rev, inv_inv]
    rw [h1, hybinv]
  have hybC : yb ∈ fixedSubgroup γ := mem_fixedSubgroup.2 hγyb
  have hSC : ((P₀.mapSurjective hπ : Sylow 2 A) : Subgroup A) ≤ fixedSubgroup γ := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := (ha : a ∈ (P₀ : Subgroup L).map π)
    exact mem_fixedSubgroup.2 (by rw [← hact, hP₀ t ht])
  obtain ⟨c, hcC, hcS⟩ := exists_conj_mem_sylow_of_le (P₀.mapSurjective hπ) (fixedSubgroup γ)
    hSC hybC hyb2
  obtain ⟨p, hp, hpc⟩ := (hcS : c⁻¹ * yb * c ∈ (P₀ : Subgroup L).map π)
  obtain ⟨c', hc'⟩ := hπ c
  set y₁ : L := c' * p * c'⁻¹ with hy₁
  have hπy₁ : π y₁ = yb := by
    rw [hy₁, map_mul, map_mul, map_inv, hc', hpc]
    group
  have hζc : c'⁻¹ * α c' ∈ Subgroup.center L := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hact, hc', mem_fixedSubgroup.1 hcC, inv_mul_cancel]
  obtain ⟨ζ, hζ, hαc⟩ : ∃ ζ ∈ Subgroup.center L, α c' = c' * ζ :=
    ⟨c'⁻¹ * α c', hζc, by group⟩
  have hαy₁ : α y₁ = y₁ := by
    have h1 : ζ * p * ζ⁻¹ = p := by
      rw [(Subgroup.mem_center_iff.1 hζ p).symm, mul_inv_cancel_right]
    rw [hy₁, map_mul, map_mul, map_inv, hP₀ p hp, hαc]
    calc c' * ζ * p * (c' * ζ)⁻¹ = c' * (ζ * p * ζ⁻¹) * c'⁻¹ := by group
      _ = c' * p * c'⁻¹ := by rw [h1]
  obtain ⟨z, hzc, hz1, hy₀z⟩ : ∃ z : L, z ∈ Subgroup.center L ∧ π z = 1 ∧ y₀ = y₁ * z := by
    have h1 : π (y₁⁻¹ * y₀) = 1 := by rw [map_mul, map_inv, hπy₁, hπy₀, inv_mul_cancel]
    exact ⟨y₁⁻¹ * y₀, hker (MonoidHom.mem_ker.2 h1), h1, by group⟩
  have hwc : α z ∈ Subgroup.center L := by
    apply hker
    rw [MonoidHom.mem_ker, hact, hz1, map_one]
  have hy₀inv : y₀⁻¹ = y₁ * α z := by rw [← hαy₀, hy₀z, map_mul, hαy₁]
  have h1 : y₁ * z * (y₁ * α z) = 1 := by rw [← hy₀z, ← hy₀inv, mul_inv_cancel]
  have hy1sq : y₁ * y₁ = (z * α z)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc y₁ * y₁ * (z * α z) = y₁ * (y₁ * z) * α z := by group
      _ = y₁ * (z * y₁) * α z := by rw [(Subgroup.mem_center_iff.1 hzc y₁)]
      _ = y₁ * z * (y₁ * α z) := by group
      _ = 1 := h1
  have hy0sq : y₀ * y₀ = z * (α z)⁻¹ := by
    have h2 : y₀ * y₀ = y₁ * y₁ * (z * z) := by
      rw [hy₀z]
      calc y₁ * z * (y₁ * z) = y₁ * (z * y₁) * z := by group
        _ = y₁ * (y₁ * z) * z := by rw [(Subgroup.mem_center_iff.1 hzc y₁).symm]
        _ = y₁ * y₁ * (z * z) := by group
    rw [h2, hy1sq, mul_inv_rev]
    have h3 : z * (α z)⁻¹ = (α z)⁻¹ * z := (Subgroup.mem_center_iff.1 hzc (α z)⁻¹).symm
    rw [h3]
    group
  obtain ⟨s, m, hm, hsm⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card π.ker) Nat.card_pos.ne'
  have hzker : z ∈ π.ker := MonoidHom.mem_ker.2 hz1
  have hzs : z ^ (2 ^ s * m) = 1 := by
    have := Subgroup.orderOf_dvd_natCard π.ker hzker
    rw [hsm] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hzm : (z ^ m) ^ 2 ^ s = 1 := by rw [← pow_mul, mul_comm]; exact hzs
  have hzmP : z ^ m ∈ (P₀ : Subgroup L) :=
    mem_sylow_of_central_pow (pow_mem hzc m) hzm P₀
  have hαzm : α z ^ m = z ^ m := by rw [← map_pow]; exact hP₀ _ hzmP
  have hcommz : Commute z (α z)⁻¹ := (Subgroup.mem_center_iff.1 hzc (α z)⁻¹).symm
  have hy0m : (y₀ * y₀) ^ m = 1 := by
    rw [hy0sq, hcommz.mul_pow, inv_pow, hαzm, mul_inv_cancel]
  refine ⟨y₀ ^ m, ?_, ?_⟩
  · rw [← (Commute.refl y₀).mul_pow, hy0m]
  · obtain ⟨k, hk⟩ := hm
    have hyb2' : yb ^ 2 = 1 := by rw [sq]; exact hyb2
    rw [map_pow, hπy₀, hk, pow_succ, pow_mul, hyb2', one_pow, one_mul]

theorem exists_involution_lift_cover (γ : A ≃* A) (hγ : ∀ a, γ (γ a) = a)
    (hconj : ∀ s t : A, s * s = 1 → s ≠ 1 → t * t = 1 → t ≠ 1 → ∃ g, g * s * g⁻¹ = t)
    (htwist : ∃ x₀ : A, (x₀⁻¹ * γ x₀) * (x₀⁻¹ * γ x₀) = 1 ∧ x₀⁻¹ * γ x₀ ≠ 1)
    (π : L →* A) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L)
    (α : L ≃* L) (hα : ∀ x, α (α x) = x) (hact : ∀ x, π (α x) = γ (π x))
    (P₀ : Sylow 2 L) (hP₀ : ∀ t ∈ (P₀ : Subgroup L), α t = t) :
    ∀ t : A, t * t = 1 → t ≠ 1 → ∃ y : L, y * y = 1 ∧ π y = t := by
  intro t ht2 ht1
  obtain ⟨x₀, hyb2, hyb1⟩ := htwist
  obtain ⟨y, hy2, hπy⟩ := exists_involution_lift_aux_cover γ hγ π hπ hker α hα hact P₀ hP₀ x₀ hyb2
  obtain ⟨g, hg⟩ := hconj _ t hyb2 hyb1 ht2 ht1
  obtain ⟨g', hg'⟩ := hπ g
  refine ⟨g' * y * g'⁻¹, ?_, ?_⟩
  · calc g' * y * g'⁻¹ * (g' * y * g'⁻¹) = g' * (y * y) * g'⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  · rw [map_mul, map_mul, map_inv, hg', hπy]
    exact hg

end Lift

section DihedralSylow

variable {A : Type} [Group A] [Finite A]

theorem card_closure_eq_eight {a₀ b₀ : A} (ha : a₀ * a₀ = 1) (hb : b₀ * b₀ = 1)
    (hr : orderOf (a₀ * b₀) = 4) (hnot : a₀ ∉ Subgroup.zpowers (a₀ * b₀)) :
    Nat.card (Subgroup.closure ({a₀, b₀} : Set A)) = 8 := by
  set Q := Subgroup.closure ({a₀, b₀} : Set A) with hQ
  have hle : Nat.card Q ≤ 8 := by
    have := card_closure_involutions_le ha hb
    rw [hr] at this
    exact this
  have haQ : a₀ ∈ Q := Subgroup.subset_closure (by simp)
  have hbQ : b₀ ∈ Q := Subgroup.subset_closure (by simp)
  have hN : Subgroup.zpowers (a₀ * b₀) ≤ Q := Subgroup.zpowers_le.2 (mul_mem haQ hbQ)
  have hdvd : 4 ∣ Nat.card Q := by
    have := Subgroup.card_dvd_of_le hN
    rwa [Nat.card_zpowers, hr] at this
  have hne : Subgroup.zpowers (a₀ * b₀) ≠ Q := by
    intro h
    rw [← h] at haQ
    exact hnot haQ
  have hpos : 0 < Nat.card Q := Nat.card_pos
  by_contra hcon
  have h4 : Nat.card Q = 4 := by omega
  apply hne
  apply Subgroup.eq_of_le_of_card_ge hN
  rw [h4, Nat.card_zpowers, hr]

theorem exists_dihedral_gens (S : Sylow 2 A) {a₀ b₀ : A} {m : ℕ} (hm : Odd m)
    (hA : Nat.card A = 8 * m) (ha : a₀ * a₀ = 1) (hb : b₀ * b₀ = 1)
    (hr : orderOf (a₀ * b₀) = 4) (hnot : a₀ ∉ Subgroup.zpowers (a₀ * b₀)) :
    ∃ a b : A, a * a = 1 ∧ b * b = 1 ∧ orderOf (a * b) = 4 ∧ a ∉ Subgroup.zpowers (a * b) ∧
      (S : Subgroup A) = Subgroup.closure ({a, b} : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_closure_eq_eight ha hb hr hnot
  have hfac : (Nat.card A).factorization 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two, hA, padicValNat.mul (by norm_num) hm.pos.ne',
      show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by have := Nat.odd_iff.1 hm; omega)]
  let S₀ : Sylow 2 A := Sylow.ofCard (Subgroup.closure ({a₀, b₀} : Set A))
    (by rw [hcard, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S₀ S
  let φ : A ≃* A := MulAut.conj g
  refine ⟨φ a₀, φ b₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ha, map_one]
  · rw [← map_mul, hb, map_one]
  · rw [← map_mul, MulEquiv.orderOf_eq]
    exact hr
  · intro h
    rw [← map_mul] at h
    have h' : φ a₀ ∈ (Subgroup.zpowers (a₀ * b₀)).map φ.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      exact h
    exact hnot ((Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective).1 h')
  · have key : (MulAut.conj g) • Subgroup.closure ({a₀, b₀} : Set A) =
        (Subgroup.closure ({a₀, b₀} : Set A)).map φ.toMonoidHom := by
      ext x
      rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
      exact Iff.rfl
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard, key, MonoidHom.map_closure,
      Set.image_pair]
    rfl

end DihedralSylow

section Main

variable {A L : Type} [Group A] [Finite A] [Group L] [Finite L]

omit [Finite L] in
theorem central_conj_eq {ζ : L} (hζ : ζ ∈ Subgroup.center L) (g : L) : ζ * g * ζ⁻¹ = g := by
  rw [(Subgroup.mem_center_iff.1 hζ g).symm, mul_inv_cancel_right]

omit [Finite L] in
theorem commutatorElement_mul_central_left' {q g ζ : L} (hζ : ζ ∈ Subgroup.center L) :
    ⁅q * ζ, g⁆ = ⁅q, g⁆ := by
  have h1 := central_conj_eq hζ g
  rw [commutatorElement_def, commutatorElement_def]
  calc q * ζ * g * (q * ζ)⁻¹ * g⁻¹ = q * (ζ * g * ζ⁻¹) * q⁻¹ * g⁻¹ := by group
    _ = q * g * q⁻¹ * g⁻¹ := by rw [h1]

omit [Finite L] in
theorem commutatorElement_mul_central_right' {q g ζ : L} (hζ : ζ ∈ Subgroup.center L) :
    ⁅g, q * ζ⁆ = ⁅g, q⁆ := by
  have h1 := central_conj_eq hζ g⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc g * (q * ζ) * g⁻¹ * (q * ζ)⁻¹ = g * q * (ζ * g⁻¹ * ζ⁻¹) * q⁻¹ := by group
    _ = g * q * g⁻¹ * q⁻¹ := by rw [h1]

theorem odd_card_ker [Group.IsPerfect L]
    (γ : A ≃* A) (hγ : ∀ a, γ (γ a) = a)
    (hconj : ∀ s t : A, s * s = 1 → s ≠ 1 → t * t = 1 → t ≠ 1 → ∃ g, g * s * g⁻¹ = t)
    (htwist : ∃ x₀ : A, (x₀⁻¹ * γ x₀) * (x₀⁻¹ * γ x₀) = 1 ∧ x₀⁻¹ * γ x₀ ≠ 1)
    {a₀ b₀ : A} {m : ℕ} (hm : Odd m) (hA : Nat.card A = 8 * m)
    (ha : a₀ * a₀ = 1) (hb : b₀ * b₀ = 1) (hr : orderOf (a₀ * b₀) = 4)
    (hnot : a₀ ∉ Subgroup.zpowers (a₀ * b₀))
    (π : L →* A) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L)
    (α : L ≃* L) (hα : ∀ x, α (α x) = x) (hact : ∀ x, π (α x) = γ (π x))
    (hP : ∃ P : Sylow 2 L, ∀ t ∈ (P : Subgroup L), α t = t) :
    Odd (Nat.card π.ker) := by
  obtain ⟨P₀, hP₀⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have hev : 2 ∣ Nat.card π.ker := by
    rcases Nat.even_or_odd (Nat.card π.ker) with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hodd
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 hev
  set S : Sylow 2 A := P₀.mapSurjective hπ with hSdef
  obtain ⟨a, b, ha', hb', hr', hnot', hS⟩ := exists_dihedral_gens S hm hA ha hb hr hnot
  have hlift := exists_involution_lift_cover γ hγ hconj htwist π hπ hker α hα hact P₀ hP₀
  have ha1 : a ≠ 1 := by
    intro h
    apply hnot'
    rw [h]
    exact Subgroup.one_mem _
  have hb1 : b ≠ 1 := by
    intro h
    apply hnot'
    rw [h, mul_one]
    exact Subgroup.mem_zpowers a
  have h4 : (a * b) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (a * b)
    rwa [hr'] at this
  have h2ne : (a * b) ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hr'] at this
    omega
  have hu2 : (a * b) ^ 2 * (a * b) ^ 2 = 1 := by rw [← pow_add]; exact h4
  obtain ⟨ta, hta2, htaπ⟩ := hlift a ha' ha1
  obtain ⟨tb, htb2, htbπ⟩ := hlift b hb' hb1
  obtain ⟨tu, htu2, htuπ⟩ := hlift ((a * b) ^ 2) hu2 h2ne
  have haS : a ∈ (S : Subgroup A) := hS ▸ Subgroup.subset_closure (by simp)
  have hbS : b ∈ (S : Subgroup A) := hS ▸ Subgroup.subset_closure (by simp)
  have hmapmem : ∀ {g : L}, g * g = 1 → π g ∈ (S : Subgroup A) → g ∈ P₀ := fun {g} hg1 hgS =>
    mem_sylow_of_map_mem π hker P₀ (k := 1) (by rw [pow_one, sq]; exact hg1)
      (hgS : π g ∈ (P₀ : Subgroup L).map π)
  have htaP : ta ∈ P₀ := hmapmem hta2 (by rw [htaπ]; exact haS)
  have htbP : tb ∈ P₀ := hmapmem htb2 (by rw [htbπ]; exact hbS)
  have htuP : tu ∈ P₀ := hmapmem htu2 (by rw [htuπ]; exact pow_mem (mul_mem haS hbS) 2)
  set Q₁ : Subgroup L := Subgroup.closure ({ta, tb} : Set L) with hQ₁
  have hQP : Q₁ ≤ (P₀ : Subgroup L) :=
    (Subgroup.closure_le (P₀ : Subgroup L)).2
      (Set.insert_subset_iff.2 ⟨htaP, Set.singleton_subset_iff.2 htbP⟩)
  have hQmap : Q₁.map π = (S : Subgroup A) := by
    rw [hQ₁, MonoidHom.map_closure, Set.image_pair, htaπ, htbπ, ← hS]
  have hpq : ∀ p ∈ (P₀ : Subgroup L), ∃ q ∈ Q₁, π q = π p := fun p hp => by
    have : π p ∈ Q₁.map π := by
      rw [hQmap]
      exact ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := this
    exact ⟨q, hq, hqp⟩
  have hkerQ : ∀ z ∈ π.ker, z ∈ (P₀ : Subgroup L) → z ∈ Q₁ := by
    intro z hz hzP
    have hcomm := central_element_mem_sylow_derived P₀ ⟨z, hzP⟩ (hker hz)
    have hle : commutator (P₀ : Subgroup L) ≤ Q₁.subgroupOf (P₀ : Subgroup L) := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨q₁, hq₁, hqπ₁⟩ := hpq g₁ g₁.2
      obtain ⟨q₂, hq₂, hqπ₂⟩ := hpq g₂ g₂.2
      have c₁ : q₁⁻¹ * (g₁ : L) ∈ Subgroup.center L :=
        hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hqπ₁, inv_mul_cancel])
      have c₂ : q₂⁻¹ * (g₂ : L) ∈ Subgroup.center L :=
        hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hqπ₂, inv_mul_cancel])
      have e₁ : (g₁ : L) = q₁ * (q₁⁻¹ * g₁) := by group
      have e₂ : (g₂ : L) = q₂ * (q₂⁻¹ * g₂) := by group
      rw [Subgroup.mem_subgroupOf]
      change ⁅(g₁ : L), (g₂ : L)⁆ ∈ Q₁
      rw [e₁, e₂, commutatorElement_mul_central_left' c₁, commutatorElement_mul_central_right' c₂]
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hq₁ hq₂) (inv_mem hq₁)) (inv_mem hq₂)
    exact Subgroup.mem_subgroupOf.1 (hle hcomm)
  have htuQ : tu ∈ Q₁ := by
    obtain ⟨q, hq, hqπ⟩ := hpq tu htuP
    have hc : q⁻¹ * tu ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqπ, inv_mul_cancel]
    have hcP : q⁻¹ * tu ∈ (P₀ : Subgroup L) := mul_mem (inv_mem (hQP hq)) htuP
    have := mul_mem hq (hkerQ _ hc hcP)
    rwa [mul_inv_cancel_left] at this
  have hz₀L : orderOf (z₀ : L) = 2 := by rw [Subgroup.orderOf_coe]; exact hz₀
  have hz₀P : (z₀ : L) ∈ (P₀ : Subgroup L) :=
    mem_sylow_of_central_pow (hker z₀.2) (n := 1) (by
      rw [pow_one]
      have := pow_orderOf_eq_one (z₀ : L)
      rwa [hz₀L] at this) P₀
  have hz₀Q : (z₀ : L) ∈ Q₁ := hkerQ _ z₀.2 hz₀P
  have hodd2 := odd_orderOf_of_mem_closure π hta2 htb2 htu2
    (by rw [map_mul, htaπ, htbπ]; exact hr')
    (by rw [map_mul, htaπ, htbπ]; exact hnot')
    (by rw [htuπ, map_mul, htaπ, htbπ]) htuQ hz₀Q (MonoidHom.mem_ker.1 z₀.2)
  rw [hz₀L] at hodd2
  exact absurd hodd2 (by decide)

end Main

end CFSG.QuasithinUnique.Ch1
