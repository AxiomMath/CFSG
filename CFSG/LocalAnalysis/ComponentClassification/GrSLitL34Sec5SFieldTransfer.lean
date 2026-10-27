module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open Subgroup MulAction

section Transfer

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {B : Type} [CommGroup B]

private theorem pow_eq_of_sq_eq_one {N : Type*} [Monoid N] {b : N} (hb : b ^ 2 = 1) (n : ℕ) :
    b ^ n = if Even n then 1 else b := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [if_pos (even_two_mul k), pow_mul, hb, one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)), pow_succ, pow_mul, hb,
      one_pow, one_mul]

omit [Finite G] in
private theorem transfer_factor_eq
    (hfus : ∀ x ∈ M, orderOf x = 2 → ∀ g : G,
      g⁻¹ * x * g ∈ M → ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m)
    (χ : ↥M →* B) {t : ↥M} (ht : orderOf t = 2) (x : G) (p : ℕ)
    (hx : x⁻¹ * (t : G) ^ p * x ∈ M) :
    χ ⟨x⁻¹ * (t : G) ^ p * x, hx⟩ = χ t ^ p := by
  have ht2 : (t : G) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
  have hχ2 : χ t ^ 2 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  rw [pow_eq_of_sq_eq_one hχ2 p]
  have hpow := pow_eq_of_sq_eq_one ht2 p
  split_ifs at hpow ⊢ with hp
  · have h1 : (⟨x⁻¹ * (t : G) ^ p * x, hx⟩ : ↥M) = 1 := by
      apply Subtype.ext
      show x⁻¹ * (t : G) ^ p * x = 1
      rw [hpow, mul_one, inv_mul_cancel]
    rw [h1, map_one]
  · have htx : x⁻¹ * (t : G) * x ∈ M := hpow ▸ hx
    have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
    obtain ⟨m, hm, hmx⟩ := hfus t t.2 htG x htx
    have h1 : (⟨x⁻¹ * (t : G) ^ p * x, hx⟩ : ↥M) = (⟨m, hm⟩ : ↥M)⁻¹ * t * ⟨m, hm⟩ := by
      apply Subtype.ext
      show x⁻¹ * (t : G) ^ p * x = m⁻¹ * (t : G) * m
      rw [hpow, hmx]
    rw [h1, map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, mul_inv_cancel, one_mul]

end Transfer

theorem hom_eq_one_of_involution_fusion
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    {M : Subgroup G} (hidx : Odd M.index)
    (hfus : ∀ x ∈ M, orderOf x = 2 → ∀ g : G,
      g⁻¹ * x * g ∈ M → ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m)
    {B : Type} [CommGroup B] (χ : ↥M →* B)
    {t : ↥M} (ht : orderOf t = 2) : χ t = 1 := by
  classical
  have htr : MonoidHom.transfer χ (t : G) = 1 :=
    Abelianization.commutator_subset_ker (MonoidHom.transfer χ) Group.IsPerfect.mem_commutator
  have hχ2 : χ t ^ 2 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  let := M.fintypeQuotientOfFiniteIndex
  have hprod := MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot χ (t : G)
  have hfac : ∀ q : Quotient (orbitRel (zpowers (t : G)) (G ⧸ M)),
      χ ⟨q.out.out⁻¹ * (t : G) ^ Function.minimalPeriod ((t : G) • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem M (t : G) q.out⟩ =
        χ t ^ Function.minimalPeriod ((t : G) • ·) q.out :=
    fun q => transfer_factor_eq hfus χ ht _ _ _
  rw [Fintype.prod_congr _ _ hfac, Finset.prod_pow_eq_pow_sum,
    ← Subgroup.index_eq_sum_minimalPeriod, pow_eq_of_sq_eq_one hχ2,
    if_neg (Nat.not_even_iff_odd.mpr hidx)] at hprod
  rw [← hprod, htr]


section Lift

variable {M X : Type} [Group M] [Finite M] [Group X] [Finite X]

omit [Finite X] in
private theorem mem_closure_pair {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {d : X} (hd : d ∈ closure ({a, b} : Set X)) :
    d = 1 ∨ d = a ∨ d = b ∨ d = a * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have key : ∀ x y : X, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) →
      (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
        (x * y = 1 ∨ x * y = a ∨ x * y = b ∨ x * y = a * b) := by
    have hba : b * a = a * b := hab.symm
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
    have h3 : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
    have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, hba, true_or, or_true]
  induction hd using closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy => exact key x y hx hy
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl hai)
    · exact Or.inr (Or.inr (Or.inl hbi))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, hai, hbi, hab]

omit [Finite M] in
private theorem eq_one_of_two_elem_of_odd {K : Subgroup M} (hK : Odd (Nat.card K)) {x : M}
    (hxK : x ∈ K) {n : ℕ} (hx : x ^ 2 ^ n = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card K := K.orderOf_dvd_natCard hxK
  have hcop : Nat.Coprime (2 ^ n) (Nat.card K) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hK)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

omit [Finite M] [Finite X] in
private theorem exists_pair_isPGroup {π : M →* X} {t : M} {vbar : X}
    (hcomm : π t * vbar = vbar * π t) (ht : orderOf t = 2) (hvbar : orderOf vbar = 2) :
    ∃ D : Subgroup X, IsPGroup 2 D ∧ (∀ d ∈ D, ∀ e ∈ D, d * e = e * d) ∧ π t ∈ D ∧ vbar ∈ D := by
  have hπt2 : π t * π t = 1 := by rw [← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  have hv2 : vbar * vbar = 1 := by rw [← pow_two, ← hvbar, pow_orderOf_eq_one]
  set D : Subgroup X := closure ({π t, vbar} : Set X)
  have hDsq : ∀ d ∈ D, d * d = 1 := by
    intro d hd
    rcases mem_closure_pair hπt2 hv2 hcomm hd with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact hπt2
    · exact hv2
    · calc π t * vbar * (π t * vbar) = π t * (vbar * π t) * vbar := by group
        _ = π t * (π t * vbar) * vbar := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, hπt2, one_mul, hv2]
  refine ⟨D, fun d => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hDsq d d.2)⟩,
    fun d hd e he => ?_, subset_closure (Set.mem_insert _ _),
    subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right (hDsq d hd)
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hDsq e he)
  calc d * e = (d * e)⁻¹ := (inv_eq_of_mul_eq_one_right (hDsq _ (mul_mem hd he))).symm
    _ = e * d := by rw [mul_inv_rev, hdi, hei]

end Lift

theorem exists_involution_lift_centralizing
    {M X : Type} [Group M] [Finite M] [Group X] [Finite X]
    (π : M →* X) (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker))
    {t : M} (ht : orderOf t = 2) {vbar : X}
    (hvbar : orderOf vbar = 2) (hcomm : π t * vbar = vbar * π t) :
    ∃ v : M, orderOf v = 2 ∧ t * v = v * t ∧ π v = vbar := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD2, hDc, htD, hvD⟩ := exists_pair_isPGroup hcomm ht hvbar
  set H : Subgroup M := D.comap π with hH
  let ψ : ↥H →* ↥D := (π.comp H.subtype).codRestrict D fun h => h.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨d, hd⟩
    obtain ⟨m, rfl⟩ := hπ d
    exact ⟨⟨m, hd⟩, rfl⟩
  have htH : t ∈ H := htD
  have hz : IsPGroup 2 (zpowers (⟨t, htH⟩ : ↥H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
  obtain ⟨T, hT⟩ := hz.exists_le_sylow
  have htT : (⟨t, htH⟩ : ↥H) ∈ (T : Subgroup ↥H) := hT (mem_zpowers _)
  have hTD : (T : Subgroup ↥H).map ψ = ⊤ := by
    have h := (T.mapSurjective hψ).is_maximal' (hD2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  set φ : ↥(T : Subgroup ↥H) →* ↥D := ψ.comp (T : Subgroup ↥H).subtype with hφ
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, hn⟩ := T.isPGroup' x
    have hxK : (((x : ↥H) : M)) ∈ π.ker := congrArg Subtype.val hx
    have hx' : (((x : ↥H) : M)) ^ 2 ^ n = 1 := by
      simpa using congrArg (fun y : ↥(T : Subgroup ↥H) => ((y : ↥H) : M)) hn
    exact Subtype.ext (Subtype.ext (eq_one_of_two_elem_of_odd hodd hxK hx'))
  obtain ⟨w, hwT, hw⟩ := (hTD ▸ mem_top (⟨vbar, hvD⟩ : ↥D) :
    (⟨vbar, hvD⟩ : ↥D) ∈ (T : Subgroup ↥H).map ψ)
  refine ⟨((w : ↥H) : M), ?_, ?_, congrArg Subtype.val hw⟩
  · have h1 := orderOf_injective φ hφi ⟨w, hwT⟩
    have h2 : φ ⟨w, hwT⟩ = ⟨vbar, hvD⟩ := hw
    rw [h2, Subgroup.orderOf_mk, hvbar, Subgroup.orderOf_mk] at h1
    rw [Subgroup.orderOf_coe, h1]
  · have h1 : φ (⟨⟨t, htH⟩, htT⟩ * ⟨w, hwT⟩) = φ (⟨w, hwT⟩ * ⟨⟨t, htH⟩, htT⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext (hDc _ (φ _).2 _ (φ _).2)
    exact congrArg (fun y : ↥(T : Subgroup ↥H) => ((y : ↥H) : M)) (hφi h1)


end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
