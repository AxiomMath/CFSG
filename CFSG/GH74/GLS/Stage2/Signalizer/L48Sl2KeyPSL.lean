module

public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2KeyTorus

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open CFSG.PSL2Table Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F]

theorem isTorus_splitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    IsTorus (splitTorus F) := by
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_splitTorus hF hq
  exact ⟨fun x hx y hy => splitTorus_mul_comm hx hy,
    fun x hx hx1 g hg => (splitTorus_TI hF hq x hx hx1 g).mp hg,
    ⟨splitWeyl F, splitWeyl_not_mem, splitWeyl_mul_self, fun x hx => splitWeyl_conj hx,
      mem_normalizer_iff_of_TI splitWeyl_mul_self (fun y hy => splitWeyl_conj hy) hx₀
        (splitTorus_conj_mem_iff hx₀ hx₀1)⟩⟩

theorem isTorus_nonsplitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) : IsTorus (nonsplitTorus ν) := by
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_nonsplitTorus hF hq hν
  obtain ⟨w, hw, hw2, hinv, hTI⟩ := exists_nonsplitWeyl hF hν
  exact ⟨fun x hx y hy => nonsplitTorus_mul_comm hx hy,
    fun x hx hx1 g hg => (nonsplitTorus_TI hF hq hν x hx hx1 g).mp hg,
    ⟨w, hw, hw2, hinv, mem_normalizer_iff_of_TI hw2 hinv hx₀ (hTI x₀ hx₀ hx₀1)⟩⟩

theorem card_nonsplitTorus_eq (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    Nat.card (nonsplitTorus ν) = Nat.card (splitTorus F) + 1 := by
  have h2 := Ring.two_ne_zero hF
  have hT := card_splitTorus h2 (F := F)
  have hS := card_nonsplitTorus hF hν
  have := Fintype.one_lt_card (α := F)
  omega

theorem two_le_card_splitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    2 ≤ Nat.card (splitTorus F) := by
  have hT := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  omega

theorem exists_torus_of_not_conjSet (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {y : PSL(2, F)} (hy1 : y ≠ 1) (hyP : y ∉ conjSet (unipotent F)) :
    ∃ H : Subgroup PSL(2, F), IsTorus H ∧ y ∈ H ∧
      (Nat.card H = Nat.card (splitTorus F) ∨ Nat.card H = Nat.card (splitTorus F) + 1) := by
  classical
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  rcases mem_conjSet_cases hF hq hν y with h | h | h | h
  · exact absurd h hy1
  · exact absurd h hyP
  · obtain ⟨-, k, hk⟩ := h
    refine ⟨(splitTorus F).map (MulAut.conj k⁻¹).toMonoidHom,
      (isTorus_splitTorus hF hq).conj _, ?_, Or.inl ?_⟩
    · rw [Subgroup.mem_map_equiv]
      simpa using hk
    · exact Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  · obtain ⟨-, k, hk⟩ := h
    refine ⟨(nonsplitTorus ν).map (MulAut.conj k⁻¹).toMonoidHom,
      (isTorus_nonsplitTorus hF hq hν).conj _, ?_, Or.inr ?_⟩
    · rw [Subgroup.mem_map_equiv]
      simpa using hk
    · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
      exact card_nonsplitTorus_eq hF hν

theorem exists_torus_involution (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {a : PSL(2, F)} (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ H : Subgroup PSL(2, F), IsTorus H ∧ a ∈ H ∧
      (Nat.card H = Nat.card (splitTorus F) ∨ Nat.card H = Nat.card (splitTorus F) + 1) := by
  refine exists_torus_of_not_conjSet hF hq ha1 fun h => ?_
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hdvd := orderOf_dvd_of_mem_conjSet h
  rw [hord, card_unipotent (Ring.two_ne_zero hF)] at hdvd
  have := FiniteField.odd_card_of_char_ne_two hF
  omega

theorem not_dvd_borel_card {t x : ℕ} (ht : 2 ≤ t) (hx : x = t ∨ x = t + 1) :
    ¬ 2 * x ∣ t * (2 * t + 1) := by
  intro hd
  rcases hx with rfl | rfl
  · have h1 : x * 2 ∣ x * (2 * x + 1) := by rwa [mul_comm x 2]
    have := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
    omega
  · have h1 : 2 * (t + 1) ∣ t * (2 * t + 1) + t := by
      have : t * (2 * t + 1) + t = (2 * (t + 1)) * t := by ring
      rw [this]
      exact dvd_mul_right _ _
    have h2 := (Nat.dvd_add_right hd).mp h1
    have := Nat.le_of_dvd (by omega) h2
    omega

theorem eq_bot_of_char {p : ℕ} [Fact p.Prime] (hpF : ringChar F = p) (hF : ringChar F ≠ 2)
    {a : PSL(2, F)} (ha2 : a * a = 1) (ha1 : a ≠ 1) {Y : Subgroup PSL(2, F)} (hY : IsPGroup p Y)
    (hN : ∀ c : PSL(2, F), c * a = a * c → c ∈ normalizer (Y : Set PSL(2, F))) : Y = ⊥ := by
  classical
  by_contra hYb
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [Subgroup.eq_bot_iff_forall] at hYb
  push Not at hYb
  obtain ⟨y₁, hy₁Y, hy₁1⟩ := hYb
  have : CharP F p := hpF ▸ ringChar.charP F
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨Q, hYQ⟩ := hY.exists_le_sylow
  obtain ⟨c, hc⟩ := CFSG.GH74.GLS.IVK.L2Borel.exists_conj_eq_unipotent hcard Q
  have hy₁Q : y₁ ∈ (unipotent F).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]
    exact hYQ hy₁Y
  rw [Subgroup.mem_map_equiv] at hy₁Q
  have hxP : c⁻¹ * y₁ * c ∈ unipotent F := by simpa using hy₁Q
  have hx1 : c⁻¹ * y₁ * c ≠ 1 := by
    intro h
    apply hy₁1
    have := congrArg (fun z => c * z * c⁻¹) h
    simpa [mul_assoc] using this
  have hDB : centralizer {a} ≤ (borel F).map (MulAut.conj c).toMonoidHom := by
    intro d hd
    rw [mem_centralizer_singleton_iff] at hd
    have hdy : d * y₁ * d⁻¹ ∈ Y := (mem_normalizer_iff.mp (hN d hd) y₁).mp hy₁Y
    have hdQ : d * y₁ * d⁻¹ ∈ (unipotent F).map (MulAut.conj c).toMonoidHom := by
      rw [← hc]
      exact hYQ hdy
    rw [Subgroup.mem_map_equiv] at hdQ ⊢
    simp only [MulAut.conj_symm_apply] at hdQ ⊢
    have key : (c⁻¹ * d * c) * (c⁻¹ * y₁ * c) * (c⁻¹ * d * c)⁻¹ ∈ unipotent F := by
      have : (c⁻¹ * d * c) * (c⁻¹ * y₁ * c) * (c⁻¹ * d * c)⁻¹ = c⁻¹ * (d * y₁ * d⁻¹) * c := by
        group
      rw [this]
      exact hdQ
    exact (unipotent_TI hF _ hxP hx1 (c⁻¹ * d * c)).mp key
  have haD : a ∈ centralizer {a} := mem_centralizer_singleton_iff.mpr rfl
  have hcardB : Nat.card ((borel F).map (MulAut.conj c).toMonoidHom) = Nat.card (borel F) :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hB2 := card_borel h2 (F := F)
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hq1 := Fintype.one_lt_card (α := F)
  by_cases hq5 : 5 ≤ Fintype.card F
  · obtain ⟨H, hH, haH, hcardH⟩ := exists_torus_involution hF hq5 ha2 ha1
    have hdvd : Nat.card (centralizer {a} : Subgroup PSL(2, F)) ∣ Nat.card (borel F) := by
      have := Subgroup.card_dvd_of_le hDB
      rwa [hcardB] at this
    rw [hH.card_centralizer haH ha1 ha2] at hdvd
    have hT := card_splitTorus h2 (F := F)
    have ht := two_le_card_splitTorus hF hq5
    have hq' : Fintype.card F = 2 * Nat.card (splitTorus F) + 1 := by omega
    have hB : Nat.card (borel F) =
        Nat.card (splitTorus F) * (2 * Nat.card (splitTorus F) + 1) := by
      have h1 : Fintype.card F - 1 = Nat.card (splitTorus F) * 2 := by omega
      rw [h1, hq'] at hB2
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (by rw [hB2]; ring)
    rw [hB] at hdvd
    exact not_dvd_borel_card ht hcardH hdvd
  · have hq3 : Fintype.card F = 3 := by omega
    rw [hq3] at hB2
    have h2B : 2 ∣ Nat.card (borel F) := by
      have := Subgroup.orderOf_dvd_natCard _ (hDB haD)
      rwa [hord, hcardB] at this
    omega

theorem psl2Key {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : ringChar F ≠ 2) {a : PSL(2, F)}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) {Y : Subgroup PSL(2, F)} (hY : IsPGroup p Y)
    (hN : ∀ c : PSL(2, F), c * a = a * c → c ∈ normalizer (Y : Set PSL(2, F))) :
    ∀ y ∈ Y, y * a = a * y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hYb : Y = ⊥
  · intro y hy
    rw [hYb, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  by_cases hpq : p ∣ Fintype.card F
  · have hpF : ringChar F = p := by
      obtain ⟨n, hpr, hn⟩ := FiniteField.card F (ringChar F)
      have : p ∣ ringChar F ^ (n : ℕ) := hn ▸ hpq
      exact ((Nat.prime_dvd_prime_iff_eq hp hpr).mp (hp.dvd_of_dvd_pow this)).symm
    exact absurd (eq_bot_of_char hpF hF ha2 ha1 hY hN) hYb
  have hpc2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hpcq : p.Coprime (Fintype.card F) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  obtain ⟨y₀, hy₀Y, hy₀Z, hy₀1, hord⟩ : ∃ y₀ ∈ Y, (∀ y ∈ Y, y * y₀ = y₀ * y) ∧ y₀ ≠ 1 ∧
      ∀ n : ℕ, p.Coprime n → (orderOf y₀).Coprime n := by
    have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYb
    have := hY.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center Y)
    refine ⟨((z : Y) : PSL(2, F)), (z : Y).2, fun y hy => ?_, fun h => hz1 ?_, fun n hn => ?_⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    · apply Subtype.ext
      apply Subtype.ext
      simpa using h
    · rw [Subgroup.orderOf_coe]
      exact hY.orderOf_coprime hn _
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hq1 := Fintype.one_lt_card (α := F)
  by_cases hq5 : 5 ≤ Fintype.card F
  · have hy₀2 : y₀ * y₀ ≠ 1 := by
      intro h
      have h1 : orderOf y₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
      exact hy₀1 (orderOf_eq_one_iff.mp ((hord 2 hpc2).eq_one_of_dvd h1))
    have hy₀P : y₀ ∉ conjSet (unipotent F) := by
      intro h
      have h1 := orderOf_dvd_of_mem_conjSet h
      rw [card_unipotent (Ring.two_ne_zero hF)] at h1
      exact hy₀1 (orderOf_eq_one_iff.mp ((hord _ hpcq).eq_one_of_dvd h1))
    obtain ⟨H₀, hH₀, hy₀H, hcard₀⟩ := exists_torus_of_not_conjSet hF hq5 hy₀1 hy₀P
    obtain ⟨Ha, hHa, haH, hcardA⟩ := exists_torus_involution hF hq5 ha2 ha1
    exact key_of_torus (two_le_card_splitTorus hF hq5) ha2 ha1 hHa haH hcardA hy₀Y hy₀2 hy₀Z hH₀
      hy₀H hcard₀ hN
  · exfalso
    have hq3 : Fintype.card F = 3 := by omega
    have hG := card_PSL (Ring.two_ne_zero hF) (F := F)
    rw [hq3] at hG
    have hG12 : Nat.card PSL(2, F) = 12 := by omega
    have hdvd : orderOf y₀ ∣ 12 := hG12 ▸ orderOf_dvd_natCard y₀
    have h4 : (orderOf y₀).Coprime 4 := by
      have := (hord 2 hpc2).pow_right 2
      simpa using this
    have h3 : (orderOf y₀).Coprime 3 := hq3 ▸ hord _ hpcq
    have hcop : (orderOf y₀).Coprime 12 := by
      have := h4.mul_right h3
      simpa using this
    exact hy₀1 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd))

end CFSG.GH74.GLS.Stage2.Signalizer.L48
