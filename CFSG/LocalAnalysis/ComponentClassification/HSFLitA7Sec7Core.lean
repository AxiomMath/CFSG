module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Local

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

private theorem odd_card_oddCore' (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  have h := LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← CFSG.oddCore_eq_piCore] at h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  exact h ⟨2, Nat.prime_two⟩ h2 rfl

theorem oddCoreIn_le_centralizer {E N : Subgroup X} (hEN : E ≤ N)
    (hNE : N ≤ normalizer (E : Set X)) (hE : ∀ e ∈ E, e ^ 2 = 1) :
    A7Base.oddCoreIn N ≤ centralizer (E : Set X) := by
  rintro _ ⟨o, ho, rfl⟩
  rw [mem_centralizer_iff]
  intro e he
  set e' : N := ⟨e, hEN he⟩ with he'
  set c : N := o * e' * o⁻¹ * e'⁻¹ with hc
  have hcO : c ∈ CFSG.oddCore N := by
    have h1 : e' * o⁻¹ * e'⁻¹ ∈ CFSG.oddCore N :=
      (CFSG.oddCore_normal N).conj_mem _ (inv_mem ho) e'
    have := mul_mem ho h1
    rwa [show o * (e' * o⁻¹ * e'⁻¹) = c by rw [hc]; group] at this
  have hcX : (c : X) = (o : X) * e * (o : X)⁻¹ * e⁻¹ := by rw [hc]; rfl
  have hcE : (c : X) ∈ E := by
    have h1 : (o : X) * e * (o : X)⁻¹ ∈ E := (mem_normalizer_iff.mp (hNE o.2) e).mp he
    rw [hcX]; exact mul_mem h1 (inv_mem he)
  have hc2 : c ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE _ hcE)
  have hodd : Odd (orderOf c) := by
    have h1 := orderOf_dvd_natCard (⟨c, hcO⟩ : CFSG.oddCore N)
    rw [Subgroup.orderOf_mk] at h1
    exact (odd_card_oddCore' N).of_dvd_nat h1
  have h1 : orderOf c = 1 := by
    have h2 := orderOf_dvd_of_pow_eq_one hc2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have hc1 : (c : X) = 1 := by rw [orderOf_eq_one_iff.mp h1]; rfl
  rw [hcX] at hc1
  have := mul_inv_eq_one.mp hc1
  calc e * (o : X) = (o : X) * e * (o : X)⁻¹ * (o : X) := by rw [this]
    _ = (o : X) * e := by group

omit [Finite X] in
theorem exists_pow_mem_oddCoreIn [Finite X] {N : Subgroup X} {κ : X}
    (hκ : κ ∈ A7Base.oddTwoCoreIn N) :
    ∃ a : ℕ, κ ^ (2 ^ a) ∈ A7Base.oddCoreIn N := by
  obtain ⟨n, hn, rfl⟩ := hκ
  have hn' : QuotientGroup.mk' (CFSG.oddCore N) n ∈ CFSG.pCore 2 (N ⧸ CFSG.oddCore N) := hn
  have hp : IsPGroup 2 (CFSG.pCore 2 (N ⧸ CFSG.oddCore N)) := CFSG.pCore_isPGroup
  obtain ⟨a, ha⟩ := hp ⟨_, hn'⟩
  refine ⟨a, ⟨n ^ (2 ^ a), ?_, by simp⟩⟩
  show n ^ (2 ^ a) ∈ CFSG.oddCore N
  rw [← QuotientGroup.eq_one_iff]
  have := congrArg Subtype.val ha
  simpa using this

omit [Finite X] in
theorem conj_mem_oddTwoCoreIn {N : Subgroup X} {m κ : X} (hm : m ∈ N)
    (hκ : κ ∈ A7Base.oddTwoCoreIn N) : m * κ * m⁻¹ ∈ A7Base.oddTwoCoreIn N := by
  obtain ⟨n, hn, rfl⟩ := hκ
  have hn' : QuotientGroup.mk' (CFSG.oddCore N) n ∈ CFSG.pCore 2 (N ⧸ CFSG.oddCore N) := hn
  refine ⟨⟨m, hm⟩ * n * ⟨m, hm⟩⁻¹, ?_, by simp⟩
  show QuotientGroup.mk' (CFSG.oddCore N) (⟨m, hm⟩ * n * ⟨m, hm⟩⁻¹) ∈
    CFSG.pCore 2 (N ⧸ CFSG.oddCore N)
  rw [map_mul, map_mul, map_inv]
  exact (CFSG.pCore_normal (p := 2) (G := N ⧸ CFSG.oddCore N)).conj_mem _ hn' _

variable {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X} {yi ki ui : X}

theorem card_S₁_le (h : IsRefl F yi) (D : S.Sec6 T₁ yi ki ui) : Nat.card D.S₁ ≤ 256 := by
  set N := normalizer (S.E yi : Set X) with hN
  set Ce := centralizer (S.E yi : Set X) with hCe
  obtain ⟨e⟩ := D.automizer
  have hcardQ : Nat.card (N ⧸ Ce.subgroupOf N) = 48 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  let φ : D.S₁ →* (N ⧸ Ce.subgroupOf N) :=
    (QuotientGroup.mk' (Ce.subgroupOf N)).comp (Subgroup.inclusion D.S₁_le)
  have hrange : Nat.card φ.range ≤ 16 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 φ.range :=
      D.isPGroup_S₁.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp
    have hdvd := Subgroup.card_subgroup_dvd_card φ.range
    rw [hcardQ, hm] at hdvd
    rw [hm]
    have h16 : 2 ^ m ∣ 2 ^ 4 := by
      have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
      rw [h48] at hdvd
      exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (by norm_num)) hdvd
    exact Nat.le_of_dvd (by norm_num) h16
  have hker : Nat.card φ.ker ≤ 16 := by
    have hle : φ.ker.map D.S₁.subtype ≤ S.E yi := by
      refine le_E_of_le_centralizer h ((D.isPGroup_S₁.to_subgroup φ.ker).map D.S₁.subtype) ?_
      rintro _ ⟨s, hs, rfl⟩
      have hs' : (Subgroup.inclusion D.S₁_le s : N) ∈ Ce.subgroupOf N := by
        have hs1 : φ s = 1 := hs
        exact (QuotientGroup.eq_one_iff _).mp hs1
      exact hs'
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective D.S₁.subtype_injective, h.card_E] at this
    exact this
  have hmul := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hmul
  rw [← hmul]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 16 * 16 := Nat.mul_le_mul hker hrange
    _ = 256 := by norm_num

theorem u_not_mem_Q₁ (h : IsRefl F yi) (D : S.Sec6 T₁ yi ki ui) : D.u ∉ D.Q₁ := by
  intro hu
  rw [D.Q₁_eq] at hu
  set N := normalizer (S.E yi : Set X) with hN
  have huK : D.u ∈ A7Base.oddTwoCoreIn N := hu.2
  have hdN : D.d ∈ N := D.d_mem.1
  set κ := D.u * D.d * D.u⁻¹ * D.d⁻¹ with hκ
  have hκK : κ ∈ A7Base.oddTwoCoreIn N := by
    have h1 : D.d * D.u⁻¹ * D.d⁻¹ ∈ A7Base.oddTwoCoreIn N :=
      conj_mem_oddTwoCoreIn hdN (inv_mem huK)
    have := mul_mem huK h1
    rwa [show D.u * (D.d * D.u⁻¹ * D.d⁻¹) = κ by rw [hκ]; group] at this
  have hc : D.d ^ 3 * (D.u * D.d * D.u⁻¹ * D.d)⁻¹ ∈ centralizer (S.E yi : Set X) :=
    mul_mem D.d_cube (inv_mem D.u_inv_d)
  have hd : D.d = (D.d ^ 3 * (D.u * D.d * D.u⁻¹ * D.d)⁻¹) * κ := by rw [hκ]; group
  have hκN : κ ∈ N := by
    obtain ⟨n, -, hn⟩ := hκK
    rw [← hn]; exact n.2
  have hE2 : ∀ e ∈ S.E yi, e ^ 2 = 1 := fun e he => h.elemAbelianTwo_E.sq_eq_one e he
  have hκE : ∀ e ∈ S.E yi, κ * e * κ⁻¹ ∈ S.E yi := fun e he =>
    (mem_normalizer_iff.mp hκN e).mp he
  have hact : ∀ e ∈ S.E yi, D.d * e * D.d⁻¹ = κ * e * κ⁻¹ := by
    intro e he
    set c' := D.d ^ 3 * (D.u * D.d * D.u⁻¹ * D.d)⁻¹ with hc'
    have h1 : c' * (κ * e * κ⁻¹) * c'⁻¹ = κ * e * κ⁻¹ := by
      have := mem_centralizer_iff.mp hc _ (hκE e he)
      rw [← this, mul_inv_cancel_right]
    calc D.d * e * D.d⁻¹ = c' * (κ * e * κ⁻¹) * c'⁻¹ := by
          conv_lhs => rw [hd]
          group
      _ = κ * e * κ⁻¹ := h1
  have hpow : ∀ n : ℕ, ∀ e ∈ S.E yi, D.d ^ n * e * (D.d ^ n)⁻¹ = κ ^ n * e * (κ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro e _; simp
    | succ n ih =>
      intro e he
      calc D.d ^ (n + 1) * e * (D.d ^ (n + 1))⁻¹ = D.d ^ n * (D.d * e * D.d⁻¹) * (D.d ^ n)⁻¹ := by
            rw [pow_succ]; group
        _ = D.d ^ n * (κ * e * κ⁻¹) * (D.d ^ n)⁻¹ := by rw [hact e he]
        _ = κ ^ n * (κ * e * κ⁻¹) * (κ ^ n)⁻¹ := ih _ (hκE e he)
        _ = κ ^ (n + 1) * e * (κ ^ (n + 1))⁻¹ := by rw [pow_succ]; group
  obtain ⟨a, ha⟩ := exists_pow_mem_oddCoreIn hκK
  have hO := oddCoreIn_le_centralizer (E := S.E yi) (N := N) (le_normalizer) le_rfl hE2 ha
  have hd2 : D.d ^ (2 ^ a) ∈ centralizer (S.E yi : Set X) := by
    rw [mem_centralizer_iff]
    intro e he
    have h1 := hpow (2 ^ a) e he
    have h2 := mem_centralizer_iff.mp hO e he
    rw [← h2, mul_inv_cancel_right] at h1
    calc e * D.d ^ 2 ^ a = D.d ^ 2 ^ a * e * (D.d ^ 2 ^ a)⁻¹ * D.d ^ 2 ^ a := by rw [h1]
      _ = D.d ^ 2 ^ a * e := by group
  apply D.d_not_mem
  have hcop : Nat.Coprime (2 ^ a) 3 := Nat.Coprime.pow_left a (by norm_num)
  have hg := Nat.gcd_eq_gcd_ab (2 ^ a) 3
  rw [Nat.Coprime.gcd_eq_one hcop] at hg
  have h1 : (1 : ℤ) = ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) 3 + ((3 : ℕ) : ℤ) * Nat.gcdB (2 ^ a) 3 :=
    by exact_mod_cast hg
  have : D.d = (D.d ^ (2 ^ a)) ^ (Nat.gcdA (2 ^ a) 3) * (D.d ^ 3) ^ (Nat.gcdB (2 ^ a) 3) := by
    calc D.d = D.d ^ (1 : ℤ) := (zpow_one _).symm
      _ = D.d ^ (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) 3 + ((3 : ℕ) : ℤ) * Nat.gcdB (2 ^ a) 3) := by
        rw [← h1]
      _ = _ := by rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [this]
  exact mul_mem (zpow_mem hd2 _) (zpow_mem D.d_cube _)

theorem card_Q₁_le (h : IsRefl F yi) (D : S.Sec6 T₁ yi ki ui) : Nat.card D.Q₁ ≤ 128 := by
  have hle : D.Q₁ ≤ D.S₁ := by rw [D.Q₁_eq]; exact inf_le_left
  have huS : D.u ∈ D.S₁ := by rw [D.S₁_eq]; exact mem_sup_right (mem_zpowers _)
  have hmul := Subgroup.relIndex_mul_card D.Q₁ D.S₁
  rw [inf_eq_left.mpr hle] at hmul
  have hne : D.Q₁.relIndex D.S₁ ≠ 1 := fun h1 =>
    u_not_mem_Q₁ h D (Subgroup.relIndex_eq_one.mp h1 huS)
  have hne0 : D.Q₁.relIndex D.S₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact (Nat.card_pos (α := D.S₁)).ne' hmul.symm
  have h2 : 2 ≤ D.Q₁.relIndex D.S₁ := by omega
  have := card_S₁_le h D
  nlinarith

end Sec7

end CFSG.ComponentClassification.HSFLit
