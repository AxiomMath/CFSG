module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup

theorem commutator_eq_bot_of_comm {Q : Type*} [Group Q] {P : Subgroup Q}
    (h : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : ⁅P, P⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  exact h b hb a ha

theorem commutator_commutator_eq_bot_of_card_dvd_six {Q : Type*} [Group Q] [Finite Q]
    (h : Nat.card Q ∣ 6) : ⁅commutator Q, commutator Q⁆ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Q) := inferInstance
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hP3 : Nat.card P ∣ 3 := by
    rw [P.card_eq_multiplicity]
    have h3 : (Nat.card Q).factorization 3 ≤ 1 := by
      by_contra hc
      push Not at hc
      have : 3 ^ 2 ∣ Nat.card Q := (Nat.pow_dvd_pow 3 hc).trans (Nat.ordProj_dvd _ _)
      exact absurd (this.trans h) (by norm_num)
    exact (Nat.pow_dvd_pow 3 h3).trans (by norm_num)
  have hidx : (P : Subgroup Q).index ∣ 2 := by
    have hmul := (P : Subgroup Q).card_mul_index
    rcases (Nat.dvd_prime Nat.prime_three).1 hP3 with h1 | h1
    ·
      have hn3 : ¬ 3 ∣ Nat.card Q := fun h3 => by
        have := P.dvd_card_of_dvd_card h3
        rw [h1] at this
        exact absurd this (by norm_num)
      have h2 : Nat.card Q ∣ 2 := by
        have h6 : Nat.card Q ∣ 2 * 3 := h
        exact (Nat.Coprime.dvd_of_dvd_mul_right
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn3).symm h6)
      rw [h1, one_mul] at hmul
      rw [hmul]
      exact h2
    · rw [h1] at hmul
      have : 3 * (P : Subgroup Q).index ∣ 3 * 2 := hmul ▸ h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hPn : (P : Subgroup Q).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  have hle : commutator Q ≤ P := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      exact le_top
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hc : Nat.card (Q ⧸ (P : Subgroup Q)) = 2 := by rw [← Subgroup.index_eq_card, h2]
      have : IsCyclic (Q ⧸ (P : Subgroup Q)) := isCyclic_of_prime_card hc
      have := Abelianization.commutator_subset_ker (QuotientGroup.mk' (P : Subgroup Q))
      rwa [QuotientGroup.ker_mk'] at this
  have hPc : ∀ a ∈ (P : Subgroup Q), ∀ b ∈ (P : Subgroup Q), a * b = b * a := by
    intro a ha b hb
    rcases (Nat.dvd_prime Nat.prime_three).1 hP3 with h1 | h3
    · have hbot : (P : Subgroup Q) = ⊥ := Subgroup.card_eq_one.mp h1
      rw [hbot, Subgroup.mem_bot] at hb
      rw [hb, mul_one, one_mul]
    · have : IsCyclic P := isCyclic_of_prime_card h3
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : P) ⟨b, hb⟩)
  rw [eq_bot_iff, ← commutator_eq_bot_of_comm hPc]
  exact commutator_mono hle hle

theorem commutator_commutator_le_of_relIndex_dvd_six {G : Type*} [Group G] {H N F : Subgroup G}
    [Finite H] (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (h6 : N.relIndex H ∣ 6)
    (hFH : F ≤ H) : ⁅⁅F, F⁆, ⁅F, F⁆⁆ ≤ N := by
  set Q := H ⧸ N.subgroupOf H
  have hQ : Nat.card Q ∣ 6 := by
    rw [← Subgroup.index_eq_card]
    exact h6
  have hbot := commutator_commutator_eq_bot_of_card_dvd_six hQ
  rw [commutator_def] at hbot
  have hle : ⁅⁅F.subgroupOf H, F.subgroupOf H⁆, ⁅F.subgroupOf H, F.subgroupOf H⁆⁆ ≤
      N.subgroupOf H := by
    rw [← QuotientGroup.ker_mk' (N.subgroupOf H), ← MonoidHom.comap_bot,
      ← Subgroup.map_le_iff_le_comap]
    simp only [Subgroup.map_commutator]
    rw [← hbot]
    exact commutator_mono (commutator_mono le_top le_top) (commutator_mono le_top le_top)
  have hmap := Subgroup.map_mono (f := H.subtype) hle
  simp only [Subgroup.map_commutator] at hmap
  rwa [Subgroup.map_subgroupOf_eq_of_le hFH, Subgroup.map_subgroupOf_eq_of_le hNH] at hmap

theorem isMulCommutative_of_card_dvd_four {E : Type*} [Group E] [Finite E]
    (h : Nat.card E ∣ 4) : IsMulCommutative E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : Nat.card E ∣ 2 ^ 2 := h
  obtain ⟨k, hk, hE⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
  interval_cases k
  · have : Subsingleton E := (Nat.card_eq_one_iff_unique.mp (by simpa using hE)).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : IsCyclic E := isCyclic_of_prime_card (p := 2) (by simpa using hE)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hE

theorem not_mem_commutator_of_card_dvd_twelve {E : Type*} [Group E] [Finite E]
    (h12 : Nat.card E ∣ 12) {z : E} (hz : orderOf z = 2) (hzc : z ∈ center E) :
    z ∉ commutator E := by
  by_cases h3 : 3 ∣ Nat.card E
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P⟩ : Nonempty (Sylow 3 E) := inferInstance
    have hE0 : Nat.card E ≠ 0 := Nat.card_pos.ne'
    have hP3 : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity]
      have h1 : (Nat.card E).factorization 3 = 1 := by
        apply le_antisymm
        · by_contra hc
          push Not at hc
          have : 3 ^ 2 ∣ Nat.card E := (Nat.pow_dvd_pow 3 hc).trans (Nat.ordProj_dvd _ _)
          exact absurd (this.trans h12) (by norm_num)
        · exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hE0).1 h3
      rw [h1, pow_one]
    have hzN : z ∈ normalizer ((P : Subgroup E) : Set E) := by
      rw [mem_normalizer_iff]
      intro h
      rw [show z * h * z⁻¹ = h by rw [(mem_center_iff.mp hzc h).symm, mul_inv_cancel_right]]
    have h6 : 2 * 3 ∣ Nat.card (normalizer ((P : Subgroup E) : Set E)) := by
      have h3' : 3 ∣ Nat.card (normalizer ((P : Subgroup E) : Set E)) := by
        have := Subgroup.card_dvd_of_le (le_normalizer (H := (P : Subgroup E)))
        rwa [hP3] at this
      have h2' : 2 ∣ Nat.card (normalizer ((P : Subgroup E) : Set E)) :=
        hz ▸ Subgroup.orderOf_dvd_natCard _ hzN
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2' h3'
    have hidx : (normalizer ((P : Subgroup E) : Set E)).index ∣ 2 := by
      have hmul := (normalizer ((P : Subgroup E) : Set E)).card_mul_index
      obtain ⟨k, hk⟩ := h6
      rw [hk] at hmul
      have : 2 * 3 * (k * (normalizer ((P : Subgroup E) : Set E)).index) ∣ 2 * 3 * 2 := by
        rw [← mul_assoc, hmul]
        exact h12
      exact (dvd_mul_left _ _).trans (Nat.dvd_of_mul_dvd_mul_left (by norm_num) this)
    have hcount0 := card_sylow_modEq_one (p := 3) (G := E)
    rw [Sylow.card_eq_index_normalizer P] at hcount0
    have hcount : (normalizer ((P : Subgroup E) : Set E)).index ≡ 1 [MOD 3] := hcount0
    have hidx1 : (normalizer ((P : Subgroup E) : Set E)).index = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
      · exact h
      · rw [h] at hcount
        exact absurd hcount (by decide)
    have hPn : (P : Subgroup E).Normal := by
      rw [Subgroup.index_eq_one] at hidx1
      exact normalizer_eq_top_iff.mp hidx1
    have hQ : Nat.card (E ⧸ (P : Subgroup E)) ∣ 4 := by
      rw [← Subgroup.index_eq_card]
      have hmul := (P : Subgroup E).card_mul_index
      rw [hP3] at hmul
      have : 3 * (P : Subgroup E).index ∣ 3 * 4 := hmul ▸ h12
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have := isMulCommutative_of_card_dvd_four hQ
    have hle : commutator E ≤ (P : Subgroup E) := by
      have := Abelianization.commutator_subset_ker (QuotientGroup.mk' (P : Subgroup E))
      rwa [QuotientGroup.ker_mk'] at this
    intro hzc'
    have hd := Subgroup.orderOf_dvd_natCard _ (hle hzc')
    rw [hz, hP3] at hd
    exact absurd hd (by norm_num)
  · have h4 : Nat.card E ∣ 4 := by
      have : Nat.card E ∣ 4 * 3 := h12
      exact Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm this
    have := isMulCommutative_of_card_dvd_four h4
    rw [show commutator E = ⊥ from
      commutator_eq_bot_of_comm (P := ⊤) fun a _ b _ => mul_comm' a b, Subgroup.mem_bot]
    intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem conj_eq_self_of_prime_of_not_dvd {G : Type*} [Group G] {V : Subgroup G} [Finite V]
    {m : ℕ} (hVm : Nat.card V = 2 ^ m) {x : G} (hxV : x ∈ normalizer (V : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hxr : x ^ r = 1) (hnot : ∀ j, 1 ≤ j → j ≤ m → ¬ r ∣ 2 ^ j - 1) :
    ∀ v ∈ V, x * v * x⁻¹ = v := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have := Fintype.ofFinite V
  have hmem : ∀ v : V, x * (v : G) * x⁻¹ ∈ V := fun v => (mem_normalizer_iff.mp hxV v).mp v.2
  let f : Function.End V := fun v => ⟨x * v * x⁻¹, hmem v⟩
  have hfpow : ∀ (n : ℕ) (v : V), (((f ^ n) v : V) : G) = x ^ n * v * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro v; simp; rfl
    | succ n ih =>
      intro v
      rw [pow_succ' f n]
      change x * (((f ^ n) v : V) : G) * x⁻¹ = _
      rw [ih, pow_succ' x n, mul_inv_rev]
      simp only [mul_assoc]
  have hf : f ^ r ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    rw [pow_one, hfpow, hxr, one_mul, inv_one, mul_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := r) (n := 1) hf
  set C : Subgroup V := (centralizer ({x} : Set G)).subgroupOf V with hCdef
  have hfixC : ∀ v : V, v ∈ Function.fixedPoints f ↔ v ∈ C := by
    intro v
    rw [Function.mem_fixedPoints, hCdef, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : x * (v : G) * x⁻¹ = v := congrArg Subtype.val h
      calc (v : G) * x = x * v * x⁻¹ * x := by rw [h1]
        _ = x * v := by group
    · intro h
      apply Subtype.ext
      change x * (v : G) * x⁻¹ = v
      rw [← h, mul_inv_cancel_right]
  have hcardC : Fintype.card (Function.fixedPoints f) = Nat.card C := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight hfixC)
  obtain ⟨c, hc, hCc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hVm ▸ Subgroup.card_subgroup_dvd_card C)
  rw [hcardC, hCc, ← Nat.card_eq_fintype_card, hVm] at hmod
  have hcm : c = m := by
    by_contra hne
    have hlt : c < m := lt_of_le_of_ne hc hne
    have hd : r ∣ 2 ^ m - 2 ^ c := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hc)).mp
      hmod.symm
    have hsplit : 2 ^ m - 2 ^ c = 2 ^ c * (2 ^ (m - c) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hc]
    rw [hsplit] at hd
    have hcop : Nat.Coprime r (2 ^ c) := by
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    exact hnot (m - c) (by omega) (Nat.sub_le m c) (hcop.dvd_of_dvd_mul_left hd)
  have hCtop : C = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hCc, hcm, hVm]
  intro v hv
  have hvC : (⟨v, hv⟩ : V) ∈ C := hCtop ▸ Subgroup.mem_top _
  rw [hCdef, mem_subgroupOf, mem_centralizer_singleton_iff] at hvC
  change (v : G) * x = x * v at hvC
  rw [← hvC, mul_inv_cancel_right]

end CFSG.EvenSmallLie.UnitarySix.Yamada
