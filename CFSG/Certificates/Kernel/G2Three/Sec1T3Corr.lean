module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.G2Three.Sec1T3

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_index_two_ge {K H : Subgroup G} [Finite K] (hp : IsPGroup 2 K) (hHK : H ≤ K)
    (hne : H ≠ K) : ∃ M : Subgroup G, H ≤ M ∧ M ≤ K ∧ Nat.card K = 2 * Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hp.to_subgroup (H.subgroupOf K))
  have e1 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hlt : a < n := by
    by_contra h
    refine hne (Subgroup.eq_of_le_of_card_ge hHK ?_)
    rw [hn, ← e1, ha]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨M', hM', hle⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := K) 2 (n := a) (m := n - 1)
    (by rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1)) (H.subgroupOf K) ha (by omega)
  refine ⟨M'.map K.subtype, fun h hh => ⟨⟨h, hHK hh⟩, hle (by rwa [mem_subgroupOf]), rfl⟩,
    map_subtype_le M', ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective, hM', hn, ← pow_succ']
  congr 1
  omega

theorem isMaximal_iff_card {K M : Subgroup G} [Finite K] (hp : IsPGroup 2 K) :
    (M < K ∧ ∀ N : Subgroup G, M < N → N ≤ K → N = K) ↔
      M ≤ K ∧ Nat.card K = 2 * Nat.card M := by
  constructor
  · rintro ⟨hlt, hmax⟩
    obtain ⟨M', h1, h2, h3⟩ := exists_index_two_ge hp hlt.le hlt.ne
    have hfin : Finite M' := Finite.of_injective _ (Subgroup.inclusion_injective h2)
    have hpos : 0 < Nat.card M' := Nat.card_pos
    have hM' : M' ≠ K := by
      rintro rfl
      omega
    rcases h1.lt_or_eq with h | rfl
    · exact absurd (hmax M' h h2) hM'
    · exact ⟨hlt.le, h3⟩
  · rintro ⟨hle, hc⟩
    have hfin : Finite M := Finite.of_injective _ (Subgroup.inclusion_injective hle)
    have hpos : 0 < Nat.card M := Nat.card_pos
    refine ⟨lt_of_le_of_ne hle fun he => by subst he; omega, fun N hMN hNK => ?_⟩
    have hfinN : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNK)
    obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hMN.le
    obtain ⟨i, hi⟩ := Subgroup.card_dvd_of_le hNK
    have hji : Nat.card M * (j * i) = Nat.card M * 2 := by
      rw [← mul_assoc, ← hj, ← hi, hc, mul_comm]
    have hji' : j * i = 2 := Nat.eq_of_mul_eq_mul_left hpos hji
    have hj2 : j ≤ 2 := Nat.le_of_dvd (by decide) ⟨i, hji'.symm⟩
    interval_cases j
    · omega
    · exact absurd (Subgroup.eq_of_le_of_card_ge hMN.le (by rw [hj, mul_one])) hMN.ne
    · refine Subgroup.eq_of_le_of_card_ge hNK ?_
      rw [hc, hj]
      omega

theorem isMulCommutative_of_sq {H : Type*} [Group H] {E : Subgroup H}
    (h : ∀ x ∈ E, x ^ 2 = 1) : IsMulCommutative E := by
  have inv : ∀ x ∈ E, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h x hx)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  change (a : H) * b = b * a
  have := inv _ (E.mul_mem a.2 b.2)
  rw [mul_inv_rev, inv _ a.2, inv _ b.2] at this
  exact this.symm

theorem isElemAbelian_iff_sq {H : Type*} [Group H] {E : Subgroup H} :
    IsElemAbelian 2 E ↔ ∀ x ∈ E, x * x = 1 := by
  have e : ∀ x : H, x ^ 2 = 1 ↔ x * x = 1 := fun x => by rw [pow_two]
  refine ⟨fun h x hx => (e x).1 (h.2 x hx), fun h => ?_⟩
  have h2 : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => (e x).2 (h x hx)
  exact ⟨isMulCommutative_of_sq h2, h2⟩

theorem pRank_eq_of_max [Finite G] {X : Subgroup G} {r : ℕ}
    (hex : ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ r)
    (hle : ∀ E : Subgroup G, E ≤ X → IsElemAbelian 2 E → Nat.card E ≤ 2 ^ r) : pRank 2 X = r := by
  refine IsGreatest.csSup_eq ⟨hex, ?_⟩
  rintro k ⟨E, hEX, hE, hc⟩
  have := hle E hEX hE
  rw [hc] at this
  exact (Nat.pow_le_pow_iff_right (by decide)).1 this

theorem two_pow_pRank_of_comm [Finite G] {K : Subgroup G} (hK : IsMulCommutative K)
    (hp : IsPGroup 2 K) : 2 ^ pRank 2 K = {x | x ∈ K ∧ x * x = 1}.ncard := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ K ∧ x * x = 1}
      mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, by
        have hc := Subgroup.mul_comm_of_mem_isMulCommutative K hb.1 ha.1
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hc]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨K.one_mem, one_mul 1⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hΩK : Ω ≤ K := fun x hx => hx.1
  have hΩ : IsElemAbelian 2 Ω := isElemAbelian_iff_sq.2 fun x hx => hx.2
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 (hp.to_le hΩK)
  have hc : Nat.card Ω = {x | x ∈ K ∧ x * x = 1}.ncard := rfl
  rw [← hc, pRank_eq_of_max ⟨Ω, hΩK, hΩ, hr⟩ fun E hEK hE => ?_, hr]
  rw [← hr]
  have : Finite Ω := Finite.of_injective _ (Subgroup.inclusion_injective hΩK)
  refine Subgroup.card_le_of_le fun x hx => ⟨hEK hx, (isElemAbelian_iff_sq.1 hE) x hx⟩

theorem comm_mem_of_gens {s : Set G} {N : Subgroup G}
    (hn : ∀ x ∈ closure s, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hs : ∀ a ∈ s, ∀ b ∈ s, ⁅a, b⁆ ∈ N) :
    ∀ a ∈ closure s, ∀ b ∈ closure s, ⁅a, b⁆ ∈ N := by
  have h1 : ∀ a ∈ closure s, ∀ b ∈ s, ⁅a, b⁆ ∈ N := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact hs x hx
    | one =>
      intro b _
      rw [commutatorElement_def]
      simpa using N.one_mem
    | mul x y hx hy ihx ihy =>
      intro b hb
      have e : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem (hn x hx _ (ihy b hb)) (ihx b hb)
    | inv x hx ihx =>
      intro b hb
      have e : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hn _ ((closure s).inv_mem hx) _ (N.inv_mem (ihx b hb))
  intro a ha b hb
  induction hb using Subgroup.closure_induction with
  | mem y hy => exact h1 a ha y hy
  | one =>
    rw [commutatorElement_def]
    simpa using N.one_mem
  | mul y z hy hz ihy ihz =>
    have e : ⁅a, y * z⁆ = ⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem ihy (hn y hy _ ihz)
  | inv y hy ihy =>
    have e : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hn _ ((closure s).inv_mem hy) _ (N.inv_mem ihy)

section Corr

variable (X N : Subgroup G) [(N.subgroupOf X).Normal]

abbrev quo (K : Subgroup G) : Subgroup (X ⧸ N.subgroupOf X) :=
  (K.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))

variable {X N}

theorem mem_quo {K : Subgroup G} (hNK : N ≤ K) (x : X) :
    (x : X ⧸ N.subgroupOf X) ∈ quo X N K ↔ (x : G) ∈ K := by
  constructor
  · rintro ⟨y, hy, he⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    rw [mem_subgroupOf] at he
    have := K.mul_mem hy (hNK he)
    simpa using this
  · intro hx
    exact ⟨x, (mem_subgroupOf).2 hx, rfl⟩

theorem quo_le_quo_iff {K₁ K₂ : Subgroup G} (hN : N ≤ K₂) (hK : K₁ ≤ X) :
    quo X N K₁ ≤ quo X N K₂ ↔ K₁ ≤ K₂ := by
  constructor
  · intro h x hx
    have : ((⟨x, hK hx⟩ : X) : X ⧸ N.subgroupOf X) ∈ quo X N K₂ :=
      h ⟨⟨x, hK hx⟩, (mem_subgroupOf).2 hx, rfl⟩
    exact (mem_quo hN _).1 this
  · rintro h _ ⟨y, hy, rfl⟩
    exact ⟨y, (mem_subgroupOf).2 (h ((mem_subgroupOf).1 hy)), rfl⟩

theorem quo_inj {K₁ K₂ : Subgroup G} (hN₁ : N ≤ K₁) (hN₂ : N ≤ K₂) (hK₁ : K₁ ≤ X)
    (hK₂ : K₂ ≤ X) (h : quo X N K₁ = quo X N K₂) : K₁ = K₂ :=
  le_antisymm ((quo_le_quo_iff hN₂ hK₁).1 h.le) ((quo_le_quo_iff hN₁ hK₂).1 h.ge)

theorem exists_quo (hNX : N ≤ X) (Y : Subgroup (X ⧸ N.subgroupOf X)) :
    ∃ K : Subgroup G, N ≤ K ∧ K ≤ X ∧ quo X N K = Y := by
  refine ⟨(Y.comap (QuotientGroup.mk' (N.subgroupOf X))).map X.subtype, fun n hn => ?_,
    map_subtype_le _, ?_⟩
  · refine ⟨⟨n, hNX hn⟩, ?_, rfl⟩
    have h1 : ((⟨n, hNX hn⟩ : X) : X ⧸ N.subgroupOf X) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((mem_subgroupOf).2 hn)
    rw [SetLike.mem_coe, mem_comap, QuotientGroup.mk'_apply, h1]
    exact Y.one_mem
  · have e : ((Y.comap (QuotientGroup.mk' (N.subgroupOf X))).map X.subtype).subgroupOf X =
        Y.comap (QuotientGroup.mk' (N.subgroupOf X)) := by
      ext x
      rw [mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨y, hy, he⟩
        rwa [← Subtype.ext he]
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [quo, e, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem quo_isElemAbelian_iff {K : Subgroup G} (hNK : N ≤ K) (hKX : K ≤ X) :
    IsElemAbelian 2 (quo X N K) ↔ ∀ k ∈ K, k * k ∈ N := by
  rw [isElemAbelian_iff_sq]
  constructor
  · intro h k hk
    have := h _ ((mem_quo hNK ⟨k, hKX hk⟩).2 hk)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf] at this
    exact this
  · rintro h _ ⟨y, hy, rfl⟩
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact h _ ((mem_subgroupOf).1 hy)

theorem maxElemAbelian_quo (hNX : N ≤ X) {K₁ K₂ : Subgroup G}
    (hK : ∀ K : Subgroup G, (N ≤ K ∧ K ≤ X ∧ (∀ k ∈ K, k * k ∈ N) ∧
      ∀ K' : Subgroup G, K ≤ K' → K' ≤ X → (∀ k ∈ K', k * k ∈ N) → K' = K) ↔ K = K₁ ∨ K = K₂) :
    {Y : Subgroup (X ⧸ N.subgroupOf X) | Y ≤ ⊤ ∧ IsElemAbelian 2 Y ∧
      ∀ Y' : Subgroup (X ⧸ N.subgroupOf X), Y ≤ Y' → Y' ≤ ⊤ → IsElemAbelian 2 Y' → Y' = Y} =
      {quo X N K₁, quo X N K₂} := by
  ext Y
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, le_top, true_and,
    forall_const]
  constructor
  · rintro ⟨hEA, hmax⟩
    obtain ⟨K, hNK, hKX, rfl⟩ := exists_quo hNX Y
    have hsq := (quo_isElemAbelian_iff hNK hKX).1 hEA
    have hKm : K = K₁ ∨ K = K₂ := by
      refine (hK K).1 ⟨hNK, hKX, hsq, fun K' hKK' hK'X hsq' => ?_⟩
      have hNK' : N ≤ K' := hNK.trans hKK'
      refine quo_inj hNK' hNK hK'X hKX (hmax _ ((quo_le_quo_iff hNK' hKX).2 hKK') ?_)
      exact (quo_isElemAbelian_iff hNK' hK'X).2 hsq'
    rcases hKm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hY
    obtain ⟨K, hKe, rfl⟩ : ∃ K, (K = K₁ ∨ K = K₂) ∧ quo X N K = Y := by
      rcases hY with rfl | rfl
      · exact ⟨K₁, Or.inl rfl, rfl⟩
      · exact ⟨K₂, Or.inr rfl, rfl⟩
    obtain ⟨hNK, hKX, hsq, hmax⟩ := (hK K).2 hKe
    refine ⟨(quo_isElemAbelian_iff hNK hKX).2 hsq, fun Y' hle hEA' => ?_⟩
    obtain ⟨K', hNK', hK'X, rfl⟩ := exists_quo hNX Y'
    rw [hmax K' ((quo_le_quo_iff hNK' hKX).1 hle) hK'X
      ((quo_isElemAbelian_iff hNK' hK'X).1 hEA')]

end Corr

end CFSG.KC.G2Three.Sec1T3
