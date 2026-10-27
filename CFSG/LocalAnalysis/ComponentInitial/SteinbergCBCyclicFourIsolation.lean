module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCBCyclicFourCentric
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly

variable {G : Type*} [Group G]

theorem eq_of_card_eq_four {H : Subgroup G} (hH : Nat.card H = 4) {a b c d p : G}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hp : p ∈ H) :
    p = a ∨ p = b ∨ p = c ∨ p = d := by
  by_contra hne
  push Not at hne
  obtain ⟨hpa, hpb, hpc, hpd⟩ := hne
  have : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hsub : ({p, a, b, c, d} : Set G) ⊆ H := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h5 : ({p, a, b, c, d} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hpa, hpb, hpc, hpd]),
      Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]), Set.ncard_insert_of_notMem (by simp [hcd]),
      Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h5, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hH] at hle
  omega

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {g s : G} {a : ℕ}
    (hg : orderOf g = 2 ^ (a + 1)) (hs : s ∈ Subgroup.zpowers g) (hs2 : s * s = 1) :
    s = 1 ∨ s = g ^ 2 ^ a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  have hk : ((2 ^ (a + 1) : ℕ) : ℤ) ∣ k * 2 := by
    rw [← hg, orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_two, hs2]
  have hk' : ((2 ^ a : ℕ) : ℤ) ∣ k := by
    have e : ((2 ^ (a + 1) : ℕ) : ℤ) = ((2 ^ a : ℕ) : ℤ) * 2 := by push_cast; ring
    rw [e] at hk
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 hk
  obtain ⟨m, rfl⟩ := hk'
  have hu : g ^ 2 ^ a * g ^ 2 ^ a = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hg, pow_orderOf_eq_one]
  rw [zpow_mul, zpow_natCast]
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · left
    obtain ⟨q, rfl⟩ : (2 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero h0
    rw [zpow_mul, zpow_two, hu, one_zpow]
  · right
    have hm : m = 2 * (m / 2) + 1 := by omega
    rw [hm, zpow_add, zpow_mul, zpow_two, hu, one_zpow, one_mul, zpow_one]

theorem cyclic_times_four_inversion_sylow_central_normalizer_forces_isolation [Finite G]
    (Q : Sylow 2 G) {P S : Subgroup G} {x : G} {a : ℕ}
    (hP : Nonempty (P ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hS : IsCyclic S) (hScard : Nat.card S = 2 ^ a) (ha : 2 ≤ a) (hx : orderOf x = 2)
    (hPS : ∀ p ∈ P, ∀ s ∈ S, p * s = s * p) (hPS1 : P ⊓ S = ⊥)
    (hxA : Subgroup.zpowers x ⊓ (P ⊔ S) = ⊥)
    (hQ : (Q : Subgroup G) = P ⊔ S ⊔ Subgroup.zpowers x)
    (hxP : x ∈ Subgroup.normalizer (P : Set G)) (hxP1 : ∃ p ∈ P, x⁻¹ * p * x ≠ p)
    (hxS : ∀ s ∈ S, x⁻¹ * s * x = s⁻¹) {t : G} (htS : t ∈ S) (ht : orderOf t = 2)
    (hNQ : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({t} : Set G)) :
    Set.range (fun g : G => g⁻¹ * t * g) ∩ (Q : Set G) = {t} ∧
      (∀ g : G, ∃ c ∈ Subgroup.centralizer ({t} : Set G), ∃ k ∈ CFSG.oddCore G, g = c * k) ∧
      (∃! v : G, v ∈ P ⊓ Subgroup.centralizer ({x} : Set G) ∧ v ≠ 1) ∧
      ∀ v ∈ P ⊓ Subgroup.centralizer ({x} : Set G), v ≠ 1 →
        ∀ D : Subgroup G, D ≤ Q →
          (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) =
            (Subgroup.center D).map D.subtype →
          Subgroup.normalizer (D : Set G) ≤ Subgroup.centralizer ({t} : Set G) ∧
            (¬ IsMulCommutative D →
              (Subgroup.center D).map D.subtype = Subgroup.closure {t, v}) ∧
            (IsMulCommutative D → D = P ⊔ S ∨
              ∃ y ∈ (Q : Subgroup G), y ∉ P ⊔ S ∧
                D = Subgroup.closure {t, v} ⊔ Subgroup.zpowers y ∧
                ((Nonempty (D ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) ∧
                    Subgroup.closure {d : G | d ∈ D ∧ orderOf d = 2} =
                      Subgroup.closure {t, v}) ∨
                  (IsElemAbelian 2 D ∧ Nat.card D = 8))) := by
  classical
  obtain ⟨eP⟩ := hP
  have hP2 : ∀ p ∈ P, p * p = 1 := fun p hp => by
    have h1 : (⟨p, hp⟩ : P) * ⟨p, hp⟩ = 1 := eP.injective (by
      rw [map_mul, map_one]
      generalize eP ⟨p, hp⟩ = u
      revert u
      decide)
    exact congrArg Subtype.val h1
  have hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := fun p hp q hq => by
    have h1 : (⟨p, hp⟩ : P) * ⟨q, hq⟩ = ⟨q, hq⟩ * ⟨p, hp⟩ := eP.injective (by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h1
  have hPcard : Nat.card P = 4 := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_prod]
    simp
  obtain ⟨g₀', hg₀'⟩ := @IsCyclic.exists_generator _ _ hS
  set g₀ : G := (g₀' : G) with hg₀_def
  have hg₀S : g₀ ∈ S := g₀'.2
  have hg₀ord : orderOf g₀ = 2 ^ a := by
    rw [hg₀_def, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₀', hScard]
  have hSz : ∀ s ∈ S, s ∈ Subgroup.zpowers g₀ := fun s hs => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg₀' ⟨s, hs⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [hg₀_def, ← Subgroup.coe_zpow, hk]⟩
  have hSc : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := fun s hs s' hs' => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hSz s hs)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hSz s' hs')
    exact (Commute.zpow_zpow_self g₀ i j).eq
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    norm_num at ht
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hinvS : ∀ s ∈ S, s * s = 1 → s = 1 ∨ s = g₀ ^ 2 ^ (a' + 1) := fun s hs hs2 =>
    eq_one_or_eq_of_mem_zpowers_of_mul_self hg₀ord (hSz s hs) hs2
  have ht0 : t = g₀ ^ 2 ^ (a' + 1) := (hinvS t htS htt).resolve_left ht1
  have hinvS' : ∀ s ∈ S, s * s = 1 → s = 1 ∨ s = t := fun s hs hs2 => by
    rw [ht0]
    exact hinvS s hs hs2
  set r := g₀ ^ 2 ^ a' with hr_def
  have hrS : r ∈ S := S.pow_mem hg₀S _
  have hrr : r * r = t := by rw [ht0, hr_def, ← pow_add, ← two_mul, ← pow_succ']
  have hxx : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hconj_inv : ∀ b, x⁻¹ * b * x = x * b * x⁻¹ := fun b => by rw [hxinv]
  have hσP : ∀ p ∈ P, x * p * x⁻¹ ∈ P := fun p hp => (Subgroup.mem_normalizer_iff.1 hxP p).1 hp
  have hσS : ∀ s ∈ S, x * s * x⁻¹ = s⁻¹ := fun s hs => by rw [← hconj_inv]; exact hxS s hs
  have hσσ : ∀ b, x * (x * b * x⁻¹) * x⁻¹ = b := fun b => by
    calc x * (x * b * x⁻¹) * x⁻¹ = (x * x) * b * (x * x)⁻¹ := by group
      _ = b := by rw [hxx]; group
  set A := P ⊔ S with hA_def
  have hPnS : P ≤ Subgroup.normalizer (S : Set G) :=
    le_trans (fun p hp => Subgroup.mem_centralizer_iff.2 fun s hs => (hPS p hp s hs).symm)
      (Subgroup.centralizer_le_normalizer _)
  have hAmem : ∀ b, b ∈ A ↔ ∃ p ∈ P, ∃ s ∈ S, p * s = b := fun b => by
    rw [← SetLike.mem_coe, hA_def, Subgroup.coe_mul_of_left_le_normalizer_right P S hPnS,
      Set.mem_mul]
    simp only [SetLike.mem_coe]
  have hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := by
    intro b hb c hc
    obtain ⟨p, hp, s, hs, rfl⟩ := (hAmem b).1 hb
    obtain ⟨p', hp', s', hs', rfl⟩ := (hAmem c).1 hc
    calc p * s * (p' * s') = p * (s * p') * s' := by group
      _ = p * (p' * s) * s' := by rw [← hPS p' hp' s hs]
      _ = (p * p') * (s * s') := by group
      _ = (p' * p) * (s' * s) := by rw [hPc p hp p' hp', hSc s hs s' hs']
      _ = p' * (p * s') * s := by group
      _ = p' * (s' * p) * s := by rw [hPS p hp s' hs']
      _ = p' * s' * (p * s) := by group
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hxnA : x ∉ A := fun hxA' => hx1 (by
    have hmem : x ∈ Subgroup.zpowers x ⊓ A := ⟨Subgroup.mem_zpowers x, hxA'⟩
    rwa [hxA, Subgroup.mem_bot] at hmem)
  have hσA : ∀ b ∈ A, x * b * x⁻¹ ∈ A := fun b hb => by
    obtain ⟨p, hp, s, hs, rfl⟩ := (hAmem b).1 hb
    rw [show x * (p * s) * x⁻¹ = (x * p * x⁻¹) * (x * s * x⁻¹) by group, hσS s hs]
    exact (hAmem _).2 ⟨_, hσP p hp, _, S.inv_mem hs, rfl⟩
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨hσA b, fun hb => ?_⟩
    have := hσA _ hb
    rwa [hσσ] at this
  have hQmem : ∀ q ∈ (Q : Subgroup G), q ∈ A ∨ ∃ b ∈ A, q = b * x := by
    intro q hq
    rw [hQ, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A _
      (Subgroup.zpowers_le.2 hxN), Set.mem_mul] at hq
    obtain ⟨b, hb, u, hu, rfl⟩ := hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hk : x ^ k = x ^ (k % 2) := by rw [← zpow_mod_orderOf x k, hx]; norm_num
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, zpow_zero, mul_one]
      exact hb
    · right
      exact ⟨b, hb, by rw [hk, h1, zpow_one]⟩
  obtain ⟨p₀, hp₀P, hp₀⟩ := hxP1
  have hp₀' : x * p₀ * x⁻¹ ≠ p₀ := by rw [← hconj_inv]; exact hp₀
  set v₀ := p₀ * (x * p₀ * x⁻¹) with hv₀_def
  have hv₀P : v₀ ∈ P := P.mul_mem hp₀P (hσP p₀ hp₀P)
  have hv₀1 : v₀ ≠ 1 := fun e => hp₀' (by
    rw [eq_inv_of_mul_eq_one_right e, inv_eq_of_mul_eq_one_right (hP2 p₀ hp₀P)])
  have hσv₀ : x * v₀ * x⁻¹ = v₀ := by
    calc x * v₀ * x⁻¹ = (x * p₀ * x⁻¹) * (x * (x * p₀ * x⁻¹) * x⁻¹) := by rw [hv₀_def]; group
      _ = (x * p₀ * x⁻¹) * p₀ := by rw [hσσ]
      _ = v₀ := by rw [hv₀_def, hPc _ (hσP p₀ hp₀P) p₀ hp₀P]
  have hσp₀ : x * p₀ * x⁻¹ = v₀ * p₀ := by
    calc x * p₀ * x⁻¹ = (x * p₀ * x⁻¹) * (p₀ * p₀) := by rw [hP2 p₀ hp₀P, mul_one]
      _ = (p₀ * (x * p₀ * x⁻¹)) * p₀ := by
          rw [← mul_assoc (x * p₀ * x⁻¹) p₀ p₀, hPc _ (hσP p₀ hp₀P) p₀ hp₀P]
      _ = v₀ * p₀ := by rw [hv₀_def]
  have hp₀1 : p₀ ≠ 1 := fun e => hp₀' (by rw [e]; group)
  have hv₀p₀ : v₀ ≠ p₀ := fun e => hp₀' (by rw [← e]; exact hσv₀)
  have hv₀p₀' : v₀ * p₀ ≠ 1 := fun e => hv₀p₀ (by
    rw [eq_inv_of_mul_eq_one_left e, inv_eq_of_mul_eq_one_right (hP2 p₀ hp₀P)])
  have hv₀_ne : v₀ ≠ v₀ * p₀ := fun e => hp₀1 (by simpa using e)
  have hp₀_ne : p₀ ≠ v₀ * p₀ := fun e => hv₀1 (by simpa using e)
  have hPelts : ∀ p ∈ P, p = 1 ∨ p = v₀ ∨ p = p₀ ∨ p = v₀ * p₀ := fun p hp =>
    eq_of_card_eq_four hPcard P.one_mem hv₀P hp₀P (P.mul_mem hv₀P hp₀P) hv₀1.symm hp₀1.symm
      hv₀p₀'.symm hv₀p₀ hv₀_ne hp₀_ne hp
  have hPfix : ∀ p ∈ P, x * p * x⁻¹ = p → p = 1 ∨ p = v₀ := fun p hp hfix => by
    rcases hPelts p hp with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · rw [e] at hfix
      exact absurd hfix hp₀'
    · exfalso
      rw [e] at hfix
      apply hp₀_ne
      calc p₀ = x * (v₀ * p₀) * x⁻¹ := by
            rw [show x * (v₀ * p₀) * x⁻¹ = (x * v₀ * x⁻¹) * (x * p₀ * x⁻¹) by group, hσv₀,
              hσp₀, ← mul_assoc, hP2 v₀ hv₀P, one_mul]
        _ = v₀ * p₀ := hfix
  have hCPx : ∀ w, w ∈ P ⊓ Subgroup.centralizer ({x} : Set G) ↔ w ∈ P ∧ x * w * x⁻¹ = w :=
    fun w => by
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hw, hwx⟩
        exact ⟨hw, by rw [← hwx, mul_inv_cancel_right]⟩
      · rintro ⟨hw, hwx⟩
        exact ⟨hw, (mul_inv_eq_iff_eq_mul.1 hwx).symm⟩
  have hM1 : ∃! v : G, v ∈ P ⊓ Subgroup.centralizer ({x} : Set G) ∧ v ≠ 1 := by
    refine ⟨v₀, ⟨(hCPx v₀).2 ⟨hv₀P, hσv₀⟩, hv₀1⟩, ?_⟩
    rintro w ⟨hw, hw1⟩
    obtain ⟨hwP, hwx⟩ := (hCPx w).1 hw
    exact (hPfix w hwP hwx).resolve_left hw1
  have hσt : x * t * x⁻¹ = t := by rw [hσS t htS, inv_eq_of_mul_eq_one_right htt]
  have hcfg : CyclicFourInversionConfig Q A x t v₀ := by
    refine
      { le_Q := by rw [hQ]; exact le_sup_left
        x_mem := by rw [hQ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
        x_not_mem := hxnA
        x_mul_x := hxx
        mem_cases := hQmem
        comm := hAc
        conj_mem := hσA
        fixed_iff := ?_
        t_mem := Subgroup.mem_sup_right htS
        v_mem := Subgroup.mem_sup_left hv₀P
        t_mul_t := htt
        v_mul_v := hP2 v₀ hv₀P
        t_comm_v := (hPS v₀ hv₀P t htS).symm
        t_ne_one := ht1
        v_ne_one := hv₀1
        v_ne_t := fun e => hv₀1 (by
          have hmem : v₀ ∈ P ⊓ S := ⟨hv₀P, e ▸ htS⟩
          rwa [hPS1, Subgroup.mem_bot] at hmem)
        sq_eq_t := ?_
        exists_sqrt := ⟨r, Subgroup.mem_sup_right hrS, hrr, hσS r hrS⟩
        exists_shift := ⟨p₀, Subgroup.mem_sup_left hp₀P, hσp₀⟩
        outside_sq := ?_
        normalizer_le := hNQ }
    · intro b hb
      constructor
      · intro hfix
        obtain ⟨p, hp, s, hs, rfl⟩ := (hAmem b).1 hb
        rw [show x * (p * s) * x⁻¹ = (x * p * x⁻¹) * (x * s * x⁻¹) by group, hσS s hs] at hfix
        have e : p⁻¹ * (x * p * x⁻¹) = s * s := by
          calc p⁻¹ * (x * p * x⁻¹) = p⁻¹ * ((x * p * x⁻¹) * s⁻¹) * s := by group
            _ = p⁻¹ * (p * s) * s := by rw [hfix]
            _ = s * s := by group
        have hmem : s * s ∈ P ⊓ S :=
          ⟨e ▸ P.mul_mem (P.inv_mem hp) (hσP p hp), S.mul_mem hs hs⟩
        rw [hPS1, Subgroup.mem_bot] at hmem
        rw [hmem] at e
        have hpfix : x * p * x⁻¹ = p := (inv_mul_eq_one.1 e).symm
        rcases hPfix p hp hpfix with hp1 | hpv <;> rcases hinvS' s hs hmem with hs1 | hst
        · rw [hp1, hs1, mul_one]
          exact Set.mem_insert _ _
        · rw [hp1, hst, one_mul]
          simp
        · rw [hpv, hs1, mul_one]
          simp
        · rw [hpv, hst, hPS v₀ hv₀P t htS]
          simp
      · intro hbF
        rcases hbF with e | e | e | e <;> rw [e]
        · group
        · exact hσt
        · exact hσv₀
        · rw [show x * (t * v₀) * x⁻¹ = (x * t * x⁻¹) * (x * v₀ * x⁻¹) by group, hσt, hσv₀]
    · intro b hb hb1 hb2
      obtain ⟨p, hp, s, hs, rfl⟩ := (hAmem b).1 hb
      have e : p * s * (p * s) = s * s := by
        calc p * s * (p * s) = p * (s * p) * s := by group
          _ = p * (p * s) * s := by rw [← hPS p hp s hs]
          _ = (p * p) * (s * s) := by group
          _ = s * s := by rw [hP2 p hp, one_mul]
      rw [e] at hb1 hb2 ⊢
      exact (hinvS' _ (S.mul_mem hs hs) hb2).resolve_left hb1
    · intro b hb
      obtain ⟨p, hp, s, hs, rfl⟩ := (hAmem b).1 hb
      have hwP : p * (x * p * x⁻¹) ∈ P := P.mul_mem hp (hσP p hp)
      have hσw : x * (p * (x * p * x⁻¹)) * x⁻¹ = p * (x * p * x⁻¹) := by
        calc x * (p * (x * p * x⁻¹)) * x⁻¹ =
            (x * p * x⁻¹) * (x * (x * p * x⁻¹) * x⁻¹) := by group
          _ = (x * p * x⁻¹) * p := by rw [hσσ]
          _ = p * (x * p * x⁻¹) := by rw [hPc _ (hσP p hp) p hp]
      have e : p * s * x * (p * s * x) = p * (x * p * x⁻¹) := by
        calc p * s * x * (p * s * x) = p * s * (x * (p * s) * x⁻¹) * (x * x) := by group
          _ = p * s * ((x * p * x⁻¹) * s⁻¹) := by
              rw [show x * (p * s) * x⁻¹ = (x * p * x⁻¹) * (x * s * x⁻¹) by group, hσS s hs,
                hxx, mul_one]
          _ = p * (s * (x * p * x⁻¹)) * s⁻¹ := by group
          _ = p * ((x * p * x⁻¹) * s) * s⁻¹ := by rw [← hPS _ (hσP p hp) s hs]
          _ = p * (x * p * x⁻¹) := by group
      rw [e]
      exact hPfix _ hwP hσw
  have htQ : t ∈ (Q : Subgroup G) := hcfg.le_Q hcfg.t_mem
  have hiso : ∀ g : G, g⁻¹ * t * g ∈ (Q : Subgroup G) → g⁻¹ * t * g = t := by
    intro g hg
    by_contra hmove
    obtain ⟨D, hD, -, n, hn, hnt⟩ :=
      CFSG.RankTwoShapes.exists_alperinSubgroup_moving Q htQ hg hmove
    have hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D := by
      rw [inf_comm]
      exact hD.2.2.1
    have hnC := (hcfg.centric_conclusions hD.1 hcen).1 hn
    rw [Subgroup.mem_centralizer_singleton_iff] at hnC
    apply hnt
    rw [mul_assoc, ← hnC, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨?_, ?_, hM1, ?_⟩
  · ext y
    constructor
    · rintro ⟨⟨g, rfl⟩, hy⟩
      exact hiso g hy
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨⟨1, by group⟩, htQ⟩
  · have hzZ : (⟨t, htQ⟩ : (Q : Subgroup G)) ∈ Subgroup.center (Q : Subgroup G) :=
      Subgroup.mem_center_iff.2 fun q => Subtype.ext (hcfg.F_comm hcfg.t_mem_F q.2)
    have hzo : orderOf (⟨t, htQ⟩ : (Q : Subgroup G)) = 2 := by rw [Subgroup.orderOf_mk, ht]
    open CFSG.ComponentClassification.StandardRecognition in
    exact (glauberman_zStar_central_sylow_involution_univ Q ⟨t, htQ⟩ hzZ hzo hiso).1
  · intro v hv hv1 D hDQ hDcen
    have hvv₀ : v = v₀ := hM1.unique ⟨hv, hv1⟩ ⟨(hCPx v₀).2 ⟨hv₀P, hσv₀⟩, hv₀1⟩
    rw [hvv₀]
    have hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D := fun z hz => by
      rw [hDcen] at hz
      exact (mem_map_center_iff.1 hz).1
    exact hcfg.centric_conclusions hDQ hcen

end CFSG.LocalAnalysis.ComponentInitial
