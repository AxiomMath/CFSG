module

public import CFSG.GH74.GLS.Stage4.Q9.OddCore
public import CFSG.GH74.GLS.Stage4.Q9.VSupport
public import CFSG.GH74.GLS.Stage4.Q9.Rigidity

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

section OddCorePackage

variable {G : Type*} [Group G]

private theorem conj_mem_centralizer {a x c : G} (hx : x ∈ centralizer ({a} : Set G)) :
    c * x * c⁻¹ ∈ centralizer ({c * a * c⁻¹} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hx ⊢
  calc c * x * c⁻¹ * (c * a * c⁻¹) = c * (x * a) * c⁻¹ := by group
    _ = c * (a * x) * c⁻¹ := by rw [hx]
    _ = c * a * c⁻¹ * (c * x * c⁻¹) := by group

private theorem card_centralizer_eq_of_isConj {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  refine Nat.card_congr
    { toFun := fun x => ⟨c * x * c⁻¹, conj_mem_centralizer x.2⟩
      invFun := fun y => ⟨c⁻¹ * y * c, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · have := conj_mem_centralizer (c := c⁻¹) y.2
    have e : c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a := by group
    rw [e, inv_inv] at this
    exact this
  · apply Subtype.ext
    show c⁻¹ * (c * (x : G) * c⁻¹) * c = x
    group
  · apply Subtype.ext
    show c * (c⁻¹ * (y : G) * c) * c⁻¹ = y
    group

private theorem orderOf_mul_eq_two_of_commute {z u : G} (hz : orderOf z = 2) (hu : orderOf u = 2)
    (hzu : z * u = u * z) (hne : z ≠ u) : orderOf (z * u) = 2 := by
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hc : Commute z u := hzu
  refine orderOf_eq_prime ?_ ?_
  · rw [hc.mul_pow, hz2, hu2, one_mul]
  · intro h1
    exact mul_notMem_of_orderOf_eq_two hz hu hne (by simp [h1])

end OddCorePackage

theorem oddcore_package {G : Type*} [Group G] [Finite G] {z u : G} (hz : orderOf z = 2)
    (hu : orderOf u = 2) (hzu : z * u = u * z) (hne : z ≠ u)
    (hone : ∀ w : G, orderOf w = 2 → IsConj z w)
    (hCpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) →
      r = 2 ∨ r = 3 ∨ r = 5)
    (hC5 : (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 5 ≤ 2)
    (A S : Subgroup G) (hzA : z ∈ A) (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    (hSA : S ≤ A) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex A) (hzS : z ∈ S)
    (hzZ : ∀ s ∈ S, s * z = z * s)
    (hwc : ∀ g ∈ A, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z) :
    ∃ O : Subgroup G, O ≤ A ∧ (∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) ∧ Odd (Nat.card O) ∧
      (∀ a ∈ A, ∃ c ∈ A, c * z = z * c ∧ ∃ o ∈ O, a = c * o) ∧
      (∀ N : Subgroup G, N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) → Odd (Nat.card N) →
        N ≤ O) ∧
      (∀ o ∈ O, u * o * u⁻¹ ∈ O) ∧
      (∀ r : ℕ, r.Prime → r ∣ Nat.card O → r = 3 ∨ r = 5) ∧
      (Nat.card ↥(O ⊓ Subgroup.centralizer ({z} : Set G))).factorization 5 ≤ 2 ∧
      (Nat.card ↥(O ⊓ Subgroup.centralizer ({u} : Set G))).factorization 5 ≤ 2 ∧
      (Nat.card ↥(O ⊓ Subgroup.centralizer ({z * u} : Set G))).factorization 5 ≤ 2 := by
  obtain ⟨O, hOA, hOnorm, hOodd, hOfac, hOmax⟩ :=
    zstar_ambient A hzA hz S hSA hS2 hSidx hzS hzZ hwc
  have hui : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hu
  have huO : ∀ o ∈ O, u * o * u⁻¹ ∈ O := by
    let N : Subgroup G := O.map (MulAut.conj u).toMonoidHom
    have hmem : ∀ o ∈ O, u * o * u⁻¹ ∈ N := fun o ho =>
      Subgroup.mem_map.mpr ⟨o, ho, by simp⟩
    have hNA : N ≤ A := by
      intro n hn
      obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hn
      exact huA o (hOA ho)
    have hNnorm : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
      intro a ha n hn
      obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hn
      have ha' : u⁻¹ * a * u ∈ A := by
        rw [hui]
        simpa [hui] using huA a ha
      have h1 := hmem _ (hOnorm _ ha' o ho)
      have e : a * (MulAut.conj u).toMonoidHom o * a⁻¹ =
          u * ((u⁻¹ * a * u) * o * (u⁻¹ * a * u)⁻¹) * u⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact h1
    have hNodd : Odd (Nat.card N) := by
      have : Nat.card N = Nat.card O :=
        Subgroup.card_map_of_injective (MulAut.conj u).injective
      rw [this]
      exact hOodd
    intro o ho
    exact hOmax N hNA hNnorm hNodd (hmem o ho)
  have hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O := fun o ho => hOnorm z hzA o ho
  have hvord : ∀ v ∈ ({z, u, z * u} : Set G), orderOf v = 2 := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with h | h | h <;> rw [h]
    · exact hz
    · exact hu
    · exact orderOf_mul_eq_two_of_commute hz hu hzu hne
  have hdvd : ∀ v : G, orderOf v = 2 →
      Nat.card ↥(O ⊓ Subgroup.centralizer ({v} : Set G)) ∣
        Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    intro v hv
    rw [card_centralizer_eq_of_isConj (hone v hv)]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hπ : ∀ v ∈ ({z, u, z * u} : Set G), ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ↥(O ⊓ Subgroup.centralizer ({v} : Set G)) → r = 3 ∨ r = 5 := by
    intro v hv r hr hrd
    have hrC : r ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) :=
      hrd.trans (hdvd v (hvord v hv))
    have hrO : r ∣ Nat.card O := hrd.trans (Subgroup.card_dvd_of_le inf_le_left)
    rcases hCpr r hr hrC with h | h | h
    · exact absurd (h ▸ hrO) hOodd.not_two_dvd_nat
    · exact Or.inl h
    · exact Or.inr h
  have h5 : ∀ v : G, orderOf v = 2 →
      (Nat.card ↥(O ⊓ Subgroup.centralizer ({v} : Set G))).factorization 5 ≤ 2 := by
    intro v hv
    refine le_trans ?_ hC5
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr (hdvd v hv) 5
  exact ⟨O, hOA, hOnorm, hOodd, hOfac, hOmax, huO,
    odd_prime_support hz hu hzu hne O hOodd hOz huO (fun r => r = 3 ∨ r = 5) hπ,
    h5 z hz, h5 u hu, h5 (z * u) (orderOf_mul_eq_two_of_commute hz hu hzu hne)⟩

theorem sl2_nine_odd_normal_trivial {G : Type*} [Group G] (K N : Subgroup G) (hNK : N ≤ K)
    (hN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hodd : Odd (Nat.card N))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) [Finite G] : N = ⊥ := by
  have hKcard : Nat.card K = 720 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_specialLinearGroup_two_nine hF
  have hnorm : (N.subgroupOf K).Normal := ⟨fun n hn g => hN g g.2 n hn⟩
  have hcardN : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hmul : Nat.card N * Nat.card (↥K ⧸ N.subgroupOf K) = 720 := by
    rw [← hcardN, ← hKcard, ← Subgroup.index_eq_card, mul_comm, Subgroup.index_mul_card]
  have hodd2 := Nat.odd_iff.mp hodd
  by_cases h360 : 360 ∣ Nat.card (↥K ⧸ N.subgroupOf K)
  ·
    obtain ⟨j, hj⟩ := h360
    rw [hj] at hmul
    have h1 : 360 * (Nat.card N * j) = 360 * 2 := by
      calc 360 * (Nat.card N * j) = Nat.card N * (360 * j) := by ring
        _ = 720 := hmul
        _ = 360 * 2 := by norm_num
    have h2 : Nat.card N * j = 2 := Nat.eq_of_mul_eq_mul_left (by norm_num) h1
    have h3 : Nat.card N ∣ 2 := ⟨j, h2.symm⟩
    have h4 : Nat.card N ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    exact Subgroup.eq_bot_of_card_eq N (by omega)
  ·
    exfalso
    have hψ := sl2_nine_hom_trivial hF e (QuotientGroup.mk' (N.subgroupOf K)) h360
    have htop : N.subgroupOf K = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      have := DFunLike.congr_fun hψ x
      simpa using this
    have hcardtop : Nat.card (N.subgroupOf K) = 720 := by
      rw [htop, Subgroup.card_top, hKcard]
    omega

theorem sl2_nine_inf_odd_normal_trivial {G : Type*} [Group G] [Finite G] (K O : Subgroup G)
    (hKO : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O) (hodd : Odd (Nat.card O))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) : ∀ x ∈ K, x ∈ O → x = 1 := by
  intro x hxK hxO
  have hbot := sl2_nine_odd_normal_trivial K (K ⊓ O) inf_le_left
    (fun k hk n hn =>
      Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk (Subgroup.mem_inf.mp hn).1) (inv_mem hk),
        hKO k hk n (Subgroup.mem_inf.mp hn).2⟩)
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_right)) hF e
  have hx : x ∈ K ⊓ O := Subgroup.mem_inf.mpr ⟨hxK, hxO⟩
  rw [hbot] at hx
  exact Subgroup.mem_bot.mp hx

end CFSG.GH74.GLS.Stage4.Q9
