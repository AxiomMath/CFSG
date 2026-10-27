module

public import CFSG.GH74.Uniqueness.SU.SU13TA3E
public import CFSG.GH74.Uniqueness.SU.SU13TA9PermE
public import CFSG.GH74.Uniqueness.SU.SU13TA9F

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Subgroup

namespace L9

open Equiv Equiv.Perm

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem exists_Es (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1)
    {E : Subgroup H} (hE3' : IsPGroup 3 E) (hEmap : E.map π = Ebar) :
    ∃ Es : Subgroup H, c.s₁ ∈ E ∧ E ≤ Es ∧ Nat.card E = 27 ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ IsPGroup 3 Es ∧ Nat.card Es = 81 ∧
      (∀ x ∈ Es, x * z = z * x) ∧
      (∀ R : Subgroup H, (∀ x ∈ R, x * z = z * x) → IsPGroup 3 R → Es ≤ R → R = Es) ∧
      (∀ A : Subgroup H, A ≤ Es → Nat.card A = 27 → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = E) ∧
      (centralizer (E : Set H) ⊓ centralizer ({z} : Set H) = E ⊔ zpowers z) := by
  have := hπ.finite'
  have hE3 : IsPGroup 3 Ebar := IsPGroup.of_card (n := 3) (by rw [card_Ebar]; norm_num)
  have hP3 : IsPGroup 3 Pst := IsPGroup.of_card (n := 4) (by rw [card_Pst]; norm_num)
  obtain ⟨Es, hEs3, hEsmap⟩ := hπ.exists_lift_isPGroup_three hP3
  have hEcard : Nat.card E = 27 := by
    rw [← hπ.card_map_of_isPGroup_three hE3', hEmap, card_Ebar]
  have hEscard : Nat.card Es = 81 := by
    rw [← hπ.card_map_of_isPGroup_three hEs3, hEsmap, card_Pst]
  have hEEs : E ≤ Es := hπ.le_of_map_le_of_isPGroup_three hE3' hEs3
    (by rw [hEmap, hEsmap]; exact Ebar_le_Pst)
  have hzcen : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hz2 : z ^ 2 = 1 := hπ.sq_eq_one_of_mem_ker' hz
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzcen g)
  have hmapE : ∀ x ∈ E, π x ∈ Ebar := fun x hx => hEmap ▸ Subgroup.mem_map_of_mem π hx
  refine ⟨Es, ?_, hEEs, hEcard, ?_, hEs3, hEscard, fun x _ => hzcen x, ?_, ?_, ?_⟩
  ·
    have hec : π c.s₁ ∈ E.map π := by rw [hEmap, c.π_s₁]; exact ec_mem_Ebar
    obtain ⟨y, hyE, hy⟩ := hec
    have : y = c.s₁ := hπ.eq_of_odd_orderOf_of_map_eq
      (TwoCover.odd_orderOf_of_mem_isPGroup_three hE3' hyE) (odd_orderOf_s₁ c) hy
    rw [← this]
    exact hyE
  ·
    intro a ha b hb
    have hab : Commute (π a) (π b) := Ebar_comm _ (hmapE a ha) _ (hmapE b hb)
    exact (hπ.commute_of_odd_orderOf (TwoCover.odd_orderOf_of_mem_isPGroup_three hE3' hb) hab).eq
  ·
    intro R _ hR hEsR
    have hdvd : Nat.card R ∣ Nat.card H := Subgroup.card_subgroup_dvd_card R
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
    have hH : Nat.card H = 362880 := by
      rw [hπ.card, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hk4 : k ≤ 4 := by
      by_contra hcon
      have h5 : 3 ^ 5 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      rw [← hk] at h5
      have h5' : 3 ^ 5 ∣ Nat.card H := h5.trans hdvd
      rw [hH] at h5'
      revert h5'
      decide
    have hRle : Nat.card R ≤ Nat.card Es := by
      rw [hk, hEscard]
      calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
        _ = 81 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hEsR hRle).symm
  ·
    intro A hAEs hAcard hAab
    have hA3 : IsPGroup 3 A := hEs3.to_le hAEs
    have hAmap_card : Nat.card (A.map π) = 27 := by
      rw [hπ.card_map_of_isPGroup_three hA3, hAcard]
    have hAmap_le : A.map π ≤ Pst := by
      rw [← hEsmap]
      exact Subgroup.map_mono hAEs
    have hAmap_ab : ∀ x ∈ A.map π, ∀ y ∈ A.map π, Commute x y := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show π a * π b = π b * π a
      rw [← map_mul, ← map_mul, hAab a ha b hb]
    have hAeq : A.map π = Ebar := eq_Ebar_of_abelian_card_27 hAmap_le hAmap_ab hAmap_card
    exact hπ.eq_of_map_eq_of_isPGroup_three hA3 hE3' (hAeq.trans hEmap.symm)
  ·
    rw [hzz, inf_top_eq, hπ.centralizer_eq_comap_of_isPGroup_three hE3', hEmap, centralizer_Ebar]
    have hle : E ⊔ zpowers z ≤ Ebar.comap π := by
      refine sup_le (fun x hx => ?_) ?_
      · rw [Subgroup.mem_comap]
        exact hmapE x hx
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
        exact Ebar.one_mem
    have hdisj : Disjoint E (zpowers z) := by
      rw [Subgroup.disjoint_def]
      intro x hxE hxz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
      rw [zpow_eq_zpow_emod k (show z ^ (2 : ℤ) = 1 by exact_mod_cast hz2)] at hxE ⊢
      have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hk with hk | hk
      · rw [hk]; exact zpow_zero z
      · rw [hk] at hxE
        have hzE : z ∈ E := by simpa using hxE
        have := TwoCover.odd_orderOf_of_mem_isPGroup_three hE3' hzE
        rw [orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) hz2 hz1] at this
        exact absurd this (by decide)
    have hcomm : ∀ x ∈ E, ∀ y ∈ zpowers z, Commute x y := by
      intro x _ y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (show Commute x z from hzcen x).zpow_right k
    have hcard2 : Nat.card ↥(E ⊔ zpowers z) = 54 := by
      rw [card_sup_of_commute hcomm hdisj, hEcard, Nat.card_zpowers,
        orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) hz2 hz1]
    have hcard1 : Nat.card ↥(Ebar.comap π) = 54 := by rw [hπ.card_comap, card_Ebar]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])).symm

end L9

end CFSG.GH74.Uniqueness.SU.SU13.TA
