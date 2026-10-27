module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenCentralizer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar
open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem N_inf_centralizer_inf_M [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} (hx : x ∈ fr.N) (hxM : x ∉ fr.M) :
    fr.N ⊓ centralizer ({x} : Set G) ⊓ fr.M = fr.ZN := by
  rw [← M_inf_centralizer p7 p10 hz x hx hxM, inf_comm, ← inf_assoc, inf_eq_left.mpr M_le_N]

theorem card_N_inf_centralizer_le [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} (hx : x ∈ fr.N) (hxM : x ∉ fr.M) :
    Nat.card (fr.N ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 3 ^ 5 := by
  have hle : fr.N ⊓ centralizer ({x} : Set G) ≤ normalizer (fr.M : Set G) :=
    inf_le_left.trans (N_le_centralizer_P₁.trans centralizer_P₁_le_normalizer_M)
  have h := card_sup_mul_card_inf hle
  rw [N_inf_centralizer_inf_M p7 p10 hz hx hxM, card_ZN p7 p10 hz, p10.card_M] at h
  have hsup : Nat.card (fr.N ⊓ centralizer ({x} : Set G) ⊔ fr.M : Subgroup G) ≤ 3 ^ 7 :=
    card_N p10 ▸ Subgroup.card_le_of_le (sup_le inf_le_left M_le_N)
  have h2 : Nat.card (fr.N ⊓ centralizer ({x} : Set G) : Subgroup G) * 3 ^ 5 ≤ 3 ^ 5 * 3 ^ 5 := by
    calc Nat.card (fr.N ⊓ centralizer ({x} : Set G) : Subgroup G) * 3 ^ 5 =
          Nat.card (fr.N ⊓ centralizer ({x} : Set G) ⊔ fr.M : Subgroup G) * 27 := h.symm
      _ ≤ 3 ^ 7 * 27 := Nat.mul_le_mul_right _ hsup
      _ = 3 ^ 5 * 3 ^ 5 := by norm_num
  exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

theorem card_N_inf_centralizer_ge [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} (hx : x ∈ fr.N) :
    3 ^ 5 ≤ Nat.card (fr.N ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  obtain ⟨W, hW, hcard⟩ := exists_commutator_subgroup (A := fr.N) (x := x) fun n hn =>
    S_le_ZN (commutator_mem_S_of_mem_N p7 p10 hz hn hx)
  have hWS : W ≤ fr.S := fun w hw => by
    obtain ⟨n, hn, rfl⟩ := (hW w).mp hw
    exact commutator_mem_S_of_mem_N p7 p10 hz hn hx
  have h9 : Nat.card W ≤ 9 := card_S_eq p7 p10 hz ▸ Subgroup.card_le_of_le hWS
  rw [card_N p10] at hcard
  have h2 : 3 ^ 5 * 9 ≤ Nat.card (fr.N ⊓ centralizer ({x} : Set G) : Subgroup G) * 9 := by
    calc 3 ^ 5 * 9 = Nat.card (fr.N ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card W := by
          rw [← hcard]; norm_num
      _ ≤ _ := Nat.mul_le_mul_left _ h9
  exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

theorem card_N_inf_centralizer [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} (hx : x ∈ fr.N) (hxM : x ∉ fr.M) :
    Nat.card (fr.N ⊓ centralizer ({x} : Set G) : Subgroup G) = 3 ^ 5 :=
  le_antisymm (card_N_inf_centralizer_le p7 p10 hz hx hxM) (card_N_inf_centralizer_ge p7 p10 hz hx)

theorem card_zpowers_sup_ZN [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} (hx : x ∈ fr.N) (hxM : x ∉ fr.M) :
    Nat.card (zpowers x ⊔ fr.ZN : Subgroup G) = 3 ^ 4 := by
  have hx1 : x ≠ 1 := fun h => hxM (h ▸ one_mem _)
  have hord : orderOf x = 3 := orderOf_eq_prime (N_pow_three p7 p10 hz x hx) hx1
  have hle : zpowers x ≤ normalizer (fr.ZN : Set G) := zpowers_le.mpr
    (centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ hh =>
      (comm_of_mem_ZN hh hx).symm))
  have h := card_sup_mul_card_inf hle
  have h3 : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
  have hbot : zpowers x ⊓ fr.ZN = ⊥ := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : zpowers x ⊓ fr.ZN ≤ zpowers x)
    rw [h3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : zpowers x ⊓ fr.ZN ≤ zpowers x)
        (by rw [h1, h3])
      have hxZ : x ∈ zpowers x ⊓ fr.ZN := by rw [heq]; exact mem_zpowers x
      exact hxM (ZN_le_M p10 hxZ.2)
  rw [hbot, Subgroup.card_bot, mul_one, h3, card_ZN p7 p10 hz] at h
  rw [h]
  norm_num

theorem comm_of_mem_N_inf_centralizer [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} (hx : x ∈ fr.N) (hxM : x ∉ fr.M) :
    ∀ a ∈ fr.N ⊓ centralizer ({x} : Set G), ∀ b ∈ fr.N ⊓ centralizer ({x} : Set G),
      a * b = b * a := by
  set C := fr.N ⊓ centralizer ({x} : Set G) with hC
  set B₀ := zpowers x ⊔ fr.ZN with hB₀
  have hB₀C : B₀ ≤ C := sup_le (zpowers_le.mpr ⟨hx, mem_centralizer_singleton_iff.mpr rfl⟩)
    fun y hy => ⟨hy.1, mem_centralizer_singleton_iff.mpr (comm_of_mem_ZN hy hx).symm⟩
  have hcomm : ∀ y ∈ C, C ≤ centralizer ({y} : Set G) := by
    intro y hy
    by_cases hyB : y ∈ B₀
    · intro c hc
      have hle : B₀ ≤ centralizer ({c} : Set G) := sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hc.2).symm))
        fun w hw => mem_centralizer_singleton_iff.mpr (comm_of_mem_ZN hw hc.1).symm
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hle hyB)).symm
    · set B₁ := B₀ ⊔ zpowers y with hB₁
      have hB₁C : B₁ ≤ C := sup_le hB₀C (zpowers_le.mpr hy)
      have hdvd : Nat.card B₁ ∣ 3 ^ 5 :=
        card_N_inf_centralizer p7 p10 hz hx hxM ▸ Subgroup.card_dvd_of_le hB₁C
      have h81 : 3 ^ 4 ∣ Nat.card B₁ :=
        card_zpowers_sup_ZN p7 p10 hz hx hxM ▸ Subgroup.card_dvd_of_le le_sup_left
      have hne : Nat.card B₁ ≠ 3 ^ 4 := fun h => hyB (by
        have heq : B₀ = B₁ := Subgroup.eq_of_le_of_card_ge le_sup_left
          (by rw [h, card_zpowers_sup_ZN p7 p10 hz hx hxM])
        rw [heq]
        exact mem_sup_right (mem_zpowers y))
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rw [hk'] at h81 hne
      have hk4 : 4 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h81
      have hk5 : k = 5 := by
        rcases Nat.lt_or_ge k 5 with h | h
        · exact absurd (by rw [show k = 4 by omega]) hne
        · omega
      have heq : B₁ = C := Subgroup.eq_of_le_of_card_ge hB₁C
        (by rw [hk', hk5, card_N_inf_centralizer p7 p10 hz hx hxM])
      rw [← heq]
      refine sup_le (sup_le ?_ ?_) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hy.2).symm)
      · exact fun w hw => mem_centralizer_singleton_iff.mpr (comm_of_mem_ZN hw hy.1).symm
  intro a ha b hb
  exact mem_centralizer_singleton_iff.mp (hcomm b hb ha)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
