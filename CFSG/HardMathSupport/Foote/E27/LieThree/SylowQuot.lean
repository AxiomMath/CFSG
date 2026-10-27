module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem range_map_sub {G H : Type*} [Group G] [Group H] (P : Subgroup G) (π : G →* H) :
    (π.comp P.subtype).range = P.map π := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem E27Config.false_of_sylow_table_quot (h : E27Config X K R T z) (hz : z ∈ K)
    {G : Type*} [Group G] [Finite G] (π : G →* ↥K) (hπ : Function.Surjective π)
    (hker : ∀ x ∈ π.ker, x ^ 2 = 1) (P : Subgroup G)
    (hP : Nat.card P = 3 ^ (Nat.card G).factorization 3)
    (hprop : ∀ s ∈ P, orderOf s = 3 → 81 ∣ Nat.card ↥(P ⊓ centralizer ({s} : Set G))) :
    False := by
  have hPker : ∀ x ∈ P, π x = 1 → x = 1 := by
    intro x hx h1
    have hxk : x ∈ π.ker := h1
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hker x hxk)
    have h3 : orderOf x ∣ 3 ^ (Nat.card G).factorization 3 := by
      rw [← hP]; exact Subgroup.orderOf_dvd_natCard P hx
    have hg : orderOf x ∣ Nat.gcd (3 ^ (Nat.card G).factorization 3) 2 := Nat.dvd_gcd h3 h2
    have hc : Nat.gcd (3 ^ (Nat.card G).factorization 3) 2 = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left _ (by norm_num))
    rw [hc] at hg
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    intro hd
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 3 hd
    have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hker x.1 x.2))
    rw [hx] at this
    omega
  have hcard : Nat.card G = Nat.card ↥K * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have hfac : (Nat.card G).factorization 3 = (Nat.card ↥K).factorization 3 := by
    rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hk3, add_zero]
  have hinj : Function.Injective (π.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hPker x.1 x.2 hx)
  have hS₀ : Nat.card (P.map π) = 3 ^ (Nat.card ↥K).factorization 3 := by
    rw [← hfac, ← hP, ← range_map_sub P π]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine h.false_of_sylow_table hz (MulEquiv.refl ↥K) (P.map π) hS₀ ?_
  rintro _ ⟨s, hs, rfl⟩ ho
  have hs1 : s ≠ 1 := fun e => by
    rw [e, map_one, orderOf_one] at ho; omega
  have hs3 : s ^ 3 = 1 := by
    have h3 : π (s ^ 3) = 1 := by
      rw [map_pow, ← ho]; exact pow_orderOf_eq_one _
    exact hPker _ (pow_mem hs 3) h3
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have h81 := hprop s hs hso
  set Q := P ⊓ centralizer ({s} : Set G) with hQ
  have hQP : Q ≤ P := inf_le_left
  have hinjQ : Function.Injective (π.comp Q.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hPker x.1 (hQP x.2) hx)
  have hcQ : Nat.card (Q.map π) = Nat.card Q := by
    rw [← range_map_sub Q π]; exact (Nat.card_congr (MonoidHom.ofInjective hinjQ).toEquiv).symm
  have hle : Q.map π ≤ P.map π ⊓ centralizer ({π s} : Set ↥K) := by
    refine le_inf (map_mono hQP) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := (mem_centralizer_iff.1 ((inf_le_right : Q ≤ centralizer ({s} : Set G)) hx)) s (Set.mem_singleton s)
    rw [← map_mul, ← map_mul, this]
  rw [← hcQ] at h81
  exact h81.trans (Subgroup.card_dvd_of_le hle)

end CFSG.HardMathSupport.Foote.E27
