module

public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd
public import CFSG.Walter.W67.CentralExt

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Transfer

theorem exists_sylow_isMulCommutative_of_ker_le_center {E L : Type*} [Group E] [Finite E]
    [Group L] [Finite L] (π : E →* L) (hker : π.ker ≤ Subgroup.center E) {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ Q : Sylow p L, IsCyclic (Q : Subgroup L)) :
    ∃ P : Sylow p E, IsMulCommutative (P : Subgroup E) := by
  obtain ⟨P⟩ : Nonempty (Sylow p E) := inferInstance
  refine ⟨P, ?_⟩
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map π).exists_le_sylow
  let f := (π.comp (P : Subgroup E).subtype).rangeRestrict
  have : IsCyclic (π.comp (P : Subgroup E).subtype).range := by
    refine Bender.isCyclic_of_le_isCyclic (hcyc Q) ?_
    rintro _ ⟨x, rfl⟩
    exact hQ ⟨x, x.2, rfl⟩
  have hf : f.ker ≤ Subgroup.center (P : Subgroup E) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    have hxc : (x : E) ∈ Subgroup.center E := hker hx
    rw [Subgroup.mem_center_iff] at hxc ⊢
    intro y
    exact Subtype.ext (hxc y)
  exact f.isMulCommutative_of_isCyclic_of_ker_le_center hf

theorem inf_commutator_eq_bot_of_odd_central {E : Type*} [Group E] [Finite E] {R : Subgroup E}
    [R.Normal] (hR : R ≤ Subgroup.center E) (hodd : Odd (Nat.card R))
    (hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Sylow p (E ⧸ R), IsCyclic (P : Subgroup (E ⧸ R))) :
    R ⊓ commutator E = ⊥ := by
  refine CFSG.Walter.W67.inf_commutator_eq_bot hR fun p hp hpR => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpR)
  obtain ⟨P, hP⟩ := exists_sylow_isMulCommutative_of_ker_le_center (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk']; exact hR) (hcyc p hp hp2)
  exact ⟨⟨hp⟩, P, hP⟩

end Transfer

namespace Bender

theorem BenderType.isCyclic_sylow_of_odd
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (hi : i = 1 ∨ i = 2) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (P : Sylow p K) : IsCyclic (P : Subgroup K) := by
  have hodd : Odd (Nat.card (P : Subgroup K)) := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk]
    exact (Fact.out (p := p.Prime)).odd_of_ne_two hp |>.pow
  have htriv : Nat.card (P : Subgroup K) = 1 → IsCyclic (P : Subgroup K) := fun h1 =>
    @isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.mp h1).1
  rcases hi with rfl | rfl
  · have he : e = 1 := by
      rcases h.cases' with ⟨-, he, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩
      · exact he
      · omega
      · omega
    subst he
    rcases h.linear_subgroup_cases (P : Subgroup K) with h1 | ⟨-, hcyc, -⟩ | ⟨z, -, -, hc, -⟩ |
      ⟨h2, -⟩ | ⟨m, hm, -, ⟨φ⟩⟩ | h6
    · obtain ⟨k, hk⟩ := h1.exists_card_eq
      have hk0 : k = 0 := by
        by_contra hk0
        have : 2 ∣ Nat.card (P : Subgroup K) := by rw [hk]; exact dvd_pow_self 2 hk0
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
      exact htriv (by rw [hk, hk0, pow_zero])
    · exact hcyc
    · exact absurd hodd (by rw [hc]; simp)
    · exact absurd hodd (Nat.not_odd_iff_even.mpr h2)
    · exact absurd hodd (Nat.not_odd_iff_even.mpr (BenderType.even_card_of_psl2 hm φ))
    · exact absurd hodd (by rw [h6]; decide)
  · by_cases hP : (P : Subgroup K) = ⊥
    · exact htriv (by rw [hP, Subgroup.card_bot])
    · obtain ⟨T, hPT, hT, -⟩ := h.suzuki_odd_subgroup hodd hP
      exact isCyclic_of_le_isCyclic hT hPT

end Bender

section Splitting

open Bender

theorem center_eq_bot_of_benderType
    {E : Type*} [Group E] [Finite E] {n i e : ℕ}
    (hi : i = 1 ∨ i = 2) (hgen : Subgroup.closure {x : E | x * x = 1} = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center E)))
    (h : BenderType (E ⧸ Subgroup.center E) n i e) : Subgroup.center E = ⊥ := by
  have hint : Subgroup.center E ⊓ commutator E = ⊥ :=
    inf_commutator_eq_bot_of_odd_central le_rfl hodd fun p hp hp2 P => by
      have : Fact p.Prime := ⟨hp⟩
      exact h.isCyclic_sylow_of_odd hi hp2 P
  have hsq : ∀ g : E, g * g ∈ commutator E := by
    let φ : E →* Abelianization E := (powMonoidHom 2).comp Abelianization.of
    have hφ : ∀ g, φ g = Abelianization.of (g * g) := fun g => by simp [φ, sq]
    have hker : Subgroup.closure {x : E | x * x = 1} ≤ φ.ker := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ, show x * x = 1 from hx, map_one]
    intro g
    have h1 : φ g = 1 := MonoidHom.mem_ker.mp (hker (by rw [hgen]; exact Subgroup.mem_top g))
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, ← hφ]
    exact h1
  rw [eq_bot_iff]
  intro r hr
  have hr2 : r * r ∈ Subgroup.center E ⊓ commutator E := ⟨mul_mem hr hr, hsq r⟩
  rw [hint, Subgroup.mem_bot] at hr2
  rw [Subgroup.mem_bot]
  have hord : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hr2)
  have hdvd : orderOf r ∣ Nat.card (Subgroup.center E) := by
    have := orderOf_dvd_natCard (⟨r, hr⟩ : Subgroup.center E)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem benderType_of_center_eq_bot {E : Type*} [Group E] {n i e : ℕ}
    (h : BenderType (E ⧸ Subgroup.center E) n i e) (hc : Subgroup.center E = ⊥) :
    BenderType E n i e :=
  h.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

end Splitting

end CFSG.GH74.Uniqueness
