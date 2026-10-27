module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Card

variable {G : Type} [Group G]

theorem exists_commHom {Q K : Subgroup G} (hQ' : ⁅Q, Q⁆ ≤ zOf Q) (hKQ : K ≤ Q) {y : G} (hy : y ∈ Q) :
    ∃ f : ↥K →* ↥(zOf Q), ∀ k : ↥K, ((f k : ↥(zOf Q)) : G) = ⁅(k : G), y⁆ := by
  have hmem : ∀ k : ↥K, ⁅(k : G), y⁆ ∈ zOf Q := fun k =>
    hQ' (Subgroup.commutator_mem_commutator (hKQ k.2) hy)
  refine ⟨MonoidHom.mk' (fun k => ⟨⁅(k : G), y⁆, hmem k⟩) ?_, fun k => rfl⟩
  intro a b
  apply Subtype.ext
  show ⁅((a * b : ↥K) : G), y⁆ = ⁅(a : G), y⁆ * ⁅(b : G), y⁆
  have hc : Commute (⁅(b : G), y⁆) (a : G) :=
    (Subgroup.mem_centralizer_iff.mp (hmem b).2 (a : G) (hKQ a.2)).symm
  have hcomm : Commute (⁅(a : G), y⁆) (⁅(b : G), y⁆) :=
    Subgroup.mem_centralizer_iff.mp (hmem b).2 (⁅(a : G), y⁆) (hmem a).1
  rw [Subgroup.coe_mul, commutatorElement_mul_left_eq_conj_mul]
  calc (a : G) * ⁅(b : G), y⁆ * (a : G)⁻¹ * ⁅(a : G), y⁆ = ⁅(b : G), y⁆ * ⁅(a : G), y⁆ := by
        rw [← hc.eq]; group
    _ = ⁅(a : G), y⁆ * ⁅(b : G), y⁆ := hcomm.symm.eq

omit [Group G] in
theorem card_eq_prime_of_ne_bot {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = p) {S : Subgroup H} (hS : S ≠ ⊥) : Nat.card ↥S = p := by
  have hdvd : Nat.card ↥S ∣ p := hcard ▸ Subgroup.card_subgroup_dvd_card S
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hS
  · exact h

omit [Group G] in
theorem zpowers_eq_top_of_card_prime {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = p) {c : H} (hc : c ≠ 1) : zpowers c = ⊤ := by
  have hne : zpowers c ≠ ⊥ := by
    intro h
    apply hc
    have hmem : c ∈ zpowers c := Subgroup.mem_zpowers c
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact Subgroup.eq_top_of_card_eq _ (by rw [card_eq_prime_of_ne_bot hp hcard hne, hcard])

theorem card_eq_prime_cube [Finite G] {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQ' : ⁅Q, Q⁆ ≤ zOf Q) (hcard : Nat.card ↥(zOf Q) = p) {x : G} (hxQ : x ∈ Q) (hxZ : x ∉ zOf Q)
    (hab : ∀ a ∈ Q ⊓ centralizer ({x} : Set G), ∀ b ∈ Q ⊓ centralizer ({x} : Set G), a * b = b * a) :
    Nat.card ↥Q = p ^ 3 := by
  obtain ⟨y, hyQ, hyx⟩ : ∃ y ∈ Q, ¬ (y * x = x * y) := by
    by_contra hno
    push Not at hno
    exact hxZ ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun h hh => hno h hh⟩
  have hK'Q : Q ⊓ centralizer ({x} : Set G) ≤ Q := inf_le_left
  have hxK' : x ∈ Q ⊓ centralizer ({x} : Set G) :=
    ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_commHom hQ' (le_refl Q) hxQ
  obtain ⟨θ, hθ⟩ := exists_commHom hQ' hK'Q hyQ
  have hψy : ψ ⟨y, hyQ⟩ ≠ 1 := by
    intro h
    have h1 := hψ ⟨y, hyQ⟩
    rw [h, Subgroup.coe_one] at h1
    exact hyx (commutatorElement_eq_one_iff_mul_comm.mp h1.symm)
  have hθx : θ ⟨x, hxK'⟩ ≠ 1 := by
    intro h
    have h1 := hθ ⟨x, hxK'⟩
    rw [h, Subgroup.coe_one] at h1
    exact hyx (commutatorElement_eq_one_iff_mul_comm.mp h1.symm).symm
  have hdec : ∀ q ∈ Q, ∃ k₀ ∈ Q ⊓ centralizer ({x} : Set G), ∃ i : ℤ, q = k₀ * y ^ i := by
    intro q hq
    obtain ⟨c, hc⟩ : ∃ c, c = ψ ⟨y, hyQ⟩ := ⟨_, rfl⟩
    have hztop : zpowers c = ⊤ := zpowers_eq_top_of_card_prime hp hcard (hc ▸ hψy)
    have hmem : ψ ⟨q, hq⟩ ∈ zpowers c := hztop ▸ Subgroup.mem_top _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨q * y ^ (-i), ⟨Q.mul_mem hq (Subgroup.zpow_mem _ hyQ _), ?_⟩, i, by group⟩
    show q * y ^ (-i) ∈ centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ψ (⟨q, hq⟩ * ⟨y, hyQ⟩ ^ (-i)) = 1 := by
      rw [map_mul, map_zpow, ← hc, ← hi, ← zpow_add, add_neg_cancel, zpow_zero]
    have h2 := hψ (⟨q, hq⟩ * ⟨y, hyQ⟩ ^ (-i))
    rw [h1, Subgroup.coe_one] at h2
    have h3 : (((⟨q, hq⟩ * ⟨y, hyQ⟩ ^ (-i) : ↥Q)) : G) = q * y ^ (-i) := by simp
    rw [h3] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2.symm
  have hkerθ : (θ.ker).map (Q ⊓ centralizer ({x} : Set G)).subtype = zOf Q := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hky : ⁅(k : G), y⁆ = 1 := by
        have := hθ k
        rw [MonoidHom.mem_ker.mp hk, Subgroup.coe_one] at this
        exact this.symm
      refine ⟨hK'Q k.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      obtain ⟨k₀, hk₀, i, rfl⟩ := hdec q hq
      have h1 : k₀ * (k : G) = (k : G) * k₀ := hab k₀ hk₀ (k : G) k.2
      have hc : Commute (k : G) y := commutatorElement_eq_one_iff_mul_comm.mp hky
      have h2 : y ^ i * (k : G) = (k : G) * y ^ i := (hc.zpow_right i).symm.eq
      calc k₀ * y ^ i * (k : G) = k₀ * (y ^ i * (k : G)) := by group
        _ = k₀ * ((k : G) * y ^ i) := by rw [h2]
        _ = (k₀ * (k : G)) * y ^ i := by group
        _ = ((k : G) * k₀) * y ^ i := by rw [h1]
        _ = (k : G) * (k₀ * y ^ i) := by group
    · rintro ⟨hgQ, hgc⟩
      have hgx : g * x = x * g := (Subgroup.mem_centralizer_iff.mp hgc x hxQ).symm
      have hgK' : g ∈ Q ⊓ centralizer ({x} : Set G) :=
        ⟨hgQ, Subgroup.mem_centralizer_singleton_iff.mpr hgx⟩
      refine ⟨⟨g, hgK'⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hθ, Subgroup.coe_one]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hgc y hyQ).symm
  have hkerψ : (ψ.ker).map Q.subtype = Q ⊓ centralizer ({x} : Set G) := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hkx : ⁅(k : G), x⁆ = 1 := by
        have := hψ k
        rw [MonoidHom.mem_ker.mp hk, Subgroup.coe_one] at this
        exact this.symm
      exact ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp hkx)⟩
    · rintro ⟨hgQ, hgc⟩
      refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hψ, Subgroup.coe_one]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hgc)
  have hθrange : Nat.card ↥θ.range = p := by
    refine card_eq_prime_of_ne_bot hp hcard fun h => hθx ?_
    have : θ ⟨x, hxK'⟩ ∈ θ.range := ⟨_, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hψrange : Nat.card ↥ψ.range = p := by
    refine card_eq_prime_of_ne_bot hp hcard fun h => hψy ?_
    have : ψ ⟨y, hyQ⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hθker : Nat.card ↥θ.ker = p := by
    have h : Nat.card ↥(θ.ker.map (Q ⊓ centralizer ({x} : Set G)).subtype) = Nat.card ↥θ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [hkerθ, hcard] at h
    exact h.symm
  have hψker : Nat.card ↥ψ.ker = Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) := by
    have h : Nat.card ↥(ψ.ker.map Q.subtype) = Nat.card ↥ψ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [hkerψ] at h
    exact h.symm
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 := Subgroup.card_ker_mul_card_range θ
  rw [hψker, hψrange] at h1
  rw [hθker, hθrange] at h2
  rw [← h1, ← h2]
  ring

end Card

end CFSG.GH74.GLS.Stage2.Bender.Thm1
