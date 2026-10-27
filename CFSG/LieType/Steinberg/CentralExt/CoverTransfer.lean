module

public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LocalAnalysis.AGLEmbedding.TimmesfeldRouteAux

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.CoverTransfer

theorem ker_eq_bot_of_isogeny_cover_trivial {Γ J : Type} [Group Γ] [Group J] {p : ℕ}
    [hp : Fact p.Prime] (ψ : Γ →* J) (hψ : Function.Surjective ψ) (hker : ψ.ker = center Γ)
    (htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* J),
      Function.Surjective η → η.ker ≤ center P → IsPGroup p η.ker → η.ker = ⊥)
    (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* Γ)
    (hη : Function.Surjective η) (hC : η.ker ≤ center P) (hpk : IsPGroup p η.ker) :
    η.ker = ⊥ := by
  set N := (ψ.comp η).ker with hN
  have hNc : N ≤ center P := by
    intro x hx
    have hx' : η x ∈ center Γ := by
      rw [← hker]
      exact hx
    have hperf : commutator (P ⧸ center P) = ⊤ := by
      have : Group.IsPerfect (P ⧸ center P) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center P))
      exact Group.IsPerfect.commutator_eq_top
    have hZ := CFSG.AGLEmbedding.center_quotient_center_eq_bot_of_commutator_eq_top hperf
    have hmk : (QuotientGroup.mk' (center P) x) ∈ center (P ⧸ center P) := by
      refine mem_center_iff.2 fun y => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) y
      have hxy : ⁅x, y⁆ ∈ center P := hC (by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_center_iff.1 hx' (η y)).symm)
      have h1 : QuotientGroup.mk' (center P) ⁅x, y⁆ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hxy
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
    exact hmk
  set N₀ := CoprimeSplit.copPart p N hNc with hN₀
  let η' : P ⧸ N₀ →* J := QuotientGroup.lift N₀ (ψ.comp η) fun x hx => hx.1
  have hη'mk : ∀ x : P, η' (x : P ⧸ N₀) = ψ (η x) := fun x => rfl
  have hη' : Function.Surjective η' := fun y => by
    obtain ⟨g, rfl⟩ := hψ y
    obtain ⟨x, rfl⟩ := hη g
    exact ⟨(x : P ⧸ N₀), hη'mk x⟩
  have hmemN : ∀ x : P, (x : P ⧸ N₀) ∈ η'.ker → x ∈ N := fun x hx => by
    rw [MonoidHom.mem_ker, hη'mk] at hx
    exact hx
  have hker' : η'.ker ≤ center (P ⧸ N₀) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxc := hNc (hmemN x hy)
    refine mem_center_iff.2 fun z => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 hxc z]
  have hp' : IsPGroup p η'.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := p) hNc (hmemN x hy)
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← QuotientGroup.mk_pow, Subgroup.coe_one, QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (P ⧸ N₀) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N₀)
  have h0 := htriv (P ⧸ N₀) η' hη' hker' hp'
  rw [eq_bot_iff]
  intro x hx
  have hxN : x ∈ N := by
    rw [hN, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, map_one]
  have hx0 : x ∈ N₀ := by
    have : (x : P ⧸ N₀) ∈ η'.ker := by
      rw [MonoidHom.mem_ker, hη'mk]
      exact hxN
    rw [h0, mem_bot, QuotientGroup.eq_one_iff] at this
    exact this
  obtain ⟨k, hk⟩ := hpk ⟨x, hx⟩
  have hord : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hk
    simpa using this)
  have hcop : p.Coprime (orderOf x) := hx0.2
  have h1 : orderOf x = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 hord
    rcases i with _ | i
    · simpa using hi
    · exfalso
      rw [hi] at hcop
      exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop (dvd_pow_self p (Nat.succ_ne_zero i)))
  rw [mem_bot]
  exact orderOf_eq_one_iff.1 h1

theorem exists_section_of_isogeny_cover_trivial {Γ J : Type} [Group Γ] [Finite Γ]
    [Group.IsPerfect Γ] [Group J] {p : ℕ} [Fact p.Prime] (ψ : Γ →* J)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = center Γ)
    (htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* J),
      Function.Surjective η → η.ker ≤ center P → IsPGroup p η.ker → η.ker = ⊥)
    (E : Type) [Group E] [Finite E] (π : E →* Γ) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hpk : IsPGroup p π.ker) : ∃ σ : Γ →* E, ∀ g, π (σ g) = g :=
  FieldFour.exists_section_of_ker_eq_bot
    (fun P _ _ _ η hη hC h2 => ker_eq_bot_of_isogeny_cover_trivial ψ hψ hker htriv P η hη hC h2)
    E π hπ hcen hpk

end CFSG.LieType.Steinberg.CentralExt.CoverTransfer
