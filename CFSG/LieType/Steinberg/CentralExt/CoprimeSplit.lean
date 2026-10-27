module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

open Subgroup

namespace CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

section CopPart

variable {E : Type*} [Group E]

@[expose] def copPart (p : ℕ) (C : Subgroup E) (hC : C ≤ center E) : Subgroup E where
  carrier := {c | c ∈ C ∧ p.Coprime (orderOf c)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨C.mul_mem ha hb, Nat.Coprime.coprime_dvd_right ?_ (Nat.Coprime.mul_right ha' hb')⟩
    exact (Commute.orderOf_mul_dvd_lcm (mem_center_iff.1 (hC hb) a)).trans (Nat.lcm_dvd_mul _ _)
  one_mem' := ⟨C.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨C.inv_mem ha, by rwa [orderOf_inv]⟩

theorem mem_copPart {p : ℕ} {C : Subgroup E} {hC : C ≤ center E} {c : E} :
    c ∈ copPart p C hC ↔ c ∈ C ∧ p.Coprime (orderOf c) :=
  Iff.rfl

instance copPart_normal (p : ℕ) (C : Subgroup E) (hC : C ≤ center E) :
    (copPart p C hC).Normal :=
  ⟨fun _ hn g => by
    rw [mem_center_iff.1 (hC hn.1) g, mul_inv_cancel_right]
    exact hn⟩

theorem exists_pow_prime_pow_mem_copPart [Finite E] {p : ℕ} [hp : Fact p.Prime] {C : Subgroup E}
    (hC : C ≤ center E) {c : E} (hc : c ∈ C) : ∃ a : ℕ, c ^ p ^ a ∈ copPart p C hC := by
  obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' p
    hp.out.one_lt.ne'
  refine ⟨a, C.pow_mem hc _, ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) ⟨m, hcm⟩, hcm,
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos _)]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hm

end CopPart

universe u

variable {E K : Type u} [Group E] [Group K]

theorem exists_section_of_parts [Finite E] {p : ℕ} [hp : Fact p.Prime] {π : E →* K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E)
    (hP : ∀ (E' : Type u) [Group E'] [Finite E'] (π' : E' →* K), Function.Surjective π' →
      π'.ker ≤ center E' → IsPGroup p π'.ker → ∃ σ : K →* E', ∀ g, π' (σ g) = g)
    (hQ : ∀ (E' : Type u) [Group E'] [Finite E'] (π' : E' →* K), Function.Surjective π' →
      π'.ker ≤ center E' → p.Coprime (Nat.card π'.ker) → ∃ σ : K →* E', ∀ g, π' (σ g) = g) :
    ∃ σ : K →* E, ∀ g, π (σ g) = g := by
  set N := copPart p π.ker hcen
  have hNker : N ≤ π.ker := fun _ h => h.1
  let π₁ : E ⧸ N →* K := QuotientGroup.lift N π hNker
  have hπ₁e : ∀ e : E, π₁ (e : E ⧸ N) = π e := fun e => rfl
  have hπ₁ : Function.Surjective π₁ := fun g => by
    obtain ⟨e, rfl⟩ := hπ g
    exact ⟨(e : E ⧸ N), rfl⟩
  have hker₁ : π₁.ker ≤ center (E ⧸ N) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hy
    rw [mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hcen he) z']
  have hp₁ : IsPGroup p π₁.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hy
    obtain ⟨a, ha⟩ := exists_pow_prime_pow_mem_copPart (p := p) hcen he
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    exact ha
  obtain ⟨σ₁, hσ₁⟩ := hP (E ⧸ N) π₁ hπ₁ hker₁ hp₁
  set E₂ : Subgroup E := σ₁.range.comap (QuotientGroup.mk' N)
  let π₂ : E₂ →* K := π.comp E₂.subtype
  have hπ₂ : Function.Surjective π₂ := fun g => by
    obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (σ₁ g)
    refine ⟨⟨e, ⟨g, he.symm⟩⟩, ?_⟩
    change π e = g
    rw [← hπ₁e, he, hσ₁]
  have hker₂ : π₂.ker ≤ center E₂ := fun x hx => by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_center_iff.1 (hcen hx)) y)
  have hker₂N : ∀ x : E₂, x ∈ π₂.ker → (x : E) ∈ N := fun x hx => by
    obtain ⟨g, hg⟩ := x.2
    have hπx : π x = 1 := hx
    have hg1 : g = 1 := by
      have := hσ₁ g
      rw [hg] at this
      change π₁ ((x : E) : E ⧸ N) = g at this
      rw [hπ₁e, hπx] at this
      exact this.symm
    rw [hg1, map_one] at hg
    exact (QuotientGroup.eq_one_iff _).1 hg.symm
  have hcop : p.Coprime (Nat.card π₂.ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hgN := hker₂N g g.2
    have hord : orderOf ((g : E₂) : E) = p := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
    have := hgN.2
    rw [hord] at this
    exact hp.out.one_lt.ne' ((Nat.coprime_self p).1 this)
  obtain ⟨σ₂, hσ₂⟩ := hQ E₂ π₂ hπ₂ hker₂ hcop
  exact ⟨E₂.subtype.comp σ₂, fun g => hσ₂ g⟩

end CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
