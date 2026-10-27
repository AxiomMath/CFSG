module

public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

open Subgroup

namespace CFSG.LieType.Steinberg.CentralExt.PrimeCover

theorem ker_eq_bot_of_forall_prime {H : Type*} [Group H]
    (htriv : ∀ (ℓ : ℕ), ℓ.Prime → ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
      (η : P →* H), Function.Surjective η → η.ker ≤ center P → IsPGroup ℓ η.ker → η.ker = ⊥)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* H)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) : π.ker = ⊥ := by
  by_contra hne
  have h1 : Nat.card π.ker ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  set ℓ := (Nat.card π.ker).minFac with hℓdef
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  have hdvd : ℓ ∣ Nat.card π.ker := Nat.minFac_dvd _
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set N := CoprimeSplit.copPart ℓ π.ker hcen
  have hNker : N ≤ π.ker := fun _ h => h.1
  let π₁ : E ⧸ N →* H := QuotientGroup.lift N π hNker
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
  have hp₁ : IsPGroup ℓ π₁.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hy
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := ℓ) hcen he
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (E ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have h0 := htriv ℓ hℓ (E ⧸ N) π₁ hπ₁ hker₁ hp₁
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hgN : (g : E) ∈ N := by
    have hmem : ((g : E) : E ⧸ N) ∈ π₁.ker := by
      rw [MonoidHom.mem_ker, hπ₁e]
      exact g.2
    rw [h0, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hord : orderOf (g : E) = ℓ := by rw [Subgroup.orderOf_coe, hg]
  have hcop := hgN.2
  rw [hord] at hcop
  exact hℓ.one_lt.ne' ((Nat.coprime_self ℓ).1 hcop)

theorem exists_section_of_forall_prime {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (htriv : ∀ (ℓ : ℕ), ℓ.Prime → ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
      (η : P →* H), Function.Surjective η → η.ker ≤ center P → IsPGroup ℓ η.ker → η.ker = ⊥)
    (E : Type) [Group E] [Finite E] (π : E →* H) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) : ∃ σ : H →* E, ∀ g, π (σ g) = g := by
  set P := CFSG.Quasithin.perfectCore (⊤ : Subgroup E)
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect _)
  set η : P →* H := π.comp P.subtype
  have hmap : P.map π = ⊤ := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_top_of_surjective π hπ]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect (by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top)
  have hη : Function.Surjective η := fun g => by
    have hg : g ∈ P.map π := hmap ▸ Subgroup.mem_top g
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : η.ker ≤ center P := fun x hx => by
    have hx' : (x : E) ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)
    exact mem_center_iff.2 fun y => Subtype.ext (mem_center_iff.1 (hcen hx') y)
  have hinj : Function.Injective η :=
    (MonoidHom.ker_eq_bot_iff η).1 (ker_eq_bot_of_forall_prime htriv η hη hker)
  let e : P ≃* H := MulEquiv.ofBijective η ⟨hinj, hη⟩
  exact ⟨P.subtype.comp e.symm.toMonoidHom, fun g => e.apply_symm_apply g⟩

end CFSG.LieType.Steinberg.CentralExt.PrimeCover
