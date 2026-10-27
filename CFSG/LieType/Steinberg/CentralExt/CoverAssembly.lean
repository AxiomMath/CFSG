module

public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

open CFSG.LieType.Steinberg.CentralExt.FieldFour

namespace CFSG.LieType.Steinberg.CentralExt.CoverAssembly

theorem ker_eq_bot_of_central_quotient {H J : Type} [Group H] [Group J] {p : ℕ} [Fact p.Prime]
    {θ : H →* J} (hθ : Function.Surjective θ) (hθc : θ.ker ≤ Subgroup.center H)
    (htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* J),
      Function.Surjective η → η.ker ≤ Subgroup.center P → IsPGroup p η.ker → η.ker = ⊥)
    (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* H)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P) (hp : IsPGroup p η.ker) :
    η.ker = ⊥ := by
  set η' : P →* J := θ.comp η
  have hcen' : η'.ker ≤ Subgroup.center P := fun y hy => by
    refine mem_center_of_forall_commutator_mem_center fun g => hC ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (hθc hy) (η g)).symm
  set N := CoprimeSplit.copPart p η'.ker hcen'
  have hN : N ≤ η'.ker := fun _ h => h.1
  let η'' : P ⧸ N →* J := QuotientGroup.lift N η' hN
  have hη''e : ∀ e : P, η'' (e : P ⧸ N) = η' e := fun e => rfl
  have hη'' : Function.Surjective η'' := fun g => by
    obtain ⟨e, rfl⟩ := (hθ.comp hη) g
    exact ⟨(e : P ⧸ N), rfl⟩
  have : Group.IsPerfect (P ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hker'' : η''.ker ≤ Subgroup.center (P ⧸ N) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ η'.ker := by
      rw [MonoidHom.mem_ker, ← hη''e]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hcen' he) z']
  have hp'' : IsPGroup p η''.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ η'.ker := by
      rw [MonoidHom.mem_ker, ← hη''e]
      exact hy
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := p) hcen' he
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have hbot := htriv (P ⧸ N) η'' hη'' hker'' hp''
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ η'.ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, map_one]
  have hxN : x ∈ N := by
    have hq : (x : P ⧸ N) ∈ η''.ker := by
      rw [MonoidHom.mem_ker, hη''e]
      exact hx'
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hq
    exact hq
  obtain ⟨n, hn⟩ := hp ⟨x, hx⟩
  have hx1 : x ^ p ^ n = 1 := congrArg Subtype.val hn
  have hcop : Nat.Coprime (orderOf x) (p ^ n) :=
    Nat.Coprime.pow_right n (CoprimeSplit.mem_copPart.1 hxN).2.symm
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
  exact Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hx1)

theorem exists_section_of_cover_and_coprime {H J : Type} [Group H] [Finite H] [Group.IsPerfect H]
    [Group J] {p : ℕ} [Fact p.Prime] {θ : H →* J} (hθ : Function.Surjective θ)
    (hθc : θ.ker ≤ Subgroup.center H)
    (htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* J),
      Function.Surjective η → η.ker ≤ Subgroup.center P → IsPGroup p η.ker → η.ker = ⊥)
    (hcop : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → p.Coprime (Nat.card π.ker) → ∃ σ : H →* E, ∀ g, π (σ g) = g)
    (E : Type) [Group E] [Finite E] (π : E →* H) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : H →* E, ∀ g, π (σ g) = g :=
  CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun P _ _ _ η hη hC h2 => ker_eq_bot_of_central_quotient hθ hθc htriv P η hη hC h2)
      E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => hcop E' π' hπ' hcen' hc')

theorem hopfMultiplier_quotient {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ Subgroup.center H)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : H →* E, ∀ g, π (σ g) = g) :
    commutator (H ⧸ Z) = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier (H ⧸ Z) ≃* Z) := by
  set q : H →* H ⧸ Z := QuotientGroup.mk' Z
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Z := QuotientGroup.ker_mk' _
  have hperf : Group.IsPerfect (H ⧸ Z) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ⟨?_⟩⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover (H ⧸ Z)) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (H ⧸ Z) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq (hker.symm ▸ hZ)
      fun π hπ hcen => hsplit _ π hπ hcen)
  exact (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans (MulEquiv.subgroupCongr hker))

end CFSG.LieType.Steinberg.CentralExt.CoverAssembly
