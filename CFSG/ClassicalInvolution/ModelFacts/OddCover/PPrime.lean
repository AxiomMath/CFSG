module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

universe u v

@[expose] def NoCover (Q : ℕ → Prop) (X : Type v) [Group X] : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* X),
    Function.Surjective π → π.ker ≤ Subgroup.center E → Q (Nat.card π.ker) → π.ker = ⊥

theorem NoCover.of_mulEquiv {Q : ℕ → Prop} {X : Type v} {Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : NoCover.{u} Q X) : NoCover.{u} Q Y := by
  intro E _ _ _ π hπ hcen hQ
  let π' : E →* X := e.symm.toMonoidHom.comp π
  have hker : π'.ker = π.ker := by
    ext x
    simp [π', MonoidHom.mem_ker]
  have := h E π' (e.symm.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hQ)
  rwa [hker] at this

section PrimePart

variable {E : Type*} [Group E]

@[expose] def pPrimePart {p : ℕ} (hp : p.Prime) (C : Subgroup E) (hC : C ≤ Subgroup.center E) :
    Subgroup E where
  carrier := {c | c ∈ C ∧ ¬ p ∣ orderOf c}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨C.mul_mem ha hb, fun h => ?_⟩
    have h1 : orderOf (a * b) ∣ orderOf a * orderOf b :=
      (Commute.orderOf_mul_dvd_lcm (Subgroup.mem_center_iff.1 (hC hb) a)).trans
        (Nat.lcm_dvd_mul _ _)
    rcases (Nat.Prime.dvd_mul hp).1 (h.trans h1) with h2 | h2
    exacts [ha' h2, hb' h2]
  one_mem' := ⟨C.one_mem, by rw [orderOf_one]; exact hp.not_dvd_one⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨C.inv_mem ha, by rwa [orderOf_inv]⟩

theorem mem_pPrimePart {p : ℕ} {hp : p.Prime} {C : Subgroup E} {hC : C ≤ Subgroup.center E}
    {c : E} : c ∈ pPrimePart hp C hC ↔ c ∈ C ∧ ¬ p ∣ orderOf c :=
  Iff.rfl

instance pPrimePart_normal {p : ℕ} (hp : p.Prime) (C : Subgroup E) (hC : C ≤ Subgroup.center E) :
    (pPrimePart hp C hC).Normal :=
  ⟨fun _ hn g => by
    rw [Subgroup.mem_center_iff.1 (hC hn.1) g, mul_inv_cancel_right]
    exact hn⟩

theorem exists_pow_mem_pPrimePart [Finite E] {p : ℕ} (hp : p.Prime) {C : Subgroup E}
    (hC : C ≤ Subgroup.center E) {c : E} (hc : c ∈ C) :
    ∃ a : ℕ, c ^ p ^ a ∈ pPrimePart hp C hC := by
  obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' p hp.ne_one
  refine ⟨a, C.pow_mem hc _, ?_⟩
  rw [orderOf_pow_of_dvd (pow_pos hp.pos a).ne' ⟨m, hcm⟩, hcm,
    Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  exact hm

end PrimePart

section Reduction

variable {E : Type u} {X : Type v} [Group E] [Group X]

theorem not_dvd_card_ker {p : ℕ} [hp : Fact p.Prime]
    (hX : NoCover.{u} (fun n => ∃ k, n = p ^ k) X) [Finite E] [Group.IsPerfect E] (π : E →* X)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) : ¬ p ∣ Nat.card π.ker := by
  set M := pPrimePart hp.out π.ker hcen with hM
  have hMk : M ≤ π.ker := fun _ hc => hc.1
  let π' : E ⧸ M →* X := QuotientGroup.lift M π hMk
  have hπ' : Function.Surjective π' := fun y => by
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨x, rfl⟩
  have hker' : π'.ker = π.ker.map (QuotientGroup.mk' M) := QuotientGroup.ker_lift M π hMk
  have hcen' : π'.ker ≤ Subgroup.center (E ⧸ M) := by
    rw [hker']
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact congrArg (QuotientGroup.mk (s := M)) (Subgroup.mem_center_iff.1 (hcen hc) g)
  have hpg : IsPGroup p π'.ker := by
    rintro ⟨x, hx⟩
    rw [hker'] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_pow_mem_pPrimePart hp.out hcen hc
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' M c) ^ p ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (E ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  have hbot : π'.ker = ⊥ := hX (E ⧸ M) π' hπ' hcen' (IsPGroup.iff_card.1 hpg)
  rw [hker', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxM : ((x : π.ker) : E) ∈ M := hbot x.2
  apply hxM.2
  rw [Subgroup.orderOf_coe, hx]

theorem NoCover.odd_of_pPrime {p : ℕ} [hp : Fact p.Prime]
    (h1 : NoCover.{u} (fun n => ∃ k, n = p ^ k) X)
    (h2 : NoCover.{u} (fun n => Odd n ∧ ¬ p ∣ n) X) : NoCover.{u} Odd X := by
  intro E _ _ _ π hπ hcen hodd
  exact h2 E π hπ hcen ⟨hodd, not_dvd_card_ker h1 π hπ hcen⟩

end Reduction

end CFSG.ClassicalInvolution.ModelFacts.OddCover
