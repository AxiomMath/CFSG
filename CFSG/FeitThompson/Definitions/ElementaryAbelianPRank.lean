module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Subgroup

variable {p d : ℕ} {X Y : Type*} [Group X] [Group Y]

theorem card_pi_multiplicative_zmod (p d : ℕ) :
    Nat.card (Fin d → Multiplicative (ZMod p)) = p ^ d := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem pow_eq_one_multiplicative_zmod (p : ℕ) (a : Multiplicative (ZMod p)) : a ^ p = 1 := by
  induction a using Multiplicative.ofAdd.surjective.forall.2 with
  | _ x => rw [← ofAdd_nsmul]; simp

theorem pow_eq_one_pi_multiplicative_zmod (p d : ℕ) (a : Fin d → Multiplicative (ZMod p)) :
    a ^ p = 1 := by
  funext i
  simpa using pow_eq_one_multiplicative_zmod p (a i)

private theorem nonempty_addEquiv_pi_zmod (p d : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (hcard : Nat.card V = p ^ d) :
    Nonempty (V ≃+ (Fin d → ZMod p)) := by
  have hp : p.Prime := Fact.out
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcard' : Nat.card V = p ^ finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  have hd : finrank (ZMod p) V = d := by
    refine Nat.pow_right_injective hp.two_le (?_ : p ^ _ = p ^ _)
    rw [← hcard', hcard]
  exact ⟨(Module.finBasisOfFinrankEq (ZMod p) V hd).equivFun.toAddEquiv⟩

theorem nonempty_mulEquiv_pi_of_exponent {G : Type*} [CommGroup G] (hp : p.Prime)
    (hexp : ∀ x : G, x ^ p = 1) (hcard : Nat.card G = p ^ d) :
    Nonempty (G ≃* (Fin d → Multiplicative (ZMod p))) := by
  have hfp := Fact.mk hp
  have hnz : NeZero p := ⟨hp.ne_zero⟩
  have hfin : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have hfin' : Finite (Additive G) := inferInstanceAs (Finite G)
  let inst : Module (ZMod p) (Additive G) := AddCommMonoid.zmodModule (fun x => by
    induction x using Additive.ofMul.surjective.forall.2 with
    | _ a => rw [← ofMul_pow, hexp a]; rfl)
  obtain ⟨e⟩ := nonempty_addEquiv_pi_zmod p d (Additive G)
    (by rw [← hcard]; exact Nat.card_congr Additive.ofMul.symm)
  exact ⟨(MulEquiv.multiplicativeAdditive G).symm.trans
    ((AddEquiv.toMultiplicative e).trans (MulEquiv.piMultiplicative _))⟩

def elementaryAbelianRanks (p : ℕ) (X : Type*) [Group X] : Set ℕ :=
  {d | ∃ H : Subgroup X, Nonempty (H ≃* (Fin d → Multiplicative (ZMod p)))}

@[simp]
theorem mem_elementaryAbelianRanks :
    d ∈ elementaryAbelianRanks p X ↔
      ∃ H : Subgroup X, Nonempty (H ≃* (Fin d → Multiplicative (ZMod p))) := Iff.rfl

theorem mem_elementaryAbelianRanks_iff_exists_subgroup (hp : p.Prime) :
    d ∈ elementaryAbelianRanks p X ↔
      ∃ H : Subgroup X, IsMulCommutative H ∧ (∀ x ∈ H, x ^ p = 1) ∧ Nat.card H = p ^ d := by
  constructor
  · rintro ⟨H, ⟨f⟩⟩
    refine ⟨H, IsMulCommutative.of_comm fun a b =>
      f.injective (by simpa using mul_comm (f a) (f b)), fun x hx => ?_, ?_⟩
    · have h : (⟨x, hx⟩ : H) ^ p = 1 :=
        f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
      exact congrArg (Subgroup.subtype H) h
    · rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
  · rintro ⟨H, hcomm, hexp, hcard⟩
    let _ : CommGroup H := IsMulCommutative.instCommGroup
    exact ⟨H, nonempty_mulEquiv_pi_of_exponent hp (fun x => Subtype.ext (hexp x.1 x.2)) hcard⟩

theorem exists_subgroup_card_eq_of_mem_elementaryAbelianRanks
    (h : d ∈ elementaryAbelianRanks p X) : ∃ H : Subgroup X, Nat.card H = p ^ d := by
  obtain ⟨H, ⟨f⟩⟩ := h
  exact ⟨H, by rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]⟩

theorem zero_mem_elementaryAbelianRanks (p : ℕ) (X : Type*) [Group X] :
    0 ∈ elementaryAbelianRanks p X :=
  ⟨⊥, ⟨MulEquiv.ofUnique⟩⟩

theorem elementaryAbelianRanks_nonempty (p : ℕ) (X : Type*) [Group X] :
    (elementaryAbelianRanks p X).Nonempty :=
  ⟨0, zero_mem_elementaryAbelianRanks p X⟩

theorem le_card_of_mem_elementaryAbelianRanks [Finite X] (hp : 1 < p)
    (h : d ∈ elementaryAbelianRanks p X) : d ≤ Nat.card X := by
  obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks h
  exact (Nat.lt_pow_self hp).le.trans (hH ▸ H.card_le_card_group)

theorem bddAbove_elementaryAbelianRanks [Finite X] (hp : 1 < p) :
    BddAbove (elementaryAbelianRanks p X) :=
  ⟨Nat.card X, fun _ hd => le_card_of_mem_elementaryAbelianRanks hp hd⟩

noncomputable def elementaryAbelianPRank (p : ℕ) (X : Type*) [Group X] : ℕ :=
  sSup (elementaryAbelianRanks p X)

theorem elementaryAbelianPRank_eq_sSup (p : ℕ) (X : Type*) [Group X] :
    elementaryAbelianPRank p X =
      sSup {d | ∃ H : Subgroup X, Nonempty (H ≃* (Fin d → Multiplicative (ZMod p)))} := (rfl)

theorem le_elementaryAbelianPRank [Finite X] (hp : 1 < p) (h : d ∈ elementaryAbelianRanks p X) :
    d ≤ elementaryAbelianPRank p X :=
  le_csSup (bddAbove_elementaryAbelianRanks hp) h

theorem elementaryAbelianPRank_le [Finite X] {n : ℕ}
    (h : ∀ d ∈ elementaryAbelianRanks p X, d ≤ n) : elementaryAbelianPRank p X ≤ n :=
  csSup_le (elementaryAbelianRanks_nonempty p X) h

theorem elementaryAbelianPRank_mem_elementaryAbelianRanks [Finite X] (hp : 1 < p) :
    elementaryAbelianPRank p X ∈ elementaryAbelianRanks p X :=
  Nat.sSup_mem (elementaryAbelianRanks_nonempty p X) (bddAbove_elementaryAbelianRanks hp)

theorem exists_subgroup_mulEquiv_of_elementaryAbelianPRank [Finite X] (hp : 1 < p) :
    ∃ H : Subgroup X,
      Nonempty (H ≃* (Fin (elementaryAbelianPRank p X) → Multiplicative (ZMod p))) :=
  elementaryAbelianPRank_mem_elementaryAbelianRanks hp

theorem pow_elementaryAbelianPRank_dvd_card [Finite X] (hp : 1 < p) :
    p ^ elementaryAbelianPRank p X ∣ Nat.card X := by
  obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks
    (elementaryAbelianPRank_mem_elementaryAbelianRanks (X := X) (p := p) hp)
  exact hH ▸ H.card_subgroup_dvd_card

theorem elementaryAbelianPRank_le_card [Finite X] (hp : 1 < p) :
    elementaryAbelianPRank p X ≤ Nat.card X :=
  elementaryAbelianPRank_le fun _ hd => le_card_of_mem_elementaryAbelianRanks hp hd

theorem elementaryAbelianPRank_eq_zero_of_subsingleton [Subsingleton X] (hp : 1 < p) :
    elementaryAbelianPRank p X = 0 := by
  refine Nat.le_antisymm (elementaryAbelianPRank_le fun d hd => ?_) (Nat.zero_le _)
  obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks hd
  have h1 : p ^ d = 1 := by
    rw [← hH, Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, ⟨1⟩⟩
  simpa [Nat.pow_eq_one, show p ≠ 1 by omega] using h1

theorem elementaryAbelianPRank_pi (hp : 1 < p) (d : ℕ) :
    elementaryAbelianPRank p (Fin d → Multiplicative (ZMod p)) = d := by
  have : NeZero p := ⟨by omega⟩
  refine Nat.le_antisymm (elementaryAbelianPRank_le fun e he => ?_)
    (le_elementaryAbelianPRank hp ⟨⊤, ⟨Subgroup.topEquiv⟩⟩)
  obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks he
  refine (Nat.pow_le_pow_iff_right hp).1 ?_
  rw [← hH, ← card_pi_multiplicative_zmod p d]
  exact H.card_le_card_group

theorem elementaryAbelianPRank_le_of_injective [Finite Y] (hp : 1 < p) {f : X →* Y}
    (hf : Function.Injective f) : elementaryAbelianPRank p X ≤ elementaryAbelianPRank p Y := by
  have : Finite X := Finite.of_injective f hf
  obtain ⟨H, ⟨g⟩⟩ := exists_subgroup_mulEquiv_of_elementaryAbelianPRank (p := p) (X := X) hp
  exact le_elementaryAbelianPRank hp ⟨H.map f, ⟨(H.equivMapOfInjective f hf).symm.trans g⟩⟩

theorem elementaryAbelianPRank_le_of_le [Finite X] (hp : 1 < p) {H K : Subgroup X} (h : H ≤ K) :
    elementaryAbelianPRank p H ≤ elementaryAbelianPRank p K :=
  elementaryAbelianPRank_le_of_injective hp (f := Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

theorem elementaryAbelianPRank_subgroup_le [Finite X] (hp : 1 < p) (H : Subgroup X) :
    elementaryAbelianPRank p H ≤ elementaryAbelianPRank p X :=
  elementaryAbelianPRank_le_of_injective hp H.subtype_injective

theorem elementaryAbelianPRank_eq_of_mulEquiv [Finite X] [Finite Y] (hp : 1 < p) (e : X ≃* Y) :
    elementaryAbelianPRank p X = elementaryAbelianPRank p Y :=
  Nat.le_antisymm (elementaryAbelianPRank_le_of_injective hp (f := e.toMonoidHom) e.injective)
    (elementaryAbelianPRank_le_of_injective hp (f := e.symm.toMonoidHom) e.symm.injective)

theorem one_le_elementaryAbelianPRank_iff [Finite X] (hp : p.Prime) :
    1 ≤ elementaryAbelianPRank p X ↔ p ∣ Nat.card X := by
  have := Fact.mk hp
  refine ⟨fun h => (dvd_pow_self p (by omega)).trans
    (pow_elementaryAbelianPRank_dvd_card hp.one_lt), fun h => ?_⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  refine le_elementaryAbelianPRank hp.one_lt ⟨zpowers x, ⟨?_⟩⟩
  have hc : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hx]
  refine ((zmodCyclicMulEquiv (G := zpowers x) inferInstance).symm.trans ?_).trans
    (MulEquiv.piUnique (fun _ : Fin 1 => Multiplicative (ZMod p))).symm
  rw [hc]

theorem elementaryAbelianPRank_eq_zero_iff [Finite X] (hp : p.Prime) :
    elementaryAbelianPRank p X = 0 ↔ ¬ p ∣ Nat.card X := by
  rw [← one_le_elementaryAbelianPRank_iff hp (X := X)]
  omega

end

end CFSG.FeitThompson
