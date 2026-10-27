module

public import CFSG.Quasithin.Background.A1cModuleAut
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG.Quasithin.XMod (IsIrrSec IsInv)

section Abstract

variable {V : Type*} [CommGroup V]

theorem eq_one_of_commute_irreducible_of_fixed {S : Subgroup (MulAut V)}
    (hirr : IsIrrSec ↥S (⊥ : Subgroup V) ⊤) {t : MulAut V} (ht : ∀ s ∈ S, s * t = t * s)
    {w : V} (hw : t w = w) (hw1 : w ≠ 1) : t = 1 := by
  let W : Subgroup V :=
    { carrier := {v | t v = v}
      one_mem' := map_one t
      mul_mem' := fun {a b} (ha : t a = a) (hb : t b = b) => by
        show t (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} (ha : t a = a) => by
        show t a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hW : IsInv ↥S W := by
    intro s w (hw : t w = w)
    have h := congrArg (fun φ : MulAut V => φ w) (ht s s.2)
    simp only [MulAut.mul_apply, hw] at h
    exact h.symm
  rcases hirr.2 W hW bot_le le_top with h | h
  · exfalso
    have hwW : w ∈ W := hw
    rw [h] at hwW
    exact hw1 (Subgroup.mem_bot.mp hwW)
  · refine MulEquiv.ext fun v => ?_
    have hv : v ∈ W := by rw [h]; trivial
    exact hv

variable [Finite V]

theorem eq_one_of_commute_irreducible_of_pow_two_pow (hV : IsPGroup 2 V)
    {S : Subgroup (MulAut V)} (hirr : IsIrrSec ↥S (⊥ : Subgroup V) ⊤) {t : MulAut V}
    (ht : ∀ s ∈ S, s * t = t * s) {k : ℕ} (hk : t ^ 2 ^ k = 1) : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hk, one_zpow, Subgroup.coe_one]
  obtain ⟨p, hp⟩ := CFSG.Quasithin.XMod.nontrivial_of_isIrrSec_bot_top hirr
  have : Nontrivial V := ⟨⟨p, 1, hp⟩⟩
  obtain ⟨n, hn, hcard⟩ := hV.nontrivial_iff_card.mp inferInstance
  obtain ⟨b, hb, hb1⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point V
    (by rw [hcard]; exact dvd_pow_self 2 (by omega)) (a := (1 : V)) (fun g => smul_one g)
  exact eq_one_of_commute_irreducible_of_fixed hirr ht (hb ⟨t, Subgroup.mem_zpowers t⟩)
    (Ne.symm hb1)

end Abstract

theorem exists_quotAction {P : Type*} [CommGroup P] (Zq : Subgroup P) {SG TG : Type*}
    [Group SG] [Group TG] (σ : SG →* MulAut P) (τ : TG →* MulAut P)
    (hσ : ∀ s x, x ∈ Zq ↔ σ s x ∈ Zq) (hτ : ∀ t x, x ∈ Zq ↔ τ t x ∈ Zq) (hne : Zq ≠ ⊤)
    (hirr : ∀ J : Subgroup P, Zq ≤ J → (∀ s : SG, ∀ x ∈ J, σ s x ∈ J) → J = Zq ∨ J = ⊤) :
    ∃ (σ' : SG →* MulAut (P ⧸ Zq)) (τ' : TG →* MulAut (P ⧸ Zq)),
      (∀ s (x : P), σ' s (x : P ⧸ Zq) = ((σ s x : P) : P ⧸ Zq)) ∧
      (∀ t (x : P), τ' t (x : P ⧸ Zq) = ((τ t x : P) : P ⧸ Zq)) ∧
      IsIrrSec ↥σ'.range (⊥ : Subgroup (P ⧸ Zq)) ⊤ := by
  have hmap : ∀ φ : MulAut P, (∀ x, x ∈ Zq ↔ φ x ∈ Zq) →
      Zq.map (φ : P ≃* P).toMonoidHom = Zq := by
    intro φ hφ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hφ x).1 hx
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      exact (hφ _).2 (by simpa using hy)
  let σ' : SG →* MulAut (P ⧸ Zq) :=
    { toFun := fun s => QuotientGroup.congr Zq Zq (σ s) (hmap (σ s) (hσ s))
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((σ 1) x) : P ⧸ Zq) = ↑x
          rw [map_one]; rfl
      map_mul' := fun s s' => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((σ (s * s')) x) : P ⧸ Zq) = ↑((σ s) ((σ s') x))
          rw [map_mul]; rfl }
  let τ' : TG →* MulAut (P ⧸ Zq) :=
    { toFun := fun t => QuotientGroup.congr Zq Zq (τ t) (hmap (τ t) (hτ t))
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((τ 1) x) : P ⧸ Zq) = ↑x
          rw [map_one]; rfl
      map_mul' := fun t t' => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((τ (t * t')) x) : P ⧸ Zq) = ↑((τ t) ((τ t') x))
          rw [map_mul]; rfl }
  refine ⟨σ', τ', fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  have hnt : Nontrivial (P ⧸ Zq) := by
    obtain ⟨x, hx⟩ : ∃ x : P, x ∉ Zq := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.2 fun x _ => h x)
    exact ⟨⟨QuotientGroup.mk x, 1, fun h => hx ((QuotientGroup.eq_one_iff x).1 h)⟩⟩
  refine ⟨bot_lt_top, fun J hJ _ _ => ?_⟩
  have hZJ : Zq ≤ J.comap (QuotientGroup.mk' Zq) := fun x hx => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact J.one_mem
  have hJσ : ∀ s : SG, ∀ x ∈ J.comap (QuotientGroup.mk' Zq),
      σ s x ∈ J.comap (QuotientGroup.mk' Zq) := fun s x hx =>
    hJ ⟨σ' s, ⟨s, rfl⟩⟩ (QuotientGroup.mk x) hx
  rcases hirr _ hZJ hJσ with h | h
  · left
    refine (Subgroup.eq_bot_iff_forall J).2 fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      have : x ∈ J.comap (QuotientGroup.mk' Zq) := hq
      rw [h] at this
      exact (QuotientGroup.eq_one_iff x).2 this
  · right
    refine eq_top_iff.2 fun q _ => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      have : x ∈ J.comap (QuotientGroup.mk' Zq) := by rw [h]; trivial
      exact this

end CFSG.CGT.PushingUpLit.ThmOne
